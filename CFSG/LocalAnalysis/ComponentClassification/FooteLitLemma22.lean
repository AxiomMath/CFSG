module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoreInner
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoprime
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalOrbits

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G]

theorem mem_oddResidualIn {Y : Subgroup G} {g : G} (hg : g ∈ Y)
    (h2 : ∃ k : ℕ, orderOf g = 2 ^ k) : g ∈ oddResidualIn Y :=
  Subgroup.subset_closure ⟨hg, h2⟩

theorem oddResidualIn_le (Y : Subgroup G) : oddResidualIn Y ≤ Y :=
  closure_le _ |>.mpr fun _ hg => hg.1

theorem oddResidualIn_mono {Y Y' : Subgroup G} (h : Y ≤ Y') :
    oddResidualIn Y ≤ oddResidualIn Y' :=
  closure_mono fun _ hg => ⟨h hg.1, hg.2⟩

theorem footeFixed_eq_oddResidualIn (L : Subgroup G) (t : G) :
    footeFixed L t = oddResidualIn ((L ⊓ centralizer ({t} : Set G)) ⊔ oddCoreOfCentralizer t) :=
  rfl

theorem conj_mem_oddResidualIn {Y : Subgroup G} {g : G} (hg : g ∈ normalizer (Y : Set G))
    {x : G} (hx : x ∈ oddResidualIn Y) : g * x * g⁻¹ ∈ oddResidualIn Y := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨hyY, k, hk⟩ := hy
    apply Subgroup.subset_closure
    refine ⟨(mem_normalizer_iff.mp hg y).mp hyY, k, ?_⟩
    rw [← hk]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem mem_normalizer_oddResidualIn {Y : Subgroup G} {g : G}
    (hg : g ∈ normalizer (Y : Set G)) :
    g ∈ normalizer ((oddResidualIn Y : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_oddResidualIn hg, fun h => ?_⟩
  have := conj_mem_oddResidualIn (inv_mem hg) h
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

variable [Finite G]

theorem eq_one_of_two_element_of_odd {A : Subgroup G} (hA : Odd (Nat.card A)) {g : G}
    (hg : g ∈ A) (h2 : ∃ k : ℕ, orderOf g = 2 ^ k) : g = 1 := by
  obtain ⟨k, hk⟩ := h2
  have hodd := odd_orderOf_of_mem_of_odd hA hg
  rw [hk] at hodd
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exact absurd hodd (by rw [pow_succ]; exact Nat.not_odd_iff_even.mpr (even_two.mul_left _))

theorem oddResidualIn_eq_bot_of_odd {A : Subgroup G} (hA : Odd (Nat.card A)) :
    oddResidualIn A = ⊥ := by
  rw [eq_bot_iff]
  refine (closure_le _).mpr fun g hg => ?_
  exact mem_bot.mpr (eq_one_of_two_element_of_odd hA hg.1 hg.2)

theorem mem_of_two_element_of_mem_sup {A N : Subgroup G} (hAN : A ≤ normalizer (N : Set G))
    (hR : oddResidualIn A ≤ N) {g : G} (hg : g ∈ A ⊔ N) (h2 : ∃ k : ℕ, orderOf g = 2 ^ k) :
    g ∈ N := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A N hAN] at hg
  obtain ⟨a, ha, n, hn, rfl⟩ := hg
  obtain ⟨j, m, hm, hjm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos a).ne'
  have hm0 : m ≠ 0 := fun h => by simp [h] at hm
  have ham : a ^ m ∈ N := by
    apply hR
    apply mem_oddResidualIn (pow_mem ha m)
    refine ⟨j, ?_⟩
    rw [orderOf_pow' a hm0, hjm, Nat.gcd_mul_left_left,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  obtain ⟨k, hk⟩ := h2
  have hpow : ∀ i : ℕ, (a ^ i)⁻¹ * (a * n) ^ i ∈ N := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hconj := (mem_normalizer_iff.mp (hAN (inv_mem ha)) _).mp ih
      have e : (a ^ (i + 1))⁻¹ * (a * n) ^ (i + 1) =
          a⁻¹ * ((a ^ i)⁻¹ * (a * n) ^ i) * a⁻¹⁻¹ * n := by
        rw [pow_succ, pow_succ]; group
      rw [e]
      exact mul_mem hconj hn
  have ha2 : a ^ 2 ^ k ∈ N := by
    have h := hpow (2 ^ k)
    rw [show (a * n) ^ 2 ^ k = 1 by rw [← hk, pow_orderOf_eq_one], mul_one] at h
    exact inv_mem_iff.mp h
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
  have haN : a ∈ N := by
    have hg := Nat.gcd_eq_gcd_ab m (2 ^ k)
    rw [hcop.gcd_eq_one, Nat.cast_one] at hg
    have e : a = (a ^ m) ^ (Nat.gcdA m (2 ^ k)) * (a ^ 2 ^ k) ^ (Nat.gcdB m (2 ^ k)) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hg, zpow_one]
    rw [e]
    exact mul_mem (zpow_mem ham _) (zpow_mem ha2 _)
  exact mul_mem haN hn

theorem odd_card_sup_of_le_normalizer {A N : Subgroup G} (hAN : A ≤ normalizer (N : Set G))
    (hA : Odd (Nat.card A)) (hN : Odd (Nat.card N)) : Odd (Nat.card ↥(A ⊔ N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hev
  obtain ⟨⟨g, hg⟩, hgo⟩ := exists_prime_orderOf_dvd_card' 2
    (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev))
  rw [Subgroup.orderOf_mk] at hgo
  have hgN := mem_of_two_element_of_mem_sup hAN (by rw [oddResidualIn_eq_bot_of_odd hA]; exact
    bot_le) hg ⟨1, by rw [hgo, pow_one]⟩
  have := odd_orderOf_of_mem_of_odd hN hgN
  rw [hgo] at this
  exact absurd this (by decide)

omit [Finite G] in
theorem le_oddCoreIn {Y N : Subgroup G} (hNY : N ≤ Y) (hYN : Y ≤ normalizer (N : Set G))
    (hN : Odd (Nat.card N)) : N ≤ oddCoreIn Y := by
  have : (N.subgroupOf Y).Normal := (normal_subgroupOf_iff_le_normalizer hNY).mpr hYN
  have hcop : Nat.Coprime 2 (Nat.card ↥(N.subgroupOf Y)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hNY).toEquiv]
    exact Nat.coprime_two_left.mpr hN
  have hle : N.subgroupOf Y ≤ pPrimeCore 2 ↥Y := le_sSup ⟨inferInstance, hcop⟩
  intro x hx
  exact ⟨⟨x, hNY hx⟩, hle (show (⟨x, hNY hx⟩ : Y) ∈ N.subgroupOf Y from hx), rfl⟩

theorem oddResidualIn_eq_self_of_isPComponent {K W : Subgroup G} (hKW : K ≤ W)
    (hK : IsPComponent 2 (K.subgroupOf W)) : oddResidualIn K = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hres, -⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K W hKW).mp hK
  refine le_antisymm (oddResidualIn_le K) ?_
  intro x hx
  have hxtop : (⟨x, hx⟩ : K) ∈ CatalogueBPrimeJoin.primeResidual 2 K := hres ▸ mem_top _
  have hle : (CatalogueBPrimeJoin.primeResidual 2 K).map K.subtype ≤ oddResidualIn K := by
    rw [map_le_iff_le_comap]
    refine sSup_le fun P hP => ?_
    intro y hy
    obtain ⟨i, hi⟩ := hP ⟨y, hy⟩
    have hyi : (y : G) ^ 2 ^ i = 1 := by
      have := congrArg (fun z : P => ((z : K) : G)) hi
      simpa using this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hyi)
    exact mem_oddResidualIn y.2 ⟨j, hj⟩
  exact hle ⟨⟨x, hx⟩, hxtop, rfl⟩

theorem exists_mem_inf_centralizer_of_mem_sup {p : ℕ} [Fact p.Prime] {P Y N : Subgroup G}
    (hP : IsPGroup p P) (hN : ¬ p ∣ Nat.card N) (hPY : P ≤ normalizer (Y : Set G))
    (hPN : P ≤ normalizer (N : Set G)) (hYN : Y ≤ normalizer (N : Set G)) {g : G}
    (hg : g ∈ Y ⊔ N) (hgP : g ∈ centralizer (P : Set G)) :
    ∃ y ∈ Y ⊓ centralizer (P : Set G), y⁻¹ * g ∈ N ⊓ centralizer (P : Set G) := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right Y N hYN] at hg
  obtain ⟨y₀, hy₀, n₀, hn₀, rfl⟩ := hg
  have hYNn : ¬ p ∣ Nat.card ↥(Y ⊓ N) := fun h => hN (h.trans (card_dvd_of_le inf_le_right))
  have hPYN : P ≤ normalizer ((Y ⊓ N : Subgroup G) : Set G) := by
    intro u hu
    rw [mem_normalizer_iff]
    intro z
    simp only [mem_inf]
    exact and_congr (mem_normalizer_iff.mp (hPY hu) z) (mem_normalizer_iff.mp (hPN hu) z)
  obtain ⟨m, hm, hym⟩ := exists_mul_mem_centralizer hP hYNn hPYN (y := y₀) (fun u hu => by
    refine mem_inf.mpr ⟨mul_mem (inv_mem hy₀) ((mem_normalizer_iff.mp (hPY hu) y₀).mp hy₀), ?_⟩
    have hcu : u * (y₀ * n₀) = y₀ * n₀ * u := (mem_centralizer_iff.mp hgP) u hu
    have e : y₀⁻¹ * (u * y₀ * u⁻¹) = n₀ * (u * n₀⁻¹ * u⁻¹) := by
      calc y₀⁻¹ * (u * y₀ * u⁻¹) = y₀⁻¹ * (u * (y₀ * n₀)) * n₀⁻¹ * u⁻¹ := by group
        _ = y₀⁻¹ * (y₀ * n₀ * u) * n₀⁻¹ * u⁻¹ := by rw [hcu]
        _ = n₀ * (u * n₀⁻¹ * u⁻¹) := by group
    rw [e]
    exact mul_mem hn₀ ((mem_normalizer_iff.mp (hPN hu) _).mp (inv_mem hn₀)))
  refine ⟨y₀ * m, mem_inf.mpr ⟨mul_mem hy₀ (mem_inf.mp hm).1, hym⟩, mem_inf.mpr ⟨?_, ?_⟩⟩
  · rw [show (y₀ * m)⁻¹ * (y₀ * n₀) = m⁻¹ * n₀ by group]
    exact mul_mem (inv_mem (mem_inf.mp hm).2) hn₀
  · exact mul_mem (inv_mem hym) hgP

omit [Finite G] in
theorem mem_normalizer_inf' {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro z
  simp only [mem_inf]
  exact and_congr (mem_normalizer_iff.mp hA z) (mem_normalizer_iff.mp hB z)

omit [Finite G] in
theorem mem_normalizer_oddCoreIn {L : Subgroup G} {g : G} (hg : g ∈ normalizer (L : Set G)) :
    g ∈ normalizer ((oddCoreIn L : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => Walter.conj_mem_map_of_characteristic hg hx, fun hx => ?_⟩
  have := Walter.conj_mem_map_of_characteristic (inv_mem hg) hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

omit [Finite G] in
theorem mem_normalizer_oddCoreOfCentralizer {t g : G} (hg : g ∈ centralizer ({t} : Set G)) :
    g ∈ normalizer ((oddCoreOfCentralizer t : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_oddCoreOfCentralizer hg hx, fun hx => ?_⟩
  have := conj_mem_oddCoreOfCentralizer (inv_mem hg) hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

omit [Finite G] in
theorem mem_normalizer_centralizer_singleton {t g : G} (hg : g * t = t * g) :
    g ∈ normalizer ((centralizer ({t} : Set G) : Subgroup G) : Set G) :=
  le_normalizer (mem_centralizer_singleton_iff.mpr hg)

omit [Finite G] in
theorem le_normalizer_sup_of_le_normalizer {U O : Subgroup G} (hUO : U ≤ normalizer (O : Set G)) :
    O ≤ normalizer ((U ⊔ O : Subgroup G) : Set G) := by
  have key : ∀ o ∈ O, ∀ x ∈ U ⊔ O, o * x * o⁻¹ ∈ U ⊔ O := by
    intro o ho x hx
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right U O hUO] at hx
    obtain ⟨u, hu, o', ho', rfl⟩ := hx
    rw [show o * (u * o') * o⁻¹ = u * ((u⁻¹ * o * u) * o' * o⁻¹) by group]
    have h1 : u⁻¹ * o * u ∈ O := by
      have := (mem_normalizer_iff.mp (hUO (inv_mem hu)) o).mp ho
      rwa [inv_inv] at this
    exact mul_mem (mem_sup_left hu) (mem_sup_right (mul_mem (mul_mem h1 ho') (inv_mem ho)))
  intro o ho
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key o ho x, fun hx => ?_⟩
  have := key o⁻¹ (inv_mem ho) _ hx
  rwa [show o⁻¹ * (o * x * o⁻¹) * o⁻¹⁻¹ = x by group] at this

omit [Finite G] in
theorem centralizer_zpowers_eq (t : G) :
    centralizer ((zpowers t : Subgroup G) : Set G) = centralizer ({t} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem oddCoreOfCentralizer_inf_le_normalizer (hLB : FooteLBalanceInput) {b c : G}
    (hb : orderOf b = 2) (hbc : b * c = c * b) {Y : Subgroup G}
    (hYc : Y ≤ centralizer ({c} : Set G))
    (hY : IsPComponent 2 (Y.subgroupOf (centralizer ({c} : Set G)))) :
    oddCoreOfCentralizer b ⊓ centralizer ({c} : Set G) ≤ normalizer (Y : Set G) := by
  have hbC : b ∈ centralizer ({c} : Set G) := mem_centralizer_singleton_iff.mpr hbc
  set b' : centralizer ({c} : Set G) := ⟨b, hbC⟩
  have hb' : orderOf b' = 2 := by rw [Subgroup.orderOf_mk]; exact hb
  have hN := (hLB _ b' hb' _ hY).1
  intro x hx
  obtain ⟨x', hx', rfl⟩ := mem_map.mp (oddCoreOfCentralizer_inf_le _ b' hx)
  exact mem_normalizer_of_subgroupOf hYc (hN hx')

omit [Finite G] in
theorem coreActionKernel_facts {L : Subgroup G} {t : G} (ht : t ∈ coreActionKernel L) :
    t ∈ normalizer (L : Set G) ∧ ∀ x ∈ L, x⁻¹ * t⁻¹ * x * t ∈ oddCoreIn L := ht

theorem exists_mem_centralizer_of_le_coreActionKernel {L P : Subgroup G} (hP : IsPGroup 2 P)
    (hPL : P ≤ coreActionKernel L) {x : G} (hx : x ∈ L) :
    ∃ y ∈ L ⊓ centralizer (P : Set G), y⁻¹ * x ∈ oddCoreIn L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : ¬ 2 ∣ Nat.card (oddCoreIn L) := by
    have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥L)
    rw [oddCoreIn, Subgroup.card_map_of_injective L.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop
  have hPO : P ≤ normalizer ((oddCoreIn L : Subgroup G) : Set G) := fun u hu =>
    mem_normalizer_oddCoreIn (hPL hu).1
  obtain ⟨n, hn, hxn⟩ := exists_mul_mem_centralizer hP hO hPO (y := x) (fun u hu => by
    have h := (hPL (inv_mem hu)).2 x hx
    rwa [inv_inv, show x⁻¹ * u * x * u⁻¹ = x⁻¹ * (u * x * u⁻¹) by group] at h)
  refine ⟨x * n, mem_inf.mpr ⟨mul_mem hx (map_subtype_le _ hn), hxn⟩, ?_⟩
  rw [show (x * n)⁻¹ * x = n⁻¹ by group]
  exact inv_mem hn

omit [Finite G] in
theorem footeFixed_le_centralizer (L : Subgroup G) (t : G) :
    footeFixed L t ≤ centralizer ({t} : Set G) :=
  (oddResidualIn_le _).trans (sup_le inf_le_right (oddCoreOfCentralizer_le_centralizer t))

theorem odd_card_oddCoreOfCentralizer (t : G) : Odd (Nat.card (oddCoreOfCentralizer t)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥(centralizer ({t} : Set G)))
  rw [oddCoreOfCentralizer, Subgroup.card_map_of_injective (subtype_injective _)]
  exact Nat.coprime_two_left.mp hcop

theorem odd_card_oddCoreIn (L : Subgroup G) : Odd (Nat.card (oddCoreIn L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥L)
  rw [oddCoreIn, Subgroup.card_map_of_injective (subtype_injective _)]
  exact Nat.coprime_two_left.mp hcop

theorem footeFixed_le_oddResidualIn_sup (L : Subgroup G) (t : G) :
    footeFixed L t ≤ oddResidualIn (L ⊓ centralizer ({t} : Set G)) ⊔ oddCoreOfCentralizer t := by
  have hA : L ⊓ centralizer ({t} : Set G) ≤ normalizer ((oddResidualIn
      (L ⊓ centralizer ({t} : Set G)) ⊔ oddCoreOfCentralizer t : Subgroup G) : Set G) :=
    fun u hu => mem_normalizer_sup (mem_normalizer_oddResidualIn (le_normalizer hu))
      (mem_normalizer_oddCoreOfCentralizer (mem_inf.mp hu).2)
  have hle : (L ⊓ centralizer ({t} : Set G)) ⊔ oddCoreOfCentralizer t ≤
      (L ⊓ centralizer ({t} : Set G)) ⊔
        (oddResidualIn (L ⊓ centralizer ({t} : Set G)) ⊔ oddCoreOfCentralizer t) :=
    sup_le_sup_left le_sup_right _
  refine (closure_le _).mpr fun g hg => ?_
  exact mem_of_two_element_of_mem_sup hA le_sup_left (hle hg.1) hg.2

theorem le_oddResidualIn_sup_oddCoreIn {a : G} {L P : Subgroup G} (hL : IsTwoComponentAt a L)
    (hP : IsPGroup 2 P) (hPL : P ≤ coreActionKernel L) :
    L ≤ oddResidualIn (L ⊓ centralizer (P : Set G)) ⊔ oddCoreIn L := by
  obtain ⟨-, hLa, hLc⟩ := hL
  have hA : L ⊓ centralizer (P : Set G) ≤ normalizer ((oddResidualIn
      (L ⊓ centralizer (P : Set G)) ⊔ oddCoreIn L : Subgroup G) : Set G) := fun u hu =>
    mem_normalizer_sup (mem_normalizer_oddResidualIn (le_normalizer hu))
      (mem_normalizer_oddCoreIn (le_normalizer (mem_inf.mp hu).1))
  calc L = oddResidualIn L := (oddResidualIn_eq_self_of_isPComponent hLa hLc).symm
    _ ≤ _ := by
      refine (closure_le _).mpr fun g hg => ?_
      obtain ⟨y, hy, hyg⟩ := exists_mem_centralizer_of_le_coreActionKernel hP hPL hg.1
      have hgmem : g ∈ (L ⊓ centralizer (P : Set G)) ⊔
          (oddResidualIn (L ⊓ centralizer (P : Set G)) ⊔ oddCoreIn L) := by
        rw [show g = y * (y⁻¹ * g) by group]
        exact mul_mem (mem_sup_left hy) (mem_sup_right (mem_sup_right hyg))
      exact mem_of_two_element_of_mem_sup hA le_sup_left hgmem hg.2

theorem oddResidualIn_inf_oddCoreIn_le {t : G} {L : Subgroup G}
    (hLt : IsTwoComponentAt t (footeFixed L t)) :
    oddResidualIn (L ⊓ centralizer ({t} : Set G)) ⊓ oddCoreIn L ≤ oddCoreOfCentralizer t := by
  set M := oddResidualIn (L ⊓ centralizer ({t} : Set G)) with hM
  set U := M ⊓ oddCoreIn L with hU
  set Ot := oddCoreOfCentralizer t with hOt
  set Lt := footeFixed L t with hLtdef
  have hUodd : Odd (Nat.card U) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn L) (card_dvd_of_le inf_le_right)
  have hMC : M ≤ centralizer ({t} : Set G) := (oddResidualIn_le _).trans inf_le_right
  have hML : M ≤ L := (oddResidualIn_le _).trans inf_le_left
  have hUOt : U ≤ normalizer (Ot : Set G) := fun u hu =>
    mem_normalizer_oddCoreOfCentralizer (hMC (mem_inf.mp hu).1)
  have hUOodd : Odd (Nat.card ↥(U ⊔ Ot)) :=
    odd_card_sup_of_le_normalizer hUOt hUodd (odd_card_oddCoreOfCentralizer t)
  have hMU : M ≤ normalizer ((U ⊔ Ot : Subgroup G) : Set G) := fun m hm =>
    mem_normalizer_sup (mem_normalizer_inf' (le_normalizer hm)
      (mem_normalizer_oddCoreIn (le_normalizer (hML hm))))
      (mem_normalizer_oddCoreOfCentralizer (hMC hm))
  have hOU : Ot ≤ normalizer ((U ⊔ Ot : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer hUOt
  have hLtN : Lt ≤ normalizer ((U ⊔ Ot : Subgroup G) : Set G) :=
    (footeFixed_le_oddResidualIn_sup L t).trans (sup_le hMU hOU)
  have hW : (U ⊔ Ot) ⊓ Lt ≤ oddCoreIn Lt :=
    le_oddCoreIn inf_le_right (fun x hx => mem_normalizer_inf' (hLtN hx) (le_normalizer hx))
      (Odd.of_dvd_nat hUOodd (card_dvd_of_le inf_le_left))
  have hOLt : oddCoreIn Lt ≤ Ot := UGSChain.map_pPrimeCore_le_of_isPComponent hLt.2.1 hLt.2.2
  have hMLt : M ≤ Lt := oddResidualIn_mono le_sup_left
  intro u hu
  exact hOLt (hW (mem_inf.mpr ⟨mem_sup_left hu, hMLt (mem_inf.mp hu).1⟩))

theorem footeFixed_footeFixed_le (hLB : FooteLBalanceInput) {b c : G} {L : Subgroup G}
    (hb : orderOf b = 2) (hc : orderOf c = 2) (hbc : b * c = c * b)
    (hcL : c ∈ normalizer (L : Set G)) (hLc : IsTwoComponentAt c (footeFixed L c)) :
    footeFixed (footeFixed L b) c ≤ footeFixed L c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ob := oddCoreOfCentralizer b with hOb
  set Oc := oddCoreOfCentralizer c with hOc
  set Lc := footeFixed L c with hLcdef
  set X := Ob ⊓ centralizer ({c} : Set G) with hX
  set A := L ⊓ centralizer ({b} : Set G) ⊓ centralizer ({c} : Set G) with hA
  have hcb : c ∈ centralizer ({b} : Set G) := mem_centralizer_singleton_iff.mpr hbc.symm
  have hObodd : ¬ 2 ∣ Nat.card Ob := (odd_card_oddCoreOfCentralizer b).not_two_dvd_nat
  have hXodd : Odd (Nat.card X) :=
    Odd.of_dvd_nat (odd_card_oddCoreOfCentralizer b) (card_dvd_of_le inf_le_left)
  have hcp : IsPGroup 2 (zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  have hAC : A ≤ (L ⊓ centralizer ({c} : Set G)) ⊔ Oc := fun u hu =>
    mem_sup_left (mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hu).1).1, (mem_inf.mp hu).2⟩)
  have hALc : A ≤ normalizer (Lc : Set G) := fun u hu =>
    mem_normalizer_oddResidualIn (le_normalizer (hAC hu))
  have hPY : zpowers c ≤ normalizer ((L ⊓ centralizer ({b} : Set G) : Subgroup G) : Set G) :=
    zpowers_le.mpr (mem_normalizer_inf' hcL (mem_normalizer_centralizer_singleton hbc.symm))
  have hPN : zpowers c ≤ normalizer (Ob : Set G) :=
    zpowers_le.mpr (mem_normalizer_oddCoreOfCentralizer hcb)
  have hYN : L ⊓ centralizer ({b} : Set G) ≤ normalizer (Ob : Set G) := fun u hu =>
    mem_normalizer_oddCoreOfCentralizer (mem_inf.mp hu).2
  have hLbc : footeFixed L b ⊓ centralizer ({c} : Set G) ≤ A ⊔ X := by
    intro h hh
    obtain ⟨hhLb, hhc⟩ := mem_inf.mp hh
    have hh1 : h ∈ (L ⊓ centralizer ({b} : Set G)) ⊔ Ob := oddResidualIn_le _ hhLb
    have hhP : h ∈ centralizer ((zpowers c : Subgroup G) : Set G) := by
      rw [centralizer_zpowers_eq]; exact hhc
    obtain ⟨y, hy, hyh⟩ := exists_mem_inf_centralizer_of_mem_sup hcp hObodd hPY hPN hYN hh1 hhP
    rw [centralizer_zpowers_eq] at hy hyh
    rw [show h = y * (y⁻¹ * h) by group]
    exact mul_mem (mem_sup_left hy) (mem_sup_right hyh)
  refine (closure_le _).mpr fun g hg => ?_
  obtain ⟨hgmem, hg2⟩ := hg
  have hg1 : g ∈ A ⊔ ((Lc ⊔ Oc) ⊔ X) := by
    have hle : (footeFixed L b ⊓ centralizer ({c} : Set G)) ⊔ Oc ≤ A ⊔ ((Lc ⊔ Oc) ⊔ X) :=
      sup_le (hLbc.trans (sup_le le_sup_left (le_sup_of_le_right le_sup_right)))
        (le_sup_of_le_right (le_sup_of_le_left le_sup_right))
    exact hle hgmem
  have hAN1 : A ≤ normalizer (((Lc ⊔ Oc) ⊔ X : Subgroup G) : Set G) := fun u hu =>
    mem_normalizer_sup (mem_normalizer_sup (hALc hu)
        (mem_normalizer_oddCoreOfCentralizer (mem_inf.mp hu).2))
      (mem_normalizer_inf' (mem_normalizer_oddCoreOfCentralizer (mem_inf.mp (mem_inf.mp hu).1).2)
        (le_normalizer (mem_inf.mp hu).2))
  have hRA : oddResidualIn A ≤ (Lc ⊔ Oc) ⊔ X :=
    (oddResidualIn_mono hAC).trans (le_sup_of_le_left le_sup_left)
  have hg3 := mem_of_two_element_of_mem_sup hAN1 hRA hg1 hg2
  have hXN : X ≤ normalizer ((Lc ⊔ Oc : Subgroup G) : Set G) := fun u hu =>
    mem_normalizer_sup (oddCoreOfCentralizer_inf_le_normalizer hLB hb hbc hLc.2.1 hLc.2.2 hu)
      (mem_normalizer_oddCoreOfCentralizer (mem_inf.mp hu).2)
  have hg4 := mem_of_two_element_of_mem_sup hXN
    (by rw [oddResidualIn_eq_bot_of_odd hXodd]; exact bot_le)
    (show g ∈ X ⊔ (Lc ⊔ Oc) by rw [sup_comm]; exact hg3) hg2
  have hOcN : Oc ≤ normalizer (Lc : Set G) :=
    pPrimeCore_le_normalizer_of_isPComponent hLc.2.1 hLc.2.2
  exact mem_of_two_element_of_mem_sup hOcN
    (by rw [oddResidualIn_eq_bot_of_odd (odd_card_oddCoreOfCentralizer c)]; exact bot_le)
    (show g ∈ Oc ⊔ Lc by rw [sup_comm]; exact hg4) hg2

omit [Finite G] in
theorem isPGroup_closure_pair {b c : G} (hb : orderOf b = 2) (hc : orderOf c = 2)
    (hbc : b * c = c * b) : IsPGroup 2 (closure ({b, c} : Set G)) := by
  have hbb : b * b = 1 := by rw [← sq, ← hb, pow_orderOf_eq_one]
  have hcc : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have key : ∀ x ∈ closure ({b, c} : Set G),
      x * x = 1 ∧ x ∈ centralizer ({b, c} : Set G) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · refine ⟨hbb, mem_centralizer_iff.mpr ?_⟩
        rintro y (rfl | rfl)
        · rfl
        · exact hbc.symm
      · refine ⟨hcc, mem_centralizer_iff.mpr ?_⟩
        rintro y (rfl | rfl)
        · exact hbc
        · rfl
    | one => exact ⟨mul_one 1, one_mem _⟩
    | mul x y hx hy ihx ihy =>
      have hxy : x * y = y * x := by
        have h := mem_centralizer_iff.mp
          ((centralizer_closure ({b, c} : Set G)).symm ▸ ihy.2 : y ∈ centralizer
            ((closure ({b, c} : Set G) : Subgroup G) : Set G)) x hx
        exact h
      refine ⟨?_, mul_mem ihx.2 ihy.2⟩
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hxy]
        _ = 1 := by rw [← mul_assoc, ihx.1, one_mul, ihy.1]
    | inv x _ ihx =>
      exact ⟨by rw [← mul_inv_rev, ihx.1, inv_one], inv_mem ihx.2⟩
  intro x
  exact ⟨1, Subtype.ext (by rw [pow_one, sq]; exact (key x x.2).1)⟩

theorem footeFixed_le_footeFixed_footeFixed {a b c : G} {L : Subgroup G}
    (hL : IsTwoComponentAt a L) (hb : orderOf b = 2) (hc : orderOf c = 2) (hbc : b * c = c * b)
    (hbL : b ∈ coreActionKernel L) (hcL : c ∈ coreActionKernel L)
    (hLc : IsTwoComponentAt c (footeFixed L c)) :
    footeFixed L c ≤ footeFixed (footeFixed L b) c := by
  set Oc := oddCoreOfCentralizer c with hOc
  set Mc := oddResidualIn (L ⊓ centralizer ({c} : Set G)) with hMc
  set V := closure ({b, c} : Set G) with hV
  set MV := oddResidualIn (L ⊓ centralizer (V : Set G)) with hMV
  have hVp := isPGroup_closure_pair hb hc hbc
  have hVL : V ≤ coreActionKernel L :=
    (closure_le _).mpr (Set.insert_subset_iff.mpr ⟨hbL, Set.singleton_subset_iff.mpr hcL⟩)
  have hCV : centralizer (V : Set G) = centralizer ({b, c} : Set G) := centralizer_closure _
  have hCVb : centralizer (V : Set G) ≤ centralizer ({b} : Set G) := by
    rw [hCV]; exact centralizer_le (by simp)
  have hCVc : centralizer (V : Set G) ≤ centralizer ({c} : Set G) := by
    rw [hCV]; exact centralizer_le (by simp)
  have hMVL : MV ≤ L := (oddResidualIn_le _).trans inf_le_left
  have hMVOL : MV ≤ normalizer ((oddCoreIn L : Subgroup G) : Set G) := fun m hm =>
    mem_normalizer_oddCoreIn (le_normalizer (hMVL hm))
  have hLMV := le_oddResidualIn_sup_oddCoreIn hL hVp hVL
  have hMVMc : MV ≤ Mc := oddResidualIn_mono (inf_le_inf_left _ hCVc)
  have hMcle : Mc ≤ MV ⊔ Oc := by
    intro m hm
    have hmL : m ∈ L := ((oddResidualIn_le _).trans inf_le_left) hm
    have h1 := hLMV hmL
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hMVOL] at h1
    obtain ⟨m', hm', o, ho, rfl⟩ := h1
    have hoMc : o ∈ Mc := by
      rw [show o = m'⁻¹ * (m' * o) by group]
      exact mul_mem (inv_mem (hMVMc hm')) hm
    exact mul_mem (mem_sup_left hm')
      (mem_sup_right (oddResidualIn_inf_oddCoreIn_le hLc (mem_inf.mpr ⟨hoMc, ho⟩)))
  have hMVLb : MV ≤ footeFixed L b ⊓ centralizer ({c} : Set G) := by
    refine le_inf ?_ ((oddResidualIn_le _).trans (inf_le_right.trans hCVc))
    exact (oddResidualIn_mono (inf_le_inf_left _ hCVb)).trans (oddResidualIn_mono le_sup_left)
  refine (closure_le _).mpr fun g hg => ?_
  rw [SetLike.mem_coe, footeFixed_eq_oddResidualIn]
  apply mem_oddResidualIn _ hg.2
  have hAN : L ⊓ centralizer ({c} : Set G) ≤ normalizer ((Mc ⊔ Oc : Subgroup G) : Set G) :=
    fun u hu => mem_normalizer_sup (mem_normalizer_oddResidualIn (le_normalizer hu))
      (mem_normalizer_oddCoreOfCentralizer (mem_inf.mp hu).2)
  have hle : (L ⊓ centralizer ({c} : Set G)) ⊔ Oc ≤ (L ⊓ centralizer ({c} : Set G)) ⊔ (Mc ⊔ Oc) :=
    sup_le_sup_left le_sup_right _
  have h1 := mem_of_two_element_of_mem_sup hAN le_sup_left (hle hg.1) hg.2
  have hle2 : Mc ⊔ Oc ≤ (footeFixed L b ⊓ centralizer ({c} : Set G)) ⊔ Oc :=
    sup_le (hMcle.trans (sup_le (hMVLb.trans le_sup_left) le_sup_right)) le_sup_right
  exact hle2 h1

theorem footeFixed_le_oddResidualIn_sup_oddCoreIn {b : G} {L : Subgroup G}
    (hLb : IsTwoComponentAt b (footeFixed L b)) :
    footeFixed L b ⊓ oddCoreOfCentralizer b ≤ oddCoreIn (footeFixed L b) ∧
      footeFixed L b ≤ oddResidualIn (L ⊓ centralizer ({b} : Set G)) ⊔
        oddCoreIn (footeFixed L b) := by
  set Ob := oddCoreOfCentralizer b with hOb
  set Lb := footeFixed L b with hLbdef
  set Mb := oddResidualIn (L ⊓ centralizer ({b} : Set G)) with hMb
  have hO : Lb ⊓ Ob ≤ oddCoreIn Lb :=
    le_oddCoreIn inf_le_left (fun x hx => mem_normalizer_inf' (le_normalizer hx)
        (mem_normalizer_oddCoreOfCentralizer (hLb.2.1 hx)))
      (Odd.of_dvd_nat (odd_card_oddCoreOfCentralizer b) (card_dvd_of_le inf_le_right))
  have hMbOb : Mb ≤ normalizer (Ob : Set G) := fun m hm =>
    mem_normalizer_oddCoreOfCentralizer (((oddResidualIn_le _).trans inf_le_right) hm)
  refine ⟨hO, fun j hj => ?_⟩
  have hj' := footeFixed_le_oddResidualIn_sup L b hj
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hMbOb] at hj'
  obtain ⟨m, hm, o, ho, rfl⟩ := hj'
  have hmLb : m ∈ Lb := oddResidualIn_mono le_sup_left hm
  have hoO : o ∈ oddCoreIn Lb := hO (mem_inf.mpr
    ⟨by rw [show o = m⁻¹ * (m * o) by group]; exact mul_mem (inv_mem hmLb) hj, ho⟩)
  exact mul_mem (mem_sup_left hm) (mem_sup_right hoO)

theorem mem_coreActionKernel_footeFixed {b c : G} {L : Subgroup G} (hbc : b * c = c * b)
    (hcL : c ∈ coreActionKernel L) (hLb : IsTwoComponentAt b (footeFixed L b)) :
    c ∈ coreActionKernel (footeFixed L b) := by
  set Ob := oddCoreOfCentralizer b with hOb
  set Lb := footeFixed L b with hLbdef
  set Mb := oddResidualIn (L ⊓ centralizer ({b} : Set G)) with hMb
  have hcb : c ∈ centralizer ({b} : Set G) := mem_centralizer_singleton_iff.mpr hbc.symm
  have hcLC : c ∈ normalizer ((L ⊓ centralizer ({b} : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf' hcL.1 (mem_normalizer_centralizer_singleton hbc.symm)
  have hcLb : c ∈ normalizer (Lb : Set G) :=
    mem_normalizer_oddResidualIn (mem_normalizer_sup hcLC (mem_normalizer_oddCoreOfCentralizer hcb))
  have hcMb : c ∈ normalizer (Mb : Set G) := mem_normalizer_oddResidualIn hcLC
  obtain ⟨hO, hLbM⟩ := footeFixed_le_oddResidualIn_sup_oddCoreIn hLb
  have hMbOLb : Mb ≤ normalizer ((oddCoreIn Lb : Subgroup G) : Set G) := fun m hm =>
    mem_normalizer_oddCoreIn (le_normalizer (oddResidualIn_mono le_sup_left hm))
  refine ⟨hcLb, fun j hj => ?_⟩
  have hj' := hLbM hj
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hMbOLb] at hj'
  obtain ⟨m, hm, o, hoO, rfl⟩ := hj'
  have hmL : m ∈ L := ((oddResidualIn_le _).trans inf_le_left) hm
  have hmc1 : m⁻¹ * c⁻¹ * m * c ∈ oddCoreIn L := hcL.2 m hmL
  have hmc2 : m⁻¹ * c⁻¹ * m * c ∈ Mb := by
    have h := (mem_normalizer_iff.mp (inv_mem hcMb) m).mp hm
    rw [inv_inv] at h
    rw [show m⁻¹ * c⁻¹ * m * c = m⁻¹ * (c⁻¹ * m * c) by group]
    exact mul_mem (inv_mem hm) h
  have hmc3 : m⁻¹ * c⁻¹ * m * c ∈ Ob :=
    oddResidualIn_inf_oddCoreIn_le hLb (mem_inf.mpr ⟨hmc2, hmc1⟩)
  have hmc : m⁻¹ * c⁻¹ * m * c ∈ oddCoreIn Lb :=
    hO (mem_inf.mpr ⟨oddResidualIn_mono le_sup_left hmc2, hmc3⟩)
  have hco : c⁻¹ * o * c ∈ oddCoreIn Lb := by
    have h := (mem_normalizer_iff.mp (mem_normalizer_oddCoreIn (inv_mem hcLb)) o).mp hoO
    rwa [inv_inv] at h
  rw [show (m * o)⁻¹ * c⁻¹ * (m * o) * c = o⁻¹ * (m⁻¹ * c⁻¹ * m * c) * (c⁻¹ * o * c) by group]
  exact mul_mem (mul_mem (inv_mem hoO) hmc) hco

omit [Finite G] in
theorem mem_pPrimeCore_iff_mem_oddCoreIn {L : Subgroup G} (z : L) :
    z ∈ pPrimeCore 2 L ↔ (z : G) ∈ oddCoreIn L :=
  (Subgroup.mem_map_iff_mem L.subtype_injective).symm

theorem exists_quotient_mulEquiv_footeFixed {a b : G} {L : Subgroup G}
    (hL : IsTwoComponentAt a L) (hb : orderOf b = 2) (hbL : b ∈ coreActionKernel L)
    (hLb : IsTwoComponentAt b (footeFixed L b)) :
    ∃ φ : L ⧸ pPrimeCore 2 L ≃* footeFixed L b ⧸ pPrimeCore 2 (footeFixed L b),
      (∀ (m : G) (hmL : m ∈ L) (hmb : m ∈ footeFixed L b),
        m ∈ oddResidualIn (L ⊓ centralizer ({b} : Set G)) →
          φ (⟨m, hmL⟩ : L) = (⟨m, hmb⟩ : footeFixed L b)) ∧
      ∀ d ∈ normalizer (L : Set G) ⊓ centralizer ({b} : Set G),
        ∀ (x x' : L) (y y' : footeFixed L b), (x' : G) = d * x * d⁻¹ →
          (y' : G) = d * y * d⁻¹ → φ x = y → φ x' = y' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Lb := footeFixed L b with hLbdef
  set Mb := oddResidualIn (L ⊓ centralizer ({b} : Set G)) with hMb
  have hMbL : Mb ≤ L := (oddResidualIn_le _).trans inf_le_left
  have hMbLb : Mb ≤ Lb := oddResidualIn_mono le_sup_left
  have hbp : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  have hsup1 : Mb ⊔ oddCoreIn L = L := by
    refine le_antisymm (sup_le hMbL (map_subtype_le _)) ?_
    have h := le_oddResidualIn_sup_oddCoreIn hL hbp (zpowers_le.mpr hbL)
    rwa [centralizer_zpowers_eq] at h
  obtain ⟨-, hLbM⟩ := footeFixed_le_oddResidualIn_sup_oddCoreIn hLb
  have hsup2 : Mb ⊔ oddCoreIn Lb = Lb := le_antisymm (sup_le hMbLb (map_subtype_le _)) hLbM
  obtain ⟨-, e₁, he₁⟩ := restriction_quotient_mulEquiv hMbL hsup1
  obtain ⟨-, e₂, he₂⟩ := restriction_quotient_mulEquiv hMbLb hsup2
  set φ := e₁.symm.trans e₂ with hφ
  have hφ1 : ∀ (m : G) (hmL : m ∈ L) (hmb : m ∈ Lb), m ∈ Mb →
      φ (⟨m, hmL⟩ : L) = (⟨m, hmb⟩ : Lb) := by
    intro m hmL hmb hm
    have h1 := he₁ ⟨m, hm⟩ hmL
    have h2 := he₂ ⟨m, hm⟩ hmb
    rw [hφ, MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply, h2]
  refine ⟨φ, hφ1, ?_⟩
  rintro d ⟨hdL, hdb⟩ x x' y y' hx' hy' hxy
  have hdLC : d ∈ normalizer ((L ⊓ centralizer ({b} : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf' hdL (le_normalizer hdb)
  have hdMb : d ∈ normalizer (Mb : Set G) := mem_normalizer_oddResidualIn hdLC
  have hdLb : d ∈ normalizer (Lb : Set G) :=
    mem_normalizer_oddResidualIn (mem_normalizer_sup hdLC (mem_normalizer_oddCoreOfCentralizer hdb))
  have hMbOL : Mb ≤ normalizer ((oddCoreIn L : Subgroup G) : Set G) := fun u hu =>
    mem_normalizer_oddCoreIn (le_normalizer (hMbL hu))
  have hx : (x : G) ∈ Mb ⊔ oddCoreIn L := hsup1.symm.le x.2
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hMbOL] at hx
  obtain ⟨m, hm, o, ho, hmo⟩ := hx
  have hxm : (x : L ⧸ pPrimeCore 2 L) = ((⟨m, hMbL hm⟩ : L) : L ⧸ pPrimeCore 2 L) := by
    rw [QuotientGroup.eq, mem_pPrimeCore_iff_mem_oddCoreIn]
    show (x : G)⁻¹ * m ∈ oddCoreIn L
    rw [← hmo, mul_inv_rev, inv_mul_cancel_right]
    exact inv_mem ho
  have hym : ((⟨m, hMbLb hm⟩ : Lb) : Lb ⧸ pPrimeCore 2 Lb) = (y : Lb ⧸ pPrimeCore 2 Lb) := by
    rw [← hφ1 m (hMbL hm) (hMbLb hm) hm, ← hxm, hxy]
  have hmy : m⁻¹ * (y : G) ∈ oddCoreIn Lb := by
    have h := QuotientGroup.eq.mp hym
    rwa [mem_pPrimeCore_iff_mem_oddCoreIn] at h
  have hm' : d * m * d⁻¹ ∈ Mb := (mem_normalizer_iff.mp hdMb m).mp hm
  have hx'm : (x' : L ⧸ pPrimeCore 2 L) =
      ((⟨d * m * d⁻¹, hMbL hm'⟩ : L) : L ⧸ pPrimeCore 2 L) := by
    rw [QuotientGroup.eq, mem_pPrimeCore_iff_mem_oddCoreIn]
    show (x' : G)⁻¹ * (d * m * d⁻¹) ∈ oddCoreIn L
    rw [hx', ← hmo, show (d * (m * o) * d⁻¹)⁻¹ * (d * m * d⁻¹) = (d * o * d⁻¹)⁻¹ by group]
    exact inv_mem ((mem_normalizer_iff.mp (mem_normalizer_oddCoreIn hdL) o).mp ho)
  have hy'm : ((⟨d * m * d⁻¹, hMbLb hm'⟩ : Lb) : Lb ⧸ pPrimeCore 2 Lb) =
      (y' : Lb ⧸ pPrimeCore 2 Lb) := by
    rw [QuotientGroup.eq, mem_pPrimeCore_iff_mem_oddCoreIn]
    show (d * m * d⁻¹)⁻¹ * (y' : G) ∈ oddCoreIn Lb
    rw [hy', show (d * m * d⁻¹)⁻¹ * (d * (y : G) * d⁻¹) = d * (m⁻¹ * (y : G)) * d⁻¹ by group]
    exact (mem_normalizer_iff.mp (mem_normalizer_oddCoreIn hdLb) _).mp hmy
  rw [hx'm, hφ1 _ (hMbL hm') (hMbLb hm') hm', hy'm]

theorem foote_lemma_2_2 (hLB : FooteLBalanceInput) {a b c : G} {L : Subgroup G}
    (hL : IsTwoComponentAt a L) (hb : orderOf b = 2) (hc : orderOf c = 2) (hbc : b * c = c * b)
    (hbL : b ∈ coreActionKernel L) (hcL : c ∈ coreActionKernel L)
    (hLb : IsTwoComponentAt b (footeFixed L b)) (hLc : IsTwoComponentAt c (footeFixed L c)) :
    c ∈ coreActionKernel (footeFixed L b) ∧
      footeFixed (footeFixed L b) c = footeFixed L c ∧
      ∃ φ : L ⧸ pPrimeCore 2 L ≃* footeFixed L b ⧸ pPrimeCore 2 (footeFixed L b),
        (∀ (m : G) (hmL : m ∈ L) (hmb : m ∈ footeFixed L b),
          m ∈ oddResidualIn (L ⊓ centralizer ({b} : Set G)) →
            φ (⟨m, hmL⟩ : L) = (⟨m, hmb⟩ : footeFixed L b)) ∧
        ∀ d ∈ normalizer (L : Set G) ⊓ centralizer ({b} : Set G),
          ∀ (x x' : L) (y y' : footeFixed L b), (x' : G) = d * x * d⁻¹ →
            (y' : G) = d * y * d⁻¹ → φ x = y → φ x' = y' :=
  ⟨mem_coreActionKernel_footeFixed hbc hcL hLb,
    le_antisymm (footeFixed_footeFixed_le hLB hb hc hbc hcL.1 hLc)
      (footeFixed_le_footeFixed_footeFixed hL hb hc hbc hbL hcL hLc),
    exists_quotient_mulEquiv_footeFixed hL hb hbL hLb⟩

end CFSG.ComponentClassification.FooteLit
