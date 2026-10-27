module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.B68Defs
public import CFSG.GroupTheory.FixedPointCount

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteen

open Subgroup CFSG.EvenSporadicStandard.HypOne.BabyHyp.B68

@[expose] def Cap13 {G : Type} [Group G] (N : Fin 4 → ℕ) : Prop :=
  ∀ {u x : G}, Inv N 0 u → orderOf x = 13 → u * x = x * u →
    Nat.card (centralizer ({u} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 52

structure Arith13 (N sz : Fin 4 → ℕ) : Prop where
  nsq : ¬ 13 ^ 2 ∣ N 0
  dvd0 : 13 ∣ sz 0
  dvd3 : 13 ∣ sz 3

section Sylow

theorem exists_pow_six_pow_mod (j : ℕ) (hj : 0 < j) (hj13 : j < 13) :
    ∃ m : ℕ, 6 ^ m % 13 = j := by
  have key : ∀ j : Fin 13, 0 < j.val → ∃ m : Fin 12, 6 ^ m.val % 13 = j.val := by decide
  obtain ⟨m, hm⟩ := key ⟨j, hj13⟩ hj
  exact ⟨m, hm⟩

theorem conj_pow_six_pow {S : Type*} [Group S] {t n : S} (hn : n * t * n⁻¹ = t ^ 6) (m : ℕ) :
    n ^ m * t * (n ^ m)⁻¹ = t ^ (6 ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc n ^ (m + 1) * t * (n ^ (m + 1))⁻¹ = n * (n ^ m * t * (n ^ m)⁻¹) * n⁻¹ := by
          rw [pow_succ']; group
      _ = n * t ^ (6 ^ m) * n⁻¹ := by rw [ih]
      _ = (n * t * n⁻¹) ^ (6 ^ m) := conj_pow.symm
      _ = (t ^ 6) ^ (6 ^ m) := by rw [hn]
      _ = t ^ (6 ^ (m + 1)) := by rw [← pow_mul, pow_succ, mul_comm]

theorem isConj_of_orderOf_thirteen {S : Type*} [Group S] [Finite S]
    (hS : ¬ 13 ^ 2 ∣ Nat.card S) {t n : S} (ht : orderOf t = 13) (hn : n * t * n⁻¹ = t ^ 6)
    {h : S} (hh : orderOf h = 13) : IsConj t h := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨P, hP⟩ := CFSG.Monster.Existence.StdOdd.Cert.exists_sylow_eq_of_card_eq_prime hS
    (zpowers t) (by rw [Nat.card_zpowers, ht])
  have hhp : IsPGroup 13 (zpowers h) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hh, pow_one])
  obtain ⟨σ, hσ⟩ := CFSG.Monster.Existence.StdOdd.Cert.exists_conj_mem_sylow P hhp
  rw [hP] at hσ
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hσ
  have hlt : j % 13 < 13 := Int.emod_lt_of_pos j (by norm_num)
  have hnn : 0 ≤ j % 13 := Int.emod_nonneg j (by norm_num)
  obtain ⟨j', hj'⟩ := Int.eq_ofNat_of_zero_le hnn
  have htj : t ^ j = t ^ j' := by
    have := zpow_mod_orderOf t j
    rw [ht] at this
    rw [← this]
    have e : j % ((13 : ℕ) : ℤ) = j' := hj'
    rw [e, zpow_natCast]
  have hj'lt : j' < 13 := by omega
  have hj0 : j' ≠ 0 := by
    rintro rfl
    have h1 : σ⁻¹ * h * σ = 1 := by rw [← hj, htj]; simp
    have hh1 : h = 1 := by
      have := congrArg (fun z => σ * z * σ⁻¹) h1
      simpa [mul_assoc] using this
    rw [hh1, orderOf_one] at hh
    omega
  obtain ⟨m, hm⟩ := exists_pow_six_pow_mod j' (Nat.pos_of_ne_zero hj0) hj'lt
  have hconj : n ^ m * t * (n ^ m)⁻¹ = σ⁻¹ * h * σ := by
    rw [conj_pow_six_pow hn m, ← hj, htj, ← pow_mod_orderOf, ht, hm]
  have h1 : IsConj t (σ⁻¹ * h * σ) := isConj_iff.2 ⟨n ^ m, hconj⟩
  have h2 : IsConj (σ⁻¹ * h * σ) h := isConj_iff.2 ⟨σ, by group⟩
  exact h1.trans h2

theorem thirteen_mul_card_isConj_le {S : Type*} [Group S] [Finite S] {t : S}
    (ht : orderOf t = 13) : 13 * Nat.card {h : S // IsConj t h} ≤ Nat.card S := by
  have h1 := Subgroup.index_mul_card (centralizer ({t} : Set S))
  rw [Subgroup.index_centralizer_eq_ncard] at h1
  have h2 : 13 ≤ Nat.card (centralizer ({t} : Set S)) := by
    rw [← ht, ← Nat.card_zpowers]
    exact Subgroup.card_le_of_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have h3 : (conjugatesOf t).ncard = Nat.card {h : S // IsConj t h} := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [h3] at h1
  calc 13 * Nat.card {h : S // IsConj t h} ≤ Nat.card (centralizer ({t} : Set S)) *
        Nat.card {h : S // IsConj t h} := Nat.mul_le_mul_right _ h2
    _ = Nat.card S := by rw [mul_comm]; exact h1

end Sylow

section Fix

theorem card_fix_le_four {Γ X : Type*} [Group Γ] [Finite Γ] [MulAction Γ X]
    [MulAction.IsPretransitive Γ X] (x₀ : X) {t n : Γ} (ht : orderOf t = 13)
    (htx : t • x₀ = x₀) (hnx : n • x₀ = x₀) (hn : n * t * n⁻¹ = t ^ 6)
    (hS : ¬ 13 ^ 2 ∣ Nat.card (MulAction.stabilizer Γ x₀))
    (hC : Nat.card (centralizer ({t} : Set Γ)) ≤ 52) :
    Nat.card {y : X // t • y = y} ≤ 4 := by
  have hf := CFSG.GroupAction.card_fix_mul_card_stabilizer x₀ t
  set S := MulAction.stabilizer Γ x₀ with hSdef
  have htS : t ∈ S := htx
  have hnS : n ∈ S := hnx
  let t' : S := ⟨t, htS⟩
  let n' : S := ⟨n, hnS⟩
  have ht' : orderOf t' = 13 := by rw [← ht]; exact Subgroup.orderOf_mk _ _
  have hn' : n' * t' * n'⁻¹ = t' ^ 6 := Subtype.ext hn
  have hclass := thirteen_mul_card_isConj_le ht'
  have key : ∀ h : {h : Γ // h ∈ S ∧ IsConj t h}, IsConj t' (⟨h.1, h.2.1⟩ : S) := by
    intro h
    refine isConj_of_orderOf_thirteen hS ht' hn' ?_
    have h13 : orderOf h.1 = 13 := by
      obtain ⟨c, hc⟩ := isConj_iff.1 h.2.2
      rw [← hc, orderOf_conj_eq, ht]
    rw [Subgroup.orderOf_mk]
    exact h13
  have hinj : Nat.card {h : Γ // h ∈ S ∧ IsConj t h} ≤ Nat.card {h : S // IsConj t' h} := by
    refine Nat.card_le_card_of_injective (fun h => ⟨⟨h.1, h.2.1⟩, key h⟩) ?_
    intro a b hab
    have := congrArg (fun z : {h : S // IsConj t' h} => ((z.1 : S) : Γ)) hab
    exact Subtype.ext this
  have hspos : 0 < Nat.card S := Nat.card_pos
  set F := Nat.card {y : X // t • y = y} with hF
  set s := Nat.card S with hs
  set c := Nat.card (centralizer ({t} : Set Γ)) with hc
  set m := Nat.card {h : Γ // h ∈ S ∧ IsConj t h} with hm
  set m' := Nat.card {h : S // IsConj t' h} with hm'
  have h1 : 13 * F * s ≤ 52 * s := by
    calc 13 * F * s = 13 * (F * s) := by ring
      _ = 13 * (c * m) := by rw [hf]
      _ ≤ 13 * (52 * m') := by gcongr
      _ = 52 * (13 * m') := by ring
      _ ≤ 52 * s := by gcongr
  have h2 := Nat.le_of_mul_le_mul_right h1 hspos
  omega

end Fix

section Orbit

variable {G : Type} [Group G] [Finite G] {N sz : Fin 4 → ℕ}

@[expose, instance_reducible] def conjAction (Γ : Subgroup G) (O : Set G)
    (hO : ∀ g ∈ Γ, ∀ s ∈ O, g * s * g⁻¹ ∈ O) : MulAction Γ O :=
  { smul := fun g s => ⟨(g : G) * (s : G) * (g : G)⁻¹, hO g g.2 s s.2⟩
    one_smul := fun s => Subtype.ext (by
      show ((1 : Γ) : G) * (s : G) * ((1 : Γ) : G)⁻¹ = s
      simp)
    mul_smul := fun g h s => Subtype.ext (by
      show ((g * h : Γ) : G) * (s : G) * ((g * h : Γ) : G)⁻¹ =
        (g : G) * ((h : G) * (s : G) * (h : G)⁻¹) * (g : G)⁻¹
      simp [mul_assoc]) }

theorem not_commute_of_dvd (hT4 : TableIV (G := G) N sz) (hnsq : ¬ 13 ^ 2 ∣ N 0) {k : Fin 4}
    (hk : 13 ∣ sz k) {r s x : G} (hr : Inv N 0 r) (hs : Inv N 0 s) (hso : Orb N k r s)
    (hx : orderOf x = 13) (hxr : x * r = r * x) (hxs : x * s = s * x) : False := by
  obtain ⟨-, hconj, hcard⟩ := hT4 r hr
  have hO : ∀ h ∈ centralizer ({r} : Set G), h * s * h⁻¹ ∈ {s | Inv N 0 s ∧ Orb N k r s} := by
    intro h hh
    have hh' : h * r = r * h := mem_centralizer_singleton_iff.1 hh
    exact ⟨Inv.of_isConj hs (isConj_iff.2 ⟨h, rfl⟩), Orb.conj hh' hso⟩
  have htr : ∀ s' ∈ {s | Inv N 0 s ∧ Orb N k r s},
      ∃ h ∈ centralizer ({r} : Set G), h * s * h⁻¹ = s' :=
    fun s' hs' => hconj k s s' hs hs'.1 hso hs'.2
  have hmul := card_inf_centralizer_mul_ncard_of_orbit (centralizer ({r} : Set G)) s _ hO htr
  rw [hcard k, hr.2] at hmul
  have hxmem : x ∈ (centralizer ({r} : Set G) ⊓ centralizer ({s} : Set G) : Subgroup G) :=
    ⟨mem_centralizer_singleton_iff.2 hxr, mem_centralizer_singleton_iff.2 hxs⟩
  have hdvd := Subgroup.orderOf_dvd_natCard _ hxmem
  rw [hx] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  obtain ⟨m, hm⟩ := hk
  apply hnsq
  exact ⟨c * m, by rw [← hmul, hc, hm]; ring⟩

theorem ncard_fix_le_four (hT4 : TableIV (G := G) N sz) (hnsq : ¬ 13 ^ 2 ∣ N 0)
    (hCap : Cap13 (G := G) N) {k : Fin 4} {r s₀ x g : G} (hr : Inv N 0 r) (hs₀ : Inv N 0 s₀)
    (hk : Orb N k r s₀) (hx : orderOf x = 13) (hxr : x * r = r * x) (hxs : x * s₀ = s₀ * x)
    (hgr : g * r = r * g) (hgs : g * s₀ = s₀ * g) (hgx : g * x * g⁻¹ = x ^ 6) :
    {s : G | Inv N 0 s ∧ Orb N k r s ∧ x * s = s * x}.ncard ≤ 4 := by
  obtain ⟨-, hconj, hcard⟩ := hT4 r hr
  set Γ : Subgroup G := centralizer ({r} : Set G) with hΓ
  set O : Set G := {s | Inv N 0 s ∧ Orb N k r s} with hOdef
  have hO : ∀ g ∈ Γ, ∀ s ∈ O, g * s * g⁻¹ ∈ O := by
    intro g hg s hs
    have hg' : g * r = r * g := mem_centralizer_singleton_iff.1 hg
    exact ⟨Inv.of_isConj hs.1 (isConj_iff.2 ⟨g, rfl⟩), Orb.conj hg' hs.2⟩
  letI : MulAction Γ O := conjAction Γ O hO
  have htrans : MulAction.IsPretransitive Γ O := ⟨fun s s' => by
    obtain ⟨c, hc, hcs⟩ := hconj k s s' s.2.1 s'.2.1 s.2.2 s'.2.2
    exact ⟨⟨c, hc⟩, Subtype.ext hcs⟩⟩
  let x₀ : O := ⟨s₀, hs₀, hk⟩
  let t : Γ := ⟨x, mem_centralizer_singleton_iff.2 hxr⟩
  let n : Γ := ⟨g, mem_centralizer_singleton_iff.2 hgr⟩
  have ht : orderOf t = 13 := by rw [← hx]; exact Subgroup.orderOf_mk _ _
  have htx : t • x₀ = x₀ := by
    apply Subtype.ext
    show x * s₀ * x⁻¹ = s₀
    rw [mul_inv_eq_iff_eq_mul]
    exact hxs
  have hnx : n • x₀ = x₀ := by
    apply Subtype.ext
    show g * s₀ * g⁻¹ = s₀
    rw [mul_inv_eq_iff_eq_mul]
    exact hgs
  have hn : n * t * n⁻¹ = t ^ 6 := Subtype.ext hgx
  have hcardO : Nat.card O = sz k := by rw [Nat.card_coe_set_eq]; exact hcard k
  have hS : ¬ 13 ^ 2 ∣ Nat.card (MulAction.stabilizer Γ x₀) := by
    intro h
    apply hnsq
    have h1 := Subgroup.index_mul_card (MulAction.stabilizer Γ x₀)
    rw [MulAction.index_stabilizer_of_transitive Γ x₀, hcardO] at h1
    have h2 : Nat.card Γ = N 0 := hr.2
    rw [h2] at h1
    rw [← h1]
    exact Dvd.dvd.mul_left h _
  have hC : Nat.card (centralizer ({t} : Set Γ)) ≤ 52 := by
    refine le_trans ?_ (hCap hr hx hxr.symm)
    refine Nat.card_le_card_of_injective
      (fun c => (⟨(c.1 : G), c.1.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 c.2))⟩ :
          ↥(Γ ⊓ centralizer ({x} : Set G) : Subgroup G))) ?_
    intro a b hab
    have := congrArg (fun z : ↥(Γ ⊓ centralizer ({x} : Set G) : Subgroup G) => (z : G)) hab
    exact Subtype.ext (Subtype.ext this)
  have hfix := card_fix_le_four x₀ ht htx hnx hn hS hC
  have hconv : Nat.card {y : O // t • y = y} =
      {s : G | Inv N 0 s ∧ Orb N k r s ∧ x * s = s * x}.ncard := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr ?_
    exact
      { toFun := fun y => ⟨y.1.1, y.1.2.1, y.1.2.2, by
          have h := congrArg Subtype.val y.2
          exact mul_inv_eq_iff_eq_mul.1 h⟩
        invFun := fun s => ⟨⟨s.1, s.2.1, s.2.2.1⟩, by
          apply Subtype.ext
          show x * s.1 * x⁻¹ = s.1
          rw [mul_inv_eq_iff_eq_mul]
          exact s.2.2.2⟩
        left_inv := fun y => rfl
        right_inv := fun s => rfl }
  rw [← hconv]
  exact hfix

theorem ncard_commuting_le (hA : Arith13 N sz) (hT4 : TableIV (G := G) N sz)
    (hCap : Cap13 (G := G) N) {x r r' s₂ g : G} (hx : orderOf x = 13) (hr : Inv N 0 r)
    (hr' : Inv N 0 r') (hs₂ : Inv N 0 s₂) (hxr : x * r = r * x) (hxr' : x * r' = r' * x)
    (hxs₂ : x * s₂ = s₂ * x) (hrr' : r * r' = r' * r) (hne : r' ≠ r)
    (hrs₂ : orderOf (r * s₂) = 3) (hgr : g * r = r * g) (hgr' : g * r' = r' * g)
    (hgs₂ : g * s₂ = s₂ * g) (hgx : g * x * g⁻¹ = x ^ 6) :
    {s : G | Inv N 0 s ∧ s * x = x * s}.ncard ≤ 9 := by
  obtain ⟨hcov, -, -⟩ := hT4 r hr
  let Fk : Fin 4 → Set G := fun k => {s | Inv N 0 s ∧ Orb N k r s ∧ x * s = s * x}
  have hF0 : Fk 0 = ∅ := Set.eq_empty_of_forall_notMem fun s hs =>
    not_commute_of_dvd hT4 hA.nsq hA.dvd0 hr hs.1 hs.2.1 hx hxr hs.2.2
  have hF3 : Fk 3 = ∅ := Set.eq_empty_of_forall_notMem fun s hs =>
    not_commute_of_dvd hT4 hA.nsq hA.dvd3 hr hs.1 hs.2.1 hx hxr hs.2.2
  have hrr'2 : (r * r') ^ 2 = 1 := by
    rw [pow_two]
    calc r * r' * (r * r') = r * (r' * r) * r' := by group
      _ = r * (r * r') * r' := by rw [hrr']
      _ = (r * r) * (r' * r') := by group
      _ = 1 := by rw [hr.mul_self, hr'.mul_self, one_mul]
  have hord2 : orderOf (r * r') ∣ 2 := orderOf_dvd_of_pow_eq_one hrr'2
  have hr'1 : Orb N 1 r r' := by
    obtain ⟨k, hk⟩ := hcov r' hr' hne
    fin_cases k
    · exfalso
      have : r' ∈ Fk 0 := ⟨hr', hk, hxr'⟩
      rw [hF0] at this
      exact this
    · exact hk
    · exfalso
      have h3 : orderOf (r * r') = 3 := hk
      rw [h3] at hord2
      omega
    · exfalso
      have h4 : orderOf (r * r') = 4 ∧ Inv N 1 ((r * r') ^ 2) := hk
      rw [h4.1] at hord2
      omega
  have h1 := ncard_fix_le_four hT4 hA.nsq hCap hr hr' hr'1 hx hxr hxr' hgr hgr' hgx
  have hk2 : Orb N 2 r s₂ := hrs₂
  have h2 := ncard_fix_le_four hT4 hA.nsq hCap hr hs₂ hk2 hx hxr hxs₂ hgr hgs₂ hgx
  have hsub : {s : G | Inv N 0 s ∧ s * x = x * s} ⊆ {r} ∪ Fk 0 ∪ Fk 1 ∪ Fk 2 ∪ Fk 3 := by
    intro s hs
    by_cases hsr : s = r
    · left; left; left; left
      exact hsr
    · obtain ⟨k, hk⟩ := hcov s hs.1 hsr
      have hmem : s ∈ Fk k := ⟨hs.1, hk, hs.2.symm⟩
      fin_cases k
      · left; left; left; right; exact hmem
      · left; left; right; exact hmem
      · left; right; exact hmem
      · right; exact hmem
  calc {s : G | Inv N 0 s ∧ s * x = x * s}.ncard
      ≤ ({r} ∪ Fk 0 ∪ Fk 1 ∪ Fk 2 ∪ Fk 3).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ({r} ∪ Fk 0 ∪ Fk 1 ∪ Fk 2).ncard + (Fk 3).ncard := Set.ncard_union_le _ _
    _ ≤ ({r} ∪ Fk 0 ∪ Fk 1).ncard + (Fk 2).ncard + (Fk 3).ncard := by
        gcongr; exact Set.ncard_union_le _ _
    _ ≤ ({r} ∪ Fk 0).ncard + (Fk 1).ncard + (Fk 2).ncard + (Fk 3).ncard := by
        gcongr; exact Set.ncard_union_le _ _
    _ ≤ ({r} : Set G).ncard + (Fk 0).ncard + (Fk 1).ncard + (Fk 2).ncard + (Fk 3).ncard := by
        gcongr; exact Set.ncard_union_le _ _
    _ ≤ 9 := by
        rw [hF0, hF3, Set.ncard_empty, Set.ncard_singleton]
        have h1' : (Fk 1).ncard ≤ 4 := h1
        have h2' : (Fk 2).ncard ≤ 4 := h2
        omega

end Orbit

section Cosets

variable {G : Type} [Group G] [Finite G] {N : Fin 4 → ℕ}

theorem conj_eq_inv_of_trivial_inf {K : Subgroup G} {y : G}
    (hyK : ∀ k ∈ K, y * k * y⁻¹ ∈ K) (hy2 : y * y = 1)
    (hfix : ∀ k ∈ K, k * y = y * k → k = 1) {k : G} (hk : k ∈ K) : y * k * y⁻¹ = k⁻¹ := by
  let φ : K →* K :=
    { toFun := fun a => ⟨y * a * y⁻¹, hyK a a.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hφ : MonoidHom.FixedPointFree φ := by
    intro a ha
    have h : y * (a : G) * y⁻¹ = a := congrArg Subtype.val ha
    apply Subtype.ext
    apply hfix a a.2
    calc (a : G) * y = y * a * y⁻¹ * y := by rw [h]
      _ = y * a := by group
  have hinv : Function.Involutive φ := by
    intro a
    apply Subtype.ext
    change y * (y * (a : G) * y⁻¹) * y⁻¹ = a
    have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    rw [hy]
    calc y * (y * (a : G) * y) * y = (y * y) * a * (y * y) := by group
      _ = a := by rw [hy2]; group
  have h := congrFun (MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hφ hinv) ⟨k, hk⟩
  exact congrArg Subtype.val h

theorem inf_centralizer_eq_bot (hCap : Cap13 (G := G) N) {x t : G} (hx : orderOf x = 13)
    (ht : Inv N 0 t) (htx : t * x = x * t) {K : Subgroup G}
    (hKx : K ≤ centralizer ({x} : Set G)) (hodd : Odd (Nat.card K)) (h13 : ¬ 13 ∣ Nat.card K) :
    K ⊓ centralizer ({t} : Set G) = ⊥ := by
  have hD := hCap ht hx htx
  set D : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) with hDdef
  have hxD : x ∈ D :=
    ⟨mem_centralizer_singleton_iff.2 htx.symm, mem_centralizer_singleton_iff.2 rfl⟩
  have htD : t ∈ D := ⟨mem_centralizer_singleton_iff.2 rfl, mem_centralizer_singleton_iff.2 htx⟩
  have h13D : 13 ∣ Nat.card D := hx ▸ Subgroup.orderOf_dvd_natCard D hxD
  have h2D : 2 ∣ Nat.card D := ht.1 ▸ Subgroup.orderOf_dvd_natCard D htD
  have h26 : 26 ∣ Nat.card D := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 13) h2D h13D
    simpa using this
  set c := Nat.card ↥(K ⊓ centralizer ({t} : Set G)) with hc
  have hle : K ⊓ centralizer ({t} : Set G) ≤ D := fun g hg => ⟨hg.2, hKx hg.1⟩
  have hcD : c ∣ Nat.card D := Subgroup.card_dvd_of_le hle
  have hcK : c ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_left
  have hcodd : Odd c := Odd.of_dvd_nat hodd hcK
  have hc13 : ¬ 13 ∣ c := fun h => h13 (h.trans hcK)
  have hc2 : ¬ 2 ∣ c := by
    obtain ⟨a, ha⟩ := hcodd
    omega
  have hcop : Nat.Coprime 26 c := by
    have h2 : Nat.Coprime 2 c := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hc2
    have h13' : Nat.Coprime 13 c := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hc13
    exact (Nat.Coprime.mul_right h2.symm h13'.symm).symm
  have h26c : 26 * c ∣ Nat.card D := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h26 hcD
  have hle52 : 26 * c ≤ 52 := (Nat.le_of_dvd Nat.card_pos h26c).trans hD
  have hc1 : c = 1 := by
    obtain ⟨a, ha⟩ := hcodd
    omega
  exact Subgroup.eq_bot_of_card_eq _ hc1

theorem coset_mem {x t : G} {K : Subgroup G} (ht : Inv N 0 t) (htx : t * x = x * t)
    (hKx : K ≤ centralizer ({x} : Set G)) (hodd : Odd (Nat.card K))
    (hinv : ∀ k ∈ K, t * k * t⁻¹ = k⁻¹) {k : G} (hk : k ∈ K) :
    Inv N 0 (t * k) ∧ t * k * x = x * (t * k) := by
  obtain ⟨a, ha⟩ := hodd
  let k' : K := ⟨k, hk⟩
  have hpow : k' ^ (2 * a + 1) = 1 := by rw [← ha]; exact pow_card_eq_one'
  let m : G := ((k' ^ (a + 1) : K) : G)
  have hm : m ∈ K := (k' ^ (a + 1)).2
  have hmm : m * m = k := by
    have h1 : k' ^ (a + 1) * k' ^ (a + 1) = k' := by
      rw [← pow_add]
      have e : a + 1 + (a + 1) = (2 * a + 1) + 1 := by ring
      rw [e, pow_succ, hpow, one_mul]
    exact congrArg Subtype.val h1
  have hmi : t * m * t⁻¹ = m⁻¹ := hinv m hm
  have hki : t * k * t⁻¹ = k⁻¹ := hinv k hk
  have e : t * k = m⁻¹ * t * m := by
    have h1 : t * k = k⁻¹ * t := by
      have := hki
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have h2 : t * m = m⁻¹ * t := by
      have := hmi
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    calc t * k = k⁻¹ * t := h1
      _ = (m * m)⁻¹ * t := by rw [hmm]
      _ = m⁻¹ * (m⁻¹ * t) := by group
      _ = m⁻¹ * (t * m) := by rw [h2]
      _ = m⁻¹ * t * m := by group
  refine ⟨?_, ?_⟩
  · rw [e]
    exact Inv.of_isConj ht (isConj_iff.2 ⟨m⁻¹, by rw [inv_inv]⟩)
  · exact commute_mul_of_commute htx (mem_centralizer_singleton_iff.1 (hKx hk))

theorem card_mul_card_le {ι : Type*} [Fintype ι] {x : G} {t : ι → G} {K : Subgroup G}
    (ht : ∀ i, Inv N 0 (t i)) (htx : ∀ i, t i * x = x * t i)
    (hKx : K ≤ centralizer ({x} : Set G)) (hodd : Odd (Nat.card K))
    (hinv : ∀ i, ∀ k ∈ K, t i * k * (t i)⁻¹ = k⁻¹) (hdis : ∀ i j, i ≠ j → t j * t i ∉ K) :
    Fintype.card ι * Nat.card K ≤ {s : G | Inv N 0 s ∧ s * x = x * s}.ncard := by
  let f : ι × K → {s : G | Inv N 0 s ∧ s * x = x * s} := fun p =>
    ⟨t p.1 * p.2, coset_mem (ht p.1) (htx p.1) hKx hodd (hinv p.1) p.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨i, k⟩ ⟨j, k'⟩ h
    have h' : t i * (k : G) = t j * (k' : G) := congrArg Subtype.val h
    by_cases hij : i = j
    · subst hij
      exact Prod.ext rfl (Subtype.ext (mul_left_cancel h'))
    · exfalso
      apply hdis i j hij
      have e : t j * t i = (k' : G) * (k : G)⁻¹ := by
        calc t j * t i = t j * (t i * k) * (k : G)⁻¹ := by group
          _ = t j * (t j * k') * (k : G)⁻¹ := by rw [h']
          _ = (t j * t j) * k' * (k : G)⁻¹ := by group
          _ = (k' : G) * (k : G)⁻¹ := by rw [(ht j).mul_self, one_mul]
      rw [e]
      exact K.mul_mem k'.2 (K.inv_mem k.2)
  have h := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := ι), Nat.card_coe_set_eq] at h
  exact h

theorem mul_not_mem_of_ne {K : Subgroup G} {a b l : G} (ha : a * a = 1) (hb : b * b = 1)
    (hl : l * l = 1) (hlK : ∀ k ∈ K, l * k * l⁻¹ = k⁻¹) (hne : l * b * a * l ≠ a * b) :
    b * a ∉ K ∧ a * b ∉ K := by
  have hl' : l⁻¹ = l := inv_eq_of_mul_eq_one_right hl
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have key : b * a ∉ K := by
    intro hba
    apply hne
    have := hlK _ hba
    rw [hl', mul_inv_rev, ha', hb'] at this
    calc l * b * a * l = l * (b * a) * l := by group
      _ = a * b := this
  refine ⟨key, fun hab => key ?_⟩
  have := K.inv_mem hab
  rwa [mul_inv_rev, ha', hb'] at this

end Cosets

section Main

variable {G : Type} [Group G] [Finite G] {N sz : Fin 4 → ℕ}

theorem eq_bot_of_data (hA : Arith13 N sz) (hT4 : TableIV (G := G) N sz) (hCap : Cap13 (G := G) N)
    {x t1 t2 t4 t5 g : G} (hx : orderOf x = 13)
    (h1 : Inv N 0 t1) (h2 : Inv N 0 t2) (h4 : Inv N 0 t4) (h5 : Inv N 0 t5)
    (c1 : t1 * x = x * t1) (c2 : t2 * x = x * t2) (c4 : t4 * x = x * t4)
    (c5 : t5 * x = x * t5) (h15 : t1 * t5 = t5 * t1) (hne15 : t5 ≠ t1)
    (h12 : orderOf (t1 * t2) = 3) (hgx : g * x * g⁻¹ = x ^ 6) (hg1 : g * t1 = t1 * g)
    (hg2 : g * t2 = t2 * g) (hg5 : g * t5 = t5 * g)
    (w12 : t4 * t2 * t1 * t4 ≠ t1 * t2) (w14 : t2 * t4 * t1 * t2 ≠ t1 * t4)
    (w15 : t2 * t5 * t1 * t2 ≠ t1 * t5) (w24 : t1 * t4 * t2 * t1 ≠ t2 * t4)
    (w25 : t1 * t5 * t2 * t1 ≠ t2 * t5) (w45 : t1 * t5 * t4 * t1 ≠ t4 * t5)
    {K : Subgroup G} (hKx : K ≤ centralizer ({x} : Set G))
    (hKn : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hodd : Odd (Nat.card K)) (h13 : ¬ 13 ∣ Nat.card K) : K = ⊥ := by
  have hinv : ∀ u : G, Inv N 0 u → u * x = x * u → ∀ k ∈ K, u * k * u⁻¹ = k⁻¹ := by
    intro u hu hux k hk
    have hbot := inf_centralizer_eq_bot hCap hx hu hux hKx hodd h13
    refine conj_eq_inv_of_trivial_inf (K := K) (fun k hk => hKn u
      (mem_centralizer_singleton_iff.2 hux) k hk) hu.mul_self (fun k hk hku => ?_) hk
    have : k ∈ K ⊓ centralizer ({u} : Set G) := ⟨hk, mem_centralizer_singleton_iff.2 hku⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  have i1 := hinv t1 h1 c1
  have i2 := hinv t2 h2 c2
  have i4 := hinv t4 h4 c4
  have i5 := hinv t5 h5 c5
  have p12 := mul_not_mem_of_ne (K := K) (a := t1) (b := t2) (l := t4) h1.mul_self h2.mul_self
    h4.mul_self i4 w12
  have p14 := mul_not_mem_of_ne (K := K) (a := t1) (b := t4) (l := t2) h1.mul_self h4.mul_self
    h2.mul_self i2 w14
  have p15 := mul_not_mem_of_ne (K := K) (a := t1) (b := t5) (l := t2) h1.mul_self h5.mul_self
    h2.mul_self i2 w15
  have p24 := mul_not_mem_of_ne (K := K) (a := t2) (b := t4) (l := t1) h2.mul_self h4.mul_self
    h1.mul_self i1 w24
  have p25 := mul_not_mem_of_ne (K := K) (a := t2) (b := t5) (l := t1) h2.mul_self h5.mul_self
    h1.mul_self i1 w25
  have p45 := mul_not_mem_of_ne (K := K) (a := t4) (b := t5) (l := t1) h4.mul_self h5.mul_self
    h1.mul_self i1 w45
  let t : Fin 4 → G := ![t1, t2, t4, t5]
  have hdis : ∀ i j, i ≠ j → t j * t i ∉ K := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | exact p12.1 | exact p12.2 | exact p14.1 | exact p14.2 | exact p15.1 | exact p15.2
      | exact p24.1 | exact p24.2 | exact p25.1 | exact p25.2 | exact p45.1 | exact p45.2
  have hcard := card_mul_card_le (ι := Fin 4) (x := x) (t := t) (K := K)
    (fun i => by fin_cases i <;> assumption) (fun i => by fin_cases i <;> assumption) hKx hodd
    (fun i => by fin_cases i <;> assumption) hdis
  have hF := ncard_commuting_le hA hT4 hCap hx h1 h5 h2 c1.symm c5.symm c2.symm h15 hne15 h12
    hg1 hg5 hg2 hgx
  rw [Fintype.card_fin] at hcard
  have hle : Nat.card K ≤ 2 := by omega
  obtain ⟨a, ha⟩ := hodd
  exact Subgroup.eq_bot_of_card_eq _ (by omega)

theorem eq_bot_of_conj {G : Type} [Group G] [Finite G] (hp2 : ¬ 13 ^ 2 ∣ Nat.card G)
    {x₀ x : G} (hx₀ : orderOf x₀ = 13) (hx : orderOf x = 13)
    (H : ∀ K : Subgroup G, K ≤ centralizer ({x₀} : Set G) →
      (∀ c ∈ centralizer ({x₀} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) → Odd (Nat.card K) →
      ¬ 13 ∣ Nat.card K → K = ⊥)
    {K : Subgroup G} (hKx : K ≤ centralizer ({x} : Set G))
    (hKn : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hodd : Odd (Nat.card K)) (h13 : ¬ 13 ∣ Nat.card K) : K = ⊥ := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨S, hS⟩ := CFSG.Monster.Existence.StdOdd.Cert.exists_sylow_eq_of_card_eq_prime hp2
    (zpowers x) (by rw [Nat.card_zpowers, hx])
  have hx₀p : IsPGroup 13 (zpowers x₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx₀, pow_one])
  obtain ⟨g, hg⟩ := CFSG.Monster.Existence.StdOdd.Cert.exists_conj_mem_sylow S hx₀p
  rw [hS] at hg
  have hyo : orderOf (g⁻¹ * x₀ * g) = orderOf x := by
    rw [CFSG.Monster.Existence.StdOdd.Cert.orderOf_inv_mul_mul, hx₀, hx]
  have hC := CFSG.Monster.Existence.StdOdd.Cert.centralizer_singleton_eq_of_mem_zpowers hg hyo
  let K' : Subgroup G := K.map (MulAut.conj g).toMonoidHom
  have hmem : ∀ k : G, k ∈ K → g * k * g⁻¹ ∈ K' := fun k hk =>
    Subgroup.mem_map.2 ⟨k, hk, rfl⟩
  have hKy : ∀ k ∈ K, k * (g⁻¹ * x₀ * g) = (g⁻¹ * x₀ * g) * k := fun k hk => by
    have := hKx hk
    rw [← hC] at this
    exact mem_centralizer_singleton_iff.1 this
  have hK'x₀ : K' ≤ centralizer ({x₀} : Set G) := by
    intro k' hk'
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hk'
    rw [mem_centralizer_singleton_iff]
    show g * k * g⁻¹ * x₀ = x₀ * (g * k * g⁻¹)
    calc g * k * g⁻¹ * x₀ = g * (k * (g⁻¹ * x₀ * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x₀ * g) * k) * g⁻¹ := by rw [hKy k hk]
      _ = x₀ * (g * k * g⁻¹) := by group
  have hK'n : ∀ c ∈ centralizer ({x₀} : Set G), ∀ k ∈ K', c * k * c⁻¹ ∈ K' := by
    intro c hc k' hk'
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hk'
    have hcx : c * x₀ = x₀ * c := mem_centralizer_singleton_iff.1 hc
    have hc' : g⁻¹ * c * g ∈ centralizer ({x} : Set G) := by
      rw [← hC, mem_centralizer_singleton_iff]
      calc g⁻¹ * c * g * (g⁻¹ * x₀ * g) = g⁻¹ * (c * x₀) * g := by group
        _ = g⁻¹ * (x₀ * c) * g := by rw [hcx]
        _ = g⁻¹ * x₀ * g * (g⁻¹ * c * g) := by group
    have := hmem _ (hKn _ hc' k hk)
    convert this using 1
    show c * (g * k * g⁻¹) * c⁻¹ = g * (g⁻¹ * c * g * k * (g⁻¹ * c * g)⁻¹) * g⁻¹
    group
  have hcard : Nat.card K' = Nat.card K :=
    (Nat.card_congr (Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv).symm
  have hbot := H K' hK'x₀ hK'n (hcard ▸ hodd) (hcard ▸ h13)
  refine (Subgroup.eq_bot_iff_forall K).2 fun k hk => ?_
  have := hmem k hk
  rw [hbot, Subgroup.mem_bot] at this
  have h2 : k = g⁻¹ * (g * k * g⁻¹) * g := by group
  rw [h2, this]
  group

end Main

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteen
