module

public import CFSG.GH74.Generic.BProg.B2.WeakSigGen
public import CFSG.Walter.J1Props.Aut
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG Subgroup

namespace WeakSigJ1

section Gen

variable {X : Type} [Group X]

theorem mem_zpowers_of_two {u a : X} (hu : orderOf u = 2) (ha : a ∈ zpowers u) : a = 1 ∨ a = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have h2 : ((orderOf u : ℕ) : ℤ) = 2 := by rw [hu]; rfl
  have hk := zpow_mod_orderOf u k
  rw [h2] at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left; rw [← hk, h0, zpow_zero]
  · right; rw [← hk, h1, zpow_one]

theorem mem_sup_of_commute {A B : Subgroup X}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {z : X} (hz : z ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, z = a * b := by
  have hA : A ≤ Subgroup.normalizer (B : Set X) := fun a ha =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun b hb => (h a ha b hb).symm)
  have := Subgroup.coe_mul_of_left_le_normalizer_right A B hA
  rw [← SetLike.mem_coe, this] at hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  exact ⟨a, ha, b, hb, rfl⟩

theorem mem_sup_zpowers_of_two {u : X} (hu2 : orderOf u = 2) {L : Subgroup X}
    (hLu : L ≤ centralizer ({u} : Set X)) {g : X} (hg : g ∈ zpowers u ⊔ L) :
    (∃ l ∈ L, g = l) ∨ ∃ l ∈ L, g = u * l := by
  have hcomm : ∀ a ∈ zpowers u, ∀ b ∈ L, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hbu : b * u = u * b := Subgroup.mem_centralizer_singleton_iff.1 (hLu hb)
    exact ((Commute.zpow_left (show Commute u b from hbu.symm) k).eq)
  obtain ⟨a, ha, l, hl, rfl⟩ := mem_sup_of_commute hcomm hg
  rcases mem_zpowers_of_two hu2 ha with rfl | rfl
  · exact Or.inl ⟨l, hl, by simp⟩
  · exact Or.inr ⟨l, hl, rfl⟩

end Gen

section Split

variable {J : Type} [Group J]

structure SplitCent (J : Type) [Group J] : Prop where
  simple : IsSimpleGroup J
  even : 2 ∣ Nat.card J
  center : ∀ z : J, (∀ g : J, g * z = z * g) → z = 1
  aut : ∀ φ : MulAut J, ∃ g : J, φ = MulAut.conj g
  split : ∀ u : J, orderOf u = 2 → ∃ F : Subgroup J, F ≤ centralizer ({u} : Set J) ∧ u ∉ F ∧
    centralizer ({u} : Set J) = zpowers u ⊔ F ∧ IsSimpleGroup ↥F ∧ (∃ a b : ↥F, a * b ≠ b * a) ∧
    2 ∣ Nat.card ↥F ∧
    ∀ f g : ↥F, f * f = 1 → f ≠ 1 → g * f = f * g → Odd (orderOf g) → g = 1

theorem odd_mem_of_mem_sup {u : J} (hu2 : orderOf u = 2) {F : Subgroup J}
    (hFc : F ≤ centralizer ({u} : Set J)) (huF : u ∉ F) {g : J} (hg : g ∈ zpowers u ⊔ F)
    (hodd : Odd (orderOf g)) : g ∈ F := by
  rcases mem_sup_zpowers_of_two hu2 hFc hg with ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩
  · exact hl
  · exfalso
    obtain ⟨k, hk⟩ := hodd
    have hcu : Commute u l := (Subgroup.mem_centralizer_singleton_iff.1 (hFc hl)).symm
    have hu2' : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
    have h1 : (u * l) ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
    rw [hcu.mul_pow, pow_succ u, pow_mul, hu2', one_pow, one_mul] at h1
    apply huF
    have : u = (l ^ (2 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact F.inv_mem (F.pow_mem hl _)

theorem noOddNormal_zpowers_sup {u : J} (hu2 : orderOf u = 2) {F : Subgroup J}
    (hFc : F ≤ centralizer ({u} : Set J)) (huF : u ∉ F) (hFs : IsSimpleGroup ↥F)
    (hFev : 2 ∣ Nat.card ↥F) : NoOddNormal (zpowers u ⊔ F) := by
  intro N hNH hodd hnorm
  have hNF : N ≤ F := by
    intro n hn
    have hord : Odd (orderOf n) :=
      Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hn)
    exact odd_mem_of_mem_sup hu2 hFc huF (hNH hn) hord
  have hN : (N.subgroupOf F).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNF]
    intro f hf
    exact hnorm f (Subgroup.mem_sup_right hf)
  rcases hFs.eq_bot_or_eq_top_of_normal (N.subgroupOf F) with hb | ht
  · rw [eq_bot_iff]
    intro n hn
    have hmem : (⟨n, hNF hn⟩ : ↥F) ∈ N.subgroupOf F := hn
    rw [hb, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
  · exfalso
    have hFN : F ≤ N := fun f hf => by
      have hmem : (⟨f, hf⟩ : ↥F) ∈ N.subgroupOf F := by rw [ht]; trivial
      exact hmem
    have hdvd : Nat.card ↥F ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hFN
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (hFev.trans hdvd))

theorem eq_one_of_commute_zpowers_sup {u : J} (hu2 : orderOf u = 2) {F : Subgroup J}
    (hFc : F ≤ centralizer ({u} : Set J)) (huF : u ∉ F)
    (hCeq : centralizer ({u} : Set J) = zpowers u ⊔ F) (hFs : IsSimpleGroup ↥F)
    (hFna : ∃ a b : ↥F, a * b ≠ b * a) {g : J} (hodd : Odd (orderOf g))
    (hg : ∀ x ∈ zpowers u ⊔ F, g * x = x * g) : g = 1 := by
  have hgu : g ∈ centralizer ({u} : Set J) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hg u (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
  rw [hCeq] at hgu
  have hgF : g ∈ F := odd_mem_of_mem_sup hu2 hFc huF hgu hodd
  have hZ : center ↥F = ⊥ := by
    have := hFs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥F) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hFna
      have : a ∈ center ↥F := by rw [h]; trivial
      exact hab (Subgroup.mem_center_iff.1 this b).symm
  have hmem : (⟨g, hgF⟩ : ↥F) ∈ center ↥F := by
    rw [Subgroup.mem_center_iff]
    intro f
    exact Subtype.ext (hg f (Subgroup.mem_sup_right f.2)).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

end Split

section Facts

variable {J : Type} [Group J]

theorem odd_of_commute_one {a b : J} (hab : Commute a b) (ha : a * a = 1) (hb : b * b = 1) :
    (a * b) * (a * b) = 1 := by
  rw [← sq, hab.mul_pow, sq, sq, ha, hb, one_mul]

theorem centralizer_facts (h : SplitCent J) (S0 : Subgroup J) (hS : ∀ g ∈ S0, g * g = 1)
    (hc : ∀ a ∈ S0, ∀ b ∈ S0, a * b = b * a) :
    NoOddNormal (centralizer (S0 : Set J)) ∧
      ∀ g : J, Odd (orderOf g) → (∀ x ∈ centralizer (S0 : Set J), g * x = x * g) → g = 1 := by
  have hS0C : ∀ s ∈ S0, s ∈ centralizer (S0 : Set J) := fun s hs => by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hc b hb s hs
  by_cases hbot : ∀ s ∈ S0, s = 1
  · have hC : centralizer (S0 : Set J) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [hbot s hs]
      simp
    rw [hC]
    refine ⟨?_, ?_⟩
    · intro N _ hodd hnorm
      have hN : N.Normal := ⟨fun n hn g => (mem_normalizer_iff.mp (hnorm g trivial) n).mp hn⟩
      have := h.simple
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
      · exact h1
      · exfalso
        rw [h1, Subgroup.card_top] at hodd
        exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h.even)
    · intro g _ hg
      exact h.center g (fun x => (hg x trivial).symm)
  · push Not at hbot
    obtain ⟨t, htS, ht1⟩ := hbot
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have htt : t * t = 1 := hS t htS
    have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact htt) ht1
    obtain ⟨F, hFc, htF, hCeq, hFs, hFna, hFev, hFodd⟩ := h.split t ht2
    have hCt : centralizer (S0 : Set J) ≤ centralizer ({t} : Set J) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htS)
    by_cases hS2 : ∃ s ∈ S0, s ≠ 1 ∧ s ≠ t
    · obtain ⟨s, hsS, hs1, hst⟩ := hS2
      have hodd_triv : ∀ n ∈ centralizer (S0 : Set J), Odd (orderOf n) → n = 1 := by
        intro n hn hodd
        have hnt : n ∈ zpowers t ⊔ F := hCeq ▸ hCt hn
        have hnF : n ∈ F := odd_mem_of_mem_sup ht2 hFc htF hnt hodd
        have hsC : s ∈ zpowers t ⊔ F :=
          hCeq ▸ (Subgroup.mem_centralizer_singleton_iff.mpr (hc s hsS t htS))
        have hsn : s * n = n * s := Subgroup.mem_centralizer_iff.mp hn s hsS
        have htn : t * n = n * t := Subgroup.mem_centralizer_iff.mp hn t htS
        obtain ⟨f, hfF, hf1, hff, hfn⟩ : ∃ f ∈ F, f ≠ 1 ∧ f * f = 1 ∧ f * n = n * f := by
          rcases mem_sup_zpowers_of_two ht2 hFc hsC with ⟨l, hl, hsl⟩ | ⟨l, hl, hsl⟩
          · refine ⟨s, hsl ▸ hl, hs1, hS s hsS, hsn⟩
          · have hf : t * s = l := by rw [hsl, ← mul_assoc, htt, one_mul]
            refine ⟨l, hl, ?_, ?_, ?_⟩
            · intro h1'
              apply hst
              have : t * s = t * t := by rw [hf, h1', htt]
              exact mul_left_cancel this
            · rw [← hf]
              exact odd_of_commute_one (hc t htS s hsS) htt (hS s hsS)
            · rw [← hf, mul_assoc, hsn, ← mul_assoc, htn, mul_assoc]
        have hF1 := hFodd ⟨f, hfF⟩ ⟨n, hnF⟩ (Subtype.ext hff) (fun h1' => hf1 (congrArg Subtype.val h1'))
          (Subtype.ext hfn.symm) (by rwa [Subgroup.orderOf_mk])
        exact congrArg Subtype.val hF1
      refine ⟨?_, ?_⟩
      · intro N hNC hodd _
        rw [eq_bot_iff]
        intro n hn
        have hnodd : Odd (orderOf n) :=
          Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hn)
        exact Subgroup.mem_bot.mpr (hodd_triv n (hNC hn) hnodd)
      · intro g hodd hg
        have hgC : g ∈ centralizer (S0 : Set J) := by
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          exact (hg b (hS0C b hb)).symm
        exact hodd_triv g hgC hodd
    · push Not at hS2
      have hCeq' : centralizer (S0 : Set J) = centralizer ({t} : Set J) := by
        apply le_antisymm hCt
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        by_cases h1 : s = 1
        · rw [h1]; simp
        · rw [hS2 s hs h1]
          exact (Subgroup.mem_centralizer_singleton_iff.mp hx).symm
      rw [hCeq', hCeq]
      exact ⟨noOddNormal_zpowers_sup ht2 hFc htF hFs hFev, fun g hodd hg =>
        eq_one_of_commute_zpowers_sup ht2 hFc htF hCeq hFs hFna hodd hg⟩

end Facts

section Loc

variable {J : Type} [Group J]

theorem conj_injective (h : SplitCent J) : Function.Injective (MulAut.conj : J →* MulAut J) := by
  intro a b hab
  have hx : ∀ x : J, a * x * a⁻¹ = b * x * b⁻¹ := fun x => by
    have := congrArg (fun ψ : MulAut J => ψ x) hab
    simpa using this
  have hz : b⁻¹ * a = 1 := by
    apply h.center
    intro g
    have h1 : (b⁻¹ * a) * g * (b⁻¹ * a)⁻¹ = g := by
      have h2 : b⁻¹ * (a * g * a⁻¹) * b = g := by rw [hx g]; group
      have h3 : (b⁻¹ * a) * g * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * g * a⁻¹) * b := by group
      rw [h3, h2]
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  exact (inv_mul_eq_one.mp hz).symm

theorem exists_involution [Finite J] (h : SplitCent J) : ∃ u : J, u * u = 1 ∧ u ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := J) 2 h.even
  refine ⟨u, ?_, ?_⟩
  · have : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    rwa [sq] at this
  · intro h1
    rw [h1, orderOf_one] at hu
    omega

theorem noncentral_of_ne_one (h : SplitCent J) {x : J} (hx : x ≠ 1) : ∃ y : J, y * x ≠ x * y := by
  by_contra hcon
  push Not at hcon
  exact hx (h.center x hcon)

theorem locProp_of_splitCent [Finite J] (h : SplitCent J) : LocProp J := by
  intro A _ _ α hA
  have hAea := hA.1
  have hinj := conj_injective h
  have hsq : ∀ a : A, a * a = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hAea
  have hcomm : ∀ a b : A, a * b = b * a := fun a b => mul_comm' a b
  let S0 : Subgroup A → Subgroup J := fun E => (E.map α).comap (MulAut.conj : J →* MulAut J)
  have hmemS0 : ∀ (E : Subgroup A) (g : J), g ∈ S0 E ↔ MulAut.conj g ∈ E.map α := fun E g => Iff.rfl
  have hS : ∀ E : Subgroup A, ∀ g ∈ S0 E, g * g = 1 := by
    intro E g hg
    obtain ⟨a, _, hag⟩ := Subgroup.mem_map.mp ((hmemS0 E g).mp hg)
    apply hinj
    rw [map_mul, ← hag, ← map_mul, hsq a, map_one, map_one]
  have hc : ∀ E : Subgroup A, ∀ a ∈ S0 E, ∀ b ∈ S0 E, a * b = b * a := by
    intro E a ha b hb
    obtain ⟨x, _, hx⟩ := Subgroup.mem_map.mp ((hmemS0 E a).mp ha)
    obtain ⟨y, _, hy⟩ := Subgroup.mem_map.mp ((hmemS0 E b).mp hb)
    apply hinj
    rw [map_mul, map_mul, ← hx, ← hy, ← map_mul, ← map_mul, hcomm]
  have hfix : ∀ E : Subgroup A, fixedIn J (E.map α) = centralizer ((S0 E : Subgroup J) : Set J) := by
    intro E
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 := hx _ ((hmemS0 E g).mp hg)
      rw [MulAut.conj_apply] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1
    · intro hx φ hφ
      obtain ⟨g, rfl⟩ := h.aut φ
      have hg : g ∈ S0 E := (hmemS0 E g).mpr hφ
      have := Subgroup.mem_centralizer_iff.mp hx g hg
      rw [MulAut.conj_apply]
      exact mul_inv_eq_iff_eq_mul.mpr this
  refine ⟨fun E _ => ?_, fun φ hodd hφ => ?_, ?_⟩
  · rw [hfix E]
    exact (centralizer_facts h (S0 E) (hS E) (hc E)).1
  · obtain ⟨g, rfl⟩ := h.aut φ
    have hgodd : Odd (orderOf g) := by
      rwa [← orderOf_injective (MulAut.conj : J →* MulAut J) hinj g]
    have htop : pRank 2 A - 1 ≤ pRank 2 ↥(⊤ : Subgroup A) := by
      rw [WeakSigGen.pRank_top_eq hAea]
      exact Nat.sub_le _ _
    have hle : fixedIn J ((⊤ : Subgroup A).map α) ≤ gammaAct α :=
      le_iSup_of_le (⊤ : Subgroup A) (le_iSup_of_le htop le_rfl)
    have h1 := (centralizer_facts h (S0 ⊤) (hS ⊤) (hc ⊤)).2 g hgodd (fun x hx => by
      have hx' : x ∈ fixedIn J ((⊤ : Subgroup A).map α) := by rw [hfix]; exact hx
      have := hφ x (hle hx')
      rw [MulAut.conj_apply] at this
      exact mul_inv_eq_iff_eq_mul.mp this)
    rw [h1, map_one]
  ·
    have htop : pRank 2 A - 1 ≤ pRank 2 ↥(⊤ : Subgroup A) := by
      rw [WeakSigGen.pRank_top_eq hAea]
      exact Nat.sub_le _ _
    refine ⟨⊤, htop, ?_⟩
    rw [hfix]
    by_cases hS1 : ∃ t ∈ S0 ⊤, t ≠ 1
    · obtain ⟨t, htS, ht1⟩ := hS1
      refine ⟨t, ?_, ⟨1, by rw [pow_one, sq]; exact hS ⊤ t htS⟩, noncentral_of_ne_one h ht1⟩
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hc ⊤ b hb t htS
    · push Not at hS1
      obtain ⟨u, hu, hu1⟩ := exists_involution h
      refine ⟨u, ?_, ⟨1, by rw [pow_one, sq]; exact hu⟩, noncentral_of_ne_one h hu1⟩
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      rw [hS1 b hb]
      simp

end Loc

section J1

open CFSG.Walter CFSG.Walter.J1Props CFSG.Open

theorem a5_fact : ∀ f g : alternatingGroup (Fin 5), f * f = 1 → f ≠ 1 → g * f = f * g →
    g ^ 15 = 1 → g = 1 := by
  decide +kernel

theorem walterJ1_center' :
    ∀ z : walterJ1, (∀ g : walterJ1, g * z = z * g) → z = 1 := by
  intro z hz
  have hs : IsSimpleGroup walterJ1 := J1_simple
  have hZ : Subgroup.center walterJ1 = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center walterJ1) with h | h
    · exact h
    · exfalso
      have h1 : Subgroup.centralizer ({tJ} : Set walterJ1) = ⊤ := by
        rw [eq_top_iff]
        intro g _
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_center_iff.1 (by rw [h]; exact Subgroup.mem_top g) tJ).symm
      have h2 := card_centralizer_of_orderOf_eq_two (x := tJ) orderOf_tJ
      rw [h1, Subgroup.card_top, J1_card] at h2
      omega
  have : z ∈ Subgroup.center walterJ1 := Subgroup.mem_center_iff.2 fun g => (hz g)
  rwa [hZ, Subgroup.mem_bot] at this

theorem splitCent_walterJ1 : SplitCent walterJ1 := by
  refine ⟨J1_simple, ?_, walterJ1_center', J3_aut, ?_⟩
  · rw [J1_card]; norm_num
  · intro u hu
    obtain ⟨g, hg⟩ := jankoHyp.exists_conj_eq_t hu
    set h := jankoHyp.conj g⁻¹ with hh
    have ht : h.t = u := by
      rw [hh, CFSG.Walter.J1.JankoHyp.conj_t, ← hg]
      group
    have hs5 : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have hcard : Nat.card h.F = 60 := by
      rw [Nat.card_congr h.iso.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    have hFs : IsSimpleGroup h.F := MulEquiv.isSimpleGroup h.iso
    refine ⟨h.F, ?_, ?_, ?_, hFs, ?_, ?_, ?_⟩
    · rw [← ht]; exact h.le_centralizer
    · rw [← ht]; exact h.t_not_mem
    · rw [← ht]; exact h.centralizer_eq
    · by_contra hcon
      push Not at hcon
      have : IsMulCommutative ↥h.F := ⟨⟨fun a b => hcon a b⟩⟩
      have := IsSimpleGroup.prime_card (α := ↥h.F)
      rw [hcard] at this
      exact absurd this (by norm_num)
    · rw [hcard]; norm_num
    · intro f g hff hf1 hgf hodd
      have hg15 : g ^ 15 = 1 := by
        have hd : orderOf g ∣ 15 * 4 := by
          have := orderOf_dvd_natCard g
          rw [hcard] at this
          exact this
        have hcop : Nat.Coprime (orderOf g) 4 := by
          have h2 : Nat.Coprime (orderOf g) 2 := (Nat.coprime_two_left.mpr hodd).symm
          simpa using h2.pow_right 2
        exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hd)
      have e1 := a5_fact (h.iso f) (h.iso g)
        (by rw [← map_mul, hff, map_one])
        (fun h1 => hf1 (h.iso.injective (by rw [h1, map_one])))
        (by rw [← map_mul, ← map_mul, hgf])
        (by rw [← map_pow, hg15, map_one])
      exact h.iso.injective (by rw [e1, map_one])

end J1

end WeakSigJ1

open CFSG.Walter CFSG.Walter.J1Props CFSG.Open in
theorem genLoc_walterJ1 : GenLoc walterJ1 :=
  (WeakSigJ1.locProp_of_splitCent WeakSigJ1.splitCent_walterJ1).genLoc

end CFSG.GH74.Generic.BProg.B2
