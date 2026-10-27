module

public import CFSG.GH74.GLS.C3.Layer1.Th2P61Obs
public import CFSG.GH74.GLS.C3.Layer1.Th2BalA7

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
  CFSG.ClassicalInvolution.Balance CFSG.Assembly.Dichotomy CFSG.GH74.GLS.Th2.Bal
open scoped commutatorElement

theorem perm4_aux : ∀ s z : Perm (Fin 4), (∀ i, s i ≠ i) → s * z = z * s → z ^ 3 = 1 → z = 1 := by
  decide +kernel

theorem perm4_pow_twelve : ∀ z : Perm (Fin 4), z ^ 12 = 1 := by decide +kernel

theorem fixes_of_odd_commute_two_two {σ ζ : Perm (Fin 7)} (hσ : σ.cycleType = {2, 2})
    (hζ : Odd (orderOf ζ)) (hc : σ * ζ = ζ * σ) {i : Fin 7} (hi : σ i ≠ i) : ζ i = i := by
  classical
  have hScard : σ.support.card = 4 := by
    rw [← Equiv.Perm.sum_cycleType, hσ]; rfl
  have hcomm : ∀ x, σ (ζ x) = ζ (σ x) := fun x => by
    have := congrArg (fun f : Perm (Fin 7) => f x) hc
    simpa using this
  have hζS : ∀ x, ζ x ∈ σ.support ↔ x ∈ σ.support := by
    intro x
    simp only [Equiv.Perm.mem_support]
    rw [hcomm x]
    constructor
    · intro h h1
      exact h (by rw [h1])
    · intro h h1
      exact h (ζ.injective h1)
  have hcard : Fintype.card {x // x ∈ σ.support} = 4 :=
    (Fintype.card_coe σ.support).trans hScard
  let e : {x // x ∈ σ.support} ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  have hσS : ∀ x, σ x ∈ σ.support ↔ x ∈ σ.support := fun x => Equiv.Perm.apply_mem_support
  let σ' : Perm {x // x ∈ σ.support} := σ.subtypePerm hσS
  let ζ' : Perm {x // x ∈ σ.support} := ζ.subtypePerm hζS
  have hcomm' : σ' * ζ' = ζ' * σ' := by
    show σ.subtypePerm hσS * ζ.subtypePerm hζS = ζ.subtypePerm hζS * σ.subtypePerm hσS
    rw [Equiv.Perm.subtypePerm_mul, Equiv.Perm.subtypePerm_mul]
    simp only [hc]
  have hζ'm : ζ' ^ (orderOf ζ) = 1 := by
    rw [show ζ' = ζ.subtypePerm hζS from rfl, Equiv.Perm.subtypePerm_pow]
    ext x
    simp [pow_orderOf_eq_one]
  have h12 := perm4_pow_twelve (e.permCongrHom ζ')
  have hm : (e.permCongrHom ζ') ^ (orderOf ζ) = 1 := by rw [← map_pow, hζ'm, map_one]
  have hg := (pow_gcd_eq_one (a := e.permCongrHom ζ') (m := orderOf ζ) (n := 12)).2 ⟨hm, h12⟩
  have hg3 : Nat.gcd (orderOf ζ) 12 ∣ 3 := by
    have hd12 : Nat.gcd (orderOf ζ) 12 ∣ 12 := Nat.gcd_dvd_right _ _
    have hdm : Nat.gcd (orderOf ζ) 12 ∣ orderOf ζ := Nat.gcd_dvd_left _ _
    have hodd : Odd (Nat.gcd (orderOf ζ) 12) := Odd.of_dvd_nat hζ hdm
    have hcop : Nat.Coprime (Nat.gcd (orderOf ζ) 12) 4 := by
      rw [Nat.coprime_comm]
      exact (Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd) : Nat.Coprime (2 ^ 2) _)
    have : Nat.gcd (orderOf ζ) 12 ∣ 4 * 3 := hd12
    exact hcop.dvd_of_dvd_mul_left this
  have h3 : (e.permCongrHom ζ') ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := hg3
    rw [hk, pow_mul, hg, one_pow]
  have hs : ∀ j, (e.permCongrHom σ') j ≠ j := by
    intro j h
    have h1 : e (σ' (e.symm j)) = j := by simpa [Equiv.permCongrHom_coe, Equiv.permCongr_apply] using h
    have h2 : σ' (e.symm j) = e.symm j := by
      rw [← e.symm_apply_apply (σ' (e.symm j)), h1]
    have h3 : σ (e.symm j : Fin 7) = (e.symm j : Fin 7) := congrArg Subtype.val h2
    exact (Equiv.Perm.mem_support.1 (e.symm j).2) h3
  have hz : e.permCongrHom ζ' = 1 :=
    perm4_aux _ _ hs (by rw [← map_mul, ← map_mul, hcomm']) h3
  have hζ'1 : ζ' = 1 := by
    have := (e.permCongrHom).injective (hz.trans (map_one _).symm)
    exact this
  have hiS : i ∈ σ.support := Equiv.Perm.mem_support.2 hi
  have := congrArg (fun f : Perm {x // x ∈ σ.support} => (f ⟨i, hiS⟩ : Fin 7)) hζ'1
  exact this

theorem mem_alternatingGroup_of_odd_orderOf {σ : Perm (Fin 7)} (hσ : Odd (orderOf σ)) :
    σ ∈ alternatingGroup (Fin 7) := by
  have h2 : orderOf (Equiv.Perm.sign σ) ∣ orderOf σ := orderOf_map_dvd Equiv.Perm.sign σ
  have h3 : orderOf (Equiv.Perm.sign σ) ∣ 2 := orderOf_dvd_of_pow_eq_one (Int.units_pow_two _)
  have h4 : orderOf (Equiv.Perm.sign σ) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h3 with h | h
    · exact h
    · rw [h] at h2
      exact absurd (Odd.of_dvd_nat hσ h2) (by decide)
  exact Equiv.Perm.mem_alternatingGroup.2 (orderOf_eq_one_iff.1 h4)

theorem involutionOddCore_eq_bot_of_odd {Z : Subgroup (Perm (Fin 7))}
    (hZ : alternatingGroup (Fin 7) ≤ Z) {f : ↥Z} (hf2 : f * f = 1) (hf1 : f ≠ 1)
    (hodd : (f : Perm (Fin 7)) ∉ alternatingGroup (Fin 7)) : involutionOddCore f = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup ↥Z := involutionOddCore f with hW
  have hWodd : Odd (Nat.card W) := odd_card_involutionOddCore f
  set C : Subgroup (Perm (Fin 7)) :=
    centralizer ({(f : Perm (Fin 7))} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) with hC
  set W' : Subgroup (Perm (Fin 7)) := W.map Z.subtype with hW'
  have hfsq : (f : Perm (Fin 7)) ^ 2 = 1 := by
    rw [pow_two]; exact congrArg Subtype.val hf2
  have hf1' : (f : Perm (Fin 7)) ≠ 1 := fun h => hf1 (Subtype.ext h)
  have hW'C : W' ≤ C := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · have h1 := involutionOddCore_le_centralizer f hw
      rw [Subgroup.mem_centralizer_singleton_iff] at h1
      show (w : Perm (Fin 7)) ∈ centralizer ({(f : Perm (Fin 7))} : Set (Perm (Fin 7)))
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val h1
    · have hord : Odd (orderOf (w : Perm (Fin 7))) := by
        have e : orderOf (w : Perm (Fin 7)) = orderOf (⟨w, hw⟩ : ↥W) := by
          rw [Subgroup.orderOf_mk]; exact (Subgroup.orderOf_coe w)
        rw [e]
        exact Odd.of_dvd_nat hWodd (orderOf_dvd_natCard _)
      exact mem_alternatingGroup_of_odd_orderOf hord
  set W'' : Subgroup ↥C := W'.subgroupOf C with hW''
  have hWn : W''.Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [hW'', Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨z, hz, hzn⟩ := hn
    have hcZ : (c : Perm (Fin 7)) ∈ Z := hZ c.2.2
    have hcc : (⟨(c : Perm (Fin 7)), hcZ⟩ : ↥Z) ∈ centralizer ({f} : Set ↥Z) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp c.2.1
    have h1 := conj_mem_involutionOddCore hcc hz
    refine ⟨_, h1, ?_⟩
    simp [← hzn]
  have hW''odd : Odd (Nat.card W'') := by
    have h1 : Nat.card W'' = Nat.card W' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW'C).toEquiv
    have h2 : Nat.card W' = Nat.card W := Subgroup.card_map_of_injective Z.subtype_injective
    rw [h1, h2]; exact hWodd
  have hbot'' : W'' = ⊥ := by
    have hfu : (f : Perm (Fin 7)) ^ 2 = 1 := hfsq
    rcases A7.involution_cycleType (f : Perm (Fin 7)) hfu hf1' with h | h | h
    · obtain ⟨ρ⟩ := A7.centralizer_A7_swap_equiv (Equiv.Perm.isSwap_iff_cycleType.mpr h)
      exact eq_bot_of_normal_odd_of_equiv_perm5 ρ W'' hW''odd
    · exfalso
      have hs := Equiv.Perm.sign_of_cycleType (f : Perm (Fin 7))
      rw [h] at hs
      have h6 : ((-1 : ℤˣ)) ^ (Multiset.sum ({2, 2} : Multiset ℕ) +
          Multiset.card ({2, 2} : Multiset ℕ)) = 1 := Even.neg_one_pow (by decide)
      rw [h6] at hs
      exact hodd (Equiv.Perm.mem_alternatingGroup.2 hs)
    · obtain ⟨ρ⟩ := A7.centralizer_A7_two_two_two_equiv h
      exact eq_bot_of_normal_odd_of_equiv_perm4 ρ W'' hW''odd
  have hW'bot : W' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hW'C hx⟩ : ↥C) ∈ W'' := by
      rw [hW'', Subgroup.mem_subgroupOf]; exact hx
    rw [hbot'', Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  rw [eq_bot_iff]
  intro w hw
  have : (w : Perm (Fin 7)) ∈ W' := ⟨w, hw, rfl⟩
  rw [hW'bot, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (Subtype.ext this)

@[expose] def IsRootFour (F : Subgroup (Perm (Fin 7))) : Prop :=
  F ≤ alternatingGroup (Fin 7) ∧ Nat.card ↥F = 4 ∧ (∀ f ∈ F, f * f = 1) ∧
    ∃ S : Finset (Fin 7), S.card = 4 ∧ ∀ f ∈ F, f ≠ 1 → f.support = S

theorem IsRootFour.ncard_moved {F : Subgroup (Perm (Fin 7))} (h : IsRootFour F) :
    Set.ncard {i : Fin 7 | ∃ f ∈ F, f i ≠ i} = 4 := by
  obtain ⟨-, hcard, -, S, hS, hsupp⟩ := h
  obtain ⟨f₁, hf₁F, hf₁1⟩ : ∃ f ∈ F, f ≠ 1 := by
    by_contra hno
    push Not at hno
    have : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 hno
    rw [this, Subgroup.card_bot] at hcard
    omega
  have hset : {i : Fin 7 | ∃ f ∈ F, f i ≠ i} = ↑S := by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.mem_coe]
    constructor
    · rintro ⟨f, hf, hi⟩
      have hf1 : f ≠ 1 := by
        rintro rfl
        exact hi rfl
      rw [← hsupp f hf hf1]
      exact Equiv.Perm.mem_support.2 hi
    · intro hi
      rw [← hsupp f₁ hf₁F hf₁1] at hi
      exact ⟨f₁, hf₁F, Equiv.Perm.mem_support.1 hi⟩
  rw [hset, Set.ncard_coe_finset, hS]

theorem a7_even {Z : Subgroup (Perm (Fin 7))} (hZ : alternatingGroup (Fin 7) ≤ Z)
    {F : Subgroup ↥Z} (hF2 : ∀ f ∈ F, f * f = 1) {ζ : ↥Z} (hζ : ζ ∈ deltaCore F) (hζ1 : ζ ≠ 1) :
    ∀ f ∈ F, (f : Perm (Fin 7)) ∈ alternatingGroup (Fin 7) := by
  intro f hf
  by_cases hf1 : f = 1
  · rw [hf1]; exact one_mem _
  · by_contra hodd
    have h1 := deltaCore_le_involutionOddCore hf hf1 hζ
    rw [involutionOddCore_eq_bot_of_odd hZ (hF2 f hf) hf1 hodd, Subgroup.mem_bot] at h1
    exact hζ1 h1

theorem root_of_commuting {F : Subgroup (Perm (Fin 7))} (hF4 : 4 ≤ Nat.card F)
    (hF2 : ∀ f ∈ F, f * f = 1) (hFalt : ∀ f ∈ F, f ∈ alternatingGroup (Fin 7))
    {ζ : Perm (Fin 7)} (hζodd : Odd (orderOf ζ)) (hζ1 : ζ ≠ 1)
    (hζc : ∀ f ∈ F, f * ζ = ζ * f) :
    IsRootFour F ∧ ∃ S : Finset (Fin 7), S.card = 4 ∧ (∀ f ∈ F, f ≠ 1 → f.support = S) ∧
      ∀ i ∈ S, ζ i = i := by
  classical
  have hcard : Nat.card F = 4 := by
    have hle : F ≤ alternatingGroup (Fin 7) := fun f hf => hFalt f hf
    have h4 : Nat.card ↥F ≤ 4 := A7.card_le_four_of_sq_eq_one F hle hF2
    omega
  have hct : ∀ f ∈ F, f ≠ 1 → f.cycleType = {2, 2} := by
    intro f hf hf1
    have hfu : f ^ 2 = 1 := by
      rw [pow_two]; exact hF2 f hf
    have hs := Equiv.Perm.mem_alternatingGroup.1 (hFalt f hf)
    rw [Equiv.Perm.sign_of_cycleType] at hs
    rcases A7.involution_cycleType f hfu hf1 with h | h | h
    · exfalso
      rw [h] at hs
      have h3 : ((-1 : ℤˣ)) ^ (Multiset.sum ({2} : Multiset ℕ) + Multiset.card ({2} : Multiset ℕ)) = -1 :=
        Odd.neg_one_pow (by decide)
      rw [h3] at hs
      exact absurd hs (by decide)
    · exact h
    · exfalso
      rw [h] at hs
      have h3 : ((-1 : ℤˣ)) ^ (Multiset.sum ({2, 2, 2} : Multiset ℕ) +
          Multiset.card ({2, 2, 2} : Multiset ℕ)) = -1 := Odd.neg_one_pow (by decide)
      rw [h3] at hs
      exact absurd hs (by decide)
  obtain ⟨f₁, hf₁F, hf₁1⟩ : ∃ f ∈ F, f ≠ 1 := by
    by_contra hno
    push Not at hno
    have : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 hno
    rw [this, Subgroup.card_bot] at hcard
    omega
  have hfix : ∀ f ∈ F, f ≠ 1 → ∀ i, f i ≠ i → ζ i = i :=
    fun f hf hf1 i hi => fixes_of_odd_commute_two_two (hct f hf hf1) hζodd (hζc f hf) hi
  have hζsupp : 3 ≤ ζ.support.card := by
    have h2 : 2 ≤ ζ.support.card := Equiv.Perm.two_le_card_support_of_ne_one hζ1
    by_contra hlt
    have h2' : ζ.support.card = 2 := by omega
    have hsw : ζ.IsSwap := Equiv.Perm.card_support_eq_two.1 h2'
    have : orderOf ζ = 2 := hsw.orderOf
    rw [this] at hζodd
    exact absurd hζodd (by decide)
  have hsuppcard : ∀ f ∈ F, f ≠ 1 → f.support.card = 4 := by
    intro f hf hf1
    rw [← Equiv.Perm.sum_cycleType, hct f hf hf1]; rfl
  have hsupp_eq : ∀ f ∈ F, f ≠ 1 → f.support = f₁.support := by
    intro f hf hf1
    have hsub : f.support ∪ f₁.support ⊆ ζ.supportᶜ := by
      intro i hi
      rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
      rcases Finset.mem_union.1 hi with h | h
      · exact hfix f hf hf1 i (Equiv.Perm.mem_support.1 h)
      · exact hfix f₁ hf₁F hf₁1 i (Equiv.Perm.mem_support.1 h)
    have hcardc : (ζ.supportᶜ).card ≤ 4 := by
      rw [Finset.card_compl]
      simp only [Fintype.card_fin]
      omega
    have hle := (Finset.card_le_card hsub).trans hcardc
    have h4 := hsuppcard f hf hf1
    have h4' := hsuppcard f₁ hf₁F hf₁1
    have hl1 : f.support ⊆ f.support ∪ f₁.support := Finset.subset_union_left
    have hl2 : f₁.support ⊆ f.support ∪ f₁.support := Finset.subset_union_right
    have e1 : f.support = f.support ∪ f₁.support :=
      Finset.eq_of_subset_of_card_le hl1 (by omega)
    have e2 : f₁.support = f.support ∪ f₁.support :=
      Finset.eq_of_subset_of_card_le hl2 (by omega)
    rw [e1, ← e2]
  have hS : ∀ f ∈ F, f ≠ 1 → f.support = f₁.support := hsupp_eq
  refine ⟨⟨fun f hf => hFalt f hf, hcard, hF2, f₁.support, hsuppcard f₁ hf₁F hf₁1, hS⟩,
    f₁.support, hsuppcard f₁ hf₁F hf₁1, hS, ?_⟩
  intro i hi
  exact hfix f₁ hf₁F hf₁1 i (Equiv.Perm.mem_support.1 hi)

theorem eq_one_or_swap_of_comm {S : Finset (Fin 7)} (hS : S.card = 4) {x y : Fin 7} (hxy : x ≠ y)
    (hxS : x ∉ S) (hyS : y ∉ S) {t' : Perm (Fin 7)} (hfix : ∀ i ∈ S, t' i = i)
    (hc : t' * swap x y = swap x y * t') : t' = 1 ∨ t' = swap x y := by
  classical
  have hc' : ∀ i, t' (swap x y i) = swap x y (t' i) := fun i => by
    have := congrArg (fun p : Perm (Fin 7) => p i) hc
    simpa using this
  have hx' : t' x = x ∨ t' x = y := by
    by_contra hne
    push Not at hne
    have h1 : swap x y (t' x) = t' x := swap_apply_of_ne_of_ne hne.1 hne.2
    have h2 := hc' x
    rw [swap_apply_left, h1] at h2
    exact hxy (t'.injective h2).symm
  have hy' : t' y = x ∨ t' y = y := by
    by_contra hne
    push Not at hne
    have h1 : swap x y (t' y) = t' y := swap_apply_of_ne_of_ne hne.1 hne.2
    have h2 := hc' y
    rw [swap_apply_right, h1] at h2
    exact hxy (t'.injective h2)
  set U : Finset (Fin 7) := S ∪ {x, y} with hU
  have hxy_disj : Disjoint S {x, y} := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rcases Finset.mem_insert.1 hi' with rfl | hi''
    · exact hxS hi
    · rw [Finset.mem_singleton.1 hi''] at hi
      exact hyS hi
  have hUcard : U.card = 6 := by
    rw [hU, Finset.card_union_of_disjoint hxy_disj, hS, Finset.card_pair hxy]
  have hUmap : ∀ u ∈ U, t' u ∈ U := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · rw [hfix u hu]; exact Finset.mem_union_left _ hu
    · rcases Finset.mem_insert.1 hu with rfl | hu'
      · rcases hx' with h | h
        · rw [h]; exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
        · rw [h]; exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      · rw [Finset.mem_singleton.1 hu']
        rcases hy' with h | h
        · rw [h]; exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
        · rw [h]; exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have himg : U.image t' = U := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hw
      exact hUmap u hu
    · rw [Finset.card_image_of_injective _ t'.injective]
  have hUout : ∀ i, i ∉ U → t' i ∉ U := by
    intro i hi hti
    rw [← himg] at hti
    obtain ⟨u, hu, hut⟩ := Finset.mem_image.1 hti
    exact hi (t'.injective hut ▸ hu)
  have hRcard : (Uᶜ).card = 1 := by
    rw [Finset.card_compl, hUcard]; rfl
  have hrem : ∀ i, i ∉ U → t' i = i := by
    intro i hi
    have hi' : i ∈ Uᶜ := Finset.mem_compl.2 hi
    have hti : t' i ∈ Uᶜ := Finset.mem_compl.2 (hUout i hi)
    exact Finset.card_le_one.1 hRcard.le _ hti _ hi'
  have hSx : ∀ i ∈ S, i ≠ x := by
    rintro i hi rfl
    exact hxS hi
  have hSy : ∀ i ∈ S, i ≠ y := by
    rintro i hi rfl
    exact hyS hi
  have hxU : x ∈ U := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have hyU : y ∈ U := Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hUcases : ∀ i ∈ U, i ∈ S ∨ i = x ∨ i = y := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · exact Or.inl hi
    · rcases Finset.mem_insert.1 hi with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Finset.mem_singleton.1 h))
  rcases hx' with h | h
  · left
    have hyy : t' y = y := by
      have h2 := hc' x
      rw [swap_apply_left, h, swap_apply_left] at h2
      exact h2
    refine Equiv.ext fun i => ?_
    by_cases hiU : i ∈ U
    · rcases hUcases i hiU with hiS | rfl | rfl
      · rw [hfix i hiS]; rfl
      · rw [h]; rfl
      · rw [hyy]; rfl
    · rw [hrem i hiU]; rfl
  · right
    have hyy : t' y = x := by
      have h2 := hc' x
      rw [swap_apply_left, h, swap_apply_right] at h2
      exact h2
    refine Equiv.ext fun i => ?_
    by_cases hiU : i ∈ U
    · rcases hUcases i hiU with hiS | rfl | rfl
      · rw [hfix i hiS, swap_apply_of_ne_of_ne (hSx i hiS) (hSy i hiS)]
      · rw [h, swap_apply_left]
      · rw [hyy, swap_apply_right]
    · have hix : i ≠ x := fun h' => hiU (h' ▸ hxU)
      have hiy : i ≠ y := fun h' => hiU (h' ▸ hyU)
      rw [hrem i hiU, swap_apply_of_ne_of_ne hix hiy]

theorem a7_E_structure {F E : Subgroup (Perm (Fin 7))} (hF : IsRootFour F) (hFE : F ≤ E)
    (hE2 : ∀ e ∈ E, e * e = 1) (hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) (hnot : ¬ E ≤ F) :
    ∃ t : Perm (Fin 7), t.IsSwap ∧ (∀ i, (∃ f ∈ F, f i ≠ i) → t i = i) ∧
      E = F ⊔ Subgroup.zpowers t := by
  classical
  obtain ⟨hFalt, hcard, hF2, S, hS, hsupp⟩ := hF
  have hcommFE : ∀ f ∈ F, ∀ e ∈ E, f * e = e * f := fun f hf e he => hEc f (hFE hf) e he
  obtain ⟨f₁, hf₁F, hf₁1⟩ : ∃ f ∈ F, f ≠ 1 := by
    by_contra hno
    push Not at hno
    have : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 hno
    rw [this, Subgroup.card_bot] at hcard
    omega
  have hS₁ : f₁.support = S := hsupp f₁ hf₁F hf₁1
  have hpres : ∀ e ∈ E, ∀ i ∈ S, e i ∈ S := by
    intro e he i hi
    rw [← hS₁] at hi ⊢
    rw [Equiv.Perm.mem_support] at hi ⊢
    intro h
    apply hi
    have hc : f₁ (e i) = e (f₁ i) := by
      have := congrArg (fun p : Perm (Fin 7) => p i) (hcommFE f₁ hf₁F e he)
      simpa using this
    exact (e.injective (h.symm.trans hc)).symm
  have hreg : ∀ i₀ ∈ S, ∀ j ∈ S, ∃ f ∈ F, f i₀ = j := by
    intro i₀ hi₀ j hj
    have hmem : ∀ f : ↥F, (f : Perm (Fin 7)) i₀ ∈ S := by
      intro f
      by_cases hf1 : (f : Perm (Fin 7)) = 1
      · rw [hf1]; exact hi₀
      · have h1 : i₀ ∈ (f : Perm (Fin 7)).support := (hsupp f f.2 hf1).symm ▸ hi₀
        have h2 := Equiv.Perm.apply_mem_support.2 h1
        rwa [hsupp f f.2 hf1] at h2
    let g : ↥F → {x // x ∈ S} := fun f => ⟨(f : Perm (Fin 7)) i₀, hmem f⟩
    have hinj : Function.Injective g := by
      intro f f' h
      have h1 : (f : Perm (Fin 7)) i₀ = (f' : Perm (Fin 7)) i₀ := congrArg Subtype.val h
      have hk : ((f'⁻¹ * f : ↥F) : Perm (Fin 7)) i₀ = i₀ := by
        show (f' : Perm (Fin 7))⁻¹ ((f : Perm (Fin 7)) i₀) = i₀
        rw [h1]
        simp
      by_cases hk1 : ((f'⁻¹ * f : ↥F) : Perm (Fin 7)) = 1
      · have : f'⁻¹ * f = 1 := Subtype.ext hk1
        exact (inv_mul_eq_one.1 this).symm
      · exfalso
        have h2 : i₀ ∈ ((f'⁻¹ * f : ↥F) : Perm (Fin 7)).support :=
          (hsupp _ (f'⁻¹ * f).2 hk1).symm ▸ hi₀
        exact (Equiv.Perm.mem_support.1 h2) hk
    have hc : Nat.card {x // x ∈ S} ≤ Nat.card ↥F := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, hS, hcard]
    have hbij := hinj.bijective_of_nat_card_le hc
    obtain ⟨f, hf⟩ := hbij.2 ⟨j, hj⟩
    exact ⟨f, f.2, congrArg Subtype.val hf⟩
  have hagree : ∀ e ∈ E, ∃ f ∈ F, ∀ i ∈ S, e i = f i := by
    intro e he
    obtain ⟨i₀, hi₀⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨f, hfF, hf⟩ := hreg i₀ hi₀ (e i₀) (hpres e he i₀ hi₀)
    refine ⟨f, hfF, fun i hi => ?_⟩
    obtain ⟨f', hf'F, hf'⟩ := hreg i₀ hi₀ i hi
    have hc1 : f' (e i₀) = e (f' i₀) := by
      have := congrArg (fun p : Perm (Fin 7) => p i₀) (hcommFE f' hf'F e he)
      simpa using this
    have hc2 : f (f' i₀) = f' (f i₀) := by
      have := congrArg (fun p : Perm (Fin 7) => p i₀) (hEc f (hFE hfF) f' (hFE hf'F))
      simpa using this
    calc e i = e (f' i₀) := by rw [hf']
      _ = f' (e i₀) := hc1.symm
      _ = f' (f i₀) := by rw [hf]
      _ = f (f' i₀) := hc2.symm
      _ = f i := by rw [hf']
  obtain ⟨σ, hσE, hσF⟩ := Set.not_subset.mp hnot
  obtain ⟨f₀, hf₀F, hf₀⟩ := hagree σ hσE
  set t : Perm (Fin 7) := f₀⁻¹ * σ with ht
  have htE : t ∈ E := E.mul_mem (E.inv_mem (hFE hf₀F)) hσE
  have htfix : ∀ i ∈ S, t i = i := by
    intro i hi
    rw [ht, Perm.mul_apply, hf₀ i hi]
    simp
  have ht2 : t * t = 1 := hE2 t htE
  have ht1 : t ≠ 1 := by
    intro h1
    apply hσF
    have : σ = f₀ * t := by rw [ht]; group
    rw [this, h1, mul_one]
    exact hf₀F
  have hsupp_t : t.support ⊆ Sᶜ := fun i hi => by
    rw [Finset.mem_compl]
    intro hiS
    exact (Equiv.Perm.mem_support.1 hi) (htfix i hiS)
  have hcard_t : t.support.card ≤ 3 := by
    have := Finset.card_le_card hsupp_t
    rw [Finset.card_compl, Fintype.card_fin, hS] at this
    omega
  have hswap : t.IsSwap := by
    have htsq : t ^ 2 = 1 := by rw [pow_two]; exact ht2
    rcases A7.involution_cycleType t htsq ht1 with h | h | h
    · exact Equiv.Perm.isSwap_iff_cycleType.mpr h
    · exfalso
      have : t.support.card = 4 := by rw [← Equiv.Perm.sum_cycleType, h]; rfl
      omega
    · exfalso
      have : t.support.card = 6 := by rw [← Equiv.Perm.sum_cycleType, h]; rfl
      omega
  refine ⟨t, hswap, ?_, ?_⟩
  · rintro i ⟨f, hf, hi⟩
    have hf1 : f ≠ 1 := by
      rintro rfl
      exact hi rfl
    have : i ∈ S := by
      rw [← hsupp f hf hf1]
      exact Equiv.Perm.mem_support.2 hi
    exact htfix i this
  · apply le_antisymm
    · intro σ' hσ'
      obtain ⟨f', hf'F, hf'⟩ := hagree σ' hσ'
      set t' : Perm (Fin 7) := f'⁻¹ * σ' with ht'
      have ht'E : t' ∈ E := E.mul_mem (E.inv_mem (hFE hf'F)) hσ'
      have ht'fix : ∀ i ∈ S, t' i = i := by
        intro i hi
        rw [ht', Perm.mul_apply, hf' i hi]
        simp
      have hswap' := hswap
      obtain ⟨x, y, hxy, hxyt⟩ := hswap'
      have hxsupp : x ∈ t.support := by
        rw [hxyt, Equiv.Perm.support_swap hxy]
        simp
      have hysupp : y ∈ t.support := by
        rw [hxyt, Equiv.Perm.support_swap hxy]
        simp
      have hxS : x ∉ S := Finset.mem_compl.1 (hsupp_t hxsupp)
      have hyS : y ∉ S := Finset.mem_compl.1 (hsupp_t hysupp)
      have hc : t' * swap x y = swap x y * t' := by
        rw [← hxyt]
        exact hEc t' ht'E t htE
      have hσ'eq : σ' = f' * t' := by rw [ht']; group
      rcases eq_one_or_swap_of_comm hS hxy hxS hyS ht'fix hc with h | h
      · rw [hσ'eq, h, mul_one]
        exact Subgroup.mem_sup_left hf'F
      · rw [hσ'eq, h, ← hxyt]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hf'F)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    · exact sup_le hFE (Subgroup.zpowers_le.2 htE)

section Act

@[expose] noncomputable def a7Act {G : Type} [Group G] (J : Subgroup G)
    (e : kBar J ≃* alternatingGroup (Fin 7)) : ↥(normalizer (J : Set G)) →* Perm (Fin 7) :=
  (a7Theta e).symm.toMonoidHom.comp (barAct J)

theorem a7Act_eq_one_iff {G : Type} [Group G] {J : Subgroup G}
    (e : kBar J ≃* alternatingGroup (Fin 7)) (m : ↥(normalizer (J : Set G))) :
    a7Act J e m = 1 ↔ barAct J m = 1 :=
  MulEquiv.map_eq_one_iff (a7Theta e).symm

theorem a7Act_comm_iff {G : Type} [Group G] {J : Subgroup G}
    (e : kBar J ≃* alternatingGroup (Fin 7)) (m n : ↥(normalizer (J : Set G))) :
    a7Act J e m * a7Act J e n = a7Act J e n * a7Act J e m ↔
      barAct J m * barAct J n = barAct J n * barAct J m := by
  have hφ : ∀ u v : MulAut (kBar J),
      (a7Theta e).symm u * (a7Theta e).symm v = (a7Theta e).symm (u * v) :=
    fun u v => (map_mul _ u v).symm
  show (a7Theta e).symm (barAct J m) * (a7Theta e).symm (barAct J n) =
    (a7Theta e).symm (barAct J n) * (a7Theta e).symm (barAct J m) ↔ _
  rw [hφ, hφ]
  exact (a7Theta e).symm.injective.eq_iff

theorem a7Act_of_mem {G : Type} [Group G] {J : Subgroup G}
    (e : kBar J ≃* alternatingGroup (Fin 7)) {k : G} (hk : k ∈ J) :
    a7Act J e ⟨k, Subgroup.le_normalizer hk⟩ =
      ((e (QuotientGroup.mk (⟨k, hk⟩ : ↥J))) : Perm (Fin 7)) := by
  show (a7Theta e).symm (barAct J ⟨k, _⟩) = _
  rw [barAct_of_mem hk, MulEquiv.symm_apply_eq]
  have := a7Theta_even e (e (QuotientGroup.mk (⟨k, hk⟩ : ↥J)))
  rw [e.symm_apply_apply] at this
  exact this.symm

theorem alternatingGroup_le_range_a7Act {G : Type} [Group G] {J : Subgroup G}
    (e : kBar J ≃* alternatingGroup (Fin 7)) : alternatingGroup (Fin 7) ≤ (a7Act J e).range := by
  intro σ hσ
  obtain ⟨kb, hkb⟩ := e.surjective ⟨σ, hσ⟩
  induction kb using QuotientGroup.induction_on with | H k => ?_
  refine ⟨⟨(k : G), Subgroup.le_normalizer k.2⟩, ?_⟩
  rw [a7Act_of_mem e k.2]
  exact congrArg Subtype.val hkb

variable {G : Type} [Group G] [Finite G]

theorem obs_root {B : Subgroup G} {a : G} {J D : Subgroup G} (h : ObsData B a J D)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (e : kBar J ≃* alternatingGroup (Fin 7)) :
    IsRootFour ((D.subgroupOf (normalizer (J : Set G))).map (a7Act J e)) := by
  classical
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  set M : Subgroup G := normalizer (J : Set G) with hM
  set ψ : ↥M →* Perm (Fin 7) := a7Act J e with hψ
  set Z : Subgroup (Perm (Fin 7)) := ψ.range with hZ
  have hZA : alternatingGroup (Fin 7) ≤ Z := alternatingGroup_le_range_a7Act e
  let φ : ↥M →* ↥Z := ψ.rangeRestrict
  have hφ : Function.Surjective φ := MonoidHom.rangeRestrict_surjective ψ
  have hφψ : ∀ m, ((φ m : ↥Z) : Perm (Fin 7)) = ψ m := fun m => rfl
  have hDM : D ≤ M := fun d hd => h.D_norm d hd
  have hD2 : ∀ d ∈ D, d * d = 1 := fun d hd => hBsq d (h.D_le hd)
  have hfaith : ∀ d (hd : d ∈ D), ψ ⟨d, hDM hd⟩ = 1 → d = 1 := by
    intro d hd h1
    by_contra hd1
    exact h.D_faith d hd hd1 ((barAct_eq_one_iff _).1 ((a7Act_eq_one_iff e _).1 h1))
  obtain ⟨x, hxX, hxmove⟩ := h.X_move
  have hxN : x ∈ M := h.X_norm x hxX
  have hζ1 : ψ ⟨x, hxN⟩ ≠ 1 := by
    intro h1
    exact hxmove ((barAct_eq_one_iff _).1 ((a7Act_eq_one_iff e _).1 h1))
  set F' : Subgroup ↥Z := (D.subgroupOf M).map φ with hF'
  have hF'card : Nat.card F' = Nat.card D := by
    have hbij : Function.Bijective (φ.subgroupMap (D.subgroupOf M)) := by
      refine ⟨?_, φ.subgroupMap_surjective _⟩
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro m hm
      have h1 : φ (m : ↥M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hm)
      have h1' : ψ (m : ↥M) = 1 := congrArg Subtype.val h1
      have hmD : ((m : ↥M) : G) ∈ D := Subgroup.mem_subgroupOf.mp m.2
      have := hfaith _ hmD h1'
      exact Subtype.ext (Subtype.ext this)
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv
  have hF'4 : 4 ≤ Nat.card F' := by rw [hF'card]; exact h.D_card
  have hF'2 : ∀ f ∈ F', f * f = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul]
    have : m * m = 1 := Subtype.ext (hD2 m (Subgroup.mem_subgroupOf.mp hm))
    rw [this, map_one]
  have hζmem : ∀ f ∈ F', f ≠ 1 → φ ⟨x, hxN⟩ ∈ involutionOddCore f := by
    rintro _ ⟨m, hm, rfl⟩ hf1
    have hmD : (m : G) ∈ D := Subgroup.mem_subgroupOf.mp hm
    have hm1 : (m : G) ≠ 1 := by
      intro hm1
      apply hf1
      have : m = 1 := Subtype.ext hm1
      rw [this, map_one]
    exact map_mem_involutionOddCore φ hφ (d := (m : G)) m.2 (hD2 _ hmD) hxN
      (h.mem_core hB hxX hmD hm1)
  have hζ : φ ⟨x, hxN⟩ ∈ deltaCore F' := by
    have : Subgroup.zpowers (φ ⟨x, hxN⟩) ≤ deltaCore F' :=
      le_deltaCore fun f hf hf1 => Subgroup.zpowers_le.2 (hζmem f hf hf1)
    exact this (Subgroup.mem_zpowers _)
  have hζ1' : φ ⟨x, hxN⟩ ≠ 1 := fun h1 => hζ1 (congrArg Subtype.val h1)
  have hFalt' := a7_even hZA hF'2 hζ hζ1'
  have hFeq : (D.subgroupOf M).map ψ = F'.map Z.subtype := by
    rw [hF', Subgroup.map_map]
    rfl
  set F : Subgroup (Perm (Fin 7)) := (D.subgroupOf M).map ψ with hF
  have hFcard : Nat.card F = Nat.card D := by
    rw [hFeq, Subgroup.card_map_of_injective Z.subtype_injective, hF'card]
  have hF2 : ∀ f ∈ F, f * f = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul]
    have : m * m = 1 := Subtype.ext (hD2 m (Subgroup.mem_subgroupOf.mp hm))
    rw [this, map_one]
  have hFalt : ∀ f ∈ F, f ∈ alternatingGroup (Fin 7) := by
    intro f hf
    rw [hFeq] at hf
    obtain ⟨f', hf', rfl⟩ := hf
    exact hFalt' f' hf'
  have hζodd : Odd (orderOf (ψ ⟨x, hxN⟩)) := by
    have h1 : orderOf (ψ ⟨x, hxN⟩) ∣ orderOf (⟨x, hxN⟩ : ↥M) := orderOf_map_dvd ψ _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat (h.odd_orderOf hB hxX) h1
  have hζc : ∀ f ∈ F, f * ψ ⟨x, hxN⟩ = ψ ⟨x, hxN⟩ * f := by
    rintro _ ⟨m, hm, rfl⟩
    have hmD : (m : G) ∈ D := Subgroup.mem_subgroupOf.mp hm
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (h.comm_D hB hxX hmD).symm
  exact (root_of_commuting (by rw [hFcard]; exact h.D_card) hF2 hFalt hζodd hζ1 hζc).1

theorem obs_A7_B {B : Subgroup G} {a : G} {J D : Subgroup G} (h : ObsData B a J D)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (hBN : ∀ g ∈ B, g ∈ normalizer (J : Set G))
    (e : kBar J ≃* alternatingGroup (Fin 7)) :
    ∃ t : Perm (Fin 7), t.IsSwap ∧
      (∀ i, (∃ f ∈ (D.subgroupOf (normalizer (J : Set G))).map (a7Act J e), f i ≠ i) → t i = i) ∧
      (B.subgroupOf (normalizer (J : Set G))).map (a7Act J e) =
        (D.subgroupOf (normalizer (J : Set G))).map (a7Act J e) ⊔ Subgroup.zpowers t := by
  classical
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  set M : Subgroup G := normalizer (J : Set G) with hM
  set ψ : ↥M →* Perm (Fin 7) := a7Act J e with hψ
  have hF := obs_root h hB e
  have hDB : D.subgroupOf M ≤ B.subgroupOf M := fun m hm => h.D_le hm
  have hFE : (D.subgroupOf M).map ψ ≤ (B.subgroupOf M).map ψ := Subgroup.map_mono hDB
  have hE2 : ∀ e' ∈ (B.subgroupOf M).map ψ, e' * e' = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul]
    have : m * m = 1 := Subtype.ext (hBsq m (Subgroup.mem_subgroupOf.mp hm))
    rw [this, map_one]
  have hEc : ∀ e₁ ∈ (B.subgroupOf M).map ψ, ∀ e₂ ∈ (B.subgroupOf M).map ψ, e₁ * e₂ = e₂ * e₁ := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hBc _ (Subgroup.mem_subgroupOf.mp hm) _ (Subgroup.mem_subgroupOf.mp hn)
  have hnot : ¬ (B.subgroupOf M).map ψ ≤ (D.subgroupOf M).map ψ := by
    intro hEF
    obtain ⟨y, β, hy, hβ, hx, -, hnc⟩ := h.exists_noncomm hB hBN
    have hxX : ⁅y, β⁆ ∈ ⁅AG D ⊓ centralizer ({a} : Set G), B⁆ :=
      Subgroup.commutator_mem_commutator hy hβ
    have hβE : ψ ⟨β, hBN β hβ⟩ ∈ (B.subgroupOf M).map ψ :=
      ⟨⟨β, hBN β hβ⟩, Subgroup.mem_subgroupOf.mpr hβ, rfl⟩
    obtain ⟨m, hm, hmβ⟩ := hEF hβE
    have hmD : (m : G) ∈ D := Subgroup.mem_subgroupOf.mp hm
    apply hnc
    have hcomm : ψ ⟨β, hBN β hβ⟩ * ψ ⟨⁅y, β⁆, hx⟩ = ψ ⟨⁅y, β⁆, hx⟩ * ψ ⟨β, hBN β hβ⟩ := by
      rw [← hmβ, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (h.comm_D hB hxX hmD).symm
    exact (a7Act_comm_iff e _ _).1 hcomm
  obtain ⟨t, ht, hdisj, hEeq⟩ := a7_E_structure hF hFE hE2 hEc hnot
  exact ⟨t, ht, hdisj, hEeq⟩

end Act

end CFSG.GH74.GLS.Th2.Obs
