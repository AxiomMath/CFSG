module

public import CFSG.Holt.General.ComponentsImage
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36W

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}

omit [Fintype α] in
theorem swap_mul_swap_apply_of_ne {i j z : α} (h1 : z ≠ i) (h2 : z ≠ σ i) (h3 : z ≠ j)
    (h4 : z ≠ σ j) : (swap i (σ i) * swap j (σ j)) z = z := by
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]

omit [Fintype α] in
theorem apply_mem_of_commute_swap_mul_swap (hσ : σ * σ = 1) {π : Perm α} {i j : α}
    (hi : σ i ≠ i) (hji : j ≠ i) (hjσ : j ≠ σ i)
    (hπ : π * (swap i (σ i) * swap j (σ j)) = swap i (σ i) * swap j (σ j) * π) :
    π i = i ∨ π i = σ i ∨ π i = j ∨ π i = σ j := by
  have hσσ : ∀ v, σ (σ v) = v := fun v => by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  by_contra h
  simp only [not_or] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hiσj : i ≠ σ j := fun h => hjσ (by rw [h, hσσ])
  have hτi : (swap i (σ i) * swap j (σ j)) i = σ i := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hji.symm hiσj, swap_apply_left]
  have h5 : π ((swap i (σ i) * swap j (σ j)) i) = (swap i (σ i) * swap j (σ j)) (π i) := by
    rw [← Perm.mul_apply, hπ, Perm.mul_apply]
  rw [hτi, swap_mul_swap_apply_of_ne h1 h2 h3 h4] at h5
  exact hi (π.injective h5)

theorem apply_eq_or_of_commute (hσ : σ * σ = 1) (h6 : 6 ≤ σ.support.card) {π : Perm α}
    (hc : ∀ i ∈ σ.support, ∀ j ∈ σ.support, j ≠ i → j ≠ σ i →
      π * (swap i (σ i) * swap j (σ j)) = swap i (σ i) * swap j (σ j) * π)
    {i : α} (hi : i ∈ σ.support) : π i = i ∨ π i = σ i := by
  have hσσ : ∀ v, σ (σ v) = v := fun v => by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  have hi' : σ i ≠ i := Perm.mem_support.mp hi
  obtain ⟨j, hj, hjn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {i, σ i}) (t := σ.support) (lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hjn
  obtain ⟨j', hj', hj'n⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {i, σ i, j, σ j}) (t := σ.support) (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj'n
  obtain ⟨hj'1, hj'2, hj'3, hj'4⟩ := hj'n
  have hA := apply_mem_of_commute_swap_mul_swap hσ hi' hjn.1 hjn.2 (hc i hi j hj hjn.1 hjn.2)
  have hB := apply_mem_of_commute_swap_mul_swap hσ hi' hj'1 hj'2 (hc i hi j' hj' hj'1 hj'2)
  have e1 : j ≠ σ j' := fun h => hj'4 (by rw [h, hσσ])
  have e3 : σ j ≠ i := fun h => hjn.2 (by rw [← h, hσσ])
  have e4 : σ j ≠ σ i := fun h => hjn.1 (σ.injective h)
  have e2 : σ j ≠ σ j' := fun h => hj'3 (σ.injective h).symm
  rcases hA with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · rcases hB with h' | h' | h' | h'
    · exact absurd (h.symm.trans h') hjn.1
    · exact absurd (h.symm.trans h') hjn.2
    · exact absurd (h'.symm.trans h) hj'3
    · exact absurd (h.symm.trans h') e1
  · rcases hB with h' | h' | h' | h'
    · exact absurd (h.symm.trans h') e3
    · exact absurd (h.symm.trans h') e4
    · exact absurd (h'.symm.trans h) hj'4
    · exact absurd (h.symm.trans h') e2

theorem apply_apply_comm (hσ : σ * σ = 1) {π₁ π₂ : Perm α}
    (h₁ : ∀ i ∈ σ.support, π₁ i = i ∨ π₁ i = σ i) (h₂ : ∀ i ∈ σ.support, π₂ i = i ∨ π₂ i = σ i)
    {i : α} (hi : i ∈ σ.support) : π₁ (π₂ i) = π₂ (π₁ i) := by
  have hσσ : ∀ v, σ (σ v) = v := fun v => by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  have hi' : σ i ≠ i := Perm.mem_support.mp hi
  have hσi : σ i ∈ σ.support := Perm.mem_support.mpr (by rw [hσσ]; exact hi'.symm)
  have hcomm : ∀ π : Perm α, (∀ i ∈ σ.support, π i = i ∨ π i = σ i) → π (σ i) = σ (π i) := by
    intro π hπ
    rcases hπ i hi with h | h
    · rcases hπ (σ i) hσi with h' | h'
      · rw [h', h]
      · exact absurd (π.injective (h'.trans ((hσσ i).trans h.symm))) hi'
    · rcases hπ (σ i) hσi with h' | h'
      · exact absurd (π.injective (h'.trans h.symm)) hi'
      · rw [h', h]
  rcases h₂ i hi with h | h
  · rw [h]
    rcases h₁ i hi with h' | h'
    · rw [h', h]
    · rw [h', hcomm π₂ h₂, h]
  · rw [h, hcomm π₁ h₁]
    rcases h₁ i hi with h' | h'
    · rw [h', h]
    · rw [h', hcomm π₂ h₂, h]

theorem mul_comm_of_fix (hF : Fintype.card α - σ.support.card ≤ 3) {π₁ π₂ : Perm α}
    (hA₁ : π₁ ∈ alternatingGroup α) (hA₂ : π₂ ∈ alternatingGroup α)
    (h₁ : ∀ i ∈ σ.support, π₁ i = i) (h₂ : ∀ i ∈ σ.support, π₂ i = i) :
    π₁ * π₂ = π₂ * π₁ := by
  have hp : ∀ π : Perm α, (∀ i ∈ σ.support, π i = i) →
      ∀ x, π x ∉ σ.support ↔ x ∉ σ.support := by
    intro π hπ x
    constructor
    · intro h hx
      exact h (by rw [hπ x hx]; exact hx)
    · intro h hπx
      have h1 := hπ _ hπx
      exact h (by rw [← π.injective h1]; exact hπx)
  have hq : ∀ π : Perm α, (∀ i ∈ σ.support, π i = i) → ∀ x, π x ≠ x → x ∉ σ.support :=
    fun π hπ x hx hxs => hx (hπ x hxs)
  have hcard : Nat.card {x // x ∉ σ.support} ≤ 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe]
    exact hF
  have : IsCyclic (alternatingGroup {x // x ∉ σ.support}) :=
    alternatingGroup.isCyclic_of_card_le_three hcard
  have key : ∀ (π : Perm α) (hπ : ∀ i ∈ σ.support, π i = i),
      Perm.ofSubtype (π.subtypePerm (p := fun x => x ∉ σ.support) (hp π hπ)) = π :=
    fun π hπ => Perm.ofSubtype_subtypePerm _ (hq π hπ)
  have hA : ∀ (π : Perm α) (hπ : ∀ i ∈ σ.support, π i = i), π ∈ alternatingGroup α →
      π.subtypePerm (p := fun x => x ∉ σ.support) (hp π hπ) ∈
        alternatingGroup {x // x ∉ σ.support} := by
    intro π hπ hπA
    rw [Perm.mem_alternatingGroup, Perm.sign_subtypePerm _ _ (hq π hπ)]
    exact Perm.mem_alternatingGroup.mp hπA
  have hc := (IsMulCommutative.is_comm (M := alternatingGroup {x // x ∉ σ.support})).comm
    ⟨_, hA π₁ h₁ hA₁⟩ ⟨_, hA π₂ h₂ hA₂⟩
  have hc' := congrArg (fun s => Perm.ofSubtype (Subtype.val s)) hc
  simp only [Subgroup.coe_mul, map_mul] at hc'
  rwa [key π₁ h₁, key π₂ h₂] at hc'

theorem eq_bot_of_perfect_of_commute (hσ : σ * σ = 1) (hF : Fintype.card α - σ.support.card ≤ 3)
    (h6 : 6 ≤ σ.support.card) {P : Subgroup (Perm α)} (hP : ⁅P, P⁆ = P)
    (hc : ∀ π ∈ P, ∀ i ∈ σ.support, ∀ j ∈ σ.support, j ≠ i → j ≠ σ i →
      π * (swap i (σ i) * swap j (σ j)) = swap i (σ i) * swap j (σ j) * π) :
    P = ⊥ := by
  have hai : ∀ (f : Perm α) (x : α), f (f⁻¹ x) = x := fun f x => by
    rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
  have hpair : ∀ π ∈ P, ∀ i ∈ σ.support, π i = i ∨ π i = σ i := fun π hπ i hi =>
    apply_eq_or_of_commute hσ h6 (hc π hπ) hi
  let T : Subgroup (Perm α) :=
    { carrier := {π | π ∈ alternatingGroup α ∧ ∀ i ∈ σ.support, π i = i}
      mul_mem' := by
        rintro π₁ π₂ ⟨hA₁, h₁⟩ ⟨hA₂, h₂⟩
        exact ⟨mul_mem hA₁ hA₂, fun i hi => by rw [Perm.mul_apply, h₂ i hi, h₁ i hi]⟩
      one_mem' := ⟨one_mem _, fun i _ => rfl⟩
      inv_mem' := by
        rintro π ⟨hA, h⟩
        exact ⟨inv_mem hA, fun i hi => by rw [Perm.inv_eq_iff_eq, h i hi]⟩ }
  have hPT : P ≤ T := by
    rw [← hP, commutator_le]
    intro π₁ hπ₁ π₂ hπ₂
    refine ⟨?_, fun i hi => ?_⟩
    · rw [Perm.mem_alternatingGroup, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    · have h := apply_apply_comm hσ (hpair _ (inv_mem hπ₁)) (hpair _ (inv_mem hπ₂)) hi
      rw [commutatorElement_def, Perm.mul_apply, Perm.mul_apply, Perm.mul_apply, h, hai, hai]
  rw [← hP, eq_bot_iff, commutator_le]
  intro π₁ hπ₁ π₂ hπ₂
  obtain ⟨hA₁, h₁⟩ := hPT hπ₁
  obtain ⟨hA₂, h₂⟩ := hPT hπ₂
  rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm_of_fix hF hA₁ hA₂ h₁ h₂

end Perm

variable {X : Type} [Group X] {M : Subgroup X} {r : ℕ}
  {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}

theorem IsPermAction.not_isPComponent_of_fix_le_three (hρ : IsPermAction θ ρ) [Finite X]
    (hr : 4 ≤ r) {c : X} (hcN : c ∈ normalizer (M : Set X)) (hc2 : c * c = 1)
    (hfix : r - (ρ ⟨c, hcN⟩).support.card ≤ 3) (h6 : 6 ≤ (ρ ⟨c, hcN⟩).support.card)
    {Y : Subgroup X} (hMY : M ⊓ centralizer ({c} : Set X) ≤ Y)
    (hYN : Y ≤ normalizer (M : Set X)) (hYC : Y ≤ centralizer ({c} : Set X))
    {R : Subgroup X} (hRM : R ≤ M) (hRY : R ≤ Y) : ¬ IsPComponent 2 (R.subgroupOf Y) := by
  classical
  intro hRpc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := ρ ⟨c, hcN⟩ with hσdef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul, show (⟨c, hcN⟩ : ↥(normalizer (M : Set X))) * ⟨c, hcN⟩ = 1 from
      Subtype.ext hc2, map_one]
  have hσσ : ∀ v, σ (σ v) = v := fun v => by rw [← Perm.mul_apply, hσ2, Perm.one_apply]
  have hai : ∀ (f : Perm (Fin r)) (x : Fin r), f (f⁻¹ x) = x := fun f x => by
    rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
  let φ : ↥Y →* Perm (Fin r) := ρ.comp (Subgroup.inclusion hYN)
  have hφ : ∀ y : ↥Y, φ y = ρ ⟨y, hYN y.2⟩ := fun _ => rfl
  have hφσ : ∀ y : ↥Y, φ y * σ = σ * φ y := by
    intro y
    rw [hφ, hσdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hYC y.2))
  have hker : ¬ R.subgroupOf Y ≤ φ.rangeRestrict.ker := by
    intro hle
    refine UnbalancedCorr.not_le_of_isPComponent_of_coprime hRY hRpc
      (Y := (pPrimeCore 2 ↥M).map M.subtype)
      (by rw [card_map_of_injective M.subtype_injective]; exact pPrimeCore_coprime_card) ?_
    intro z hz
    have h1 : (⟨z, hRY hz⟩ : ↥Y) ∈ φ.rangeRestrict.ker :=
      hle (show (⟨z, hRY hz⟩ : ↥Y) ∈ R.subgroupOf Y from hz)
    rw [MonoidHom.mem_ker] at h1
    have h2 : ρ ⟨z, hYN (hRY hz)⟩ = 1 := congrArg Subtype.val h1
    exact mem_core_of_mem_coreActionKernel hρ hr (hRM hz) (hρ.mem_coreActionKernel _ h2)
  have himg := CFSG.Holt.General.isPComponent_map φ.rangeRestrict_surjective hRpc hker
  let N : Subgroup (Perm (Fin r)) :=
    { carrier := {π | ∀ v, π v = v ∨ π v = σ v}
      mul_mem' := by
        intro π₁ π₂ h₁ h₂ v
        rw [Perm.mul_apply]
        rcases h₂ v with h | h
        · rw [h]
          exact h₁ v
        · rw [h]
          rcases h₁ (σ v) with h' | h'
          · exact Or.inr h'
          · exact Or.inl (h'.trans (hσσ v))
      one_mem' := fun v => Or.inl rfl
      inv_mem' := by
        intro π h v
        rcases h (π⁻¹ v) with h' | h'
        · rw [hai] at h'
          exact Or.inl h'.symm
        · rw [hai] at h'
          exact Or.inr ((hσσ _).symm.trans (congrArg σ h'.symm)) }
  have hNsq : ∀ π ∈ N, π * π = 1 := by
    intro π hπ
    refine Equiv.Perm.ext fun v => ?_
    rw [Perm.mul_apply, Perm.one_apply]
    rcases hπ v with h | h
    · rw [h, h]
    · rcases hπ (σ v) with h' | h'
      · by_cases hv : σ v = v
        · rw [h, h', hv]
        · exact absurd (π.injective (h.trans h'.symm)).symm hv
      · rw [h, h', hσσ]
  have hNn : (N.subgroupOf φ.range).Normal := by
    refine ⟨fun π hπ k v => ?_⟩
    obtain ⟨y, hy⟩ := k.2
    have hkσ : (k : Perm (Fin r)) * σ = σ * k := by rw [← hy]; exact hφσ y
    have hkσ' : ∀ w, (k : Perm (Fin r)) (σ w) = σ ((k : Perm (Fin r)) w) := fun w => by
      rw [← Perm.mul_apply, hkσ, Perm.mul_apply]
    have hπ' : ∀ w, (π : Perm (Fin r)) w = w ∨ (π : Perm (Fin r)) w = σ w := hπ
    change ((k : Perm (Fin r)) * π * (k : Perm (Fin r))⁻¹) v = v ∨
      ((k : Perm (Fin r)) * π * (k : Perm (Fin r))⁻¹) v = σ v
    rw [Perm.mul_apply, Perm.mul_apply]
    rcases hπ' ((k : Perm (Fin r))⁻¹ v) with h | h
    · rw [h, hai]
      exact Or.inl rfl
    · rw [h, hkσ', hai]
      exact Or.inr rfl
  have hN2 : IsPGroup 2 (N.subgroupOf φ.range) := by
    intro π
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [pow_one, sq]
    exact hNsq _ π.2
  have hcomm := TwoComponentCentralizers.commutes_with_normal_two _ _
    ((CatalogueBAlternating.pComponent_two_iff _).1 himg) hN2
  have hτ : ∀ i ∈ σ.support, ∀ j ∈ σ.support, j ≠ i → j ≠ σ i →
      swap i (σ i) * swap j (σ j) ∈ N ∧ swap i (σ i) * swap j (σ j) ∈ φ.range := by
    intro i hi j hj hji hjσ
    have hi' : σ i ≠ i := Perm.mem_support.mp hi
    have hj' : σ j ≠ j := Perm.mem_support.mp hj
    have hiσj : i ≠ σ j := fun h => hjσ (by rw [h, hσσ])
    have hσiσj : σ i ≠ σ j := fun h => hji (σ.injective h).symm
    have hσij : σ i ≠ j := fun h => hjσ h.symm
    have hτN : swap i (σ i) * swap j (σ j) ∈ N := by
      intro v
      by_cases h1 : v = i
      · subst h1
        right
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hji.symm hiσj, swap_apply_left]
      by_cases h2 : v = σ i
      · subst h2
        right
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hσij hσiσj, swap_apply_right, hσσ]
      by_cases h3 : v = j
      · subst h3
        right
        rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hiσj.symm hσiσj.symm]
      by_cases h4 : v = σ j
      · subst h4
        right
        rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hji hjσ, hσσ]
      · left
        exact swap_mul_swap_apply_of_ne h1 h2 h3 h4
    refine ⟨hτN, ?_⟩
    have hτA : swap i (σ i) * swap j (σ j) ∈ alternatingGroup (Fin r) := by
      rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hi'.symm, Perm.sign_swap hj'.symm]
      rfl
    have hτσ : swap i (σ i) * swap j (σ j) * σ = σ * (swap i (σ i) * swap j (σ j)) := by
      refine Equiv.Perm.ext fun v => ?_
      change (swap i (σ i) * swap j (σ j)) (σ v) = σ ((swap i (σ i) * swap j (σ j)) v)
      by_cases hv : σ v = v
      · have hτv : (swap i (σ i) * swap j (σ j)) v = v := by
          rcases hτN v with h | h
          · exact h
          · exact h.trans hv
        rw [hv, hτv, hv]
      · rcases hτN v with h | h <;> rcases hτN (σ v) with h' | h'
        · rw [h', h]
        · exact absurd ((swap i (σ i) * swap j (σ j)).injective
            (h'.trans ((hσσ v).trans h.symm))) hv
        · exact absurd ((swap i (σ i) * swap j (σ j)).injective (h'.trans h.symm)) hv
        · rw [h', h]
    obtain ⟨w, hwC, hw⟩ := hρ.exists_lift hcN hc2 (b := ⟨_, hτA⟩) hτσ
    refine ⟨⟨w, hMY ⟨w.2, hwC⟩⟩, ?_⟩
    rw [hφ]
    change ρ ⟨w, le_normalizer w.2⟩ = _
    rw [hρ.apply_of_mem hr w, hw]
  have hP : (R.subgroupOf Y).map φ = ⊥ := by
    have hperf : ⁅R.subgroupOf Y, R.subgroupOf Y⁆ = R.subgroupOf Y :=
      Subgroup.isPerfect_iff.mp (CatalogueBAlternating.pComponent_perfect hRpc)
    refine eq_bot_of_perfect_of_commute hσ2 (by rw [Fintype.card_fin]; exact hfix) h6
      (by rw [← map_commutator, hperf]) ?_
    rintro _ ⟨z, hz, rfl⟩ i hi j hj hji hjσ
    obtain ⟨hτN, hτI⟩ := hτ i hi j hj hji hjσ
    have hz' : φ.rangeRestrict z ∈
        centralizer ((N.subgroupOf φ.range : Subgroup ↥φ.range) : Set ↥φ.range) :=
      (commutator_eq_bot_iff_le_centralizer.mp hcomm) (mem_map_of_mem _ hz)
    have h1 := mem_centralizer_iff.mp hz' ⟨_, hτI⟩ hτN
    exact (congrArg Subtype.val h1).symm
  apply hker
  intro z hz
  have h1 : φ z = 1 := by
    have h2 : φ z ∈ (R.subgroupOf Y).map φ := mem_map_of_mem _ hz
    rw [hP] at h2
    exact h2
  rw [MonoidHom.mem_ker]
  exact Subtype.ext h1

end CFSG.ComponentClassification.SolMax
