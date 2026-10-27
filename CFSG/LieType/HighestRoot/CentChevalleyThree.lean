module

public import CFSG.LieType.HighestRoot.CentChevalley
public import CFSG.LieType.HighestRoot.CentChevalleyCenter
public import CFSG.LieType.HighestRoot.CentChevalleyToral
public import CFSG.LieType.HighestRoot.CentChevalleySLThree
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement Matrix

variable {τ : Tag} {K : Type} [Field K]

section Prelim

theorem signTuple_eq_one_or_eq_neg_one (i j : Fin τ.rank) :
    signTuple τ K i j = 1 ∨ signTuple τ K i j = -1 := by
  rcases Int.even_or_odd (τ.cartan i j) with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow

theorem ringChar_ne_two_of_card_eq_three [Finite K] (hK3 : Nat.card K = 3) : ringChar K ≠ 2 := by
  intro h2
  have h2' : (2 : K) = 0 := by
    have h := ringChar.Nat.cast_ringChar (R := K)
    rw [h2] at h
    exact_mod_cast h
  have h3 := three_eq_zero hK3
  exact one_ne_zero (by linear_combination h3 - h2' : (1 : K) = 0)

theorem iform_le_of_symmetrizer_le
    {i : Fin τ.rank}
    (hlong : ∀ j, τ.symmetrizer j j ≤ τ.symmetrizer i i) :
    ∀ ε, IsRoot τ ε → iform ε ε ≤ iform (Pi.single i 1) (Pi.single i 1) := by
  intro ε hε
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hε
  rw [hj, iform_single_single]
  linarith [hlong j]

theorem iform_neg_self_ne_zero
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) : iform (-α) α ≠ 0 := by
  rw [← neg_one_smul ℤ α, iform_smul_left]
  have := iform_self_pos hα.ne_zero
  omega

theorem ne_neg_of_isRoot
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) : α ≠ -α := by
  intro h
  refine hα.ne_zero (funext fun k => ?_)
  have h2 := congrFun h k
  simp only [Pi.neg_apply] at h2
  simp only [Pi.zero_apply]
  omega

theorem not_isSolvable_of_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  have := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have := hQ.1
  exact Group.IsPerfect.not_isSolvable Q

end Prelim

section Classes

variable (τ K) in
noncomputable abbrev signChar (i : Fin τ.rank) : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ :=
  maskChar (signTupleBits (signTuple τ K i))

variable {i : Fin τ.rank}

theorem rootCharKernel_signTuple_eq
    (hK : ringChar K ≠ 2) :
    rootCharKernel (signTuple τ K i) = kernelRoots (signChar τ K i) :=
  rootCharKernel_eq_kernelRoots hK (signTuple_eq_one_or_eq_neg_one i)

theorem mem_pair_iff_of_mk_eq_of_iform
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {β : Fin τ.rank → ℤ}
    (horth : ∀ α ∈ kernelRoots χ, α ≠ β → α ≠ -β → iform α β = 0)
    {α γ : kernelRoots χ} (h : (⟦α⟧ : KernelComponent χ) = ⟦γ⟧) :
    ((α : Fin τ.rank → ℤ) = β ∨ (α : Fin τ.rank → ℤ) = -β) ↔
      ((γ : Fin τ.rank → ℤ) = β ∨ (γ : Fin τ.rank → ℤ) = -β) := by
  have key : ∀ δ : kernelRoots χ, iform (δ : Fin τ.rank → ℤ) β ≠ 0 →
      (δ : Fin τ.rank → ℤ) = β ∨ (δ : Fin τ.rank → ℤ) = -β := by
    intro δ hδ
    by_contra hne
    rw [not_or] at hne
    exact hδ (horth δ δ.2 hne.1 hne.2)
  have step : ∀ a b : kernelRoots χ, iform (a : Fin τ.rank → ℤ) b ≠ 0 →
      ((a : Fin τ.rank → ℤ) = β ∨ (a : Fin τ.rank → ℤ) = -β) →
      ((b : Fin τ.rank → ℤ) = β ∨ (b : Fin τ.rank → ℤ) = -β) := by
    intro a b hab ha
    refine key b ?_
    rw [iform_comm]
    rcases ha with ha | ha
    · rwa [← ha]
    · rw [ha, ← neg_one_smul ℤ β, iform_smul_left] at hab
      intro h0
      exact hab (by rw [h0, mul_zero])
  have hr : Relation.EqvGen (fun a b : kernelRoots χ =>
      (a : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (b : Fin τ.rank → ℤ)) ≠ 0) α γ :=
    Quotient.exact h
  clear h
  induction hr with
  | rel a b hab =>
    have hab' : iform (a : Fin τ.rank → ℤ) b ≠ 0 := by rwa [← dotProduct_mulVec_eq_iform]
    have hba : iform (b : Fin τ.rank → ℤ) a ≠ 0 := by rwa [iform_comm]
    exact ⟨step a b hab', step b a hba⟩
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem mem_pair_iff_of_mk_eq
    (hK : ringChar K ≠ 2)
    (hlong : ∀ ε, IsRoot τ ε → iform ε ε ≤ iform (Pi.single i 1) (Pi.single i 1))
    {α β : kernelRoots (signChar τ K i)} (h : (⟦α⟧ : KernelComponent (signChar τ K i)) = ⟦β⟧) :
    ((α : Fin τ.rank → ℤ) = Pi.single i 1 ∨ (α : Fin τ.rank → ℤ) = -Pi.single i 1) ↔
      ((β : Fin τ.rank → ℤ) = Pi.single i 1 ∨ (β : Fin τ.rank → ℤ) = -Pi.single i 1) := by
  have hker := rootCharKernel_signTuple_eq (i := i) hK
  refine mem_pair_iff_of_mk_eq_of_iform (fun α hα hne hne' => ?_) h
  exact iform_eq_zero_of_mem_rootCharKernel_signTuple hK hlong (by rw [hker]; exact hα) hne hne'

theorem two_lt_ncard_componentRoots
    (hK : ringChar K ≠ 2) {wit : List ℕ}
    (hc : isolatedCheck τ i wit = true)
    (hγ : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ kernelRoots (signChar τ K i))
    {k : KernelComponent (signChar τ K i)} (hk : k ≠ ⟦⟨Pi.single i 1, hγ⟩⟧) :
    2 < (componentRoots (signChar τ K i) k).ncard := by
  have hker := rootCharKernel_signTuple_eq (i := i) hK
  induction k using Quotient.inductionOn with
  | h α =>
  obtain ⟨α, hα⟩ := α
  have hne : α ≠ Pi.single i 1 := by
    rintro rfl
    exact hk rfl
  have hne' : α ≠ -Pi.single i 1 := by
    rintro rfl
    exact hk (mk_eq_of_iform_ne_zero (iform_neg_self_ne_zero (isRoot_single τ i)))
  obtain ⟨ε, hε, -, -, hεα, hεα', hαε⟩ := exists_of_isolatedCheck hK hc (hker ▸ hα) hne hne'
  have hε' : ε ∈ kernelRoots (signChar τ K i) := hker ▸ hε
  have hnα : -α ∈ kernelRoots (signChar τ K i) := ⟨IsRoot.neg hα.1, chi_neg hα.2⟩
  have hfin : (componentRoots (signChar τ K i) ⟦⟨α, hα⟩⟧).Finite :=
    (finite_setOf_isRoot τ).subset fun β ⟨h, _⟩ => h.1
  refine (Set.two_lt_ncard_iff hfin).2 ⟨α, -α, ε, ⟨hα, rfl⟩,
    ⟨hnα, mk_eq_of_iform_ne_zero (iform_neg_self_ne_zero hα.1)⟩,
    ⟨hε', (mk_eq_of_iform_ne_zero (β := ⟨ε, hε'⟩) hαε).symm⟩, ne_neg_of_isRoot hα.1,
    Ne.symm hεα, Ne.symm hεα'⟩

end Classes

section Decomposition

variable {M : Type*} [CommGroup M]

open _root_.Classical in
theorem exists_eq_mul_of_commute
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (k₀ : KernelComponent χ) {x : ModGL τ K} (hxS : x ∈ rootSpan τ K (kernelRoots χ))
    (hxk : ∀ k, k ≠ k₀ → ∀ y ∈ componentRootSpan K χ k, x * y = y * x) :
    ∃ j ∈ componentRootSpan K χ k₀, ∃ t ∈ torusGroup τ K ⊓
      Subgroup.centralizer (componentRootSpan K χ k₀ : Set (ModGL τ K)), x = t * j := by
  obtain ⟨-, hfinI, hcomm, -, ⟨μ, hμ, hμs, -⟩, -⟩ :=
    root_character_kernel_orthogonal_central_product τ K χ
  set J := componentRootSpan K χ k₀ with hJ
  obtain ⟨t, ht⟩ := hμs ⟨x, hxS⟩
  have hμt : ((μ t : rootSpan τ K (kernelRoots χ)) : ModGL τ K) = x := congrArg Subtype.val ht
  have htk : ∀ k, k ≠ k₀ → t k ∈ Subgroup.center (componentRootSpan K χ k) := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro y
    have hxy : x * y = y * x := hxk k hk y y.2
    have hc : t * Pi.mulSingle k y * t⁻¹ * (Pi.mulSingle k y)⁻¹ =
        Pi.mulSingle k (t k * y * (t k)⁻¹ * y⁻¹) := by
      ext k' : 1
      by_cases hk' : k' = k
      · subst hk'
        simp
      · simp [Pi.mulSingle_eq_of_ne hk']
    have h1 := congrArg (fun s => ((μ s : rootSpan τ K (kernelRoots χ)) : ModGL τ K)) hc
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hμt, hμ] at h1
    have h2 : ((t k * y * (t k)⁻¹ * y⁻¹ : componentRootSpan K χ k) : ModGL τ K) = 1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← h1, hxy]
      group
    have h3 : t k * y * (t k)⁻¹ * y⁻¹ = 1 := Subtype.ext h2
    calc y * t k = (t k * y * (t k)⁻¹ * y⁻¹)⁻¹ * (t k * y) := by group
      _ = t k * y := by rw [h3, inv_one, one_mul]
  set t' := t * (Pi.mulSingle k₀ (t k₀))⁻¹ with ht'
  have hT : ∀ k, ((t' k : componentRootSpan K χ k) : ModGL τ K) ∈
      torusGroup τ K ⊓ Subgroup.centralizer (J : Set (ModGL τ K)) := by
    intro k
    by_cases hk : k = k₀
    · subst hk
      simp [t']
    · have e : t' k = t k := by simp [t', Pi.mulSingle_eq_of_ne hk]
      rw [e]
      refine ⟨componentTorus_le_torusGroup K χ k
        (coe_mem_componentTorus_of_mem_center (htk k hk)), ?_⟩
      have hc := hcomm k k₀ hk
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
      exact hc (t k).2
  have hP : ((μ t' : rootSpan τ K (kernelRoots χ)) : ModGL τ K) ∈
      torusGroup τ K ⊓ Subgroup.centralizer (J : Set (ModGL τ K)) := by
    have h := Subgroup.pi_mem_of_mulSingle_mem (H := (torusGroup τ K ⊓
      Subgroup.centralizer (J : Set (ModGL τ K))).comap
        ((rootSpan τ K (kernelRoots χ)).subtype.comp μ)) t' fun k => by
      rw [Subgroup.mem_comap, MonoidHom.comp_apply, Subgroup.coe_subtype, hμ]
      exact hT k
    exact h
  refine ⟨t k₀, (t k₀).2, _, hP, ?_⟩
  have e : t = t' * Pi.mulSingle k₀ (t k₀) := by rw [ht', inv_mul_cancel_right]
  have h := congrArg (fun s => ((μ s : rootSpan τ K (kernelRoots χ)) : ModGL τ K)) e
  simp only [map_mul, Subgroup.coe_mul, hμt, hμ] at h
  exact h

open _root_.Classical in
theorem exists_eq_mul_of_mem_rootSpan
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (k : KernelComponent χ) {x : ModGL τ K} (hxS : x ∈ rootSpan τ K (kernelRoots χ)) :
    ∃ j ∈ componentRootSpan K χ k, ∃ c ∈ Subgroup.centralizer
      (componentRootSpan K χ k : Set (ModGL τ K)), x = c * j := by
  obtain ⟨-, hfinI, hcomm, -, ⟨μ, hμ, hμs, -⟩, -⟩ :=
    root_character_kernel_orthogonal_central_product τ K χ
  obtain ⟨t, ht⟩ := hμs ⟨x, hxS⟩
  have hμt : ((μ t : rootSpan τ K (kernelRoots χ)) : ModGL τ K) = x := congrArg Subtype.val ht
  set t' := t * (Pi.mulSingle k (t k))⁻¹ with ht'
  have hC : ∀ l, ((t' l : componentRootSpan K χ l) : ModGL τ K) ∈
      Subgroup.centralizer (componentRootSpan K χ k : Set (ModGL τ K)) := by
    intro l
    by_cases hl : l = k
    · subst hl
      simp [t']
    · have e : t' l = t l := by simp [t', Pi.mulSingle_eq_of_ne hl]
      rw [e]
      have hc := hcomm l k hl
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
      exact hc (t l).2
  have hP : ((μ t' : rootSpan τ K (kernelRoots χ)) : ModGL τ K) ∈
      Subgroup.centralizer (componentRootSpan K χ k : Set (ModGL τ K)) := by
    have h := Subgroup.pi_mem_of_mulSingle_mem (H := (Subgroup.centralizer
      (componentRootSpan K χ k : Set (ModGL τ K))).comap
        ((rootSpan τ K (kernelRoots χ)).subtype.comp μ)) t' fun l => by
      rw [Subgroup.mem_comap, MonoidHom.comp_apply, Subgroup.coe_subtype, hμ]
      exact hC l
    exact h
  refine ⟨t k, (t k).2, _, hP, ?_⟩
  have e : t = t' * Pi.mulSingle k (t k) := by rw [ht', inv_mul_cancel_right]
  have h := congrArg (fun s => ((μ s : rootSpan τ K (kernelRoots χ)) : ModGL τ K)) e
  simp only [map_mul, Subgroup.coe_mul, hμt, hμ] at h
  exact h

end Decomposition

section Main

variable [Finite K]

open _root_.Classical in
theorem eq_sup_of_card_eq_three
    (hK3 : Nat.card K = 3) {i : Fin τ.rank}
    (hlong : ∀ ε, IsRoot τ ε → iform ε ε ≤ iform (Pi.single i 1) (Pi.single i 1))
    {wit : List ℕ} (hc : isolatedCheck τ i wit = true) {L : Subgroup (ModGL τ K)}
    (hLX : L ≤ toralCentralizer τ K (signTuple τ K i))
    (hLN : rootSpan τ K (rootCharKernel (signTuple τ K i)) ≤
      Subgroup.normalizer (L : Set (ModGL τ K)))
    (eL : L ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    L = rootSubgroup τ K (Pi.single i 1) ⊔ rootSubgroup τ K (-Pi.single i 1) := by
  have hK := ringChar_ne_two_of_card_eq_three hK3
  have hker := rootCharKernel_signTuple_eq (i := i) hK
  set χ := signChar τ K i with hχ
  set γ : Fin τ.rank → ℤ := Pi.single i 1 with hγ_def
  set J := rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) with hJ_def
  have hγk : γ ∈ kernelRoots χ := hker ▸ single_mem_rootCharKernel_signTuple hK i
  set k₀ : KernelComponent χ := ⟦⟨γ, hγk⟩⟧ with hk₀
  obtain ⟨-, -, -, hnorm, -, -⟩ := root_character_kernel_orthogonal_central_product τ K χ
  have hS₀ : componentRootSpan K χ k₀ = J := by
    rw [hJ_def, ← rootSpan_pair_eq]
    change rootSpan τ K (componentRoots χ k₀) = _
    congr 1
    ext α
    constructor
    · rintro ⟨hα, hαk⟩
      exact (mem_pair_iff_of_mk_eq hK hlong hαk).2 (Or.inl rfl)
    · rintro (rfl | rfl)
      · exact ⟨hγk, rfl⟩
      · exact ⟨⟨IsRoot.neg hγk.1, chi_neg hγk.2⟩,
          mk_eq_of_iform_ne_zero (iform_neg_self_ne_zero hγk.1)⟩
  have hLS : L ≤ rootSpan τ K (kernelRoots χ) := by
    rw [← hker]
    exact le_rootSpan_of_closure_eq_top hK3 hK (signTuple_eq_one_or_eq_neg_one i) hLX
      (closure_orderOf_three_eq_top_of_mulEquiv hK3 eL)
  have hSL : rootSpan τ K (kernelRoots χ) ≤ Subgroup.normalizer (L : Set (ModGL τ K)) := by
    rw [← hker]
    exact hLN
  have hLk : ∀ k, k ≠ k₀ →
      componentRootSpan K χ k ≤ Subgroup.centralizer (L : Set (ModGL τ K)) := by
    intro k hk
    have hSk := (hnorm k).1
    have hSkN : rootSpan τ K (kernelRoots χ) ≤
        Subgroup.normalizer (componentRootSpan K χ k : Set (ModGL τ K)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSk).1 (hnorm k).2
    have hq : CFSG.IsQuasisimple (componentRootSpan K χ k) :=
      isQuasisimple_componentRootSpan hK (two_lt_ncard_componentRoots hK hc hγk hk)
    have hN : ((L ⊓ componentRootSpan K χ k).subgroupOf (componentRootSpan K χ k)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hnL, hnS⟩ := Subgroup.mem_inf.1 hn
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · simpa using (Subgroup.mem_normalizer_iff.1 (hSL (hSk g.2)) _).1 hnL
      · simpa using mul_mem (mul_mem g.2 hnS) (inv_mem g.2)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN with htop | hcen
    ·
      exfalso
      have hle : componentRootSpan K χ k ≤ L := fun x hx => by
        have h : (⟨x, hx⟩ : componentRootSpan K χ k) ∈
            (L ⊓ componentRootSpan K χ k).subgroupOf (componentRootSpan K χ k) :=
          htop ▸ Subgroup.mem_top _
        exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 h)).1
      have := isSolvable_of_mulEquiv hK3 eL
      exact not_isSolvable_of_isQuasisimple hq
        (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
          (Subgroup.inclusion_injective hle))
    ·
      have h1 : ⁅⁅componentRootSpan K χ k, L⁆, componentRootSpan K χ k⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        refine (Subgroup.commutator_le).2 fun s hs l hl => ?_
        have hmem : ⁅s, l⁆ ∈ L ⊓ componentRootSpan K χ k := by
          rw [commutatorElement_def]
          refine Subgroup.mem_inf.2 ⟨mul_mem ?_ (inv_mem hl), ?_⟩
          · exact (Subgroup.mem_normalizer_iff.1 (hSL (hSk hs)) l).1 hl
          · rw [mul_assoc, mul_assoc]
            refine mul_mem hs ?_
            have h := (Subgroup.mem_normalizer_iff.1 (hSkN (hLS hl)) s⁻¹).1 (inv_mem hs)
            rwa [← mul_assoc]
        have hz := hcen (Subgroup.mem_subgroupOf.2 hmem :
          (⟨⁅s, l⁆, hmem.2⟩ : componentRootSpan K χ k) ∈ _)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hy⟩)
      have h2 := CFSG.LocalCores.perfect_double_commutator hq.1 h1
      rwa [Subgroup.commutator_eq_bot_iff_le_centralizer] at h2
  have hdec : ∀ x ∈ L, ∃ j ∈ J, ∃ t ∈ torusGroup τ K ⊓ Subgroup.centralizer (J : Set _),
      x = t * j := by
    intro x hx
    rw [← hS₀]
    exact exists_eq_mul_of_commute χ k₀ (hLS hx) fun k hk y hy =>
      (Subgroup.mem_centralizer_iff.1 (hLk k hk hy)) x hx
  have h3 : ∀ x ∈ L, orderOf x = 3 → x ∈ J := by
    intro x hx hx3
    obtain ⟨j, hj, t, ⟨htT, htJ⟩, rfl⟩ := hdec x hx
    have ht2 : t ^ 2 = 1 := sq_eq_one_of_mem_torusGroup hK3 htT
    have hcomm' : Commute t j := ((Subgroup.mem_centralizer_iff.1 htJ) j hj).symm
    have hpow : (t * j) ^ 3 = 1 := by
      rw [← hx3]
      exact pow_orderOf_eq_one _
    rw [hcomm'.mul_pow, show t ^ 3 = t by rw [pow_succ, ht2, one_mul]] at hpow
    rw [eq_inv_of_mul_eq_one_left hpow]
    exact mul_mem (inv_mem (pow_mem hj 3)) hj
  have hgen := closure_orderOf_three_eq_top_of_mulEquiv hK3 eL
  have hle : L ≤ J := by
    intro x hx
    have hle' : Subgroup.closure {y : L | orderOf y = 3} ≤ J.subgroupOf L :=
      (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_subgroupOf.2
        (h3 y.1 y.2 (by rw [Subgroup.orderOf_coe]; exact hy))
    exact Subgroup.mem_subgroupOf.1 (hle' (hgen ▸ Subgroup.mem_top (⟨x, hx⟩ : L)))
  obtain ⟨eJ⟩ := (odd_arbitrary_root_pair_SL2_p_components τ K hK (isRoot_single τ i)).2.1
  have : Fintype K := Fintype.ofFinite K
  have : Finite J := Finite.of_equiv _ eJ.toEquiv
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_eq_24 hK3 eL, card_eq_24 hK3 eJ.symm]

end Main

section Datum

theorem mem_toralCentralizer_iff_mem_centralizer
    {a : Fin τ.rank → Kˣ} {z : adjointGroup τ K}
    (hzC : (z : ModGL τ K) = rootDiagUnit τ a) (y : adjointGroup τ K) :
    (y : ModGL τ K) ∈ toralCentralizer τ K a ↔
      y ∈ Subgroup.centralizer ({z} : Set (adjointGroup τ K)) := by
  rw [mem_toralCentralizer, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hzC]
    calc (y : ModGL τ K) * rootDiagUnit τ a =
        (rootDiagUnit τ a * y * (rootDiagUnit τ a)⁻¹) * rootDiagUnit τ a := by rw [h]
      _ = rootDiagUnit τ a * y := by group
  · intro h
    refine ⟨y.2, ?_⟩
    have h' := congrArg (fun x : adjointGroup τ K => (x : ModGL τ K)) h
    simp only [Subgroup.coe_mul, hzC] at h'
    calc rootDiagUnit τ a * y * (rootDiagUnit τ a)⁻¹ =
        (y : ModGL τ K) * rootDiagUnit τ a * (rootDiagUnit τ a)⁻¹ := by rw [h']
      _ = y := by group

variable [Finite K]

theorem eq_rankOneGroup_of_card_eq_three
    (hK3 : Nat.card K = 3) {i : Fin τ.rank}
    (hlong : ∀ j, τ.symmetrizer j j ≤ τ.symmetrizer i i) {wit : List ℕ}
    (hc : isolatedCheck τ i wit = true) {z : adjointGroup τ K}
    (hz : z ∈ rankOneGroup (adjDatum (rootOperatorFamily τ) K) (Pi.single i 1))
    (h2 : orderOf z = 2) {L : Subgroup (adjointGroup τ K)}
    (hLC : L ≤ Subgroup.centralizer ({z} : Set (adjointGroup τ K)))
    (hCL : Subgroup.centralizer ({z} : Set (adjointGroup τ K)) ≤
      Subgroup.normalizer (L : Set (adjointGroup τ K)))
    (eL : L ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    L = rankOneGroup (adjDatum (rootOperatorFamily τ) K) (Pi.single i 1) := by
  have hK := ringChar_ne_two_of_card_eq_three hK3
  have hγ : IsRoot τ (Pi.single i 1) := isRoot_single τ i
  rw [rankOneGroup_adjDatum _ hγ] at hz ⊢
  have hzC : (z : ModGL τ K) = rootDiagUnit τ (signTuple τ K i) := by
    rw [← torusElt_neg_one_eq]
    refine eq_torusElt_neg_one hK i (Subgroup.mem_subgroupOf.1 hz) ?_
    rwa [Subgroup.orderOf_coe]
  have hL'X : L.map (adjointGroup τ K).subtype ≤ toralCentralizer τ K (signTuple τ K i) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_toralCentralizer_iff_mem_centralizer hzC x).2 (hLC hx)
  have hL'N : rootSpan τ K (rootCharKernel (signTuple τ K i)) ≤
      Subgroup.normalizer ((L.map (adjointGroup τ K).subtype : Subgroup (ModGL τ K)) :
        Set (ModGL τ K)) := by
    intro y hy
    have hyH : y ∈ adjointGroup τ K := rootSpan_le_adjointGroup K _ hy
    have hyC : (⟨y, hyH⟩ : adjointGroup τ K) ∈
        Subgroup.centralizer ({z} : Set (adjointGroup τ K)) :=
      (mem_toralCentralizer_iff_mem_centralizer hzC ⟨y, hyH⟩).1
        (rootSpan_rootCharKernel_le_toralCentralizer _ hy)
    exact Subgroup.le_normalizer_map (adjointGroup τ K).subtype ⟨⟨y, hyH⟩, hCL hyC, rfl⟩
  have eL' : L.map (adjointGroup τ K).subtype ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (Subgroup.equivMapOfInjective L (adjointGroup τ K).subtype Subtype.val_injective).symm.trans
      eL
  have h := eq_sup_of_card_eq_three hK3 (iform_le_of_symmetrizer_le hlong) hc hL'X hL'N eL'
  rw [← h]
  exact (Subgroup.comap_map_eq_self_of_injective Subtype.val_injective L).symm

theorem centralizerCondition_rankOneGroup
    (hτ : NoG2 τ) (hK : ringChar K ≠ 2) {i : Fin τ.rank}
    (hlong : ∀ j, τ.symmetrizer j j ≤ τ.symmetrizer i i) {wit : List ℕ}
    (hc : isolatedCheck τ i wit = true) :
    CentralizerCondition K (rankOneGroup (adjDatum (rootOperatorFamily τ) K) (Pi.single i 1)) :=
  fun _ hz h2 => ⟨centralizer_le_normalizer_rankOneGroup hτ hK hlong hc hz h2,
    fun hK3 _ hLC hCL ⟨eL⟩ _ => eq_rankOneGroup_of_card_eq_three hK3 hlong hc hz h2 hLC hCL eL⟩

theorem highestRootCZ_adjDatum
    (hτ : NoG2 τ) (hK : ringChar K ≠ 2) {i : Fin τ.rank}
    (hlong : ∀ j, τ.symmetrizer j j ≤ τ.symmetrizer i i) {wit : List ℕ}
    (hc : isolatedCheck τ i wit = true)
    (hmax : ∀ δ ∈ (adjDatum (rootOperatorFamily τ) K).roots,
      rootForm (adjDatum (rootOperatorFamily τ) K) δ δ ≤
        rootForm (adjDatum (rootOperatorFamily τ) K) (Pi.single i 1) (Pi.single i 1)) :
    HighestRootCZ (adjDatum (rootOperatorFamily τ) K) K :=
  ⟨Pi.single i 1, mem_adjDatum_roots.2 (isRoot_single τ i), hmax,
    centralizerCondition_rankOneGroup hτ hK hlong hc⟩

end Datum

end CFSG.LieType.HighestRoot
