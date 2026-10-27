module

public import CFSG.LieType.Chevalley.OddToralInvolutionFixedComponents

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint (iform iform_comm iform_add_left iform_smul_left
  iform_smul_right iform_self_pos)
open CFSG.ComponentClassification.CatalogueBGeneralLinear (no_pComponent_of_solvable)
open Matrix

section Pair

variable {τ : Tag} {K : Type} [Field K]

theorem not_isRoot_nsmul_add_of_iform
    {a : Fin τ.rank → Kˣ} {γ δ : Fin τ.rank → ℤ}
    (hγ : γ ∈ rootCharKernel a) (hδ : δ ∈ rootCharKernel a) (hγδ : iform γ δ = 0)
    (hker : ∀ ε ∈ rootCharKernel a, iform ε γ = 0 ∨ iform ε δ = 0) {a' b' : ℕ} (ha' : 0 < a')
    (hb' : 0 < b') : ¬IsRoot τ (a' • γ + b' • δ) := by
  intro hε
  have hεK : a' • γ + b' • δ ∈ rootCharKernel a := by
    refine ⟨hε, ?_⟩
    rw [rootChar_add, rootChar_nsmul, rootChar_nsmul, hγ.2, hδ.2, one_pow, one_pow, mul_one]
  have hδγ : iform δ γ = 0 := by rw [iform_comm]; exact hγδ
  have hγγ := iform_self_pos hγ.1.ne_zero
  have hδδ := iform_self_pos hδ.1.ne_zero
  have ha'' : (0 : ℤ) < a' := by exact_mod_cast ha'
  have hb'' : (0 : ℤ) < b' := by exact_mod_cast hb'
  rcases hker _ hεK with h | h
  · rw [← Nat.cast_smul_eq_nsmul ℤ a', ← Nat.cast_smul_eq_nsmul ℤ b', iform_add_left,
      iform_smul_left, iform_smul_left, hδγ, mul_zero, add_zero] at h
    have := mul_pos ha'' hγγ
    omega
  · rw [← Nat.cast_smul_eq_nsmul ℤ a', ← Nat.cast_smul_eq_nsmul ℤ b', iform_add_left,
      iform_smul_left, iform_smul_left, hγδ, mul_zero, zero_add] at h
    have := mul_pos hb'' hδδ
    omega

theorem iform_neg_left'
    (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  rw [← neg_one_smul ℤ x, iform_smul_left, neg_one_mul]

theorem iform_neg_right'
    (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [← neg_one_smul ℤ y, iform_smul_right, neg_one_mul]

theorem rootSpan_two_pairs
    (α β : Fin τ.rank → ℤ) :
    rootSpan τ K {α, -α, β, -β} =
      (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α)) ⊔ (rootSubgroup τ K β ⊔ rootSubgroup τ K (-β)) :=
  by rw [rootSpan, iSup_insert, iSup_insert, iSup_insert, iSup_singleton, sup_assoc]

theorem toral_two_pair_central_product
    {a : Fin τ.rank → Kˣ} {α β : Fin τ.rank → ℤ}
    (hker : rootCharKernel a = {α, -α, β, -β}) (hαβ : iform α β = 0) :
    rootSpan τ K (rootCharKernel a) =
      (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α)) ⊔ (rootSubgroup τ K β ⊔ rootSubgroup τ K (-β)) ∧
    ⁅rootSubgroup τ K α ⊔ rootSubgroup τ K (-α), rootSubgroup τ K β ⊔ rootSubgroup τ K (-β)⁆ = ⊥ ∧
    ∃ μ : ↥(rootSubgroup τ K α ⊔ rootSubgroup τ K (-α)) ×
        ↥(rootSubgroup τ K β ⊔ rootSubgroup τ K (-β)) →* ↥(rootSpan τ K (rootCharKernel a)),
      (∀ x, (μ (x, 1) : ModGL τ K) = x) ∧ (∀ y, (μ (1, y) : ModGL τ K) = y) ∧
      Function.Surjective μ ∧
      ∀ s ∈ μ.ker, s.1 ∈ Subgroup.center ↥(rootSubgroup τ K α ⊔ rootSubgroup τ K (-α)) ∧
        s.2 ∈ Subgroup.center ↥(rootSubgroup τ K β ⊔ rootSubgroup τ K (-β)) := by
  have hmem : ∀ ε, ε ∈ rootCharKernel a ↔ ε = α ∨ ε = -α ∨ ε = β ∨ ε = -β := fun ε => by
    rw [hker]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hαK : α ∈ rootCharKernel a := (hmem α).2 (Or.inl rfl)
  have hβK : β ∈ rootCharKernel a := (hmem β).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hβα : iform β α = 0 := by rw [iform_comm]; exact hαβ
  have hcommUU : ∀ γ ∈ ({α, -α} : Set (Fin τ.rank → ℤ)), ∀ δ ∈ ({β, -β} : Set (Fin τ.rank → ℤ)),
      ∀ x ∈ rootSubgroup τ K γ, ∀ y ∈ rootSubgroup τ K δ, Commute x y := by
    intro γ hγ δ hδ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ hδ
    have hγK : γ ∈ rootCharKernel a := by
      rcases hγ with rfl | rfl
      · exact hαK
      · exact (hmem _).2 (Or.inr (Or.inl rfl))
    have hδK : δ ∈ rootCharKernel a := by
      rcases hδ with rfl | rfl
      · exact hβK
      · exact (hmem _).2 (Or.inr (Or.inr (Or.inr rfl)))
    have hγδ : iform γ δ = 0 := by
      rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl <;>
        simp [iform_neg_left', iform_neg_right', hαβ]
    have hγγ := iform_self_pos hγK.1.ne_zero
    have hne : γ ≠ δ := by
      rintro rfl
      omega
    have hne' : γ ≠ -δ := by
      rintro rfl
      rw [iform_neg_left'] at hγδ
      have := iform_self_pos hδK.1.ne_zero
      omega
    refine commute_of_forall_not_isRoot hγK.1 hδK.1 hne hne' (fun a' b' ha' hb' => ?_) K
    refine not_isRoot_nsmul_add_of_iform hγK hδK hγδ (fun ε hε => ?_) ha' hb'
    rcases (hmem ε).1 hε with rfl | rfl | rfl | rfl
    · right
      rcases hδ with rfl | rfl <;> simp [iform_neg_right', hαβ]
    · right
      rcases hδ with rfl | rfl <;> simp [iform_neg_left', iform_neg_right', hαβ]
    · left
      rcases hγ with rfl | rfl <;> simp [iform_neg_right', hβα]
    · left
      rcases hγ with rfl | rfl <;> simp [iform_neg_left', iform_neg_right', hβα]
  have hUQ : ∀ γ ∈ ({α, -α} : Set (Fin τ.rank → ℤ)), rootSubgroup τ K γ ≤
      Subgroup.centralizer ((rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) : Subgroup (ModGL τ K)) :
        Set (ModGL τ K)) := by
    intro γ hγ
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_ <;> intro y hy <;> rw [Subgroup.mem_centralizer_iff] <;> intro x hx
    · exact (hcommUU γ hγ β (Or.inl rfl) x hx y hy).eq
    · exact (hcommUU γ hγ (-β) (Or.inr rfl) x hx y hy).eq
  have hQQ : rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) ≤
      Subgroup.centralizer ((rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) : Subgroup (ModGL τ K)) :
        Set (ModGL τ K)) :=
    sup_le (hUQ α (Or.inl rfl)) (hUQ (-α) (Or.inr rfl))
  have hcomm : ∀ x ∈ rootSubgroup τ K α ⊔ rootSubgroup τ K (-α),
      ∀ y ∈ rootSubgroup τ K β ⊔ rootSubgroup τ K (-β), Commute x y := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (hQQ hx) y hy).symm
  have hS : rootSpan τ K (rootCharKernel a) =
      (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α)) ⊔
        (rootSubgroup τ K β ⊔ rootSubgroup τ K (-β)) := by
    rw [hker, rootSpan_two_pairs]
  let ν : ↥(rootSubgroup τ K α ⊔ rootSubgroup τ K (-α)) ×
      ↥(rootSubgroup τ K β ⊔ rootSubgroup τ K (-β)) →* ModGL τ K :=
    MonoidHom.noncommCoprod (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α)).subtype
      (rootSubgroup τ K β ⊔ rootSubgroup τ K (-β)).subtype (fun x y => hcomm x x.2 y y.2)
  have hν : ∀ s, ν s = (s.1 : ModGL τ K) * s.2 := fun s => rfl
  have hrange : ν.range = rootSpan τ K (rootCharKernel a) :=
    (MonoidHom.noncommCoprod_range _ _ _).trans (by
      rw [Subgroup.range_subtype, Subgroup.range_subtype, hS])
  have hmemν : ∀ s, ν s ∈ rootSpan τ K (rootCharKernel a) := fun s => hrange ▸ ⟨s, rfl⟩
  have hker1 : ∀ s ∈ (ν.codRestrict _ hmemν).ker, (s.1 : ModGL τ K) * s.2 = 1 := fun s hs => by
    rw [← hν]
    exact congrArg Subtype.val ((MonoidHom.mem_ker).1 hs)
  refine ⟨hS, (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hQQ,
    ν.codRestrict _ hmemν, fun x => ?_, fun y => ?_, fun g => ?_, fun s hs => ⟨?_, ?_⟩⟩
  · change ν (x, 1) = x
    rw [hν]
    simp
  · change ν (1, y) = y
    rw [hν]
    simp
  · obtain ⟨s, hs⟩ : (g : ModGL τ K) ∈ ν.range := by
      rw [hrange]
      exact g.2
    exact ⟨s, Subtype.ext hs⟩
  · have hs1 : (s.1 : ModGL τ K) ∈ rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) := by
      rw [eq_inv_of_mul_eq_one_left (hker1 s hs)]
      exact inv_mem s.2.2
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2 _ hs1).eq
  · have hs2 : (s.2 : ModGL τ K) ∈ rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) := by
      rw [eq_inv_of_mul_eq_one_right (hker1 s hs)]
      exact inv_mem s.1.2
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm _ hs2 g g.2).eq.symm

end Pair

section Roots

theorem isRoot_G2_iff {v : Fin Tag.G2.rank → ℤ} :
    IsRoot .G2 v ↔ ∃ k : Fin 12, Tag.G2.rootCertificate.root k = v := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .G2),
    show Tag.G2.rootCertificate.roots.length = 12 by decide]
  exact ⟨fun ⟨k, hk, h⟩ => ⟨⟨k, hk⟩, h⟩, fun ⟨k, h⟩ => ⟨k, k.2, h⟩⟩

theorem kernelRoots_maskChar_G2_eq
    {b : Fin Tag.G2.rank → Bool} {α β : Fin Tag.G2.rank → ℤ}
    (h1 : ∀ k : Fin 12, maskPairing b (Tag.G2.rootCertificate.root k) % 2 = 0 →
      List.ofFn (Tag.G2.rootCertificate.root k) = List.ofFn α ∨
        List.ofFn (Tag.G2.rootCertificate.root k) = List.ofFn (-α) ∨
        List.ofFn (Tag.G2.rootCertificate.root k) = List.ofFn β ∨
        List.ofFn (Tag.G2.rootCertificate.root k) = List.ofFn (-β))
    (h2 : ∀ v ∈ [α, -α, β, -β], (∃ k : Fin 12,
      List.ofFn (Tag.G2.rootCertificate.root k) = List.ofFn v) ∧ maskPairing b v % 2 = 0) :
    kernelRoots (maskChar b) = {α, -α, β, -β} := by
  ext v
  rw [mem_kernelRoots_maskChar, isRoot_G2_iff, Int.even_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨k, rfl⟩, hk⟩
    rcases h1 k hk with h | h | h | h
    · exact Or.inl (List.ofFn_injective h)
    · exact Or.inr (Or.inl (List.ofFn_injective h))
    · exact Or.inr (Or.inr (Or.inl (List.ofFn_injective h)))
    · exact Or.inr (Or.inr (Or.inr (List.ofFn_injective h)))
  · intro hv
    have hv' : v ∈ [α, -α, β, -β] := by
      rcases hv with rfl | rfl | rfl | rfl <;> simp
    obtain ⟨⟨k, hk⟩, hev⟩ := h2 v hv'
    exact ⟨⟨k, List.ofFn_injective hk⟩, hev⟩

theorem kernelRoots_maskChar_G2_tf :
    kernelRoots (maskChar (τ := .G2) ![true, false]) = {![0, 1], -![0, 1], ![2, 3], -![2, 3]} :=
  kernelRoots_maskChar_G2_eq (by decide +kernel) (by decide +kernel)

theorem kernelRoots_maskChar_G2_ft :
    kernelRoots (maskChar (τ := .G2) ![false, true]) = {![1, 0], -![1, 0], ![1, 2], -![1, 2]} :=
  kernelRoots_maskChar_G2_eq (by decide +kernel) (by decide +kernel)

theorem kernelRoots_maskChar_G2_tt :
    kernelRoots (maskChar (τ := .G2) ![true, true]) = {![1, 1], -![1, 1], ![1, 3], -![1, 3]} :=
  kernelRoots_maskChar_G2_eq (by decide +kernel) (by decide +kernel)

end Roots

section Main

variable {K : Type} [Field K]

theorem odd_G2_toral_two_pair
    [Finite K] (hK : ringChar K ≠ 2) (a : Fin Tag.G2.rank → Kˣ)
    (ha : ∀ i, a i = 1 ∨ a i = -1) {α β : Fin Tag.G2.rank → ℤ}
    (hker : rootCharKernel a = {α, -α, β, -β}) (hαβ : α ⬝ᵥ (Tag.G2.symmetrizedCartan *ᵥ β) = 0) :
    rootSpan .G2 K (rootCharKernel a) =
      (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)) ⊔
        (rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β)) ∧
    ⁅rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α),
      rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β)⁆ = ⊥ ∧
    (∃ μ : ↥(rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)) ×
        ↥(rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β)) →* ↥(rootSpan .G2 K (rootCharKernel a)),
      (∀ x, (μ (x, 1) : ModGL .G2 K) = x) ∧ (∀ y, (μ (1, y) : ModGL .G2 K) = y) ∧
      Function.Surjective μ ∧
      ∀ s ∈ μ.ker, s.1 ∈ Subgroup.center ↥(rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)) ∧
        s.2 ∈ Subgroup.center ↥(rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β))) ∧
    Nonempty (SL2 K ≃* ↥(rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α))) ∧
    Nonempty (SL2 K ≃* ↥(rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β))) ∧
    rootSpan .G2 K (rootCharKernel a) ≤ toralCentralizer .G2 K a ∧
    ((rootSpan .G2 K (rootCharKernel a)).subgroupOf (toralCentralizer .G2 K a)).Normal ∧
    Group.IsSolvable (toralCentralizer .G2 K a ⧸
      (rootSpan .G2 K (rootCharKernel a)).subgroupOf (toralCentralizer .G2 K a)) ∧
    derivedSeries (toralCentralizer .G2 K a ⧸
      (rootSpan .G2 K (rootCharKernel a)).subgroupOf (toralCentralizer .G2 K a)) 2 = ⊥ ∧
    (Nat.card K = 3 → Group.IsSolvable (toralCentralizer .G2 K a) ∧
      ∀ (p : ℕ) (L : Subgroup (toralCentralizer .G2 K a)), ¬ CFSG.IsPComponent p L) := by
  have hαβ' : iform α β = 0 := by rwa [← dotProduct_mulVec_eq_iform]
  have hαK : α ∈ rootCharKernel a := by rw [hker]; exact Or.inl rfl
  have hβK : β ∈ rootCharKernel a := by rw [hker]; exact Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨hS, hcomm, ⟨μ, hμ1, hμ2, hμs, hμk⟩⟩ := toral_two_pair_central_product (K := K) hker hαβ'
  obtain ⟨-, ⟨eα⟩, -, h3α⟩ := odd_arbitrary_root_pair_SL2_p_components .G2 K hK hαK.1
  obtain ⟨-, ⟨eβ⟩, -, h3β⟩ := odd_arbitrary_root_pair_SL2_p_components .G2 K hK hβK.1
  obtain ⟨hSX, hnorm, hsolv, hD, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .G2 K hK a ha
  refine ⟨hS, hcomm, ⟨μ, hμ1, hμ2, hμs, hμk⟩, ⟨eα⟩, ⟨eβ⟩, hSX, hnorm, hsolv, hD, fun hq => ?_⟩
  have := (h3α.1 hq).1
  have := (h3β.1 hq).1
  have : Group.IsSolvable ↥(rootSpan .G2 K (rootCharKernel a)) :=
    Group.isSolvable_of_surjective hμs
  have : Group.IsSolvable ↥((rootSpan .G2 K (rootCharKernel a)).subgroupOf
      (toralCentralizer .G2 K a)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hSX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hSX).injective
  have hX : Group.IsSolvable (toralCentralizer .G2 K a) :=
    Group.isSolvable_of_ker_le_range
      ((rootSpan .G2 K (rootCharKernel a)).subgroupOf (toralCentralizer .G2 K a)).subtype
      (QuotientGroup.mk'
        ((rootSpan .G2 K (rootCharKernel a)).subgroupOf (toralCentralizer .G2 K a)))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  exact ⟨hX, fun p L => no_pComponent_of_solvable p L⟩

theorem odd_G2_toral_involution_fixed_p_components
    (K : Type) [Field K] [Finite K]
    (hK : Odd (Nat.card K)) (a : Fin Tag.G2.rank → Kˣ) (ha : ∀ i, a i = 1 ∨ a i = -1) :
    (∀ p : ℕ, p.Prime → ∀ L : Subgroup (toralCentralizer .G2 K a),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
    (a = 1 → toralCentralizer .G2 K a = adjointGroup .G2 K) ∧
    (a = 1 ∨ a = ![-1, 1] ∨ a = ![1, -1] ∨ a = ![-1, -1]) ∧
    (∀ α β : Fin Tag.G2.rank → ℤ,
      ((a = ![-1, 1] ∧ α = ![0, 1] ∧ β = ![2, 3]) ∨ (a = ![1, -1] ∧ α = ![1, 0] ∧ β = ![1, 2]) ∨
        (a = ![-1, -1] ∧ α = ![1, 1] ∧ β = ![1, 3])) →
      rootCharKernel a = {α, -α, β, -β} ∧ α ⬝ᵥ (Tag.G2.symmetrizedCartan *ᵥ β) = 0 ∧
      rootSpan .G2 K (rootCharKernel a) =
        (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)) ⊔
          (rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β)) ∧
      ⁅rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α),
        rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β)⁆ = ⊥ ∧
      (∃ μ : ↥(rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)) ×
          ↥(rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β)) →*
            ↥(rootSpan .G2 K (rootCharKernel a)),
        (∀ x, (μ (x, 1) : ModGL .G2 K) = x) ∧ (∀ y, (μ (1, y) : ModGL .G2 K) = y) ∧
        Function.Surjective μ ∧
        ∀ s ∈ μ.ker, s.1 ∈ Subgroup.center ↥(rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)) ∧
          s.2 ∈ Subgroup.center ↥(rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β))) ∧
      Nonempty (SL2 K ≃* ↥(rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α))) ∧
      Nonempty (SL2 K ≃* ↥(rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β))) ∧
      rootSpan .G2 K (rootCharKernel a) ≤ toralCentralizer .G2 K a ∧
      ((rootSpan .G2 K (rootCharKernel a)).subgroupOf (toralCentralizer .G2 K a)).Normal ∧
      Group.IsSolvable (toralCentralizer .G2 K a ⧸
        (rootSpan .G2 K (rootCharKernel a)).subgroupOf (toralCentralizer .G2 K a)) ∧
      derivedSeries (toralCentralizer .G2 K a ⧸
        (rootSpan .G2 K (rootCharKernel a)).subgroupOf (toralCentralizer .G2 K a)) 2 = ⊥) ∧
    (Nat.card K = 3 → a ≠ 1 → Group.IsSolvable (toralCentralizer .G2 K a) ∧
      ∀ (p : ℕ) (L : Subgroup (toralCentralizer .G2 K a)), ¬ CFSG.IsPComponent p L) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hK2 : ringChar K ≠ 2 := fun h => by
    have := FiniteField.even_card_iff_char_two.1 h
    rw [← Nat.card_eq_fintype_card] at this
    exact (Nat.not_even_iff_odd.2 hK) (Nat.even_iff.2 this)
  have h1 : (1 : Kˣ) ≠ -1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hK2 (congrArg Units.val h).symm
  have hcases : a = 1 ∨ a = ![-1, 1] ∨ a = ![1, -1] ∨ a = ![-1, -1] := by
    have e : a = ![a ⟨0, by decide⟩, a ⟨1, by decide⟩] := funext fun i => by fin_cases i <;> rfl
    rcases ha ⟨0, by decide⟩ with h0 | h0 <;> rcases ha ⟨1, by decide⟩ with h1' | h1' <;>
      rw [e, h0, h1']
    · left
      funext i
      fin_cases i <;> rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hbits : ∀ b : Fin Tag.G2.rank → Bool, signTupleBits a = b →
      rootCharKernel a = kernelRoots (maskChar b) := fun b hb => by
    rw [rootCharKernel_eq_kernelRoots hK2 ha, hb]
  have hpair : ∀ α β : Fin Tag.G2.rank → ℤ,
      ((a = ![-1, 1] ∧ α = ![0, 1] ∧ β = ![2, 3]) ∨ (a = ![1, -1] ∧ α = ![1, 0] ∧ β = ![1, 2]) ∨
        (a = ![-1, -1] ∧ α = ![1, 1] ∧ β = ![1, 3])) →
      rootCharKernel a = {α, -α, β, -β} ∧ α ⬝ᵥ (Tag.G2.symmetrizedCartan *ᵥ β) = 0 := by
    rintro α β (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · refine ⟨(hbits ![true, false] (funext fun i => ?_)).trans kernelRoots_maskChar_G2_tf,
        by decide +kernel⟩
      fin_cases i
      exacts [decide_eq_true rfl, decide_eq_false h1]
    · refine ⟨(hbits ![false, true] (funext fun i => ?_)).trans kernelRoots_maskChar_G2_ft,
        by decide +kernel⟩
      fin_cases i
      exacts [decide_eq_false h1, decide_eq_true rfl]
    · refine ⟨(hbits ![true, true] (funext fun i => ?_)).trans kernelRoots_maskChar_G2_tt,
        by decide +kernel⟩
      fin_cases i
      exacts [decide_eq_true rfl, decide_eq_true rfl]
  refine ⟨odd_toral_involution_fixed_p_components .G2 K hK a ha, fun h => ?_, hcases,
    fun α β hαβ => ?_, fun hq hne => ?_⟩
  · subst h
    rw [toralCentralizer, rootDiagUnit_one]
    exact inf_eq_left.2 fun g _ => Subgroup.mem_centralizer_iff.2 fun x hx => by
      rw [Set.mem_singleton_iff.1 hx, one_mul, mul_one]
  · obtain ⟨hker, hform⟩ := hpair α β hαβ
    obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8', h9', -⟩ :=
      odd_G2_toral_two_pair hK2 a ha hker hform
    exact ⟨hker, hform, h1', h2', h3', h4', h5', h6', h7', h8', h9'⟩
  · rcases hcases with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · obtain ⟨hker, hform⟩ := hpair ![0, 1] ![2, 3] (Or.inl ⟨rfl, rfl, rfl⟩)
      exact (odd_G2_toral_two_pair hK2 _ ha hker hform).2.2.2.2.2.2.2.2.2 hq
    · obtain ⟨hker, hform⟩ := hpair ![1, 0] ![1, 2] (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
      exact (odd_G2_toral_two_pair hK2 _ ha hker hform).2.2.2.2.2.2.2.2.2 hq
    · obtain ⟨hker, hform⟩ := hpair ![1, 1] ![1, 3] (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
      exact (odd_G2_toral_two_pair hK2 _ ha hker hform).2.2.2.2.2.2.2.2.2 hq

end Main

end CFSG.LieType.Chevalley
