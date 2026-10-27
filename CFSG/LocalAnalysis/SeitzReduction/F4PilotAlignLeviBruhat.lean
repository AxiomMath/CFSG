module

public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_mono perfectCore_le_derivedSeriesOf)
open scoped commutatorElement Pointwise

variable {τ : Tag} {K : Type} [Field K]

@[expose] def toralSetKernel (𝒜 : Set (Fin τ.rank → Kˣ)) : Set (Fin τ.rank → ℤ) :=
  {α | IsRoot τ α ∧ ∀ a ∈ 𝒜, rootChar a α = 1}

@[expose] def signedSimpleRoots (J : Set (Fin τ.rank)) : Set (Fin τ.rank → ℤ) :=
  {α | ∃ j ∈ J, α = Pi.single j 1 ∨ α = -Pi.single j 1}

theorem isRoot_of_mem_signedSimpleRoots {J : Set (Fin τ.rank)} {α : Fin τ.rank → ℤ}
    (hα : α ∈ signedSimpleRoots J) : IsRoot τ α := by
  obtain ⟨j, -, rfl | rfl⟩ := hα
  exacts [isRoot_single τ j, IsRoot.neg (isRoot_single τ j)]

section Conj


theorem mem_rootSpan_inter_of_forall_conj_eq (𝒜 : Set (Fin τ.rank → Kˣ))
    {S : Set (Fin τ.rank → ℤ)} (hS : S.Finite) (hSroot : ∀ α ∈ S, IsRoot τ α)
    (hcoll : ∀ {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α → Set.range α = S →
      Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod)
        Set.univ (rootSpan τ K S))
    {u : ModGL τ K} (hu : u ∈ rootSpan τ K S)
    (hfix : ∀ a ∈ 𝒜, rootDiagUnit τ a * u * (rootDiagUnit τ a)⁻¹ = u) :
    u ∈ rootSpan τ K (toralSetKernel 𝒜 ∩ S) := by
  have : Finite S := hS.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  set α : Fin n → Fin τ.rank → ℤ := fun k => (e.symm k : Fin τ.rank → ℤ)
  have hα : Function.Injective α := fun k k' h => e.symm.injective (Subtype.ext h)
  have hrange : Set.range α = S := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (e.symm k).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [α]⟩
  have hαS : ∀ k, α k ∈ S := fun k => (e.symm k).2
  have hbij := hcoll α hα hrange
  obtain ⟨c, -, rfl⟩ := hbij.2.2 hu
  have hc : ∀ a ∈ 𝒜, (fun k => (rootChar a (α k) : K) * c k) = c := by
    intro a ha
    have hmap : rootDiagUnit τ a * (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod *
        (rootDiagUnit τ a)⁻¹ =
          (List.ofFn fun k => pinnedX τ K (α k) ((rootChar a (α k) : K) * c k)).prod := by
      have h := map_list_prod (MulAut.conj (rootDiagUnit τ a)).toMonoidHom
        (List.ofFn fun k => pinnedX τ K (α k) (c k))
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, List.map_ofFn] at h
      rw [h]
      refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
      exact rootDiagUnit_conj_pinnedX a (hSroot _ (hαS k)) (c k)
    have hfa := hfix a ha
    rw [hmap] at hfa
    exact hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) hfa
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  by_cases hk : ∀ a ∈ 𝒜, rootChar a (α k) = 1
  · exact le_iSup₂_of_le (f := fun β (_ : β ∈ toralSetKernel 𝒜 ∩ S) => rootSubgroup τ K β)
      (α k) ⟨⟨hSroot _ (hαS k), hk⟩, hαS k⟩ le_rfl (Subgroup.subset_closure ⟨c k, rfl⟩)
  · simp only [not_forall, exists_prop] at hk
    obtain ⟨a, ha, hne⟩ := hk
    have hck : c k = 0 := by
      have h1 : (rootChar a (α k) : K) * c k = c k := congrFun (hc a ha) k
      have h2 : ((rootChar a (α k) : K) - 1) * c k = 0 := by
        linear_combination h1
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact absurd (Units.ext (sub_eq_zero.1 h3)) hne
      · exact h3
    simp only [hck, pinnedX_zero]
    exact one_mem _

end Conj

section Full


theorem exists_bruhat_factors_of_forall_conj_eq (𝒜 : Set (Fin τ.rank → Kˣ)) {g : ModGL τ K}
    (hg : g ∈ adjointGroup τ K)
    (hfix : ∀ a ∈ 𝒜, rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ = g) :
    ∃ w : WeylGroup τ, (∀ a ∈ 𝒜, w ∈ rootCharStabilizer a) ∧ ∃ h ∈ torusGroup τ K,
      ∃ u ∈ rootSpan τ K (toralSetKernel 𝒜 ∩ {α | IsRoot τ α ∧ 0 < height α}),
      ∃ v ∈ rootSpan τ K (toralSetKernel 𝒜 ∩ inversionSet w),
        g = h * u * canonicalRep (coxeterSystem τ) K w * v := by
  have hg1 : g ∈ toralCentralizer τ K (1 : Fin τ.rank → Kˣ) :=
    mem_toralCentralizer.2 ⟨hg, by rw [rootDiagUnit_one, one_mul, inv_one, mul_one]⟩
  obtain ⟨w, -, h, hh, u, hu, v, hv, rfl⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors τ K 1).1 g hg1
  have huU : u ∈ posUnipotent τ K := rootSpan_mono Set.inter_subset_right hu
  have hvI : v ∈ rootSpan τ K (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  have hfac : ∀ a ∈ 𝒜, w ∈ rootCharStabilizer a ∧
      rootDiagUnit τ a * u * (rootDiagUnit τ a)⁻¹ = u ∧
      rootDiagUnit τ a * v * (rootDiagUnit τ a)⁻¹ = v := by
    intro a ha
    have hga : h * u * canonicalRep (coxeterSystem τ) K w * v ∈ toralCentralizer τ K a :=
      mem_toralCentralizer.2 ⟨hg, hfix a ha⟩
    obtain ⟨w', hw', h', hh', u', hu', v', hv', heq⟩ :=
      (Chevalley_toral_centralizer_Bruhat_factors τ K a).1 _ hga
    obtain ⟨hww, -, huu, hvv⟩ := (Chevalley_toral_centralizer_Bruhat_factors τ K a).2.1 w w' h h'
      u u' v v' hh hh' huU (rootSpan_mono Set.inter_subset_right hu') hvI
      (rootSpan_mono Set.inter_subset_right hv') heq
    refine ⟨hww ▸ hw', ?_, ?_⟩
    · rw [huu]
      exact conj_eq_iff_mem_centralizer.2 (rootSpan_le_centralizer a Set.inter_subset_left hu')
    · rw [hvv]
      exact conj_eq_iff_mem_centralizer.2 (rootSpan_le_centralizer a Set.inter_subset_left hv')
  refine ⟨w, fun a ha => (hfac a ha).1, h, hh, u, ?_, v, ?_, rfl⟩
  · exact mem_rootSpan_inter_of_forall_conj_eq 𝒜
      ((finite_setOf_isRoot τ).subset fun β hβ => hβ.1) (fun β hβ => hβ.1)
      (fun α hα hr => (positive_root_collection τ K).2 α hα hr) huU fun a ha => (hfac a ha).2.1
  · exact mem_rootSpan_inter_of_forall_conj_eq 𝒜 (inversionSet_finite w) (fun β hβ => hβ.1)
      (fun α hα hr => (bruhat_cell_factorization τ K).2.1 w α hα hr) hvI
      fun a ha => (hfac a ha).2.2

theorem mem_parabolicLevi_of_forall_conj_eq (𝒜 : Set (Fin τ.rank → Kˣ)) (J : Set (Fin τ.rank))
    (hker : ∀ α ∈ toralSetKernel 𝒜, 0 < height α → ∀ i ∉ J, α i = 0)
    (hW : ∀ w : WeylGroup τ, (∀ a ∈ 𝒜, w ∈ rootCharStabilizer a) →
      ∀ v : Fin τ.rank → ℤ, ∀ i ∉ J, (w • v) i = v i)
    {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (hfix : ∀ a ∈ 𝒜, rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ = g) :
    g ∈ parabolicLevi τ K J := by
  obtain ⟨w, hw, h, hh, u, hu, v, hv, rfl⟩ := exists_bruhat_factors_of_forall_conj_eq 𝒜 hg hfix
  have hsub : ∀ {S : Set (Fin τ.rank → ℤ)},
      S ⊆ toralSetKernel 𝒜 ∩ {α | IsRoot τ α ∧ 0 < height α} →
        rootSpan τ K S ≤ parabolicLevi τ K J := fun {S} hS =>
    (rootSpan_mono (show S ⊆ parabolicPosRoots τ J from fun α hα =>
      ⟨⟨(hS hα).1.1, hker α (hS hα).1 (hS hα).2.2⟩, (hS hα).2⟩)).trans
        (parabolicLeviUnipotent_le_parabolicLevi J)
  have hwJ : w ∈ parabolicWeylGroup τ J := by
    rw [← SetLike.mem_coe, (parabolic_Weyl_coordinate_stabilizer τ J).1]
    exact hW w hw
  refine mul_mem (mul_mem (mul_mem (torusGroup_le_parabolicLevi J hh) (hsub le_rfl hu))
    (canonicalRep_mem_parabolicLevi hwJ)) (hsub (fun α hα => ⟨hα.1, hα.2.1, hα.2.2.1⟩) hv)

end Full

theorem commutator_sup_le_of_comm_of_le_normalizer {G : Type*} [Group G] {H Q : Subgroup G}
    (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hN : H ≤ Subgroup.normalizer (Q : Set G)) :
    ⁅H ⊔ Q, H ⊔ Q⁆ ≤ Q := by
  have hset : ((H ⊔ Q : Subgroup G) : Set G) = (H : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN
  have hconj : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.1 (hN hh) q).1 hq
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [← SetLike.mem_coe, hset] at hx hy
  obtain ⟨h, hh, q, hq, rfl⟩ := hx
  obtain ⟨h', hh', q', hq', rfl⟩ := hy
  have e1 : ⁅h * q, h' * q'⁆ = (h * h') * (h'⁻¹ * q * h' * (q' * q⁻¹)) * (h' * h)⁻¹ *
      (h' * q'⁻¹ * h'⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e1, ← hH h hh h' hh']
  have hq1 : h'⁻¹ * q * h'⁻¹⁻¹ ∈ Q := hconj _ (inv_mem hh') q hq
  rw [inv_inv] at hq1
  exact mul_mem (hconj _ (mul_mem hh hh') _ (mul_mem hq1 (mul_mem hq' (inv_mem hq))))
    (hconj _ hh' _ (inv_mem hq'))

section Levi


theorem closure_xUnit_yUnit_eq_rootSpan (J : Set (Fin τ.rank)) :
    Subgroup.closure {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c} =
      rootSpan τ K (signedSimpleRoots J) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, c, rfl | rfl⟩
    · rw [← pinnedX_single]
      exact le_iSup₂_of_le (f := fun α (_ : α ∈ signedSimpleRoots J) => rootSubgroup τ K α)
        (Pi.single j 1) ⟨j, hj, Or.inl rfl⟩ le_rfl (Subgroup.subset_closure ⟨c, rfl⟩)
    · rw [← pinnedX_neg_single]
      exact le_iSup₂_of_le (f := fun α (_ : α ∈ signedSimpleRoots J) => rootSubgroup τ K α)
        (-Pi.single j 1) ⟨j, hj, Or.inr rfl⟩ le_rfl (Subgroup.subset_closure ⟨c, rfl⟩)
  · refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    obtain ⟨j, hj, rfl | rfl⟩ := hα
    · rw [pinnedX_single]
      exact Subgroup.subset_closure ⟨j, hj, c, Or.inl rfl⟩
    · rw [pinnedX_neg_single]
      exact Subgroup.subset_closure ⟨j, hj, c, Or.inr rfl⟩

theorem parabolicLevi_eq_sup_rootSpan (J : Set (Fin τ.rank)) :
    parabolicLevi τ K J = torusGroup τ K ⊔ rootSpan τ K (signedSimpleRoots J) := by
  rw [parabolicLevi, closure_xUnit_yUnit_eq_rootSpan]

theorem commutator_parabolicLevi_le_rootSpan (J : Set (Fin τ.rank)) :
    ⁅parabolicLevi τ K J, parabolicLevi τ K J⁆ ≤ rootSpan τ K (signedSimpleRoots J) := by
  rw [parabolicLevi_eq_sup_rootSpan]
  exact commutator_sup_le_of_comm_of_le_normalizer
    (fun x hx y hy => (triangular_borel_structure.{0, 0} τ K).1 x hx y hy)
    (torusGroup_le_normalizer_rootSpan fun α hα => isRoot_of_mem_signedSimpleRoots hα)

theorem perfectCore_le_rootSpan_of_le_parabolicLevi {J : Set (Fin τ.rank)}
    {H : Subgroup (ModGL τ K)} (hH : H ≤ parabolicLevi τ K J) :
    perfectCore H ≤ rootSpan τ K (signedSimpleRoots J) :=
  (perfectCore_mono hH).trans
    ((perfectCore_le_derivedSeriesOf _ 1).trans (commutator_parabolicLevi_le_rootSpan J))

end Levi

section Core


theorem perfectCore_le_rootSpan_of_forall_conj_eq (𝒜 : Set (Fin τ.rank → Kˣ))
    (J : Set (Fin τ.rank))
    (hker : ∀ α ∈ toralSetKernel 𝒜, 0 < height α → ∀ i ∉ J, α i = 0)
    (hW : ∀ w : WeylGroup τ, (∀ a ∈ 𝒜, w ∈ rootCharStabilizer a) →
      ∀ v : Fin τ.rank → ℤ, ∀ i ∉ J, (w • v) i = v i)
    {H : Subgroup (ModGL τ K)}
    (hH : ∀ g ∈ H, g ∈ adjointGroup τ K ∧
      ∀ a ∈ 𝒜, rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ = g) :
    perfectCore H ≤ rootSpan τ K (signedSimpleRoots J) :=
  perfectCore_le_rootSpan_of_le_parabolicLevi fun g hg =>
    mem_parabolicLevi_of_forall_conj_eq 𝒜 J hker hW (hH g hg).1 (hH g hg).2

end Core

end CFSG.SeitzReduction.F4Pilot
