module

public import CFSG.LieType.Chevalley.PinnedBridge
public import CFSG.LieType.Chevalley.Canonical
public import CFSG.LieType.Chevalley.BorelStructure
public import CFSG.LieType.Chevalley.RootOps.All

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

theorem weylElt_mul_pinnedX_mul_inv
    (R : Type) [CommRing R] (i : Fin τ.rank)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ ε : R, ε * ε = 1 ∧ ∀ c : R,
      weylElt τ R i 1 * pinnedX τ R α c * (weylElt τ R i 1)⁻¹ =
        pinnedX τ R (reflect τ i α) (ε * c) := by
  set F := rootOperatorFamily τ
  have hα' : IsRoot τ (reflect τ i α) := IsRoot.reflect i hα
  set s := (F.pinnedFamilySign α : R) with hs
  set s' := (F.pinnedFamilySign (reflect τ i α) : R) with hs'
  set σ := (F.sign i ⟨α, hα⟩ : R) with hσ
  have h1 : s * s = 1 := F.pinnedFamilySign_mul_self R α
  have h2 : s' * s' = 1 := F.pinnedFamilySign_mul_self R (reflect τ i α)
  have h3 : σ * σ = 1 := F.sign_cast_mul_self (R := R) i ⟨α, hα⟩
  refine ⟨s' * σ * s, by linear_combination (σ * σ * s * s) * h2 + (s * s) * h3 + h1, fun c => ?_⟩
  have hsm : simple τ i • (⟨α, hα⟩ : Root τ) = ⟨reflect τ i α, hα'⟩ :=
    Subtype.ext (simple_smul i α)
  rw [F.pinnedX_eq_eltUnit R hα, F.weylElt_mul_eltUnit_mul_inv, F.pinnedX_eq_eltUnit R hα', hsm]
  congr 1
  linear_combination (-(σ * s * c)) * h2

theorem map_conj_weylElt_rootSubgroup
    (R : Type) [CommRing R] (i : Fin τ.rank)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (rootSubgroup τ R α).map (MulAut.conj (weylElt τ R i 1)).toMonoidHom =
      rootSubgroup τ R (reflect τ i α) := by
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv R i hα
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    refine ⟨pinnedX τ R α (ε * c), Subgroup.subset_closure ⟨_, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h, ← mul_assoc, hε, one_mul]

theorem map_conj_mul {G : Type*} [Group G] (a b : G) (K : Subgroup G) :
    K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_prod_weylElt_rootSubgroup
    (R : Type) [CommRing R] (ω : List (Fin τ.rank))
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (rootSubgroup τ R α).map (MulAut.conj (ω.map fun i => weylElt τ R i 1).prod).toMonoidHom =
      rootSubgroup τ R ((coxeterSystem τ).wordProd ω • α) := by
  induction ω with
  | nil =>
    ext g
    simp
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, map_conj_mul, ih,
      map_conj_weylElt_rootSubgroup R i (IsRoot.smul hα _), (coxeterSystem τ).wordProd_cons,
      mul_smul, simple_smul]

theorem canonical_weyl_root_transport
    (τ : Tag) (R : Type) [CommRing R] :
    (∀ (w : WeylGroup τ) (S : Set (Fin τ.rank → ℤ)), (∀ α ∈ S, IsRoot τ α) →
      (rootSpan τ R S).map (MulAut.conj (canonicalRep (coxeterSystem τ) R w)).toMonoidHom =
        rootSpan τ R ((fun α => w • α) '' S)) ∧
    (∀ (w : WeylGroup τ) (α : Fin τ.rank → ℤ), IsRoot τ α →
      (rootSubgroup τ R α).map (MulAut.conj (canonicalRep (coxeterSystem τ) R w)).toMonoidHom =
        rootSubgroup τ R (w • α)) ∧
    ∀ w : WeylGroup τ, canonicalRep (coxeterSystem τ) R w ∈
      Subgroup.normalizer (torusGroup τ R : Set (Module.End R (RootModule τ R))ˣ) := by
  have hroot : ∀ (w : WeylGroup τ) (α : Fin τ.rank → ℤ), IsRoot τ α →
      (rootSubgroup τ R α).map (MulAut.conj (canonicalRep (coxeterSystem τ) R w)).toMonoidHom =
        rootSubgroup τ R (w • α) := fun w α hα => by
    obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
    rw [canonicalRep_wordProd hω]
    exact map_conj_prod_weylElt_rootSubgroup R ω hα
  refine ⟨fun w S hS => ?_, hroot, fun w => ?_⟩
  · simp only [rootSpan, Subgroup.map_iSup, iSup_image]
    exact iSup_congr fun α => iSup_congr fun hα => hroot w α (hS α hα)
  · refine (Subgroup.closure_le _).2 ?_ (canonicalRep_mem_closure (coxeterSystem τ) R w)
    rintro _ ⟨i, rfl⟩
    exact weylElt_mem_normalizer_torus τ R i 1

end CFSG.LieType.Chevalley
