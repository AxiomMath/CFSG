module

public import CFSG.LieType.Chevalley.LangAdjointDiagonalLift
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

theorem rootChar_smul_eq_rootChar_of_forall_isRoot
    {a b : Fin τ.rank → Kˣ} {w : WeylGroup τ}
    (h : ∀ α, IsRoot τ α → rootChar a (w • α) = rootChar b α) (v : Fin τ.rank → ℤ) :
    rootChar a (w • v) = rootChar b v := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : w • v = ∑ i, v i • (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    conv_lhs => rw [hv]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm w (v i) _
  rw [hw, rootChar_sum]
  conv_rhs => rw [hv, rootChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rootChar_zsmul, rootChar_zsmul, h _ (.basis i)]

theorem rootDiag_canonicalRep_hVec
    (a : Fin τ.rank → Kˣ) (w : WeylGroup τ) (j : Fin τ.rank) :
    rootDiag a ((canonicalRep (coxeterSystem τ) K w : Module.End K (RootModule τ K))
      (hVec τ K j)) =
      (canonicalRep (coxeterSystem τ) K w : Module.End K (RootModule τ K)) (hVec τ K j) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω, ← RootWalk.hVecSum_single, RootWalk.prod_weylElt_hVecSum]
  simp only [RootWalk.hVecSum, map_sum, map_smul, rootDiag_hVec]

theorem rootDiagUnit_canonicalRep_rootVec
    (a : Fin τ.rank → Kˣ) (w : WeylGroup τ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {c : Kˣ}
    (hc : (canonicalRep (coxeterSystem τ) K w : Module.End K (RootModule τ K)) (rootVec τ K α) =
      (c : K) • rootVec τ K (w • α)) :
    ((rootDiagUnit τ a : ModGL τ K) : Module.End K (RootModule τ K))
        ((canonicalRep (coxeterSystem τ) K w : Module.End K (RootModule τ K)) (rootVec τ K α)) =
      ((c : K) * (rootChar a (w • α) : K)) • rootVec τ K (w • α) := by
  rw [hc, map_smul, show ((rootDiagUnit τ a : ModGL τ K) : Module.End K (RootModule τ K)) =
    rootDiag a from rfl, rootDiag_rootVec a (IsRoot.smul hα w), smul_smul]

theorem canonicalRep_rootDiagUnit_rootVec
    (b : Fin τ.rank → Kˣ) (w : WeylGroup τ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {c : Kˣ}
    (hc : (canonicalRep (coxeterSystem τ) K w : Module.End K (RootModule τ K)) (rootVec τ K α) =
      (c : K) • rootVec τ K (w • α)) :
    (canonicalRep (coxeterSystem τ) K w : Module.End K (RootModule τ K))
        (((rootDiagUnit τ b : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K α)) =
      ((rootChar b α : K) * (c : K)) • rootVec τ K (w • α) := by
  rw [show ((rootDiagUnit τ b : ModGL τ K) : Module.End K (RootModule τ K)) = rootDiag b from rfl,
    rootDiag_rootVec b hα, map_smul, hc, smul_smul]

theorem rootDiagUnit_eq_conj_canonicalRep_iff
    (a b : Fin τ.rank → Kˣ) (w : WeylGroup τ) :
    rootDiagUnit τ a = canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ b *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ ↔
      ∀ v : Fin τ.rank → ℤ, rootChar a (w • v) = rootChar b v := by
  have hmaps := mapsRootLines_canonicalRep (R := K) w
  rw [eq_mul_inv_iff_mul_eq]
  constructor
  · intro h
    refine rootChar_smul_eq_rootChar_of_forall_isRoot fun α hα => ?_
    obtain ⟨c, hc⟩ := hmaps α hα
    have h1 := congrArg (fun f : ModGL τ K => (f : Module.End K (RootModule τ K))
      (rootVec τ K α)) h
    simp only [Units.val_mul, Module.End.mul_apply] at h1
    rw [rootDiagUnit_canonicalRep_rootVec a w hα hc,
      canonicalRep_rootDiagUnit_rootVec b w hα hc] at h1
    have h2 := eq_of_smul_rootVec_eq_smul (IsRoot.smul hα w) h1
    rw [mul_comm] at h2
    exact Units.ext (mul_right_cancel₀ c.ne_zero h2)
  · intro h
    refine Units.ext (rootModule_end_ext (fun j => ?_) fun β hβ => ?_)
    · simp only [Units.val_mul, Module.End.mul_apply]
      rw [show ((rootDiagUnit τ a : ModGL τ K) : Module.End K (RootModule τ K)) = rootDiag a
          from rfl, rootDiag_canonicalRep_hVec,
        show ((rootDiagUnit τ b : ModGL τ K) : Module.End K (RootModule τ K)) = rootDiag b
          from rfl, rootDiag_hVec]
    · obtain ⟨c, hc⟩ := hmaps β hβ
      simp only [Units.val_mul, Module.End.mul_apply]
      rw [rootDiagUnit_canonicalRep_rootVec a w hβ hc,
        canonicalRep_rootDiagUnit_rootVec b w hβ hc, h β, mul_comm]

theorem rootDiagUnit_mem_torusGroup
    [IsAlgClosed K] (a : Fin τ.rank → Kˣ) :
    rootDiagUnit τ a ∈ torusGroup τ K := by
  obtain ⟨t, ht⟩ := (exceptional_Lang_adjoint_diagonal_lift τ K a).2
  rw [ht]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
  exact torusElt_mem_torusGroup j _

theorem rootDiagUnit_eq_conj_canonicalRep_of_mem_bruhatCell
    [IsAlgClosed K]
    (a b : Fin τ.rank → Kˣ) {w : WeylGroup τ} {g : ModGL τ K} (hg : g ∈ bruhatCell τ K w)
    (hconj : g * rootDiagUnit τ b * g⁻¹ = rootDiagUnit τ a) :
    rootDiagUnit τ a = canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ b *
      (canonicalRep (coxeterSystem τ) K w)⁻¹ := by
  have hTB := triangular_borel_structure.{0, 0} τ K
  have hTa := rootDiagUnit_mem_torusGroup (τ := τ) a
  have hTb := rootDiagUnit_mem_torusGroup (τ := τ) b
  set n := canonicalRep (coxeterSystem τ) K w with hn
  set da := rootDiagUnit τ a with hda
  set db := rootDiagUnit τ b with hdb
  obtain ⟨⟨bb, v⟩, ⟨hbb, hv⟩, hbv⟩ := ((bruhat_cell_factorization τ K).1 w).2.2 hg
  have hbb' : bb ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← hTB.2.2.2.2.1]
    exact hbb
  obtain ⟨h, hh, u, hu, rfl⟩ := hbb'
  simp only at hbv
  subst hbv
  have hconj' : h * u * n * v * db * (h * u * n * v)⁻¹ = da := hconj
  set s := n * db * n⁻¹ with hs
  have hsT : s ∈ torusGroup τ K :=
    (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := K) w) db).1 hTb
  set t := da * s⁻¹ with ht
  have htT : t ∈ torusGroup τ K := mul_mem hTa (inv_mem hsT)
  have hdu : da * u * da⁻¹ ∈ posUnipotent τ K := by
    have := ((chevalley_root_character_and_field_conjugation τ K).2.2.2.1 a).2.1
    rw [← this]
    exact ⟨u, hu, rfl⟩
  have hdv : db * v * db⁻¹ ∈ rootSpan τ K (inversionSet w) := by
    have : (rootSpan τ K (inversionSet w)).map (MulAut.conj db).toMonoidHom =
        rootSpan τ K (inversionSet w) :=
      map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup b hα.1
    rw [← this]
    exact ⟨v, hv, rfl⟩
  have hu' : t⁻¹ * (da * u * da⁻¹) * t ∈ posUnipotent τ K := by
    have hN := hTB.2.2.1 (inv_mem htT)
    have := (Subgroup.mem_normalizer_iff.1 hN (da * u * da⁻¹)).1 hdu
    simpa using this
  have hg' : da * (h * u * n * v) * db⁻¹ = h * u * n * v := by
    rw [← hconj']
    group
  have heq : h * t * (t⁻¹ * (da * u * da⁻¹) * t) * n * (db * v * db⁻¹) = h * u * n * v := by
    calc h * t * (t⁻¹ * (da * u * da⁻¹) * t) * n * (db * v * db⁻¹) =
        (h * da) * u * n * v * db⁻¹ := by
          simp only [ht, hs]
          group
      _ = da * (h * u * n * v) * db⁻¹ := by
          have hcomm : da * h = h * da := rootDiagUnit_mul_comm_of_mem_torusGroup a hh
          rw [← hcomm]
          group
      _ = h * u * n * v := hg'
  obtain ⟨-, h1, -⟩ := (Chevalley_toral_centralizer_Bruhat_factors τ K a).2.1 w w (h * t) h _ u _ v
    (mul_mem hh htT) hh hu' hu hdv hv heq
  have ht1 : t = 1 := by
    rwa [mul_eq_left] at h1
  rw [ht, mul_inv_eq_one] at ht1
  exact ht1

theorem exceptional_root_diagonal_conjugacy_Weyl_transporter
    (τ : Tag) (K : Type) [Field K]
    [IsAlgClosed K] (a b : Fin τ.rank → Kˣ) :
    ((∃ g ∈ adjointGroup τ K, g * rootDiagUnit τ b * g⁻¹ = rootDiagUnit τ a) ↔
      ∃ w : WeylGroup τ, ∀ v : Fin τ.rank → ℤ, rootChar a (w • v) = rootChar b v) ∧
    (∀ (w : WeylGroup τ) (g : ModGL τ K), g ∈ bruhatCell τ K w →
      g * rootDiagUnit τ b * g⁻¹ = rootDiagUnit τ a →
        rootDiagUnit τ a = canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ b *
          (canonicalRep (coxeterSystem τ) K w)⁻¹) ∧
    (∀ w : WeylGroup τ, rootDiagUnit τ a = canonicalRep (coxeterSystem τ) K w *
        rootDiagUnit τ b * (canonicalRep (coxeterSystem τ) K w)⁻¹ ↔
      ∀ v : Fin τ.rank → ℤ, rootChar a (w • v) = rootChar b v) ∧
    ∀ w : WeylGroup τ, canonicalRep (coxeterSystem τ) K w ∈ adjointGroup τ K := by
  refine ⟨⟨fun ⟨g, hg, hconj⟩ => ?_, fun ⟨w, hw⟩ => ?_⟩, fun w g hg hconj =>
    rootDiagUnit_eq_conj_canonicalRep_of_mem_bruhatCell a b hg hconj,
    fun w => rootDiagUnit_eq_conj_canonicalRep_iff a b w,
    fun w => canonicalRep_mem_adjointGroup _ K w⟩
  · have hg' : g ∈ (adjointGroup τ K : Set (ModGL τ K)) := hg
    rw [(bruhat_decomposition τ K).1, Set.mem_iUnion] at hg'
    obtain ⟨w, hw⟩ := hg'
    exact ⟨w, (rootDiagUnit_eq_conj_canonicalRep_iff a b w).1
      (rootDiagUnit_eq_conj_canonicalRep_of_mem_bruhatCell a b hw hconj)⟩
  · exact ⟨_, canonicalRep_mem_adjointGroup _ K w,
      ((rootDiagUnit_eq_conj_canonicalRep_iff a b w).2 hw).symm⟩

end CFSG.LieType.Chevalley
