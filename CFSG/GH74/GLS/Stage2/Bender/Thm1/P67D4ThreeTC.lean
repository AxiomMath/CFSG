module

public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup

public section

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
open scoped Pointwise

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

variable {τ : Tag} {K : Type} [Field K]

theorem rootCharKernel_inv (a : Fin τ.rank → Kˣ) : rootCharKernel a⁻¹ = rootCharKernel a := by
  ext α
  simp only [rootCharKernel, Set.mem_ofPred_eq, rootChar_inv_apply, inv_eq_one]

theorem rootSpan_empty :
    rootSpan τ K (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by
  simp [rootSpan]

theorem exists_weyl_of_conj_regular [IsAlgClosed K] (a b : Fin τ.rank → Kˣ)
    (ha : rootCharKernel a = ∅) (hb : rootCharKernel b = ∅) {g : ModGL τ K}
    (hg : g ∈ adjointGroup τ K)
    (hconj : rootDiagUnit τ a * g = g * rootDiagUnit τ b) :
    ∃ (w : WeylGroup τ) (h : ModGL τ K), h ∈ torusGroup τ K ∧
      g = h * canonicalRep (coxeterSystem τ) K w ∧ weylTuple w b = a := by
  classical
  have hTB := triangular_borel_structure.{0, 0} τ K
  have huniq := (Chevalley_toral_centralizer_Bruhat_factors τ K (fun _ => 1)).2.1
  have hposfin : {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β}.Finite :=
    (finite_setOf_isRoot τ).subset fun β hβ => hβ.1
  obtain ⟨w, h, hh, u, hu, v, hv, rfl⟩ : ∃ w : WeylGroup τ, ∃ h ∈ torusGroup τ K,
      ∃ u ∈ posUnipotent τ K, ∃ v ∈ rootSpan τ K (inversionSet w),
        g = h * u * canonicalRep (coxeterSystem τ) K w * v := by
    have hg' : g ∈ (adjointGroup τ K : Set (ModGL τ K)) := hg
    rw [(bruhat_decomposition τ K).1, Set.mem_iUnion] at hg'
    obtain ⟨w, hw⟩ := hg'
    obtain ⟨⟨b', v⟩, ⟨hb', hv⟩, hbv⟩ := ((bruhat_cell_factorization τ K).1 w).2.2 hw
    have hb'' : b' ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
      rw [← hTB.2.2.2.2.1]
      exact hb'
    obtain ⟨h, hh, u, hu, rfl⟩ := hb''
    exact ⟨w, h, hh, u, hu, v, hv, hbv.symm⟩
  set n := canonicalRep (coxeterSystem τ) K w with hn
  set da := rootDiagUnit τ a with hda
  set db := rootDiagUnit τ b with hdb
  set dwb := rootDiagUnit τ (weylTuple w b) with hdwb
  have hnb : n * db = dwb * n := by
    have := canonicalRep_conj_rootDiagUnit (K := K) w b
    rw [← hn, ← hdb, ← hdwb, mul_inv_eq_iff_eq_mul] at this
    exact this
  have hdaH : da⁻¹ ∈ torusGroup τ K := inv_mem (rootDiagUnit_mem_torusGroup a)
  have hdwbH : dwb ∈ torusGroup τ K := rootDiagUnit_mem_torusGroup _
  have hha : da⁻¹ * h = h * da⁻¹ := by
    have := rootDiagUnit_mul_comm_of_mem_torusGroup a hh
    rw [← hda] at this
    calc da⁻¹ * h = da⁻¹ * h * (da * da⁻¹) := by group
      _ = da⁻¹ * (h * da) * da⁻¹ := by group
      _ = da⁻¹ * (da * h) * da⁻¹ := by rw [this]
      _ = h * da⁻¹ := by group
  set t := da⁻¹ * dwb with ht
  have htH : t ∈ torusGroup τ K := mul_mem hdaH hdwbH
  have hdu : da⁻¹ * u * da ∈ posUnipotent τ K := by
    have := ((chevalley_root_character_and_field_conjugation τ K).2.2.2.1 a⁻¹).2.1
    rw [← this]
    refine ⟨u, hu, ?_⟩
    change rootDiagUnit τ a⁻¹ * u * (rootDiagUnit τ a⁻¹)⁻¹ = da⁻¹ * u * da
    rw [hda, ← rootDiagUnit_inv, inv_inv]
  have hdv : db⁻¹ * v * db ∈ rootSpan τ K (inversionSet w) := by
    have : (rootSpan τ K (inversionSet w)).map (MulAut.conj (rootDiagUnit τ b⁻¹)).toMonoidHom =
        rootSpan τ K (inversionSet w) :=
      map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup b⁻¹ hα.1
    rw [← this]
    refine ⟨v, hv, ?_⟩
    change rootDiagUnit τ b⁻¹ * v * (rootDiagUnit τ b⁻¹)⁻¹ = db⁻¹ * v * db
    rw [hdb, ← rootDiagUnit_inv, inv_inv]
  have hu' : t⁻¹ * (da⁻¹ * u * da) * t ∈ posUnipotent τ K := by
    have hN := hTB.2.2.1 (inv_mem htH)
    have := (Subgroup.mem_normalizer_iff.1 hN (da⁻¹ * u * da)).1 hdu
    simpa using this
  have heq : h * t * (t⁻¹ * (da⁻¹ * u * da) * t) * n * (db⁻¹ * v * db) = h * u * n * v := by
    have h1 : da⁻¹ * (h * u * n * v) * db = h * u * n * v := by
      calc da⁻¹ * (h * u * n * v) * db = da⁻¹ * ((h * u * n * v) * db) := by rw [mul_assoc]
        _ = da⁻¹ * (da * (h * u * n * v)) := by rw [← hconj]
        _ = h * u * n * v := by group
    have e2 : h * t * (t⁻¹ * (da⁻¹ * u * da) * t) * n * (db⁻¹ * v * db) =
        h * da⁻¹ * u * (dwb * n) * (db⁻¹ * v * db) := by
      rw [ht]
      group
    rw [e2, ← hnb]
    calc h * da⁻¹ * u * (n * db) * (db⁻¹ * v * db) = (h * da⁻¹) * u * n * v * db := by group
      _ = (da⁻¹ * h) * u * n * v * db := by rw [hha]
      _ = da⁻¹ * (h * u * n * v) * db := by group
      _ = h * u * n * v := h1
  obtain ⟨-, h1, h2, h3⟩ := huniq w w (h * t) h _ u _ v (mul_mem hh htH) hh hu' hu hdv hv heq
  have ht1 : t = 1 := by
    have := h1
    rwa [mul_eq_left] at this
  rw [ht1] at h2
  simp only [inv_one, one_mul, mul_one] at h2
  have hwb : weylTuple w b = a := by
    have : da = dwb := by
      have h5 : da⁻¹ * dwb = 1 := ht1
      calc da = da * (da⁻¹ * dwb) := by rw [h5, mul_one]
        _ = dwb := by group
    exact (rootDiagUnit_injective this.symm)
  have hu1 : u = 1 := by
    have hfix : rootDiagUnit τ a⁻¹ * u * (rootDiagUnit τ a⁻¹)⁻¹ = u := by
      rw [← rootDiagUnit_inv, inv_inv]
      exact h2
    have := mem_rootSpan_inter_of_conj_eq a⁻¹ hposfin (fun β hβ => hβ.1)
      (fun α hα hr => (positive_root_collection τ K).2 α hα hr) hu hfix
    rw [rootCharKernel_inv, ha, Set.empty_inter, rootSpan_empty, Subgroup.mem_bot] at this
    exact this
  have hv1 : v = 1 := by
    have hfix : rootDiagUnit τ b⁻¹ * v * (rootDiagUnit τ b⁻¹)⁻¹ = v := by
      rw [← rootDiagUnit_inv, inv_inv]
      exact h3
    have := mem_rootSpan_inter_of_conj_eq b⁻¹ (inversionSet_finite w) (fun β hβ => hβ.1)
      (fun α hα hr => (bruhat_cell_factorization τ K).2.1 w α hα hr) hv hfix
    rw [rootCharKernel_inv, hb, Set.empty_inter, rootSpan_empty, Subgroup.mem_bot] at this
    exact this
  refine ⟨w, h, hh, ?_, hwb⟩
  rw [hu1, hv1, mul_one, mul_one]

end CFSG.GH74.GLS.Stage2.Bender.Thm1
