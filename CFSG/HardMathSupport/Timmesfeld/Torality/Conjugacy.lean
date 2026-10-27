module

public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

set_option linter.unusedSectionVars false

section


theorem bruhat_factor_exists (τ : Tag) (K : Type) [Field K] :
    ∀ g ∈ adjointGroup τ K, ∃ w : WeylGroup τ, ∃ h ∈ torusGroup τ K,
      ∃ u ∈ posUnipotent τ K, ∃ v ∈ rootSpan τ K (inversionSet w),
        g = h * u * canonicalRep (coxeterSystem τ) K w * v := by
  have hTB := triangular_borel_structure.{0, 0} τ K
  intro g hg
  have hg' : g ∈ (adjointGroup τ K : Set (ModGL τ K)) := hg
  rw [(bruhat_decomposition τ K).1, Set.mem_iUnion] at hg'
  obtain ⟨w, hw⟩ := hg'
  obtain ⟨⟨b, v⟩, ⟨hb, hv⟩, hbv⟩ := ((bruhat_cell_factorization τ K).1 w).2.2 hw
  have hb' : b ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← hTB.2.2.2.2.1]
    exact hb
  obtain ⟨h, hh, u, hu, rfl⟩ := hb'
  exact ⟨w, h, hh, u, hu, v, hv, hbv.symm⟩

theorem bruhat_factor_unique (τ : Tag) (K : Type) [Field K] :
    ∀ (w w' : WeylGroup τ) (h h' u u' v v' : ModGL τ K), h ∈ torusGroup τ K →
      h' ∈ torusGroup τ K → u ∈ posUnipotent τ K → u' ∈ posUnipotent τ K →
      v ∈ rootSpan τ K (inversionSet w) → v' ∈ rootSpan τ K (inversionSet w') →
      h * u * canonicalRep (coxeterSystem τ) K w * v =
        h' * u' * canonicalRep (coxeterSystem τ) K w' * v' →
      w = w' ∧ h = h' ∧ u = u' ∧ v = v' := by
  have hTB := triangular_borel_structure.{0, 0} τ K
  intro w w' h h' u u' v v' hh hh' hu hu' hv hv' heq
  have hb : h * u ∈ borelGroup τ K :=
    mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hu)
  have hb' : h' * u' ∈ borelGroup τ K :=
    mul_mem (Subgroup.mem_sup_left hh') (Subgroup.mem_sup_right hu')
  have hc := ((bruhat_cell_factorization τ K).1 w).1 (x := (h * u, v)) ⟨hb, hv⟩
  have hc' := ((bruhat_cell_factorization τ K).1 w').1 (x := (h' * u', v')) ⟨hb', hv'⟩
  simp only at hc hc'
  have hww : w = w' := by
    by_contra hne
    have hdis := (bruhat_decomposition τ K).2.1 w w' hne
    rw [heq] at hc
    exact Set.disjoint_left.1 hdis hc hc'
  subst hww
  have hinj := ((bruhat_cell_factorization τ K).1 w).2.1 (x₁ := (h * u, v))
    (x₂ := (h' * u', v')) ⟨hb, hv⟩ ⟨hb', hv'⟩ heq
  simp only [Prod.mk.injEq] at hinj
  obtain ⟨hhu, hvv⟩ := hinj
  obtain ⟨h1, h2⟩ := hTB.2.2.2.2.2.2.1 h hh h' hh' u hu u' hu' hhu
  exact ⟨rfl, h1, h2, hvv⟩

theorem exists_weyl_of_conj_family (τ : Tag) (K : Type) [Field K] [IsAlgClosed K] {ι : Type}
    (a b : ι → Fin τ.rank → Kˣ) {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (hconj : ∀ i, g * rootDiagUnit τ (b i) * g⁻¹ = rootDiagUnit τ (a i)) :
    ∃ w : WeylGroup τ, ∀ i, rootDiagUnit τ (a i) =
      canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ (b i) *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ := by
  have hTB := triangular_borel_structure.{0, 0} τ K
  obtain ⟨w, t, ht, u, hu, v, hv, rfl⟩ := bruhat_factor_exists τ K g hg
  refine ⟨w, fun i => ?_⟩
  set d := rootDiagUnit τ (b i) with hd
  set e := rootDiagUnit τ (a i) with he
  have hdT : d ∈ torusGroup τ K := rootDiagUnit_mem_torusGroup _
  have heT : e ∈ torusGroup τ K := rootDiagUnit_mem_torusGroup _
  have hnw := canonicalRep_mem_normalizer (R := K) w
  set nw := canonicalRep (coxeterSystem τ) K w with hnwdef
  have hnormT : ∀ x ∈ torusGroup τ K, nw * x * nw⁻¹ ∈ torusGroup τ K := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 hnw x).1 hx
  set t₁ := nw * d * nw⁻¹ with ht₁
  have ht₁T : t₁ ∈ torusGroup τ K := hnormT d hdT
  have hv₁ : d⁻¹ * v * d ∈ rootSpan τ K (inversionSet w) := by
    have : (rootSpan τ K (inversionSet w)).map (MulAut.conj d⁻¹).toMonoidHom =
        rootSpan τ K (inversionSet w) := by
      refine map_rootSpan_of_forall fun α hα => ?_
      have := map_conj_rootDiagUnit_rootSubgroup (fun j => (b i j)⁻¹) hα.1
      rwa [show rootDiagUnit τ (fun j => (b i j)⁻¹) = d⁻¹ from
        (((rootDiagUnitHom τ K).map_inv (b i)).symm)] at this
    rw [← this]
    exact ⟨v, hv, by simp⟩
  have hu' : t₁⁻¹ * u * t₁ ∈ posUnipotent τ K := by
    have hN := hTB.2.2.1 (inv_mem ht₁T)
    have := (Subgroup.mem_normalizer_iff.1 hN u).1 hu
    simpa using this
  have h1 := hconj i
  rw [← hd, ← he, mul_inv_eq_iff_eq_mul] at h1
  have heq : (e * t) * u * nw * v = (t * t₁) * (t₁⁻¹ * u * t₁) * nw * (d⁻¹ * v * d) := by
    have h2 : e * (t * u * nw * v) = t * u * nw * v * d := h1.symm
    calc (e * t) * u * nw * v = e * (t * u * nw * v) := by group
      _ = t * u * nw * v * d := h2
      _ = (t * t₁) * (t₁⁻¹ * u * t₁) * nw * (d⁻¹ * v * d) := by
        simp only [ht₁]
        group
  have hcomm : e * t = t * e := by
    have := rootDiagUnit_mul_comm_of_mem_torusGroup (a i) ht
    exact this
  obtain ⟨-, h3, -, -⟩ := bruhat_factor_unique τ K w w (e * t) (t * t₁) u (t₁⁻¹ * u * t₁) v
    (d⁻¹ * v * d) (mul_mem heT ht) (mul_mem ht ht₁T) hu hu' hv hv₁ heq
  have h4 : t₁ = e := by
    have : t * e = t * t₁ := by rw [← hcomm]; exact h3
    exact (mul_left_cancel this).symm
  rw [← h4]

end

end CFSG.HardMathSupport.Timmesfeld.Torality
