module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Sp6
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Link
public import Certificates.Certificate126

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.EvenSmallLie.Sp6
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Q3.TL4.E4C CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data

theorem link_parts :
    twin () * sp6Rep2 = sp6Rep2 * twin () ∧ three () ^ 3 = 1 ∧
      norms (L0 ()) (rho ()) (jay ()) (three ()) = true ∧
      three () * rho () ≠ rho () * three () := by
  have h := Certificates.certificate126
  simp only [linkCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [tab_eq] at h1
  exact ⟨h1, h2, h3, h4⟩

theorem exists_emb
    {M : Type} [Group M]
    (e : M ≃* ↥co3X36) {K : Subgroup M} {s : M} (hd : QuatTwinDatum K s) :
    ∃ φ : M →* Equiv.Perm (Fin 36), Function.Injective φ ∧ φ.range = co3X36 ∧ K.map φ = K0 := by
  obtain ⟨m, hm⟩ := sp62QuatIdent e hd
  refine ⟨(MulAut.conj (emb e m)).toMonoidHom.comp (emb e),
    (MulAut.conj (emb e m)).injective.comp (emb_injective e), ?_, ?_⟩
  · rw [MonoidHom.range_comp, range_emb]
    exact conjSub_eq_self_of_mem (e m).2
  · rw [← Subgroup.map_map]
    exact hm

theorem eq_rep_of_isUniqueInvolution {sc : Equiv.Perm (Fin 36)}
    (h : IsUniqueInvolution K0 sc) : sc = sp6Rep2 := by
  have ht := check_parts.2.2.2.2.2.2.2.1
  simp only [treeCheck, Bool.and_eq_true, List.all_eq_true] at ht
  have hρ := ht.1 (rho ()) (by simp [U, L0, q8Elems])
  simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hρ
  obtain ⟨⟨-, h2⟩, h4⟩ := hρ
  have hρK : rho () ∈ K0 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hsq : rho () * rho () * (rho () * rho ()) = 1 := by
    rw [← h4]
    simp [pow_succ, mul_assoc]
  have hne : rho () * rho () ≠ 1 := by
    rw [← pow_two]
    exact h2
  rw [← (h.unique _ (K0.mul_mem hρK hρK) hsq).resolve_left hne, check_parts.1, tab_eq]

theorem e4QuatNbrInv_PSp
    {M : Type} [Group M] [Finite M] (hM : CFSG.Blueprint.LieModel M .PSp 3 2 1) :
    E4QuatNbrInv M := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hM
  refine Vtx.e4QuatNbrInv_of_model co3X36 K0 (fun K s hd => exists_emb e hd)
    (fun sc hsc h hh hne hle => ?_)
  rw [eq_twin_of_le_normalizer hh hne hle]
  have h1 := hsc.conj (twin ())
  rwa [show twin () * sc * (twin ())⁻¹ = sc by
    rw [eq_rep_of_isUniqueInvolution hsc, link_parts.1]
    group] at h1

theorem three_mem :
    three () ∈ co3X36 := by
  have hQX : sp6CentQ2.originalSubgroup ≤ co3X36 := by
    rw [← sp6_cent_spec₂.1, sp6Q_originalSubgroup]
    exact inf_le_left
  rw [three, tab_eq]
  refine hQX (evalCodes_mem _ (fun g hg => ?_) _)
  rw [sp6CentQ2, certificate_originalSubgroup]
  exact Subgroup.subset_closure hg

theorem e4QuatActs3_PSp
    {M : Type} [Group M] [Finite M] (hM : CFSG.Blueprint.LieModel M .PSp 3 2 1) :
    E4QuatActs3 M := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hM
  exact Vtx.e4QuatActs3_of_model co3X36 K0 (fun K s hd => exists_emb e hd)
    ⟨three (), three_mem, link_parts.2.1, conjSub_eq_of_norms mem_K0_iff link_parts.2.2.1,
      rho (), Subgroup.subset_closure (Set.mem_insert _ _), link_parts.2.2.2⟩

end CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
