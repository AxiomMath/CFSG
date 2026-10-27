module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QHom
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAComp2

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} (h : Setting25 G t z z₁ ι zv R0 F)
  {φ : ↥(normalizer (Rgrp h : Set G)) →* A5WrTwo}

private lemma Kgrp_le_normalizer_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) :
    Kgrp ι z ≤ normalizer (Rgrp h : Set G) := by
  intro k hk
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  refine ⟨fun hx => Rgrp_conj h hk hx, fun hx => ?_⟩
  have h1 := Rgrp_conj h (Subgroup.inv_mem (Kgrp ι z) hk) hx
  rwa [show k⁻¹ * (k * x * k⁻¹) * (k⁻¹)⁻¹ = x from by group] at h1

private lemma alt5_commutator_eq_top : commutator (alternatingGroup (Fin 5)) = ⊤ :=
  commutator_alternatingGroup_eq_top (α := Fin 5) (by simp)

private theorem exists_involution_commutator_alt5 :
    ∃ a : alternatingGroup (Fin 5), a ∈ commutator (alternatingGroup (Fin 5)) ∧
      a ≠ 1 ∧ a * a = 1 := by
  let a : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3,
      Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        ⟨0, 1, by decide, rfl⟩ ⟨2, 3, by decide, rfl⟩⟩
  have ha_comm : a ∈ commutator (alternatingGroup (Fin 5)) := by
    rw [alt5_commutator_eq_top]
    exact Subgroup.mem_top a
  have ha_ne : a ≠ 1 := by
    intro hne
    have h0 : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 5)) 0 =
        (1 : Equiv.Perm (Fin 5)) 0 :=
      congrArg (fun p : alternatingGroup (Fin 5) => (p : Equiv.Perm (Fin 5)) 0) hne
    simp [Equiv.swap_apply_def] at h0
  have ha_sq : a * a = 1 := by
    apply Subtype.ext
    ext i
    fin_cases i <;> decide
  exact ⟨a, ha_comm, ha_ne, ha_sq⟩

theorem exists_involution_commutator_K :
    ∃ q ∈ Kgrp ι z, q ∉ Rgrp h ∧ q * q = 1 ∧ q ∈ ⁅Kgrp ι z, Kgrp ι z⁆ := by
  obtain ⟨n, hn, hnz⟩ := h.exists_n_z₁
  have hQK : Qgrp h n ≤ Kgrp ι z := Qgrp_le_K h hn hnz
  have hdisj : Disjoint (Rgrp h) (Qgrp h n) := Rgrp_disjoint_Qgrp h hn hnz
  obtain ⟨a, ha_comm, ha_ne, ha_sq⟩ := exists_involution_commutator_alt5
  obtain ⟨e⟩ := Qgrp_equiv h hn hnz
  let q0 : ↥(Qgrp h n) := e.symm (1, a)
  have heq0 : e q0 = (1, a) := e.apply_symm_apply (1, a)
  haveI : IsMulCommutative (Multiplicative (ZMod 2)) :=
    IsMulCommutative.of_comm (fun a b => mul_comm a b)
  have hcommZ2 : commutator (Multiplicative (ZMod 2)) = ⊥ :=
    commutator_eq_bot (Multiplicative (ZMod 2))
  have hprod : commutator (Multiplicative (ZMod 2) × alternatingGroup (Fin 5)) =
      (⊥ : Subgroup (Multiplicative (ZMod 2))).prod
        (⊤ : Subgroup (alternatingGroup (Fin 5))) := by
    rw [← hcommZ2, ← alt5_commutator_eq_top]
    simp only [_root_.commutator_def]
    rw [← Subgroup.top_prod_top, Subgroup.commutator_prod_prod]
  have hmix : (1, a) ∈ commutator (Multiplicative (ZMod 2) × alternatingGroup (Fin 5)) := by
    rw [hprod, Subgroup.mem_prod]
    exact ⟨Subgroup.mem_bot.mpr rfl, trivial⟩
  have hq0comm : q0 ∈ commutator ↥(Qgrp h n) := by
    have hmap : (commutator ↥(Qgrp h n)).map e.toMonoidHom =
        commutator (Multiplicative (ZMod 2) × alternatingGroup (Fin 5)) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective, _root_.commutator_def]
    have h1 : (1, a) ∈ (commutator ↥(Qgrp h n)).map e.toMonoidHom := by
      rw [hmap]
      exact hmix
    rcases Subgroup.mem_map.mp h1 with ⟨y, hy, hyeq⟩
    have hyq : y = q0 := e.injective (hyeq.trans heq0.symm)
    rwa [hyq] at hy
  have hq0ne : q0 ≠ 1 := by
    intro hne
    apply ha_ne
    have h2 := congrArg (fun x : ↥(Qgrp h n) => (e x).2) hne
    simpa [heq0] using h2
  have hq0sq : q0 * q0 = 1 := by
    apply e.injective
    rw [map_mul, heq0, map_one]
    simp [ha_sq]
  have hqG_commQ : (q0 : G) ∈ ⁅Qgrp h n, Qgrp h n⁆ := by
    rw [← Subgroup.map_subtype_commutator (Qgrp h n)]
    exact Subgroup.mem_map_of_mem _ hq0comm
  refine ⟨(q0 : G), hQK q0.2, ?_, ?_, ?_⟩
  · intro hmem
    have hbot := (disjoint_iff_inf_le.mp hdisj) (Subgroup.mem_inf.mpr ⟨hmem, q0.2⟩)
    exact hq0ne (Subtype.ext (by simpa using hbot))
  · simpa using congrArg Subtype.val hq0sq
  · exact (Subgroup.commutator_mono hQK hQK) hqG_commQ

theorem invol_Aq (hs : Lemma27Spec h φ) :
    ∃ q : ↥(normalizer (Aq h : Set (Xq z))), (q : Xq z) ∉ Aq h ∧ (q : Xq z) * (q : Xq z) = 1 ∧
      psiq h hs q ∈ commutator A5WrTwo := by
  obtain ⟨q, hqK, hqR, hqq, hqcomm⟩ := exists_involution_commutator_K h
  have hKN : Kgrp ι z ≤ normalizer (Rgrp h : Set G) := Kgrp_le_normalizer_Rgrp h
  have hqN : q ∈ normalizer (Rgrp h : Set G) := hKN hqK
  refine ⟨piN h ⟨q, hqN⟩, ?_, ?_, ?_⟩
  · rw [piN_val h]
    exact fun hmem => hqR ((mem_Aq_iff h ⟨q, normalizer_Rgrp_le_Mgrp h hqN⟩).mp hmem)
  · have hn : (⟨q, hqN⟩ : ↥(normalizer (Rgrp h : Set G))) * ⟨q, hqN⟩ = 1 :=
      Subtype.ext (by simpa using hqq)
    have hsq : piN h ⟨q, hqN⟩ * piN h ⟨q, hqN⟩ = 1 := by
      rw [← map_mul, hn, map_one]
    simpa using congrArg Subtype.val hsq
  · rw [psiq_piN h hs]
    have hq_commN : q ∈ ⁅normalizer (Rgrp h : Set G), normalizer (Rgrp h : Set G)⁆ :=
      (Subgroup.commutator_mono hKN hKN) hqcomm
    have hsub_comm : (⟨q, hqN⟩ : ↥(normalizer (Rgrp h : Set G))) ∈
        commutator ↥(normalizer (Rgrp h : Set G)) := by
      have hmap := Subgroup.map_subtype_commutator (normalizer (Rgrp h : Set G))
      have h1 : q ∈ (commutator ↥(normalizer (Rgrp h : Set G))).map
          (normalizer (Rgrp h : Set G)).subtype := by
        rw [hmap]
        exact hq_commN
      rcases Subgroup.mem_map.mp h1 with ⟨y, hy, hyq⟩
      have : y = ⟨q, hqN⟩ := Subtype.ext (by simpa using hyq)
      rwa [this] at hy
    have hφmap : (commutator ↥(normalizer (Rgrp h : Set G))).map φ = commutator A5WrTwo := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hs.surj, _root_.commutator_def]
    have hφcomm : φ ⟨q, hqN⟩ ∈ (commutator ↥(normalizer (Rgrp h : Set G))).map φ :=
      Subgroup.mem_map_of_mem φ hsub_comm
    rwa [hφmap] at hφcomm

end CFSG.EvenSporadicStandard.HNRecog.Harada
