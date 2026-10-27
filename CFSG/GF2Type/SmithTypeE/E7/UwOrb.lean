module

public import CFSG.GF2Type.SmithTypeE.E7.IdUA
public import Certificates.Certificate38820

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod

theorem planeImg_eq_planeImgM (k i : ℕ) : planeImg k i = planeImgM (tvCols k) i := rfl

attribute [local irreducible] planeImg planeImgM tvCols tvLin

section Cert


theorem uwGensCheck_holds : uw7ChkGens () = true := Certificates.certificate38820.1

theorem uwClsCheck_holds : uw7ChkCls () = true := Certificates.certificate38820.2.1

theorem uwOrbCheck_holds : ∀ v < 75735, Relation.ReflTransGen
    (fun a b => ∃ g < 45, uw7Cls a = uw7Cls b ∧ planeImg (uw7Gens ())[g]! a = b)
    ((uw7Reps ())[uw7Cls v]!) v :=
  Certificates.certificate38820.2.2.1

theorem uwDistCheck_holds : uw7ChkDist () = true := Certificates.certificate38820.2.2.2

theorem gens_unpack : (uw7Gens ()).size = 45 ∧
    ∀ g < 45, (uw7Gens ())[g]! < 365211 ∧ planeImg (uw7Gens ())[g]! 0 = 0 := by
  have h := uwGensCheck_holds
  simp only [uw7ChkGens, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun g hg => ?_⟩
  have hg' : g < (uw7Gens ()).size := by omega
  have := Array.all_eq_true'.mp h2 (uw7Gens ())[g] (Array.getElem_mem hg')
  rw [getElem!_pos (uw7Gens ()) g hg']
  simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this

theorem cls_unpack :
    (∀ c < 4, (uw7Reps ())[c]! < 75735 ∧ uw7Cls (uw7Reps ())[c]! = c) ∧
    ∀ c < 4, ((List.range 75735).filter fun j => uw7Cls j == c).length = uw7Sizes[c]! := by
  have h := uwClsCheck_holds
  simp only [uw7ChkCls, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨-, h2⟩, h3⟩ := h
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · have := List.all_eq_true.mp h2 c (List.mem_range.mpr hc)
    simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this
  · have := List.all_eq_true.mp h3 c (List.mem_range.mpr hc)
    simpa only [beq_iff_eq] using this

end Cert

section Classes

theorem uw7Cls_le (j : ℕ) : uw7Cls j ≤ 3 := by
  unfold uw7Cls
  split_ifs <;> omega


theorem opp_iff_fB {i j : ℕ} (hi : i < 75735) (hj : j < 75735) :
    Opp i j ↔ fB (wt i) (wt j) = true := by
  have h := fModel_wtV hi hj
  rw [wtV, wtV, fModel_decode] at h
  by_cases ho : Opp i j
  · rw [if_pos ho] at h
    refine ⟨fun _ => ?_, fun _ => ho⟩
    cases hb : fB (wt i) (wt j)
    · rw [hb] at h
      exact absurd h (by decide)
    · rfl
  · rw [if_neg ho] at h
    constructor
    · intro h'
      exact absurd h' ho
    · intro hb
      rw [hb] at h
      exact absurd h (by decide)

theorem adjW_zero_zero : adjW 0 0 = true := by
  simp [adjW]

theorem uw7Cls_eq_two_iff {j : ℕ} (hj : j < 75735) :
    uw7Cls j = 2 ↔ adjW 0 j = false ∧ ¬ Opp 0 j := by
  rw [opp_iff_fB (by norm_num) hj]
  by_cases h0 : j = 0
  · subst h0
    simp [uw7Cls, adjW_zero_zero]
  · cases ha : adjW 0 j <;> cases hf : fB (wt 0) (wt j) <;> simp [uw7Cls, h0, ha, hf]

theorem tvP_mem_Stab0 {k : Fin 365211} (hk : planeImg k.val 0 = 0) :
    (⟨tvP k, tvP_mem k⟩ : TD6) ∈ Stab0 := by
  rw [MulAction.mem_stabilizer_iff, tvP_smul]
  exact Fin.ext hk

end Classes

section Orbits


theorem card_filter_cls {c : ℕ} (hc : c < 4) :
    (Finset.univ.filter fun j : Fin 75735 => uw7Cls j.val = c).card = uw7Sizes[c]! := by
  obtain ⟨-, h⟩ := cls_unpack
  rw [← h c hc]
  have e : (Finset.univ.filter fun j : Fin 75735 => uw7Cls j.val = c).map Fin.valEmbedding =
      (Finset.range 75735).filter fun j => uw7Cls j = c := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    exact ⟨fun ⟨b, hb, hba⟩ => hba ▸ ⟨b.2, hb⟩, fun ⟨ha, hc⟩ => ⟨⟨a, ha⟩, hc, rfl⟩⟩
  rw [← Finset.card_map Fin.valEmbedding, e]
  simp only [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  apply congrArg List.length
  apply List.filter_congr
  intro x _
  by_cases hx : uw7Cls x = c <;> simp [hx]

theorem ncard_cls {c : ℕ} (hc : c < 4) :
    {j : Fin 75735 | uw7Cls j.val = c}.ncard = uw7Sizes[c]! := by
  rw [show {j : Fin 75735 | uw7Cls j.val = c} =
      ↑(Finset.univ.filter fun j : Fin 75735 => uw7Cls j.val = c) by ext; simp,
    Set.ncard_coe_finset, card_filter_cls hc]

theorem ncard_mid : {j : Fin 75735 | adjW 0 j.val = false ∧ ¬ Opp 0 j.val}.ncard = 41664 := by
  have e : {j : Fin 75735 | adjW 0 j.val = false ∧ ¬ Opp 0 j.val} =
      {j : Fin 75735 | uw7Cls j.val = 2} := by
    ext j
    exact (uw7Cls_eq_two_iff j.2).symm
  rw [e, ncard_cls (by norm_num)]
  rfl

theorem orb_tree_aux : ∀ v < 75735, ∃ r : Fin 75735, r.val = (uw7Reps ())[uw7Cls v]! ∧
    ∃ g ∈ Stab0, ((g • r : Fin 75735) : ℕ) = v := by
  obtain ⟨-, hgens⟩ := gens_unpack
  obtain ⟨hreps, -⟩ := cls_unpack
  have key : ∀ (r : Fin 75735) (b : ℕ), Relation.ReflTransGen
      (fun a b => ∃ g < 45, uw7Cls a = uw7Cls b ∧ planeImg (uw7Gens ())[g]! a = b) r.val b →
      ∃ g ∈ Stab0, ((g • r : Fin 75735) : ℕ) = b := by
    intro r b h
    induction h with
    | refl => exact ⟨1, Stab0.one_mem, by rw [one_smul]⟩
    | tail _ hbc ih =>
      obtain ⟨g₀, hg₀, hg₀r⟩ := ih
      obtain ⟨g, hg, -, hgv⟩ := hbc
      obtain ⟨hgl, hg0⟩ := hgens g hg
      obtain ⟨k, hk⟩ : ∃ k : Fin 365211, k.val = (uw7Gens ())[g]! := ⟨⟨_, hgl⟩, rfl⟩
      rw [← hk] at hg0 hgv
      refine ⟨⟨tvP k, tvP_mem k⟩ * g₀, Stab0.mul_mem (tvP_mem_Stab0 hg0) hg₀, ?_⟩
      rw [mul_smul, tvP_smul]
      change planeImg k.val (g₀ • r : Fin 75735).val = _
      rw [hg₀r]
      exact hgv
  intro v hv
  have hc : uw7Cls v < 4 := by
    have := uw7Cls_le v
    omega
  exact ⟨⟨_, (hreps _ hc).1⟩, rfl, key _ _ (uwOrbCheck_holds v hv)⟩

theorem exists_stab0_image {j j' : Fin 75735} (h : uw7Cls j.val = uw7Cls j'.val) :
    ∃ g ∈ Stab0, g • j = j' := by
  obtain ⟨r, hr, g, hg, hgr⟩ := orb_tree_aux j.val j.2
  obtain ⟨r', hr', g', hg', hgr'⟩ := orb_tree_aux j'.val j'.2
  have hrr : r = r' := Fin.ext (by rw [hr, hr', h])
  subst hrr
  refine ⟨g' * g⁻¹, Stab0.mul_mem hg' (Stab0.inv_mem hg), ?_⟩
  have h1 : g⁻¹ • j = r := by
    rw [inv_smul_eq_iff]
    exact (Fin.ext hgr).symm
  rw [mul_smul, h1]
  exact Fin.ext hgr'

theorem exists_stab0_mid {j j' : Fin 75735} (hj : adjW 0 j.val = false ∧ ¬ Opp 0 j.val)
    (hj' : adjW 0 j'.val = false ∧ ¬ Opp 0 j'.val) : ∃ g ∈ Stab0, g • j = j' :=
  exists_stab0_image (((uw7Cls_eq_two_iff j.2).2 hj).trans ((uw7Cls_eq_two_iff j'.2).2 hj').symm)

theorem uw7Cls_eq_distD {j : ℕ} (hj : j < 75735) : uw7Cls j = distD 0 j := by
  have h := uwDistCheck_holds
  simp only [uw7ChkDist, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h j hj

theorem exists_stab0_image_distD {j j' : Fin 75735} (h : distD 0 j.val = distD 0 j'.val) :
    ∃ g ∈ Stab0, g • j = j' :=
  exists_stab0_image (by rw [uw7Cls_eq_distD j.2, uw7Cls_eq_distD j'.2, h])

end Orbits

end CFSG.GF2Type.SmithTypeE.E7
