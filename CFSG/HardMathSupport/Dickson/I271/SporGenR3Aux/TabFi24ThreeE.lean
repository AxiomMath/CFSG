module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24FreeLam
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24FreeBfs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24Shape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThG2Rec

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi24

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)
open CFSG.GH74.QTGen4.Recog.G23 (SatisfiesG23Words)
open CFSG.HardMathSupport.Dickson.I271.Fi24Free.Native (frG1 frH0)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

set_option linter.unusedSectionVars false

section Groups


noncomputable abbrev centX : Subgroup J := Subgroup.centralizer ({xJ} : Set J)

theorem mem_centX {g : J} : g ∈ centX ↔ xJ * g = g * xJ := by
  simp [Subgroup.mem_centralizer_iff]

noncomputable abbrev cent1 : Subgroup J := centX ⊓ lvl 2

noncomputable abbrev stab4 : Subgroup J :=
  lvl 2 ⊓ MulAction.stabilizer J cA ⊓ MulAction.stabilizer J cB

theorem mem_stab4 {g : J} : g ∈ stab4 ↔ g ∈ lvl 2 ∧ g • cA = cA ∧ g • cB = cB := by
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, and_assoc]

theorem comm_xJ {g : J} (hs : s0 * g = g * s0) (hu : u2 * g = g * u2) : xJ * g = g * xJ := by
  show s0 * u2 * g = g * (s0 * u2)
  calc s0 * u2 * g = s0 * (u2 * g) := mul_assoc _ _ _
    _ = s0 * (g * u2) := by rw [hu]
    _ = (s0 * g) * u2 := (mul_assoc _ _ _).symm
    _ = (g * s0) * u2 := by rw [hs]
    _ = g * (s0 * u2) := mul_assoc _ _ _

theorem s0_mem_centX (hF : FrameFacts) : s0 ∈ centX := by
  rw [mem_centX]
  show s0 * u2 * s0 = s0 * (s0 * u2)
  rw [mul_assoc, ← s0_mul_u2 hF]

theorem u2_mem_centX (hF : FrameFacts) : u2 ∈ centX := by
  rw [mem_centX]
  show s0 * u2 * u2 = u2 * (s0 * u2)
  rw [← mul_assoc, ← s0_mul_u2 hF]

theorem centX_comm_smul {g : J} (hg : g ∈ centX) (p : Fin 306936) :
    g • xJ • p = xJ • g • p :=
  (comm_smul_smul (mem_centX.1 hg) p).symm

theorem mem_cent1 {g : J} : g ∈ cent1 ↔ g ∈ centX ∧ g ∈ lvl 2 := Subgroup.mem_inf

theorem cB_fix_of_cA_fix (hF : FrameFacts) {g : J} (hg : g ∈ centX) (h : g • cA = cA) :
    g • cB = cB := by
  rw [← xJ_smul_cA hF, centX_comm_smul hg, h]

theorem fix_m1_of_fix (hF : FrameFacts) {g : J} (hg : g ∈ centX) (h : g • pt1 = pt1) :
    g • third pt0 pt1 = third pt0 pt1 := by
  rw [← xJ_smul_pt1 hF, centX_comm_smul hg, h]

end Groups

section Dec


theorem stab4_le_centX : stab4 ≤ centX := by
  intro g hg
  obtain ⟨hl, hA, hB⟩ := mem_stab4.1 hg
  have hs : s0 * g = g * s0 := mem_cent0.1 (lvl_two_le_cent0 hl)
  have hu : u2 * g = g * u2 := by
    apply CFSG.Sporadic.Fi24.jR_injective
    rw [map_mul, map_mul, jR_u2]
    have c0 := (smul_eq_iff_commute g cA).1 hA
    have c1 := (smul_eq_iff_commute g cB).1 hB
    calc cls cA * cls cB * jR g = cls cA * (cls cB * jR g) := by rw [mul_assoc]
      _ = cls cA * (jR g * cls cB) := by rw [c1]
      _ = (cls cA * jR g) * cls cB := by rw [mul_assoc]
      _ = (jR g * cls cA) * cls cB := by rw [c0]
      _ = jR g * (cls cA * cls cB) := by rw [mul_assoc]
  exact mem_centX.2 (comm_xJ hs hu)

theorem stab4_le_cent1 : stab4 ≤ cent1 :=
  fun _ hg => mem_cent1.2 ⟨stab4_le_centX hg, (mem_stab4.1 hg).1⟩

theorem mem_cent1_of_fix (hF : FrameFacts) {g : J} (hg : g ∈ centX) (h : g • pt0 = pt0) :
    g ∈ cent1 := by
  refine mem_cent1.2 ⟨hg, mem_lvl_two_of_fix h ?_⟩
  rw [← xJ_smul_pt0 hF, centX_comm_smul hg, h]

theorem u2_mem_cent1 (hF : FrameFacts) : u2 ∈ cent1 :=
  mem_cent1.2 ⟨u2_mem_centX hF, mem_lvl_two_of_fix (u2_smul_pt0 hF) (u2_smul_pt1 hF)⟩

theorem cent1_fix_m1 (hF : FrameFacts) {g : J} (hg : g ∈ cent1) :
    g • third pt0 pt1 = third pt0 pt1 :=
  fix_m1_of_fix hF (mem_cent1.1 hg).1 (fix_of_mem_lvl_two (mem_cent1.1 hg).2).2

theorem card_cent1_of_orbit (hF : FrameFacts)
    (horb : Nat.card (MulAction.orbit cent1 cA) = 3) :
    Nat.card cent1 = 3 * Nat.card stab4 := by
  haveI : Finite J := finite_J
  have h := CFSG.Perm.card_eq_orbit_mul cent1 stab4 cA stab4_le_cent1
    (fun _ hl => (mem_stab4.1 hl).2.1)
    (fun _ hh hfix => mem_stab4.2 ⟨(mem_cent1.1 hh).2, hfix,
      cB_fix_of_cA_fix hF (mem_cent1.1 hh).1 hfix⟩)
  rw [h, horb]

theorem card_centX_of_orbit (hF : FrameFacts)
    (horb : Nat.card (MulAction.orbit centX pt0) = 3) :
    Nat.card centX = 3 * Nat.card cent1 := by
  haveI : Finite J := finite_J
  have h := CFSG.Perm.card_eq_orbit_mul centX cent1 pt0 inf_le_left
    (fun _ hl => (fix_of_mem_lvl_two (mem_cent1.1 hl).2).1)
    (fun _ hh hfix => mem_cent1_of_fix hF hh hfix)
  rw [h, horb]

end Dec

section Main


theorem centX_not_cA {g : J} (hg : g ∈ centX) (h : g • pt0 = cA) : False := by
  have hF := frame_facts
  have hB := bfs_facts
  have h1 : g • pt1 = cB := by
    rw [← xJ_smul_pt0 hF, centX_comm_smul hg, h, xJ_smul_cA hF]
  have hk : wordElt frH0 * g ∈ lvl 2 := by
    refine mem_lvl_two_of_fix ?_ ?_
    · rw [mul_smul, h, h0_cA hB]
    · rw [mul_smul, h1, h0_cB hB]
  have ha : InLam (g • cA) :=
    inLam_smul (mem_centX.1 hg) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  refine chirality hB (mem_frLam.2 ha) hk ⟨?_, ?_⟩
  · rw [mul_smul]
  · rw [mul_smul, ← xJ_smul_cA hF, centX_comm_smul hg]

theorem centX_not_ell2 {g : J} (hg : g ∈ centX)
    (h : g • pt0 = cA ∨ g • pt0 = cB ∨ g • pt0 = third cA cB) : False := by
  have hF := frame_facts
  have hu := u2_mem_centX hF
  rcases h with h | h | h
  · exact centX_not_cA hg h
  · refine centX_not_cA (mul_mem (inv_mem hu) hg) ?_
    rw [mul_smul, h, inv_smul_eq_iff]
    exact (u2_smul_cA hF).symm
  · refine centX_not_cA (mul_mem hu hg) ?_
    rw [mul_smul, h, u2_smul_m2 hF]

theorem orbit_centX_pt0 : MulAction.orbit centX pt0 = {pt0, pt1, third pt0 pt1} := by
  have hF := frame_facts
  ext p
  simp only [MulAction.mem_orbit_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    rcases inLam_smul (mem_centX.1 hg) (Or.inl rfl : InLam pt0) with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact (centX_not_ell2 hg (Or.inl h)).elim
    · exact (centX_not_ell2 hg (Or.inr (Or.inl h))).elim
    · exact (centX_not_ell2 hg (Or.inr (Or.inr h))).elim
  · rintro (rfl | rfl | rfl)
    · exact ⟨1, one_smul _ _⟩
    · exact ⟨⟨s0, s0_mem_centX hF⟩, fr_s0_pt0 hF⟩
    · exact ⟨⟨s0 * s0, mul_mem (s0_mem_centX hF) (s0_mem_centX hF)⟩, by
        show (s0 * s0) • pt0 = third pt0 pt1
        rw [mul_smul, fr_s0_pt0 hF, fr_s0_pt1 hF]⟩

theorem orbit_cent1_cA : MulAction.orbit cent1 cA = {cA, cB, third cA cB} := by
  have hF := frame_facts
  ext p
  simp only [MulAction.mem_orbit_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨hgC, hgl⟩ := mem_cent1.1 hg
    obtain ⟨f0, f1⟩ := fix_of_mem_lvl_two hgl
    have f2 := cent1_fix_m1 hF hg
    rcases inLam_smul (mem_centX.1 hgC) (Or.inr (Or.inr (Or.inr (Or.inl rfl))) : InLam cA) with
      h | h | h | h | h | h
    · exact absurd (smul_left_cancel g (h.trans f0.symm)) hF.disj_A.1
    · exact absurd (smul_left_cancel g (h.trans f1.symm)) hF.disj_A.2.1
    · exact absurd (smul_left_cancel g (h.trans f2.symm)) hF.disj_A.2.2
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (rfl | rfl | rfl)
    · exact ⟨1, one_smul _ _⟩
    · exact ⟨⟨u2, u2_mem_cent1 hF⟩, u2_smul_cA hF⟩
    · exact ⟨⟨u2 * u2, mul_mem (u2_mem_cent1 hF) (u2_mem_cent1 hF)⟩, by
        show (u2 * u2) • cA = third cA cB
        rw [mul_smul, u2_smul_cA hF, u2_smul_cB hF]⟩

theorem card_orbit_centX : Nat.card (MulAction.orbit centX pt0) = 3 := by
  have hF := frame_facts
  rw [Nat.card_coe_set_eq, orbit_centX_pt0]
  exact Set.ncard_eq_three.2 ⟨pt0, pt1, third pt0 pt1, pt0_ne_pt1, (third_ne_fst hF.nc_01).symm,
    (third_ne_snd hF.nc_01).symm, rfl⟩

theorem card_orbit_cent1 : Nat.card (MulAction.orbit cent1 cA) = 3 := by
  have hF := frame_facts
  rw [Nat.card_coe_set_eq, orbit_cent1_cA]
  exact Set.ncard_eq_three.2 ⟨cA, cB, third cA cB, fst_ne_snd hF.nc_AB,
    (third_ne_fst hF.nc_AB).symm, (third_ne_snd hF.nc_AB).symm, rfl⟩

theorem card_centX : Nat.card centX = 9 * Nat.card stab4 := by
  have hF := frame_facts
  rw [card_centX_of_orbit hF card_orbit_centX, card_cent1_of_orbit hF card_orbit_cent1]
  ring

theorem card_stab4_le : Nat.card stab4 ≤ 4245696 := by
  have hB := bfs_facts
  haveI : Finite J := finite_J
  have h := CFSG.Perm.card_eq_orbit_mul (lvl 2) stab4 ((cA, cB) : Fin 306936 × Fin 306936)
    (fun _ hg => (mem_stab4.1 hg).1)
    (fun _ hl => by rw [Prod.smul_mk, (mem_stab4.1 hl).2.1, (mem_stab4.1 hl).2.2])
    (fun _ hg hfix => mem_stab4.2 ⟨hg, (Prod.ext_iff.1 hfix).1, (Prod.ext_iff.1 hfix).2⟩)
  rw [card_lvl_two] at h
  have h2 := Nat.mul_le_mul_right (Nat.card stab4) (orbit_card_ge hB)
  omega

end Main

section Letters


theorem leaf_closure_of_six_some {X : Type} [Group X] (ε : Fin 6 → X) (hε : SatisfiesG23Words ε)
    (hne : ∃ i, ε i ≠ 1) :
    LeafType 3 ↥(Subgroup.closure (Set.range ε)) ∧ IsSimpleGroup ↥(Subgroup.closure (Set.range ε)) ∧
      (∃ a b : ↥(Subgroup.closure (Set.range ε)), a * b ≠ b * a) ∧
      Nat.card ↥(Subgroup.closure (Set.range ε)) = 4245696 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_adjointG2_of_six ε hε hne
  exact leafType_three_of_equiv_adjointG2 e

end Letters

section Shape


theorem shapeRkAt_xJ : ShapeRkAt 3 (LeafType 3) (fun _ _ => True) xJ := by
  haveI : Finite ↥J := finite_J
  have hF := frame_facts
  obtain ⟨hleaf, hsimp, hnab, hcard⟩ := leaf_closure_of_six_some epsJ hF.eps_rel hF.eps_ne
  have hLS : Subgroup.closure (Set.range epsJ) ≤ stab4 := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨h0, h1, hA, hB⟩ := hF.eps_fix i
    exact mem_stab4.2 ⟨mem_lvl_two_of_fix h0 h1, hA, hB⟩
  have hS : Nat.card stab4 = 4245696 :=
    le_antisymm card_stab4_le (hcard ▸ Subgroup.card_le_of_le hLS)
  have hC : Nat.card centX = Nat.card (Subgroup.closure (Set.range epsJ)) * 3 ^ 2 := by
    rw [card_centX, hS, hcard]
    norm_num
  refine shapeRkAt_of_simple_pindex Nat.prime_three
    (fun _ _ _ _ e h => LeafType.of_equiv e h) (fun _ _ _ _ _ h => h)
    (Subgroup.closure (Set.range epsJ)) (hLS.trans stab4_le_centX) hsimp hnab (k := 2) ?_ hC ?_
    hleaf trivial
  · rw [hcard]
    norm_num
  · rw [hC, hcard]
    decide

theorem isConj_rep4_xJ : IsConj (wordElt [2]) xJ := by
  have hF := frame_facts
  rw [isConj_iff]
  exact ⟨wordElt frG1, by rw [hF.conj, mul_inv_cancel_right]⟩

theorem shapeRkAt_fi24Rep3_four :
    ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (fi24Rep3 4) := by
  haveI : Finite ↥J := finite_J
  obtain ⟨c, hc⟩ := isConj_iff.1 isConj_rep4_xJ
  have h := ShapeRkAt.of_equiv Nat.prime_three (fun _ _ _ _ e h => LeafType.of_equiv e h)
    (fun _ _ _ _ _ h => h) (MulAut.conj c⁻¹) shapeRkAt_xJ
  have hk : (MulAut.conj c⁻¹) xJ = fi24Rep3 4 := by
    rw [← hc, MulAut.conj_apply]
    show c⁻¹ * (c * wordElt [2] * c⁻¹) * c⁻¹⁻¹ = wordElt [2]
    group
  rw [hk] at h
  exact h

end Shape

end CFSG.HardMathSupport.Dickson.I271.TabFi24
