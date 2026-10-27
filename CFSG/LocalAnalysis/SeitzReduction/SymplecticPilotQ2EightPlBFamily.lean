module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightPlBModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightPlDAbstract

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix QuadraticMap CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Kinds

theorem plB_two_le_three : (2 : ℕ) ≤ 3 := by norm_num

@[expose] def PlBBad0 (J : Finset (Fin (3 + 1 + 1 - 1))) : Prop :=
  PEMShort J ∧ (⟨0, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∈ J

@[expose] def PlBBad1 (J : Finset (Fin (3 + 1 + 1 - 1))) : Prop :=
  PEMShort J ∧ (⟨1, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∈ J

theorem plB_short_iff {J : Finset (Fin (3 + 1 + 1 - 1))} :
    PEMShort J ↔ (⟨3, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∈ J := by
  constructor
  · rintro ⟨j, hj, hj3⟩
    have hj' : j = ⟨3, by omega⟩ := Fin.ext (by have := j.isLt; simp at hj3 ⊢; omega)
    exact hj' ▸ hj
  · intro h
    exact ⟨_, h, by simp⟩

theorem plB_not_mem_peSuppM {J : Finset (Fin (3 + 1 + 1 - 1))} {x : Fin (3 + 1 + 1 - 1)}
    (h : ∀ j ∈ J, x.val ≠ j.val ∧ (j.val + 1 < 3 + 1 → x.val ≠ j.val + 1)) :
    x ∉ peSuppM J := by
  intro hx
  obtain ⟨j, hj, hj'⟩ := peP_mem_peSuppM_iff.1 hx
  have := h j hj
  omega

theorem plB_val_lt_of_not_short {J : Finset (Fin (3 + 1 + 1 - 1))} (h : ¬ PEMShort J)
    {j : Fin (3 + 1 + 1 - 1)} (hj : j ∈ J) : j.val ≤ 2 := by
  by_contra hc
  exact h ⟨j, hj, by simp; omega⟩

theorem plB_val_of_bad0 {J : Finset (Fin (3 + 1 + 1 - 1))} (hJ : J.card ≤ 2) (h : PlBBad0 J)
    {j : Fin (3 + 1 + 1 - 1)} (hj : j ∈ J) : j.val = 0 ∨ j.val = 3 := by
  obtain ⟨hs, h0⟩ := h
  have h3 := plB_short_iff.1 hs
  have hne : (⟨0, by omega⟩ : Fin (3 + 1 + 1 - 1)) ≠ ⟨3, by omega⟩ := by simp
  rcases pe_eq_or_eq_of_card_le_two hJ h0 h3 hne hj with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem plB_val_of_bad1 {J : Finset (Fin (3 + 1 + 1 - 1))} (hJ : J.card ≤ 2) (h : PlBBad1 J)
    {j : Fin (3 + 1 + 1 - 1)} (hj : j ∈ J) : j.val = 1 ∨ j.val = 3 := by
  obtain ⟨hs, h1⟩ := h
  have h3 := plB_short_iff.1 hs
  have hne : (⟨1, by omega⟩ : Fin (3 + 1 + 1 - 1)) ≠ ⟨3, by omega⟩ := by simp
  rcases pe_eq_or_eq_of_card_le_two hJ h1 h3 hne hj with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem plB_val_of_not_zero_one {J : Finset (Fin (3 + 1 + 1 - 1))}
    (h0 : (⟨0, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∉ J)
    (h1 : (⟨1, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∉ J) {j : Fin (3 + 1 + 1 - 1)} (hj : j ∈ J) :
    2 ≤ j.val := by
  by_contra hc
  rcases Nat.lt_or_ge j.val 1 with h | h
  · exact h0 (by rwa [show j = ⟨0, by omega⟩ from Fin.ext (by simp; omega)] at hj)
  · exact h1 (by rwa [show j = ⟨1, by omega⟩ from Fin.ext (by simp; omega)] at hj)

theorem plB_not_zero_of_star {J : Finset (Fin (3 + 1 + 1 - 1))} (h0 : ¬ PlBBad0 J)
    (hs : PEMShort J) : (⟨0, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∉ J := fun h => h0 ⟨hs, h⟩

theorem plB_not_one_of_star {J : Finset (Fin (3 + 1 + 1 - 1))} (h1 : ¬ PlBBad1 J)
    (hs : PEMShort J) : (⟨1, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∉ J := fun h => h1 ⟨hs, h⟩

end Kinds

section Off

variable {K : Type} [Field K] {J : Finset (Fin (3 + 1 + 1 - 1))}

theorem plB_peOffM_vec (hs : ¬ PEMShort J) : PEOffM J (kOmMVec K (3 + 1)) :=
  ⟨fun a _ => by simp [kOmMVec], fun h => absurd h hs⟩

theorem plB_peOffM_pdPP {m : Fin (3 + 1)} (hm : (m : Fin (3 + 1 + 1 - 1)) ∉ peSuppM J) :
    PEOffM J (pdPP (K := K) m) := by
  refine ⟨fun a ha => ?_, fun _ => by simp [pdPP]⟩
  have h1 : a ≠ m := fun h => hm (h ▸ ha)
  simp [pdPP, h1]

theorem plB_peOffM_pePU {m : Fin (3 + 1)} (hm : (m : Fin (3 + 1 + 1 - 1)) ∉ peSuppM J)
    (hs : ¬ PEMShort J) : PEOffM J (pePU K m) := by
  refine ⟨fun a ha => ?_, fun h => absurd h hs⟩
  have h1 : a ≠ m := fun h => hm (h ▸ ha)
  simp [pePU, pdPP, kOmMVec, h1]

theorem plB_peOffM_W {m : Fin (3 + 1)} (hm : (m : Fin (3 + 1 + 1 - 1)) ∉ peSuppM J)
    (hl : ((Fin.last 3 : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1)) ∉ peSuppM J) (hs : ¬ PEMShort J) :
    PEOffM J (plBW K m) := by
  refine ⟨fun a ha => ?_, fun h => absurd h hs⟩
  have h1 : a ≠ m := fun h => hm (h ▸ ha)
  have h2 : a ≠ 3 := fun h => hl (by
    rw [show ((Fin.last 3 : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1)) = 3 from rfl, ← h]
    exact ha)
  simp [plBW, pdPP, h1, h2]

end Off

section Indices

theorem plB_two_ne_last : (⟨2, by omega⟩ : Fin (3 + 1)) ≠ Fin.last 3 := by decide

theorem plB_zero_ne_last : (⟨0, by omega⟩ : Fin (3 + 1)) ≠ Fin.last 3 := by decide

theorem plB_one_ne_last : (⟨1, by omega⟩ : Fin (3 + 1)) ≠ Fin.last 3 := by decide

theorem plB_two_ne_one : (⟨2, by omega⟩ : Fin (3 + 1)) ≠ ⟨1, by omega⟩ := by decide

theorem plB_zero_ne_one : (⟨0, by omega⟩ : Fin (3 + 1)) ≠ ⟨1, by omega⟩ := by decide

end Indices

section Data

variable {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) (hn : 4 ≤ 3 + 1 + 1)

@[expose] noncomputable def plBE2 : StatedOmega (StatedQuadMinus (3 + 1 + 1) K 1 1) :=
  plBSieg hK hn plB_two_ne_last plB_two_ne_one plB_one_ne_last

@[expose] noncomputable def plBE0 : StatedOmega (StatedQuadMinus (3 + 1 + 1) K 1 1) :=
  plBSieg hK hn plB_zero_ne_last plB_zero_ne_one plB_one_ne_last

@[expose] noncomputable def plBG2 : StatedOmega (StatedQuadPlus (3 + 1) K) :=
  (plBSieg_mem_range hK hn plB_two_ne_last plB_two_ne_one plB_one_ne_last (by norm_num)).choose

theorem pcOPExt_plBG2 : pcOPExt (K := K) (Fin.last 3) (plBG2 hK hn) = plBE2 hK hn :=
  (plBSieg_mem_range hK hn plB_two_ne_last plB_two_ne_one plB_one_ne_last
    (by norm_num)).choose_spec

@[expose] noncomputable def plBG0 : StatedOmega (StatedQuadPlus (3 + 1) K) :=
  (plBSieg_mem_range hK hn plB_zero_ne_last plB_zero_ne_one plB_one_ne_last (by norm_num)).choose

theorem pcOPExt_plBG0 : pcOPExt (K := K) (Fin.last 3) (plBG0 hK hn) = plBE0 hK hn :=
  (plBSieg_mem_range hK hn plB_zero_ne_last plB_zero_ne_one plB_one_ne_last
    (by norm_num)).choose_spec

theorem plB_place_lev (J : {J : Finset (Fin (3 + 1 + 1 - 1)) // J.card ≤ 2})
    (hs : ¬ PEMShort J.1)
    (x : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J) :
    (pcOPExt (K := K) (Fin.last 3) 1)⁻¹ * peRhoM hn (q2Omega_irreducible_one_one hK) x *
        pcOPExt (K := K) (Fin.last 3) 1 ∈
      (q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK).range := by
  rw [map_one, inv_one, one_mul, mul_one, range_q2OmMIota,
    mem_fixedSubgroup_kOmMBetaC_iff K (by omega) (q2Omega_irreducible_one_one hK), peRhoM_mulVec]
  exact spinAction_leviM_of_peOff _ x (plB_peOffM_vec hs)

theorem plB_place_star (J : {J : Finset (Fin (3 + 1 + 1 - 1)) // J.card ≤ 2})
    (h0 : (⟨0, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∉ J.1)
    (h1 : (⟨1, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∉ J.1)
    (x : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J) :
    (q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK
        (plBT01 hK (by norm_num)))⁻¹ * peRhoM hn (q2Omega_irreducible_one_one hK) x *
        q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK
          (plBT01 hK (by norm_num)) ∈ (pcOPExt (K := K) ⟨0, by omega⟩).range := by
  have hz : ((⟨0, by omega⟩ : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1)) ∉ peSuppM J.1 :=
    plB_not_mem_peSuppM fun j hj => by
      have := plB_val_of_not_zero_one h0 h1 hj
      exact ⟨by simp; omega, fun _ => by simp⟩
  have ho : ((⟨1, by omega⟩ : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1)) ∉ peSuppM J.1 :=
    plB_not_mem_peSuppM fun j hj => by
      have := plB_val_of_not_zero_one h0 h1 hj
      exact ⟨by simp; omega, fun _ => by simp; omega⟩
  refine peP_conj_mem_range_of_peOff hK (by norm_num) hn _ x ?_ ?_
  · rw [q2OmMIota_plBT01_mulVec_a]
    exact peOffM_inl_add_pdPP hz ho
  · rw [q2OmMIota_plBT01_mulVec_b]
    exact peOffM_inr_add_pdPP hz ho

theorem plB_place_star2 (J : {J : Finset (Fin (3 + 1 + 1 - 1)) // J.card ≤ 2})
    (hJ : ∀ j ∈ J.1, 3 ≤ j.val)
    (x : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J) :
    (q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK
        (plBT01 hK (by norm_num) * plBT21 hK (by norm_num)))⁻¹ *
        peRhoM hn (q2Omega_irreducible_one_one hK) x *
        q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK
          (plBT01 hK (by norm_num) * plBT21 hK (by norm_num)) ∈
      (pcOPExt (K := K) ⟨2, by omega⟩).range := by
  have hz : ((⟨2, by omega⟩ : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1)) ∉ peSuppM J.1 :=
    plB_not_mem_peSuppM fun j hj => by
      have := hJ j hj
      exact ⟨by simp; omega, fun _ => by simp; omega⟩
  have ho : ((⟨1, by omega⟩ : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1)) ∉ peSuppM J.1 :=
    plB_not_mem_peSuppM fun j hj => by
      have := hJ j hj
      exact ⟨by simp; omega, fun _ => by simp; omega⟩
  refine peP_conj_mem_range_of_peOff hK (by norm_num) hn _ x ?_ ?_
  · rw [q2OmMIota_plBT0121_mulVec_a]
    exact peOffM_inl_add_pdPP hz ho
  · rw [q2OmMIota_plBT0121_mulVec_b]
    exact peOffM_inr_add_pdPP hz ho

theorem plB_place_bad0 (J : {J : Finset (Fin (3 + 1 + 1 - 1)) // J.card ≤ 2})
    (hJ : PlBBad0 J.1)
    (x : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J) :
    (pcOPExt (K := K) (Fin.last 3) (plBG2 hK hn))⁻¹ * peRhoM hn (q2Omega_irreducible_one_one hK) x *
        pcOPExt (K := K) (Fin.last 3) (plBG2 hK hn) ∈
      (q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK).range := by
  rw [pcOPExt_plBG2, range_q2OmMIota]
  refine plB_conj_mem_fixed hK (by norm_num) _ _ ?_
  rw [plBE2, plBSieg_mulVec_vec, peRhoM_mulVec]
  refine spinAction_leviM_of_peOff _ x (plB_peOffM_pdPP (plB_not_mem_peSuppM fun j hj => ?_))
  have := plB_val_of_bad0 J.2 hJ hj
  exact ⟨by simp; omega, fun _ => by simp; omega⟩

theorem plB_place_bad1 (J : {J : Finset (Fin (3 + 1 + 1 - 1)) // J.card ≤ 2})
    (hJ : PlBBad1 J.1)
    (x : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J) :
    (pcOPExt (K := K) (Fin.last 3) (plBG0 hK hn))⁻¹ * peRhoM hn (q2Omega_irreducible_one_one hK) x *
        pcOPExt (K := K) (Fin.last 3) (plBG0 hK hn) ∈
      (q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK).range := by
  rw [pcOPExt_plBG0, range_q2OmMIota]
  refine plB_conj_mem_fixed hK (by norm_num) _ _ ?_
  rw [plBE0, plBSieg_mulVec_vec, peRhoM_mulVec]
  refine spinAction_leviM_of_peOff _ x (plB_peOffM_pdPP (plB_not_mem_peSuppM fun j hj => ?_))
  have := plB_val_of_bad1 J.2 hJ hj
  exact ⟨by simp; omega, fun _ => by simp⟩

end Data

section Family

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = 2) (hn : 4 ≤ 3 + 1 + 1) {e : L ≃* StatedSp (3 + 1) K}
  (Φ : ∀ k : Fin (3 + 1), StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
    centralizerPerfectCore (modelToG e (nsTorusSp K k)))

open Classical in
@[expose] noncomputable def plBFamily :
    ∀ J, (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J →* G := fun J =>
  if h0 : PlBBad0 J.1 then
    plDConjL (fun k => pcOPExt (K := K) k) (pePPhi Φ)
      (q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK)
      (L.subtype.comp e.symm.toMonoidHom) (Fin.last 3) (plBG2 hK hn)
      (q2OmMIota_injective (r := 3 + 1) _ _ hK)
      ((peRhoM hn (q2Omega_irreducible_one_one hK)).comp
        ((minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J).subtype)
      (fun x => plB_place_bad0 hK hn J h0 x)
  else if h1 : PlBBad1 J.1 then
    plDConjL (fun k => pcOPExt (K := K) k) (pePPhi Φ)
      (q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK)
      (L.subtype.comp e.symm.toMonoidHom) (Fin.last 3) (plBG0 hK hn)
      (q2OmMIota_injective (r := 3 + 1) _ _ hK)
      ((peRhoM hn (q2Omega_irreducible_one_one hK)).comp
        ((minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J).subtype)
      (fun x => plB_place_bad1 hK hn J h1 x)
  else if hs : PEMShort J.1 then
    peTrans (fun k => pcOPExt (K := K) k) (pePPhi Φ)
      (q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK)
      (L.subtype.comp e.symm.toMonoidHom) ⟨0, by omega⟩ (pcOPExt_injective (K := K) _)
      (plBT01 hK (by norm_num))
      ((peRhoM hn (q2Omega_irreducible_one_one hK)).comp
        ((minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J).subtype)
      (fun x => plB_place_star hK hn J (plB_not_zero_of_star h0 hs) (plB_not_one_of_star h1 hs) x)
  else
    plDConjL (fun k => pcOPExt (K := K) k) (pePPhi Φ)
      (q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK)
      (L.subtype.comp e.symm.toMonoidHom) (Fin.last 3) 1
      (q2OmMIota_injective (r := 3 + 1) _ _ hK)
      ((peRhoM hn (q2Omega_irreducible_one_one hK)).comp
        ((minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J).subtype)
      (fun x => plB_place_lev hK hn J hs x)

theorem plBFamily_lev (J : {J : Finset (Fin (3 + 1 + 1 - 1)) // J.card ≤ 2})
    (hs : ¬ PEMShort J.1)
    (x : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J)
    {h : StatedSp (3 + 1) K}
    (hh : q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK h =
      peRhoM hn (q2Omega_irreducible_one_one hK) x) :
    plBFamily hK hn Φ J x = ((e.symm h : L) : G) := by
  have h0 : ¬ PlBBad0 J.1 := fun h => hs h.1
  have h1 : ¬ PlBBad1 J.1 := fun h => hs h.1
  simp only [plBFamily, dite_eq_right h0, dite_eq_right h1, dite_eq_right hs]
  exact (plDConjL_apply _ _ x (h := h) (by rw [map_one, inv_one, one_mul, mul_one]; exact hh)).trans
    (plDConjL_one_value (Φ := pePPhi Φ) (ε := L.subtype.comp e.symm.toMonoidHom) h)

theorem plBFamily_star (J : {J : Finset (Fin (3 + 1 + 1 - 1)) // J.card ≤ 2})
    (h0 : (⟨0, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∉ J.1)
    (h1 : (⟨1, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∉ J.1) (hs : PEMShort J.1)
    (x : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J)
    {g : StatedOmega (StatedQuadPlus (3 + 1) K)}
    (hg : pcOPExt (K := K) ⟨0, by omega⟩ g =
      (q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK
        (plBT01 hK (by norm_num)))⁻¹ * peRhoM hn (q2Omega_irreducible_one_one hK) x *
        q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK
          (plBT01 hK (by norm_num))) :
    plBFamily hK hn Φ J x = ((e.symm (plBT01 hK (by norm_num)) : L) : G) *
      pePPhi Φ ⟨0, by omega⟩ g * (((e.symm (plBT01 hK (by norm_num)) : L) : G))⁻¹ := by
  have h0' : ¬ PlBBad0 J.1 := fun h => h0 h.2
  have h1' : ¬ PlBBad1 J.1 := fun h => h1 h.2
  simp only [plBFamily, dite_eq_right h0', dite_eq_right h1', dite_eq_left hs]
  exact peTrans_apply _ _ x hg

theorem plBFamily_bad0 (J : {J : Finset (Fin (3 + 1 + 1 - 1)) // J.card ≤ 2})
    (h0 : PlBBad0 J.1)
    (x : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J)
    {h : StatedSp (3 + 1) K}
    (hh : q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK h =
      (plBE2 hK hn)⁻¹ * peRhoM hn (q2Omega_irreducible_one_one hK) x * plBE2 hK hn) :
    plBFamily hK hn Φ J x = pePPhi Φ (Fin.last 3) (plBG2 hK hn) * ((e.symm h : L) : G) *
      (pePPhi Φ (Fin.last 3) (plBG2 hK hn))⁻¹ := by
  simp only [plBFamily, dite_eq_left h0]
  exact plDConjL_apply _ _ x (by rw [pcOPExt_plBG2]; exact hh)

theorem plBFamily_bad1 (J : {J : Finset (Fin (3 + 1 + 1 - 1)) // J.card ≤ 2})
    (h0 : ¬ PlBBad0 J.1) (h1 : PlBBad1 J.1)
    (x : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J)
    {h : StatedSp (3 + 1) K}
    (hh : q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK h =
      (plBE0 hK hn)⁻¹ * peRhoM hn (q2Omega_irreducible_one_one hK) x * plBE0 hK hn) :
    plBFamily hK hn Φ J x = pePPhi Φ (Fin.last 3) (plBG0 hK hn) * ((e.symm h : L) : G) *
      (pePPhi Φ (Fin.last 3) (plBG0 hK hn))⁻¹ := by
  simp only [plBFamily, dite_eq_right h0, dite_eq_left h1]
  exact plDConjL_apply _ _ x (by rw [pcOPExt_plBG0]; exact hh)

end Family

section Agree

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = 2) (hn : 4 ≤ 3 + 1 + 1) {e : L ≃* StatedSp (3 + 1) K} {t : G}
  {Φ : ∀ k : Fin (3 + 1), StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
    centralizerPerfectCore (modelToG e (nsTorusSp K k))}

theorem plB_exists_iota_of_lev (I : {J : Finset (Fin (3 + 1 + 1 - 1)) // J.card ≤ 2})
    (hs : ¬ PEMShort I.1)
    (x : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam I) :
    ∃ h, q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK h =
      peRhoM hn (q2Omega_irreducible_one_one hK) x := by
  obtain ⟨h, hh⟩ := plB_place_lev hK hn I hs x
  rw [map_one, inv_one, one_mul, mul_one] at hh
  exact ⟨h, hh⟩

theorem plB_mem_range_ext3 (I : {J : Finset (Fin (3 + 1 + 1 - 1)) // J.card ≤ 2})
    (hs : ¬ PEMShort I.1)
    (h3 : ((Fin.last 3 : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1)) ∉ peSuppM I.1)
    (x : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam I) :
    peRhoM hn (q2Omega_irreducible_one_one hK) x ∈ (pcOPExt (K := K) (Fin.last 3)).range := by
  refine (mem_pcOPExt_range_iff (Fin.last 3) hK (by norm_num) _).2 ⟨?_, ?_⟩
  · rw [peRhoM_mulVec]
    exact spinAction_leviM_of_peOff _ x (peOffM_pdPA h3 hs)
  · rw [peRhoM_mulVec]
    exact spinAction_leviM_of_peOff _ x (peOffM_pdPB h3 hs)

variable (hΦ : ∀ k, IsNsOmPlusParam hK plB_two_le_three le_rfl e t k (Φ k))
  (hal : NsOmPlusAligned e Φ)
include hΦ hal

theorem plB_agree_comm {m j : Fin (3 + 1)} (hm : m ≠ Fin.last 3) (hmj : m ≠ j)
    (hj : j ≠ Fin.last 3) {g' : StatedOmega (StatedQuadPlus (3 + 1) K)}
    (hg' : pcOPExt (K := K) (Fin.last 3) g' = plBSieg hK hn hm hmj hj)
    (I : {J : Finset (Fin (3 + 1 + 1 - 1)) // J.card ≤ 2})
    (x : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam I)
    (hs : ¬ PEMShort I.1) (hmS : (m : Fin (3 + 1 + 1 - 1)) ∉ peSuppM I.1)
    (h3 : ((Fin.last 3 : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1)) ∉ peSuppM I.1)
    {h h' : StatedSp (3 + 1) K}
    (hh : q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK h =
      peRhoM hn (q2Omega_irreducible_one_one hK) x)
    (hh' : q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK h' =
      (plBSieg hK hn hm hmj hj)⁻¹ * peRhoM hn (q2Omega_irreducible_one_one hK) x *
        plBSieg hK hn hm hmj hj) :
    pePPhi Φ (Fin.last 3) g' * ((e.symm h' : L) : G) * (pePPhi Φ (Fin.last 3) g')⁻¹ =
      ((e.symm h : L) : G) := by
  obtain ⟨z', hz'⟩ := plB_mem_range_ext3 hK hn I hs h3 x
  have hcomm : peRhoM hn (q2Omega_irreducible_one_one hK) x * plBSieg hK hn hm hmj hj =
      plBSieg hK hn hm hmj hj * peRhoM hn (q2Omega_irreducible_one_one hK) x := by
    refine plBSieg_commute hK hn hm hmj hj _ ?_ ?_
    · rw [peRhoM_mulVec]
      exact spinAction_leviM_of_peOff _ x (plB_peOffM_pePU hmS hs)
    · rw [peRhoM_mulVec]
      exact spinAction_leviM_of_peOff _ x (plB_peOffM_W hmS h3 hs)
  refine plDConjL_value_comm (ext := fun k => pcOPExt (K := K) k) (peAligned_plus hal)
    (peNormal_plus hK plB_two_le_three le_rfl hΦ) (q2OmMIota_injective (r := 3 + 1) _ _ hK)
    (k := Fin.last 3) (z' := z') (h₀ := h) (hz'.trans hh.symm) ?_ ?_
  · change pcOPExt (Fin.last 3) g' * pcOPExt (Fin.last 3) z' =
      pcOPExt (Fin.last 3) z' * pcOPExt (Fin.last 3) g'
    rw [hg', hz']
    exact hcomm.symm
  · change q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK h' =
      (pcOPExt (Fin.last 3) g')⁻¹ * pcOPExt (Fin.last 3) z' * pcOPExt (Fin.last 3) g'
    rw [hg', hz']
    exact hh'

theorem plB_agree_trans {m j : Fin (3 + 1)} (hm : m ≠ Fin.last 3) (hmj : m ≠ j)
    (hj : j ≠ Fin.last 3) {g' : StatedOmega (StatedQuadPlus (3 + 1) K)}
    (hg' : pcOPExt (K := K) (Fin.last 3) g' = plBSieg hK hn hm hmj hj) (i : Fin (3 + 1))
    {y : StatedSp (3 + 1) K}
    (hy : q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y ∈
      (pcOPExt (K := K) (Fin.last 3)).range)
    (hA : (((plBSieg hK hn hm hmj hj : StatedOmega (StatedQuadMinus (3 + 1 + 1) K 1 1)) :
      GL (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
        ((((q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y :
          StatedOmega (StatedQuadMinus (3 + 1 + 1) K 1 1)) :
            GL (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) :
              Matrix (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPA K i) =
      (((q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y :
        StatedOmega (StatedQuadMinus (3 + 1 + 1) K 1 1)) :
          GL (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) :
            Matrix (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPA K i)
    (hB : (((plBSieg hK hn hm hmj hj : StatedOmega (StatedQuadMinus (3 + 1 + 1) K 1 1)) :
      GL (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
        ((((q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y :
          StatedOmega (StatedQuadMinus (3 + 1 + 1) K 1 1)) :
            GL (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) :
              Matrix (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPB K i) =
      (((q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y :
        StatedOmega (StatedQuadMinus (3 + 1 + 1) K 1 1)) :
          GL (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) :
            Matrix (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ pdPB K i)
    {z : StatedOmega (StatedQuadMinus (3 + 1 + 1) K 1 1)} {h' : StatedSp (3 + 1) K}
    {m_z : StatedOmega (StatedQuadPlus (3 + 1) K)}
    (hh' : q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK h' =
      (plBSieg hK hn hm hmj hj)⁻¹ * z * plBSieg hK hn hm hmj hj)
    (hz : pcOPExt (K := K) i m_z =
      (q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y)⁻¹ * z *
        q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y) :
    pePPhi Φ (Fin.last 3) g' * ((e.symm h' : L) : G) * (pePPhi Φ (Fin.last 3) g')⁻¹ =
      ((e.symm y : L) : G) * pePPhi Φ i m_z * (((e.symm y : L) : G))⁻¹ := by
  obtain ⟨m_g, hm_g⟩ := plB_conj_mem_range_of_fix hK (by norm_num) i _ _ hA hB
  refine plDConjL_value_trans (ext := fun k => pcOPExt (K := K) k) (peAligned_plus hal)
    (peNormal_plus hK plB_two_le_three le_rfl hΦ) (k := Fin.last 3) (i := i) hy (g' := g')
    (m_g := m_g) ?_ ?_ hz
  · change pcOPExt i m_g =
      (q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y)⁻¹ *
        pcOPExt (Fin.last 3) g' *
          q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y
    rw [hg']
    exact hm_g
  · change q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK h' =
      (pcOPExt (Fin.last 3) g')⁻¹ * z * pcOPExt (Fin.last 3) g'
    rw [hg']
    exact hh'

end Agree

end CFSG.SeitzReduction.SymplecticPilot
