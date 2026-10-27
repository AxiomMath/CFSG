module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightPlDModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightPlDAbstract

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix QuadraticMap CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Kinds

@[expose] def PlDMoves (J : Finset (Fin (3 + 2))) : Prop := ∃ j ∈ J, 3 ≤ j.val

@[expose] def PlDBad0 (J : Finset (Fin (3 + 2))) : Prop := PlDMoves J ∧ (0 : Fin (3 + 2)) ∈ J

@[expose] def PlDBad1 (J : Finset (Fin (3 + 2))) : Prop := PlDMoves J ∧ (1 : Fin (3 + 2)) ∈ J

theorem plD_not_mem_peSupp {J : Finset (Fin (3 + 2))} {x : Fin (3 + 2)}
    (h : ∀ j ∈ J, (j.val ≤ 2 → x.val ≠ j.val ∧ x.val ≠ j.val + 1) ∧
      (3 ≤ j.val → x.val ≠ 3 ∧ x.val ≠ 4)) : x ∉ peSupp J := by
  intro hx
  obtain ⟨j, hj, hj'⟩ := pe_mem_peSupp_iff.1 hx
  have := h j hj
  have := j.isLt
  omega

theorem plD_val_le_of_not_moves {J : Finset (Fin (3 + 2))} (h : ¬ PlDMoves J) {j : Fin (3 + 2)}
    (hj : j ∈ J) : j.val ≤ 2 := by
  by_contra hc
  exact h ⟨j, hj, by omega⟩

theorem plD_val_of_bad0 {J : Finset (Fin (3 + 2))} (hJ : J.card ≤ 2) (h : PlDBad0 J)
    {j : Fin (3 + 2)} (hj : j ∈ J) : j.val = 0 ∨ 3 ≤ j.val := by
  obtain ⟨⟨b, hb, hb3⟩, h0⟩ := h
  have hne : (0 : Fin (3 + 2)) ≠ b := Fin.ne_of_val_ne (by simp; omega)
  rcases pe_eq_or_eq_of_card_le_two hJ h0 hb hne hj with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr hb3

theorem plD_val_of_bad1 {J : Finset (Fin (3 + 2))} (hJ : J.card ≤ 2) (h : PlDBad1 J)
    {j : Fin (3 + 2)} (hj : j ∈ J) : j.val = 1 ∨ 3 ≤ j.val := by
  obtain ⟨⟨b, hb, hb3⟩, h1⟩ := h
  have hne : (1 : Fin (3 + 2)) ≠ b := Fin.ne_of_val_ne (by simp; omega)
  rcases pe_eq_or_eq_of_card_le_two hJ h1 hb hne hj with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr hb3

theorem plD_val_of_not_zero_one {J : Finset (Fin (3 + 2))} (h0 : (0 : Fin (3 + 2)) ∉ J)
    (h1 : (1 : Fin (3 + 2)) ∉ J) {j : Fin (3 + 2)} (hj : j ∈ J) : 2 ≤ j.val := by
  by_contra hc
  have hj' : j = 0 ∨ j = 1 := by
    rcases Nat.lt_or_ge j.val 1 with h | h
    · exact Or.inl (Fin.ext (by simp; omega))
    · exact Or.inr (Fin.ext (by simp; omega))
  rcases hj' with rfl | rfl
  · exact h0 hj
  · exact h1 hj

end Kinds

section Off

variable {K : Type} [Field K] {r : ℕ}

theorem plD_peOff_add {S : Finset (Fin (r + 2))} {x y : Fin (r + 2) ⊕ Fin (r + 2) → K}
    (hx : PEOff S x) (hy : PEOff S y) : PEOff S (x + y) := by
  intro a ha
  simp [(hx a ha).1, (hx a ha).2, (hy a ha).1, (hy a ha).2]

theorem plD_peOff_single_inl {S : Finset (Fin (r + 2))} {a : Fin (r + 2)} (ha : a ∉ S) :
    PEOff S (Pi.single (Sum.inl a) (1 : K)) := by
  intro x hx
  have h : x ≠ a := fun h => ha (h ▸ hx)
  simp [h]

theorem plD_peOff_single_inr {S : Finset (Fin (r + 2))} {a : Fin (r + 2)} (ha : a ∉ S) :
    PEOff S (Pi.single (Sum.inr a) (1 : K)) := by
  intro x hx
  have h : x ≠ a := fun h => ha (h ▸ hx)
  simp [h]

theorem plD_peOff_vec {S : Finset (Fin (r + 2))} (h : Fin.last (r + 1) ∉ S) :
    PEOff S (kOmegaVec K (r + 1)) :=
  plD_peOff_add (plD_peOff_single_inl h) (plD_peOff_single_inr h)

theorem plD_peOff_pdMP {S : Finset (Fin (r + 2))} {m : Fin (r + 1)} (h : m.castSucc ∉ S) :
    PEOff S (pdMP (K := K) m) :=
  plD_peOff_add (plD_peOff_single_inl h) (plD_peOff_single_inr h)

theorem plD_peOff_peMU {S : Finset (Fin (r + 2))} {m : Fin (r + 1)} (hm : m.castSucc ∉ S)
    (hN : Fin.last (r + 1) ∉ S) : PEOff S (peMU K m) :=
  plD_peOff_add (plD_peOff_pdMP hm) (plD_peOff_vec hN)

theorem plD_peOff_W {S : Finset (Fin (r + 2))} {m : Fin (r + 1)} (hm : m.castSucc ∉ S)
    (hr : (Fin.last r).castSucc ∉ S) (hN : Fin.last (r + 1) ∉ S) : PEOff S (plDW K m) :=
  plD_peOff_add (plD_peOff_add (plD_peOff_single_inl hm) (plD_peOff_pdMP hr))
    (plD_peOff_single_inl hN)

end Off

section Data

variable {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)

@[expose] noncomputable def plDG' (m : Fin (3 + 1)) (hm : m ≠ Fin.last 3) :
    StatedOmega (StatedQuadMinus (3 + 1) K 1 1) :=
  (plDSieg_mem_range (K := K) (r := 3) (by omega) hm hK le_rfl).choose

theorem pcOMExt_plDG' (m : Fin (3 + 1)) (hm : m ≠ Fin.last 3) :
    pcOMExt (K := K) (Fin.last 3) (plDG' hK m hm) = plDSieg (by omega) hm :=
  (plDSieg_mem_range (K := K) (r := 3) (by omega) hm hK le_rfl).choose_spec

theorem plD_two_ne_last : (2 : Fin (3 + 1)) ≠ Fin.last 3 := by decide

theorem plD_zero_ne_last : (0 : Fin (3 + 1)) ≠ Fin.last 3 := by decide

variable (hn : 3 ≤ 3 + 2)

theorem plD_place_lev (J : {J : Finset (Fin (3 + 2)) // J.card ≤ 2}) (hJ : ¬ PlDMoves J.1)
    (x : (plusDatum (3 + 2) K hn).leviAmalgam J) :
    (pcOMExt (K := K) (Fin.last 3) 1)⁻¹ * peRho hn x * pcOMExt (K := K) (Fin.last 3) 1 ∈
      (q2OmIota (r := 3 + 1) (by omega) hK (by omega)).range := by
  rw [map_one, inv_one, one_mul, mul_one, range_q2OmIota,
    mem_fixedSubgroup_kOmegaBetaC_iff K (by omega), peRho_mulVec]
  refine spinAction_levi_of_peOff hn x (plD_peOff_vec (plD_not_mem_peSupp fun j hj => ?_))
  have := plD_val_le_of_not_moves hJ hj
  have hv : (Fin.last (3 + 1)).val = 4 := rfl
  omega

theorem plD_place_star (J : {J : Finset (Fin (3 + 2)) // J.card ≤ 2})
    (h0 : (0 : Fin (3 + 2)) ∉ J.1) (h1 : (1 : Fin (3 + 2)) ∉ J.1)
    (x : (plusDatum (3 + 2) K hn).leviAmalgam J) :
    (q2OmIota (r := 3 + 1) (by omega) hK (by omega) (plDT01 le_rfl))⁻¹ * peRho hn x *
        q2OmIota (r := 3 + 1) (by omega) hK (by omega) (plDT01 le_rfl) ∈
      (pcOMExt (K := K) ⟨0, by omega⟩).range := by
  have hz : ((⟨0, by omega⟩ : Fin (3 + 1)).castSucc : Fin (3 + 2)) ∉ peSupp J.1 :=
    plD_not_mem_peSupp fun j hj => by
      have := plD_val_of_not_zero_one h0 h1 hj
      have hv : ((⟨0, by omega⟩ : Fin (3 + 1)).castSucc : Fin (3 + 2)).val = 0 := rfl
      omega
  have ho : ((⟨1, by omega⟩ : Fin (3 + 1)).castSucc : Fin (3 + 2)) ∉ peSupp J.1 :=
    plD_not_mem_peSupp fun j hj => by
      have := plD_val_of_not_zero_one h0 h1 hj
      have hv : ((⟨1, by omega⟩ : Fin (3 + 1)).castSucc : Fin (3 + 2)).val = 1 := rfl
      omega
  refine pe_conj_mem_range_of_peOff hK le_rfl hn _ x ?_ ?_
  · rw [q2OmIota_plDT01_mulVec_a]
    exact peOff_inl_add_pdMP hz ho
  · rw [q2OmIota_plDT01_mulVec_b]
    exact peOff_inr_add_pdMP hz ho

theorem plD_place_star2 (J : {J : Finset (Fin (3 + 2)) // J.card ≤ 2})
    (hJ : ∀ j ∈ J.1, 3 ≤ j.val) (x : (plusDatum (3 + 2) K hn).leviAmalgam J) :
    (q2OmIota (r := 3 + 1) (by omega) hK (by omega) (plDT01 le_rfl * plDT21 le_rfl))⁻¹ *
        peRho hn x * q2OmIota (r := 3 + 1) (by omega) hK (by omega)
          (plDT01 le_rfl * plDT21 le_rfl) ∈ (pcOMExt (K := K) ⟨2, by omega⟩).range := by
  have hz : ((⟨2, by omega⟩ : Fin (3 + 1)).castSucc : Fin (3 + 2)) ∉ peSupp J.1 :=
    plD_not_mem_peSupp fun j hj => by
      have := hJ j hj
      have hv : ((⟨2, by omega⟩ : Fin (3 + 1)).castSucc : Fin (3 + 2)).val = 2 := rfl
      omega
  have ho : ((⟨1, by omega⟩ : Fin (3 + 1)).castSucc : Fin (3 + 2)) ∉ peSupp J.1 :=
    plD_not_mem_peSupp fun j hj => by
      have := hJ j hj
      have hv : ((⟨1, by omega⟩ : Fin (3 + 1)).castSucc : Fin (3 + 2)).val = 1 := rfl
      omega
  refine pe_conj_mem_range_of_peOff hK le_rfl hn _ x ?_ ?_
  · rw [q2OmIota_plDT0121_mulVec_a]
    exact peOff_inl_add_pdMP hz ho
  · rw [q2OmIota_plDT0121_mulVec_b]
    exact peOff_inr_add_pdMP hz ho

theorem plD_place_bad0 (J : {J : Finset (Fin (3 + 2)) // J.card ≤ 2}) (hJ : PlDBad0 J.1)
    (x : (plusDatum (3 + 2) K hn).leviAmalgam J) :
    (pcOMExt (K := K) (Fin.last 3) (plDG' hK 2 plD_two_ne_last))⁻¹ * peRho hn x *
        pcOMExt (K := K) (Fin.last 3) (plDG' hK 2 plD_two_ne_last) ∈
      (q2OmIota (r := 3 + 1) (by omega) hK (by omega)).range := by
  rw [pcOMExt_plDG', range_q2OmIota]
  refine plD_conj_mem_fixed (by omega) _ _ ?_
  rw [plDSieg_mulVec_vec, peRho_mulVec]
  refine spinAction_levi_of_peOff hn x (plD_peOff_pdMP (plD_not_mem_peSupp fun j hj => ?_))
  have := plD_val_of_bad0 J.2 hJ hj
  have hv : ((2 : Fin (3 + 1)).castSucc : Fin (3 + 2)).val = 2 := rfl
  omega

theorem plD_place_bad1 (J : {J : Finset (Fin (3 + 2)) // J.card ≤ 2}) (hJ : PlDBad1 J.1)
    (x : (plusDatum (3 + 2) K hn).leviAmalgam J) :
    (pcOMExt (K := K) (Fin.last 3) (plDG' hK 0 plD_zero_ne_last))⁻¹ * peRho hn x *
        pcOMExt (K := K) (Fin.last 3) (plDG' hK 0 plD_zero_ne_last) ∈
      (q2OmIota (r := 3 + 1) (by omega) hK (by omega)).range := by
  rw [pcOMExt_plDG', range_q2OmIota]
  refine plD_conj_mem_fixed (by omega) _ _ ?_
  rw [plDSieg_mulVec_vec, peRho_mulVec]
  refine spinAction_levi_of_peOff hn x (plD_peOff_pdMP (plD_not_mem_peSupp fun j hj => ?_))
  have := plD_val_of_bad1 J.2 hJ hj
  have hv : ((0 : Fin (3 + 1)).castSucc : Fin (3 + 2)).val = 0 := rfl
  omega

end Data

section Family

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = 2) (hn : 3 ≤ 3 + 2) {e : L ≃* StatedSp (3 + 1) K}
  (Φ : ∀ k : Fin (3 + 1), StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
    centralizerPerfectCore (modelToG e (nsTorusSp K k)))

theorem plD_not_zero_of_star {J : Finset (Fin (3 + 2))} (h0 : ¬ PlDBad0 J) (hm : PlDMoves J) :
    (0 : Fin (3 + 2)) ∉ J := fun h => h0 ⟨hm, h⟩

theorem plD_not_one_of_star {J : Finset (Fin (3 + 2))} (h1 : ¬ PlDBad1 J) (hm : PlDMoves J) :
    (1 : Fin (3 + 2)) ∉ J := fun h => h1 ⟨hm, h⟩

open Classical in
@[expose] noncomputable def plDFamily :
    ∀ J, (plusDatum (3 + 2) K hn).leviAmalgam J →* G := fun J =>
  if h0 : PlDBad0 J.1 then
    plDConjL (fun k => pcOMExt (K := K) k) (peMPhi Φ)
      (q2OmIota (r := 3 + 1) (by omega) hK (by omega)) (L.subtype.comp e.symm.toMonoidHom)
      (Fin.last 3) (plDG' hK 2 plD_two_ne_last) (q2OmIota_injective (r := 3 + 1) _ hK _)
      ((peRho hn).comp ((plusDatum (3 + 2) K hn).leviAmalgam J).subtype)
      (fun x => plD_place_bad0 hK hn J h0 x)
  else if h1 : PlDBad1 J.1 then
    plDConjL (fun k => pcOMExt (K := K) k) (peMPhi Φ)
      (q2OmIota (r := 3 + 1) (by omega) hK (by omega)) (L.subtype.comp e.symm.toMonoidHom)
      (Fin.last 3) (plDG' hK 0 plD_zero_ne_last) (q2OmIota_injective (r := 3 + 1) _ hK _)
      ((peRho hn).comp ((plusDatum (3 + 2) K hn).leviAmalgam J).subtype)
      (fun x => plD_place_bad1 hK hn J h1 x)
  else if hm : PlDMoves J.1 then
    peTrans (fun k => pcOMExt (K := K) k) (peMPhi Φ)
      (q2OmIota (r := 3 + 1) (by omega) hK (by omega)) (L.subtype.comp e.symm.toMonoidHom)
      ⟨0, by omega⟩ (pcOMExt_injective _) (plDT01 le_rfl)
      ((peRho hn).comp ((plusDatum (3 + 2) K hn).leviAmalgam J).subtype)
      (fun x => plD_place_star hK hn J (plD_not_zero_of_star h0 hm) (plD_not_one_of_star h1 hm) x)
  else
    plDConjL (fun k => pcOMExt (K := K) k) (peMPhi Φ)
      (q2OmIota (r := 3 + 1) (by omega) hK (by omega)) (L.subtype.comp e.symm.toMonoidHom)
      (Fin.last 3) 1 (q2OmIota_injective (r := 3 + 1) _ hK _)
      ((peRho hn).comp ((plusDatum (3 + 2) K hn).leviAmalgam J).subtype)
      (fun x => plD_place_lev hK hn J hm x)

theorem plDFamily_lev (J : {J : Finset (Fin (3 + 2)) // J.card ≤ 2}) (hm : ¬ PlDMoves J.1)
    (x : (plusDatum (3 + 2) K hn).leviAmalgam J) {h : StatedSp (3 + 1) K}
    (hh : q2OmIota (r := 3 + 1) (by omega) hK (by omega) h = peRho hn x) :
    plDFamily hK hn Φ J x = ((e.symm h : L) : G) := by
  have h0 : ¬ PlDBad0 J.1 := fun h => hm h.1
  have h1 : ¬ PlDBad1 J.1 := fun h => hm h.1
  simp only [plDFamily, dite_eq_right h0, dite_eq_right h1, dite_eq_right hm]
  exact (plDConjL_apply _ _ x (h := h) (by rw [map_one, inv_one, one_mul, mul_one]; exact hh)).trans
    (plDConjL_one_value (Φ := peMPhi Φ) (ε := L.subtype.comp e.symm.toMonoidHom) h)

theorem plDFamily_star (J : {J : Finset (Fin (3 + 2)) // J.card ≤ 2})
    (h0 : (0 : Fin (3 + 2)) ∉ J.1) (h1 : (1 : Fin (3 + 2)) ∉ J.1) (hm : PlDMoves J.1)
    (x : (plusDatum (3 + 2) K hn).leviAmalgam J) {g : StatedOmega (StatedQuadMinus (3 + 1) K 1 1)}
    (hg : pcOMExt (K := K) ⟨0, by omega⟩ g =
      (q2OmIota (r := 3 + 1) (by omega) hK (by omega) (plDT01 le_rfl))⁻¹ * peRho hn x *
        q2OmIota (r := 3 + 1) (by omega) hK (by omega) (plDT01 le_rfl)) :
    plDFamily hK hn Φ J x = ((e.symm (plDT01 le_rfl) : L) : G) * peMPhi Φ ⟨0, by omega⟩ g *
      (((e.symm (plDT01 le_rfl) : L) : G))⁻¹ := by
  have h0' : ¬ PlDBad0 J.1 := fun h => h0 h.2
  have h1' : ¬ PlDBad1 J.1 := fun h => h1 h.2
  simp only [plDFamily, dite_eq_right h0', dite_eq_right h1', dite_eq_left hm]
  exact peTrans_apply _ _ x hg

theorem plDFamily_bad0 (J : {J : Finset (Fin (3 + 2)) // J.card ≤ 2}) (h0 : PlDBad0 J.1)
    (x : (plusDatum (3 + 2) K hn).leviAmalgam J) {h : StatedSp (3 + 1) K}
    (hh : q2OmIota (r := 3 + 1) (by omega) hK (by omega) h =
      (plDSieg (K := K) (r := 3) (by omega) plD_two_ne_last)⁻¹ * peRho hn x *
        plDSieg (by omega) plD_two_ne_last) :
    plDFamily hK hn Φ J x = peMPhi Φ (Fin.last 3) (plDG' hK 2 plD_two_ne_last) *
      ((e.symm h : L) : G) * (peMPhi Φ (Fin.last 3) (plDG' hK 2 plD_two_ne_last))⁻¹ := by
  simp only [plDFamily, dite_eq_left h0]
  exact plDConjL_apply _ _ x (by rw [pcOMExt_plDG']; exact hh)

theorem plDFamily_bad1 (J : {J : Finset (Fin (3 + 2)) // J.card ≤ 2}) (h0 : ¬ PlDBad0 J.1)
    (h1 : PlDBad1 J.1) (x : (plusDatum (3 + 2) K hn).leviAmalgam J) {h : StatedSp (3 + 1) K}
    (hh : q2OmIota (r := 3 + 1) (by omega) hK (by omega) h =
      (plDSieg (K := K) (r := 3) (by omega) plD_zero_ne_last)⁻¹ * peRho hn x *
        plDSieg (by omega) plD_zero_ne_last) :
    plDFamily hK hn Φ J x = peMPhi Φ (Fin.last 3) (plDG' hK 0 plD_zero_ne_last) *
      ((e.symm h : L) : G) * (peMPhi Φ (Fin.last 3) (plDG' hK 0 plD_zero_ne_last))⁻¹ := by
  simp only [plDFamily, dite_eq_right h0, dite_eq_left h1]
  exact plDConjL_apply _ _ x (by rw [pcOMExt_plDG']; exact hh)

end Family

section Agree

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = 2) (hn : 3 ≤ 3 + 2) {e : L ≃* StatedSp (3 + 1) K} {t : G}
  {Φ : ∀ k : Fin (3 + 1), StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
    centralizerPerfectCore (modelToG e (nsTorusSp K k))}

theorem plD_exists_iota_of_lev (I : {J : Finset (Fin (3 + 2)) // J.card ≤ 2})
    (hmI : ¬ PlDMoves I.1) (x : (plusDatum (3 + 2) K hn).leviAmalgam I) :
    ∃ h, q2OmIota (r := 3 + 1) (by omega) hK (by omega) h = peRho hn x := by
  obtain ⟨h, hh⟩ := plD_place_lev hK hn I hmI x
  rw [map_one, inv_one, one_mul, mul_one] at hh
  exact ⟨h, hh⟩

include hK in
theorem plD_mem_range_ext3 (I : {J : Finset (Fin (3 + 2)) // J.card ≤ 2})
    (h3 : (Fin.last 3).castSucc ∉ peSupp I.1) (h4 : Fin.last (3 + 1) ∉ peSupp I.1)
    (x : (plusDatum (3 + 2) K hn).leviAmalgam I) :
    peRho hn x ∈ (pcOMExt (K := K) (Fin.last 3)).range := by
  refine (mem_pcOMExt_range_iff (Fin.last 3) hK le_rfl _).2 ⟨?_, ?_⟩
  · rw [peRho_mulVec]
    exact spinAction_levi_of_peOff hn x (peOff_pdMA h3 h4)
  · rw [peRho_mulVec]
    exact spinAction_levi_of_peOff hn x (peOff_pdMB h3 h4)

variable (hΦ : ∀ k, IsNsOmMinusParam hK le_rfl e t k (Φ k)) (hal : NsOmMinusAligned e Φ)
include hΦ hal

theorem plD_agree_comm {m : Fin (3 + 1)} (hm : m ≠ Fin.last 3)
    (I : {J : Finset (Fin (3 + 2)) // J.card ≤ 2}) (x : (plusDatum (3 + 2) K hn).leviAmalgam I)
    (hmS : m.castSucc ∉ peSupp I.1) (h3 : (Fin.last 3).castSucc ∉ peSupp I.1)
    (h4 : Fin.last (3 + 1) ∉ peSupp I.1) {h h' : StatedSp (3 + 1) K}
    (hh : q2OmIota (r := 3 + 1) (by omega) hK (by omega) h = peRho hn x)
    (hh' : q2OmIota (r := 3 + 1) (by omega) hK (by omega) h' =
      (plDSieg (K := K) (r := 3) (by omega) hm)⁻¹ * peRho hn x * plDSieg (by omega) hm) :
    peMPhi Φ (Fin.last 3) (plDG' hK m hm) * ((e.symm h' : L) : G) *
      (peMPhi Φ (Fin.last 3) (plDG' hK m hm))⁻¹ = ((e.symm h : L) : G) := by
  obtain ⟨z', hz'⟩ := plD_mem_range_ext3 hK hn I h3 h4 x
  have hcomm : peRho hn x * plDSieg (K := K) (r := 3) (by omega) hm =
      plDSieg (by omega) hm * peRho hn x := by
    refine plDSieg_commute (by omega) hm (peRho hn (x : spinGroup (quadPlus (3 + 2) K))) ?_ ?_
    · rw [peRho_mulVec]
      exact spinAction_levi_of_peOff hn x (plD_peOff_peMU hmS h4)
    · rw [peRho_mulVec]
      exact spinAction_levi_of_peOff hn x (plD_peOff_W hmS h3 h4)
  refine plDConjL_value_comm (ext := fun k => pcOMExt (K := K) k) (peAligned_minus hal)
    (peNormal_minus hK le_rfl hΦ) (q2OmIota_injective (r := 3 + 1) _ hK _) (k := Fin.last 3)
    (z' := z') (h₀ := h) (hz'.trans hh.symm) ?_ ?_
  · change pcOMExt (Fin.last 3) (plDG' hK m hm) * pcOMExt (Fin.last 3) z' =
      pcOMExt (Fin.last 3) z' * pcOMExt (Fin.last 3) (plDG' hK m hm)
    rw [pcOMExt_plDG', hz']
    exact hcomm.symm
  · change q2OmIota (r := 3 + 1) (by omega) hK (by omega) h' =
      (pcOMExt (Fin.last 3) (plDG' hK m hm))⁻¹ * pcOMExt (Fin.last 3) z' *
        pcOMExt (Fin.last 3) (plDG' hK m hm)
    rw [pcOMExt_plDG', hz']
    exact hh'

theorem plD_agree_trans {m : Fin (3 + 1)} (hm : m ≠ Fin.last 3) (i : Fin (3 + 1))
    {y : StatedSp (3 + 1) K}
    (hy : q2OmIota (r := 3 + 1) (by omega) hK (by omega) y ∈ (pcOMExt (K := K) (Fin.last 3)).range)
    (hA : (((plDSieg (K := K) (r := 3) (by omega) hm : StatedOmega (StatedQuadPlus (3 + 2) K)) :
      GL (Fin (3 + 2) ⊕ Fin (3 + 2)) K) :
        Matrix (Fin (3 + 2) ⊕ Fin (3 + 2)) (Fin (3 + 2) ⊕ Fin (3 + 2)) K) *ᵥ
        ((((q2OmIota (r := 3 + 1) (by omega) hK (by omega) y :
          StatedOmega (StatedQuadPlus (3 + 2) K)) : GL (Fin (3 + 2) ⊕ Fin (3 + 2)) K) :
            Matrix (Fin (3 + 2) ⊕ Fin (3 + 2)) (Fin (3 + 2) ⊕ Fin (3 + 2)) K) *ᵥ pdMA K i) =
      (((q2OmIota (r := 3 + 1) (by omega) hK (by omega) y :
        StatedOmega (StatedQuadPlus (3 + 2) K)) : GL (Fin (3 + 2) ⊕ Fin (3 + 2)) K) :
          Matrix (Fin (3 + 2) ⊕ Fin (3 + 2)) (Fin (3 + 2) ⊕ Fin (3 + 2)) K) *ᵥ pdMA K i)
    (hB : (((plDSieg (K := K) (r := 3) (by omega) hm : StatedOmega (StatedQuadPlus (3 + 2) K)) :
      GL (Fin (3 + 2) ⊕ Fin (3 + 2)) K) :
        Matrix (Fin (3 + 2) ⊕ Fin (3 + 2)) (Fin (3 + 2) ⊕ Fin (3 + 2)) K) *ᵥ
        ((((q2OmIota (r := 3 + 1) (by omega) hK (by omega) y :
          StatedOmega (StatedQuadPlus (3 + 2) K)) : GL (Fin (3 + 2) ⊕ Fin (3 + 2)) K) :
            Matrix (Fin (3 + 2) ⊕ Fin (3 + 2)) (Fin (3 + 2) ⊕ Fin (3 + 2)) K) *ᵥ pdMB K i) =
      (((q2OmIota (r := 3 + 1) (by omega) hK (by omega) y :
        StatedOmega (StatedQuadPlus (3 + 2) K)) : GL (Fin (3 + 2) ⊕ Fin (3 + 2)) K) :
          Matrix (Fin (3 + 2) ⊕ Fin (3 + 2)) (Fin (3 + 2) ⊕ Fin (3 + 2)) K) *ᵥ pdMB K i)
    {z : StatedOmega (StatedQuadPlus (3 + 2) K)} {h' : StatedSp (3 + 1) K}
    {m_z : StatedOmega (StatedQuadMinus (3 + 1) K 1 1)}
    (hh' : q2OmIota (r := 3 + 1) (by omega) hK (by omega) h' =
      (plDSieg (K := K) (r := 3) (by omega) hm)⁻¹ * z * plDSieg (by omega) hm)
    (hz : pcOMExt (K := K) i m_z = (q2OmIota (r := 3 + 1) (by omega) hK (by omega) y)⁻¹ * z *
      q2OmIota (r := 3 + 1) (by omega) hK (by omega) y) :
    peMPhi Φ (Fin.last 3) (plDG' hK m hm) * ((e.symm h' : L) : G) *
      (peMPhi Φ (Fin.last 3) (plDG' hK m hm))⁻¹ =
      ((e.symm y : L) : G) * peMPhi Φ i m_z * (((e.symm y : L) : G))⁻¹ := by
  obtain ⟨m_g, hm_g⟩ := plD_conj_mem_range_of_fix hK le_rfl i _ _ hA hB
  refine plDConjL_value_trans (ext := fun k => pcOMExt (K := K) k) (peAligned_minus hal)
    (peNormal_minus hK le_rfl hΦ) (k := Fin.last 3) (i := i) hy (g' := plDG' hK m hm)
    (m_g := m_g) ?_ ?_ hz
  · change pcOMExt i m_g = (q2OmIota (r := 3 + 1) (by omega) hK (by omega) y)⁻¹ *
      pcOMExt (Fin.last 3) (plDG' hK m hm) * q2OmIota (r := 3 + 1) (by omega) hK (by omega) y
    rw [pcOMExt_plDG']
    exact hm_g
  · change q2OmIota (r := 3 + 1) (by omega) hK (by omega) h' =
      (pcOMExt (Fin.last 3) (plDG' hK m hm))⁻¹ * z * pcOMExt (Fin.last 3) (plDG' hK m hm)
    rw [pcOMExt_plDG']
    exact hh'

end Agree

end CFSG.SeitzReduction.SymplecticPilot
