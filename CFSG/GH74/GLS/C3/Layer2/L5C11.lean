module

public import CFSG.GH74.GLS.C3.Layer2.L5C10
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import CFSG.GH74.GLS.C3.Layer2.L5C10
public import CFSG.GH74.GLS.C3.Layer2.L5C11Inputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C11Inputs
public import Certificates.Certificate5045
public import Certificates.Certificate5051
public import Certificates.Certificate5052
public import Certificates.Certificate5053
public import Certificates.Certificate5070

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

theorem mem_Fgrp5_iff {p : Amb 5} : p ∈ Fgrp 5 ↔ F5b p = true := by
  rw [F5b, decide_eq_true_iff]
  rfl

theorem gTw_mul_self : gTw * gTw = 1 :=
  Certificates.certificate5053.1

theorem gTw_inv : gTw⁻¹ = gTw :=
  Certificates.certificate5053.2.1

theorem gTw_conj_conj
    (t : Amb 5) : gTw * (gTw * t * gTw⁻¹) * gTw⁻¹ = t := by
  have h1 : gTw * gTw = 1 := gTw_mul_self
  have h2 : gTw⁻¹ * gTw⁻¹ = 1 := by rw [gTw_inv, h1]
  calc gTw * (gTw * t * gTw⁻¹) * gTw⁻¹ = (gTw * gTw) * t * (gTw⁻¹ * gTw⁻¹) := by group
    _ = t := by rw [h1, h2]; simp

theorem gTw_conj_F5_chk :
    allAmb5.all (fun p => imp (F5b p) (F5b (gTw * p * gTw⁻¹))) = true :=
  Certificates.certificate5053.2.2.1

theorem gTw_conj_T5_chk :
    allAmb5.all (fun p => decide (T5b p = T5b (gTw * p * gTw⁻¹))) = true :=
  Certificates.certificate5053.2.2.2.1

theorem gTw_conj_F5
    {p : Amb 5} (hp : p ∈ Fgrp 5) : gTw * p * gTw⁻¹ ∈ Fgrp 5 := by
  have h := gTw_conj_F5_chk
  simp only [List.all_eq_true, imp_eq_true] at h
  exact mem_Fgrp5_iff.2 (h p (mem_allAmb5 p) (mem_Fgrp5_iff.1 hp))

theorem gTw_conj_T5_iff
    {p : Amb 5} : gTw * p * gTw⁻¹ ∈ T5 ↔ p ∈ T5 := by
  have h := gTw_conj_T5_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  rw [mem_T5_iff_b, mem_T5_iff_b, ← h p (mem_allAmb5 p)]

theorem gTw_x0 : gTw * x0 5 * gTw⁻¹ = x0 5 :=
  Certificates.certificate5053.2.2.2.2.1

theorem gTw_fst (p : Amb 5) : (gTw * p * gTw⁻¹).1 = p.1 := by
  simp [gTw]

theorem gTw_el16_chk : (List.finRange 16).all
    (fun i => decide (gTw * el16 (twG i) * gTw⁻¹ = el16 i)) = true :=
  Certificates.certificate5053.2.2.2.2.2.2.1

theorem gTw_el16
    (i : Fin 16) : gTw * el16 (twG i) * gTw⁻¹ = el16 i := by
  have h := gTw_el16_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h i trivial

theorem twG_twG_chk :
    (List.finRange 16).all (fun i => decide (twG (twG i) = i)) = true :=
  Certificates.certificate5053.2.2.2.2.2.2.2.1

theorem twG_twG (i : Fin 16) : twG (twG i) = i := by
  have h := twG_twG_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h i trivial

theorem gTw_conj_Rml_chk :
    Rml.all (fun p => decide (gTw * p * gTw⁻¹ ∈ Rml)) = true :=
  Certificates.certificate5053.2.2.2.2.2.2.2.2.1

theorem gTw_conj_iff
    {M : Subgroup (Amb 5)} (hM : ∀ p ∈ M, gTw * p * gTw⁻¹ ∈ M) (p : Amb 5) :
    gTw * p * gTw⁻¹ ∈ M ↔ p ∈ M := by
  refine ⟨fun hp => ?_, hM p⟩
  have := hM _ hp
  rwa [gTw_conj_conj] at this

theorem gTw_conj_Rm_iff
    (p : Amb 5) : gTw * p * gTw⁻¹ ∈ Rm ↔ p ∈ Rm :=
  gTw_conj_iff (fun p hp => by
    have h := gTw_conj_Rml_chk
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    exact mem_Rm.2 (h p (mem_Rm.1 hp))) p

@[expose] def conjF5 : ↥(Fgrp 5) ≃* ↥(Fgrp 5) where
  toFun t := ⟨gTw * (t : Amb 5) * gTw⁻¹, gTw_conj_F5 t.2⟩
  invFun t := ⟨gTw * (t : Amb 5) * gTw⁻¹, gTw_conj_F5 t.2⟩
  left_inv t := Subtype.ext (gTw_conj_conj _)
  right_inv t := Subtype.ext (gTw_conj_conj _)
  map_mul' s t := Subtype.ext (by
    show gTw * ((s : Amb 5) * (t : Amb 5)) * gTw⁻¹ =
      (gTw * (s : Amb 5) * gTw⁻¹) * (gTw * (t : Amb 5) * gTw⁻¹)
    group)

section Twist

variable {h : IsAConfig 5 x K T Q S a}

@[expose] def Coord5.twist (c : Coord5 h) : Coord5 h where
  ι := c.ι.trans conjF5
  hι1 := by
    show gTw * (((c.ι (xC x) : Fgrp 5) : Amb 5)) * gTw⁻¹ = x0 5
    rw [c.hι1, gTw_x0]
  hιQ := fun g => by
    show (gTw * ((c.ι g : Fgrp 5) : Amb 5) * gTw⁻¹).1 = 1 ↔ (g : G) ∈ Q
    rw [gTw_fst]
    exact c.hιQ g
  hιT := fun g => by
    show (g : G) ∈ T ↔ gTw * ((c.ι g : Fgrp 5) : Amb 5) * gTw⁻¹ ∈ T5
    rw [gTw_conj_T5_iff]
    exact c.hιT g

variable (c : Coord5 h)

theorem Coord5.rco_twist
    (g : G) : c.twist.rco g = gTw * c.rco g * gTw⁻¹ := by
  by_cases hg : g ∈ centralizer ({x} : Set G)
  · rw [Coord5.rco_of_mem c.twist hg, Coord5.rco_of_mem c hg]
    rfl
  · have h1 : c.twist.rco g = 1 := by simp [Coord5.rco, hg]
    have h2 : c.rco g = 1 := by simp [Coord5.rco, hg]
    rw [h1, h2]
    group

theorem Coord5.lift_twist_of
    {M : Subgroup (Amb 5)} (hM : ∀ p, gTw * p * gTw⁻¹ ∈ M ↔ p ∈ M) :
    c.twist.lift M = c.lift M := by
  ext g
  rw [Coord5.mem_lift_rco, Coord5.mem_lift_rco, Coord5.rco_twist, hM]

theorem Coord5.lift_twist_Rm :
    c.twist.lift Rm = c.lift Rm :=
  Coord5.lift_twist_of c gTw_conj_Rm_iff

theorem Coord5.eq_liftEl
    {g : G} (hg : g ∈ c.lift Rm) {i : Fin 16} (hrc : c.rco g = el16 i) :
    g = c.liftEl i :=
  Coord5.rco_inj c (Coord5.lift_mem_cent hg) (c.liftEl_mem_C i) (hrc.trans (c.rco_liftEl i).symm)

theorem Coord5.liftEl_twist
    (i : Fin 16) : c.twist.liftEl i = c.liftEl (twG i) := by
  symm
  have hR : c.liftEl (twG i) ∈ c.twist.lift Rm := by
    rw [Coord5.lift_twist_Rm]; exact c.liftEl_mem _
  exact Coord5.eq_liftEl c.twist hR (by
    rw [Coord5.rco_twist, c.rco_liftEl, gTw_el16])

theorem Coord5.planeOf_twist
    (V : Subgroup G) :
    c.twist.planeOf V = (c.planeOf V).image twG := by
  ext i
  rw [Coord5.mem_planeOf, Finset.mem_image, Coord5.liftEl_twist]
  constructor
  · intro hi
    exact ⟨twG i, Coord5.mem_planeOf.2 hi, twG_twG i⟩
  · rintro ⟨j, hj, rfl⟩
    rw [twG_twG]
    exact Coord5.mem_planeOf.1 hj

theorem fam1G_image_tw :
    fam1G.image (fun V => V.image twG) = fam0G :=
  Certificates.certificate5053.2.2.2.2.2.2.2.2.2.2.2.1

end Twist

section Reduce

variable {h : IsAConfig 5 x K T Q S a}

theorem exists_nbar0
    (hF : C1Facts) (c : Coord5 h) (hG4 : pRank 2 G ≤ 4)
    (hP : ∀ V ∈ FamQ (c.lift Rm) Q, V ⊓ (T ⊓ K) = ⊥) (hncard : (FamQ (c.lift Rm) Q).ncard = 4) :
    ∃ c' : Coord5 h, c'.lift Rm = c.lift Rm ∧ ∃ F : Finset (Finset (Fin 16)), F.card = 4 ∧
      F = fam0G ∧ (∀ V, V ∈ F ↔ ∃ W ∈ FamQ (c'.lift Rm) Q, c'.planeOf W = V) ∧
      (∀ n : ↥(normalizer ((c'.lift Rm : Subgroup G) : Set G)), PplG.image (c'.rhoG n) = PplG) ∧
      (∀ A ∈ n24L, ∃ n : ↥(normalizer ((c'.lift Rm : Subgroup G) : Set G)), c'.rhoG n = A) := by
  obtain ⟨F, hFcard, hFfam, hFmem, hFP, hF0, hF1⟩ := exists_nbar hF c hG4 hP hncard
  rcases hFfam with hf | hf
  · exact ⟨c, rfl, F, hFcard, hf, hFmem, hFP, hF0 hf⟩
  ·
    have hTR : c.twist.lift Rm = c.lift Rm := Coord5.lift_twist_Rm c
    have hP' : ∀ V ∈ FamQ (c.twist.lift Rm) Q, V ⊓ (T ⊓ K) = ⊥ := by
      rw [hTR]; exact hP
    have hn' : (FamQ (c.twist.lift Rm) Q).ncard = 4 := by rw [hTR]; exact hncard
    obtain ⟨F', hF'card, hF'fam, hF'mem, hF'P, hF'0, hF'1⟩ :=
      exists_nbar hF c.twist hG4 hP' hn'
    have hFF' : F' = F.image (fun V => V.image twG) := by
      ext V
      rw [hF'mem, Finset.mem_image]
      constructor
      · rintro ⟨W, hW, rfl⟩
        refine ⟨c.planeOf W, (hFmem _).2 ⟨W, ?_, rfl⟩, ?_⟩
        · rwa [hTR] at hW
        · rw [Coord5.planeOf_twist]
      · rintro ⟨U, hU, rfl⟩
        obtain ⟨W, hW, rfl⟩ := (hFmem U).1 hU
        refine ⟨W, ?_, Coord5.planeOf_twist c W⟩
        rwa [hTR]
    have hF'eq : F' = fam0G := by
      rw [hFF', hf, fam1G_image_tw]
    exact ⟨c.twist, hTR, F', hF'card, hF'eq, hF'mem, hF'P, hF'0 hF'eq⟩

end Reduce

end CFSG.GH74.GLS.C3.Layer2.L5
