module

public import CFSG.GH74.GLS.C3.Layer2.L5C0
public import CFSG.GH74.GLS.C3.Layer2.L5C9
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
public import Certificates.Certificate5051
public import Certificates.Certificate5059

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem getD_map_finRange (p : Perm (Fin 16)) (i : Fin 16) :
    ((List.finRange 16).map p).getD i.val 0 = p i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  have : (List.finRange 16)[i.val]? = some i := by
    rw [List.getElem?_eq_getElem (by simp)]
    simp [List.getElem_finRange]
  rw [this]
  rfl

@[expose] def nrm (p : Perm (Fin 16)) : Perm (Fin 16) :=
  let l := (List.finRange 16).map p
  HF.mkPerm fun i => l.getD i.val 0

theorem nrm_eq (p : Perm (Fin 16)) : nrm p = p := by
  unfold nrm
  have hf : (fun i : Fin 16 => ((List.finRange 16).map p).getD i.val 0) = ⇑p := by
    funext i
    exact getD_map_finRange p i
  simp only [hf]
  exact HF.mkPerm_coe p

theorem map_nrm (L : List (Perm (Fin 16))) : L.map nrm = L := by
  rw [List.map_congr_left (g := id) (fun p _ => nrm_eq p), List.map_id]

theorem sh0_R1_not_ge_chk :
    RhatL0.any (fun p => !(decide (p ∈ R1L))) = true :=
  Certificates.certificate5059.1

theorem sh0_R1_not_ge :
    ¬ (RsubP0 ≤ R1subP) := by
  intro hle
  have h := sh0_R1_not_ge_chk
  simp only [List.any_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨p, hp, hpn⟩ := h
  exact hpn (hle hp)

theorem RhatL1_nodup : RhatL1.Nodup :=
  Certificates.certificate5059.2.1

theorem RhatL1_length : RhatL1.length = 16 :=
  Certificates.certificate5059.2.2.1

theorem RsubP1_card :
    Nat.card RsubP1 = 16 := by
  rw [natCard_eq_length RsubP1 RhatL1 RhatL1_nodup (fun p => Iff.rfl)]
  exact RhatL1_length

theorem RhatL1_sq_chk :
    RhatL1.all (fun a => decide (a * a = 1)) = true :=
  Certificates.certificate5059.2.2.2.1

theorem RhatL1_comm_chk :
    RhatL1.all (fun a => RhatL1.all fun b => decide (a * b = b * a)) = true :=
  Certificates.certificate5059.2.2.2.2

theorem RsubP1_le_Sh1 : RsubP1 ≤ Sh1 := fun p hp => by
  have h := RsubP1_le_Sh1_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h p hp

theorem aut1_of_e16
    (hE16 : ∀ B : Subgroup (Perm (Fin 16)), B ≤ Sh1 → Nat.card B = 16 → (∀ b ∈ B, b * b = 1) →
      (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) → B = RsubP1)
    (γ : ↥Sh1 ≃* ↥Sh1) (r : ↥Sh1) (hr : (r : Perm (Fin 16)) ∈ RsubP1) :
    ((γ r : ↥Sh1) : Perm (Fin 16)) ∈ RsubP1 := by
  let f : ↥Sh1 →* Perm (Fin 16) := Sh1.subtype.comp γ.toMonoidHom
  have hfinj : Function.Injective f := fun s t hst => γ.injective (Subtype.ext hst)
  set B : Subgroup (Perm (Fin 16)) := (RsubP1.subgroupOf Sh1).map f with hB
  have hmemB : ∀ b, b ∈ B ↔ ∃ y : ↥Sh1, (y : Perm (Fin 16)) ∈ RsubP1 ∧ f y = b := by
    intro b
    rw [hB, Subgroup.mem_map]
    simp [Subgroup.mem_subgroupOf]
  have hBle : B ≤ Sh1 := by
    intro b hb
    obtain ⟨y, -, rfl⟩ := (hmemB b).1 hb
    exact (γ y).2
  have hsq := RhatL1_sq_chk
  have hcomm := RhatL1_comm_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at hsq hcomm
  have hBcard : Nat.card B = 16 := by
    rw [hB, Subgroup.card_map_of_injective hfinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe RsubP1_le_Sh1).toEquiv, RsubP1_card]
  have hBeq : B = RsubP1 := hE16 B hBle hBcard
    (by
      intro b hb
      obtain ⟨y, hy, rfl⟩ := (hmemB b).1 hb
      rw [← map_mul]
      have h1 : y * y = 1 := Subtype.ext (hsq _ hy)
      rw [h1, map_one])
    (by
      intro b hb b' hb'
      obtain ⟨y, hy, rfl⟩ := (hmemB b).1 hb
      obtain ⟨y', hy', rfl⟩ := (hmemB b').1 hb'
      rw [← map_mul, ← map_mul]
      have h1 : y * y' = y' * y := Subtype.ext (hcomm _ hy _ hy')
      rw [h1])
  have : f r ∈ B := (hmemB _).2 ⟨r, hr, rfl⟩
  rw [hBeq] at this
  exact this

end CFSG.GH74.GLS.C3.Layer2.L5
