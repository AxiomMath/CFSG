module

public import CFSG.LocalAnalysis.OddStandard.ONanB2CM
public import Certificates.Certificate6150

public section

namespace CFSG.OddStandard.ONanRec.CM

open Subgroup

@[expose] noncomputable def aM : M480 :=
  ⟨wordPerm aW, mem_M480_wordPerm lettersOK_cert lt12_aW⟩

@[expose] noncomputable def bM : M480 :=
  ⟨wordPerm bW, mem_M480_wordPerm lettersOK_cert lt12_bW⟩

@[expose] noncomputable def cM : M480 :=
  ⟨wordPerm cW, mem_M480_wordPerm lettersOK_cert lt12_cW⟩

@[expose] noncomputable def g2M : M480 :=
  ⟨wordPerm g2W, mem_M480_wordPerm lettersOK_cert lt12_g2W⟩

@[simp] theorem coe_aM : (aM : Equiv.Perm (Fin 480)) =
    wordPerm aW := rfl
@[simp] theorem coe_bM : (bM : Equiv.Perm (Fin 480)) =
    wordPerm bW := rfl
@[simp] theorem coe_cM : (cM : Equiv.Perm (Fin 480)) =
    wordPerm cW := rfl
@[simp] theorem coe_g2M : (g2M : Equiv.Perm (Fin 480)) =
    wordPerm g2W := rfl

theorem g2M_eq : g2M = gM * fM * yM ^ 3 := by
  apply Subtype.ext
  simp only [coe_g2M, Subgroup.coe_mul, SubgroupClass.coe_pow, coe_gM, coe_fM, coe_yM]
  rw [g2W, wordPerm_append, wordPerm_append, wordPerm_wpow]
  rfl

structure MirrorFacts : Prop where
  y_sq : yM * yM = aM
  comm1 : yM * (r1M * r2M * r2M) * yM⁻¹ * (r1M * r2M * r2M)⁻¹ = r1M
  comm2 : yM * (r1M * r2M) * yM⁻¹ * (r1M * r2M)⁻¹ = r2M
  y_z : yM * zM = zM * yM
  y_d : yM * dM = dM * yM
  x5_pow : (yM * bM * cM) ^ 5 = 1
  x5_ne : yM * bM * cM ≠ 1
  g_z : gM⁻¹ * zM * gM = zM ^ 3
  g_d : gM⁻¹ * dM * gM = zM * dM

theorem mirrorFacts_cert :
    MirrorFacts := by
  have F := Certificates.certificate6150.1
  exact ⟨Subtype.ext F.y_sq, Subtype.ext F.comm1, Subtype.ext F.comm2, Subtype.ext F.y_z,
    Subtype.ext F.y_d, Subtype.ext F.x5_pow, fun he => F.x5_ne (congrArg Subtype.val he),
    Subtype.ext F.g_z, Subtype.ext F.g_d⟩

theorem lift_gen2_relsM :
    ∀ r ∈ relsM, FreeGroup.lift gen2Perm r = 1 :=
  Certificates.certificate6150.2.1

theorem gen2Perm_eq (i : Fin 6) :
    gen2Perm i = if i = 5 then (g2M : Equiv.Perm (Fin 480)) else genPerm i := by
  unfold gen2Perm
  split_ifs with h5
  · subst h5
    rfl
  · have e2 : substG2 (2 * i.val) = [2 * i.val] := by
      unfold substG2
      have : i.val ≠ 5 := fun h' => h5 (Fin.ext h')
      split_ifs <;> first | omega | rfl
    rw [e2]
    simp only [wordPerm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rfl

@[expose] noncomputable def evalM (u t : M480) (w : List ℕ) :
    M480 :=
  (w.map fun k => if k = 1 then r1M else if k = 2 then r2M else if k = 3 then u else t).prod

theorem coe_evalM (u t : M480) (w : List ℕ) :
    ((evalM u t w : M480) : Equiv.Perm (Fin 480)) = evalP u t w := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    simp only [evalM, evalP, List.map_cons, List.prod_cons, Subgroup.coe_mul] at ih ⊢
    rw [ih]
    split_ifs <;> rfl

theorem coe_pow_eq_one_iff {x : M480} {n : ℕ} :
    (x : Equiv.Perm (Fin 480)) ^ n = 1 ↔ x ^ n = 1 := by
  rw [← SubgroupClass.coe_pow, OneMemClass.coe_eq_one]

theorem mirror_chain {l : ℕ}
    (hl : l < 2) (m : M480) (h1 : m * m = 1) (h2 : m ≠ 1) (hz : m * zM = zM * m)
    (hu : m * (yM * fM ^ l) * m = (yM * fM ^ l)⁻¹) :
    (l = 0 ∧ ∃ k < 4, m * (yM * fM ^ l) ^ k = cM ∨ m * (yM * fM ^ l) ^ k = dM * cM * dM) ∨
      ∃ w ∈ badWords,
        ((evalM (yM * fM ^ l) m w) ^ 6 = 1 ∧ (evalM (yM * fM ^ l) m w) ^ 2 ≠ 1 ∧
          (evalM (yM * fM ^ l) m w) ^ 3 ≠ 1) ∨
        ((evalM (yM * fM ^ l) m w) ^ 8 = 1 ∧ (evalM (yM * fM ^ l) m w) ^ 4 ≠ 1) := by
  have key := Certificates.certificate6150.2.2 l hl m.val m.2 (congrArg Subtype.val h1)
    (fun he => h2 (Subtype.ext he)) (congrArg Subtype.val hz) (congrArg Subtype.val hu)
  rcases key with ⟨hl0, k, hk, hc | hc⟩ | ⟨w, hw, h68⟩
  · exact Or.inl ⟨hl0, k, hk, Or.inl (Subtype.ext hc)⟩
  · exact Or.inl ⟨hl0, k, hk, Or.inr (Subtype.ext hc)⟩
  · refine Or.inr ⟨w, hw, ?_⟩
    have e : evalP (yP * fP ^ l) m.val w = (evalM (yM * fM ^ l) m w : Equiv.Perm (Fin 480)) :=
      (coe_evalM (yM * fM ^ l) m w).symm
    rw [e] at h68
    simp only [coe_pow_eq_one_iff, ne_eq] at h68
    exact h68

end CFSG.OddStandard.ONanRec.CM
