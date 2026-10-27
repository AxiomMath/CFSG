module

public import CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Certificates.Kernel.Misc.PermClosSound
import all CFSG.Certificates.Kernel.Spor.OrdSound

public section

namespace CFSG.KC.CosetLat

open CFSG.KC.Ord CFSG.KS.Ord
open CFSG.KC.Misc.Clos (ClosEnc)

@[expose] def matCode (p d w : ℕ) (A : Matrix (Fin d) (Fin d) (ZMod p)) : ℕ :=
  ∑ i : Fin d, ∑ j : Fin d, (A i j).val * 2 ^ (w * (d * i.val + j.val))

noncomputable def entL {p d : ℕ} (A : Matrix (Fin d) (Fin d) (ZMod p)) (t : ℕ) : ℕ :=
  if h : t < d * d then
    (A ⟨t / d, (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero fun h0 => by simp [h0] at h)).2 h⟩
      ⟨t % d, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by simp [h0] at h)⟩).val
  else 0

theorem entL_idx {p d : ℕ} (A : Matrix (Fin d) (Fin d) (ZMod p)) (i j : Fin d) :
    entL A (d * i.val + j.val) = (A i j).val := by
  have hlt := idx_lt i.isLt j.isLt
  obtain ⟨e1, e2⟩ := dm_eq (d := d) (i := i.val) j.isLt
  unfold entL
  rw [dif_pos hlt]
  have key : ∀ a b : Fin d, a = i → b = j → (A a b).val = (A i j).val := by
    rintro _ _ rfl rfl
    rfl
  exact key _ _ (Fin.ext e1) (Fin.ext e2)

private theorem matCode_eq_pk {p d : ℕ} (w : ℕ) (A : Matrix (Fin d) (Fin d) (ZMod p)) :
    matCode p d w A = pk w (d * d) (entL A) := by
  rw [pk_rows, matCode, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [entL_idx]

theorem entL_lt {p d : ℕ} [NeZero p] (A : Matrix (Fin d) (Fin d) (ZMod p)) (t : ℕ) :
    entL A t < p := by
  unfold entL
  split
  · exact ZMod.val_lt _
  · exact Nat.pos_of_ne_zero (NeZero.ne p)

theorem ordMat_matCode {p d w : ℕ} [NeZero p] (hp : p ≤ 2 ^ w)
    (A : Matrix (Fin d) (Fin d) (ZMod p)) :
    Canon p d w (matCode p d w A) ∧ ordMat p d w (d * w) (matCode p d w A) = A := by
  rw [matCode_eq_pk]
  have hg : ∀ t < d * d, entL A t < p := fun t _ => entL_lt A t
  refine ⟨canon_pk hg hp, ?_⟩
  funext i j
  rw [ordMat_pk (fun t ht => Nat.lt_of_lt_of_le (hg t ht) hp), entL_idx, ZMod.natCast_zmod_val]

theorem canon_eq_of_ordMat {p d w : ℕ} (hw : 0 < w) {A B : ℕ} (hA : Canon p d w A)
    (hB : Canon p d w B) (h : ordMat p d w (d * w) A = ordMat p d w (d * w) B) : A = B := by
  rw [pk_lane hw hA.1, pk_lane hw hB.1]
  refine pk_congr fun t ht => ?_
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at ht)
  have hi : t / d < d := (Nat.div_lt_iff_lt_mul hd).2 ht
  have hj : t % d < d := Nat.mod_lt _ hd
  have e := congrFun (congrFun h ⟨t / d, hi⟩) ⟨t % d, hj⟩
  have et : d * w * (t / d) + w * (t % d) = w * t := by
    rw [Nat.mul_comm d w, Nat.mul_assoc, ← Nat.mul_add, Nat.div_add_mod]
  simp only [ordMat] at e
  rw [et] at e
  have ha := hA.2 t ht
  have hb := hB.2 t ht
  unfold lane at ha hb ⊢
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at e
  exact e

theorem matCode_enc {p w S d T L H CM RM ONE LV HV : ℕ} [NeZero p]
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) :
    ClosEnc (fun g : Matrix.GeneralLinearGroup (Fin d) (ZMod p) => matCode p d w g)
      (mulR p w S d T L H CM RM) ONE := by
  obtain ⟨-, hS, hw, -, hT, -⟩ := consts_facts hc
  have hp : p ≤ 2 ^ w :=
    (Nat.le_mul_of_pos_right p (Nat.two_pow_pos T)).trans
      (hT.trans (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le w 1)))
  have hone := one_sound hc
  subst hS
  refine ⟨?_, fun a b => ?_, fun a b hab => ?_⟩
  · obtain ⟨h1, h2⟩ := ordMat_matCode hp ((1 : Matrix.GeneralLinearGroup (Fin d) (ZMod p)) :
      Matrix (Fin d) (Fin d) (ZMod p))
    refine canon_eq_of_ordMat hw h1 hone.1 ?_
    rw [h2, hone.2, Units.val_one]
  · obtain ⟨ha1, -⟩ := ordMat_matCode hp (a : Matrix (Fin d) (Fin d) (ZMod p))
    obtain ⟨hb1, -⟩ := ordMat_matCode hp (b : Matrix (Fin d) (Fin d) (ZMod p))
    obtain ⟨h1, h2⟩ := ordMat_matCode hp ((a * b : Matrix.GeneralLinearGroup (Fin d) (ZMod p)) :
      Matrix (Fin d) (Fin d) (ZMod p))
    obtain ⟨m1, m2⟩ := mulR_sound hc ha1 hb1
    refine canon_eq_of_ordMat hw h1 m1 ?_
    rw [h2, m2, (ordMat_matCode hp _).2, (ordMat_matCode hp _).2, Units.val_mul]
  · apply Units.ext
    rw [← (ordMat_matCode (w := w) hp (a : Matrix (Fin d) (Fin d) (ZMod p))).2,
      ← (ordMat_matCode (w := w) hp (b : Matrix (Fin d) (Fin d) (ZMod p))).2]
    exact congrArg _ hab

end CFSG.KC.CosetLat

end
