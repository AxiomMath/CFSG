module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10XDef

public section

namespace CFSG.OddStandard.SmallF3.FritzII

variable {G : Type} [Group G] {t x1 x2 : G}

theorem fzxElt_add (ht : t ^ 2 = 1) (h1 : x1 ^ 4 = 1) (h2 : x2 ^ 4 = 1)
    (htx1 : t * x1 = x1 * t) (htx2 : t * x2 = x2 * t) (h12 : x1 * x2 = x2 * x1)
    (v w : FzXW) :
    fzxElt t x1 x2 (v + w) = fzxElt t x1 x2 v * fzxElt t x1 x2 w := by
  have e0 : t ^ (v.1 + w.1).val = t ^ v.1.val * t ^ w.1.val := by
    rw [ZMod.val_add, ← pow_eq_pow_mod _ ht, pow_add]
  have e1 : x1 ^ (v.2.1 + w.2.1).val = x1 ^ v.2.1.val * x1 ^ w.2.1.val := by
    rw [ZMod.val_add, ← pow_eq_pow_mod _ h1, pow_add]
  have e2 : x2 ^ (v.2.2 + w.2.2).val = x2 ^ v.2.2.val * x2 ^ w.2.2.val := by
    rw [ZMod.val_add, ← pow_eq_pow_mod _ h2, pow_add]
  have kB1 : x2 ^ v.2.2.val * t ^ w.1.val = t ^ w.1.val * x2 ^ v.2.2.val :=
    (Commute.pow_pow (show Commute t x2 from htx2) w.1.val v.2.2.val).eq.symm
  have kB2 : x1 ^ v.2.1.val * t ^ w.1.val = t ^ w.1.val * x1 ^ v.2.1.val :=
    (Commute.pow_pow (show Commute t x1 from htx1) w.1.val v.2.1.val).eq.symm
  have kQ : x2 ^ v.2.2.val * x1 ^ w.2.1.val = x1 ^ w.2.1.val * x2 ^ v.2.2.val :=
    (Commute.pow_pow (show Commute x1 x2 from h12) w.2.1.val v.2.2.val).eq.symm
  simp only [fzxElt, Prod.fst_add, Prod.snd_add, e0, e1, e2]
  generalize t ^ v.1.val = A at *
  generalize t ^ w.1.val = B at *
  generalize x1 ^ v.2.1.val = P at *
  generalize x1 ^ w.2.1.val = Q at *
  generalize x2 ^ v.2.2.val = R at *
  generalize x2 ^ w.2.2.val = S at *
  calc A * B * (P * Q) * (R * S) = A * B * P * Q * R * S := by simp only [mul_assoc]
    _ = A * B * P * (Q * R) * S := by simp only [mul_assoc]
    _ = A * B * P * (R * Q) * S := by rw [kQ]
    _ = A * P * R * (B * Q * S) := by
        have h1 : P * (R * (B * (Q * S))) = B * (P * (R * (Q * S))) := by
          calc P * (R * (B * (Q * S))) = P * ((R * B) * (Q * S)) := by simp only [mul_assoc]
            _ = P * ((B * R) * (Q * S)) := by rw [kB1]
            _ = (P * B) * (R * (Q * S)) := by simp only [mul_assoc]
            _ = (B * P) * (R * (Q * S)) := by rw [kB2]
            _ = B * (P * (R * (Q * S))) := by simp only [mul_assoc]
        calc A * B * P * (R * Q) * S = A * (B * (P * (R * (Q * S)))) := by simp only [mul_assoc]
          _ = A * (P * (R * (B * (Q * S)))) := by rw [h1]
          _ = A * P * R * (B * Q * S) := by simp only [mul_assoc]

end CFSG.OddStandard.SmallF3.FritzII
