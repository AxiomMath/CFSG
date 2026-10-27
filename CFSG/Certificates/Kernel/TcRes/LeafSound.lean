module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Certificates.Kernel.TcRes.Kit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.KC.TcRes

open CFSG.TcRes.TK CFSG.KC.TcRes.Lane

theorem leaf_walk {W T M : ℕ} {ok : ℕ → Bool} : ∀ n p rest,
    Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
      (fun _ ih p rest => CFSG.TcRes.TK.andB (CFSG.TcRes.TK.orB (Nat.ble T p) (ok (Nat.land rest M)))
        (ih (Nat.succ p) (Nat.shiftRight rest W))) n p rest = true →
    ∀ i < n, p + i < T → ok (Nat.land (Nat.shiftRight rest (W * i)) M) = true := by
  intro n
  induction n with
  | zero => intro _ _ _ i hi; omega
  | succ n ih =>
    intro p rest h i hi hpi
    change CFSG.TcRes.TK.andB (CFSG.TcRes.TK.orB (Nat.ble T p) (ok (Nat.land rest M)))
      (Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
        (fun _ ih p rest => CFSG.TcRes.TK.andB (CFSG.TcRes.TK.orB (Nat.ble T p) (ok (Nat.land rest M)))
          (ih (Nat.succ p) (Nat.shiftRight rest W))) n (Nat.succ p) (Nat.shiftRight rest W)) =
      true at h
    rw [andB_eq_true] at h
    rcases i with _ | i
    · have h1 := h.1
      rw [orB_eq_true, ble_eq_true] at h1
      rcases h1 with h1 | h1
      · omega
      · simpa using h1
    · have := ih (Nat.succ p) (Nat.shiftRight rest W) h.2 i (by omega) (by omega)
      rw [nshr, nshr, ← Nat.shiftRight_add, show W + W * i = W * (i + 1) by ring] at this
      exact this

theorem pl5_of_leaf {RC BS LF : ℕ → ℕ} {ADJ PW : ℕ}
    (hleaf : ∀ L < 101, pleaf5 RC BS LF ADJ PW L = true) {p : ℕ} (hp : p < 1612) :
    pl5OK RC BS ADJ PW (prec5 LF p) = true := by
  have h := leaf_walk (W := 448) (T := 1612) (M := M448) (ok := pl5OK RC BS ADJ PW) 16 _ _
    (hleaf (p / 16) (by omega)) (p % 16) (Nat.mod_lt _ (by norm_num)) (by
      change p / 16 * 16 + p % 16 < 1612
      omega)
  have e1 : Nat.shiftRight p 4 = p / 16 := by rw [nshr, Nat.shiftRight_eq_div_pow]
  have e2 : Nat.land p 15 = p % 16 := by
    rw [nland]
    exact Nat.and_two_pow_sub_one_eq_mod p 4
  change pl5OK RC BS ADJ PW (Nat.land (Nat.shiftRight (LF (Nat.shiftRight p 4))
    (Nat.mul (Nat.land p 15) 448)) M448) = true
  rw [e1, e2, nmul, mul_comm]
  exact h

theorem pl_of_leaf {RC LF : ℕ → ℕ} {ADJ PW NEG START : ℕ}
    (hleaf : ∀ L < 117, pleaf RC LF ADJ PW NEG START L = true) {p : ℕ}
    (hp : p < fld START 16 75) (hp' : p < 1872) :
    plOK RC ADJ PW NEG (prec LF p) = true := by
  have hl := hleaf (p / 16) (by omega)
  rw [pleaf, strictB_eq] at hl
  have h := leaf_walk (W := 547) (T := fld START 16 75) (M := M547) (ok := plOK RC ADJ PW NEG)
    16 _ _ hl (p % 16) (Nat.mod_lt _ (by norm_num)) (by
      change p / 16 * 16 + p % 16 < fld START 16 75
      omega)
  have e1 : Nat.shiftRight p 4 = p / 16 := by rw [nshr, Nat.shiftRight_eq_div_pow]
  have e2 : Nat.land p 15 = p % 16 := by
    rw [nland]
    exact Nat.and_two_pow_sub_one_eq_mod p 4
  change plOK RC ADJ PW NEG (Nat.land (Nat.shiftRight (LF (Nat.shiftRight p 4))
    (Nat.mul (Nat.land p 15) 547)) M547) = true
  rw [e1, e2, nmul, mul_comm]
  exact h

end CFSG.KC.TcRes

end
