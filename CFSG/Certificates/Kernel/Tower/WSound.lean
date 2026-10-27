module

public import Certificates.Data.Kernel.Tower.W
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerModels

public section

namespace Certificates.KernelTower

open CFSG.OddStandard.AltStdSmall4 CFSG.OddStandard.AltStdSmall4.Tower

theorem allB_eq_true {n : Nat} {p : Nat → Bool} : allB n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => exact ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | succ n ih =>
    have e : allB (n + 1) p = (p n && allB n p) := rfl
    rw [e, Bool.and_eq_true, ih]
    refine ⟨fun h k hk => ?_, fun h => ⟨h n (Nat.lt_succ_self n), fun k hk => h k (by omega)⟩⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact h.2 k hk
    · exact h.1

theorem lane_eq (T w i : Nat) : lane T w (2 ^ w - 1) i = T / 2 ^ (w * i) % 2 ^ w := by
  change (T >>> (w * i)) &&& (2 ^ w - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem lane_le (T w m i : Nat) : lane T w m i ≤ m := Nat.and_le_right

theorem shr6 (a : Nat) : Nat.shiftRight a 6 = a / 64 := Nat.shiftRight_eq_div_pow a 6

theorem and63 (a : Nat) : Nat.land a 63 = a % 64 := Nat.and_two_pow_sub_one_eq_mod a 6

theorem mul_bit (c v j : Nat) :
    Nat.mul c (Nat.land (Nat.shiftRight v j) 1) = GL62.Code.sel v j c := by
  change c * ((v >>> j) &&& 1) = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, GL62.Code.sel,
    Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ j) with h | h <;> simp [h]

theorem actK_eq (m v : Nat) : actK m v = GL62.Code.act m v := by
  have h0 : Nat.land v 1 = Nat.land (Nat.shiftRight v 0) 1 := rfl
  rw [actK, h0, mul_bit, mul_bit, mul_bit, mul_bit, mul_bit, mul_bit, GL62.Code.act]
  change _ = (((((_ ^^^ _) ^^^ _) ^^^ _) ^^^ _) ^^^ _)
  simp only [Nat.xor_assoc]
  rfl

theorem mulK_eq (a b : Nat) : mulK a b = GL62.Code.mul a b := by
  rw [GL62.Code.mul_eq, mulK, actK_eq, actK_eq, actK_eq, actK_eq, actK_eq, actK_eq]
  rfl

theorem lpFrom_sound {LP : Nat} {L : List Nat} {i : Nat} (h : lpFrom LP L i = true) :
    i + L.length = 128 ∧ ∀ k (hk : k < L.length), matAt LP (i + k) = L[k] := by
  induction L generalizing i with
  | nil =>
    have e : lpFrom LP [] i = Nat.beq i 128 := rfl
    rw [e, Nat.beq_eq] at h
    exact ⟨by simpa using h, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | cons c L ih =>
    have e : lpFrom LP (c :: L) i = (Nat.beq (matAt LP i) c && lpFrom LP L (Nat.succ i)) := rfl
    rw [e, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨h1, h2⟩ := ih h.2
    refine ⟨by simp only [List.length_cons]; omega, fun k hk => ?_⟩
    rcases k with _ | k
    · simpa using h.1
    · have := h2 k (by simpa using hk)
      rw [show i + (k + 1) = Nat.succ i + k by omega, this]
      rfl

theorem lpOK_sound {LP : Nat} {L : List Nat} (h : lpOK LP L = true) :
    L.length = 128 ∧ ∀ k < 128, matAt LP k = L[k]! := by
  obtain ⟨h1, h2⟩ := lpFrom_sound h
  refine ⟨by omega, fun k hk => ?_⟩
  have hk' : k < L.length := by omega
  rw [getElem!_pos L k hk', ← h2 k hk', Nat.zero_add]

theorem smOK_get {LP SM : Nat} (h : smOK LP SM = true) {i j : Nat} (hi : i < 128) (hj : j < 128) :
    matAt LP (lane SM 7 127 (Nat.add (Nat.mul 128 i) j)) = mulK (matAt LP i) (matAt LP j) := by
  exact Nat.eq_of_beq_eq_true (allB_eq_true.1 (allB_eq_true.1 h i hi) j hj)

theorem acOK_get {LP AC : Nat} (h : acOK LP AC = true) {i v : Nat} (hi : i < 128) (hv : v < 64) :
    lane AC 6 63 (Nat.add (Nat.mul 64 i) v) = actK (matAt LP i) v := by
  exact Nat.eq_of_beq_eq_true (allB_eq_true.1 (allB_eq_true.1 h i hi) v hv)

variable {S : Subgroup (GL (Fin 6) (ZMod 2))} {L : List Nat}

theorem wm_eq (hS : SubModel S L) {LP SM AC : Nat} (hLP : lpOK LP L = true)
    (hSM : smOK LP SM = true) (hAC : acOK LP AC = true) {a b : Nat} (ha : a < 8192)
    (hb : b < 8192) :
    wm SM AC a b = CFSG.SCATWreath.wMul (CFSG.SCATWreath.smulTab L) (CFSG.SCATWreath.actTab L) a b := by
  have hi : a / 64 < 128 := by omega
  have hj : b / 64 < 128 := by omega
  have hv : b % 64 < 64 := Nat.mod_lt _ (by norm_num)
  obtain ⟨_, hget⟩ := lpOK_sound hLP
  have hk : lane SM 7 127 (Nat.add (Nat.mul 128 (a / 64)) (b / 64)) < 128 :=
    Nat.lt_succ_of_le (lane_le _ _ _ _)
  have hsm := smOK_get hSM hi hj
  rw [hget _ hk, hget _ hi, hget _ hj, mulK_eq] at hsm
  have hidx : L.idxOf (GL62.Code.mul L[a / 64]! L[b / 64]!) =
      lane SM 7 127 (Nat.add (Nat.mul 128 (a / 64)) (b / 64)) := by
    rw [← hsm, getElem!_pos L _ (hS.len ▸ hk)]
    exact hS.nodup.idxOf_getElem _ _
  have hac := acOK_get hAC hi hv
  rw [hget _ hi, actK_eq] at hac
  rw [CFSG.SCATWreath.wMul, hS.smulTab_get hi hj, hS.actTab_get hi hv, wm, shr6, shr6, and63,
    and63, hidx, hac]
  rfl

theorem isModel_congr {G : Type*} [Group G] {K : Subgroup G} {n : Nat} {mul mul' : Nat → Nat → Nat}
    {dec : Nat → G} (M : IsModel K n mul dec) (h : ∀ a < n, ∀ b < n, mul' a b = mul a b) :
    IsModel K n mul' dec where
  mem := M.mem
  inj := M.inj
  surj := M.surj
  mul_lt a ha b hb := h a ha b hb ▸ M.mul_lt a ha b hb
  dec_mul a ha b hb := h a ha b hb ▸ M.dec_mul a ha b hb
  zero_lt := M.zero_lt
  dec_zero := M.dec_zero

theorem wm_model (hS : SubModel S L) {LP SM AC : Nat} (hLP : lpOK LP L = true)
    (hSM : smOK LP SM = true) (hAC : acOK LP AC = true) :
    IsModel (⊤ : Subgroup (Grp S)) 8192 (wm SM AC) hS.decW :=
  isModel_congr hS.isModel_decW fun _ ha _ hb => wm_eq hS hLP hSM hAC ha hb

end Certificates.KernelTower
