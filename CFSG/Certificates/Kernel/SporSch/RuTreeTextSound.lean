module

public import Certificates.Data.Kernel.SporSch.RuTreeK
public import CFSG.Certificates.Kernel.Misc.HexDropSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
import all CFSG.Certificates.Kernel.Misc.HexFlatSound

public section

namespace CFSG.KC.Misc.HexFlat

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.HexText CFSG.KS.RuTree
open CFSG.KS.Text (hexV)

@[expose] noncomputable def entK (n : Nat) (F : Nat → Nat) (k : Nat) : Nat :=
  pg 24 (mask 24) (F (Nat.div k n)) (Nat.mod k n)

@[expose] def AH (c : Char) : Prop := c.toNat < 128 ∧ hexV (Char.toNat c) < 16

theorem isNilK_eq {cs : List Char} (h : isNilK cs = true) : cs = [] := by
  cases cs with
  | nil => rfl
  | cons _ _ => exact absurd h Bool.false_ne_true

theorem chunk_sound {cs : List Char} {n T a b : Nat} {F : Nat → Nat}
    (hF : hexFlat cs 6 n 24 T F = true) (hE : isNilK (dropL a (dropL b cs)) = true)
    (hab : a + b = 6 * n * T) :
    cs.length = 6 * n * T ∧ (∀ k < cs.length, AH cs[k]!) ∧
    ∀ k < n * T, numA cs (6 * k) 6 = entK n F k := by
  have dF := digits_of hF
  obtain ⟨aF, eF⟩ := decode hF
  rw [dropL_eq, dropL_eq, List.drop_drop] at hE
  have hE' := isNilK_eq hE
  have hn : 0 < n := by
    unfold hexFlat at hF
    simp only [bAnd_iff] at hF
    exact Nat.blt_eq.mp hF.2.1
  have hlen : cs.length = 6 * n * T := by
    have h1 : cs.length ≤ 6 * n * T := by
      have := congrArg List.length hE'
      rw [List.length_drop, List.length_nil] at this
      omega
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT
      omega
    · have hp : 0 < 6 * n * T := Nat.mul_pos (Nat.mul_pos (by decide) hn) hT
      have h2 := (aF (6 * n * T - 1) (by omega)).1
      omega
  refine ⟨hlen, fun k hk => ⟨(aF k (by omega)).2, dF k (by omega)⟩, fun k hk => ?_⟩
  unfold entK
  have hj : k / n < T := by
    rw [Nat.div_lt_iff_lt_mul hn]
    rw [Nat.mul_comm] at hk
    exact hk
  change numA cs (6 * k) 6 = pg 24 (mask 24) (F (k / n)) (k % n)
  rw [(eF (k / n) hj (k % n) (Nat.mod_lt _ hn)).1]
  congr 2
  have := Nat.div_add_mod k n
  rw [this]

@[expose] noncomputable def entK2 (n T : Nat) (F R : Nat → Nat) (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (pg 24 (mask 24) (R 0) (Nat.sub k (Nat.mul n T)))
    (entK n F k) (Nat.blt k (Nat.mul n T))

theorem chunk_sound2 {cs : List Char} {n T r a b : Nat} {F R : Nat → Nat}
    (hF : hexFlat cs 6 n 24 T F = true) (hR : hexFlat (dropL (6 * n * T) cs) 6 r 24 1 R = true)
    (hE : isNilK (dropL a (dropL b cs)) = true) (hab : a + b = 6 * (n * T + r)) :
    cs.length = 6 * (n * T + r) ∧ (∀ k < cs.length, AH cs[k]!) ∧
    ∀ k < n * T + r, numA cs (6 * k) 6 = entK2 n T F R k := by
  have dF := digits_of hF
  have dR := digits_of hR
  obtain ⟨aF, eF⟩ := decode hF
  obtain ⟨aR, eR⟩ := decode hR
  rw [dropL_eq] at dR aR eR
  rw [dropL_eq, dropL_eq, List.drop_drop] at hE
  have hE' := isNilK_eq hE
  have hn : 0 < n := by
    unfold hexFlat at hF
    simp only [bAnd_iff] at hF
    exact Nat.blt_eq.mp hF.2.1
  have hr : 0 < r := by
    unfold hexFlat at hR
    simp only [bAnd_iff] at hR
    exact Nat.blt_eq.mp hR.2.1
  have hlen : cs.length = 6 * (n * T + r) := by
    have h1 : cs.length ≤ 6 * (n * T + r) := by
      have := congrArg List.length hE'
      rw [List.length_drop, List.length_nil] at this
      omega
    have hp : 0 < 6 * r * 1 := by omega
    have h2 := (aR (6 * r * 1 - 1) (by omega)).1
    rw [List.length_drop] at h2
    have : 6 * n * T = 6 * (n * T) := Nat.mul_assoc 6 n T
    omega
  have e6 : 6 * n * T = 6 * (n * T) := Nat.mul_assoc 6 n T
  refine ⟨hlen, fun k hk => ?_, fun k hk => ?_⟩
  · by_cases hk₀ : k < 6 * n * T
    · exact ⟨(aF k hk₀).2, dF k hk₀⟩
    · have e : 6 * n * T + (k - 6 * n * T) = k := by omega
      have h1 := (aR (k - 6 * n * T) (by omega)).2
      have h2 := dR (k - 6 * n * T) (by omega)
      rw [getElem!_drop, e] at h1 h2
      exact ⟨h1, h2⟩
  · unfold entK2
    by_cases hk₀ : k < n * T
    · have hb : Nat.blt k (Nat.mul n T) = true := Nat.blt_eq.mpr hk₀
      rw [hb]
      change numA cs (6 * k) 6 = pg 24 (mask 24) (F (k / n)) (k % n)
      have hj : k / n < T := by
        rw [Nat.div_lt_iff_lt_mul hn]
        rw [Nat.mul_comm] at hk₀
        exact hk₀
      rw [(eF (k / n) hj (k % n) (Nat.mod_lt _ hn)).1]
      congr 2
      rw [Nat.div_add_mod k n]
    · have hb : Nat.blt k (Nat.mul n T) = false := by
        cases h : Nat.blt k (Nat.mul n T)
        · rfl
        · exact absurd (Nat.blt_eq.mp h) hk₀
      rw [hb]
      change numA cs (6 * k) 6 = pg 24 (mask 24) (R 0) (k - n * T)
      rw [(eR 0 (by decide) (k - n * T) (by omega)).1, numA_drop]
      congr 1
      rw [e6]
      omega

theorem getElem!_app (l₁ l₂ : List Char) (k : Nat) :
    (l₁ ++ l₂)[k]! = if k < l₁.length then l₁[k]! else l₂[k - l₁.length]! := by
  by_cases h : k < l₁.length
  · simp only [h, ↓reduceIte, getElem!_def, List.getElem?_append_left h]
  · simp only [h, ↓reduceIte, getElem!_def, List.getElem?_append_right (Nat.le_of_not_lt h)]

theorem ah_app {l₁ l₂ : List Char} (h₁ : ∀ k < l₁.length, AH l₁[k]!)
    (h₂ : ∀ k < l₂.length, AH l₂[k]!) : ∀ k < (l₁ ++ l₂).length, AH (l₁ ++ l₂)[k]! := by
  intro k hk
  rw [getElem!_app]
  rw [List.length_append] at hk
  by_cases h : k < l₁.length
  · simp only [h, ↓reduceIte]
    exact h₁ k h
  · simp only [h, ↓reduceIte]
    exact h₂ _ (by omega)

theorem numA_app_right (l₁ l₂ : List Char) (o : Nat) :
    ∀ c, numA (l₁ ++ l₂) (l₁.length + o) c = numA l₂ o c
  | 0 => rfl
  | c + 1 => by
    simp only [numA]
    have h : ¬ (l₁.length + o + c < l₁.length) := by omega
    rw [numA_app_right l₁ l₂ o c, getElem!_app]
    simp only [h, ↓reduceIte]
    rw [show l₁.length + o + c - l₁.length = o + c by omega]

theorem numA_app_left (l₁ l₂ : List Char) (o : Nat) :
    ∀ c, o + c ≤ l₁.length → numA (l₁ ++ l₂) o c = numA l₁ o c
  | 0, _ => rfl
  | c + 1, h => by
    simp only [numA]
    have h' : o + c < l₁.length := by omega
    rw [numA_app_left l₁ l₂ o c (by omega), getElem!_app]
    simp only [h', ↓reduceIte]

theorem hexAt_ofList {cs : List Char} (h : ∀ k < cs.length, AH cs[k]!) {o w : Nat}
    (hw : o + w ≤ cs.length) :
    CFSG.Monster.B.Max2.Native.hexAt (String.ofList cs).toUTF8 o w = numA cs o w :=
  num_bytes (D := cs.length) (fun k hk => ⟨hk, (h k hk).1⟩)
    (fun c => CFSG.Monster.B.Max2.Native.hexAt (String.ofList cs).toUTF8 o c) rfl (fun _ => rfl) w
    hw (fun s hs => (h (o + s) (by omega)).2)

theorem chunk_rec {pre cs post : List Char} {K : Nat} {E : Nat → Nat}
    (hlen : cs.length = 6 * K) (hah : ∀ k < cs.length, AH cs[k]!)
    (hent : ∀ k < K, numA cs (6 * k) 6 = E k)
    (hpre : ∀ k < pre.length, AH pre[k]!) (hpost : ∀ k < post.length, AH post[k]!)
    {k : Nat} (hk : k < K) :
    CFSG.Monster.B.Max2.Native.hexAt (String.ofList (pre ++ cs ++ post)).toUTF8 (pre.length + 6 * k) 5 =
        E k / 16 ∧
      CFSG.Monster.B.Max2.Native.hexAt (String.ofList (pre ++ cs ++ post)).toUTF8
        (pre.length + 6 * k + 5) 1 = E k % 16 := by
  have hall := ah_app (ah_app hpre hah) hpost
  have hL : (pre ++ cs ++ post).length = pre.length + cs.length + post.length := by
    simp only [List.length_append]
  have hk6 : 6 * k + 6 ≤ cs.length := by omega
  have hd : hexV (Char.toNat cs[6 * k + 5]!) < 16 := (hah (6 * k + 5) (by omega)).2
  have key : E k = numA cs (6 * k) 5 * 16 + hexV (Char.toNat cs[6 * k + 5]!) := by
    rw [← hent k hk]
    rfl
  constructor
  · rw [hexAt_ofList hall (by omega), List.append_assoc, numA_app_right,
      numA_app_left _ _ _ _ (by omega), key]
    omega
  · rw [hexAt_ofList hall (by omega), Nat.add_assoc, List.append_assoc, numA_app_right,
      numA_app_left _ _ _ _ (by omega), key]
    change 0 * 16 + hexV (Char.toNat cs[6 * k + 5 + 0]!) = _
    rw [Nat.add_zero]
    omega

private theorem utf8_size_ascii' : ∀ cs : List Char,
    (∀ k < cs.length, (cs[k]!).toNat < 128) → cs.utf8Encode.size = cs.length
  | [], _ => rfl
  | c :: cs, h => by
    have hc : c.toNat < 128 := by simpa using h 0 (by simp)
    rw [List.utf8Encode_cons, CFSG.KS.HexText.utf8_single hc, ByteArray.size_append,
      utf8_size_ascii' cs (fun k hk => by simpa using h (k + 1) (by simp; omega))]
    simp
    omega

theorem size_ofList {cs : List Char} (h : ∀ k < cs.length, (cs[k]!).toNat < 128) :
    (String.ofList cs).toUTF8.size = cs.length := by
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  exact utf8_size_ascii' cs h

end CFSG.KC.Misc.HexFlat

end
