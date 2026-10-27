module

public import Certificates.Data.Kernel.Misc.G23F3
public import CFSG.Certificates.Kernel.G2Three.Pack
public import CFSG.Certificates.Kernel.Misc.Spec.ArrF2
import CFSG.Certificates.Kernel.Spor.PK.MiscBase

public section

namespace CFSG.KC.Misc.G23F3

open CFSG.KS.Mat3 CFSG.KC.Ord CFSG.KD.G2Three CFSG.KC.G2Three CFSG.Sporadic.He.Native
open CFSG.KC.Misc.Spec CFSG.KC.Misc.G24

@[expose] def toM3 (X : Array (Array ℕ)) : Matrix (Fin 14) (Fin 14) (ZMod 3) :=
  Matrix.of fun i j => (((X[i.val]!)[j.val]! : ℕ) : ZMod 3)

@[expose] def ofM3 (M : Matrix (Fin 14) (Fin 14) (ZMod 3)) : Array (Array ℕ) :=
  Array.ofFn fun i => Array.ofFn fun j => (M i j).val

theorem ofM3_entry (M : Matrix (Fin 14) (Fin 14) (ZMod 3)) (i j : Fin 14) :
    ((ofM3 M)[i.val]!)[j.val]! = (M i j).val := by
  unfold ofM3
  rw [ofFn_getElem! _ i.isLt, ofFn_getElem! _ j.isLt]

theorem toM3_ofM3 (M : Matrix (Fin 14) (Fin 14) (ZMod 3)) : toM3 (ofM3 M) = M := by
  ext i j
  unfold toM3
  rw [Matrix.of_apply, ofM3_entry]
  exact ZMod.natCast_zmod_val (M i j)

theorem mulM3_eq (X Y : Array (Array ℕ)) : mulM 3 14 X Y = ofM3 (toM3 X * toM3 Y) := by
  unfold mulM ofM3
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun k => ?_))
  unfold dot
  rw [Matrix.mul_apply]
  have e : ∀ j : ℕ, j < 14 → (col 14 Y k.val)[j]! = (Y[j]!)[k.val]! := by
    intro j hj
    unfold col
    rw [ofFn_getElem! _ hj]
  have h1 : Nat.fold 14 (fun j _ acc => acc + (X[i.val]!)[j]! * (col 14 Y k.val)[j]!) 0 =
      ∑ j ∈ Finset.range 14, (X[i.val]!)[j]! * (Y[j]!)[k.val]! := by
    rw [fold_sum (fun j => (X[i.val]!)[j]! * (col 14 Y k.val)[j]!) 14]
    exact Finset.sum_congr rfl fun j hj => by rw [e j (Finset.mem_range.1 hj)]
  rw [h1]
  have h2 : (∑ j : Fin 14, toM3 X i j * toM3 Y j k) =
      ((∑ j ∈ Finset.range 14, (X[i.val]!)[j]! * (Y[j]!)[k.val]! : ℕ) : ZMod 3) := by
    rw [Nat.cast_sum, ← Fin.sum_univ_eq_sum_range
      (fun j => (((X[i.val]!)[j]! * (Y[j]!)[k.val]! : ℕ) : ZMod 3)) 14]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [toM3]
  rw [h2, ZMod.val_natCast]

theorem idM3_eq : idM 14 = ofM3 1 := by
  unfold idM ofM3
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun j => ?_))
  rw [Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp only [if_true]
    rfl
  · have h' : ¬ i.val = j.val := fun e => h (Fin.ext e)
    simp only [h, h', if_false]
    rfl

theorem bitsK_eq (v : ℕ) : ∀ m : List ℕ, bitsK v m = bitsOf (· == v) m
  | [] => rfl
  | e :: m => by
    change 2 * bitsK v m + Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq e v) = _
    rw [bitsK_eq v m, bitsOf]
    cases h : Nat.beq e v
    · have : (e == v) = false := h
      simp [this]
    · have : (e == v) = true := h
      simp [this]

theorem pkK_eq (m : List ℕ) : pkK m = pk m := by
  change (1 <<< 196) * bitsK 2 m + bitsK 1 m = _
  rw [bitsK_eq, bitsK_eq, Nat.shiftLeft_eq, one_mul]
  rfl

theorem mul_sound (hc : constsK = true) {A B : ℕ} (hA : Canon3 196 A) (hB : Canon3 196 B) :
    Canon3 196 (MUL A B) ∧ mat3 14 196 (MUL A B) = mat3 14 196 A * mat3 14 196 B :=
  mul3s_sound hc hA hB

theorem wordK_sound (hc : constsK = true) {R : List ℕ} {n : ℕ}
    (hR : ∀ j < n, Canon3 196 (nthV R j)) :
    ∀ js : List ℕ, (∀ j ∈ js, j < n) → Canon3 196 (wordK R js) ∧
      mat3 14 196 (wordK R js) = (js.map fun j => mat3 14 196 (nthV R j)).prod
  | [], _ => by
    obtain ⟨h1, h2⟩ := one3_sound hc
    exact ⟨h1, h2⟩
  | j :: js, h => by
    obtain ⟨ih1, ih2⟩ := wordK_sound hc hR js fun k hk => h k (List.mem_cons_of_mem _ hk)
    have hj := hR j (h j List.mem_cons_self)
    change Canon3 196 (MUL (nthV R j) (wordK R js)) ∧ mat3 14 196 (MUL (nthV R j) (wordK R js)) = _
    obtain ⟨m1, m2⟩ := mul_sound hc hj ih1
    refine ⟨m1, ?_⟩
    rw [m2, ih2, List.map_cons, List.prod_cons]

theorem testBit_of_bit {X t : ℕ} : X.testBit t = (bit X t == 1) := by
  have e : bit X t = X / 2 ^ t % 2 := by
    change (X >>> t) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ t) with h | h <;> simp [h]

theorem two_sound {X : ℕ} (i j : Fin 14) (h : two X (14 * i.val + j.val) = true) :
    mat3 14 196 X i j = 2 := by
  unfold two at h
  simp only [CFSG.KS.PK.andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  have h1 : X.testBit (14 * i.val + j.val) = false := by rw [testBit_of_bit, h.1]; rfl
  have h2' : bit X (196 + (14 * i.val + j.val)) = 1 := h.2
  have h2 : X.testBit (196 + (14 * i.val + j.val)) = true := by rw [testBit_of_bit, h2']; rfl
  unfold mat3
  rw [h1, h2]
  rfl

theorem ne_one_of (hc : constsK = true) {X : ℕ} (hX : Canon3 196 X) (h : Nat.beq X ONE = false) :
    mat3 14 196 X ≠ 1 := by
  intro e
  obtain ⟨o1, o2⟩ := one3_sound hc
  have := mat3_inj (d := 14) (N := 196) rfl hX o1 (e.trans o2.symm)
  rw [this, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem splitK_sound {U V Z A1 A2 C : ℕ} (hc : constsK = true) (hU : Canon3 196 U)
    (hV : Canon3 196 V) (hZ : Canon3 196 Z) (hA1 : Canon3 196 A1) (hA2 : Canon3 196 A2)
    (hC : Canon3 196 C) (h : splitK U V Z A1 A2 C = true) :
    let u := mat3 14 196 U
    let v := mat3 14 196 V
    let z := mat3 14 196 Z
    let a₁ := mat3 14 196 A1
    let a₂ := mat3 14 196 A2
    let c := mat3 14 196 C
    a₁ * (a₁ * a₁) = 1 ∧ a₂ * (a₂ * a₂) = 1 ∧ z * (z * z) = 1 ∧ u * (u * u) = 1 ∧
      a₁ * a₂ = a₂ * a₁ ∧ u * a₁ = a₁ * u ∧ u * a₂ = a₂ * u ∧ v * a₁ = a₁ * v ∧ v * a₂ = a₂ * v ∧
      z * a₁ = a₁ * z ∧ z * a₂ = a₂ * z ∧ u * z = z * u ∧ v * z = z * v ∧ u * v = z * (v * u) ∧
      c * a₁ = a₂ * c ∧ c * a₂ = a₁ * (a₂ * c) ∧ a₁ 0 5 = 2 ∧ z 0 12 = 2 := by
  unfold splitK at h
  simp only [CFSG.KS.PK.andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  obtain ⟨o1, o2⟩ := one3_sound hc
  have M : ∀ {A B : ℕ}, Canon3 196 A → Canon3 196 B →
      mat3 14 196 (MUL A B) = mat3 14 196 A * mat3 14 196 B := fun hA hB => (mul_sound hc hA hB).2
  have K : ∀ {A B : ℕ}, Canon3 196 A → Canon3 196 B → Canon3 196 (MUL A B) :=
    fun hA hB => (mul_sound hc hA hB).1
  have e : ∀ {X Y : ℕ}, X = Y → mat3 14 196 X = mat3 14 196 Y := fun h => congrArg _ h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    two_sound (X := A1) 0 5 h17, two_sound (X := Z) 0 12 h18⟩
  · have := e h1; rwa [M hA1 (K hA1 hA1), M hA1 hA1, o2] at this
  · have := e h2; rwa [M hA2 (K hA2 hA2), M hA2 hA2, o2] at this
  · have := e h3; rwa [M hZ (K hZ hZ), M hZ hZ, o2] at this
  · have := e h4; rwa [M hU (K hU hU), M hU hU, o2] at this
  · have := e h5; rwa [M hA1 hA2, M hA2 hA1] at this
  · have := e h6; rwa [M hU hA1, M hA1 hU] at this
  · have := e h7; rwa [M hU hA2, M hA2 hU] at this
  · have := e h8; rwa [M hV hA1, M hA1 hV] at this
  · have := e h9; rwa [M hV hA2, M hA2 hV] at this
  · have := e h10; rwa [M hZ hA1, M hA1 hZ] at this
  · have := e h11; rwa [M hZ hA2, M hA2 hZ] at this
  · have := e h12; rwa [M hU hZ, M hZ hU] at this
  · have := e h13; rwa [M hV hZ, M hZ hV] at this
  · have := e h14; rwa [M hU hV, M hZ (K hV hU), M hV hU] at this
  · have := e h15; rwa [M hC hA1, M hA2 hC] at this
  · have := e h16; rwa [M hC hA2, M hA1 (K hA2 hC), M hA2 hC] at this

theorem liftK_sound (hc : constsK = true) {R : List ℕ} {n : ℕ}
    (hR : ∀ j < n, Canon3 196 (nthV R j)) {eqs : List (List ℕ × List ℕ)} {nes : List (List ℕ)}
    (heq : ∀ p ∈ eqs, (∀ j ∈ p.1, j < n) ∧ ∀ j ∈ p.2, j < n) (hne : ∀ w ∈ nes, ∀ j ∈ w, j < n)
    (h : liftK R eqs nes = true) :
    (∀ p ∈ eqs, (p.1.map fun j => mat3 14 196 (nthV R j)).prod =
      (p.2.map fun j => mat3 14 196 (nthV R j)).prod) ∧
    ∀ w ∈ nes, (w.map fun j => mat3 14 196 (nthV R j)).prod ≠ 1 := by
  unfold liftK at h
  rw [CFSG.KS.PK.andB_eq, Bool.and_eq_true] at h
  obtain ⟨hE, hN⟩ := h
  refine ⟨?_, ?_⟩
  · clear hN hne
    induction eqs with
    | nil => intro p hp; cases hp
    | cons p ps ih =>
      change (Nat.beq (wordK R p.1) (wordK R p.2) && _) = true at hE
      rw [Bool.and_eq_true, Nat.beq_eq] at hE
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · obtain ⟨a1, a2⟩ := heq q List.mem_cons_self
        rw [← (wordK_sound hc hR q.1 a1).2, ← (wordK_sound hc hR q.2 a2).2, hE.1]
      · exact ih (fun r hr => heq r (List.mem_cons_of_mem _ hr)) hE.2 q hq
  · clear hE heq
    induction nes with
    | nil => intro w hw; cases hw
    | cons w ws ih =>
      change (CFSG.KC.Ord.notB (Nat.beq (wordK R w) ONE) && _) = true at hN
      rw [Bool.and_eq_true] at hN
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · obtain ⟨k1, k2⟩ := wordK_sound hc hR x (hne x List.mem_cons_self)
        rw [← k2]
        refine ne_one_of hc k1 ?_
        cases hb : Nat.beq (wordK R x) ONE
        · rfl
        · rw [hb] at hN; exact absurd hN.1 (by decide)
      · exact ih (fun r hr => hne r (List.mem_cons_of_mem _ hr)) hN.2 x hx

end CFSG.KC.Misc.G23F3

end
