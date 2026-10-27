module

public import CFSG.GH74.QTGen4.U42.U0Core

public section

namespace CFSG.GH74.QTGen4.U42.U0AutB

open CFSG.Quasithin.A5Model CFSG.Quasithin.H13.A5 CFSG.GH74.QTGen4.U42

def xc (w : W5) (i : Fin 5) : ZMod 2 := ((Multiplicative.toAdd w : ↥Ev) : Fin 5 → ZMod 2) i

def bitL (w : W5) : Nat :=
  (if xc w 0 + xc w 2 = 1 then 2 else 0) + (if xc w 0 + xc w 1 = 1 then 1 else 0)

def bitK (σ : Equiv.Perm (Fin 5)) : Nat :=
  (if σ = pa ∨ σ = pc then 1 else 0) + (if σ = pb ∨ σ = pc then 2 else 0)

theorem mem_U0_iff (x : Mc) : x ∈ U0 ↔ x.left ∈ W3 ∧ InK4 x.right := Iff.rfl

@[expose] def cU (x : U0) : Nat := bitL x.1.left + 4 * bitK x.1.right

def K4list : List (Equiv.Perm (Fin 5)) := [1, pa, pb, pc]

theorem inK4_iff (σ : Equiv.Perm (Fin 5)) : InK4 σ ↔ σ ∈ K4list := by
  simp [InK4, K4list]

theorem hom_raw : ∀ σ ∈ K4list, ∀ τ ∈ K4list, ∀ w : W5, c4 w = 1 →
    ∀ w' : W5, c4 w' = 1 →
      bitL (w * pact σ w') + 4 * bitK (σ * τ) =
        Nat.xor (bitL w + 4 * bitK σ) (bitL w' + 4 * bitK τ) := by
  decide +kernel

theorem cU_mul (x y : U0) : cU (x * y) = Nat.xor (cU x) (cU y) := by
  have hx := (mem_U0_iff x.1).1 x.2
  have hy := (mem_U0_iff y.1).1 y.2
  exact hom_raw x.1.right ((inK4_iff _).1 hx.2) y.1.right ((inK4_iff _).1 hy.2)
    x.1.left (mem_W3.1 hx.1) y.1.left (mem_W3.1 hy.1)

theorem cU_lt16 (x : U0) : cU x < 16 := by
  unfold cU bitL bitK
  split_ifs <;> omega

theorem cU_one : cU 1 = 0 := by decide +kernel

theorem cU_zc : cU zc = 0 := by
  show bitL W4 + 4 * bitK 1 = 0
  decide +kernel

theorem e2_02_mem : (⟨Multiplicative.ofAdd (e2 0 2), 1⟩ : Mc).left ∈ W3 :=
  mem_W3.2 (by decide +kernel)

theorem e2_01_mem : (⟨Multiplicative.ofAdd (e2 0 1), 1⟩ : Mc).left ∈ W3 :=
  mem_W3.2 (by decide +kernel)

@[expose] def E1 : U0 := ⟨⟨Multiplicative.ofAdd (e2 0 2), 1⟩, (mem_U0_iff _).2 ⟨e2_02_mem, Or.inl rfl⟩⟩

@[expose] def E2 : U0 := ⟨⟨Multiplicative.ofAdd (e2 0 1), 1⟩, (mem_U0_iff _).2 ⟨e2_01_mem, Or.inl rfl⟩⟩

@[expose] def E4 : U0 := ⟨⟨1, pa⟩, (mem_U0_iff _).2 ⟨W3.one_mem, Or.inr (Or.inl rfl)⟩⟩

@[expose] def E8 : U0 := ⟨⟨1, pb⟩, (mem_U0_iff _).2 ⟨W3.one_mem, Or.inr (Or.inr (Or.inl rfl))⟩⟩

theorem cU_E1 : cU E1 = 1 := by
  show bitL (Multiplicative.ofAdd (e2 0 2)) + 4 * bitK 1 = 1
  decide +kernel

theorem cU_E2 : cU E2 = 2 := by
  show bitL (Multiplicative.ofAdd (e2 0 1)) + 4 * bitK 1 = 2
  decide +kernel

theorem cU_E4 : cU E4 = 4 := by
  show bitL 1 + 4 * bitK pa = 4
  decide +kernel

theorem cU_E8 : cU E8 = 8 := by
  show bitL 1 + 4 * bitK pb = 8
  decide +kernel

@[expose] def elU (u : Nat) : U0 :=
  (if u.testBit 0 then E1 else 1) * (if u.testBit 1 then E2 else 1) *
    (if u.testBit 2 then E4 else 1) * (if u.testBit 3 then E8 else 1)

theorem cU_ite {b : Prop} [Decidable b] (E : U0) (c : Nat) (hE : cU E = c) :
    cU (if b then E else 1) = if b then c else 0 := by
  split_ifs <;> simp [cU_one, hE]

theorem cU_elU (u : Nat) (hu : u < 16) : cU (elU u) = u := by
  unfold elU
  rw [cU_mul, cU_mul, cU_mul]
  simp only [cU_ite E1 1 cU_E1, cU_ite E2 2 cU_E2, cU_ite E4 4 cU_E4, cU_ite E8 8 cU_E8]
  interval_cases u <;> decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem bitL_zero_fact : ∀ w : W5, c4 w = 1 → bitL w = 0 → w = 1 ∨ w = W4 := by
  decide +kernel

theorem bitK_zero_fact : ∀ σ ∈ K4list, bitK σ = 0 → σ = 1 := by
  decide +kernel

theorem mc_ext {x y : Mc} (h1 : x.left = y.left) (h2 : x.right = y.right) : x = y := by
  obtain ⟨a1, a2⟩ := x
  obtain ⟨b1, b2⟩ := y
  simp only at h1 h2
  subst h1
  subst h2
  rfl

theorem U0_ext {x y : U0} (h1 : x.1.left = y.1.left) (h2 : x.1.right = y.1.right) : x = y :=
  Subtype.ext (mc_ext h1 h2)

theorem cU_eq_zero_iff (x : U0) : cU x = 0 ↔ x = 1 ∨ x = zc := by
  constructor
  · intro h
    have hx := (mem_U0_iff x.1).1 x.2
    have hw : bitL x.1.left = 0 := by unfold cU at h; omega
    have hσ : bitK x.1.right = 0 := by unfold cU at h; omega
    have hσ1 : x.1.right = 1 := bitK_zero_fact _ ((inK4_iff _).1 hx.2) hσ
    rcases bitL_zero_fact x.1.left (mem_W3.1 hx.1) hw with h1 | h1
    · left
      exact U0_ext h1 hσ1
    · right
      exact U0_ext h1 hσ1
  · rintro (rfl | rfl)
    · exact cU_one
    · exact cU_zc

end CFSG.GH74.QTGen4.U42.U0AutB
