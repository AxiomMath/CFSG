module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalG3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SecondLayer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowBoundsCount
public import CFSG.Quasithin.Background.FFC3Unitri

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa : Subgroup G}
  {z b : G}

private abbrev M4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

private abbrev E : M4 := 1 + Matrix.single 0 3 1

private abbrev X (i j : Fin 4) (a : ZMod 2) : M4 := 1 + Matrix.single i j a

private lemma E_comm_ut {M : M4} (hM : ∀ i j : Fin 4, j < i → M i j = 0)
    (hd : ∀ i : Fin 4, M i i = 1) : E * M = M * E := by
  unfold E
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply, hM, hd,
      add_comm]

private lemma E_comm_X01 : E * X 0 1 1 = X 0 1 1 * E := by decide

private lemma E_comm_X12 : E * X 1 2 1 = X 1 2 1 * E := by decide

private lemma E_comm_X21 : E * X 2 1 1 = X 2 1 1 * E := by decide

private lemma E_comm_X23 : E * X 2 3 1 = X 2 3 1 * E := by decide

private lemma E_mul_self : E * E = 1 := by decide

private lemma E_ne_one : E ≠ 1 := by decide

private lemma X_mul_self {i j : Fin 4} (hij : i ≠ j) (a : ZMod 2) :
    X i j a * X i j a = 1 := by
  unfold X
  ext r c
  fin_cases i <;> fin_cases j <;> simp_all <;>
    fin_cases r <;> fin_cases c <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply] <;>
      exact CharTwo.add_self_eq_zero a

private lemma X02_eq : X 0 2 1 = (X 0 1 1 * X 1 2 1) * (X 0 1 1 * X 1 2 1) := by decide

private lemma X13_eq : X 1 3 1 = (X 1 2 1 * X 2 3 1) * (X 1 2 1 * X 2 3 1) := by decide

private lemma X03_eq : X 0 3 1 = (X 0 1 1 * X 1 3 1) * (X 0 1 1 * X 1 3 1) := by decide

private lemma X01_eq : X 0 1 1 = (X 0 2 1 * X 2 1 1) * (X 0 2 1 * X 2 1 1) := by decide

private lemma X23_eq : X 2 3 1 = (X 2 1 1 * X 1 3 1) * (X 2 1 1 * X 1 3 1) := by decide

private lemma ut_factor {M : M4} (hM : ∀ i j : Fin 4, j < i → M i j = 0)
    (hd : ∀ i : Fin 4, M i i = 1) :
    M = (1 + Matrix.single 0 1 (M 0 1)) *
        (1 + Matrix.single 1 2 (M 1 2)) *
        (1 + Matrix.single 2 3 (M 2 3)) *
        (1 + Matrix.single 0 2 (M 0 2 + M 0 1 * M 1 2)) *
        (1 + Matrix.single 1 3 (M 1 3 + M 1 2 * M 2 3)) *
        (1 + Matrix.single 0 3 (M 0 3 + M 0 1 * M 1 2 * M 2 3 +
          M 0 1 * (M 1 3 + M 1 2 * M 2 3))) := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h4 : (4 : ZMod 2) = 0 := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply,
      hM, hd, h2, h4] <;>
    first
      | linear_combination -CharTwo.add_self_eq_zero (M 0 1 * M 1 2)
      | linear_combination -CharTwo.add_self_eq_zero (M 1 2 * M 2 3)
      | linear_combination -CharTwo.add_self_eq_zero (M 0 1 * M 1 2 * M 2 3) -
          CharTwo.add_self_eq_zero (M 0 1 * (M 1 3 + M 1 2 * M 2 3))

private lemma IsRep.inv {c : G → (Fin 4 → ZMod 2)} {A : Subgroup G} {r : G} {M : M4}
    (hc : IsCoord A c) (h : IsRep A c r M) (hr : ∀ a ∈ A, r * a * r⁻¹ ∈ A) :
    IsRep A c r⁻¹ M⁻¹ := by
  obtain ⟨N, hN⟩ := hc.exists_rep (r := r⁻¹) (fun a ha => by
    simpa using conj_inv_mem_of_conj_mem hr ha)
  have h1 : IsRep A c (1 : G) (M * N) := by
    have hmul := h.mul (s := r⁻¹) hN (fun a ha => by
      simpa using conj_inv_mem_of_conj_mem hr ha)
    simpa using hmul
  have hMN : M * N = 1 := hc.rep_unique h1 IsRep.one
  rw [Matrix.inv_eq_right_inv hMN]
  exact hN

private lemma IsRep.mul_inv {c : G → (Fin 4 → ZMod 2)} {A : Subgroup G} {r : G} {M : M4}
    (hc : IsCoord A c) (h : IsRep A c r M) (hr : ∀ a ∈ A, r * a * r⁻¹ ∈ A) :
    M * M⁻¹ = 1 := by
  obtain ⟨N, hN⟩ := hc.exists_rep (r := r⁻¹) (fun a ha => by
    simpa using conj_inv_mem_of_conj_mem hr ha)
  have h1 : IsRep A c (1 : G) (M * N) := by
    have hmul := h.mul (s := r⁻¹) hN (fun a ha => by
      simpa using conj_inv_mem_of_conj_mem hr ha)
    simpa using hmul
  have hMN : M * N = 1 := hc.rep_unique h1 IsRep.one
  rw [Matrix.inv_eq_right_inv hMN, hMN]

private def Good (L A B : Subgroup G) (ζ n : G) : Prop :=
  n ∈ L ∧ (∀ a ∈ A, n * a * n⁻¹ ∈ A) ∧ ζ * n * ζ⁻¹ * n⁻¹ ∈ B

private lemma Good.one (L A B : Subgroup G) (ζ : G) : Good L A B ζ 1 := by
  refine ⟨L.one_mem, fun a ha => by simpa using ha, ?_⟩
  simp

private lemma Good.mul (W : ThLocalIn L S A B z) {ζ n m : G}
    (hn : Good L A B ζ n) (hm : Good L A B ζ m) : Good L A B ζ (n * m) := by
  refine ⟨L.mul_mem hn.1 hm.1, fun a ha => ?_, ?_⟩
  · have h : n * m * a * (n * m)⁻¹ = n * (m * a * m⁻¹) * n⁻¹ := by group
    rw [h]
    exact hn.2.1 _ (hm.2.1 a ha)
  · have hnB : ∀ y ∈ B, n * y * n⁻¹ ∈ B :=
      W.conj_mem_B (fun a ha => conj_inv_mem_of_conj_mem hn.2.1 ha)
        (fun y hy => L.mul_mem (L.mul_mem hn.1 (W.B_le hy)) (L.inv_mem hn.1))
    have h : (ζ * n * ζ⁻¹ * n⁻¹) * (n * (ζ * m * ζ⁻¹ * m⁻¹) * n⁻¹) ∈ B :=
      B.mul_mem hn.2.2 (hnB _ hm.2.2)
    have e : ζ * (n * m) * ζ⁻¹ * (n * m)⁻¹ =
        (ζ * n * ζ⁻¹ * n⁻¹) * (n * (ζ * m * ζ⁻¹ * m⁻¹) * n⁻¹) := by group
    rwa [e]

private lemma conj_mul_inv_mem_Aa (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    {n : G} (hnL : n ∈ L) (hnA : ∀ a ∈ A, n * a * n⁻¹ ∈ A) {β : G} (hβ : β ∈ B) :
    n * β * n⁻¹ * β⁻¹ ∈ Aa := by
  have hnB : ∀ y ∈ B, n * y * n⁻¹ ∈ B :=
    W.conj_mem_B (fun a ha => conj_inv_mem_of_conj_mem hnA ha)
      (fun y hy => L.mul_mem (L.mul_mem hnL (W.B_le hy)) (L.inv_mem hnL))
  have hnAa : ∀ x ∈ Aa, n * x * n⁻¹ ∈ Aa := W2.conj_mem_of_mem_L W hnL hnA
  have hnAa' : ∀ x ∈ Aa, n⁻¹ * x * n ∈ Aa := fun x hx => conj_inv_mem_of_conj_mem hnAa hx
  rcases W2.mem_Aa_or_mul_b W hβ with hβA | hβb
  · exact Aa.mul_mem (hnAa β hβA) (Aa.inv_mem hβA)
  · set c := β * b with hc
    have hcAa : c ∈ Aa := hβb
    have hβeq : β = c * b := by rw [hc, mul_assoc, ← pow_two, W2.b_sq, mul_one]
    have hd : n * b * n⁻¹ ∈ B := hnB b W2.b_mem
    have hdAa : n * b * n⁻¹ ∉ Aa := by
      intro h
      have hb : b ∈ Aa := by
        have h' := hnAa' _ h
        have e : n⁻¹ * (n * b * n⁻¹) * n = b := by group
        rwa [e] at h'
      exact W2.b_not_mem hb
    have hdb : (n * b * n⁻¹) * b ∈ Aa :=
      (W2.mem_Aa_or_mul_b W hd).resolve_left hdAa
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact W2.b_sq)
    have e : n * β * n⁻¹ * β⁻¹ = (n * c * n⁻¹) * ((n * b * n⁻¹) * b) * c⁻¹ := by
      rw [hβeq, _root_.mul_inv_rev, hbinv]
      group
    rw [e]
    exact Aa.mul_mem (Aa.mul_mem (hnAa c hcAa) hdb) (Aa.inv_mem hcAa)

private def P (Aa : Subgroup G) (ζ n : G) : Prop := ζ * n * ζ⁻¹ * n⁻¹ ∈ Aa

private lemma P.one (Aa : Subgroup G) (ζ : G) : P Aa ζ 1 := by simp [P]

private lemma mul_mem_Aa_iff (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    {x y : G} (hx : x ∈ B) (hy : y ∈ B) : x * y ∈ Aa ↔ (x ∈ Aa ↔ y ∈ Aa) := by
  constructor
  · intro hxy
    constructor
    · intro hxAa
      have e : y = x⁻¹ * (x * y) := by group
      rw [e]
      exact Aa.mul_mem (Aa.inv_mem hxAa) hxy
    · intro hyAa
      have e : x = (x * y) * y⁻¹ := by group
      rw [e]
      exact Aa.mul_mem hxy (Aa.inv_mem hyAa)
  · intro hiff
    by_cases hxAa : x ∈ Aa
    · exact Aa.mul_mem hxAa (hiff.1 hxAa)
    · have hyAa : y ∉ Aa := fun hyA => hxAa (hiff.2 hyA)
      have hxb : x * b ∈ Aa := (W2.mem_Aa_or_mul_b W hx).resolve_left hxAa
      have hyb : y * b ∈ Aa := (W2.mem_Aa_or_mul_b W hy).resolve_left hyAa
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact W2.b_sq)
      have hx' : x = (x * b) * b := by rw [mul_assoc, ← pow_two, W2.b_sq, mul_one]
      have hy' : y = (y * b) * b := by rw [mul_assoc, ← pow_two, W2.b_sq, mul_one]
      have hbb : b * (y * b) * b = (y * b)⁻¹ := by
        have := W2.b_inv (y * b) hyb
        rwa [hbinv] at this
      have e : x * y = (x * b) * (b * (y * b) * b) := by
        conv_lhs => rw [hx', hy']
        group
      rw [e, hbb]
      exact Aa.mul_mem hxb (Aa.inv_mem hyb)

private lemma P.mul_iff (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) {ζ n m : G}
    (hn : Good L A B ζ n) (hm : Good L A B ζ m) :
    P Aa ζ (n * m) ↔ (P Aa ζ n ↔ P Aa ζ m) := by
  have hψ : n * (ζ * m * ζ⁻¹ * m⁻¹) * n⁻¹ * (ζ * m * ζ⁻¹ * m⁻¹)⁻¹ ∈ Aa :=
    conj_mul_inv_mem_Aa W W2 hn.1 hn.2.1 hm.2.2
  have hnB : ∀ y ∈ B, n * y * n⁻¹ ∈ B :=
    W.conj_mem_B (fun a ha => conj_inv_mem_of_conj_mem hn.2.1 ha)
      (fun y hy => L.mul_mem (L.mul_mem hn.1 (W.B_le hy)) (L.inv_mem hn.1))
  have hhB : n * (ζ * m * ζ⁻¹ * m⁻¹) * n⁻¹ ∈ B := hnB _ hm.2.2
  have hiff : n * (ζ * m * ζ⁻¹ * m⁻¹) * n⁻¹ ∈ Aa ↔ ζ * m * ζ⁻¹ * m⁻¹ ∈ Aa := by
    constructor
    · intro hh
      have e : ζ * m * ζ⁻¹ * m⁻¹ =
          (n * (ζ * m * ζ⁻¹ * m⁻¹) * n⁻¹ * (ζ * m * ζ⁻¹ * m⁻¹)⁻¹)⁻¹ *
            (n * (ζ * m * ζ⁻¹ * m⁻¹) * n⁻¹) := by group
      rw [e]
      exact Aa.mul_mem (Aa.inv_mem hψ) hh
    · intro hy
      have e : n * (ζ * m * ζ⁻¹ * m⁻¹) * n⁻¹ =
          (n * (ζ * m * ζ⁻¹ * m⁻¹) * n⁻¹ * (ζ * m * ζ⁻¹ * m⁻¹)⁻¹) *
            (ζ * m * ζ⁻¹ * m⁻¹) := by group
      rw [e]
      exact Aa.mul_mem hψ hy
  have e : ζ * (n * m) * ζ⁻¹ * (n * m)⁻¹ =
      (ζ * n * ζ⁻¹ * n⁻¹) * (n * (ζ * m * ζ⁻¹ * m⁻¹) * n⁻¹) := by group
  change ζ * (n * m) * ζ⁻¹ * (n * m)⁻¹ ∈ Aa ↔
    (ζ * n * ζ⁻¹ * n⁻¹ ∈ Aa ↔ ζ * m * ζ⁻¹ * m⁻¹ ∈ Aa)
  rw [e]
  exact (mul_mem_Aa_iff W W2 hn.2.2 hhB).trans (iff_congr Iff.rfl hiff)

private lemma P.mul (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) {ζ n m : G}
    (hn : Good L A B ζ n) (hm : Good L A B ζ m) (hPn : P Aa ζ n) (hPm : P Aa ζ m) :
    P Aa ζ (n * m) :=
  (P.mul_iff W W2 hn hm).2 ⟨fun _ => hPm, fun _ => hPn⟩

private lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  have : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  exact this a h

private lemma Good.square (W : ThLocalIn L S A B z) {ζ n : G} (hn : Good L A B ζ n) :
    Good L A B ζ (n * n) :=
  Good.mul W hn hn

private lemma P.square (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) {ζ n : G}
    (hn : Good L A B ζ n) : P Aa ζ (n * n) :=
  (P.mul_iff W W2 hn hn).2 Iff.rfl

private lemma P.of_mem_B (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) {ζ β : G}
    (hζ : ζ ∈ S) (hβ : β ∈ B) : P Aa ζ β := by
  have h := W2.comm_mem_Aa W hβ hζ
  have e : ζ * β * ζ⁻¹ * β⁻¹ = (β * ζ * β⁻¹ * ζ⁻¹)⁻¹ := by group
  change ζ * β * ζ⁻¹ * β⁻¹ ∈ Aa
  rw [e]
  exact Aa.inv_mem h

private lemma Good.of_mem_B (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) {ζ β : G}
    (hζ : ζ ∈ S) (hβ : β ∈ B) : Good L A B ζ β := by
  refine ⟨W.B_le hβ, fun a ha => ?_, W2.Aa_le (P.of_mem_B W W2 hζ hβ)⟩
  have hc := (W.mem_B_iff β (W.B_le hβ)).1 hβ a ha
  have e : β * a * β⁻¹ = a := by
    calc β * a * β⁻¹ = a * β * β⁻¹ := by rw [hc]
      _ = a := by group
  rwa [e]

private lemma Good.of_isRep {c : G → (Fin 4 → ZMod 2)} (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hc : IsCoord A c) {ζ n : G} (hζ : ζ ∈ S)
    (hnL : n ∈ L) (hnA : ∀ a ∈ A, n * a * n⁻¹ ∈ A) (hζM : IsRep A c ζ E) {M : M4}
    (hnM : IsRep A c n M) (hcomm : E * M = M * E) : Good L A B ζ n := by
  have hζL : ζ ∈ L := W.S_le hζ
  have hζA : ∀ a ∈ A, ζ * a * ζ⁻¹ ∈ A := fun a ha => W.conj_mem_A_of_mem_S hζ ha
  have hζA' : ∀ a ∈ A, ζ⁻¹ * a * ζ ∈ A := fun a ha => conj_inv_mem_of_conj_mem hζA ha
  have hnA' : ∀ a ∈ A, n⁻¹ * a * n ∈ A := fun a ha => conj_inv_mem_of_conj_mem hnA ha
  have hζinv : IsRep A c ζ⁻¹ E⁻¹ := IsRep.inv hc hζM hζA
  have hninv : IsRep A c n⁻¹ M⁻¹ := IsRep.inv hc hnM hnA
  have h12 : IsRep A c (ζ * n) (E * M) := hζM.mul hnM hnA
  have h123 : IsRep A c (ζ * n * ζ⁻¹) ((E * M) * E⁻¹) :=
    h12.mul hζinv (fun a ha => by simpa using hζA' a ha)
  have h1234 : IsRep A c (ζ * n * ζ⁻¹ * n⁻¹) (((E * M) * E⁻¹) * M⁻¹) :=
    h123.mul hninv (fun a ha => by simpa using hnA' a ha)
  have hEinv : E⁻¹ = E := Matrix.inv_eq_right_inv E_mul_self
  have hMM : M * M⁻¹ = 1 := IsRep.mul_inv hc hnM hnA
  have hmat : (E * M) * E⁻¹ * M⁻¹ = 1 := by
    rw [hEinv]
    calc E * M * E * M⁻¹ = (M * E) * E * M⁻¹ := by rw [hcomm]
      _ = M * (E * E) * M⁻¹ := by simp only [Matrix.mul_assoc]
      _ = M * M⁻¹ := by rw [E_mul_self, Matrix.mul_one]
      _ = 1 := hMM
  have htriv : IsRep A c (ζ * n * ζ⁻¹ * n⁻¹) 1 := by
    have h := h1234
    rwa [hmat] at h
  have hcentral : ∀ a ∈ A, (ζ * n * ζ⁻¹ * n⁻¹) * a * (ζ * n * ζ⁻¹ * n⁻¹)⁻¹ = a := by
    intro a ha
    have hnorm : (ζ * n * ζ⁻¹ * n⁻¹) * a * (ζ * n * ζ⁻¹ * n⁻¹)⁻¹ ∈ A := by
      have e : (ζ * n * ζ⁻¹ * n⁻¹) * a * (ζ * n * ζ⁻¹ * n⁻¹)⁻¹ =
          ζ * (n * (ζ⁻¹ * (n⁻¹ * a * n) * ζ) * n⁻¹) * ζ⁻¹ := by group
      rw [e]
      exact hζA _ (hnA _ (hζA' _ (hnA' a ha)))
    exact hc.inj _ hnorm a ha (by rw [htriv a ha]; simp)
  have hcomm : ∀ a ∈ A, (ζ * n * ζ⁻¹ * n⁻¹) * a = a * (ζ * n * ζ⁻¹ * n⁻¹) := by
    intro a ha
    have h := hcentral a ha
    calc (ζ * n * ζ⁻¹ * n⁻¹) * a =
        ((ζ * n * ζ⁻¹ * n⁻¹) * a * (ζ * n * ζ⁻¹ * n⁻¹)⁻¹) *
          (ζ * n * ζ⁻¹ * n⁻¹) := by group
      _ = a * (ζ * n * ζ⁻¹ * n⁻¹) := by rw [h]
  have hmemL : ζ * n * ζ⁻¹ * n⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem (L.mul_mem hζL hnL) (L.inv_mem hζL)) (L.inv_mem hnL)
  exact ⟨hnL, hnA, (W.mem_B_iff _ hmemL).2 hcomm⟩

private lemma P.of_same_isRep {c : G → (Fin 4 → ZMod 2)} (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hc : IsCoord A c) {ζ s u : G} (hζ : ζ ∈ S)
    (hs : Good L A B ζ s) (hu : Good L A B ζ u) {M : M4} (hsM : IsRep A c s M)
    (huM : IsRep A c u M) : P Aa ζ s ↔ P Aa ζ u := by
  have hconj : ∀ a ∈ A, u⁻¹ * s * a * (u⁻¹ * s)⁻¹ = a := by
    intro a ha
    have e : s * a * s⁻¹ = u * a * u⁻¹ := IsRep.conj_mem hc hsM hs.2.1 hu.2.1 huM ha
    calc u⁻¹ * s * a * (u⁻¹ * s)⁻¹ = u⁻¹ * (s * a * s⁻¹) * u := by group
      _ = u⁻¹ * (u * a * u⁻¹) * u := by rw [e]
      _ = a := by group
  have hcomm : ∀ a ∈ A, (u⁻¹ * s) * a = a * (u⁻¹ * s) := by
    intro a ha
    have h := hconj a ha
    calc (u⁻¹ * s) * a =
        ((u⁻¹ * s) * a * (u⁻¹ * s)⁻¹) * (u⁻¹ * s) := by group
      _ = a * (u⁻¹ * s) := by rw [h]
  have hmemL : u⁻¹ * s ∈ L := L.mul_mem (L.inv_mem hu.1) hs.1
  have hbeta : u⁻¹ * s ∈ B := (W.mem_B_iff _ hmemL).2 hcomm
  have hbetagood : Good L A B ζ (u⁻¹ * s) := Good.of_mem_B W W2 hζ hbeta
  have hbetaP : P Aa ζ (u⁻¹ * s) := P.of_mem_B W W2 hζ hbeta
  have hs_eq : s = u * (u⁻¹ * s) := by group
  rw [hs_eq, P.mul_iff W W2 hu hbetagood]
  simp [hbetaP]

private lemma lift_coeff {c : G → (Fin 4 → ZMod 2)} {i j : Fin 4} {ζ n : G}
    (hn : Good L A B ζ n) (hPn : P Aa ζ n)
    (hnM : IsRep A c n (1 + Matrix.single i j 1)) (a : ZMod 2) :
    ∃ u : G, Good L A B ζ u ∧ P Aa ζ u ∧ IsRep A c u (1 + Matrix.single i j a) := by
  by_cases h : a = 0
  · refine ⟨1, Good.one L A B ζ, P.one Aa ζ, ?_⟩
    simpa [h] using IsRep.one
  · have ha : a = 1 := zmod2_eq_one_of_ne_zero h
    exact ⟨n, hn, hPn, by rwa [ha]⟩


private lemma P_of_mem_S (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    {c : G → (Fin 4 → ZMod 2)} (hc : IsCoord A c)
    (hS : ∀ s ∈ S, ∃ g ∈ CFSG.Quasithin.FFC.UT 4,
      IsRep A c s (g : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    {ζ y : G} (hζ : ζ ∈ S) (hy : y ∈ S) (hζM : IsRep A c ζ E)
    (hyM : IsRep A c y (1 + Matrix.single 1 2 1)) (hPy : P Aa ζ y)
    {s : G} (hs : s ∈ S) : P Aa ζ s := by
  have hζL : ζ ∈ L := W.S_le hζ
  have hyL : y ∈ L := W.S_le hy
  have hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A := fun a ha => W.conj_mem_A_of_mem_S hy ha
  have hyGood : Good L A B ζ y :=
    Good.of_isRep W W2 hc hζ hyL hyA hζM hyM E_comm_X12
  have hXinj : ∀ (i j : Fin 4) (hij : i ≠ j), Function.Injective (X i j 1).mulVec :=
    fun i j hij => Matrix.mulVec_injective_iff_isUnit.mpr
      (IsUnit.of_mul_eq_one (X i j 1) (X_mul_self hij 1))
  obtain ⟨n01, hn01L, hn01A, hn01M⟩ := hc.exists_lift W.surj (hXinj 0 1 (by decide))
  obtain ⟨n21, hn21L, hn21A, hn21M⟩ := hc.exists_lift W.surj (hXinj 2 1 (by decide))
  obtain ⟨n23, hn23L, hn23A, hn23M⟩ := hc.exists_lift W.surj (hXinj 2 3 (by decide))
  have hn01Good : Good L A B ζ n01 :=
    Good.of_isRep W W2 hc hζ hn01L hn01A hζM hn01M E_comm_X01
  have hn21Good : Good L A B ζ n21 :=
    Good.of_isRep W W2 hc hζ hn21L hn21A hζM hn21M E_comm_X21
  have hn23Good : Good L A B ζ n23 :=
    Good.of_isRep W W2 hc hζ hn23L hn23A hζM hn23M E_comm_X23
  let n02 : G := (n01 * y) * (n01 * y)
  have hn02Good : Good L A B ζ n02 := Good.square W (Good.mul W hn01Good hyGood)
  have hn02P : P Aa ζ n02 := P.square W W2 (Good.mul W hn01Good hyGood)
  have hn02M : IsRep A c n02 (X 0 2 1) := by
    have h : IsRep A c (n01 * y) (X 0 1 1 * X 1 2 1) := hn01M.mul hyM hyA
    have h2 : IsRep A c n02 ((X 0 1 1 * X 1 2 1) * (X 0 1 1 * X 1 2 1)) :=
      h.mul h (Good.mul W hn01Good hyGood).2.1
    simpa [n02, X02_eq] using h2
  let n13 : G := (y * n23) * (y * n23)
  have hn13Good : Good L A B ζ n13 := Good.square W (Good.mul W hyGood hn23Good)
  have hn13P : P Aa ζ n13 := P.square W W2 (Good.mul W hyGood hn23Good)
  have hn13M : IsRep A c n13 (X 1 3 1) := by
    have h : IsRep A c (y * n23) (X 1 2 1 * X 2 3 1) := hyM.mul hn23M hn23A
    have h2 : IsRep A c n13 ((X 1 2 1 * X 2 3 1) * (X 1 2 1 * X 2 3 1)) :=
      h.mul h (Good.mul W hyGood hn23Good).2.1
    simpa [n13, X13_eq] using h2
  let n03 : G := (n01 * n13) * (n01 * n13)
  have hn03Good : Good L A B ζ n03 := Good.square W (Good.mul W hn01Good hn13Good)
  have hn03P : P Aa ζ n03 := P.square W W2 (Good.mul W hn01Good hn13Good)
  have hn03M : IsRep A c n03 (X 0 3 1) := by
    have h : IsRep A c (n01 * n13) (X 0 1 1 * X 1 3 1) :=
      hn01M.mul hn13M hn13Good.2.1
    have h2 : IsRep A c n03 ((X 0 1 1 * X 1 3 1) * (X 0 1 1 * X 1 3 1)) :=
      h.mul h (Good.mul W hn01Good hn13Good).2.1
    simpa [n03, X03_eq] using h2
  let n01' : G := (n02 * n21) * (n02 * n21)
  have hn01'Good : Good L A B ζ n01' := Good.square W (Good.mul W hn02Good hn21Good)
  have hn01'P : P Aa ζ n01' := P.square W W2 (Good.mul W hn02Good hn21Good)
  have hn01'M : IsRep A c n01' (X 0 1 1) := by
    have h : IsRep A c (n02 * n21) (X 0 2 1 * X 2 1 1) := hn02M.mul hn21M hn21A
    have h2 : IsRep A c n01' ((X 0 2 1 * X 2 1 1) * (X 0 2 1 * X 2 1 1)) :=
      h.mul h (Good.mul W hn02Good hn21Good).2.1
    simpa [n01', X01_eq] using h2
  let n23' : G := (n21 * n13) * (n21 * n13)
  have hn23'Good : Good L A B ζ n23' := Good.square W (Good.mul W hn21Good hn13Good)
  have hn23'P : P Aa ζ n23' := P.square W W2 (Good.mul W hn21Good hn13Good)
  have hn23'M : IsRep A c n23' (X 2 3 1) := by
    have h : IsRep A c (n21 * n13) (X 2 1 1 * X 1 3 1) :=
      hn21M.mul hn13M hn13Good.2.1
    have h2 : IsRep A c n23' ((X 2 1 1 * X 1 3 1) * (X 2 1 1 * X 1 3 1)) :=
      h.mul h (Good.mul W hn21Good hn13Good).2.1
    simpa [n23', X23_eq] using h2
  obtain ⟨g, hgUT, hgM⟩ := hS s hs
  let M : M4 := (g : Matrix (Fin 4) (Fin 4) (ZMod 2))
  have hgM' : IsRep A c s M := hgM
  have hM : ∀ i j : Fin 4, j < i → M i j = 0 := CFSG.Quasithin.FFC.mem_UT.1 hgUT
  have hd : ∀ i : Fin 4, M i i = 1 := CFSG.Quasithin.FFC.UT_diag hgUT
  let a01 : ZMod 2 := M 0 1
  let a12 : ZMod 2 := M 1 2
  let a23 : ZMod 2 := M 2 3
  let a02 : ZMod 2 := M 0 2 + M 0 1 * M 1 2
  let a13 : ZMod 2 := M 1 3 + M 1 2 * M 2 3
  let a03 : ZMod 2 := M 0 3 + M 0 1 * M 1 2 * M 2 3 +
    M 0 1 * (M 1 3 + M 1 2 * M 2 3)
  let F01 : M4 := 1 + Matrix.single 0 1 a01
  let F12 : M4 := 1 + Matrix.single 1 2 a12
  let F23 : M4 := 1 + Matrix.single 2 3 a23
  let F02 : M4 := 1 + Matrix.single 0 2 a02
  let F13 : M4 := 1 + Matrix.single 1 3 a13
  let F03 : M4 := 1 + Matrix.single 0 3 a03
  have hfac : M = F01 * F12 * F23 * F02 * F13 * F03 := by
    dsimp only [F01, F12, F23, F02, F13, F03]
    simpa [a01, a12, a23, a02, a13, a03] using ut_factor hM hd
  obtain ⟨v01, hv01Good, hv01P, hv01M⟩ := lift_coeff hn01'Good hn01'P hn01'M a01
  obtain ⟨v12, hv12Good, hv12P, hv12M⟩ := lift_coeff hyGood hPy hyM a12
  obtain ⟨v23, hv23Good, hv23P, hv23M⟩ := lift_coeff hn23'Good hn23'P hn23'M a23
  obtain ⟨v02, hv02Good, hv02P, hv02M⟩ := lift_coeff hn02Good hn02P hn02M a02
  obtain ⟨v13, hv13Good, hv13P, hv13M⟩ := lift_coeff hn13Good hn13P hn13M a13
  obtain ⟨v03, hv03Good, hv03P, hv03M⟩ := lift_coeff hn03Good hn03P hn03M a03
  have hv01MF : IsRep A c v01 F01 := hv01M
  have hv12MF : IsRep A c v12 F12 := hv12M
  have hv23MF : IsRep A c v23 F23 := hv23M
  have hv02MF : IsRep A c v02 F02 := hv02M
  have hv13MF : IsRep A c v13 F13 := hv13M
  have hv03MF : IsRep A c v03 F03 := hv03M
  let u : G := v01 * v12 * v23 * v02 * v13 * v03
  have hg1 : Good L A B ζ (v01 * v12) := Good.mul W hv01Good hv12Good
  have hg2 : Good L A B ζ (v01 * v12 * v23) := Good.mul W hg1 hv23Good
  have hg3 : Good L A B ζ (v01 * v12 * v23 * v02) := Good.mul W hg2 hv02Good
  have hg4 : Good L A B ζ (v01 * v12 * v23 * v02 * v13) := Good.mul W hg3 hv13Good
  have huGood : Good L A B ζ u := by
    dsimp only [u]
    exact Good.mul W hg4 hv03Good
  have hp1 : P Aa ζ (v01 * v12) := P.mul W W2 hv01Good hv12Good hv01P hv12P
  have hp2 : P Aa ζ (v01 * v12 * v23) := P.mul W W2 hg1 hv23Good hp1 hv23P
  have hp3 : P Aa ζ (v01 * v12 * v23 * v02) := P.mul W W2 hg2 hv02Good hp2 hv02P
  have hp4 : P Aa ζ (v01 * v12 * v23 * v02 * v13) := P.mul W W2 hg3 hv13Good hp3 hv13P
  have huP : P Aa ζ u := by
    dsimp only [u]
    exact P.mul W W2 hg4 hv03Good hp4 hv03P
  have huM : IsRep A c u M := by
    dsimp only [u]
    have h1 : IsRep A c (v01 * v12) (F01 * F12) := hv01MF.mul hv12MF hv12Good.2.1
    have h2 : IsRep A c (v01 * v12 * v23) ((F01 * F12) * F23) :=
      h1.mul hv23MF hv23Good.2.1
    have h3 : IsRep A c (v01 * v12 * v23 * v02) (((F01 * F12) * F23) * F02) :=
      h2.mul hv02MF hv02Good.2.1
    have h4 : IsRep A c (v01 * v12 * v23 * v02 * v13)
        ((((F01 * F12) * F23) * F02) * F13) := h3.mul hv13MF hv13Good.2.1
    have h5 : IsRep A c (v01 * v12 * v23 * v02 * v13 * v03)
        (((((F01 * F12) * F23) * F02) * F13) * F03) :=
      h4.mul hv03MF hv03Good.2.1
    rwa [← hfac] at h5
  have hsGood : Good L A B ζ s :=
    Good.of_isRep W W2 hc hζ (W.S_le hs) (fun a ha => W.conj_mem_A_of_mem_S hs ha)
      hζM hgM' (E_comm_ut hM hd)
  exact (P.of_same_isRep W W2 hc hζ hsGood huGood hgM' huM).2 huP

theorem ThLocalIn2.comm_mem_B_not_mem_Aa (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (F : SylowFacts L S B Aa) {c : G → (Fin 4 → ZMod 2)} (hc : IsCoord A c)
    (hS : ∀ s ∈ S, ∃ g ∈ CFSG.Quasithin.FFC.UT 4,
      IsRep A c s (g : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    {ζ y : G} (hζ : ζ ∈ S) (hy : y ∈ S) (hζM : IsRep A c ζ (1 + Matrix.single 0 3 1))
    (hyM : IsRep A c y (1 + Matrix.single 1 2 1)) :
    ζ * y * ζ⁻¹ * y⁻¹ ∈ B ∧ ζ * y * ζ⁻¹ * y⁻¹ ∉ Aa := by
  have hζL : ζ ∈ L := W.S_le hζ
  have hyL : y ∈ L := W.S_le hy
  have hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A := fun a ha => W.conj_mem_A_of_mem_S hy ha
  have hyGood : Good L A B ζ y :=
    Good.of_isRep W W2 hc hζ hyL hyA hζM hyM E_comm_X12
  refine ⟨hyGood.2.2, ?_⟩
  intro hyP
  have hPall : ∀ s ∈ S, P Aa ζ s := fun s hs =>
    P_of_mem_S W W2 hc hS hζ hy hζM hyM hyP hs
  have hζB : ζ ∈ B := F.center_quotient ζ hζ hPall
  have hζcent : ∀ a ∈ A, ζ * a = a * ζ := (W.mem_B_iff ζ hζL).1 hζB
  have hζone : IsRep A c ζ 1 := by
    intro a ha
    have e : ζ * a * ζ⁻¹ = a := by
      rw [hζcent a ha]
      group
    rw [e]
    simp
  exact E_ne_one (hc.rep_unique hζM hζone)

end CFSG.EvenSporadicStandard.ThStd
