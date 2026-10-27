module

public import CFSG.HardMathSupport.U4FF.ClassDatumOpp
public import CFSG.HardMathSupport.U4FF.ClassDatumCount
public import CFSG.Quasithin.Background.SmithCurtisHecke

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.Quasithin.SmithCurtis (heckeDeg)

namespace Datum

section Hecke

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem card_conj_inf (g : G4 K n) :
    Nat.card ↥((UpperU K n).map (MulAut.conj g).toMonoidHom ⊓ UpperU K n) =
      Nat.card {u : ↥(UpperU K n) // g⁻¹ * (u : G4 K n) * g ∈ UpperU K n} := by
  have e1 := Equiv.subtypeSubtypeEquivSubtypeInter (fun x : G4 K n => x ∈ UpperU K n)
    (fun x => g⁻¹ * x * g ∈ UpperU K n)
  rw [Nat.card_congr e1]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hx⟩
    refine ⟨hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [this]
    exact hy
  · rintro ⟨hx, h⟩
    refine ⟨⟨g⁻¹ * x * g, h, ?_⟩, hx⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem heckeDeg_mul_card_conj (g : G4 K n) :
    heckeDeg (UpperU K n) g * Nat.card {u : ↥(UpperU K n) // g⁻¹ * (u : G4 K n) * g ∈ UpperU K n} =
      Nat.card ↥(UpperU K n) := by
  rw [← card_conj_inf]
  exact Subgroup.relIndex_mul_card _ _

theorem upMat_eq (hK : Nat.card K = (2 ^ n) ^ 2) (u : ↥(UpperU K n)) :
    upMat u = wMat n (paramW u).1 (paramW u).2.1 (paramW u).2.2.1 (paramW u).2.2.2 := by
  obtain ⟨a, b, c, d, -, h⟩ :=
    exists_wCond_of_mem n hK (u : SU (unitaryInvolution K 2 n) 4).2 (mem_UpperU.mp u.2)
  have hu : upMat u = wMat n a b c d := h
  have hp : paramW u = (a, b, c, d) := by
    simp [paramW, hu, wMat]
  rw [hp]
  exact hu

@[expose] def permVal : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 2, 1, 3], ![1, 3, 0, 2], ![2, 0, 3, 1], ![3, 1, 2, 0],
    ![2, 3, 0, 1], ![3, 2, 1, 0]]

theorem permTab_apply : ∀ (i : Fin 8) (a : Fin 4), permTab i a = permVal i a := by decide

theorem forall_lt_four {P : Fin 4 → Fin 4 → Prop} :
    (∀ a b, b < a → P a b) ↔ P 1 0 ∧ P 2 0 ∧ P 2 1 ∧ P 3 0 ∧ P 3 1 ∧ P 3 2 := by
  constructor
  · intro h
    exact ⟨h 1 0 (by decide), h 2 0 (by decide), h 2 1 (by decide), h 3 0 (by decide),
      h 3 1 (by decide), h 3 2 (by decide)⟩
  · rintro ⟨h10, h20, h21, h30, h31, h32⟩ a b hba
    fin_cases a <;> fin_cases b <;> first | exact absurd hba (by decide) | assumption

theorem wMat_diag (n : ℕ) (a b c d : K) (x : Fin 4) : wMat n a b c d x x = 1 := by
  fin_cases x <;> simp [wMat]

theorem pat_iff (i : Fin 8) (a b c d : K) :
    (∀ x y : Fin 4, y < x → wMat n a b c d (permVal i x) (permVal i y) = 0) ↔
      patK i (a, b, c, d) := by
  have hq : (2 : ℕ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  rw [forall_lt_four]
  fin_cases i <;> simp [permVal, patK, wMat, hq] <;>
    first
    | tauto
    | (constructor <;> intro h <;> simp_all [zero_pow hq])
    | (intros; simp_all [zero_pow hq])

theorem conj_mem_U_iff_patK (hK : Nat.card K = (2 ^ n) ^ 2) (i : Fin 8) (u : ↥(UpperU K n)) :
    (nHom K n (wTab i))⁻¹ * (u : G4 K n) * nHom K n (wTab i) ∈ UpperU K n ↔
      patK i (paramW u) := by
  have hentry : ∀ a b, gm ((nHom K n (wTab i))⁻¹ * (u : G4 K n) * nHom K n (wTab i)) a b =
      wMat n (paramW u).1 (paramW u).2.1 (paramW u).2.2.1 (paramW u).2.2.2
        (permVal i a) (permVal i b) := by
    intro a b
    rw [gm_nHom_conj_inv, permOf_wTab, permTab_apply, permTab_apply]
    have : gm (u : G4 K n) = upMat u := rfl
    rw [this, upMat_eq hK u]
  rw [mem_UpperU']
  have h2 : IsUpperUni (gm ((nHom K n (wTab i))⁻¹ * (u : G4 K n) * nHom K n (wTab i))) ↔
      ∀ x y : Fin 4, y < x → wMat n (paramW u).1 (paramW u).2.1 (paramW u).2.2.1
        (paramW u).2.2.2 (permVal i x) (permVal i y) = 0 := by
    constructor
    · intro h x y hxy
      rw [← hentry]
      exact h.1 x y hxy
    · intro h
      refine ⟨fun x y hxy => ?_, fun x => ?_⟩
      · rw [hentry]
        exact h x y hxy
      · rw [hentry]
        exact wMat_diag _ _ _ _ _ _
  rw [h2]
  exact pat_iff i _ _ _ _

@[expose] def eTab : Fin 8 → ℕ := ![0, 2, 1, 3, 3, 5, 4, 6]

theorem eTab_add_cntTab : ∀ i : Fin 8, eTab i + cntTab i = 6 := by decide

theorem eTab_mul : ∀ (s : Fin 2) (j : Fin 8), lenTab (lmulTab s j) = lenTab j + 1 →
    eTab (![1, 2] s) + eTab j = eTab (lmulTab s j) := by decide

theorem heckeDeg_nHom_wTab (hK : Nat.card K = (2 ^ n) ^ 2) (i : Fin 8) :
    heckeDeg (UpperU K n) (nHom K n (wTab i)) = (2 ^ n) ^ eTab i := by
  have h1 := heckeDeg_mul_card_conj (nHom K n (wTab i))
  have hcard : Nat.card {u : ↥(UpperU K n) //
      (nHom K n (wTab i))⁻¹ * (u : G4 K n) * nHom K n (wTab i) ∈ UpperU K n} =
      (2 ^ n) ^ cntTab i := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun u => conj_mem_U_iff_patK hK i u))]
    exact card_UpperU_patK hK i
  rw [hcard, card_UpperU hK] at h1
  have hpos : 0 < (2 ^ n) ^ cntTab i := by positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1, ← pow_add, eTab_add_cntTab]

theorem simple_eq_wTab (s : Fin 2) : csB.simple s = wTab (![1, 2] s) := by
  fin_cases s <;> rfl

theorem heckeDeg_mul_G4 (hK : Nat.card K = (2 ^ n) ^ 2) (w : WB) (s : Fin 2)
    (h : csB.length (csB.simple s * w) = csB.length w + 1) :
    heckeDeg (UpperU K n) (nSimple K n s) * heckeDeg (UpperU K n) (nHom K n w) =
      heckeDeg (UpperU K n) (nHom K n (csB.simple s * w)) := by
  obtain ⟨j, rfl⟩ := exists_wTab w
  rw [simple_mul_wTab] at h ⊢
  rw [length_wTab, length_wTab] at h
  have hs : nSimple K n s = nHom K n (wTab (![1, 2] s)) := by
    rw [nSimple, simple_eq_wTab]
  rw [hs, heckeDeg_nHom_wTab hK, heckeDeg_nHom_wTab hK, heckeDeg_nHom_wTab hK, ← pow_add]
  rw [eTab_mul s j h]

end Hecke

end Datum

end CFSG.HardMathSupport.U4FF
