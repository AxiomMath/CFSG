module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import Certificates.Data.KFCub2

public section

namespace CFSG.SectionRank

open CFSG.Blueprint CFSG.SectionRank.Native
open scoped Matrix commutatorElement
open LocalWitness

namespace OpsSpec

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem cub2_of_check [Inhabited M] [Inhabited V] (D : Cub2Data) (h : O.cub2Check D = true) :
    ∃ x y g₁ g₂ : (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ,
      x ^ D.r = 1 ∧ y ^ D.r = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      g₁ * x * g₁⁻¹ = x ^ D.h1.a * y ^ D.h1.b * ⁅x, y⁆ ^ D.h1.k ∧
      g₁ * y * g₁⁻¹ = x ^ D.h1.c * y ^ D.h1.d * ⁅x, y⁆ ^ D.h1.l ∧
      g₂ * x * g₂⁻¹ = x ^ D.h2.a * y ^ D.h2.b * ⁅x, y⁆ ^ D.h2.k ∧
      g₂ * y * g₂⁻¹ = x ^ D.h2.c * y ^ D.h2.d * ⁅x, y⁆ ^ D.h2.l := by
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB
  unfold Ops.cub2Check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hprog⟩, hrx⟩, hry⟩, hr⟩, hXr⟩, hYr⟩, hZt⟩, hZX⟩, hZY⟩, hN1⟩, hN2⟩ := h
  set R := O.regsOf D.seedA D.seedB D.nregs D.prog
  obtain ⟨wX, mX⟩ := Sp.regsOf_ok hprog hrx
  obtain ⟨wY, mY⟩ := Sp.regsOf_ok hprog hry
  have eX := Sp.pow_eq_one_of_check wX hXr
  have eY := Sp.pow_eq_one_of_check wY hYr
  let x := unitOf S mX hr.ne' eX
  let y := unitOf S mY hr.ne' eY
  have fx : valHom S x = Sp.toMat R[D.rx]! := valHom_unitOf S _ _ _
  have fy : valHom S y = Sp.toMat R[D.ry]! := valHom_unitOf S _ _ _
  have hx : x ^ D.r = 1 := unitOf_pow S mX _ eX
  have hy : y ^ D.r = 1 := unitOf_pow S mY _ eY
  set Z := O.commM D.r R[D.rx]! R[D.ry]!
  have wZ : Sp.WF Z := Sp.commM_wf wX wY D.r
  have fz : valHom S ⁅x, y⁆ = Sp.toMat Z := Sp.valHom_commutator hr hx hy wX wY fx fy
  have comm : ∀ {u : Sˣ} {U : M}, Sp.WF U → valHom S u = Sp.toMat U →
      O.eq (O.mul Z U) (O.mul U Z) = true → Commute ⁅x, y⁆ u := by
    intro u U hU hu hc
    apply valHom_injective S
    rw [map_mul, map_mul, fz, hu]
    have := Sp.toMat_eq (Sp.mul_wf wZ hU) (Sp.mul_wf hU wZ) hc
    rwa [Sp.toMat_mul wZ hU, Sp.toMat_mul hU wZ] at this
  have word : ∀ i j k : ℕ, Sp.WF (O.mul (O.mul (O.pow R[D.rx]! i) (O.pow R[D.ry]! j))
        (O.pow Z k)) ∧ valHom S (x ^ i * y ^ j * ⁅x, y⁆ ^ k) = Sp.toMat (O.mul (O.mul
          (O.pow R[D.rx]! i) (O.pow R[D.ry]! j)) (O.pow Z k)) := by
    intro i j k
    have w1 := Sp.mul_wf (Sp.pow_spec wX i).1 (Sp.pow_spec wY j).1
    refine ⟨Sp.mul_wf w1 (Sp.pow_spec wZ k).1, ?_⟩
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, fx, fy, fz,
      Sp.toMat_mul w1 (Sp.pow_spec wZ k).1, Sp.toMat_mul (Sp.pow_spec wX i).1 (Sp.pow_spec wY j).1,
      (Sp.pow_spec wX i).2, (Sp.pow_spec wY j).2, (Sp.pow_spec wZ k).2]
  have mkH : ∀ N : Cub2NormData, O.normOK N D.nregs R R[D.rx]! R[D.ry]! Z = true →
      ∃ g : Sˣ, g * x * g⁻¹ = x ^ N.a * y ^ N.b * ⁅x, y⁆ ^ N.k ∧
        g * y * g⁻¹ = x ^ N.c * y ^ N.d * ⁅x, y⁆ ^ N.l := by
    intro N hN
    unfold Ops.normOK at hN
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hN
    obtain ⟨⟨⟨⟨hrh, hoh⟩, hHo⟩, hHX⟩, hHY⟩ := hN
    obtain ⟨wH, mH⟩ := Sp.regsOf_ok hprog hrh
    have eH := Sp.pow_eq_one_of_check wH hHo
    let g := unitOf S mH hoh.ne' eH
    have fg : valHom S g = Sp.toMat R[N.rh]! := valHom_unitOf S _ _ _
    have conj : ∀ {w : Sˣ} {W : M}, Sp.WF W → valHom S w = Sp.toMat W → ∀ {u : Sˣ} {U : M},
        Sp.WF U → valHom S u = Sp.toMat U → O.conjOK R[N.rh]! U W = true → g * u * g⁻¹ = w := by
      intro w W hW hw u U hU hu hc
      rw [mul_inv_eq_iff_eq_mul]
      apply valHom_injective S
      rw [map_mul, map_mul, fg, hu, hw]
      exact Sp.toMat_of_conjOK wH hU hW hc
    exact ⟨g, conj (word _ _ _).1 (word _ _ _).2 wX fx hHX,
      conj (word _ _ _).1 (word _ _ _).2 wY fy hHY⟩
  have hz1 : ⁅x, y⁆ ≠ 1 := by
    intro h1
    apply Sp.toVec_ne hZt
    rw [Sp.toVec_vmul (Sp.unit_wf _) wZ, ← fz, h1, map_one, Matrix.vecMul_one]
  obtain ⟨g₁, hg₁x, hg₁y⟩ := mkH D.h1 hN1
  obtain ⟨g₂, hg₂x, hg₂y⟩ := mkH D.h2 hN2
  exact ⟨x, y, g₁, g₂, hx, hy, hz1, comm wX fx hZX, comm wY fy hZY, hg₁x, hg₁y, hg₂x, hg₂y⟩

end OpsSpec

end CFSG.SectionRank
