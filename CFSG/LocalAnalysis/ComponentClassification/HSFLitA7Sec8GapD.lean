module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapAut
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapQS

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open scoped Matrix

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

@[expose] def qxOf (S : A7Base X) (x : X) : X := S.t⁻¹ * x * S.t * x⁻¹

theorem conj_t_eq (x : X) : x * S.t * x⁻¹ = S.t * qxOf S x := by
  rw [qxOf]; group

theorem BData.mat_inv (A : BData S F T₁) (n : A.NA) {M : Matrix (Fin 3) (Fin 3) (ZMod 4)}
    (hM : A.mat n = M) (hMM : M * M = 1) : A.mat n⁻¹ = M := by
  have h1 : A.mat n⁻¹ * A.mat n = 1 := by rw [← A.mat_mul, inv_mul_cancel, A.mat_one]
  calc A.mat n⁻¹ = A.mat n⁻¹ * (M * M) := by rw [hMM, mul_one]
    _ = M := by rw [← hM, ← mul_assoc, h1, one_mul]

namespace BData.Syl

variable {A : BData S F T₁} (Y : A.Syl)

theorem qx_mem_Q {x : X} (hx : x ∈ Y.P) : qxOf S x ∈ Y.Q := by
  refine mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem (inv_mem Y.t_mem) hx) Y.t_mem) (inv_mem hx),
    ?_⟩
  set x' : A.NA := ⟨x, Y.mem_NA hx⟩
  set t' : A.NA := ⟨S.t, A.t_mem_NA⟩
  have hq : qxOf S x = ((t'⁻¹ * x' * t' * x'⁻¹ : A.NA) : X) := rfl
  rw [hq, ← A.mat_eq_one_iff, A.mat_mul, A.mat_mul, A.mat_mul,
    A.mat_inv t' A.mat_t (by simp), A.mat_t]
  rw [show -1 * A.mat x' * -1 * A.mat x'⁻¹ = A.mat x' * A.mat x'⁻¹ by simp, ← A.mat_mul,
    mul_inv_cancel, A.mat_one]

theorem conj_mem_Q {x : X} (hx : x ∈ Y.P) {q : X} (hq : q ∈ Y.Q) : x * q * x⁻¹ ∈ Y.Q := by
  refine mem_inf.mpr ⟨mul_mem (mul_mem hx (mem_inf.mp hq).1) (inv_mem hx), ?_⟩
  rw [mem_centralizer_iff]
  intro a ha
  have ha' : x⁻¹ * a * x ∈ A.AA := by
    have := A.conj_mem_AA (inv_mem (Y.mem_NA hx)) ha
    rwa [inv_inv] at this
  have := (mem_centralizer_iff.mp (mem_inf.mp hq).2) _ ha'
  calc a * (x * q * x⁻¹) = x * ((x⁻¹ * a * x) * q) * x⁻¹ := by group
    _ = x * (q * (x⁻¹ * a * x)) * x⁻¹ := by rw [this]
    _ = x * q * x⁻¹ * a := by group

@[expose] def InVQ2 (q : X) : Prop := ∃ w ∈ A.VV, ∃ q₁ ∈ Y.Q, q = w * q₁ ^ 2

theorem mem_QS₁_of_qx (hnc : ¬ SubConj F.E₁ F.E₂) {x : X} (hx : x ∈ Y.P)
    (hq : Y.InVQ2 (qxOf S x)) : ∃ q ∈ Y.Q, q * x ∈ A.D₁.S₁ := by
  obtain ⟨w, hw, q₁, hq₁, he⟩ := hq
  have ht' : S.t⁻¹ = S.t := by rw [inv_eq_iff_mul_eq_one, t_mul_t]
  have hwQ : w ∈ Y.Q := (A.VV_le_AA.trans Y.AA_le_Q) hw
  have hψ := Y.psi_mem_E0 hnc hq₁
  set ψ := S.t * q₁ * S.t⁻¹ * q₁ with hψdef
  have hψQ : ψ ∈ Y.Q := mul_mem (Y.t_conj_mem_Q hq₁) hq₁
  have key : (q₁ * x) * S.t * (q₁ * x)⁻¹ = S.t * (ψ * w) := by
    have h1 : x * S.t * x⁻¹ = S.t * (w * q₁ ^ 2) := by rw [conj_t_eq, he]
    have h2 : q₁ * S.t * q₁⁻¹ = S.t * ψ * q₁⁻¹ * q₁⁻¹ := by
      rw [hψdef, ht']
      calc q₁ * S.t * q₁⁻¹ = (S.t * S.t) * q₁ * S.t * q₁⁻¹ := by rw [t_mul_t, one_mul]
        _ = S.t * (S.t * q₁ * S.t * q₁) * q₁⁻¹ * q₁⁻¹ := by group
    have hc1 : ∀ a ∈ Y.Q, ∀ b ∈ Y.Q, a * b = b * a := fun a ha b hb => Y.Q_comm hnc ha hb
    calc (q₁ * x) * S.t * (q₁ * x)⁻¹ = q₁ * (x * S.t * x⁻¹) * q₁⁻¹ := by group
      _ = (q₁ * S.t * q₁⁻¹) * (q₁ * (w * q₁ ^ 2) * q₁⁻¹) := by rw [h1]; group
      _ = (S.t * ψ * q₁⁻¹ * q₁⁻¹) * (w * q₁ ^ 2) := by
          rw [h2, show q₁ * (w * q₁ ^ 2) * q₁⁻¹ = w * q₁ ^ 2 by
            rw [hc1 _ hq₁ _ (mul_mem hwQ (pow_mem hq₁ 2)), mul_inv_cancel_right]]
      _ = S.t * ψ * (q₁⁻¹ * q₁⁻¹ * w * q₁ ^ 2) := by group
      _ = S.t * ψ * w := by
          have hwq : w * q₁ = q₁ * w := hc1 _ hwQ _ hq₁
          calc S.t * ψ * (q₁⁻¹ * q₁⁻¹ * w * q₁ ^ 2)
              = S.t * ψ * (q₁⁻¹ * q₁⁻¹ * (w * q₁) * q₁) := by rw [pow_two]; group
            _ = S.t * ψ * (q₁⁻¹ * q₁⁻¹ * (q₁ * w) * q₁) := by rw [hwq]
            _ = S.t * ψ * (q₁⁻¹ * (w * q₁)) := by group
            _ = S.t * ψ * (q₁⁻¹ * (q₁ * w)) := by rw [hwq]
            _ = S.t * ψ * w := by group
      _ = S.t * (ψ * w) := by group
  obtain ⟨e, he2, hee⟩ := A.exists_of_mem_E0 hψ
  obtain ⟨v, hv2, hvv⟩ := hw
  have hcoord : ψ * w = A.Φ (e + v) := by rw [A.Φ_add, hee, hvv]
  have hx' : q₁ * x ∈ A.NA := mul_mem (Y.mem_NA hq₁.1) (Y.mem_NA hx)
  have hmap := A.map_E₁ ⟨q₁ * x, hx'⟩ (by rw [key, hcoord])
  by_cases h01 : 2 * (e + v) 0 = 0 ∧ 2 * (e + v) 1 = 0
  · refine ⟨q₁, hq₁, Y.mem_S₁_of_normalizes (mul_mem hq₁.1 hx) ?_⟩
    have hev : ∀ i, 2 * (e + v) i = 0 := by
      intro i; fin_cases i
      · exact h01.1
      · exact h01.2
      · simp only [Pi.add_apply, Fin.reduceFinMk, Fin.isValue, hv2, add_zero]
        exact he2 2
    rw [show A.Φ (e + v) = 1 * A.Φ (e + v) by rw [one_mul],
      E0t_mul (A.Φ_mem_E0 hev), ← A.E₁_eq_E0t] at hmap
    rw [mem_normalizer_iff]
    intro g
    constructor
    · intro hg; rw [← hmap]; exact ⟨g, hg, rfl⟩
    · intro hg
      rw [← hmap] at hg
      obtain ⟨g', hg', hgg⟩ := hg
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hgg
      have : g' = g := by
        have := congrArg (fun y => (q₁ * x)⁻¹ * y * (q₁ * x)) hgg
        simpa [mul_assoc] using this
      rwa [← this]
  · exfalso
    have h2 : 2 * (e + v) 2 = 0 := by
      simp only [Pi.add_apply, hv2, add_zero]; exact he2 2
    exact A.not_conj_E0t hnc h2 h01 hmap

end BData.Syl

end Sec8

end CFSG.ComponentClassification.HSFLit
