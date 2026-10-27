module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46T
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8cV

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv

namespace KD8c

open KD7 KD8ab SD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}

theorem card_H8_le : Nat.card H8 ≤ 32 := by
  have hs : Function.Surjective (fun p : (ZMod 8)ˣ × ZMod 8 =>
      (⟨aff8 p.1 p.2, aff8_mem_H8 p.1 p.2⟩ : H8)) := by
    rintro ⟨g, u, b, rfl⟩
    exact ⟨(u, b), rfl⟩
  calc Nat.card H8 ≤ Nat.card ((ZMod 8)ˣ × ZMod 8) := Nat.card_le_card_of_surjective _ hs
    _ = 32 := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        ZMod.card_units_eq_totient, ZMod.card]
      decide

omit [Finite X] in
theorem card_T_le (C : A.CaseKD) : Nat.card A.T ≤ 64 := by
  rw [A.card_T_eq, C.card_K]
  have := (Subgroup.card_le_of_le A.range_le_H8).trans card_H8_le
  omega

theorem exists_conj_eq_T (C : A.CaseKD) {h : X} (hconj : ConjTo t h) {P : Subgroup X}
    (hP : IsPGroup 2 P) (hPC : P ≤ centralizer ({h} : Set X)) (hcard : 64 ≤ Nat.card P) :
    ∃ c : X, c * h * c⁻¹ = t ∧ P.map (MulAut.conj c).toMonoidHom = A.T := by
  obtain ⟨g, rfl⟩ := hconj
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hP'C : P' ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨a, ha, rfl⟩
    have hac : a * (g * t * g⁻¹) = g * t * g⁻¹ * a := (mem_centralizer_singleton_iff.mp (hPC ha))
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g⁻¹ * a * g⁻¹⁻¹ * t = g⁻¹ * (a * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * a) * g := by rw [hac]
      _ = t * (g⁻¹ * a * g⁻¹⁻¹) := by group
  have hP'p : IsPGroup 2 P' := hP.map _
  obtain ⟨c₀, hc₀, hle⟩ := exists_conj_le_T (A := A) hP'p hP'C
  refine ⟨c₀ * g⁻¹, ?_, ?_⟩
  · have := mem_centralizer_singleton_iff.mp hc₀
    calc c₀ * g⁻¹ * (g * t * g⁻¹) * (c₀ * g⁻¹)⁻¹ = c₀ * t * c₀⁻¹ := by group
      _ = t := by rw [this, mul_inv_cancel_right]
  · have hmap : P.map (MulAut.conj (c₀ * g⁻¹)).toMonoidHom =
        P'.map (MulAut.conj c₀).toMonoidHom := by
      rw [hP', map_map]
      congr 1
      ext a
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hmap]
    refine eq_of_le_of_card_ge hle ?_
    have e1 : Nat.card (P'.map (MulAut.conj c₀).toMonoidHom) = Nat.card P' :=
      card_map_of_injective (MulAut.conj c₀).injective
    have e2 : Nat.card P' = Nat.card P := card_map_of_injective (MulAut.conj g⁻¹).injective
    rw [e1, e2]
    exact (card_T_le C).trans hcard

theorem not_conjTo_of_card_gt (C : A.CaseKD) {h : X} {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer ({h} : Set X)) (hcard : 64 < Nat.card P) : ¬ ConjTo t h := by
  intro hconj
  obtain ⟨c, -, hc⟩ := exists_conj_eq_T C hconj hP hPC hcard.le
  have e1 : Nat.card (P.map (MulAut.conj c).toMonoidHom) = Nat.card P :=
    card_map_of_injective (MulAut.conj c).injective
  rw [hc] at e1
  have := card_T_le C
  omega

variable {C : A.CaseKD} (S : KDBase A C)

theorem dy_pow_four : ∀ e : ZMod 8, dbit8 e = 0 → (d8 * aff8 (-1) e) ^ 4 ≠ 1 := by decide

include S in
theorem not_conjTo_of_pow_four {h : X} {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer ({h} : Set X)) (hcard : 64 ≤ Nat.card P)
    (h4 : ∀ a ∈ P, a ^ 4 = 1 ∨ a ^ 4 = h) : ¬ ConjTo t h := by
  intro hconj
  obtain ⟨c, hch, hc⟩ := exists_conj_eq_T C hconj hP hPC hcard
  have hdyT : S.d * S.y ∈ A.T := mul_mem (KD46.d_mem_T S) (KD46.y_mem_T S)
  have hdy := hdyT
  rw [← hc] at hdy
  obtain ⟨a, ha, hae⟩ := hdy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hae
  have h4' : (S.d * S.y) ^ 4 = 1 ∨ (S.d * S.y) ^ 4 = t := by
    rw [← hae, conj_pow, ← hch]
    rcases h4 a ha with h1 | h1 <;> rw [h1]
    · left; group
    · right; rfl
  obtain ⟨e, he, hψy⟩ := KD46.ψ_y S
  have hψ : ψX A ((S.d * S.y) ^ 4) = (d8 * aff8 (-1) e) ^ 4 := by
    rw [ψX_pow hdyT, ψX_mul (KD46.d_mem_T S) (KD46.y_mem_T S), KD46.ψ_d S, hψy]
  apply dy_pow_four e he
  rw [← hψ]
  rcases h4' with h1 | h1 <;> rw [h1]
  · exact ψX_one
  · exact ψX_t

namespace VSide

variable {S} {T₁ : Subgroup X} (V : VSide S T₁)

theorem not_conjTo_of_mem_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : ¬ ConjTo t e := by
  intro hconj
  obtain ⟨n, hn, hnt⟩ := V.D.controls e (V.E0_le_E he) hconj
  have h := V.conj_mem_E0 (inv_mem hn) he
  rw [← hnt, show n⁻¹ * (n * t * n⁻¹) * n⁻¹⁻¹ = t by group] at h
  exact V.F.t_not_mem_E0 h

end VSide

end KD8c

end CFSG.OddStandard.SmallF3.L33.KD
