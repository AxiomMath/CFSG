module

public import CFSG.ClassicalInvolution.AschTight.S1911F0c
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19T

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
  CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped MatrixGroups

theorem exists_nonabelian_two_subgroup_sl2 {F : Type} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) :
    ∃ P : Subgroup SL(2, F), IsPGroup 2 P ∧ ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
  obtain ⟨⟨a, b, h⟩, -⟩ := QuaternionMatrices.odd_field_two_dimensional_quaternion_matrices hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (QuaternionGroup 2) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have hR : IsPGroup 2 (QuaternionMatrices.quatHom h).range := by
    rw [MonoidHom.range_eq_map]
    exact (hQ.to_subgroup ⊤).map _
  refine ⟨(QuaternionMatrices.quatHom h).range, hR, QuaternionMatrices.slQuatI F,
    ⟨.a 1, Subtype.ext (QuaternionMatrices.quatHom_a_one h)⟩, QuaternionMatrices.slQuatJ h,
    ⟨.xa 0, Subtype.ext (QuaternionMatrices.quatHom_xa_zero h)⟩, ?_⟩
  intro hc
  have h1 : QuaternionMatrices.quatI F * QuaternionMatrices.quatJ a b =
      QuaternionMatrices.quatJ a b * QuaternionMatrices.quatI F :=
    congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hc
  have h2 := QuaternionMatrices.quatI_mul_quatJ_eq_neg a b
  rw [h1, QuaternionMatrices.quatJ_mul_quatI] at h2
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) h2
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) h2
  simp at h00 h01
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hb : b = 0 := by
    have : (2 : F) * b = 0 := by linear_combination -h00
    exact (mul_eq_zero.mp this).resolve_left h2F
  have ha : a = 0 := by
    have : (2 : F) * a = 0 := by linear_combination h01
    exact (mul_eq_zero.mp this).resolve_left h2F
  rw [ha, hb] at h
  have : (1 : F) = 0 := by linear_combination h
  exact one_ne_zero this

theorem exists_semilinHom_refl_of_fixes_abelian {p e : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hq : 5 ≤ p ^ e) (β : MulAut SL(2, GaloisField p e)) (hβ : β * β = 1)
    (hab : ∀ P : Subgroup SL(2, GaloisField p e), IsPGroup 2 P → (∀ x ∈ P, β x = x) →
      ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    ∃ G : GL (Fin 2) (GaloisField p e), ∀ b, β b = semilinHom G (RingEquiv.refl _) b := by
  obtain ⟨G, σ, hβG, hσ2⟩ := mulAut_involution_structure hp hq β hβ
  by_cases hσ1 : σ = 1
  · exact ⟨G, fun b => by rw [hβG b, hσ1]; rfl⟩
  exfalso
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  obtain ⟨k, hek, -⟩ := eq_frobenius_of_sq_eq_one he hσ2 hσ1
  subst hek
  have hk : 0 < k := by omega
  have hinv : ∀ b, semilinHom G σ (semilinHom G σ b) = b := by
    intro b
    rw [← hβG, ← hβG]
    have := congrArg (fun φ : MulAut SL(2, GaloisField p (2 * k)) => φ b) hβ
    simpa [MulAut.mul_apply] using this
  obtain ⟨ι⟩ := S1911.factF0 p k hp hk σ hσ1 hσ2 G hinv
  have hF : ringChar (GaloisField p k) ≠ 2 := by
    rw [ringChar.eq (GaloisField p k) p]
    exact hp
  obtain ⟨P₀, hP₀, x, hx, y, hy, hxy⟩ := exists_nonabelian_two_subgroup_sl2 hF
  let E := MonoidHom.eqLocus (semilinHom G σ) (MonoidHom.id SL(2, GaloisField p (2 * k)))
  let φ : SL(2, GaloisField p k) →* SL(2, GaloisField p (2 * k)) :=
    E.subtype.comp ι.symm.toMonoidHom
  have hφinj : Function.Injective φ :=
    Subtype.val_injective.comp ι.symm.injective
  have hfix : ∀ w ∈ P₀.map φ, β w = w := by
    rintro _ ⟨v, -, rfl⟩
    rw [hβG]
    exact (ι.symm v).2
  have hc := hab (P₀.map φ) (hP₀.map φ) hfix (φ x) ⟨x, hx, rfl⟩ (φ y) ⟨y, hy, rfl⟩
  apply hxy
  apply hφinj
  rw [map_mul, map_mul, hc]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19T
