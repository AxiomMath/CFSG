module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OOutC
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OOutE

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin (quadMinus)
open OutLin

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem outer_rank_linear (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 ≤ n) (E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F))
    (hE2 : ∀ g ∈ E, g * g = 1) (hEab : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hEN : ∀ g ∈ E, ∀ h ∈ StatedOmega (StatedQuadMinus 3 F b c),
      g * h * g⁻¹ ∈ StatedOmega (StatedQuadMinus 3 F b c))
    (hEnot : ¬ E ≤ StatedOmega (StatedQuadMinus 3 F b c)) :
    Nat.card ↥E ≤ 2 ^ (3 * n + 1) := by
  have hEO : ∀ g ∈ E, ∀ v : OW F, quadMinus 3 F b c (gv g v) = quadMinus 3 F b c v := by
    intro g hg v
    have hAA : (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *
        (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) = 1 := by
      have := congrArg Units.val (hE2 g hg)
      simpa using this
    have hN : ∀ h ∈ StatedOmega (StatedQuadMinus 3 F b c),
        ∃ h' ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x : OW F,
          (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
            ((h : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) =
          (h' : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
            ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) := by
      intro h hh
      refine ⟨g * h * g⁻¹, hEN g hg h hh, fun x => ?_⟩
      show gv g (gv h x) = gv (g * h * g⁻¹) (gv g x)
      rw [gv_mul, gv_mul, gv_inv_gv]
    have hv := omega_isometry_of_normalizes hirr _ hAA hN v
    rw [quadMinus_eq_stated, quadMinus_eq_stated]
    exact hv
  have hEP : IsPGroup 2 E := fun g => ⟨1, by
    apply Subtype.ext
    simp only [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    exact hE2 g.1 g.2⟩
  obtain ⟨G, hG, hstd⟩ := exists_std_conj hirr hF hn hEO hEP
  set E' : Subgroup (GL6 F) := E.comap (MulAut.conj G).toMonoidHom with hE'
  have hmem : ∀ g' : GL6 F, g' ∈ E' ↔ G * g' * G⁻¹ ∈ E := fun g' => Iff.rfl
  have hstd' : StdGrp b c E' := by
    refine ⟨fun g' hg' => ?_, fun g' hg' => ?_, fun g' hg' h' hh' => ?_⟩
    · have := hstd _ ((hmem g').1 hg')
      rwa [show G⁻¹ * (G * g' * G⁻¹) * G = g' by group] at this
    · have h := hE2 _ ((hmem g').1 hg')
      calc g' * g' = G⁻¹ * ((G * g' * G⁻¹) * (G * g' * G⁻¹)) * G := by group
        _ = 1 := by rw [h]; group
    · have h := hEab _ ((hmem g').1 hg') _ ((hmem h').1 hh')
      calc g' * h' = G⁻¹ * ((G * g' * G⁻¹) * (G * h' * G⁻¹)) * G := by group
        _ = G⁻¹ * ((G * h' * G⁻¹) * (G * g' * G⁻¹)) * G := by rw [h]
        _ = h' * g' := by group
  have hout' : ¬ E' ≤ StatedOmega (StatedQuadMinus 3 F b c) := by
    intro hle
    apply hEnot
    intro g hg
    have hg' : G⁻¹ * g * G ∈ E' := by
      rw [hmem, show G * (G⁻¹ * g * G) * G⁻¹ = g by group]
      exact hg
    have := outIsoConj_mem_omega hG (hle hg')
    rwa [show G * (G⁻¹ * g * G) * G⁻¹ = g by group] at this
  have hcard : Nat.card ↥E' = Nat.card ↥E :=
    Nat.card_congr
      { toFun := fun x => ⟨G * (x : GL6 F) * G⁻¹, (hmem _).1 x.2⟩
        invFun := fun y => ⟨G⁻¹ * (y : GL6 F) * G, by
          rw [hmem, show G * (G⁻¹ * (y : GL6 F) * G) * G⁻¹ = y by group]
          exact y.2⟩
        left_inv := fun x => Subtype.ext (by simp [mul_assoc])
        right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }
  have hle := card_le_of_std hirr hstd' hout'
  calc Nat.card ↥E = Nat.card ↥E' := hcard.symm
    _ ≤ 2 * Nat.card F ^ 3 := hle
    _ = 2 ^ (3 * n + 1) := by rw [hF]; ring

end CFSG.LocalAnalysis.RankThreeUC
