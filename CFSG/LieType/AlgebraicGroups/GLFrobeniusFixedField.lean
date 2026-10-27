module

public import CFSG.LieType.AlgebraicGroups.GLFrobeniusLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQMat
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleCycle

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {k : Type} [Field k] [IsAlgClosed k]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem gl_inner_frobenius_fixed_field (p e : ℕ) [Fact p.Prime] [CharP k p]
    (he : 1 ≤ e) (g : Matrix.GeneralLinearGroup ι k) :
    let Φ := Matrix.GeneralLinearGroup.map (n := ι) (iterateFrobenius k p e)
    let Ψ := (MulAut.conj g).toMonoidHom.comp Φ
    let K := (iterateFrobenius k p e).eqLocusField (RingHom.id k)
    Nat.card K = p ^ e ∧
      Nonempty (Matrix.GeneralLinearGroup ι K ≃* Ψ.eqLocus (MonoidHom.id _)) := by
  intro Φ Ψ K
  classical
  let σ := iterateFrobeniusEquiv k p e
  have hσ : σ.toRingHom = iterateFrobenius k p e := by
    ext a
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, σ,
      iterateFrobeniusEquiv_def, iterateFrobenius_def]
  have hK : CFSG.LocalAnalysis.GLTheoremA.FQ.fixF σ = K := by
    change σ.toRingHom.eqLocusField (RingHom.id k) = _
    rw [hσ]
  have hcard : Nat.card K = p ^ e := by
    rw [show Nat.card K = Nat.card {a : k | a ^ p ^ e = a} from
      Nat.card_congr (Equiv.subtypeEquivRight fun a => by
        rw [RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
        rfl)]
    exact CFSG.RankThree.Classical2.natCard_setOf_pow_eq_self (by omega)
  refine ⟨hcard, ?_⟩
  obtain ⟨h, hh⟩ := gl_frobenius_inner_twist p e he g
  change ∀ x, Ψ x = h⁻¹ * Φ (h * x * h⁻¹) * h at hh
  let inc : Matrix.GeneralLinearGroup ι K →* Matrix.GeneralLinearGroup ι k :=
    Matrix.GeneralLinearGroup.map K.subtype
  have hfix : ∀ a : Matrix.GeneralLinearGroup ι K, Φ (inc a) = inc a := by
    intro a
    have hz := CFSG.LocalAnalysis.GLTheoremA.FQ.glMap_subtype_fixed (ι := ι) σ
    rw [hσ, hK] at hz
    exact hz a
  let f : Matrix.GeneralLinearGroup ι K →* Ψ.eqLocus (MonoidHom.id _) :=
    { toFun := fun a => ⟨h⁻¹ * inc a * h, by
        change Ψ (h⁻¹ * inc a * h) = h⁻¹ * inc a * h
        rw [hh]
        have hz : h * (h⁻¹ * inc a * h) * h⁻¹ = inc a := by group
        rw [hz, hfix]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change h⁻¹ * inc (a * b) * h = (h⁻¹ * inc a * h) * (h⁻¹ * inc b * h)
        rw [map_mul]
        group) }
  refine ⟨MulEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro a b hab
    have hab' : inc a = inc b := by
      have hz := congrArg (fun x : Ψ.eqLocus (MonoidHom.id _) =>
        (x : Matrix.GeneralLinearGroup ι k)) hab
      change h⁻¹ * inc a * h = h⁻¹ * inc b * h at hz
      exact mul_left_cancel (mul_right_cancel hz)
    have hinj := CFSG.LocalAnalysis.GLTheoremA.FQ.glMap_subtype_injective (ι := ι) σ
    rw [hK] at hinj
    exact hinj hab'
  · intro x
    have hx : Ψ (x : Matrix.GeneralLinearGroup ι k) = x := x.property
    have hy : Φ (h * (x : Matrix.GeneralLinearGroup ι k) * h⁻¹) =
        h * (x : Matrix.GeneralLinearGroup ι k) * h⁻¹ := by
      have hz := hh (x : Matrix.GeneralLinearGroup ι k)
      rw [hx] at hz
      calc
        Φ (h * (x : Matrix.GeneralLinearGroup ι k) * h⁻¹) =
            h * (h⁻¹ * Φ (h * (x : Matrix.GeneralLinearGroup ι k) * h⁻¹) * h) * h⁻¹ := by group
        _ = h * (x : Matrix.GeneralLinearGroup ι k) * h⁻¹ := by rw [← hz]
    have hd := CFSG.LocalAnalysis.GLTheoremA.FQ.exists_descend σ
      (h * (x : Matrix.GeneralLinearGroup ι k) * h⁻¹)
    rw [hσ, hK] at hd
    obtain ⟨a, ha⟩ := hd hy
    refine ⟨a, Subtype.ext ?_⟩
    change h⁻¹ * inc a * h = x
    rw [ha]
    group

theorem gl_inner_frobenius_fixed_field_extension
    {F : Type} [Field F] [Finite F] [Algebra F k]
    (p f m : ℕ) [Fact p.Prime] [CharP k p]
    (hf : 1 ≤ f) (hm : 1 ≤ m) (hF : Nat.card F = p ^ f)
    (g : Matrix.GeneralLinearGroup ι k) :
    let Φ := Matrix.GeneralLinearGroup.map (n := ι) (iterateFrobenius k p (f * m))
    let Ψ := (MulAut.conj g).toMonoidHom.comp Φ
    let K := (iterateFrobenius k p (f * m)).eqLocusField (RingHom.id k)
    ∃ ρ : F →+* K, K.subtype.comp ρ = algebraMap F k ∧
      Nat.card K = Nat.card F ^ m ∧
      Nonempty (Matrix.GeneralLinearGroup ι K ≃* Ψ.eqLocus (MonoidHom.id _)) := by
  intro Φ Ψ K
  classical
  let := Fintype.ofFinite F
  have hmem : ∀ a : F, algebraMap F k a ∈ K := by
    intro a
    have ha := FiniteField.pow_card_pow m a
    rw [← Nat.card_eq_fintype_card, hF, ← pow_mul] at ha
    rw [RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply,
      ← map_pow, ha]
  let ρ : F →+* K := (algebraMap F k).codRestrict K hmem
  obtain ⟨hc, heq⟩ := gl_inner_frobenius_fixed_field p (f * m) (by nlinarith) g
  refine ⟨ρ, ?_, ?_, heq⟩
  · ext a
    rfl
  · rw [hF, ← pow_mul]
    exact hc

end CFSG.LieType.AlgebraicGroups
