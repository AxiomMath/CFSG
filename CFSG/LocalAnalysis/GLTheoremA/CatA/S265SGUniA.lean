module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryTransvectionGeneration
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.ClassicalGroups.UnitaryFlag.GramSURootGen
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGUniLevi
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeUniSpec

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.CrossUni
  (exists_isPrimitiveRoot_three)

theorem SG.exists_sl2_primeFormP {F : Type} [Field F] {n d : ℕ} (h : UnitaryFieldData 2 n F)
    (x y : Fin 2 → Fin d → F) (hxx : ∀ i j, herm h.barEquiv (x i) (x j) = 0)
    (hyy : ∀ i j, herm h.barEquiv (y i) (y j) = 0)
    (hxy : ∀ i j, herm h.barEquiv (x i) (y j) = if i = j then 1 else 0)
    {z : Fin d → F} (hz : z ≠ 0) (hzx : ∀ i, herm h.barEquiv (x i) z = 0)
    (hzy : ∀ i, herm h.barEquiv (y i) z = 0) :
    ∃ A : Subgroup (primeFormP h ((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)),
      IsSimpleGroup ↥A ∧ (∃ a b : ↥A, a * b ≠ b * a) ∧ 3 ∣ Nat.card ↥A ∧
      ∀ (g : primeFormUnitary h ((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)) (a : F),
        (∀ i, ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ x i = a • x i) →
        (∀ i, ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ y i = a⁻¹ • y i) →
        A ≤ fixSubgroup (primeFormConjHom h _ g) := by
  haveI := h.finite
  haveI := h.charP
  obtain ⟨ρ, hρinj, hρz, hρg⟩ := SG.exists_sl2_leviHom_suid (σ := h.barEquiv) h.bar_bar x y hxx hyy
    hxy hzx hzy
  have e := gramSU_one_eq_SUid h d
  let Φ : Matrix.SpecialLinearGroup (Fin 2) F →*
      primeFormP h ((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) :=
    (QuotientGroup.mk' _).comp ((Subgroup.inclusion e.symm.le).comp ρ)
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro M hM
    obtain ⟨c, -, -, hc⟩ := (QuotientGroup.eq_one_iff _).1 hM
    have h1 := hρz M
    have hc' : ((ρ M : SUid h.barEquiv d) : GL (Fin d) F) =
        Matrix.GeneralLinearGroup.scalar (Fin d) c := hc
    rw [hc', Matrix.GeneralLinearGroup.coe_scalar] at h1
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
    have h2 : (c : F) * z i = 1 * z i := by
      simpa [Matrix.scalar_apply, Matrix.mulVec_diagonal] using congrFun h1 i
    have hc1 : c = 1 := Units.ext (by simpa using mul_right_cancel₀ hi h2)
    apply hρinj
    rw [map_one]
    exact Subtype.ext (by rw [hc', hc1, map_one]; rfl)
  have hF4 : 4 ≤ Nat.card F := by
    rw [h.card]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by have := h.one_le; omega)
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
    haveI := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF4
    have hcen : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
      rw [eq_bot_iff]
      intro A hA
      obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
      have hr2 : r ^ 2 = 1 := by simpa using hr
      have h0 : (r - 1) ^ 2 = 0 := by
        linear_combination hr2 + (1 - r) * (CharP.cast_eq_zero F 2 : (2 : F) = 0)
      have hr1 : r = 1 := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)
      rw [hr1] at hA'
      have : (A : Matrix (Fin 2) (Fin 2) F) = 1 := by rw [← hA']; simp
      exact (Subgroup.mem_bot).2 (Subtype.ext (by simpa using this))
    have e' : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃*
        Matrix.SpecialLinearGroup (Fin 2) F :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) := e'.symm.toEquiv.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective e'.toMonoidHom e'.surjective
  have hnc : ∃ a b : Matrix.SpecialLinearGroup (Fin 2) F, a * b ≠ b * a := by
    refine ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩,
      ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩, fun hab => ?_⟩
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
      (g : Matrix (Fin 2) (Fin 2) F) 0 0) hab
    change (!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (!![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 at this
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
  have h3 : 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    have hu : 3 ∣ Nat.card Fˣ := by
      rw [Nat.card_units, h.card, pow_mul]
      simpa using Nat.sub_one_dvd_pow_sub_one 4 n
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three hu
    have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
    let t : Matrix.SpecialLinearGroup (Fin 2) F :=
      ⟨diagonal ![ζ, ζ⁻¹], by simp [Matrix.det_diagonal, Fin.prod_univ_two, hζ0]⟩
    have ht3 : t ^ 3 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
      change (diagonal ![ζ, ζ⁻¹]) ^ 3 = 1
      rw [diagonal_pow, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [inv_pow, hζ.pow_eq_one]
    have ht1 : t ≠ 1 := fun h1 => by
      have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
        (g : Matrix (Fin 2) (Fin 2) F) 0 0) h1
      simp [t] at this
      exact hζ.ne_one (by norm_num) this
    rw [← orderOf_eq_prime ht3 ht1]
    exact orderOf_dvd_natCard t
  let eΦ : Matrix.SpecialLinearGroup (Fin 2) F ≃* Φ.range := MonoidHom.ofInjective hinj
  haveI := hsimple
  haveI : IsSimpleGroup Φ.range := eΦ.symm.isSimpleGroup
  refine ⟨Φ.range, this, ?_, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := hnc
    exact ⟨eΦ a, eΦ b, fun h' => hab (eΦ.injective (by rw [map_mul, map_mul]; exact h'))⟩
  · rwa [← Nat.card_congr eΦ.toEquiv]
  · intro g a hx hy
    rintro _ ⟨M, rfl⟩
    rw [mem_fixSubgroup]
    have hg : conjTr h.barEquiv ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
        ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 := by
      have hg0 := (mem_primeFormUnitary (h := h)).1 g.2
      simp only [Units.val_one, Matrix.mul_one] at hg0
      exact hg0
    have hcomm := hρg (g : GL (Fin d) F) a hg hx hy M
    change primeFormConjHom h _ g (QuotientGroup.mk (Subgroup.inclusion e.symm.le (ρ M))) =
      QuotientGroup.mk (Subgroup.inclusion e.symm.le (ρ M))
    rw [primeFormConjHom_mk]
    congr 1
    exact Subtype.ext (by
      change (g : GL (Fin d) F) * (ρ M : GL (Fin d) F) * (g : GL (Fin d) F)⁻¹ = ρ M
      rw [hcomm, mul_inv_cancel_right])

end CFSG.LocalAnalysis.GLTheoremA.S265

end
