module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGPin
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGMark

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem SG.linModel_of_innLabel {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) {lab : GLALabel} (hlab : InnLabelOf B S lab)
    (ht : lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3)) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (Θ : PSimple 3 S ≃* projectiveSL n F),
      Nat.card F = 2 ^ lab.n ∧ (lab.tag = .A → n = lab.rank + 1) ∧ (lab.tag = .D → n = 4) ∧
      ∀ b ∈ B, ∀ hb : b ∈ Subgroup.normalizer (S : Set Ω),
        MulAut.congr Θ (chevAut 3 S ⟨b, hb⟩) ∈ Set.range (conjAut n F) := by
  have hraw := SG.exists_rawDatum_chevAut h hlab
  obtain ⟨t, r, m⟩ := lab
  obtain ⟨d, hdA, hdD, F, _, _, hF, -, -, Φ, hΦ⟩ : ∃ d : ℕ, (t = .A → d = r + 1) ∧
      (t = .D → d = 4) ∧ CFSG.Assembly.LargeEvenRecipeLinear d (2 ^ m) fun R _ I _ =>
        IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ ∃ Φ : PSimple 3 S ≃* R, ∀ (b : Ω)
          (hbN : b ∈ Subgroup.normalizer (S : Set Ω)), b ∈ B →
            MulAut.congr Φ (chevAut 3 S ⟨b, hbN⟩) ∈ I := by
    dsimp only at ht
    rcases ht with rfl | ⟨rfl, rfl⟩
    · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hraw
      exact ⟨r + 1, fun _ => rfl, fun h' => absurd h' (by decide), hraw⟩
    · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hraw
      rw [if_pos rfl] at hraw
      exact ⟨4, fun h' => absurd h' (by decide), fun _ => rfl, hraw⟩
  refine ⟨d, F, inferInstance, inferInstance, Φ.trans (CFSG.StandardType.TypeA.recipeEquiv d F),
    hF, hdA, hdD, fun b hb hbN => ?_⟩
  have heq : MulAut.congr (Φ.trans (CFSG.StandardType.TypeA.recipeEquiv d F))
      (chevAut 3 S ⟨b, hbN⟩) = MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv d F)
        (MulAut.congr Φ (chevAut 3 S ⟨b, hbN⟩)) := by
    ext y
    rfl
  rw [heq]
  exact CFSG.StandardType.TypeA.congr_recipeEquiv_mem (hΦ b hbN hb)

theorem SG.conjAut_inner_of_cube {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 3 ≤ n)
    (h3 : ¬ 3 ∣ n ∨ ¬ 3 ∣ Nat.card F - 1) {A : GL (Fin n) F} (hA : conjAut n F A ^ 3 = 1) :
    ∃ s : Matrix.SpecialLinearGroup (Fin n) F, conjAut n F A = MulAut.conj (proj n F s) := by
  suffices hr : conjAut n F A ∈
      (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range by
    obtain ⟨y, hy⟩ := hr
    obtain ⟨s, rfl⟩ := proj_surjective n F y
    exact ⟨s, hy.symm⟩
  rcases h3 with h3 | h3
  · exact mem_range_conj_of_mem_linearAutGroup_of_coprime (conjAut_mem_linearAutGroup A)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3) hA
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn (A ^ 3) 1
    (by rw [map_one, mul_one, map_pow, hA])
  have hbij : Function.Bijective fun u : Fˣ => u ^ 3 := Nat.Coprime.pow_left_bijective (by
    rw [Nat.card_units]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm)
  obtain ⟨γ, hγ⟩ := hbij.2 c
  have hγ' : γ ^ 3 = c := hγ
  refine conjAut_mem_range_conj_of_det_eq_pow (μ := γ) (hbij.1 ?_)
  show Matrix.GeneralLinearGroup.det A ^ 3 = (γ ^ n) ^ 3
  rw [← map_pow, ← hc, ← hγ', Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, ← pow_mul,
    ← pow_mul, mul_comm]

end CFSG.LocalAnalysis.GLTheoremA.S265

end
