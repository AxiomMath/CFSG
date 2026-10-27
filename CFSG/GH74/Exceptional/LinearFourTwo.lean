module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.Blueprint.Catalog
import CFSG.Open.StatedZModTwo
import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27L34GL

public section

namespace CFSG.GH74.Exceptional

open Matrix CFSG.ComponentClassification.PresentationLocal Blueprint Assembly.LowTwoRank

@[expose] def l42Mat : Fin 6 → Matrix (Fin 4) (Fin 4) (ZMod 2)
  | 0 => !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]
  | 1 => !![1, 0, 1, 0; 0, 0, 1, 1; 1, 0, 0, 0; 1, 1, 1, 1]
  | 2 => !![1, 1, 0, 0; 1, 0, 0, 0; 1, 0, 1, 1; 1, 1, 1, 0]
  | 3 => !![0, 0, 1, 0; 1, 1, 1, 1; 1, 0, 1, 0; 1, 1, 0, 0]
  | 4 => !![1, 1, 1, 0; 1, 0, 1, 1; 0, 0, 1, 1; 0, 0, 1, 0]
  | 5 => !![0, 1, 1, 0; 0, 1, 1, 1; 1, 0, 0, 1; 1, 1, 0, 1]

theorem l42Mat_pow_three : ∀ i : Fin 6, l42Mat i ^ 3 = 1 := by decide

theorem l42Mat_mul_sq : ∀ i j : Fin 6, i ≠ j → (l42Mat i * l42Mat j) ^ 2 = 1 := by decide

@[expose] def l42Unit (i : Fin 6) : GL (Fin 4) (ZMod 2) where
  val := l42Mat i
  inv := l42Mat i ^ 2
  val_inv := by rw [← pow_succ', l42Mat_pow_three]
  inv_val := by rw [← pow_succ, l42Mat_pow_three]

@[expose] def carmichaelIndexToFin6 (k : CarmichaelIndex 8) : Fin 6 :=
  ⟨(k.1 : ℕ) - 2, by have := k.1.isLt; have := k.2; omega⟩

theorem carmichaelIndexToFin6_injective : Function.Injective carmichaelIndexToFin6 := by
  intro k l h
  have h' := congrArg Fin.val h
  simp only [carmichaelIndexToFin6] at h'
  exact Subtype.ext (Fin.ext (by have := k.2; have := l.2; omega))

@[expose] def l42Gen (k : CarmichaelIndex 8) : GL (Fin 4) (ZMod 2) :=
  l42Unit (carmichaelIndexToFin6 k)

theorem l42Gen_pow_three (k : CarmichaelIndex 8) : l42Gen k ^ 3 = 1 :=
  Units.ext (by simp only [l42Gen, l42Unit, Units.val_pow_eq_pow_val, Units.val_one,
    l42Mat_pow_three])

theorem l42Gen_mul_sq (k l : CarmichaelIndex 8) (hkl : k ≠ l) : (l42Gen k * l42Gen l) ^ 2 = 1 :=
  Units.ext (by
    simp only [l42Gen, l42Unit, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_one]
    exact l42Mat_mul_sq _ _ (carmichaelIndexToFin6_injective.ne hkl))

theorem card_GL_four_two : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 :=
  CFSG.OddStandard.Seitz77.card_GL_four_two

noncomputable def alternatingEightEquivGLFourTwo :
    alternatingGroup (Fin 8) ≃* GL (Fin 4) (ZMod 2) := by
  classical
  have hφ := exists_hom_carmichaelCycle (n := 8) (by norm_num) l42Gen l42Gen_pow_three
    l42Gen_mul_sq
  let φ := hφ.choose
  have hφx : ∀ k, φ (carmichaelCycle k) = l42Gen k := hφ.choose_spec
  have hinj : Function.Injective φ := by
    have : IsSimpleGroup (alternatingGroup (Fin 8)) :=
      alternatingGroup.isSimpleGroup (by simp)
    rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with h | h
    · exact (MonoidHom.ker_eq_bot_iff φ).mp h
    · exfalso
      let k₀ : CarmichaelIndex 8 := ⟨2, by decide⟩
      have hk : carmichaelCycle k₀ ∈ φ.ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hφx] at hk
      have : l42Mat 0 = 1 := by
        have := congrArg Units.val hk
        simpa [l42Gen, l42Unit, carmichaelIndexToFin6, k₀] using this
      exact absurd this (by decide)
  have hcard : Nat.card (alternatingGroup (Fin 8)) = Nat.card (GL (Fin 4) (ZMod 2)) := by
    rw [card_GL_four_two, nat_card_alternatingGroup, Nat.card_fin]
    decide
  exact MulEquiv.ofBijective φ
    ((Function.Injective.bijective_of_nat_card_le hinj hcard.ge))

end CFSG.GH74.Exceptional

namespace CFSG.GH74.Exceptional

open Matrix Blueprint Assembly.LowTwoRank

theorem statedSL_eq_top_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (n : ℕ) : StatedSL n K = ⊤ :=
  CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hK n

theorem statedScalars_eq_bot_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (n : ℕ) : StatedScalars (Fin n) K = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK (Fin n)

noncomputable def statedProjStatedSLEquivOfCardTwo {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (n : ℕ) : StatedProj (StatedSL n K) ≃* GL (Fin n) K :=
  have hbot : (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) = ⊥ := by
    rw [statedScalars_eq_bot_of_card_two hK, Subgroup.bot_subgroupOf]
  ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).trans
    ((MulEquiv.subgroupCongr (statedSL_eq_top_of_card_two hK n)).trans Subgroup.topEquiv)

noncomputable def glEquivZModTwoOfCardTwo {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (n : ℕ) : GL (Fin n) K ≃* GL (Fin n) (ZMod 2) :=
  have : Fintype K := Fintype.ofFinite K
  let e : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two
    (by rw [← Nat.card_eq_fintype_card, hK])
  Units.mapEquiv (e.symm.mapMatrix (m := Fin n)).toMulEquiv

theorem nonempty_mulEquiv_alternating_eight_of_lieModel {G : Type} [Group G]
    (h : LieModel G .PSL 4 2 1) : Nonempty (G ≃* alternatingGroup (Fin 8)) := by
  rcases h with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have hK2 : Nat.card K = 2 := by simpa using hK
    exact ⟨((e.trans (statedProjStatedSLEquivOfCardTwo hK2 4)).trans
      (glEquivZModTwoOfCardTwo hK2 4)).trans alternatingEightEquivGLFourTwo.symm⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem nonempty_mulEquiv_statedProj_of_alternating_eight {A : Type} [Group A]
    (e : A ≃* alternatingGroup (Fin 8)) : Nonempty (A ≃* StatedProj (StatedSL 4 (ZMod 2))) :=
  ⟨(e.trans alternatingEightEquivGLFourTwo).trans
    (statedProjStatedSLEquivOfCardTwo (K := ZMod 2) (by simp) 4).symm⟩

end CFSG.GH74.Exceptional
