module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265FL2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF2
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265D

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Assembly
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265

theorem s265d_pp_eq {q : TauCeti.PrimePower} {r s : ℕ} (hr : r.Prime) (hs : 0 < s)
    (h : q.card = r ^ s) : q.p = r ∧ q.exponent = s := by
  rw [TauCeti.PrimePower.card_def] at h
  obtain ⟨m, hm⟩ : ∃ m, q.exponent = m + 1 := ⟨q.exponent - 1, by have := q.exponent_pos; omega⟩
  obtain ⟨k, hk⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  rw [hm, hk] at h
  obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj q.prime_p hr h
  exact ⟨h1, by omega⟩

theorem s265d_l28_stated {R : Type} [Group R] (h : catalogIs R tyL28) :
    CFSG.Open.StatedClassicalModel R .PSL 2 2 3 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | A r q =>
      rcases r with _ | _ | r
      · exact hi.elim
      · have hq : q.card = 8 := hi
        have hmodel := CFSG.HardMathSupport.Malle.E27Lie.statedClassicalModel_typeA' hv e
        obtain ⟨h1, h2⟩ := s265d_pp_eq Nat.prime_two (s := 3) (by norm_num) (hq.trans (by norm_num))
        rw [h1, h2] at hmodel
        exact hmodel
      · exact hi.elim
    | _ => exact hi.elim

theorem s265d_card_l28 {R : Type} [Group R] (h : catalogIs R tyL28) : Nat.card R = 504 := by
  have hL : CFSG.Blueprint.LieModel R .PSL 2 2 3 := Or.inl ⟨by decide, s265d_l28_stated h⟩
  rw [CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two hL,
    CFSG.RankThree.PartOne.S12K.ordA_one_eq (by norm_num : 1 ≤ 3)]
  norm_num

theorem s265d_l28_psl_model {R : Type} [Group R] (h : catalogIs R tyL28) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ 3 ∧
      Nonempty (R ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := s265d_l28_stated h
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩⟩

private theorem psl2_aut_card_le {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    [NeZero (p : K)] {A : Subgroup (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))}
    (hA : IsElemAbelian p A) : Nat.card A ≤ p ^ 2 := by
  have hA' : CFSG.IsElementaryAbelian p A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2 hA
  obtain ⟨E₀, hE₀E, hE₀in, hE₀card⟩ :=
    CFSG.RankThree.PartOne.K133.exists_inner_core_psl2 hp hp2 A hA'
  have hE₀el : CFSG.IsElementaryAbelian p E₀ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E₀).2 (isElemAbelian_mono hA hE₀E)
  obtain ⟨A', hA'el, hA'c⟩ := CFSG.RankThree.PartOne.K133.exists_elemAb_card_eq_of_le_inner
    (CFSG.GorensteinWalter.psl2_center_eq_bot K) hE₀el hE₀in
  have hle := CFSG.RankThree.PartOne.K133.psl2_elemAb_card_le hp hp2 A' hA'el
  rw [hA'c] at hle
  calc Nat.card A ≤ p * Nat.card E₀ := hE₀card
    _ ≤ p * p := Nat.mul_le_mul_left _ hle
    _ = p ^ 2 := (sq p).symm

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem three_dvd_card_of_l28 {K : Subgroup Ω} (hL : catalogIs (PSimple 3 K) tyL28) :
    3 ∣ Nat.card K := by
  have h1 : Nat.card (PSimple 3 K) ∣ Nat.card K :=
    Subgroup.card_dvd_of_surjective (chevQuotHom_surjective 3 K)
  rw [s265d_card_l28 hL] at h1
  exact (by norm_num : 3 ∣ 504).trans h1

theorem card_B_le_of_l28 {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K)
    (hL : catalogIs (PSimple 3 K) tyL28) : Nat.card B ≤ 3 ^ 4 := by
  obtain ⟨-, -, hDcard, -, -, hKcomp, -⟩ := h.cfg.std
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  haveI : Nontrivial (PSimple 3 K) := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [s265d_card_l28 hL]
    norm_num
  obtain ⟨θ⟩ := SF.nonempty_centerQuot_equiv_pSimple (p := 3) hKq
  obtain ⟨F, _, _, hF, ⟨ePSL⟩⟩ := s265d_l28_psl_model hL
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3)
    (by rw [← Nat.card_eq_fintype_card]; exact hF)
  haveI : NeZero ((3 : ℕ) : F) :=
    ⟨fun h3 => by have := (CharP.cast_eq_zero_iff F 2 3).1 h3; omega⟩
  obtain ⟨X, hXel, hBX, -⟩ := SF.exists_aut_nl h (θ.trans ePSL)
  have hXle : Nat.card X ≤ 3 ^ 2 := psl2_aut_card_le Nat.prime_three (by norm_num) hXel
  rw [hBX, hDcard]
  calc 3 ^ 2 * Nat.card X ≤ 3 ^ 2 * 3 ^ 2 := Nat.mul_le_mul_left _ hXle
    _ = 3 ^ 4 := by norm_num

end CFSG.LocalAnalysis.GLTheoremA.S265D

end
