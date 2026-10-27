module

public import CFSG.ClassicalInvolution.Phan.PhanD3Pairs
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomy
import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyOrth
public import CFSG.Timmesfeld.RankTwo.LevisSpin

public section

namespace CFSG.ClassicalInvolution.PhanD4

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap CFSG.ClassicalInvolution.ModelFacts
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair Su B12 B23)
open scoped MatrixGroups commutatorElement

variable {p e : ℕ} [Fact p.Prime]

theorem exists_lift_frame (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (fr : Frame (quadPlus 4 (GaloisField p e))) :
    ∃ R ∈ longestFundamental (plusDatum 4 (GaloisField p e) (by norm_num)),
      R.map (spinAction (quadPlus 4 (GaloisField p e))) = fr.La.range ∧ ⁅R, R⁆ = R ∧
        ∀ r ∈ R, spinAction (quadPlus 4 (GaloisField p e)) r = 1 → r = 1 := by
  obtain ⟨hodd, h4⟩ := card_galoisField_facts hp2 hq
  have hn3 : 3 ≤ 4 := by norm_num
  have hdim : Module.finrank (GaloisField p e) (Fin 4 ⊕ Fin 4 → GaloisField p e) = 2 * 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  set k₀ : Fin 4 := ⟨0, by omega⟩ with hk₀
  set fr₀ := (plusFrame 4 (GaloisField p e) hn3).toFrame
      (rootIdxD_ne 4 (by omega) k₀) true (rootSignD 4 k₀) with hfr₀
  have hperp : 2 ≤ Module.finrank (GaloisField p e) fr₀.perp := by
    have := finrank_perp_add_four fr₀
    omega
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  have : Invertible (2 : GaloisField p e) := invertibleOfNonzero h2
  obtain ⟨x, hx⟩ := exists_spin_conj hodd (nondegenerate_polarBilin_quadPlus 4 (GaloisField p e))
    fr₀ fr hperp
  have hi : (Pi.single k₀ 1 : Fin 4 → ℤ) ∈ (plusDatum 4 (GaloisField p e) hn3).roots :=
    CFSG.ClassicalInvolution.RouteD.single_mem_roots (plusDatum 4 (GaloisField p e) hn3) k₀
  refine ⟨((plusFrame 4 (GaloisField p e) hn3).longSL2 (rootIdxD_ne 4 (by omega) k₀) true
      (rootSignD 4 k₀)).range.map (MulAut.conj x).toMonoidHom, ⟨x, Pi.single k₀ 1,
      CFSG.ClassicalInvolution.RouteD.isLongestRoot_of_mem_roots_plusDatum hn3 hi, ?_⟩, ?_, ?_, ?_⟩
  · have hR := CFSG.LieType.Universal.Spin.PlusCT.rankOne_plusRootGroup hn3 k₀
      (n := 4) (K := GaloisField p e)
    exact congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hR.symm
  · rw [map_conj_map, map_longSL2_range, La_range_eq_map_conj hx]
  · have hperf : Group.IsPerfect SL(2, GaloisField p e) := sl2_isPerfect h4
    have hR₀ : ⁅((plusFrame 4 (GaloisField p e) hn3).longSL2 (rootIdxD_ne 4 (by omega) k₀) true
        (rootSignD 4 k₀)).range, ((plusFrame 4 (GaloisField p e) hn3).longSL2
        (rootIdxD_ne 4 (by omega) k₀) true (rootSignD 4 k₀)).range⁆ =
        ((plusFrame 4 (GaloisField p e) hn3).longSL2 (rootIdxD_ne 4 (by omega) k₀) true
        (rootSignD 4 k₀)).range :=
      Subgroup.isPerfect_iff.mp (Group.IsPerfect.range _)
    rw [← Subgroup.map_commutator, hR₀]
  · rintro r ⟨_, ⟨A, rfl⟩, rfl⟩ hr
    have hθ := DFunLike.congr_fun (spinAction_comp_longSL2 (plusFrame 4 (GaloisField p e) hn3)
      (rootIdxD_ne 4 (by omega) k₀) true (rootSignD 4 k₀)) A
    have h1 : fr₀.La A = 1 := by
      have h2' : spinAction (quadPlus 4 (GaloisField p e)) x *
          spinAction (quadPlus 4 (GaloisField p e)) ((plusFrame 4 (GaloisField p e) hn3).longSL2
            (rootIdxD_ne 4 (by omega) k₀) true (rootSignD 4 k₀) A) *
          (spinAction (quadPlus 4 (GaloisField p e)) x)⁻¹ = 1 := by
        simpa [MulAut.conj_apply, map_mul, map_inv] using hr
      rw [← hθ] at ⊢
      simpa using h2'
    have : A = 1 := fr₀.La_injective (h1.trans fr₀.La.map_one.symm)
    subst this
    simp

theorem exists_eps (hp2 : p ≠ 2) :
    ∃ ε : GaloisField p e, ∃ _ : ε ≠ 0, ∃ _ : (4 : GaloisField p e) ≠ 0, ¬ IsSquare (-ε) := by
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  have h4 : (4 : GaloisField p e) ≠ 0 := by
    have : (4 : GaloisField p e) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hchar : ringChar (GaloisField p e) ≠ 2 := by
    rw [ringChar.eq (GaloisField p e) p]
    exact hp2
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  have hεs : ¬ IsSquare (-(-a)) := by simpa using ha
  have hε : -a ≠ 0 := by
    intro h
    have : a = 0 := by simpa using h
    exact ha ⟨0, by simp [this]⟩
  exact ⟨-a, hε, h4, hεs⟩


theorem weakPhan_of_lifts (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {ε : GaloisField p e} (hε : ε ≠ 0)
    (h4 : (4 : GaloisField p e) ≠ 0) (hεs : ¬ IsSquare (-ε))
    (R : Fin 4 → Subgroup (spinGroup (quadPlus 4 (GaloisField p e))))
    (hRspec : ∀ k, (R k).map (spinAction (quadPlus 4 (GaloisField p e))) =
      (![frame0, frame1 ε hε h4, frame2, (frame2 (F := GaloisField p e)).swap] k).La.range ∧
      ⁅R k, R k⁆ = R k ∧
      ∀ r ∈ R k, spinAction (quadPlus 4 (GaloisField p e)) r = 1 → r = 1) :
    (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i →
        ∀ a ∈ R i, ∀ b ∈ R j, a * b = b * a) ∧
      (∀ i j : Fin 4, edgeD 4 i j →
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W (R i) (R j)) := by
  classical
  obtain ⟨hodd, h4'⟩ := card_galoisField_facts hp2 hq
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · simp at hq
    · exact h
  have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hK' : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul p e he
  have : Algebra (GaloisField p e) (GaloisField p (2 * e)) :=
    Classical.choice (Aniso.nonempty_algebra hK hK')
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  let fr : Fin 4 → Frame (quadPlus 4 (GaloisField p e)) :=
    ![frame0, frame1 ε hε h4, frame2, (frame2 (F := GaloisField p e)).swap]
  have hfinite : Finite (spinGroup (quadPlus 4 (GaloisField p e))) := by
    have : NeZero 4 := ⟨by norm_num⟩
    exact finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have S : SpinCtx p e (quadPlus 4 (GaloisField p e)) (Set.range R) :=
    { hp2 := hp2
      hq := hq
      hQ := nondegenerate_polarBilin_quadPlus 4 (GaloisField p e)
      fin := hfinite
      hker2 := OrthAut.plus_hker2 4
      hC := CFSG.ClassicalInvolution.RouteD.Gaps.not_dvd_card_center_plus hp2 (by norm_num)
      perf := by
        rintro _ ⟨k, rfl⟩
        exact (hRspec k).2.1
      inj := by
        rintro _ ⟨k, rfl⟩
        exact (hRspec k).2.2
      map := by
        rintro _ ⟨k, rfl⟩
        exact ⟨_, fr k, (hRspec k).1, rfl⟩ }
  have hW : ∀ {i j : Fin 4}, (∃ θ : Su (GaloisField p (2 * e)) p e 3 →*
      ((Fin 4 ⊕ Fin 4 → GaloisField p e) ≃ₗ[GaloisField p e] (Fin 4 ⊕ Fin 4 → GaloisField p e)),
      Function.Injective θ ∧ (B12 (GaloisField p (2 * e)) p e).map θ = (fr i).La.range ∧
        (B23 (GaloisField p (2 * e)) p e).map θ = (fr j).La.range) →
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W (R i) (R j) := by
    rintro i j ⟨θ, hinj, hU, hV⟩
    have hker : θ.ker ≤ Subgroup.center (Su (GaloisField p (2 * e)) p e 3) := by
      rw [(MonoidHom.ker_eq_bot_iff θ).mpr hinj]
      exact bot_le
    exact S.unitary_of_map ⟨i, rfl⟩ ⟨j, rfl⟩ ⟨θ.range,
      Models.unitaryBlockStandardPair_of_normalized hker rfl (by rw [(hRspec i).1]; exact hU)
        (by rw [(hRspec j).1]; exact hV)⟩
  have hC : ∀ {i j : Fin 4}, (∀ A B : Matrix.SpecialLinearGroup (Fin 2) (GaloisField p e),
      (fr i).La A * (fr j).La B = (fr j).La B * (fr i).La A) →
      ∀ a ∈ R i, ∀ b ∈ R j, a * b = b * a := by
    intro i j h
    exact S.commutes_of_map (R₂ := R j) ⟨i, rfl⟩ (by
      rw [(hRspec i).1, (hRspec j).1]
      rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
      exact h A B)
  have C02 := hC (i := 0) (j := 2) frame0_La_comm_frame2
  have C03 := hC (i := 0) (j := 3) frame0_La_comm_frame2_swap
  have C23 := hC (i := 2) (j := 3) frame2_La_comm_swap
  have hθ01 := exists_hom_01 (p := p) (e := e) (K' := GaloisField p (2 * e)) hε h4 h2 hεs hK hK'
    hodd
  have hθ12 := exists_hom_12 (p := p) (e := e) (K' := GaloisField p (2 * e)) hε h4 h2 hεs hK hK'
    hodd
  have hθ13 := exists_hom_13 (p := p) (e := e) (K' := GaloisField p (2 * e)) hε h4 h2 hεs hK hK'
    hodd
  have hna : ∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i →
      (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
        (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by decide
  have hed : ∀ i j : Fin 4, edgeD 4 i j →
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) := by decide
  refine ⟨?_, ?_⟩
  · intro i j hij h1 h2'
    rcases hna i j hij h1 h2' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact C02
    · exact fun a ha b hb => (C02 b hb a ha).symm
    · exact C03
    · exact fun a ha b hb => (C03 b hb a ha).symm
    · exact C23
    · exact fun a ha b hb => (C23 b hb a ha).symm
  · intro i j hij
    rcases hed i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨θ, hinj, -, hU, hV⟩ := hθ01
      exact hW ⟨θ, hinj, hU, hV⟩
    · obtain ⟨θ, hinj, -, hU, hV⟩ := hθ12
      exact hW ⟨θ, hinj, hU, hV⟩
    · obtain ⟨θ, hinj, -, hU, hV⟩ := hθ13
      exact hW ⟨θ, hinj, hU, hV⟩

theorem exists_weakPhan_D4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) :
    ∃ R : Fin 4 → Subgroup (spinGroup (quadPlus 4 (GaloisField p e))),
      (∀ k, R k ∈ longestFundamental (plusDatum 4 (GaloisField p e) (by norm_num))) ∧
      (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i →
        ∀ a ∈ R i, ∀ b ∈ R j, a * b = b * a) ∧
      (∀ i j : Fin 4, edgeD 4 i j →
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W (R i) (R j)) := by
  obtain ⟨ε, hε, h4, hεs⟩ := exists_eps (e := e) hp2
  let fr : Fin 4 → Frame (quadPlus 4 (GaloisField p e)) :=
    ![frame0, frame1 ε hε h4, frame2, (frame2 (F := GaloisField p e)).swap]
  choose R hRmem hRspec using fun k => exists_lift_frame hp2 hq (fr k)
  exact ⟨R, hRmem, weakPhan_of_lifts hp2 hq hε h4 hεs R hRspec⟩

end CFSG.ClassicalInvolution.PhanD4
