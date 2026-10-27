module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointProp34
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFx
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  Polynomial Subgroup

theorem exists_pow_four_ne_one {F : Type*} [Field F] [Finite F] (hF : 5 < Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 4 ≠ 1 := by
  set P : F[X] := X * (X ^ 4 - C 1) with hP
  have h1 : (X ^ 4 - C 1 : F[X]).Monic := monic_X_pow_sub_C 1 (by norm_num)
  have hP0 : P ≠ 0 := (monic_X.mul h1).ne_zero
  have hdeg : P.natDegree = 5 := by
    rw [hP, monic_X.natDegree_mul h1, natDegree_X, natDegree_X_pow_sub_C]
  obtain ⟨a, ha⟩ := exists_eval_ne_zero_of_natDegree_lt_card P hP0 (by
    rw [hdeg, ← Nat.cast_card (α := F)]
    exact_mod_cast hF)
  simp only [hP, eval_mul, eval_sub, eval_pow, eval_X, eval_C, ne_eq, mul_eq_zero, not_or] at ha
  exact ⟨a, ha.1, fun h => ha.2 (by rw [h, sub_self])⟩

variable {G : Type} [Group G] [Finite G]

namespace IsPPoint

variable {M : Subgroup G} {x : G}

theorem centralizer_le_of_not_mem_zpowers {P : Sylow 3 G} (hin : PPointThreeInputs)
    (hS : D1Global G) (hD1 : D1For G) (hFC : FullCoreLocality G) (hloc : D1Local 3 P M)
    (h : IsPPoint 3 P M x) {u : G} (huP : u ∈ (P : Subgroup G)) (hu3 : u ^ 3 = 1)
    (hux : u ∉ zpowers x) : centralizer ({u} : Set G) ≤ M := by
  by_contra hCM
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨n, f, W, hn, hfadd, hfinj, hfx, hxf, hWQ, hW, hW3, htor, -⟩ :=
    h.exists_borelData_three hin hS hD1 hFC hloc
  have hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G) :=
    h.le_centralizer_three hin hS hD1 hFC hloc
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.elem.2.1] at this
  have hf0 : f 0 = 1 := by
    have h1 := hfadd 0 0
    rw [add_zero] at h1
    exact mul_left_cancel (h1.symm.trans (mul_one (f 0)).symm)
  have hu1 : u ≠ 1 := fun h1 => hux (h1 ▸ one_mem _)
  have huo : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hP4 : 4 ≤ Open.pRank 3 (P : Subgroup G) := four_le_pRank_sylow hloc.beta P
  have hrank : 3 ≤ Open.pRank 3 (M ⊓ centralizer ({u} : Set G)) :=
    (three_le_pRank_inf_centralizer hin.h313 P.isPGroup' hP4 huP hu3).trans
      (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 hp (inf_le_inf_right _ hPM))
  obtain ⟨m, hmM, hu'⟩ := exists_isPPoint hFC hloc (show IsPElement 3 M u from
    ⟨hPM huP, huo, hrank, hCM⟩)
  set u' : G := m * u * m⁻¹ with hu'def
  have hu'o : orderOf u' = 3 := hu'.elem.2.1
  have hu'3 : u' ^ 3 = 1 := by
    have := pow_orderOf_eq_one u'
    rwa [hu'o] at this
  have hu'W : u' ∈ W := hW3 u' ⟨hu'.mem, hPC hu'.mem⟩ hu'3
  have hPCu' : (P : Subgroup G) ≤ centralizer ({u'} : Set G) :=
    hu'.le_centralizer_three hin hS hD1 hFC hloc
  have hu'1 : u' ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hu'o
    omega
  have hFx : FxData f x := ⟨hx3, hfadd, hfinj, hfx, hxf⟩
  obtain ⟨a, ha0, ha4⟩ := exists_pow_four_ne_one (F := GaloisField 3 n) (by
    rw [GaloisField.card 3 n (by omega)]
    calc 5 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  obtain ⟨g, hgx, hgf⟩ := htor (Units.mk0 a ha0)
  have hgfx : ∀ (k : GaloisField 3 n) (e : ℕ), g * (f k * x ^ e) * g⁻¹ = f (a ^ 2 * k) * x ^ e :=
    fun k e => by
      calc g * (f k * x ^ e) * g⁻¹ = (g * f k * g⁻¹) * (g * x * g⁻¹) ^ e := by
            rw [conj_pow]; group
        _ = f (a ^ 2 * k) * x ^ e := by
            rw [hgx]
            have := hgf k
            simp only [Units.val_mk0] at this
            rw [this]
  obtain ⟨t, i, hi, hu'ti⟩ := (hW u').mp hu'W
  have hgW : g * u' * g⁻¹ ∈ W := by
    rw [hu'ti, hgfx]
    exact (hW _).mpr ⟨a ^ 2 * t, i, hi, rfl⟩
  have hL'Q : (zpowers u').map (MulAut.conj g).toMonoidHom ≤
      (P : Subgroup G) ⊓ centralizer ({u'} : Set G) := by
    rw [map_conj_zpowers, zpowers_le]
    exact ⟨(hWQ hgW).1, hPCu' (hWQ hgW).1⟩
  have hL'card : Nat.card ((zpowers u').map (MulAut.conj g).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, Nat.card_zpowers, hu'o]
  have hL'eq := hu'.eq_zpowers_of_isConj_three hin hS hD1 hFC hloc hL'Q hL'card ⟨g, rfl⟩
  have hmem : g * u' * g⁻¹ ∈ zpowers u' := by
    have : g * u' * g⁻¹ ∈ (zpowers u').map (MulAut.conj g).toMonoidHom :=
      ⟨u', mem_zpowers u', rfl⟩
    rw [hL'eq] at this
    exact this
  have ht0 : t = 0 := by
    by_contra ht
    obtain ⟨k, e, hk0, he, hnf⟩ := hFx.exists_normal_form ht hi
    have hmem' : f k * x ^ e ∈ zpowers u' := by
      rw [hu'ti, hnf]
      exact mem_zpowers _
    have hg1 : g * (f k * x ^ e) * g⁻¹ ∈ zpowers u' := by
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem'
      rw [← hj]
      rw [← conj_zpow]
      exact zpow_mem hmem j
    rw [hgfx, hu'ti, hnf] at hg1
    rcases hFx.fx_mem_zpowers he (mul_ne_zero (pow_ne_zero 2 ha0) hk0) hg1 with h1 | ⟨-, h1⟩
    · have h2 : a ^ 2 = 1 := by
        have := mul_right_cancel₀ hk0 (h1.trans (one_mul k).symm)
        exact this
      exact ha4 (by rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, h2, one_pow])
    · have h2 : a ^ 2 = -1 := by
        have := mul_right_cancel₀ hk0 (h1.trans (neg_one_mul k).symm)
        exact this
      exact ha4 (by rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, h2]; norm_num)
  rw [ht0, hf0, one_mul] at hu'ti
  have hzu' : zpowers u' = zpowers x := by
    interval_cases i
    · exact absurd (by simpa using hu'ti) hu'1
    · rw [hu'ti, pow_one]
    · rw [hu'ti, hFx.x_sq, zpowers_inv]
  have hLQ : zpowers u ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) := by
    rw [zpowers_le]
    exact ⟨huP, hPC huP⟩
  have hLcard : Nat.card (zpowers u) = 3 := by rw [Nat.card_zpowers, huo]
  have hLconj : zpowers u = (zpowers x).map (MulAut.conj m⁻¹).toMonoidHom := by
    rw [← hzu', map_conj_zpowers]
    congr 1
    simp only [hu'def]
    group
  exact hux (zpowers_le.mp (h.eq_zpowers_of_isConj_three hin hS hD1 hFC hloc hLQ hLcard
    ⟨m⁻¹, hLconj⟩).le)

end IsPPoint

end CFSG.LocalAnalysis.RankFourTheoremC
