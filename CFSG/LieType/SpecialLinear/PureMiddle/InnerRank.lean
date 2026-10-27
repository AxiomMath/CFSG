module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Kron
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.QuadraticDescent
public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3F.InvolutionRank
public import CFSG.Quasithin.Background.SmithB42G2FRank

public section

open Module
open Matrix
open CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.HardMathSupport.GuralnickMalle
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

namespace CFSG.LieType.SpecialLinear.PureMiddle

theorem minorMatrix_zero {R : Type*} [CommRing R] {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R) : minorMatrix 0 M = 1 := by
  ext s t
  rw [minorMatrix, Matrix.of_apply]
  have hst : s = t := by
    apply Subtype.ext
    rw [Finset.card_eq_zero.mp (Set.powersetCard.card_eq s),
      Finset.card_eq_zero.mp (Set.powersetCard.card_eq t)]
  subst hst
  rw [Matrix.one_apply, if_pos rfl, minor]
  exact Matrix.det_isEmpty

theorem card_powersetCard_fin_six_zero :
    Fintype.card (Set.powersetCard (Fin 6) 0) = 1 := by
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
  simp

theorem card_powersetCard_fin_six_three :
    Fintype.card (Set.powersetCard (Fin 6) 3) = 20 := by
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
  simp
  decide

theorem card_powersetCard_fin_six {n : ℕ} (hn : n = 0 ∨ n = 3) :
    Fintype.card (Set.powersetCard (Fin 6) n) = if n = 3 then 20 else 1 := by
  rcases hn with rfl | rfl
  · rw [if_neg (by decide : ¬ (0 : ℕ) = 3), card_powersetCard_fin_six_zero]
  · rw [if_pos rfl, card_powersetCard_fin_six_three]

theorem six_le_rank_minor_sub_one {K : Type} [Field K] [Finite K] [CharP K 2]
    (g : Matrix (Fin 6) (Fin 6) K) (hg : g * g = 1) (hg1 : g ≠ 1) :
    6 ≤ (Matrix.of (fun s t : Set.powersetCard (Fin 6) 3 => minor g s t) - 1).rank := by
  classical
  let a : GL (Fin 6) K := ⟨g, g, hg, hg⟩
  have hcoe : (a : Matrix (Fin 6) (Fin 6) K) = g := rfl
  have ha : a * a = 1 := Units.ext (by simpa [hcoe] using hg)
  have ha1 : a ≠ 1 := by
    intro haeq
    apply hg1
    have h2 := congrArg (fun u : GL (Fin 6) K => (u : Matrix (Fin 6) (Fin 6) K)) haeq
    simpa [hcoe] using h2
  have hbound := finrank_fixSubGen_closure_add_two_mul_natRank_le K a ha ha1
  have hnat : natRank a = (g - 1).rank := by
    rw [natRank_eq_rank, hcoe]
  have hpos : 1 ≤ (g - 1).rank := by
    rw [← hnat]
    exact one_le_natRank ha1
  let B : Basis (Set.powersetCard (Fin 6) 3) K (⋀[K]^3 (Fin 6 → K)) :=
    (Pi.basisFun K (Fin 6)).exteriorPower 3
  have hrep : (glExterior3Rep K) a = exteriorPower.map 3 (Matrix.toLin' g) := by
    rw [glExterior3Rep_apply, glNaturalRep_eq_toLin, hcoe]
  have hmat : LinearMap.toMatrix B B ((glExterior3Rep K) a - 1) =
      Matrix.of (fun s t : Set.powersetCard (Fin 6) 3 => minor g s t) - 1 := by
    have hsub : LinearMap.toMatrix B B ((glExterior3Rep K) a - 1) =
        LinearMap.toMatrix B B ((glExterior3Rep K) a) -
          LinearMap.toMatrix B B (1 : Module.End K (⋀[K]^3 (Fin 6 → K))) :=
      map_sub (LinearMap.toMatrix B B) ((glExterior3Rep K) a) 1
    rw [hsub, LinearMap.toMatrix_one]
    have hmat_z : LinearMap.toMatrix B B ((glExterior3Rep K) a) =
        Matrix.of (fun s t : Set.powersetCard (Fin 6) 3 => minor g s t) := by
      rw [hrep]
      ext s t
      rw [LinearMap.toMatrix_apply, Matrix.of_apply]
      exact repr_exteriorPower_map_eq_minor g s t
    rw [hmat_z]
  have hrank : Module.finrank K (LinearMap.range ((glExterior3Rep K) a - 1)) =
      (Matrix.of (fun s t : Set.powersetCard (Fin 6) 3 => minor g s t) - 1).rank := by
    have h := Matrix.rank_eq_finrank_range_toLin
      (LinearMap.toMatrix B B ((glExterior3Rep K) a - 1)) B B
    rw [Matrix.toLin_toMatrix] at h
    rw [← h, hmat]
  have hdim : Module.finrank K (⋀[K]^3 (Fin 6 → K)) = 20 := by
    rw [exteriorPower.finrank_eq]
    simp
    decide
  have hrn := LinearMap.finrank_range_add_finrank_ker ((glExterior3Rep K) a - 1)
  rw [hdim, hrank] at hrn
  have hfix := fixSubGen_closure_singleton (glExterior3Rep K) a
  rw [hfix, hnat] at hbound
  omega

theorem six_le_rank_minor_map_sub_one {K k : Type} [Field K] [Finite K] [CharP K 2]
    [Field k] (φ : K →+* k) (g : Matrix (Fin 6) (Fin 6) K) (hg : g * g = 1)
    (hg1 : g ≠ 1) :
    6 ≤ (Matrix.of (fun s t : Set.powersetCard (Fin 6) 3 => minor (g.map φ) s t) - 1).rank := by
  have h1 : (minorMatrix 3 (g.map φ) - 1).rank = (minorMatrix 3 g - 1).rank := by
    rw [minorMatrix_map φ 3 g]
    exact CFSG.Quasithin.B42G2F.rank_map_sub_one φ (minorMatrix 3 g)
  show 6 ≤ (minorMatrix 3 (g.map φ) - 1).rank
  rw [h1]
  exact six_le_rank_minor_sub_one g hg hg1

theorem card_sub_two_mul_rank_minorMatrix_le {K k : Type} [Field K] [Finite K] [CharP K 2]
    [Field k] (φ : K →+* k) (g : Matrix (Fin 6) (Fin 6) K) (hg : g * g = 1)
    (hg1 : g ≠ 1) (n : ℕ) (hn : n = 0 ∨ n = 3) :
    Fintype.card (Set.powersetCard (Fin 6) n) -
        2 * (minorMatrix n (g.map φ) - 1).rank ≤
      if n = 3 then 8 else 1 := by
  rcases hn with rfl | rfl
  · rw [if_neg (by decide : ¬ (0 : ℕ) = 3), card_powersetCard_fin_six_zero,
      minorMatrix_zero (g.map φ), sub_self, Matrix.rank_zero]
  · rw [if_pos rfl, card_powersetCard_fin_six_three]
    have h6 : 6 ≤ (minorMatrix 3 (g.map φ) - 1).rank :=
      six_le_rank_minor_map_sub_one φ g hg hg1
    omega

theorem twelve_mul_add_pow_eight_le_pow_twenty {h : ℕ} (hh : 1 ≤ h) :
    12 * h + 8 ^ h ≤ 20 ^ h := by
  induction h, hh using Nat.le_induction with
  | base => norm_num
  | succ h hh ih =>
    rw [pow_succ, pow_succ]
    have h1 : 12 * (h + 1) + 8 ^ h * 8 ≤ (12 * h + 8 ^ h) * 20 := by omega
    have h2 : (12 * h + 8 ^ h) * 20 ≤ 20 ^ h * 20 := Nat.mul_le_mul_right 20 ih
    exact h1.trans h2

theorem twenty_four_mul_add_pow_eight_le_pow_twenty {h : ℕ} (hh : 2 ≤ h) :
    24 * h + 8 ^ h ≤ 20 ^ h := by
  induction h, hh using Nat.le_induction with
  | base => norm_num
  | succ h hh ih =>
    rw [pow_succ, pow_succ]
    have h1 : 24 * (h + 1) + 8 ^ h * 8 ≤ (24 * h + 8 ^ h) * 20 := by omega
    have h2 : (24 * h + 8 ^ h) * 20 ≤ 20 ^ h * 20 := Nat.mul_le_mul_right 20 ih
    exact h1.trans h2

theorem pow_le_two_mul_rank_kronMinor_sub_one_add_pow {K k : Type} [Field K] [Finite K]
    [CharP K 2] [Field k] [CharP k 2] {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    (hd : ∀ i, d i = 0 ∨ d i = 3) (φ : ι → (K →+* k))
    (g : Matrix (Fin 6) (Fin 6) K) (hg : g * g = 1) (hg1 : g ≠ 1) :
    20 ^ (Finset.univ.filter fun i => d i = 3).card ≤
      2 * (kronMinor (n := 6) (d := d) (fun i => g.map (φ i)) - 1).rank +
        8 ^ (Finset.univ.filter fun i => d i = 3).card := by
  classical
  set h := (Finset.univ.filter fun i => d i = 3).card with hh
  have hne : ∀ i, Nonempty (Set.powersetCard (Fin 6) (d i)) := fun i => by
    apply Fintype.card_pos_iff.mp
    rcases hd i with h0 | h3
    · rw [h0, card_powersetCard_fin_six_zero]
      norm_num
    · rw [h3, card_powersetCard_fin_six_three]
      norm_num
  have hz : ∀ i, minorMatrix (d i) (g.map (φ i)) *
      minorMatrix (d i) (g.map (φ i)) = 1 := by
    intro i
    rw [show minorMatrix (d i) (g.map (φ i)) * minorMatrix (d i) (g.map (φ i)) =
        minorMatrix (d i) ((g.map (φ i)) * (g.map (φ i))) from
      (minorMatrix_mul (d i) (g.map (φ i)) (g.map (φ i))).symm]
    have hM : (g.map (φ i)) * (g.map (φ i)) = 1 := by
      rw [← Matrix.map_mul, hg]
      simp
    rw [hM, minorMatrix_one]
  have hkron : kronMinor (n := 6) (d := d) (fun i => g.map (φ i)) =
      CFSG.QuasithinUnique.Setup.X7a.kron
        (fun i => minorMatrix (d i) (g.map (φ i))) := rfl
  have hdep := @CFSG.Quasithin.B42G2F.rank_kron_sub_one_dep k _ ι _ _
    (fun i => Set.powersetCard (Fin 6) (d i)) _ _ _ hne
    (fun i => minorMatrix (d i) (g.map (φ i))) hz
  have hfac : ∀ i, Fintype.card (Set.powersetCard (Fin 6) (d i)) -
      2 * (minorMatrix (d i) (g.map (φ i)) - 1).rank ≤
      if d i = 3 then 8 else 1 :=
    fun i => card_sub_two_mul_rank_minorMatrix_le (φ i) g hg hg1 (d i) (hd i)
  have hprod_le : ∏ i, (Fintype.card (Set.powersetCard (Fin 6) (d i)) -
      2 * (minorMatrix (d i) (g.map (φ i)) - 1).rank) ≤ 8 ^ h := by
    calc ∏ i, (Fintype.card (Set.powersetCard (Fin 6) (d i)) -
          2 * (minorMatrix (d i) (g.map (φ i)) - 1).rank)
        ≤ ∏ i, (if d i = 3 then 8 else 1) :=
          Finset.prod_le_prod fun i _ => hfac i
      _ = 8 ^ h := by
          rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, hh]
  have hprod_card : ∏ i, Fintype.card (Set.powersetCard (Fin 6) (d i)) = 20 ^ h := by
    calc ∏ i, Fintype.card (Set.powersetCard (Fin 6) (d i))
        = ∏ i, (if d i = 3 then 20 else 1) :=
          Finset.prod_congr rfl fun i _ => card_powersetCard_fin_six (hd i)
      _ = 20 ^ h := by
          rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, hh]
  have hdep' : (kronMinor (n := 6) (d := d) (fun i => g.map (φ i)) - 1).rank * 2 +
      ∏ i, (Fintype.card (Set.powersetCard (Fin 6) (d i)) -
        2 * (minorMatrix (d i) (g.map (φ i)) - 1).rank) = 20 ^ h := by
    rw [hkron]
    exact hdep.trans hprod_card
  omega

theorem six_mul_le_rank_kronMinor_sub_one {K k : Type} [Field K] [Finite K] [CharP K 2]
    [Field k] [CharP k 2] {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    (hd : ∀ i, d i = 0 ∨ d i = 3) (φ : ι → (K →+* k))
    (g : Matrix (Fin 6) (Fin 6) K) (hg : g * g = 1) (hg1 : g ≠ 1)
    (hh : 1 ≤ (Finset.univ.filter fun i => d i = 3).card) :
    6 * (Finset.univ.filter fun i => d i = 3).card ≤
      (kronMinor (n := 6) (d := d) (fun i => g.map (φ i)) - 1).rank := by
  have hmain := pow_le_two_mul_rank_kronMinor_sub_one_add_pow d hd φ g hg hg1
  have hineq := twelve_mul_add_pow_eight_le_pow_twenty hh
  omega

theorem twelve_mul_le_rank_kronMinor_sub_one {K k : Type} [Field K] [Finite K] [CharP K 2]
    [Field k] [CharP k 2] {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    (hd : ∀ i, d i = 0 ∨ d i = 3) (φ : ι → (K →+* k))
    (g : Matrix (Fin 6) (Fin 6) K) (hg : g * g = 1) (hg1 : g ≠ 1)
    (hh : 2 ≤ (Finset.univ.filter fun i => d i = 3).card) :
    12 * (Finset.univ.filter fun i => d i = 3).card ≤
      (kronMinor (n := 6) (d := d) (fun i => g.map (φ i)) - 1).rank := by
  have hmain := pow_le_two_mul_rank_kronMinor_sub_one_add_pow d hd φ g hg hg1
  have hineq := twenty_four_mul_add_pow_eight_le_pow_twenty hh
  omega

end CFSG.LieType.SpecialLinear.PureMiddle
