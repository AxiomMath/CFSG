module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerSylowTransfer
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer

public section

namespace CFSG.AGLEmbedding.TwoGenInner

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)

theorem exists_unit_orderOf_eq_lin {K : Type} [Field K] [Finite K] {f p : ℕ}
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hpq : p ∣ 2 ^ f - 1) : ∃ ω : Kˣ, orderOf ω = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hunits : Nat.card Kˣ = Nat.card K - 1 := by
    classical
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have hdvd : p ∣ Nat.card Kˣ := by
    rw [hunits, hK]
    exact hpq
  exact exists_prime_orderOf_dvd_card' p hdvd

section Torus

variable {K : Type} [Field K] {n : ℕ}

@[expose] def torusDiag (ω : Kˣ) (n : ℕ) : Fin n → K := fun i =>
  if (i : ℕ) = 0 then (ω : K) else if (i : ℕ) = 1 then ((ω⁻¹ : Kˣ) : K) else 1

theorem prod_torusDiag (ω : Kˣ) (hn : 2 ≤ n) : ∏ i : Fin n, torusDiag (K := K) ω n i = 1 := by
  have h0 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  rw [Finset.prod_eq_mul (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ h0]
  · simp [torusDiag]
  · intro c _ hc
    have h0' : (c : ℕ) ≠ 0 := fun hh => hc.1 (Fin.ext hh)
    have h1' : (c : ℕ) ≠ 1 := fun hh => hc.2 (Fin.ext hh)
    simp [torusDiag, h0', h1']
  · intro hh
    exact absurd (Finset.mem_univ _) hh
  · intro hh
    exact absurd (Finset.mem_univ _) hh

@[expose] def torusLinElement (ω : Kˣ) (hn : 2 ≤ n) : Matrix.SpecialLinearGroup (Fin n) K :=
  ⟨Matrix.diagonal (torusDiag ω n), by rw [Matrix.det_diagonal, prod_torusDiag ω hn]⟩

theorem torusLinElement_mem_upperTriangular (ω : Kˣ) (hn : 2 ≤ n) :
    torusLinElement (K := K) ω hn ∈ upperTriangular n K := by
  intro i j hij
  exact diagonal_apply_ne _ (ne_of_gt hij)

theorem torusLinElement_pow {ω : Kˣ} {p : ℕ} (hω : ω ^ p = 1) (hn : 2 ≤ n) :
    torusLinElement (K := K) ω hn ^ p = 1 := by
  have h1 : ∀ i : Fin n, torusDiag (K := K) ω n i ^ p = 1 := by
    intro i
    have hω' : ((ω : Kˣ) : K) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hω, Units.val_one]
    simp only [torusDiag]
    split_ifs
    · exact hω'
    · rw [← Units.val_pow_eq_pow_val, inv_pow, hω, inv_one, Units.val_one]
    · exact one_pow p
  have h2 : (fun i => torusDiag (K := K) ω n i ^ p) = fun _ => 1 := funext h1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  show ((Matrix.diagonal (torusDiag ω n)) ^ p) i j = (1 : Matrix (Fin n) (Fin n) K) i j
  rw [Matrix.diagonal_pow, Pi.pow_def, h2, Matrix.diagonal_one]

theorem torusLinElement_not_mem_scalars {ω : Kˣ} (hω : ω ≠ 1) (hn : 3 ≤ n) :
    torusLinElement (K := K) ω (by omega) ∉ scalars n K := by
  intro hZ
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hZ
  have hmat : (Matrix.diagonal (torusDiag (K := K) ω n) : Matrix (Fin n) (Fin n) K) =
      Matrix.scalar (Fin n) (c : K) := hc
  have e0 := congrFun (congrFun hmat ⟨0, by omega⟩) ⟨0, by omega⟩
  have e2 := congrFun (congrFun hmat ⟨2, by omega⟩) ⟨2, by omega⟩
  simp [torusDiag, Matrix.scalar_apply] at e0 e2
  exact hω (Units.ext (by rw [e0, ← e2]; simp))

end Torus

theorem exists_normalizer_element_lin {K : Type} [Field K] [Finite K] [CharP K 2] {n p : ℕ}
    {ω : Kˣ} (hω : orderOf ω = p) (hp : p.Prime) (hn : 3 ≤ n) :
    ∃ a : projectiveSL n K, orderOf a = p ∧
      a ∈ Subgroup.normalizer ((projUnitriangular n K : Subgroup (projectiveSL n K)) :
        Set (projectiveSL n K)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hωp : ω ^ p = 1 := hω ▸ pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := fun h => by
    rw [h, orderOf_one] at hω
    exact hp.one_lt.ne hω
  refine ⟨proj n K (torusLinElement ω (by omega)), orderOf_eq_prime ?_ ?_, ?_⟩
  · rw [← map_pow, torusLinElement_pow hωp (by omega), map_one]
  · intro h1
    exact torusLinElement_not_mem_scalars hω1 hn (proj_eq_one_iff.1 h1)
  · rw [(sylow_normalizers 2 (by omega : 1 ≤ n)).2.1]
    exact Subgroup.mem_map_of_mem _ (torusLinElement_mem_upperTriangular ω (by omega))

theorem torusLin_model {K : Type} [Field K] [Finite K] {f n p : ℕ}
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hpq : p ∣ 2 ^ f - 1) (hn : 3 ≤ n)
    (Q : Sylow 2 (projectiveSL n K)) :
    p ∣ Nat.card ↥(Subgroup.normalizer (Q : Set (projectiveSL n K))) := by
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨ω, hω⟩ := exists_unit_orderOf_eq_lin hK hp hpq
  obtain ⟨a, hao, haN⟩ := exists_normalizer_element_lin (K := K) hω hp hn
  obtain ⟨Q₀, hQ₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (by omega : 1 ≤ n)
  have hmem : a ∈ Subgroup.normalizer ((Q₀ : Subgroup (projectiveSL n K)) :
      Set (projectiveSL n K)) := by
    rw [hQ₀]
    exact haN
  have h1 : p ∣ Nat.card ↥(Subgroup.normalizer ((Q₀ : Subgroup (projectiveSL n K)) :
      Set (projectiveSL n K))) := by
    have := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [hao] at this
  exact forall_dvd_card_normalizer Q₀ h1 Q

theorem torusLin : TorusLin := by
  intro Y _ _ L T n f p hp hp5 _ hmodel hdvd hT
  obtain ⟨⟨_, hf, hn2, _⟩, K, hF, hfin, hK, ⟨e⟩⟩ := hmodel
  have hpn : p ∣ n := hdvd.trans (Nat.gcd_dvd_left _ _)
  have hpq : p ∣ 2 ^ f - 1 := hdvd.trans (Nat.gcd_dvd_right _ _)
  have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd (by omega) hpn)
  let e' : (↥L ⧸ Subgroup.center ↥L) ≃* projectiveSL n K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  exact dvd_card_inf_normalizer_of_equiv hT e' fun Q => torusLin_model hK hp hpq (by omega) Q

end CFSG.AGLEmbedding.TwoGenInner
