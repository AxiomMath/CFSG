module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTenBasic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus)

section Minus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem exists_perfect_le_centralizer_of_isLongRoot_minus_of_five_le (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {z : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)} (hz : IsLongRoot _ z) :
    ∃ H : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)),
      ⁅H, H⁆ = H ∧ z ∈ H ∧ H ≤ centralizer {z} := by
  have hn1 : 1 ≤ n := by omega
  set i : Fin (n - 1) := ⟨0, by omega⟩
  set j : Fin (n - 1) := ⟨1, by omega⟩
  set k : Fin (n - 1) := ⟨2, by omega⟩
  set l : Fin (n - 1) := ⟨3, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  have hik : i ≠ k := by simp [i, k, Fin.ext_iff]
  have hjk : j ≠ k := by simp [j, k, Fin.ext_iff]
  have hil : i ≠ l := by simp [i, l, Fin.ext_iff]
  have hjl : j ≠ l := by simp [j, l, Fin.ext_iff]
  have hkl : k ≠ l := by simp [k, l, Fin.ext_iff]
  obtain ⟨hQ, -⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hi := isHypCoord_coordinateQuadMinus (K := K) hn1 b c i
  have hj := isHypCoord_coordinateQuadMinus (K := K) hn1 b c j
  have hk := isHypCoord_coordinateQuadMinus (K := K) hn1 b c k
  have hl := isHypCoord_coordinateQuadMinus (K := K) hn1 b c l
  obtain ⟨z₀, hz₀def⟩ : ∃ z₀, z₀ = rootPairElt hQ (hi.orth hj (pairDisjoint_minus hn1 hij))
      (hi.orth hk (pairDisjoint_minus hn1 hik)) (hj.orth hk (pairDisjoint_minus hn1 hjk)) :=
    ⟨_, rfl⟩
  have hz₀ : IsLongRoot _ z₀ := hz₀def ▸ isLongRoot_rootPairElt hQ
    (hi.orth hj (pairDisjoint_minus hn1 hij)) (hi.orth hk (pairDisjoint_minus hn1 hik))
    (hj.orth hk (pairDisjoint_minus hn1 hjk))
  have hmem := rootPairElt_mem_perfectCore_of hi hj hk hl (pairDisjoint_minus hn1 hij)
    (pairDisjoint_minus hn1 hik) (pairDisjoint_minus hn1 hjk) (pairDisjoint_minus hn1 hil)
    (pairDisjoint_minus hn1 hjl) (pairDisjoint_minus hn1 hkl) hQ
    (Subgroup.isPerfect_iff.mp
      (isQuasisimple_minusStabPairsBar_of_five_le (K := K) hn hirr hij).1.1)
    hz₀def
  obtain ⟨c', hc⟩ := isConj_iff.mp (isConj_of_isLongRoot_minus (by omega) hirr hz₀ hz)
  refine ⟨(CFSG.Quasithin.perfectCore (centralizer {z₀})).map (MulAut.conj c').toMonoidHom,
    ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, CFSG.Quasithin.perfectCore_perfect]
  · rw [← hc]
    exact ⟨_, hmem, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h := mem_centralizer_singleton_iff.mp (CFSG.Quasithin.perfectCore_le _ hy)
    rw [mem_centralizer_singleton_iff, ← hc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c' * y * c'⁻¹ * (c' * z₀ * c'⁻¹) = c' * (y * z₀) * c'⁻¹ := by group
      _ = c' * (z₀ * y) * c'⁻¹ := by rw [h]
      _ = c' * z₀ * c'⁻¹ * (c' * y * c'⁻¹) := by group

end Minus

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_isLongRoot_conj_minus_of_five_le (hset : SeitzSetting G L) {n f : ℕ} (hn : 5 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (g : G) (hgL : g⁻¹ * t * g ∈ L) :
    ¬ IsLongRoot _ (e ⟨g⁻¹ * t * g, hgL⟩) :=
  not_isLongRoot_conj_of_perfect hset e
    (isSolvable_outer_of_mulEquiv_minus (by omega) (LinearPilot.one_le_of_card_eq_two_pow hK) hK
      hirr e)
    (fun _ hz => exists_perfect_le_centralizer_of_isLongRoot_minus_of_five_le hn hirr hz) htC ht
    g hgL

theorem not_forall_commute_sylow_conj_minus_of_five_le (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 5 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u := by
  intro U g hgL hcomm
  exact not_isLongRoot_conj_minus_of_five_le hset hn hK hirr e htC ht g hgL
    (isLongRoot_of_commute_sylow_minus_of_mulEquiv (by omega) hirr e U
      (conj_ne_one_of_orderOf ht g hgL) fun u hu => Subtype.ext (hcomm u hu))

theorem exists_conj_eq_mul_longRoot_twoSided_minus_of_five_le (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 5 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsLongRoot _ (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsLongRoot _ (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  have htC := mem_centralizer_of_inf_eq hKt
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  have hLt : L ≤ centralizer ({t} : Set G) :=
    SeitzQ2.le_centralizer_singleton_of_mem_centralizer htC
  obtain ⟨x, z, hz, hxz, hz1, ⟨U, hU⟩, ⟨U', hU'⟩, hact⟩ :=
    exists_conj_eq_mul_twoSided_of_commutator_eq_top_of_autU2
      (SeitzQ2.commutator_eq_top_of_standardSetting hset.standardSetting) ht hLt hCN hKt
      (not_forall_commute_sylow_conj_minus_of_five_le hset hn hK hirr e htC ht)
      (autU2_minus_of_mulEquiv (by omega) hirr e)
      (habel_minus hset (by omega) hK hirr e ht hKt)
  refine ⟨x, z, hz, hxz, ⟨hz.1, ?_⟩, ⟨hz.2, ?_⟩, hact⟩
  · exact isLongRoot_of_commute_sylow_minus_of_mulEquiv (by omega) hirr e U
      (fun h1 => hz1 (congrArg Subtype.val h1)) fun u hu => Subtype.ext (hU u hu)
  · exact isLongRoot_of_commute_sylow_minus_of_mulEquiv (by omega) hirr
      ((conjugateMulEquiv L x).symm.trans e) U'
      (fun h1 => hz1 (congrArg Subtype.val h1)) fun u hu => Subtype.ext (hU' u hu)

end Setting

end CFSG.SeitzReduction.OmegaPilot
