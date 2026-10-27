module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerPerfect
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFusion

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect)

section Identities

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ P₃ : HypPair Q}

theorem commutatorElement_eichler_e_f (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃)
    (t : K) :
    ⁅eichler Q P₃.e (t • P₂.e), eichler Q P₁.e P₃.f⁆ = eichler Q P₁.e (t • P₂.e) := by
  have hw : polar Q P₃.e (t • P₂.e) = 0 := by
    rw [polar_smul_right_eq, polar_comm, h₂₃.ee, mul_zero]
  have hg := eichler_mem_orthogonalGroup Q P₃.e (t • P₂.e)
  have hgu : eichler Q P₃.e (t • P₂.e) P₁.e = P₁.e :=
    eichler_apply_of_polar_eq_zero h₁₃.ee (by rw [polar_smul_right_eq, h₁₂.ee, mul_zero])
  rw [commutatorElement_eichler hg hgu h₁₃.ef]
  congr 1
  rw [eichler_apply P₃.Q_e hw, P₃.polar_fe, polar_smul_right_eq, polar_comm Q P₃.f P₂.e, h₂₃.ef,
    map_smul_eq_sq, P₂.Q_e]
  module

theorem commutatorElement_eichler_e_e (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    ⁅eichler Q P₂.e ((-1 : K) • P₃.f), eichler Q P₁.e P₃.e⁆ = eichler Q P₁.e P₂.e := by
  have hw : polar Q P₂.e ((-1 : K) • P₃.f) = 0 := by rw [polar_smul_right_eq, h₂₃.ef, mul_zero]
  have hg := eichler_mem_orthogonalGroup Q P₂.e ((-1 : K) • P₃.f)
  have hgu : eichler Q P₂.e ((-1 : K) • P₃.f) P₁.e = P₁.e :=
    eichler_apply_of_polar_eq_zero h₁₂.ee (by rw [polar_smul_right_eq, h₁₃.ef, mul_zero])
  rw [commutatorElement_eichler hg hgu h₁₃.ee]
  congr 1
  rw [eichler_apply P₂.Q_e hw, polar_comm Q P₃.e P₂.e, h₂₃.ee, polar_smul_right_eq,
    P₃.polar_ef]
  module

end Identities

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem conj_mem_perfectCore {G : Type*} [Group G] {H : Subgroup G} {c p : G} (hc : c ∈ H)
    (hp : p ∈ perfectCore H) : c * p * c⁻¹ ∈ perfectCore H :=
  (mem_normalizer_iff.mp ((Subgroup.le_normalizer.trans
    (CFSG.Quasithin.normalizer_le_normalizer_perfectCore H)) hc) p).mp hp

theorem rootPairElt_mem_perfectCore_of {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    {a a' b b' c c' e e' : Fin d} (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hk : IsHypCoord Q c c') (hl : IsHypCoord Q e e') (hij : PairDisjoint a a' b b')
    (hik : PairDisjoint a a' c c') (hjk : PairDisjoint b b' c c') (hil : PairDisjoint a a' e e')
    (hjl : PairDisjoint b b' e e') (hkl : PairDisjoint c c' e e')
    (hQ : (polarBilin Q).Nondegenerate)
    (hS : ⁅stabPairsBar Q a a' b b', stabPairsBar Q a a' b b'⁆ = stabPairsBar Q a a' b b')
    {z₀ : matrixProjectiveDerived Q}
    (hz₀ : z₀ = rootPairElt hQ (hi.orth hj hij) (hi.orth hk hik) (hj.orth hk hjk)) :
    z₀ ∈ perfectCore (centralizer {z₀}) := by
  subst hz₀
  have hik' := hi.orth hk hik
  have hil' := hi.orth hl hil
  have hjk' := hj.orth hk hjk
  have hjl' := hj.orth hl hjl
  have hkl' := hk.orth hl hkl
  have hij' := hi.orth hj hij
  have hT := exists_totallySingular_of_hypPairs hij' hik' hjk'
  set C := centralizer {rootPairElt hQ hij' hik' hjk'} with hC
  have hEΩ := eichler_mem_orthDerived hQ hT
  have hCeq := centralizer_rootPairElt hQ hij' hik' hjk'
  have hRC : ∀ X : orthDerived Q,
      (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ rootRadical _ hi.hypPair hj.hypPair →
      projHom _ X ∈ C := fun X hX => by
    rw [hC, hCeq]
    exact mem_sup_left ⟨X, mem_subgroupOf.mpr hX, rfl⟩
  have hS' : stabPairsBar Q a a' b b' ≤ perfectCore C := by
    refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ hS
    rw [hC, hCeq]
    exact (stabPairsBar_le_rootLeviBar hi hj).trans le_sup_right
  have ha : projHom _ ⟨eichler Q hl.hypPair.e ((1 : K) • hk.hypPair.e), hEΩ _ _⟩ ∈
      perfectCore C := by
    refine hS' ⟨⟨_, hEΩ _ _⟩, mem_subgroupOf.mpr ?_, rfl⟩
    have h1 : ∀ v : Fin d → K, polar Q v hl.hypPair.e = 0 →
        polar Q v ((1 : K) • hk.hypPair.e) = 0 →
        eichler Q hl.hypPair.e ((1 : K) • hk.hypPair.e) v = v :=
      fun v h1 h2 => eichler_apply_of_polar_eq_zero h1 h2
    refine ⟨⟨h1 _ hil'.ee ?_, h1 _ hil'.fe ?_⟩, h1 _ hjl'.ee ?_, h1 _ hjl'.fe ?_⟩
    · rw [polar_smul_right_eq]; exact mul_eq_zero_of_right _ hik'.ee
    · rw [polar_smul_right_eq]; exact mul_eq_zero_of_right _ hik'.fe
    · rw [polar_smul_right_eq]; exact mul_eq_zero_of_right _ hjk'.ee
    · rw [polar_smul_right_eq]; exact mul_eq_zero_of_right _ hjk'.fe
  have hb : projHom _ ⟨eichler Q hi.hypPair.e hl.hypPair.f, hEΩ _ _⟩ ∈ C :=
    hRC _ (eichler_mem_rootRadical_left hij' hil'.ef hjl'.ef)
  have hik_mem : projHom _ ⟨eichler Q hi.hypPair.e hk.hypPair.e, hEΩ _ _⟩ ∈ perfectCore C := by
    have h := mul_mem ha (conj_mem_perfectCore hb (inv_mem ha))
    have e : projHom Q ⟨eichler Q hi.hypPair.e hk.hypPair.e, hEΩ _ _⟩ =
        projHom _ ⟨eichler Q hl.hypPair.e ((1 : K) • hk.hypPair.e), hEΩ _ _⟩ *
          (projHom _ ⟨eichler Q hi.hypPair.e hl.hypPair.f, hEΩ _ _⟩ *
            (projHom _ ⟨eichler Q hl.hypPair.e ((1 : K) • hk.hypPair.e), hEΩ _ _⟩)⁻¹ *
              (projHom _ ⟨eichler Q hi.hypPair.e hl.hypPair.f, hEΩ _ _⟩)⁻¹) := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have hid := commutatorElement_eichler_e_f hik' hil' hkl' (1 : K)
      rw [one_smul] at hid
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hid, commutatorElement_def, one_smul]
      group
    rw [e]
    exact h
  have hc : projHom _ ⟨eichler Q hj.hypPair.e ((-1 : K) • hk.hypPair.f), hEΩ _ _⟩ ∈ C :=
    hRC _ (eichler_mem_rootRadical_right hij' (by rw [polar_smul_right_eq, hik'.ef, mul_zero])
      (by rw [polar_smul_right_eq, hjk'.ef, mul_zero]))
  have h := mul_mem (conj_mem_perfectCore hc hik_mem) (inv_mem hik_mem)
  have e : rootPairElt hQ hij' hik' hjk' =
      projHom _ ⟨eichler Q hj.hypPair.e ((-1 : K) • hk.hypPair.f), hEΩ _ _⟩ *
        projHom _ ⟨eichler Q hi.hypPair.e hk.hypPair.e, hEΩ _ _⟩ *
        (projHom _ ⟨eichler Q hj.hypPair.e ((-1 : K) • hk.hypPair.f), hEΩ _ _⟩)⁻¹ *
        (projHom _ ⟨eichler Q hi.hypPair.e hk.hypPair.e, hEΩ _ _⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, rootPairElt]
    congr 1
    apply Subtype.ext
    have hid := commutatorElement_eichler_e_e hij' hik' hjk' (K := K)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hid, commutatorElement_def]
  rw [e]
  exact h

theorem plusRootElt_mem_perfectCore (hn : 5 ≤ n) {i j k l : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) :
    plusRootElt K (by omega) hij hik hjk ∈
      perfectCore (centralizer {plusRootElt K (by omega) hij hik hjk}) :=
  rootPairElt_mem_perfectCore_of _ _ _ (isHypCoord_coordinateQuadPlus (K := K) l)
    (pairDisjoint_plus hij) (pairDisjoint_plus hik) (pairDisjoint_plus hjk)
    (pairDisjoint_plus hil) (pairDisjoint_plus hjl) (pairDisjoint_plus hkl) _
    (Subgroup.isPerfect_iff.mp (isQuasisimple_stabTwoBar (K := K) hn hij).1.1) rfl

theorem exists_perfect_le_centralizer_of_isLongRoot_plus (hn : 5 ≤ n)
    {z : matrixProjectiveDerived (coordinateQuadPlus n K)} (hz : IsLongRoot _ z) :
    ∃ H : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)),
      ⁅H, H⁆ = H ∧ z ∈ H ∧ H ≤ centralizer {z} := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h03 : (⟨0, by omega⟩ : Fin n) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
  have h13 : (⟨1, by omega⟩ : Fin n) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
  have h23 : (⟨2, by omega⟩ : Fin n) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
  have hQ := (regular_coordinateQuadPlus n K (by omega)).1
  have hi := isHypCoord_coordinateQuadPlus (K := K) (⟨0, by omega⟩ : Fin n)
  have hj := isHypCoord_coordinateQuadPlus (K := K) (⟨1, by omega⟩ : Fin n)
  have hk := isHypCoord_coordinateQuadPlus (K := K) (⟨2, by omega⟩ : Fin n)
  have hz₀ : IsLongRoot _ (plusRootElt K (by omega) h01 h02 h12) :=
    isLongRoot_rootPairElt hQ (hi.orth hj (pairDisjoint_plus h01))
      (hi.orth hk (pairDisjoint_plus h02)) (hj.orth hk (pairDisjoint_plus h12))
  have hmem := plusRootElt_mem_perfectCore (K := K) hn h01 h02 h12 h03 h13 h23
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_isLongRoot_plus (by omega) hz₀ hz)
  refine ⟨(perfectCore (centralizer {plusRootElt K (by omega) h01 h02 h12})).map
    (MulAut.conj c).toMonoidHom, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, perfectCore_perfect]
  · rw [← hc]
    exact ⟨_, hmem, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h := mem_centralizer_singleton_iff.mp (perfectCore_le _ hy)
    rw [mem_centralizer_singleton_iff, ← hc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * y * c⁻¹ * (c * plusRootElt K (by omega) h01 h02 h12 * c⁻¹) =
        c * (y * plusRootElt K (by omega) h01 h02 h12) * c⁻¹ := by group
      _ = c * (plusRootElt K (by omega) h01 h02 h12 * y) * c⁻¹ := by rw [h]
      _ = c * plusRootElt K (by omega) h01 h02 h12 * c⁻¹ * (c * y * c⁻¹) := by group

end Core

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_isLongRoot_conj_plus_of_five_le (hset : SeitzSetting G L) {n f : ℕ} (hn : 5 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (g : G) (hgL : g⁻¹ * t * g ∈ L) :
    ¬ IsLongRoot _ (e ⟨g⁻¹ * t * g, hgL⟩) :=
  not_isLongRoot_conj_of_perfect hset e
    (isSolvable_outer_of_mulEquiv_plus (by omega) (LinearPilot.one_le_of_card_eq_two_pow hK) hK e)
    (fun _ hz => exists_perfect_le_centralizer_of_isLongRoot_plus hn hz) htC ht g hgL

theorem not_forall_commute_sylow_conj_plus_of_five_le (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 5 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u := by
  intro U g hgL hcomm
  exact not_isLongRoot_conj_plus_of_five_le hset hn hK e htC ht g hgL
    (isLongRoot_of_commute_sylow_plus_of_mulEquiv e (by omega) U
      (conj_ne_one_of_orderOf ht g hgL) fun u hu => Subtype.ext (hcomm u hu))

theorem exists_conj_eq_mul_longRoot_twoSided_plus_of_habel_of_five_le (hset : SeitzSetting G L)
    {n f : ℕ} (hn : 5 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L) :
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
      (not_forall_commute_sylow_conj_plus_of_five_le hset hn hK e htC ht)
      (autU2_plus_of_mulEquiv e (by omega)) habel
  refine ⟨x, z, hz, hxz, ⟨hz.1, ?_⟩, ⟨hz.2, ?_⟩, hact⟩
  · exact isLongRoot_of_commute_sylow_plus_of_mulEquiv e (by omega) U
      (fun h1 => hz1 (congrArg Subtype.val h1)) fun u hu => Subtype.ext (hU u hu)
  · exact isLongRoot_of_commute_sylow_plus_of_mulEquiv ((conjugateMulEquiv L x).symm.trans e)
      (by omega) U' (fun h1 => hz1 (congrArg Subtype.val h1)) fun u hu => Subtype.ext (hU' u hu)

theorem exists_conj_eq_mul_longRoot_plus_or_residual_of_five_le (hset : SeitzSetting G L)
    {n f : ℕ} (hn : 5 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    (∃ (g : G) (z : L), IsLongRoot _ (e z) ∧ g⁻¹ * t * g = t * (z : G)) ∨
      (Even f ∧ ∃ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) ∧
        ∃ y ∈ (S : Subgroup G), ∃ w ∈ (S : Subgroup G), y * w * y⁻¹ * w⁻¹ ∉ L) := by
  by_cases habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L
  · left
    obtain ⟨x, z, -, hxz, ⟨hzL, hzl⟩, -, -⟩ :=
      exists_conj_eq_mul_longRoot_twoSided_plus_of_habel_of_five_le hset hn hK e ht hKt habel
    exact ⟨x, ⟨z, hzL⟩, hzl, hxz⟩
  · right
    refine ⟨?_, ?_⟩
    · by_contra hfe
      exact habel (habel_plus_of_odd hset hn (Nat.not_even_iff_odd.mp hfe) hK e ht hKt)
    · push Not at habel
      obtain ⟨S, hS, y, hy, w, hw, hyw⟩ := habel
      exact ⟨S, hS, y, hy, w, hw, hyw⟩

theorem exists_conj_eq_mul_longRoot_plus_of_odd (hset : SeitzSetting G L) {n f : ℕ} (hn : 5 ≤ n)
    (hf : Odd f) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ (g : G) (z : L), IsLongRoot _ (e z) ∧ g⁻¹ * t * g = t * (z : G) := by
  rcases exists_conj_eq_mul_longRoot_plus_or_residual_of_five_le hset hn hK e ht hKt with h | h
  · exact h
  · exact absurd h.1 (Nat.not_even_iff_odd.mpr hf)

end Setting

end CFSG.SeitzReduction.OmegaPilot
