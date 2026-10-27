module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFusionOuter
public import CFSG.LocalAnalysis.SeitzReduction.FusionGenericAutU2
public import CFSG.LocalAnalysis.SeitzReduction.FusionGenericAutU2Outer
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNotLongRoot

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem mem_centralizer_of_inf_eq {t : G}
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    t ∈ centralizer (L : Set G) :=
  (show t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) from hKt ▸ mem_zpowers t).1

theorem habel_minus (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L := by
  have htC := mem_centralizer_of_inf_eq hKt
  exact SeitzQ2.commutator_mem_of_sylow_le_centralizer_of_isCyclic_outer htC ht
    (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht)
    hKt (isCyclic_outer_of_mulEquiv_minus hn hirr hK e)

theorem exists_conj_eq_mul_longRoot_twoSided_minus (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
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
      (not_forall_commute_sylow_conj_minus hset hn hK hq hirr e htC ht)
      (autU2_minus_of_mulEquiv hn hirr e)
      (habel_minus hset hn hK hirr e ht hKt)
  refine ⟨x, z, hz, hxz, ⟨hz.1, ?_⟩, ⟨hz.2, ?_⟩, hact⟩
  · exact isLongRoot_of_commute_sylow_minus_of_mulEquiv hn hirr e U
      (fun h1 => hz1 (congrArg Subtype.val h1)) fun u hu => Subtype.ext (hU u hu)
  · exact isLongRoot_of_commute_sylow_minus_of_mulEquiv hn hirr
      ((conjugateMulEquiv L x).symm.trans e) U'
      (fun h1 => hz1 (congrArg Subtype.val h1)) fun u hu => Subtype.ext (hU' u hu)

theorem exists_conj_eq_mul_longRoot_minus (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ (g : G) (z : L), IsLongRoot _ (e z) ∧ g⁻¹ * t * g = t * (z : G) := by
  obtain ⟨x, z, -, hxz, ⟨hzL, hzl⟩, -, -⟩ :=
    exists_conj_eq_mul_longRoot_twoSided_minus hset hn hK hq hirr e ht hKt
  exact ⟨x, ⟨z, hzL⟩, hzl, hxz⟩

theorem habel_plus_of_odd (hset : SeitzSetting G L) {n f : ℕ} (hn : 5 ≤ n) (hf : Odd f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L := by
  have htC := mem_centralizer_of_inf_eq hKt
  exact commutator_mem_of_sylow_le_centralizer_of_isCyclic_outer_two htC ht
    (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht)
    hKt (isCyclic_map_outer_of_isPGroup_plus hn hf hK e)

theorem exists_conj_eq_mul_longRoot_twoSided_plus_of_habel (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 5 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (ht : orderOf t = 2)
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
      (not_forall_commute_sylow_conj_plus hset (by omega) hK hq e htC ht)
      (autU2_plus_of_mulEquiv e (by omega)) habel
  refine ⟨x, z, hz, hxz, ⟨hz.1, ?_⟩, ⟨hz.2, ?_⟩, hact⟩
  · exact isLongRoot_of_commute_sylow_plus_of_mulEquiv e (by omega) U
      (fun h1 => hz1 (congrArg Subtype.val h1)) fun u hu => Subtype.ext (hU u hu)
  · exact isLongRoot_of_commute_sylow_plus_of_mulEquiv ((conjugateMulEquiv L x).symm.trans e)
      (by omega) U' (fun h1 => hz1 (congrArg Subtype.val h1)) fun u hu => Subtype.ext (hU' u hu)

theorem exists_conj_eq_mul_longRoot_plus_or_residual (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 5 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    (∃ (g : G) (z : L), IsLongRoot _ (e z) ∧ g⁻¹ * t * g = t * (z : G)) ∨
      (Even f ∧ ∃ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) ∧
        ∃ y ∈ (S : Subgroup G), ∃ w ∈ (S : Subgroup G), y * w * y⁻¹ * w⁻¹ ∉ L) := by
  by_cases habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L
  · left
    obtain ⟨x, z, -, hxz, ⟨hzL, hzl⟩, -, -⟩ :=
      exists_conj_eq_mul_longRoot_twoSided_plus_of_habel hset hn hK hq e ht hKt habel
    exact ⟨x, ⟨z, hzL⟩, hzl, hxz⟩
  · right
    refine ⟨?_, ?_⟩
    · by_contra hfe
      exact habel (habel_plus_of_odd hset hn (Nat.not_even_iff_odd.mp hfe) hK e ht hKt)
    · push Not at habel
      obtain ⟨S, hS, y, hy, w, hw, hyw⟩ := habel
      exact ⟨S, hS, y, hy, w, hw, hyw⟩

omit [Finite G] in
theorem conj_mul_eq_mul_conj {t g : G} (htC : t ∈ centralizer (L : Set G)) {z : L}
    (hz : g⁻¹ * t * g = t * (z : G)) (c : L) :
    (g * (c : G))⁻¹ * t * (g * (c : G)) = t * ((c⁻¹ * z * c : L) : G) := by
  have hct : (c : G)⁻¹ * t = t * (c : G)⁻¹ :=
    (mem_centralizer_iff.mp htC _ (inv_mem c.2))
  calc (g * (c : G))⁻¹ * t * (g * (c : G)) = (c : G)⁻¹ * (g⁻¹ * t * g) * c := by group
    _ = (c : G)⁻¹ * t * (z : G) * c := by rw [hz]; group
    _ = t * (c : G)⁻¹ * (z : G) * c := by rw [hct]
    _ = t * ((c⁻¹ * z * c : L) : G) := by simp [mul_assoc]

omit [Finite G] in
theorem exists_conj_eq_mul_of_isConj {X : Type*} [Group X] (e : L ≃* X) {t g : G}
    (htC : t ∈ centralizer (L : Set G)) {z : L} (hz : g⁻¹ * t * g = t * (z : G)) {z₀ : X}
    (hc : IsConj (e z) z₀) : ∃ (g' : G) (z' : L), e z' = z₀ ∧ g'⁻¹ * t * g' = t * (z' : G) := by
  obtain ⟨c', hc'⟩ := isConj_iff.mp hc
  refine ⟨g * (e.symm c'⁻¹ : G), (e.symm c'⁻¹)⁻¹ * z * e.symm c'⁻¹, ?_,
    conj_mul_eq_mul_conj htC hz _⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, inv_inv, ← hc']

theorem exists_conj_eq_mul_longRoot_mem_minusPairPerp (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (k : Fin (n - 1)) :
    ∃ (g : G) (z : L), e z ∈ minusPairPerp (by omega) b c k ∧ IsLongRoot _ (e z) ∧
      g⁻¹ * t * g = t * (z : G) := by
  obtain ⟨g, z, hz, hgz⟩ := exists_conj_eq_mul_longRoot_minus hset hn hK hq hirr e ht hKt
  obtain ⟨z₀, hz₀D, hz₀⟩ := exists_isLongRoot_mem_minusPairPerp (K := K) hn hirr k
  obtain ⟨g', z', hz', hg'⟩ := exists_conj_eq_mul_of_isConj e (mem_centralizer_of_inf_eq hKt)
    hgz (isConj_of_isLongRoot_minus hn hirr hz hz₀)
  exact ⟨g', z', hz' ▸ hz₀D, hz' ▸ hz₀, hg'⟩

theorem exists_conj_eq_mul_longRoot_mem_pairPerp_or_residual (hset : SeitzSetting G L)
    {n f : ℕ} (hn : 5 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (k : Fin n) :
    (∃ (g : G) (z : L), e z ∈ pairPerp k ∧ IsLongRoot _ (e z) ∧ g⁻¹ * t * g = t * (z : G)) ∨
      (Even f ∧ ∃ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) ∧
        ∃ y ∈ (S : Subgroup G), ∃ w ∈ (S : Subgroup G), y * w * y⁻¹ * w⁻¹ ∉ L) := by
  rcases exists_conj_eq_mul_longRoot_plus_or_residual hset hn hK hq e ht hKt with
    ⟨g, z, hz, hgz⟩ | hres
  · left
    obtain ⟨z₀, hz₀D, hz₀⟩ := exists_isLongRoot_mem_pairPerp (K := K) (by omega : 3 ≤ n) k
    obtain ⟨g', z', hz', hg'⟩ := exists_conj_eq_mul_of_isConj e (mem_centralizer_of_inf_eq hKt)
      hgz (isConj_of_isLongRoot_plus (by omega) hz hz₀)
    exact ⟨g', z', hz' ▸ hz₀D, hz' ▸ hz₀, hg'⟩
  · exact Or.inr hres

end CFSG.SeitzReduction.OmegaPilot
