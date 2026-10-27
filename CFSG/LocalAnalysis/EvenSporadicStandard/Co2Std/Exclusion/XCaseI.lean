module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XCaseIDiag
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup
open CFSG.LocalCores

variable {V : Type*} [Group V] {X : Type*} [Group X] {ρ : X →* MulAut V} {Q : Subgroup X}
  {V₁ V₂ : Subgroup V} {z : X} {Q₁ : Subgroup (MulAut ↥V₁)} {t₁ : ↥V₁}

private lemma map_map_conj (K : Subgroup X) (x y : X) :
    (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      K.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext k
  simp [mul_assoc]

private lemma map_conj_apply_apply {x k : X} {v : V} :
    ρ (x * k * x⁻¹) (ρ x v) = ρ x (ρ k v) := by
  simp [map_mul, MulAut.mul_apply, MulAut.inv_apply_self]

private lemma apply_mem_map_conj {L M : Subgroup X} {x : X} {v : V}
    (hLM : L.map (MulAut.conj x).toMonoidHom = M) (hv : ∀ k ∈ L, ρ k v = v) :
    ∀ k ∈ M, ρ k (ρ x v) = ρ x v := by
  intro k hk
  have hk' : k ∈ L.map (MulAut.conj x).toMonoidHom := hLM.symm ▸ hk
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hk'
  change ρ (x * l * x⁻¹) (ρ x v) = ρ x v
  rw [map_conj_apply_apply, hv l hl]

private lemma fixed_eq_pair [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {K : Subgroup X}
    (hK : IsComponent K) (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) :
    ((∀ v : V, (∀ k ∈ K, ρ k v = v) ↔ v ∈ V₁) ∧
        (∀ v : V, (∀ k ∈ K.map (MulAut.conj z).toMonoidHom, ρ k v = v) ↔ v ∈ V₂)) ∨
      ((∀ v : V, (∀ k ∈ K, ρ k v = v) ↔ v ∈ V₂) ∧
        (∀ v : V, (∀ k ∈ K.map (MulAut.conj z).toMonoidHom, ρ k v = v) ↔ v ∈ V₁)) := by
  have hρz : ρ z * ρ z = 1 := by
    simpa using congrArg ρ h.mul_self
  have hρzinv : ρ (z⁻¹) = ρ z := by
    have h' : (ρ z)⁻¹ = ρ z := inv_eq_of_mul_eq_one_right hρz
    simpa using h'
  have hρz_apply : ∀ w : V, ρ z (ρ z w) = w := by
    intro w
    have h1 : (ρ z * ρ z) w = w := by
      rw [hρz, MulAut.one_apply]
    simpa [MulAut.mul_apply] using h1
  have hswap' : ∀ v : V, ρ z v ∈ V₁ ↔ v ∈ V₂ := by
    intro v
    have := h.swap (ρ z v)
    rwa [hρz_apply v] at this
  have hB : ∀ v : V,
      ((∀ k ∈ K.map (MulAut.conj z).toMonoidHom, ρ k v = v) ↔
        (∀ k ∈ K, ρ k (ρ z v) = ρ z v)) := by
    intro v
    constructor
    · intro hv k hk
      have hk' : z * k * z⁻¹ ∈ K.map (MulAut.conj z).toMonoidHom := by
        have := Subgroup.mem_map_of_mem (MulAut.conj z).toMonoidHom hk
        simpa [MulAut.conj_apply] using this
      have hk_eq : ρ (z * k * z⁻¹) v = ρ z (ρ k (ρ z v)) := by
        simp [map_mul, MulAut.mul_apply, hρzinv]
      have h := hv (z * k * z⁻¹) hk'
      rw [hk_eq] at h
      calc ρ k (ρ z v) = ρ z (ρ z (ρ k (ρ z v))) := (hρz_apply _).symm
        _ = ρ z v := by rw [h]
    · intro hv k' hk'
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hk'
      change ρ (z * k * z⁻¹) v = v
      have hk_eq : ρ (z * k * z⁻¹) v = ρ z (ρ k (ρ z v)) := by
        simp [map_mul, MulAut.mul_apply, hρzinv]
      rw [hk_eq, hv k hk, hρz_apply]
  obtain hA | hA := h.fixed_eq hK hKz
  · refine Or.inl ⟨hA, fun v => ?_⟩
    rw [hB v, hA (ρ z v)]
    exact hswap' v
  · refine Or.inr ⟨hA, fun v => ?_⟩
    rw [hB v, hA (ρ z v)]
    exact (h.swap v).symm

private lemma map_conj_z_map_conj_of_normalizes [Finite X]
    (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {K : Subgroup X} (hK : IsComponent K)
    (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) {x : X}
    (hx : K.map (MulAut.conj x).toMonoidHom = K) :
    (K.map (MulAut.conj z).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      K.map (MulAut.conj z).toMonoidHom := by
  have hK' : IsComponent (K.map (MulAut.conj z).toMonoidHom) :=
    isComponent_map_mulEquiv (MulAut.conj z) hK
  have hL : IsComponent
      ((K.map (MulAut.conj z).toMonoidHom).map (MulAut.conj x).toMonoidHom) :=
    isComponent_map_mulEquiv (MulAut.conj x) hK'
  rcases h.eq_or_eq_of_isComponent hK hKz hL with h' | h'
  · exfalso
    apply hKz
    have hEq :
        (K.map (MulAut.conj z).toMonoidHom).map (MulAut.conj x).toMonoidHom =
          K.map (MulAut.conj x).toMonoidHom := by rw [h', hx]
    exact Subgroup.map_injective (MulAut.conj x).injective hEq
  · exact h'

private lemma map_conj_eq_map_conj_z_of_not_normalizes [Finite X]
    (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {K : Subgroup X} (hK : IsComponent K)
    (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) {x : X}
    (hx : K.map (MulAut.conj x).toMonoidHom ≠ K) :
    K.map (MulAut.conj x).toMonoidHom = K.map (MulAut.conj z).toMonoidHom ∧
      (K.map (MulAut.conj z).toMonoidHom).map (MulAut.conj x).toMonoidHom = K := by
  have hK' : IsComponent (K.map (MulAut.conj z).toMonoidHom) :=
    isComponent_map_mulEquiv (MulAut.conj z) hK
  have hL : IsComponent
      ((K.map (MulAut.conj z).toMonoidHom).map (MulAut.conj x).toMonoidHom) :=
    isComponent_map_mulEquiv (MulAut.conj x) hK'
  have h1 : K.map (MulAut.conj x).toMonoidHom =
      K.map (MulAut.conj z).toMonoidHom := by
    rcases h.eq_or_eq_of_isComponent hK hKz
      (isComponent_map_mulEquiv (MulAut.conj x) hK) with h' | h'
    · exact absurd h' hx
    · exact h'
  refine ⟨h1, ?_⟩
  rcases h.eq_or_eq_of_isComponent hK hKz hL with h' | h'
  · exact h'
  · exfalso
    apply hKz
    have hEq :
        (K.map (MulAut.conj z).toMonoidHom).map (MulAut.conj x).toMonoidHom =
          K.map (MulAut.conj x).toMonoidHom := by rw [h', h1]
    exact Subgroup.map_injective (MulAut.conj x).injective hEq

private lemma action_on_fixed_K' [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    {K : Subgroup X} (hK : IsComponent K)
    (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) {x : X}
    (hx : K.map (MulAut.conj x).toMonoidHom = K) :
    ∀ g ∈ ⁅Q, Q⁆, ∃ g' ∈ ⁅Q, Q⁆, ∀ v : V,
      (∀ k' ∈ K.map (MulAut.conj z).toMonoidHom, ρ k' v = v) →
      ρ x (ρ g v) = ρ g' (ρ x v) := by
  have hx' := map_conj_z_map_conj_of_normalizes h hK hKz hx
  intro g hg
  obtain ⟨k, hk, hgk⟩ := h.exists_mul_conj_eq hK hKz hg
  have hkz : z * k * z⁻¹ ∈ K.map (MulAut.conj z).toMonoidHom := by
    have := Subgroup.mem_map_of_mem (MulAut.conj z).toMonoidHom hk
    simpa [MulAut.conj_apply] using this
  set k₁ : X := x * k * x⁻¹ with hk₁def
  have hk₁ : k₁ ∈ K := by
    have hmem := Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hk
    rw [hx] at hmem
    simpa [hk₁def, MulAut.conj_apply] using hmem
  have hk₁' : z * k₁ * z⁻¹ ∈ K.map (MulAut.conj z).toMonoidHom := by
    have := Subgroup.mem_map_of_mem (MulAut.conj z).toMonoidHom hk₁
    simpa [MulAut.conj_apply] using this
  refine ⟨k₁ * (z * k₁ * z⁻¹), h.mul_conj_mem_commutator hK hKz hk₁, ?_⟩
  intro v hv
  have hBx : ∀ k' ∈ K.map (MulAut.conj z).toMonoidHom, ρ k' (ρ x v) = ρ x v :=
    apply_mem_map_conj hx' hv
  have h1 : ρ g v = ρ k v := by
    rw [← hgk, map_mul]
    simp only [MulAut.mul_apply]
    rw [hv (z * k * z⁻¹) hkz]
  have h2 : ρ x (ρ k v) = ρ k₁ (ρ x v) := by
    simpa [hk₁def] using
      (map_conj_apply_apply (ρ := ρ) (x := x) (k := k) (v := v)).symm
  have h3 : ρ (k₁ * (z * k₁ * z⁻¹)) (ρ x v) = ρ k₁ (ρ x v) := by
    rw [map_mul]
    simp only [MulAut.mul_apply]
    rw [hBx (z * k₁ * z⁻¹) hk₁']
  rw [h1, h2, h3]

private lemma action_on_fixed_K [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    {K : Subgroup X} (hK : IsComponent K)
    (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) {x : X}
    (hx : K.map (MulAut.conj x).toMonoidHom = K)
    (hx' : (K.map (MulAut.conj z).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      K.map (MulAut.conj z).toMonoidHom) :
    ∀ g ∈ ⁅Q, Q⁆, ∃ g' ∈ ⁅Q, Q⁆, ∀ v : V,
      (∀ k ∈ K, ρ k v = v) → ρ x (ρ g v) = ρ g' (ρ x v) := by
  intro g hg
  obtain ⟨k, hk, hgk⟩ := h.exists_mul_conj_eq hK hKz hg
  set k' : X := z * k * z⁻¹ with hk'def
  have hk' : k' ∈ K.map (MulAut.conj z).toMonoidHom := by
    have := Subgroup.mem_map_of_mem (MulAut.conj z).toMonoidHom hk
    simpa [hk'def, MulAut.conj_apply] using this
  have hcomm : k * k' = k' * k := commute_of_map_conj_ne hK hKz hk hk'
  set k₁ : X := x * k' * x⁻¹ with hk₁def
  have hk₁ : k₁ ∈ K.map (MulAut.conj z).toMonoidHom := by
    have hmem := Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hk'
    rw [hx'] at hmem
    simpa [hk₁def, MulAut.conj_apply] using hmem
  obtain ⟨k₂, hk₂, hk₂eq⟩ := Subgroup.mem_map.mp hk₁
  have hk₂' : z * k₂ * z⁻¹ ∈ K.map (MulAut.conj z).toMonoidHom := by
    have := Subgroup.mem_map_of_mem (MulAut.conj z).toMonoidHom hk₂
    simpa [MulAut.conj_apply] using this
  have hcomm₂ : k₂ * (z * k₂ * z⁻¹) = (z * k₂ * z⁻¹) * k₂ :=
    commute_of_map_conj_ne hK hKz hk₂ hk₂'
  refine ⟨k₂ * (z * k₂ * z⁻¹), h.mul_conj_mem_commutator hK hKz hk₂, ?_⟩
  intro v hv
  have hAx : ∀ k ∈ K, ρ k (ρ x v) = ρ x v := apply_mem_map_conj hx hv
  have hk₂eq' : z * k₂ * z⁻¹ = k₁ := hk₂eq
  have h1 : ρ g v = ρ k' v := by
    rw [← hgk, congrArg ρ hcomm, map_mul]
    simp only [MulAut.mul_apply]
    rw [hv k hk]
  have h2 : ρ x (ρ k' v) = ρ k₁ (ρ x v) := by
    simpa [hk₁def] using
      (map_conj_apply_apply (ρ := ρ) (x := x) (k := k') (v := v)).symm
  have h3 : ρ (k₂ * (z * k₂ * z⁻¹)) (ρ x v) = ρ k₁ (ρ x v) := by
    rw [congrArg ρ hcomm₂, map_mul]
    simp only [MulAut.mul_apply]
    rw [hAx k₂ hk₂, hk₂eq']
  rw [h1, h2, h3]

private lemma xGood_of_normalizes [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    {K : Subgroup X} (hK : IsComponent K)
    (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) {x : X}
    (hx : K.map (MulAut.conj x).toMonoidHom = K) : XGood ρ Q V₁ V₂ x := by
  have hx' := map_conj_z_map_conj_of_normalizes h hK hKz hx
  obtain ⟨hA, hB⟩ | ⟨hA, hB⟩ := fixed_eq_pair h hK hKz
  · unfold XGood
    left
    refine ⟨?_, ?_⟩
    · refine h.exists_mem_Q₁ (σ := ρ x) ?_ ?_
      · intro v hv
        exact (hA (ρ x v)).mp (apply_mem_map_conj hx ((hA v).mpr hv))
      · intro g hg
        obtain ⟨g', hg', hgg'⟩ := action_on_fixed_K h hK hKz hx hx' g hg
        exact ⟨g', hg', fun v hv => hgg' v ((hA v).mpr hv)⟩
    · refine h.exists_mem_Q₂ (σ := ρ x) ?_ ?_
      · intro v hv
        exact (hB (ρ x v)).mp (apply_mem_map_conj hx' ((hB v).mpr hv))
      · intro g hg
        obtain ⟨g', hg', hgg'⟩ := action_on_fixed_K' h hK hKz hx g hg
        exact ⟨g', hg', fun v hv => hgg' v ((hB v).mpr hv)⟩
  · unfold XGood
    left
    refine ⟨?_, ?_⟩
    · refine h.exists_mem_Q₁ (σ := ρ x) ?_ ?_
      · intro v hv
        exact (hB (ρ x v)).mp (apply_mem_map_conj hx' ((hB v).mpr hv))
      · intro g hg
        obtain ⟨g', hg', hgg'⟩ := action_on_fixed_K' h hK hKz hx g hg
        exact ⟨g', hg', fun v hv => hgg' v ((hB v).mpr hv)⟩
    · refine h.exists_mem_Q₂ (σ := ρ x) ?_ ?_
      · intro v hv
        exact (hA (ρ x v)).mp (apply_mem_map_conj hx ((hA v).mpr hv))
      · intro g hg
        obtain ⟨g', hg', hgg'⟩ := action_on_fixed_K h hK hKz hx hx' g hg
        exact ⟨g', hg', fun v hv => hgg' v ((hA v).mpr hv)⟩

private lemma xGood_of_swaps [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    {K : Subgroup X} (hK : IsComponent K)
    (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) {x : X}
    (hx : K.map (MulAut.conj x).toMonoidHom = K.map (MulAut.conj z).toMonoidHom)
    (hx' : (K.map (MulAut.conj z).toMonoidHom).map (MulAut.conj x).toMonoidHom = K) :
    XGood ρ Q V₁ V₂ x := by
  obtain ⟨hA, hB⟩ | ⟨hA, hB⟩ := fixed_eq_pair h hK hKz
  · unfold XGood
    right
    refine ⟨?_, ?_⟩
    · intro v hv
      exact (hB (ρ x v)).mp (apply_mem_map_conj hx ((hA v).mpr hv))
    · intro v hv
      exact (hA (ρ x v)).mp (apply_mem_map_conj hx' ((hB v).mpr hv))
  · unfold XGood
    right
    refine ⟨?_, ?_⟩
    · intro v hv
      exact (hA (ρ x v)).mp (apply_mem_map_conj hx' ((hB v).mpr hv))
    · intro v hv
      exact (hB (ρ x v)).mp (apply_mem_map_conj hx ((hA v).mpr hv))

private lemma index_normalizer_eq_two [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    {K : Subgroup X} (hK : IsComponent K)
    (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) :
    (normalizer (K : Set X)).index = 2 := by
  have hz : z ∉ normalizer (K : Set X) := by
    intro hz
    exact hKz (Subgroup.mem_normalizer_iff_map_conj_eq.mp hz)
  rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨z, hz, fun b => ?_⟩
  by_cases hb : b ∈ normalizer (K : Set X)
  · exact Or.inr hb
  · left
    have hbK : K.map (MulAut.conj b).toMonoidHom ≠ K := fun h' =>
      hb (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h')
    obtain ⟨h1, h2⟩ := map_conj_eq_map_conj_z_of_not_normalizes h hK hKz hbK
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change K.map (MulAut.conj (b * z)).toMonoidHom = K
    rw [← map_map_conj K z b]
    exact h2

theorem XHyp.concl_of_map_conj_ne [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {K : Subgroup X}
    (hK : IsComponent K) (hKz : K.map (MulAut.conj z).toMonoidHom ≠ K) :
    XConcl ρ Q V₁ V₂ z := by
  have hz : z ∉ normalizer (K : Set X) := by
    intro hz
    exact hKz (Subgroup.mem_normalizer_iff_map_conj_eq.mp hz)
  have hindex : (normalizer (K : Set X)).index = 2 :=
    index_normalizer_eq_two h hK hKz
  have hnormal : (normalizer (K : Set X)).Normal :=
    Subgroup.normal_of_index_eq_two hindex
  have hall : ∀ x : X, XGood ρ Q V₁ V₂ x := by
    intro x
    by_cases hx : x ∈ normalizer (K : Set X)
    · exact xGood_of_normalizes h hK hKz (Subgroup.mem_normalizer_iff_map_conj_eq.mp hx)
    · have hxK : K.map (MulAut.conj x).toMonoidHom ≠ K := fun h' =>
        hx (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h')
      obtain ⟨h1, h2⟩ := map_conj_eq_map_conj_z_of_not_normalizes h hK hKz hxK
      exact xGood_of_swaps h hK hKz h1 h2
  unfold XConcl
  exact ⟨⟨normalizer (K : Set X), hnormal, hindex, hz⟩,
    h.exists_sylow_of_forall hall⟩

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
