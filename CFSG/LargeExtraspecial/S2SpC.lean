module

public import CFSG.LargeExtraspecial.S2SpOne
public import CFSG.LargeExtraspecial.S2OrthC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions OrthoF2
open LinearMap (BilinForm)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}

theorem spSiegel_mul_spSiegel_pow_three (hf : f.IsAlt) {p p₁ c : V} (hpp₁ : f p p₁ = 1)
    (hpc : f p c = 0) (hp₁c : f p₁ c = 0) :
    (spSiegel f hf p c 1 * spSiegel f hf p₁ c 1) p = p₁ ∧
      (spSiegel f hf p c 1 * spSiegel f hf p₁ c 1) ^ 3 = 1 := by
  have hp₁p : f p₁ p = 1 := by rw [isAlt_symm hf, hpp₁]
  have hcp : f c p = 0 := by rw [isAlt_symm hf, hpc]
  have hcp₁ : f c p₁ = 0 := by rw [isAlt_symm hf, hp₁c]
  have hpp : f p p = 0 := hf.self_eq_zero p
  have hp₁p₁ : f p₁ p₁ = 0 := hf.self_eq_zero p₁
  have hcc : f c c = 0 := hf.self_eq_zero c
  set r := spSiegel f hf p c 1 * spSiegel f hf p₁ c 1 with hr
  have hrv : ∀ v, r v = v + (f v p + f v p₁) • p + (f v p₁ + f v c) • p₁ +
      (f v p + f v c) • c := by
    intro v
    rw [hr, LinearEquiv.mul_apply, spSiegel_apply hf hp₁c, spSiegel_apply hf hpc]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hcp,
      hp₁p, hcc, hp₁c, one_mul, mul_zero, mul_one, add_zero]
    refine eq_of_one_smul_eq ?_
    match_scalars <;> ring_nf <;> reduce_mod_char
  refine ⟨?_, ?_⟩
  · rw [hrv, hpp, hpp₁, hpc]
    refine eq_of_one_smul_eq ?_
    match_scalars <;> decide
  · ext v
    have h3 : (r ^ 3) v = r (r (r v)) := by
      simp only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply]
    rw [h3, hrv (r (r v)), hrv (r v), hrv v]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hpp,
      hp₁p, hcp, hpp₁, hp₁p₁, hcp₁, hpc, hp₁c, hcc, mul_zero, mul_one, add_zero,
      LinearEquiv.coe_one, id]
    refine eq_of_one_smul_eq ?_
    match_scalars <;> ring_nf <;> reduce_mod_char

variable [FiniteDimensional (ZMod 2) V]

theorem sp_exists_partner_left (hf : f.IsAlt) (hnd : f.Nondegenerate) {F : Submodule (ZMod 2) V}
    {p p₁ : V} (hpF : p ∈ spPerp f F) (hp₁F : p₁ ∈ spPerp f F) (hpp₁ : f p p₁ = 1)
    {z : V ≃ₗ[ZMod 2] V} (hz : z ∈ spRadFix f F p₁) (hz1 : z ≠ 1) (hza : ¬ IsSpTypeA f z 2) :
    ∃ y ∈ spRadFix f F p, y ≠ 1 ∧ ¬ IsSpTypeA f y 2 ∧ (y * z) p = p₁ ∧ (y * z) ^ 3 = 1 := by
  obtain ⟨hp0, hp₁0, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  obtain ⟨u, huF, hp₁u, rfl⟩ := exists_eq_spSiegel_one_of_not_isSpTypeA hf hnd hp₁F hp₁0 hz hz1 hza
  set c := u + f u p • p₁ with hcdef
  have hcF : c ∈ spPerp f F := Submodule.add_mem _ huF (Submodule.smul_mem _ _ hp₁F)
  have hpc : f p c = 0 := by
    rw [hcdef, map_add, map_smul, hpp₁, smul_eq_mul, mul_one, isAlt_symm hf, zmod2_add_self]
  have hp₁c : f p₁ c = 0 := by
    rw [hcdef, map_add, map_smul, hf.self_eq_zero, smul_zero, add_zero, hp₁u]
  have hzc : spSiegel f hf p₁ u 1 = spSiegel f hf p₁ c 1 := by
    rw [hcdef, spSiegel_add_smul hf hp₁u]
  refine ⟨spSiegel f hf p c 1, (mem_spRadFix_iff hf hnd hp0 hpF).mpr ⟨c, hcF, hpc, 1, rfl⟩,
    fun h => one_ne_zero ((spSiegel_eq_one_iff hf hnd hp0 hpc 1).mp h).2,
    not_isSpTypeA_spSiegel_one hf hnd hp0 hpc, ?_⟩
  rw [hzc]
  exact spSiegel_mul_spSiegel_pow_three hf hpp₁ hpc hp₁c

theorem sp_exists_partner_right (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} {p p₁ : V} (hpF : p ∈ spPerp f F) (hp₁F : p₁ ∈ spPerp f F)
    (hpp₁ : f p p₁ = 1) {y : V ≃ₗ[ZMod 2] V} (hy : y ∈ spRadFix f F p) (hy1 : y ≠ 1)
    (hya : ¬ IsSpTypeA f y 2) :
    ∃ z ∈ spRadFix f F p₁, z ≠ 1 ∧ ¬ IsSpTypeA f z 2 ∧ (y * z) p = p₁ ∧ (y * z) ^ 3 = 1 := by
  obtain ⟨hp0, hp₁0, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  obtain ⟨u, huF, hpu, rfl⟩ := exists_eq_spSiegel_one_of_not_isSpTypeA hf hnd hpF hp0 hy hy1 hya
  set c := u + f u p₁ • p with hcdef
  have hcF : c ∈ spPerp f F := Submodule.add_mem _ huF (Submodule.smul_mem _ _ hpF)
  have hpc : f p c = 0 := by
    rw [hcdef, map_add, map_smul, hf.self_eq_zero, smul_zero, add_zero, hpu]
  have hp₁c : f p₁ c = 0 := by
    have hp₁p : f p₁ p = 1 := by rw [isAlt_symm hf, hpp₁]
    rw [hcdef, map_add, map_smul, hp₁p, smul_eq_mul, mul_one, isAlt_symm hf, zmod2_add_self]
  have hyc : spSiegel f hf p u 1 = spSiegel f hf p c 1 := by
    rw [hcdef, spSiegel_add_smul hf hpu]
  refine ⟨spSiegel f hf p₁ c 1, (mem_spRadFix_iff hf hnd hp₁0 hp₁F).mpr ⟨c, hcF, hp₁c, 1, rfl⟩,
    fun h => one_ne_zero ((spSiegel_eq_one_iff hf hnd hp₁0 hp₁c 1).mp h).2,
    not_isSpTypeA_spSiegel_one hf hnd hp₁0 hp₁c, ?_⟩
  rw [hyc]
  exact spSiegel_mul_spSiegel_pow_three hf hpp₁ hpc hp₁c

omit [FiniteDimensional (ZMod 2) V] in
theorem spRadFix_le_closure_not_isSpTypeA (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} {p : V} (hpF : p ∈ spPerp f F) (hp0 : p ≠ 0) :
    spRadFix f F p ≤ Subgroup.closure {t | t ∈ spRadFix f F p ∧ t ≠ 1 ∧ ¬ IsSpTypeA f t 2} := by
  intro t ht
  obtain ⟨u, huF, hpu, c, rfl⟩ := (mem_spRadFix_iff hf hnd hp0 hpF).mp ht
  have hmem : ∀ w : V, w ∈ spPerp f F → f p w = 0 →
      spSiegel f hf p w 1 ∈ {t | t ∈ spRadFix f F p ∧ t ≠ 1 ∧ ¬ IsSpTypeA f t 2} :=
    fun w hwF hpw => ⟨(mem_spRadFix_iff hf hnd hp0 hpF).mpr ⟨w, hwF, hpw, 1, rfl⟩,
      fun h => one_ne_zero ((spSiegel_eq_one_iff hf hnd hp0 hpw 1).mp h).2,
      not_isSpTypeA_spSiegel_one hf hnd hp0 hpw⟩
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
  · rw [← spSiegel_one_mul_zero_one hf hpu]
    exact mul_mem (Subgroup.subset_closure (hmem u huF hpu))
      (Subgroup.subset_closure (hmem 0 (Submodule.zero_mem _) (map_zero _)))
  · exact Subgroup.subset_closure (hmem u huF hpu)

theorem sp_timmesfeld_2_1_c0 (hf : f.IsAlt) (hnd : f.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ spPerp f F = ⊥) (h4 : 4 ≤ finrank (ZMod 2) (spPerp f F)) {p p₁ : V}
    (hpF : p ∈ spPerp f F) (hp₁F : p₁ ∈ spPerp f F) (hpp₁ : f p p₁ = 1) :
    ∃ y ∈ spRadFix f F p, ∃ z ∈ spRadFix f F p₁, IsSpTypeC f y 2 ∧ IsSpTypeC f z 2 ∧
      orderOf (y * z) = 3 ∧ (y * z) p = p₁ := by
  obtain ⟨hp0, hp₁0, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  have hKdim : finrank (ZMod 2) (spPerp f K) + 2 = finrank (ZMod 2) (spPerp f F) :=
    finrank_spPerp_sup_span_pair hf hnd hF hpF hp₁F hpp₁
  have hne : spPerp f K ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hKdim
    omega
  obtain ⟨c, hcK, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hcF, hpc, hp₁c⟩ := mem_spPerp_sup_span_pair.mp hcK
  have hli : ∀ {a : V}, a ≠ 0 → f a p₁ = 1 ∨ f a p = 1 → f a c = 0 →
      LinearIndependent (ZMod 2) ![a, c] := by
    intro a ha0 ha hac
    refine linearIndependent_pair_iff.mpr ⟨ha0, hc0, ?_⟩
    rintro rfl
    rcases ha with h | h
    · rw [isAlt_symm hf, hp₁c] at h
      exact zero_ne_one h
    · rw [isAlt_symm hf, hpc] at h
      exact zero_ne_one h
  have hpow := spSiegel_mul_spSiegel_pow_three hf hpp₁ hpc hp₁c
  refine ⟨spSiegel f hf p c 1, (mem_spRadFix_iff hf hnd hp0 hpF).mpr ⟨c, hcF, hpc, 1, rfl⟩,
    spSiegel f hf p₁ c 1, (mem_spRadFix_iff hf hnd hp₁0 hp₁F).mpr ⟨c, hcF, hp₁c, 1, rfl⟩,
    isSpTypeC_spSiegel_one hf hnd hpc (hli hp0 (Or.inl hpp₁) hpc),
    isSpTypeC_spSiegel_one hf hnd hp₁c
      (hli hp₁0 (Or.inr (by rw [isAlt_symm hf, hpp₁])) hp₁c), ?_, hpow.1⟩
  refine orderOf_eq_prime hpow.2 fun h => ?_
  have := hpow.1
  rw [h, LinearEquiv.coe_one, id] at this
  rw [this, hf.self_eq_zero] at hpp₁
  exact zero_ne_one hpp₁

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
variable (ρ : TauCeti.BilinForm.isometryGroup f →* (M ≃ₗ[ZMod 2] M))

abbrev SpG (f : BilinForm (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  TauCeti.BilinForm.isometryGroup f

omit [FiniteDimensional (ZMod 2) V] in
theorem sp_mul_self_of_mem_spRadFix (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} {a : V} (ha0 : a ≠ 0) (haF : a ∈ spPerp f F)
    {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ spRadFix f F a) : t * t = 1 := by
  obtain ⟨u, -, hau, c, rfl⟩ := (mem_spRadFix_iff hf hnd ha0 haF).mp ht
  exact spSiegel_mul_self hf hau c

theorem sp_timmesfeld_2_1_c (hf : f.IsAlt) (hnd : f.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ spPerp f F = ⊥) {m : ℕ} (hdim : finrank (ZMod 2) (spPerp f F) = 2 * m)
    {N : Submodule (ZMod 2) M} (hN : SpInvariant ρ F N) {p p₁ : V} (hpF : p ∈ spPerp f F)
    (hp₁F : p₁ ∈ spPerp f F) (hpp₁ : f p p₁ = 1) (hD : SpRadDecomp ρ F N p p₁)
    {U : Submodule (ZMod 2) M}
    (hUW : U ≤ N ⊓ fixOf ρ (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V)))
    (hU : ∀ g : TauCeti.BilinForm.isometryGroup f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      (g : V ≃ₗ[ZMod 2] V) p = p → ∀ u ∈ U, ρ g u ∈ U)
    (g : TauCeti.BilinForm.isometryGroup f) (hgF : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F)
    (hgp : (g : V ≃ₗ[ZMod 2] V) p = p₁) :
    ∀ h : TauCeti.BilinForm.isometryGroup f, (h : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      ∀ v ∈ U ⊔ U.map (ρ g : M →ₗ[ZMod 2] M), ρ h v ∈ U ⊔ U.map (ρ g : M →ₗ[ZMod 2] M) := by
  obtain ⟨hp0, hp₁0, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  have hp₁p : f p₁ p = 1 := by rw [isAlt_symm hf, hpp₁]
  set U' := U.map (ρ g : M →ₗ[ZMod 2] M) with hU'def
  set L := (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V)) with hLdef
  set L₁ := (spRadFix f F p₁ : Set (V ≃ₗ[ZMod 2] V)) with hL₁def
  have hLΩ : ∀ t ∈ spRadFix f F p, t ∈ SpG f :=
    fun t ht => (spRadFix_le_spFix F p ht).1
  have hL₁Ω : ∀ t ∈ spRadFix f F p₁, t ∈ SpG f :=
    fun t ht => (spRadFix_le_spFix F p₁ ht).1
  have hU'W : U' ≤ N ⊓ fixOf ρ L₁ := by
    have h := map_inf_fixOf_spRadFix ρ hf hnd hN g hgF hpF hp0
    rw [hgp] at h
    rw [hL₁def, ← h]
    exact Submodule.map_mono hUW
  have hmov : ∀ k : SpG f, (k : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      (k : V ≃ₗ[ZMod 2] V) p = p₁ → ∀ u ∈ U, ρ k u ∈ U' := by
    intro k hkF hkp u hu
    refine ⟨ρ (g⁻¹ * k) u, hU _ (mul_mem (inv_mem hgF) hkF) ?_ u hu, ?_⟩
    · change (g : V ≃ₗ[ZMod 2] V)⁻¹ ((k : V ≃ₗ[ZMod 2] V) p) = p
      rw [hkp, ← hgp]
      exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' _ p
    · change ρ g (ρ (g⁻¹ * k) u) = ρ k u
      rw [map_mul, LinearEquiv.mul_apply, map_inv,
        CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply']
  have hmov' : ∀ k : SpG f, (k : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      (k : V ≃ₗ[ZMod 2] V) p₁ = p → ∀ u' ∈ U', ρ k u' ∈ U := by
    rintro k hkF hkp _ ⟨u, hu, rfl⟩
    have : ρ k (ρ g u) = ρ (k * g) u := by rw [map_mul, LinearEquiv.mul_apply]
    change ρ k (ρ g u) ∈ U
    rw [this]
    refine hU _ (mul_mem hkF hgF) ?_ u hu
    change (k : V ≃ₗ[ZMod 2] V) ((g : V ≃ₗ[ZMod 2] V) p) = p
    rw [hgp, hkp]
  have hb0₁ : ∀ z : SpG f, (z : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p₁ →
      (z : V ≃ₗ[ZMod 2] V) ≠ 1 → ¬ IsSpTypeA f z 2 → N ⊓ fixSpace (ρ z) = N ⊓ fixOf ρ L₁ :=
    fun z hz hz1 hza => (sp_timmesfeld_2_1_b0 ρ hf hnd hF hdim hN hpF hp₁F hpp₁ hD z hz hz1 hza).1
  have hb0 : ∀ y : SpG f, (y : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p →
      (y : V ≃ₗ[ZMod 2] V) ≠ 1 → ¬ IsSpTypeA f y 2 → N ⊓ fixSpace (ρ y) = N ⊓ fixOf ρ L :=
    fun y hy hy1 hya =>
      (sp_timmesfeld_2_1_b0 ρ hf hnd hF hdim hN hp₁F hpF hp₁p hD.symm y hy hy1 hya).1
  have hsq : ∀ (a : V) (t : SpG f), a ≠ 0 → a ∈ spPerp f F →
      (t : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F a → ρ t * ρ t = 1 := by
    intro a t ha0 haF ht
    rw [← map_mul,
      show t * t = 1 from Subtype.ext (sp_mul_self_of_mem_spRadFix hf hnd ha0 haF ht), map_one]
  have hcap : ∀ y z : SpG f, (y : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p →
      (y : V ≃ₗ[ZMod 2] V) ≠ 1 → ¬ IsSpTypeA f y 2 → (z : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p₁ →
      (z : V ≃ₗ[ZMod 2] V) ≠ 1 → ¬ IsSpTypeA f z 2 →
      N ⊓ fixSpace (ρ y) ⊓ fixSpace (ρ z) = ⊥ := by
    intro y z hy hy1 hya hz hz1 hza
    rw [eq_bot_iff, ← hD.2]
    rintro v ⟨⟨hvN, hvy⟩, hvz⟩
    have h1 : v ∈ N ⊓ fixSpace (ρ y) := ⟨hvN, hvy⟩
    have h2 : v ∈ N ⊓ fixSpace (ρ z) := ⟨hvN, hvz⟩
    rw [hb0 y hy hy1 hya] at h1
    rw [hb0₁ z hz hz1 hza] at h2
    exact ⟨h1, h2⟩
  have key1 : ∀ z : SpG f, (z : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p₁ →
      (z : V ≃ₗ[ZMod 2] V) ≠ 1 → ¬ IsSpTypeA f z 2 → ∀ u ∈ U, ρ z u - u ∈ U' := by
    intro z hz hz1 hza u hu
    obtain ⟨y, hyL, hy1, hya, hyzp, hyz3⟩ :=
      sp_exists_partner_left hf hnd hpF hp₁F hpp₁ hz hz1 hza
    set Y : SpG f := ⟨y, hLΩ y hyL⟩ with hYdef
    have h3 : (ρ Y * ρ z) ^ 3 = 1 := by
      rw [← map_mul, ← map_pow,
        show (Y * z) ^ 3 = 1 from Subtype.ext (by
          rw [SubgroupClass.coe_pow, Subgroup.coe_mul]
          exact hyz3), map_one]
    have hu' := hUW hu
    have e := sub_eq_of_pow_three (hsq p Y hp0 hpF hyL) (hsq p₁ z hp₁0 hp₁F hz) h3
      (hN Y hyL.2) (hN z hz.2) (hcap Y z hyL hy1 hya hz hz1 hza) hu'.1 (hu'.2 Y hyL)
    rw [e, ← LinearEquiv.mul_apply, ← map_mul]
    exact hmov _ (mul_mem hyL.2 hz.2) hyzp u hu
  have key2 : ∀ y : SpG f, (y : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p →
      (y : V ≃ₗ[ZMod 2] V) ≠ 1 → ¬ IsSpTypeA f y 2 → ∀ u' ∈ U', ρ y u' - u' ∈ U := by
    intro y hy hy1 hya u' hu'
    obtain ⟨z, hzL, hz1, hza, hyzp, hyz3⟩ :=
      sp_exists_partner_right hf hnd hpF hp₁F hpp₁ hy hy1 hya
    set Z : SpG f := ⟨z, hL₁Ω z hzL⟩ with hZdef
    have hzy : ((Z * y : SpG f) : V ≃ₗ[ZMod 2] V) p₁ = p := by
      change z ((y : V ≃ₗ[ZMod 2] V) p₁) = p
      rw [← hyzp, LinearEquiv.mul_apply]
      have h1 := LinearEquiv.congr_fun (sp_mul_self_of_mem_spRadFix hf hnd hp0 hpF hy) (z p)
      have h2 := LinearEquiv.congr_fun (sp_mul_self_of_mem_spRadFix hf hnd hp₁0 hp₁F hzL) p
      rw [LinearEquiv.mul_apply, LinearEquiv.coe_one, id] at h1 h2
      rw [h1, h2]
    have h3 : (ρ Z * ρ y) ^ 3 = 1 := by
      have hyz : (ρ y * ρ Z) ^ 3 = 1 := by
        rw [← map_mul, ← map_pow,
          show (y * Z) ^ 3 = 1 from Subtype.ext (by
            rw [SubgroupClass.coe_pow, Subgroup.coe_mul]
            exact hyz3), map_one]
      have hYi : (ρ y)⁻¹ = ρ y := inv_eq_of_mul_eq_one_right (hsq p y hp0 hpF hy)
      have hZi : (ρ Z)⁻¹ = ρ Z := inv_eq_of_mul_eq_one_right (hsq p₁ Z hp₁0 hp₁F hzL)
      have : ρ Z * ρ y = (ρ y * ρ Z)⁻¹ := by rw [mul_inv_rev, hYi, hZi]
      rw [this, inv_pow, hyz, inv_one]
    have hu'' := hU'W hu'
    have e := sub_eq_of_pow_three (hsq p₁ Z hp₁0 hp₁F hzL) (hsq p y hp0 hpF hy) h3
      (hN Z hzL.2) (hN y hy.2) (by rw [inf_right_comm]; exact hcap y Z hy hy1 hya hzL hz1 hza)
      hu''.1 (hu''.2 Z hzL)
    rw [e, ← LinearEquiv.mul_apply, ← map_mul]
    exact hmov' _ (mul_mem hzL.2 hy.2) hzy u' hu'
  have hfixU' : ∀ v ∈ U', ∀ t : SpG f, (t : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p₁ →
      ρ t v = v := fun v hv t ht => (hU'W hv).2 t ht
  have hfixU : ∀ v ∈ U, ∀ t : SpG f, (t : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p →
      ρ t v = v := fun v hv t ht => (hUW hv).2 t ht
  have gen : ∀ {a : V} {W W' : Submodule (ZMod 2) M}, a ∈ spPerp f F → a ≠ 0 →
      (∀ v ∈ W', ∀ t : SpG f, (t : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F a → ρ t v = v) →
      (∀ z : SpG f, (z : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F a →
        (z : V ≃ₗ[ZMod 2] V) ≠ 1 → ¬ IsSpTypeA f z 2 → ∀ u ∈ W, ρ z u - u ∈ W') →
      ∀ t : SpG f, (t : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F a → ∀ u ∈ W, ρ t u - u ∈ W' := by
    intro a W W' haF ha0 hfix hkey t ht
    have hcl := spRadFix_le_closure_not_isSpTypeA hf hnd haF ha0 ht
    have hcle : Subgroup.closure {t | t ∈ spRadFix f F a ∧ t ≠ 1 ∧ ¬ IsSpTypeA f t 2} ≤
        spRadFix f F a := (Subgroup.closure_le _).mpr fun x hx => hx.1
    have hΩ : ∀ x ∈ spRadFix f F a, x ∈ SpG f :=
      fun x hx => (spRadFix_le_spFix F a hx).1
    suffices h : ∀ x ∈ Subgroup.closure {t | t ∈ spRadFix f F a ∧ t ≠ 1 ∧ ¬ IsSpTypeA f t 2},
        ∀ hx : x ∈ SpG f, ∀ u ∈ W, ρ ⟨x, hx⟩ u - u ∈ W' from h t hcl t.2
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact fun hxΩ u hu => hkey ⟨x, hxΩ⟩ hx.1 hx.2.1 hx.2.2 u hu
    | one =>
      intro h1 u hu
      rw [show (⟨1, h1⟩ : SpG f) = 1 from rfl, map_one, LinearEquiv.coe_one, id,
        sub_self]
      exact W'.zero_mem
    | mul x y hx hy ihx ihy =>
      intro hxy u hu
      have hxΩ := hΩ x (hcle hx)
      have hyΩ := hΩ y (hcle hy)
      have e : (⟨x * y, hxy⟩ : SpG f) = ⟨x, hxΩ⟩ * ⟨y, hyΩ⟩ := rfl
      have h1 := ihy hyΩ u hu
      have h2 := hfix _ h1 ⟨x, hxΩ⟩ (hcle hx)
      rw [e, map_mul, LinearEquiv.mul_apply,
        show ρ ⟨x, hxΩ⟩ (ρ ⟨y, hyΩ⟩ u) - u = ρ ⟨x, hxΩ⟩ (ρ ⟨y, hyΩ⟩ u - u) + (ρ ⟨x, hxΩ⟩ u - u)
          by rw [map_sub]; abel, h2]
      exact W'.add_mem h1 (ihx hxΩ u hu)
    | inv x hx ihx =>
      intro hxi u hu
      have hxΩ := hΩ x (hcle hx)
      have e : (⟨x⁻¹, hxi⟩ : SpG f) = (⟨x, hxΩ⟩ : SpG f)⁻¹ := rfl
      have h1 := ihx hxΩ u hu
      have h2 := hfix _ h1 ⟨x, hxΩ⟩ (hcle hx)
      have h3 : (ρ ⟨x, hxΩ⟩)⁻¹ (ρ ⟨x, hxΩ⟩ u - u) = ρ ⟨x, hxΩ⟩ u - u := by
        conv_lhs => rw [← h2]
        exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' _ _
      rw [e, map_inv]
      have h4 : (ρ ⟨x, hxΩ⟩)⁻¹ u - u = -((ρ ⟨x, hxΩ⟩)⁻¹ (ρ ⟨x, hxΩ⟩ u - u)) := by
        rw [map_sub, CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply']
        abel
      rw [h4, h3]
      exact W'.neg_mem h1
  have key3 := gen hp₁F hp₁0 hfixU' key1
  have key4 := gen hpF hp0 hfixU key2
  have inv₁ : ∀ t : SpG f, (t : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p₁ →
      ∀ v ∈ U ⊔ U', ρ t v ∈ U ⊔ U' := by
    intro t ht v hv
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hfixU' u' hu' t ht,
      show ρ t u = u + (ρ t u - u) by abel]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left hu)
      (Submodule.mem_sup_right (key3 t ht u hu))) (Submodule.mem_sup_right hu')
  have inv₀ : ∀ t : SpG f, (t : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p →
      ∀ v ∈ U ⊔ U', ρ t v ∈ U ⊔ U' := by
    intro t ht v hv
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hfixU u hu t ht, show ρ t u' = u' + (ρ t u' - u') by abel]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hu) (Submodule.add_mem _
      (Submodule.mem_sup_right hu') (Submodule.mem_sup_left (key4 t ht u' hu')))
  intro h hhF
  have hgenX := spFix_eq_closure_spRadFix hf hnd hF hdim hpF hp₁F hpp₁
  have hh : (h : V ≃ₗ[ZMod 2] V) ∈ Subgroup.closure (L ∪ L₁) := by
    rw [← hgenX]
    exact ⟨h.2, hhF⟩
  have hclΩ : Subgroup.closure (L ∪ L₁) ≤ SpG f := by
    rw [← hgenX]
    exact inf_le_left
  suffices hs : ∀ x ∈ Subgroup.closure (L ∪ L₁), ∀ hx : x ∈ SpG f,
      ∀ v ∈ U ⊔ U', ρ ⟨x, hx⟩ v ∈ U ⊔ U' from hs h hh h.2
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    intro hxΩ v hv
    rcases hx with hx | hx
    · exact inv₀ ⟨x, hxΩ⟩ hx v hv
    · exact inv₁ ⟨x, hxΩ⟩ hx v hv
  | one =>
    intro h1 v hv
    rw [show (⟨1, h1⟩ : SpG f) = 1 from rfl, map_one, LinearEquiv.coe_one, id]
    exact hv
  | mul x y hx hy ihx ihy =>
    intro hxy v hv
    have e : (⟨x * y, hxy⟩ : SpG f) = ⟨x, hclΩ hx⟩ * ⟨y, hclΩ hy⟩ := rfl
    rw [e, map_mul, LinearEquiv.mul_apply]
    exact ihx _ _ (ihy _ v hv)
  | inv x hx ihx =>
    intro hxi v hv
    have hxΩ := hclΩ hx
    have hmap : (U ⊔ U').map (ρ ⟨x, hxΩ⟩ : M →ₗ[ZMod 2] M) = U ⊔ U' :=
      Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨w, hw, rfl⟩; exact ihx hxΩ w hw)
        (LinearEquiv.finrank_map_eq _ _)
    rw [← hmap] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have e : (⟨x⁻¹, hxi⟩ : SpG f) = (⟨x, hxΩ⟩ : SpG f)⁻¹ := rfl
    rw [e, map_inv]
    change (ρ ⟨x, hxΩ⟩)⁻¹ (ρ ⟨x, hxΩ⟩ w) ∈ U ⊔ U'
    rw [CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply']
    exact hw

end S2

end CFSG.LargeExtraspecial
