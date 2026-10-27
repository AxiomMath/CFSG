module

public import CFSG.LargeExtraspecial.S2OrthMinus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_mul eichler_zero_right
  eichler_mem_orthogonalGroup)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem eichler_mul_eichler_pow_three {p p₁ c : V} (hp : q p = 0) (hp₁ : q p₁ = 0)
    (hc : q c = 1) (hpp₁ : polar q p p₁ = 1) (hpc : polar q p c = 0) (hp₁c : polar q p₁ c = 0) :
    (eichler q p c * eichler q p₁ c) p = p₁ ∧ (eichler q p c * eichler q p₁ c) ^ 3 = 1 := by
  have hp₁p : polar q p₁ p = 1 := by rw [polar_comm, hpp₁]
  have hcp : polar q c p = 0 := by rw [polar_comm, hpc]
  have hcp₁ : polar q c p₁ = 0 := by rw [polar_comm, hp₁c]
  have hpp : polar q p p = 0 := polar_self_eq_zero q p
  have hp₁p₁ : polar q p₁ p₁ = 0 := polar_self_eq_zero q p₁
  have hcc : polar q c c = 0 := polar_self_eq_zero q c
  set r := eichler q p c * eichler q p₁ c with hr
  have hrv : ∀ v, r v = v + (polar q v p + polar q v p₁) • p + (polar q v p₁ + polar q v c) • p₁ +
      (polar q v p + polar q v c) • c := by
    intro v
    rw [hr, LinearEquiv.mul_apply, eichler_apply_zmod2 hp₁ hp₁c, eichler_apply_zmod2 hp hpc, hc]
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, hcp, hp₁p, hcc, hp₁c, one_mul,
      mul_zero, mul_one, add_zero]
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
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, hpp, hp₁p, hcp, hpp₁, hp₁p₁, hcp₁,
      hpc, hp₁c, hcc, mul_zero, mul_one, add_zero, LinearEquiv.coe_one, id]
    refine eq_of_one_smul_eq ?_
    match_scalars <;> ring_nf <;> reduce_mod_char

variable [FiniteDimensional (ZMod 2) V]

theorem exists_partner_left (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    {p p₁ : V} (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F) (hp0 : p ≠ 0) (hp₁0 : p₁ ≠ 0)
    (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1) {z : V ≃ₗ[ZMod 2] V}
    (hz : z ∈ radFix q F p₁) (hz1 : z ≠ 1) (hza : ¬ IsTypeA q z 2) :
    ∃ y ∈ radFix q F p, y ≠ 1 ∧ ¬ IsTypeA q y 2 ∧ (y * z) p = p₁ ∧ (y * z) ^ 3 = 1 := by
  obtain ⟨u, huF, hp₁u, hu, rfl⟩ := exists_eq_eichler_of_not_isTypeA hq hp₁F hp₁0 hp₁ hz hz1 hza
  set c := u + polar q u p • p₁ with hcdef
  have hcF : c ∈ perp q F := Submodule.add_mem _ huF (Submodule.smul_mem _ _ hp₁F)
  have hpc : polar q p c = 0 := by
    rw [hcdef, polar_add_right, polar_smul_right, hpp₁, smul_eq_mul, mul_one, polar_comm,
      zmod2_add_self]
  have hp₁c : polar q p₁ c = 0 := by
    rw [hcdef, polar_add_right, polar_smul_right, polar_self_eq_zero, smul_zero, add_zero, hp₁u]
  have hc : q c = 1 := by
    have hup₁ : polar q u p₁ = 0 := by rw [polar_comm, hp₁u]
    rw [hcdef, map_add_eq, map_smul_zmod2, hp₁, mul_zero, add_zero, polar_smul_right, hup₁,
      smul_zero, add_zero, hu]
  have hzc : eichler q p₁ u = eichler q p₁ c := by
    rw [hcdef, CFSG.ClassicalGroups.Orthogonal.eichler_add_smul_self hp₁]
  have hc0 : c ≠ 0 := by
    rintro h
    rw [h, map_zero] at hc
    exact zero_ne_one hc
  refine ⟨eichler q p c, (mem_radFix_iff hq hp0 hp hpF).mpr ⟨c, hcF, hpc, rfl⟩, ?_,
    not_isTypeA_eichler hq hp0 hp hpc hc, ?_⟩
  · intro h1
    rcases mem_span_singleton_iff.mp ((eichler_eq_one_iff hq hp0 hp hpc).mp h1) with h | h
    · exact hc0 h
    · rw [h, hp] at hc
      exact zero_ne_one hc
  · rw [hzc]
    exact eichler_mul_eichler_pow_three hp hp₁ hc hpp₁ hpc hp₁c

theorem exists_partner_right (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    {p p₁ : V} (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F) (hp0 : p ≠ 0) (hp₁0 : p₁ ≠ 0)
    (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1) {y : V ≃ₗ[ZMod 2] V}
    (hy : y ∈ radFix q F p) (hy1 : y ≠ 1) (hya : ¬ IsTypeA q y 2) :
    ∃ z ∈ radFix q F p₁, z ≠ 1 ∧ ¬ IsTypeA q z 2 ∧ (y * z) p = p₁ ∧ (y * z) ^ 3 = 1 := by
  obtain ⟨u, huF, hpu, hu, rfl⟩ := exists_eq_eichler_of_not_isTypeA hq hpF hp0 hp hy hy1 hya
  set c := u + polar q u p₁ • p with hcdef
  have hcF : c ∈ perp q F := Submodule.add_mem _ huF (Submodule.smul_mem _ _ hpF)
  have hpc : polar q p c = 0 := by
    rw [hcdef, polar_add_right, polar_smul_right, polar_self_eq_zero, smul_zero, add_zero, hpu]
  have hp₁c : polar q p₁ c = 0 := by
    rw [hcdef, polar_add_right, polar_smul_right, polar_comm q p₁ p, hpp₁, smul_eq_mul, mul_one,
      polar_comm, zmod2_add_self]
  have hc : q c = 1 := by
    have hup : polar q u p = 0 := by rw [polar_comm, hpu]
    rw [hcdef, map_add_eq, map_smul_zmod2, hp, mul_zero, add_zero, polar_smul_right, hup,
      smul_zero, add_zero, hu]
  have hyc : eichler q p u = eichler q p c := by
    rw [hcdef, CFSG.ClassicalGroups.Orthogonal.eichler_add_smul_self hp]
  have hc0 : c ≠ 0 := by
    rintro h
    rw [h, map_zero] at hc
    exact zero_ne_one hc
  refine ⟨eichler q p₁ c, (mem_radFix_iff hq hp₁0 hp₁ hp₁F).mpr ⟨c, hcF, hp₁c, rfl⟩, ?_,
    not_isTypeA_eichler hq hp₁0 hp₁ hp₁c hc, ?_⟩
  · intro h1
    rcases mem_span_singleton_iff.mp ((eichler_eq_one_iff hq hp₁0 hp₁ hp₁c).mp h1) with h | h
    · exact hc0 h
    · rw [h, hp₁] at hc
      exact zero_ne_one hc
  · rw [hyc]
    exact eichler_mul_eichler_pow_three hp hp₁ hc hpp₁ hpc hp₁c

theorem radFix_le_closure_not_isTypeA (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) {m : ℕ} (hm : 2 ≤ m)
    (hdim : finrank (ZMod 2) (perp q F) = 2 * m) (hgen : 3 ≤ m ∨ IsMinusType q F m) {p : V}
    (hpF : p ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0) :
    radFix q F p ≤ Subgroup.closure {t | t ∈ radFix q F p ∧ t ≠ 1 ∧ ¬ IsTypeA q t 2} := by
  intro t ht
  by_cases ht1 : t = 1
  · rw [ht1]
    exact one_mem _
  by_cases hta : ¬ IsTypeA q t 2
  · exact Subgroup.subset_closure ⟨ht, ht1, hta⟩
  push Not at hta
  obtain ⟨u, huF, hpu, rfl⟩ := (mem_radFix_iff hq hp0 hp hpF).mp ht
  have hun : u ∉ (ZMod 2) ∙ p := fun h => ht1 ((eichler_eq_one_iff hq hp0 hp hpu).mpr h)
  have hqu : q u = 0 := by
    rcases zmod2_eq_zero_or_eq_one (q u) with h | h
    · exact h
    · exact absurd hta (not_isTypeA_eichler hq hp0 hp hpu h)
  have hli : LinearIndependent (ZMod 2) ![p, u] := by
    refine linearIndependent_pair_iff.mpr ⟨hp0, fun h => hun (h ▸ Submodule.zero_mem _),
      fun h => hun (h ▸ Submodule.mem_span_singleton_self p)⟩
  have h3 : 3 ≤ m := by
    rcases hgen with h | hmin
    · exact h
    · by_contra h
      have hT := hmin (Submodule.span (ZMod 2) {p, u}) (by
        rw [Submodule.span_le]
        rintro x (rfl | rfl)
        · exact hpF
        · exact huF) (fun x hx => map_eq_zero_of_mem_span_pair hp hqu hpu hx)
      rw [finrank_span_pair hli] at hT
      omega
  set T := perp q (F ⊔ Submodule.span (ZMod 2) {p, u}) with hTdef
  have hTle : T ≤ perp q F := perp_sup_span_pair_le
  have hTdim : 2 * m - 2 ≤ finrank (ZMod 2) T := by
    have h1 := Submodule.finrank_add_le_finrank_add_finrank F (Submodule.span (ZMod 2) {p, u})
    rw [finrank_span_pair hli] at h1
    have h2 := LinearMap.BilinForm.finrank_orthogonal hq (F ⊔ Submodule.span (ZMod 2) {p, u})
    have h3 := LinearMap.BilinForm.finrank_orthogonal hq F
    have h4 := Submodule.finrank_le (F ⊔ Submodule.span (ZMod 2) {p, u})
    have h5 := Submodule.finrank_le F
    rw [hTdef, h2]
    rw [hdim] at h3
    omega
  obtain ⟨u', hu'T, hqu'⟩ := exists_mem_map_eq_one_of_lt hq hF hTle (by omega)
  obtain ⟨hu'F, hpu', huu'⟩ := mem_perp_sup_span_pair.mp hu'T
  have hpuu' : polar q p (u' + u) = 0 := by rw [polar_add_right, hpu', hpu, add_zero]
  have hq' : q (u' + u) = 1 := by rw [map_add_eq, hqu', hqu, polar_comm, huu', add_zero, add_zero]
  have hmem : ∀ w : V, w ∈ perp q F → polar q p w = 0 → q w = 1 →
      eichler q p w ∈ {t | t ∈ radFix q F p ∧ t ≠ 1 ∧ ¬ IsTypeA q t 2} := by
    intro w hwF hpw hw
    refine ⟨(mem_radFix_iff hq hp0 hp hpF).mpr ⟨w, hwF, hpw, rfl⟩, ?_,
      not_isTypeA_eichler hq hp0 hp hpw hw⟩
    intro h1
    rcases mem_span_singleton_iff.mp ((eichler_eq_one_iff hq hp0 hp hpw).mp h1) with h | h
    · rw [h, map_zero] at hw
      exact zero_ne_one hw
    · rw [h, hp] at hw
      exact zero_ne_one hw
  have he : eichler q p u = eichler q p u' * eichler q p (u' + u) := by
    rw [eichler_mul hpu' hpuu', ← add_assoc, vec_add_self, zero_add]
  rw [he]
  exact mul_mem (Subgroup.subset_closure (hmem u' hu'F hpu' hqu'))
    (Subgroup.subset_closure (hmem _ (Submodule.add_mem _ hu'F huF) hpuu' hq'))

theorem mul_self_of_mem_radFix (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    {a : V} (ha0 : a ≠ 0) (ha : q a = 0) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ radFix q F a) :
    t * t = 1 := by
  obtain ⟨u, hau, rfl⟩ := (mem_pointRadical_iff hq ha0 ha).mp ht.1
  exact eichler_mul_self hau

theorem timmesfeld_2_1_c0 (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) (h3 : 3 ≤ finrank (ZMod 2) (perp q F)) {p p₁ : V}
    (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0)
    (hpp₁ : polar q p p₁ = 1) :
    ∃ y ∈ radFix q F p, ∃ z ∈ radFix q F p₁, IsTypeC q y 2 ∧ IsTypeC q z 2 ∧
      orderOf (y * z) = 3 ∧ (y * z) p = p₁ := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hp₁p : polar q p₁ p = 1 := by rw [polar_comm, hpp₁]
  obtain ⟨c, hcK, hc, -, -, -⟩ := exists_mem_radFix_not_isTypeA hq hF h3 hpF hp₁F hp0 hp hpp₁
  obtain ⟨hcF, hpc, hp₁c⟩ := mem_perp_sup_span_pair.mp hcK
  have hpow := eichler_mul_eichler_pow_three hp hp₁ hc hpp₁ hpc hp₁c
  refine ⟨eichler q p c, (mem_radFix_iff hq hp0 hp hpF).mpr ⟨c, hcF, hpc, rfl⟩,
    eichler q p₁ c, (mem_radFix_iff hq hp₁0 hp₁ hp₁F).mpr ⟨c, hcF, hp₁c, rfl⟩,
    (eichler_isTypeC hq hp0 hp hpc hc).1, (eichler_isTypeC hq hp₁0 hp₁ hp₁c hc).1, ?_, hpow.1⟩
  refine orderOf_eq_prime hpow.2 fun h => ?_
  have := hpow.1
  rw [h, LinearEquiv.coe_one, id] at this
  rw [this, polar_self_eq_zero] at hpp₁
  exact zero_ne_one hpp₁

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
variable {hq : q.polarBilin.Nondegenerate} (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M))

theorem mul_mul_eq_of_pow_three {G : Type*} [Group G] {Y Z : G} (hY : Y * Y = 1)
    (hZ : Z * Z = 1) (h3 : (Y * Z) ^ 3 = 1) : Z * Y * Z = Y * Z * Y := by
  have hYi : Y⁻¹ = Y := inv_eq_of_mul_eq_one_right hY
  have hZi : Z⁻¹ = Z := inv_eq_of_mul_eq_one_right hZ
  have e : Z * Y * Z = Y⁻¹ * (Y * Z) ^ 3 * Z⁻¹ * Y⁻¹ := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  rw [e, h3, mul_one, hYi, hZi]

omit [FiniteDimensional (ZMod 2) M] in
theorem sub_eq_of_pow_three {Y Z : M ≃ₗ[ZMod 2] M} (hY : Y * Y = 1) (hZ : Z * Z = 1)
    (h3 : (Y * Z) ^ 3 = 1) {N : Submodule (ZMod 2) M} (hYN : ∀ v ∈ N, Y v ∈ N)
    (hZN : ∀ v ∈ N, Z v ∈ N) (h0 : N ⊓ fixSpace Y ⊓ fixSpace Z = ⊥) {u : M} (huN : u ∈ N)
    (hu : Y u = u) : Z u - u = Y (Z u) := by
  have hYY : ∀ v, Y (Y v) = v := fun v => by rw [← LinearEquiv.mul_apply, hY]; rfl
  have hZZ : ∀ v, Z (Z v) = v := fun v => by rw [← LinearEquiv.mul_apply, hZ]; rfl
  have hZYZ : ∀ v, Z (Y (Z v)) = Y (Z (Y v)) := fun v => by
    have := LinearEquiv.congr_fun (mul_mul_eq_of_pow_three hY hZ h3) v
    simpa only [LinearEquiv.mul_apply] using this
  set w := u + Z u + Y (Z u) with hw
  have hYw : Y w = w := by
    rw [hw, map_add, map_add, hu, hYY]
    abel
  have hZw : Z w = w := by
    rw [hw, map_add, map_add, hZZ, hZYZ, hu]
    abel
  have hwN : w ∈ N := N.add_mem (N.add_mem huN (hZN u huN)) (hYN _ (hZN u huN))
  have hw0 : w = 0 := by
    have : w ∈ N ⊓ fixSpace Y ⊓ fixSpace Z := ⟨⟨hwN, mem_fixSpace.mpr hYw⟩, mem_fixSpace.mpr hZw⟩
    rwa [h0, Submodule.mem_bot] at this
  rw [hw, add_assoc, add_eq_zero_iff_eq_neg, vec_neg] at hw0
  nth_rewrite 2 [hw0]
  rw [sub_add_eq_sub_sub, sub_self, zero_sub, vec_neg]

theorem timmesfeld_2_1_c {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) {m : ℕ}
    (hm : 2 ≤ m) (hdim : finrank (ZMod 2) (perp q F) = 2 * m)
    (hgen : 3 ≤ m ∨ IsMinusType q F m) {N : Submodule (ZMod 2) M} (hN : OmegaInvariant ρ F N)
    {p p₁ : V} (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0)
    (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1) (hD : RadDecomp ρ F N p p₁)
    {U : Submodule (ZMod 2) M} (hUW : U ≤ N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V)))
    (hU : ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      (g : V ≃ₗ[ZMod 2] V) p = p → ∀ u ∈ U, ρ g u ∈ U)
    (g : omegaGroup q hq) (hgF : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F)
    (hgp : (g : V ≃ₗ[ZMod 2] V) p = p₁) :
    ∀ h : omegaGroup q hq, (h : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      ∀ v ∈ U ⊔ U.map (ρ g : M →ₗ[ZMod 2] M), ρ h v ∈ U ⊔ U.map (ρ g : M →ₗ[ZMod 2] M) := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hp₁p : polar q p₁ p = 1 := by rw [polar_comm, hpp₁]
  set U' := U.map (ρ g : M →ₗ[ZMod 2] M) with hU'def
  set L := (radFix q F p : Set (V ≃ₗ[ZMod 2] V)) with hLdef
  set L₁ := (radFix q F p₁ : Set (V ≃ₗ[ZMod 2] V)) with hL₁def
  have hLΩ : ∀ t ∈ radFix q F p, t ∈ omegaGroup q hq :=
    fun t ht => (radFix_le_omegaFix hq hp0 hp ht).1
  have hL₁Ω : ∀ t ∈ radFix q F p₁, t ∈ omegaGroup q hq :=
    fun t ht => (radFix_le_omegaFix hq hp₁0 hp₁ ht).1
  have hU'W : U' ≤ N ⊓ fixOf ρ L₁ := by
    have h := map_inf_fixOf_radFix ρ hN g hgF hpF hp0 hp
    rw [hgp] at h
    rw [hL₁def, ← h]
    exact Submodule.map_mono hUW
  have hmov : ∀ k : omegaGroup q hq, (k : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      (k : V ≃ₗ[ZMod 2] V) p = p₁ → ∀ u ∈ U, ρ k u ∈ U' := by
    intro k hkF hkp u hu
    refine ⟨ρ (g⁻¹ * k) u, hU _ (mul_mem (inv_mem hgF) hkF) ?_ u hu, ?_⟩
    · change (g : V ≃ₗ[ZMod 2] V)⁻¹ ((k : V ≃ₗ[ZMod 2] V) p) = p
      rw [hkp, ← hgp]
      exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' _ p
    · change ρ g (ρ (g⁻¹ * k) u) = ρ k u
      rw [map_mul, LinearEquiv.mul_apply, map_inv,
        CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply']
  have hmov' : ∀ k : omegaGroup q hq, (k : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      (k : V ≃ₗ[ZMod 2] V) p₁ = p → ∀ u' ∈ U', ρ k u' ∈ U := by
    rintro k hkF hkp _ ⟨u, hu, rfl⟩
    have : ρ k (ρ g u) = ρ (k * g) u := by rw [map_mul, LinearEquiv.mul_apply]
    change ρ k (ρ g u) ∈ U
    rw [this]
    refine hU _ (mul_mem hkF hgF) ?_ u hu
    change (k : V ≃ₗ[ZMod 2] V) ((g : V ≃ₗ[ZMod 2] V) p) = p
    rw [hgp, hkp]
  have hb0₁ : ∀ z : omegaGroup q hq, (z : V ≃ₗ[ZMod 2] V) ∈ radFix q F p₁ →
      (z : V ≃ₗ[ZMod 2] V) ≠ 1 → ¬ IsTypeA q z 2 → N ⊓ fixSpace (ρ z) = N ⊓ fixOf ρ L₁ :=
    fun z hz hz1 hza => (timmesfeld_2_1_b0 ρ hF hm hdim hN hpF hp₁F hp0 hp hp₁ hpp₁ hD z hz hz1
      hza).1
  have hb0 : ∀ y : omegaGroup q hq, (y : V ≃ₗ[ZMod 2] V) ∈ radFix q F p →
      (y : V ≃ₗ[ZMod 2] V) ≠ 1 → ¬ IsTypeA q y 2 → N ⊓ fixSpace (ρ y) = N ⊓ fixOf ρ L :=
    fun y hy hy1 hya => (timmesfeld_2_1_b0 ρ hF hm hdim hN hp₁F hpF hp₁0 hp₁ hp hp₁p hD.symm y
      hy hy1 hya).1
  have hsq : ∀ (a : V) (t : omegaGroup q hq), a ≠ 0 → q a = 0 →
      (t : V ≃ₗ[ZMod 2] V) ∈ radFix q F a → ρ t * ρ t = 1 := by
    intro a t ha0 ha ht
    rw [← map_mul, show t * t = 1 from Subtype.ext (mul_self_of_mem_radFix hq ha0 ha ht),
      map_one]
  have hcap : ∀ y z : omegaGroup q hq, (y : V ≃ₗ[ZMod 2] V) ∈ radFix q F p →
      (y : V ≃ₗ[ZMod 2] V) ≠ 1 → ¬ IsTypeA q y 2 → (z : V ≃ₗ[ZMod 2] V) ∈ radFix q F p₁ →
      (z : V ≃ₗ[ZMod 2] V) ≠ 1 → ¬ IsTypeA q z 2 →
      N ⊓ fixSpace (ρ y) ⊓ fixSpace (ρ z) = ⊥ := by
    intro y z hy hy1 hya hz hz1 hza
    rw [eq_bot_iff, ← hD.2]
    rintro v ⟨⟨hvN, hvy⟩, hvz⟩
    have h1 : v ∈ N ⊓ fixSpace (ρ y) := ⟨hvN, hvy⟩
    have h2 : v ∈ N ⊓ fixSpace (ρ z) := ⟨hvN, hvz⟩
    rw [hb0 y hy hy1 hya] at h1
    rw [hb0₁ z hz hz1 hza] at h2
    exact ⟨h1, h2⟩
  have key1 : ∀ z : omegaGroup q hq, (z : V ≃ₗ[ZMod 2] V) ∈ radFix q F p₁ →
      (z : V ≃ₗ[ZMod 2] V) ≠ 1 → ¬ IsTypeA q z 2 → ∀ u ∈ U, ρ z u - u ∈ U' := by
    intro z hz hz1 hza u hu
    obtain ⟨y, hyL, hy1, hya, hyzp, hyz3⟩ :=
      exists_partner_left hq hpF hp₁F hp0 hp₁0 hp hp₁ hpp₁ hz hz1 hza
    set Y : omegaGroup q hq := ⟨y, hLΩ y hyL⟩ with hYdef
    have h3 : (ρ Y * ρ z) ^ 3 = 1 := by
      rw [← map_mul, ← map_pow,
        show (Y * z) ^ 3 = 1 from Subtype.ext (by
          rw [SubgroupClass.coe_pow, Subgroup.coe_mul]
          exact hyz3), map_one]
    have hu' := hUW hu
    have e := sub_eq_of_pow_three (hsq p Y hp0 hp hyL) (hsq p₁ z hp₁0 hp₁ hz) h3
      (hN Y hyL.2) (hN z hz.2) (hcap Y z hyL hy1 hya hz hz1 hza) hu'.1 (hu'.2 Y hyL)
    rw [e, ← LinearEquiv.mul_apply, ← map_mul]
    exact hmov _ (mul_mem hyL.2 hz.2) hyzp u hu
  have key2 : ∀ y : omegaGroup q hq, (y : V ≃ₗ[ZMod 2] V) ∈ radFix q F p →
      (y : V ≃ₗ[ZMod 2] V) ≠ 1 → ¬ IsTypeA q y 2 → ∀ u' ∈ U', ρ y u' - u' ∈ U := by
    intro y hy hy1 hya u' hu'
    obtain ⟨z, hzL, hz1, hza, hyzp, hyz3⟩ :=
      exists_partner_right hq hpF hp₁F hp0 hp₁0 hp hp₁ hpp₁ hy hy1 hya
    set Z : omegaGroup q hq := ⟨z, hL₁Ω z hzL⟩ with hZdef
    have hzy : ((Z * y : omegaGroup q hq) : V ≃ₗ[ZMod 2] V) p₁ = p := by
      change z ((y : V ≃ₗ[ZMod 2] V) p₁) = p
      rw [← hyzp, LinearEquiv.mul_apply]
      have h1 := LinearEquiv.congr_fun (mul_self_of_mem_radFix hq hp0 hp hy) (z p)
      have h2 := LinearEquiv.congr_fun (mul_self_of_mem_radFix hq hp₁0 hp₁ hzL) p
      rw [LinearEquiv.mul_apply, LinearEquiv.coe_one, id] at h1 h2
      rw [h1, h2]
    have h3 : (ρ Z * ρ y) ^ 3 = 1 := by
      have hyz : (ρ y * ρ Z) ^ 3 = 1 := by
        rw [← map_mul, ← map_pow,
          show (y * Z) ^ 3 = 1 from Subtype.ext (by
            rw [SubgroupClass.coe_pow, Subgroup.coe_mul]
            exact hyz3), map_one]
      have hYi : (ρ y)⁻¹ = ρ y := inv_eq_of_mul_eq_one_right (hsq p y hp0 hp hy)
      have hZi : (ρ Z)⁻¹ = ρ Z := inv_eq_of_mul_eq_one_right (hsq p₁ Z hp₁0 hp₁ hzL)
      have : ρ Z * ρ y = (ρ y * ρ Z)⁻¹ := by rw [mul_inv_rev, hYi, hZi]
      rw [this, inv_pow, hyz, inv_one]
    have hu'' := hU'W hu'
    have e := sub_eq_of_pow_three (hsq p₁ Z hp₁0 hp₁ hzL) (hsq p y hp0 hp hy) h3
      (hN Z hzL.2) (hN y hy.2) (by rw [inf_right_comm]; exact hcap y Z hy hy1 hya hzL hz1 hza)
      hu''.1 (hu''.2 Z hzL)
    rw [e, ← LinearEquiv.mul_apply, ← map_mul]
    exact hmov' _ (mul_mem hzL.2 hy.2) hzy u' hu'
  have hfixU' : ∀ v ∈ U', ∀ t : omegaGroup q hq, (t : V ≃ₗ[ZMod 2] V) ∈ radFix q F p₁ →
      ρ t v = v := fun v hv t ht => (hU'W hv).2 t ht
  have hfixU : ∀ v ∈ U, ∀ t : omegaGroup q hq, (t : V ≃ₗ[ZMod 2] V) ∈ radFix q F p →
      ρ t v = v := fun v hv t ht => (hUW hv).2 t ht
  have gen : ∀ {a : V} {W W' : Submodule (ZMod 2) M}, a ∈ perp q F → a ≠ 0 → q a = 0 →
      (∀ v ∈ W', ∀ t : omegaGroup q hq, (t : V ≃ₗ[ZMod 2] V) ∈ radFix q F a → ρ t v = v) →
      (∀ z : omegaGroup q hq, (z : V ≃ₗ[ZMod 2] V) ∈ radFix q F a →
        (z : V ≃ₗ[ZMod 2] V) ≠ 1 → ¬ IsTypeA q z 2 → ∀ u ∈ W, ρ z u - u ∈ W') →
      ∀ t : omegaGroup q hq, (t : V ≃ₗ[ZMod 2] V) ∈ radFix q F a → ∀ u ∈ W, ρ t u - u ∈ W' := by
    intro a W W' haF ha0 ha hfix hkey t ht
    have hcl := radFix_le_closure_not_isTypeA hq hF hm hdim hgen haF ha0 ha ht
    have hcle : Subgroup.closure {t | t ∈ radFix q F a ∧ t ≠ 1 ∧ ¬ IsTypeA q t 2} ≤
        radFix q F a := (Subgroup.closure_le _).mpr fun x hx => hx.1
    have hΩ : ∀ x ∈ radFix q F a, x ∈ omegaGroup q hq :=
      fun x hx => (radFix_le_omegaFix hq ha0 ha hx).1
    suffices h : ∀ x ∈ Subgroup.closure {t | t ∈ radFix q F a ∧ t ≠ 1 ∧ ¬ IsTypeA q t 2},
        ∀ hx : x ∈ omegaGroup q hq, ∀ u ∈ W, ρ ⟨x, hx⟩ u - u ∈ W' from h t hcl t.2
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact fun hxΩ u hu => hkey ⟨x, hxΩ⟩ hx.1 hx.2.1 hx.2.2 u hu
    | one =>
      intro h1 u hu
      rw [show (⟨1, h1⟩ : omegaGroup q hq) = 1 from rfl, map_one, LinearEquiv.coe_one, id,
        sub_self]
      exact W'.zero_mem
    | mul x y hx hy ihx ihy =>
      intro hxy u hu
      have hxΩ := hΩ x (hcle hx)
      have hyΩ := hΩ y (hcle hy)
      have e : (⟨x * y, hxy⟩ : omegaGroup q hq) = ⟨x, hxΩ⟩ * ⟨y, hyΩ⟩ := rfl
      have h1 := ihy hyΩ u hu
      have h2 := hfix _ h1 ⟨x, hxΩ⟩ (hcle hx)
      rw [e, map_mul, LinearEquiv.mul_apply,
        show ρ ⟨x, hxΩ⟩ (ρ ⟨y, hyΩ⟩ u) - u = ρ ⟨x, hxΩ⟩ (ρ ⟨y, hyΩ⟩ u - u) + (ρ ⟨x, hxΩ⟩ u - u)
          by rw [map_sub]; abel, h2]
      exact W'.add_mem h1 (ihx hxΩ u hu)
    | inv x hx ihx =>
      intro hxi u hu
      have hxΩ := hΩ x (hcle hx)
      have e : (⟨x⁻¹, hxi⟩ : omegaGroup q hq) = (⟨x, hxΩ⟩ : omegaGroup q hq)⁻¹ := rfl
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
  have key3 := gen hp₁F hp₁0 hp₁ hfixU' key1
  have key4 := gen hpF hp0 hp hfixU key2
  have inv₁ : ∀ t : omegaGroup q hq, (t : V ≃ₗ[ZMod 2] V) ∈ radFix q F p₁ →
      ∀ v ∈ U ⊔ U', ρ t v ∈ U ⊔ U' := by
    intro t ht v hv
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hfixU' u' hu' t ht,
      show ρ t u = u + (ρ t u - u) by abel]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left hu)
      (Submodule.mem_sup_right (key3 t ht u hu))) (Submodule.mem_sup_right hu')
  have inv₀ : ∀ t : omegaGroup q hq, (t : V ≃ₗ[ZMod 2] V) ∈ radFix q F p →
      ∀ v ∈ U ⊔ U', ρ t v ∈ U ⊔ U' := by
    intro t ht v hv
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hfixU u hu t ht, show ρ t u' = u' + (ρ t u' - u') by abel]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hu) (Submodule.add_mem _
      (Submodule.mem_sup_right hu') (Submodule.mem_sup_left (key4 t ht u' hu')))
  intro h hhF
  have hgenX := omegaFix_eq_closure_radFix hq hF hm hdim hpF hp₁F hp0 hp hp₁ hpp₁
  have hh : (h : V ≃ₗ[ZMod 2] V) ∈ Subgroup.closure (L ∪ L₁) := by
    rw [← hgenX]
    exact ⟨h.2, hhF⟩
  have hclΩ : Subgroup.closure (L ∪ L₁) ≤ omegaGroup q hq := by
    rw [← hgenX]
    exact inf_le_left
  suffices hs : ∀ x ∈ Subgroup.closure (L ∪ L₁), ∀ hx : x ∈ omegaGroup q hq,
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
    rw [show (⟨1, h1⟩ : omegaGroup q hq) = 1 from rfl, map_one, LinearEquiv.coe_one, id]
    exact hv
  | mul x y hx hy ihx ihy =>
    intro hxy v hv
    have e : (⟨x * y, hxy⟩ : omegaGroup q hq) = ⟨x, hclΩ hx⟩ * ⟨y, hclΩ hy⟩ := rfl
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
    have e : (⟨x⁻¹, hxi⟩ : omegaGroup q hq) = (⟨x, hxΩ⟩ : omegaGroup q hq)⁻¹ := rfl
    rw [e, map_inv]
    change (ρ ⟨x, hxΩ⟩)⁻¹ (ρ ⟨x, hxΩ⟩ w) ∈ U ⊔ U'
    rw [CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply']
    exact hw

end S2

end CFSG.LargeExtraspecial
