module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance

theorem card_le_mul_card_ker' {H C : Type*} [Group H] [Group C] [Finite H] [IsCyclic C]
    {p : ℕ} (hp : p.Prime) (hexp : ∀ h : H, h ^ p = 1) (α : H →* C) :
    Nat.card H ≤ p * Nat.card α.ker := by
  have hexpα : Monoid.exponent α.range ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
    obtain ⟨x, rfl⟩ := α.rangeRestrict_surjective y
    rw [← map_pow, hexp x, map_one]
  rw [IsCyclic.exponent_eq_card] at hexpα
  have hsplit : Nat.card H = Nat.card α.range * Nat.card α.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv]
  rw [hsplit]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd hp.pos hexpα)

instance innerAut_normal (K : Type*) [Group K] : (innerAut K).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨k, rfl⟩ := hx
  exact ⟨g k, by rw [← mul_conj_mul_inv]⟩

theorem exists_plane_of_hom_cyclic {M : Type*} [Group M] {p : ℕ} (hp : p.Prime) (I : Subgroup M)
    {D : Subgroup M} (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 3)
    {C : Type*} [Group C] [IsCyclic C] (α : D →* C) (hker' : ∀ x : D, α x = 1 → (x : M) ∈ I) :
    ∃ E : Subgroup M, E ≤ D ∧ E ≤ I ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hDfin : Finite D :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  have hle := card_le_mul_card_ker' hp (fun h : D => Subtype.ext (hD.2 h h.2)) α
  have hker : p ^ 2 ≤ Nat.card α.ker := by
    by_contra hlt
    push Not at hlt
    have : Nat.card D ≤ p * (p ^ 2 - 1) := hle.trans (Nat.mul_le_mul_left _ (by omega))
    have h3 : p ^ 3 = p * p ^ 2 := by ring
    have := hp.pos
    have : p * (p ^ 2 - 1) < p * p ^ 2 := Nat.mul_lt_mul_of_pos_left (by omega) hp.pos
    omega
  have hdvd : Nat.card α.ker ∣ p ^ 3 := hcard ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨j, hj, hjk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hj2 : 2 ≤ j := by
    by_contra hlt
    push Not at hlt
    have : p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    have : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hker2 : p ^ 2 ∣ Nat.card α.ker := hjk ▸ pow_dvd_pow p hj2
  have : Finite α.ker := Finite.of_injective _ α.ker.subtype_injective
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime p hker2
  let φ : α.ker →* M := D.subtype.comp α.ker.subtype
  have hφ : Function.Injective φ := D.subtype_injective.comp α.ker.subtype_injective
  have hφD : ∀ x : α.ker, φ x ∈ D := fun x => (x : D).2
  refine ⟨P.map φ, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hφD x
  · rintro _ ⟨x, -, rfl⟩
    exact hker' (x : D) x.2
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨x, -, hx⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      have h := hD.1.is_comm.comm ⟨φ x, hφD x⟩ ⟨φ y, hφD y⟩
      have h2 := congrArg Subtype.val h
      change (a : M) * b = b * a
      rw [← hx, ← hy]
      exact h2
    · obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hy
      exact hD.2 _ (hφD x)
  · rw [Subgroup.card_map_of_injective hφ, hP]

theorem exists_inner_plane_of_cyclic {G : Type*} [Group G]
    (hcyc : IsCyclic (MulAut G ⧸ innerAut G)) {p : ℕ} (hp : p.Prime)
    (D : Subgroup (MulAut G)) (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 3) :
    ∃ E : Subgroup (MulAut G), E ≤ D ∧ E ≤ innerAut G ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 2 :=
  exists_plane_of_hom_cyclic hp (innerAut G) hD hcard
    ((QuotientGroup.mk' (innerAut G)).comp D.subtype) fun _ hx =>
      (QuotientGroup.eq_one_iff _).1 hx

theorem isCyclic_outer_of_gen {G : Type*} [Group G] (F : MulAut G)
    (hF : ∀ α : MulAut G, ∃ (g : G) (k : ℕ), α = MulAut.conj g * F ^ k) :
    IsCyclic (MulAut G ⧸ innerAut G) := by
  let π : MulAut G →* MulAut G ⧸ innerAut G := QuotientGroup.mk' (innerAut G)
  refine ⟨⟨π F, fun x => ?_⟩⟩
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g, k, hα⟩ := hF α
  have h1 : π (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
  have : π α = π F ^ k := by rw [hα, map_mul, h1, one_mul, map_pow]
  change π α ∈ Subgroup.zpowers (π F)
  rw [this]
  exact ⟨(k : ℤ), by simp⟩

theorem isCyclic_outer_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : IsCyclic (MulAut G' ⧸ innerAut G')) : IsCyclic (MulAut G ⧸ innerAut G) := by
  let π' : MulAut G' →* MulAut G' ⧸ innerAut G' := QuotientGroup.mk' (innerAut G')
  let π : MulAut G →* MulAut G ⧸ innerAut G := QuotientGroup.mk' (innerAut G)
  obtain ⟨c, hc⟩ := h
  obtain ⟨F', rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨⟨π ((MulAut.congr e).symm F'), fun x => ?_⟩⟩
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hc (π' (MulAut.congr e α)))
  have h1 : (MulAut.congr e α) * (F' ^ k)⁻¹ ∈ innerAut G' := by
    have : π' ((MulAut.congr e α) * (F' ^ k)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow]
      have : π' F' ^ k = π' (MulAut.congr e α) := hk
      rw [this, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).1 this
  obtain ⟨g', hg'⟩ := h1
  have h2 : α * ((MulAut.congr e).symm F' ^ k)⁻¹ = MulAut.conj (e.symm g') := by
    apply (MulAut.congr e).injective
    rw [map_mul, map_inv, map_zpow, MulEquiv.apply_symm_apply, ← hg']
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have h3 : π α * (π ((MulAut.congr e).symm F') ^ k)⁻¹ = 1 := by
    rw [← map_zpow, ← map_inv, ← map_mul, h2]
    exact (QuotientGroup.eq_one_iff _).2 ⟨_, rfl⟩
  exact ⟨k, (mul_inv_eq_one.1 h3).symm⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar
