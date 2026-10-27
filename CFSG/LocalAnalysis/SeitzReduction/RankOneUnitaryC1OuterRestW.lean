module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterRestBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

@[expose] def outerRestOmega {G : Type*} [Group G] {V : Subgroup G}
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (m : ℕ) : Subgroup G where
  carrier := {x | x ∈ V ∧ x ^ m = 1}
  mul_mem' := by
    rintro x y ⟨hx, hx1⟩ ⟨hy, hy1⟩
    exact ⟨mul_mem hx hy, by rw [(Commute.mul_pow (hcomm x hx y hy) m), hx1, hy1, one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow m⟩
  inv_mem' := by
    rintro x ⟨hx, hx1⟩
    exact ⟨inv_mem hx, by rw [inv_pow, hx1, inv_one]⟩

theorem mem_outerRestOmega {G : Type*} [Group G] {V : Subgroup G}
    {hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x} {m : ℕ} {x : G} :
    x ∈ outerRestOmega hcomm m ↔ x ∈ V ∧ x ^ m = 1 :=
  Iff.rfl

theorem outerRestOmega_le {G : Type*} [Group G] {V : Subgroup G}
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (m : ℕ) : outerRestOmega hcomm m ≤ V :=
  fun _ hx => hx.1

@[expose] def outerRestPowHom {G : Type*} [Group G] {V : Subgroup G}
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (m : ℕ) : V →* G :=
  MonoidHom.mk' (fun x => (x : G) ^ m) fun x y => by
    rw [Subgroup.coe_mul]
    exact (Commute.mul_pow (hcomm x x.2 y y.2) m)

theorem outerRestPowHom_apply {G : Type*} [Group G] {V : Subgroup G}
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (m : ℕ) (x : V) :
    outerRestPowHom hcomm m x = (x : G) ^ m :=
  rfl

namespace U3C1OuterConf

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D V : Subgroup G} {k : ℕ}

theorem outerRest_conj_mem_W (hc : U3C1OuterConf G L f t T R₂ D V k)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hk : 2 ≤ k) {n : G} (hn : n ∈ normalizer (szR (szT₁ L T) V t : Set G)) {x : G}
    (hx : x ∈ V ⊔ zpowers t) : n * x * n⁻¹ ∈ V ⊔ zpowers t := by
  have hnV := (hc.normalizer_szR_le h hS2 hk hn).2.1
  have hσ := hc.outerRest_comm_t_mem h hS2 hk hn
  have hle : V ⊔ zpowers t ≤ (V ⊔ zpowers t).comap (MulAut.conj n).toMonoidHom := by
    refine sup_le (fun r hr => ?_) (zpowers_le.mpr ?_)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mem_sup_left ((mem_normalizer_iff.mp hnV r).mp hr)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        show n * t * n⁻¹ = (n * t * n⁻¹ * t⁻¹) * t by group]
      exact mul_mem (mem_sup_left hσ) (mem_sup_right (mem_zpowers t))
  have := hle hx
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem outerRest_le_normalizer_W
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) :
    normalizer (szR (szT₁ L T) V t : Set G) ≤ normalizer ((V ⊔ zpowers t : Subgroup G) : Set G) :=
  fun n hn => mem_normalizer_iff.mpr fun x => ⟨hc.outerRest_conj_mem_W h hS2 hk hn, fun hx => by
    have := hc.outerRest_conj_mem_W h hS2 hk (inv_mem hn) hx
    rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this⟩

theorem outerRest_conj_mem_powKer (hc : U3C1OuterConf G L f t T R₂ D V k) {n : G}
    (hnV : n ∈ normalizer (V : Set G)) {x : G} (hx : x ∈ outerRestOmega hc.comm (2 ^ k)) :
    n * x * n⁻¹ ∈ outerRestOmega hc.comm (2 ^ k) :=
  ⟨(mem_normalizer_iff.mp hnV x).mp hx.1, by rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩

theorem outerRest_le_normalizer_powKer (hc : U3C1OuterConf G L f t T R₂ D V k) :
    normalizer (V : Set G) ≤ normalizer ((outerRestOmega hc.comm (2 ^ k) : Subgroup G) : Set G) :=
  fun n hn => mem_normalizer_iff.mpr fun x => ⟨hc.outerRest_conj_mem_powKer hn, fun hx => by
    have := hc.outerRest_conj_mem_powKer (inv_mem hn) hx
    rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this⟩

theorem outerRest_W_le_normalizer_V (hc : U3C1OuterConf G L f t T R₂ D V k)
    (h : U3Start G L f t T) : V ⊔ zpowers t ≤ normalizer (V : Set G) := by
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  refine sup_le Subgroup.le_normalizer (zpowers_le.mpr
    (mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => ?_))
  rw [htinv, show t * x * t = t * x * t⁻¹ by rw [htinv], hc.inv x hx]
  exact inv_mem hx

theorem outerRest_W_le_normalizer_powKer (hc : U3C1OuterConf G L f t T R₂ D V k)
    (h : U3Start G L f t T) :
    V ⊔ zpowers t ≤ normalizer ((outerRestOmega hc.comm (2 ^ k) : Subgroup G) : Set G) :=
  (hc.outerRest_W_le_normalizer_V h).trans hc.outerRest_le_normalizer_powKer

theorem outerRest_mem_W (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T) {x : G}
    (hx : x ∈ V ⊔ zpowers t) : ∃ r ∈ V, x = r ∨ x = r * t := by
  have hx' : x ∈ ((V ⊔ zpowers t : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left V (zpowers t)
    ((le_sup_right : zpowers t ≤ V ⊔ zpowers t).trans (hc.outerRest_W_le_normalizer_V h))] at hx'
  obtain ⟨r, hr, z, hz, rfl⟩ := Set.mem_mul.mp hx'
  rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
  · exact ⟨r, hr, Or.inl (mul_one r)⟩
  · exact ⟨r, hr, Or.inr rfl⟩

theorem outerRest_mul_t_sq (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    {r : G} (hr : r ∈ V) : (r * t) ^ 2 = 1 := by
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have h1 := hc.inv r hr
  calc (r * t) ^ 2 = r * (t * r * t⁻¹) * (t * t) := by rw [sq]; group
    _ = 1 := by rw [h1, ht2]; group

theorem outerRest_sq_mem_powKer (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    {x : G} (hx : x ∈ V ⊔ zpowers t) : x ^ 2 ∈ outerRestOmega hc.comm (2 ^ k) := by
  obtain ⟨r, hr, rfl | rfl⟩ := hc.outerRest_mem_W h hx
  · exact ⟨pow_mem hr 2, by rw [← pow_mul, ← pow_succ', hc.pow _ hr]⟩
  · rw [hc.outerRest_mul_t_sq h hr]; exact one_mem _

theorem outerRest_card_powKer
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    Nat.card (outerRestOmega hc.comm (2 ^ k)) = (2 ^ f) ^ k := by
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  set P := outerRestPowHom hc.comm (2 ^ k) with hP
  have hrange : P.range = szA₁ (szT₁ L T) := by
    refine le_antisymm ?_ fun b hb => ?_
    · rintro _ ⟨x, rfl⟩
      rw [outerRestPowHom_apply]
      exact hc.outerRest_pow_mem_szA₁ x.2
    · obtain ⟨r, hr, hrb⟩ := hc.outerRest_exists_pow_eq h hS2 hb
      exact ⟨⟨r, hr⟩, by rw [outerRestPowHom_apply]; exact hrb⟩
  have hker : Nat.card P.ker = Nat.card (outerRestOmega hc.comm (2 ^ k)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : V) : G), (x : V).2, x.2⟩
        invFun := fun x => ⟨⟨x, x.2.1⟩, x.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  have h1 := SzC1.card_eq_card_ker_mul_card_range P
  rw [hc.card, hker, hrange, hA₁card] at h1
  have h2 : Nat.card (outerRestOmega hc.comm (2 ^ k)) * 2 ^ f = (2 ^ f) ^ k * 2 ^ f := by
    rw [← h1]; ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h2

theorem outerRest_mul_t_iff (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    {σ r : G} (hσ : σ ∈ V) (hr : r ∈ V) :
    (σ * t)⁻¹ * (r * t) ∈ outerRestOmega hc.comm (2 ^ k) ↔ σ ^ 2 ^ k = r ^ 2 ^ k := by
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have e : (σ * t)⁻¹ * (r * t) = r⁻¹ * σ := by
    have h1 := hc.inv _ (mul_mem (inv_mem hσ) hr)
    calc (σ * t)⁻¹ * (r * t) = t⁻¹ * (σ⁻¹ * r) * t := by group
      _ = t * (σ⁻¹ * r) * t⁻¹ := by rw [htinv]
      _ = r⁻¹ * σ := by rw [h1]; group
  rw [e]
  constructor
  · rintro ⟨-, h1⟩
    rw [(Commute.mul_pow (hc.comm _ (inv_mem hr) _ hσ) _), inv_pow] at h1
    exact (eq_of_inv_mul_eq_one h1).symm
  · intro h1
    refine ⟨mul_mem (inv_mem hr) hσ, ?_⟩
    rw [(Commute.mul_pow (hc.comm _ (inv_mem hr) _ hσ) _), inv_pow, h1, inv_mul_cancel]

end U3C1OuterConf

end CFSG.SeitzReduction.RankOne
