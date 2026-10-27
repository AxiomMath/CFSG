module

public import CFSG.CGT.Timmesfeld75.Sec77Model

public section

namespace CFSG.CGT.T75F

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {m : ℕ}

section Basic

theorem card_normIn_three (hc : Sec6Ctx T T₁ 3 m) : Nat.card (normIn T T₁) = (2 ^ m) ^ 2 := by
  have := hc.card_normIn
  simpa using this

theorem card_normIn₁_three (hc : Sec6Ctx T T₁ 3 m) : Nat.card (normIn T₁ T) = (2 ^ m) ^ 2 := by
  rw [hc.card_normIn_swap, card_normIn_three hc]

theorem card_cfgM_three (hc : Sec6Ctx T T₁ 3 m) : Nat.card (cfgM T T₁) = (2 ^ m) ^ 4 := by
  rw [hc.sec3.cfg.card_cfgM, card_normIn_three hc, card_normIn₁_three hc]
  ring

theorem mem_normD_of_mem_normIn₁ {n : ℕ} (hc : Sec6Ctx T T₁ n m) {e : G}
    (he : e ∈ normIn T₁ T) (he1 : e ≠ 1) : e ∈ normD T ∧ e ∉ T := by
  have hP := hc.hy.pair
  have hS3 := hc.sec3
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun w hw => (mem_normIn.1 hw).2
  obtain ⟨x₀, hx₀⟩ := hP.conj
  have huk : e ∈ conjSubgroup x₀ T := hx₀ ▸ normIn_le _ _ he
  refine ⟨mem_normD_of_mem_conjSubgroup huk he1 (hL₁N he), fun heT => he1 ?_⟩
  have : e ∈ T ⊓ T₁ := ⟨heT, normIn_le _ _ he⟩
  rw [hS3.cfg.inf, Subgroup.mem_bot] at this
  exact this

theorem mem_normIn_of_mem_cfgM {n : ℕ} (hc : Sec6Ctx T T₁ n m) {a : G} (ha : a ∈ cfgM T T₁)
    (haT : a ∈ T) : a ∈ normIn T T₁ := by
  have hcfg := hc.sec3.cfg
  obtain ⟨l, hl, x, hx, rfl⟩ := hcfg.mem_cfgM_iff.1 ha
  have hxT : x ∈ T := by
    have h1 : l⁻¹ * (l * x) ∈ T := T.mul_mem (T.inv_mem (normIn_le _ _ hl)) haT
    simpa using h1
  have hx1 : x = 1 := by
    have : x ∈ T ⊓ T₁ := ⟨hxT, normIn_le _ _ hx⟩
    rw [hcfg.inf, Subgroup.mem_bot] at this
    exact this
  rw [hx1, mul_one]
  exact hl

theorem mem_normIn_iff_comm (h63 : Sec63) (hc : Sec6Ctx T T₁ 3 m) {e : G}
    (he : e ∈ normIn T₁ T) (he1 : e ≠ 1) {t : G} (ht : t ∈ T) :
    t ∈ normIn T T₁ ↔ e * t = t * e := by
  have hcfg := hc.sec3.cfg
  have := hc.finite
  constructor
  · intro htL
    exact (hcfg.comm_L_L₁ htL he).symm
  · intro hcomm
    obtain ⟨hD, hT⟩ := mem_normD_of_mem_normIn₁ hc he he1
    have hcard := hc.card_centralizer_eq h63 (by omega) hD hT
    have hle : normIn T T₁ ≤ T ⊓ Subgroup.centralizer ({e} : Set G) := by
      intro l hl
      refine ⟨normIn_le _ _ hl, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (hcfg.comm_L_L₁ hl he)
    have heq : normIn T T₁ = T ⊓ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
    rw [heq]
    exact ⟨ht, Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm⟩

end Basic

section Model

variable [(T.subgroupOf (hSub T (normIn T₁ T))).Normal] (M : TModel T T₁ 3 m)

theorem _root_.CFSG.CGT.Timmesfeld75.TModel.toAdd_phi_comm_eq {n : ℕ} (M : TModel T T₁ n m)
    {e : G} (he : e ∈ normD T)
    {f : Module.Dual (GaloisField 2 m) (Fin n → GaloisField 2 m)} {v : Fin n → GaloisField 2 m}
    (hdata : ∀ w, sact (ubar M.ε e) w = w + f w • v) {s : G} (hs : s ∈ T) :
    Multiplicative.toAdd (M.φ ⟨⁅e, s⁆, comm_mem_of_mem_normalizer he.2 hs⟩) =
      f (Multiplicative.toAdd (M.φ ⟨s, hs⟩)) • v := by
  have heH := M.mem_H he
  have h := toAdd_phi_comm M.compat heH he.2 hs (comm_mem_of_mem_normalizer he.2 hs)
  rw [h]
  have h2 : ((M.ε (QuotientGroup.mk (⟨e, heH⟩ : ↥(hSub T (normIn T₁ T)))) :
      SL(n, GaloisField 2 m)) : Matrix (Fin n) (Fin n) (GaloisField 2 m)) *ᵥ
        Multiplicative.toAdd (M.φ ⟨s, hs⟩) = sact (ubar M.ε e)
          (Multiplicative.toAdd (M.φ ⟨s, hs⟩)) := by
    rw [ubar_of_mem M.ε heH]
    rfl
  rw [h2, hdata]
  abel

theorem _root_.CFSG.CGT.Timmesfeld75.TModel.comm_iff_apply_eq_zero {n : ℕ}
    (M : TModel T T₁ n m) {e : G} (he : e ∈ normD T)
    {f : Module.Dual (GaloisField 2 m) (Fin n → GaloisField 2 m)} {v : Fin n → GaloisField 2 m}
    (hv : v ≠ 0) (hdata : ∀ w, sact (ubar M.ε e) w = w + f w • v) {t : G} (ht : t ∈ T) :
    e * t = t * e ↔ f (Multiplicative.toAdd (M.φ ⟨t, ht⟩)) = 0 := by
  have hcomm := M.toAdd_phi_comm_eq he hdata ht
  rw [← commutatorElement_eq_one_iff_mul_comm]
  have key : ⁅e, t⁆ = 1 ↔ f (Multiplicative.toAdd (M.φ ⟨t, ht⟩)) • v = 0 := by
    constructor
    · intro h1
      have h2 : (⟨⁅e, t⁆, comm_mem_of_mem_normalizer he.2 ht⟩ : ↥T) = 1 := Subtype.ext h1
      rw [← hcomm, h2, map_one]
      rfl
    · intro h1
      have h2 : Multiplicative.toAdd (M.φ ⟨⁅e, t⁆, comm_mem_of_mem_normalizer he.2 ht⟩) = 0 := by
        rw [hcomm]
        exact h1
      have h3 : M.φ ⟨⁅e, t⁆, comm_mem_of_mem_normalizer he.2 ht⟩ = M.φ 1 := by
        rw [map_one]
        exact Multiplicative.toAdd.injective h2
      exact congrArg Subtype.val (M.φ.injective h3)
  rw [key]
  exact (smul_eq_zero.trans (or_iff_left hv))

theorem exists_data_normIn₁ (h63 : Sec63) (hc : Sec6Ctx T T₁ 3 m) {e : G}
    (he : e ∈ normIn T₁ T) (he1 : e ≠ 1) :
    ∃ (f : Module.Dual (GaloisField 2 m) (Fin 3 → GaloisField 2 m))
      (v : Fin 3 → GaloisField 2 m), f ≠ 0 ∧ v ≠ 0 ∧ f v = 0 ∧
      (∀ w, sact (ubar M.ε e) w = w + f w • v) ∧
      ∀ (t : G) (ht : t ∈ T), t ∈ normIn T T₁ ↔ f (Multiplicative.toAdd (M.φ ⟨t, ht⟩)) = 0 := by
  obtain ⟨hD, hT⟩ := mem_normD_of_mem_normIn₁ hc he he1
  obtain ⟨f, v, hfv, hv, hf, hdata⟩ := M.exists_data hD hT
  refine ⟨f, v, hf, hv, hfv, hdata, fun t ht => ?_⟩
  rw [mem_normIn_iff_comm h63 hc he he1 ht, M.comm_iff_apply_eq_zero hD hv hdata ht]

end Model

end CFSG.CGT.T75F
