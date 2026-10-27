module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21SixA
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoGroupShapes

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.Quot

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {t u : G} {P V : Subgroup G} {v u₀ : G}

theorem card_nsub (C : SixAW t u P V v u₀) : Nat.card (nsub t u P) = 16 := by
  have h := C.secTwo
  have hv : v ∈ nsub t u P := ⟨C.v_mem_P, C.v_normalizer⟩
  have hRN : secTwoR t u ≤ nsub t u P := fun g hg => ⟨C.R_le hg, le_normalizer hg⟩
  have hcent : nsub t u P ⊓ centralizer ({t} : Set G) = secTwoR t u := by
    refine le_antisymm (fun g hg => ?_) (le_inf hRN h.R_le_centralizer)
    exact h.mem_R_of_commute C.pgroup C.R_le hg.1.1 (mem_centralizer_singleton_iff.mp hg.2)
  rcases h.orbit_cases (N := nsub t u P) inf_le_right with hle | ⟨hidx, -⟩
  · exfalso
    have hc : v * t = t * v := mem_centralizer_singleton_iff.mp (hle hv)
    have hvt : v * t * v⁻¹ = t := by rw [hc]; group
    exact h.z_ne_one (mul_eq_left.mp (C.v_t.symm.trans hvt))
  · rw [hcent] at hidx
    have h1 := Subgroup.relIndex_mul_card (secTwoR t u) (nsub t u P)
    rw [inf_of_le_left hRN, hidx, I21.card_R_eq h] at h1
    omega

theorem relIndex_zpowers_nsub (C : SixAW t u P V v u₀) :
    (zpowers u₀).relIndex (nsub t u P) = 4 := by
  have hle : zpowers u₀ ≤ nsub t u P :=
    zpowers_le.mpr ⟨C.u₀_mem_P, le_normalizer C.u₀_mem_R⟩
  have h1 := Subgroup.relIndex_mul_card (zpowers u₀) (nsub t u P)
  rw [inf_of_le_left hle, Nat.card_zpowers, C.u₀_order, card_nsub C] at h1
  omega

theorem t_mul_pow_u₀ (C : SixAW t u P V v u₀) (n : ℕ) : t * u₀ ^ n = u₀ ^ n * t :=
  ((show Commute t u₀ from C.t_u₀).pow_right n).eq

theorem mem_nsub_iff (C : SixAW t u P V v u₀) {p : G} (hp : p ∈ P) :
    p ∈ nsub t u P ↔ p⁻¹ * t * p = t ∨ p⁻¹ * t * p = t * u ^ 2 := by
  have h := C.mem_N_iff (inv_mem hp)
  rw [inv_mem_iff, inv_inv] at h
  exact h

theorem comm_mem_zpowers_iff (C : SixAW t u P V v u₀) {p : G} (hp : p ∈ P) :
    (p * t)⁻¹ * (t * p) ∈ zpowers u₀ ↔ p ∈ nsub t u P := by
  have h := C.secTwo
  have hform : (p * t)⁻¹ * (t * p) = t * (p⁻¹ * t * p) := by
    simp only [mul_inv_rev, h.t_inv, mul_assoc]
  rw [hform, mem_nsub_iff C hp]
  constructor
  · intro hmem
    obtain ⟨n, hn⟩ : ∃ n : ℕ, u₀ ^ n = t * (p⁻¹ * t * p) := mem_powers_iff_mem_zpowers.mpr hmem
    have hs : p⁻¹ * t * p = t * u₀ ^ n := by
      calc p⁻¹ * t * p = (t * t) * (p⁻¹ * t * p) := by rw [h.t_mul_t, one_mul]
        _ = t * (t * (p⁻¹ * t * p)) := mul_assoc _ _ _
        _ = t * u₀ ^ n := by rw [hn]
    have hss : (p⁻¹ * t * p) * (p⁻¹ * t * p) = 1 := by
      calc (p⁻¹ * t * p) * (p⁻¹ * t * p) = p⁻¹ * (t * t) * p := by group
        _ = 1 := by rw [h.t_mul_t]; group
    have hpow : u₀ ^ n * u₀ ^ n = 1 := by
      have e : (t * u₀ ^ n) * (t * u₀ ^ n) = (t * t) * (u₀ ^ n * u₀ ^ n) := by
        calc (t * u₀ ^ n) * (t * u₀ ^ n) = t * (u₀ ^ n * t) * u₀ ^ n := by group
          _ = t * (t * u₀ ^ n) * u₀ ^ n := by rw [← t_mul_pow_u₀ C n]
          _ = (t * t) * (u₀ ^ n * u₀ ^ n) := by group
      rw [hs, e, h.t_mul_t, one_mul] at hss
      exact hss
    have hdvd : 4 ∣ n + n := by
      have := orderOf_dvd_of_pow_eq_one (show u₀ ^ (n + n) = 1 by rw [pow_add]; exact hpow)
      rwa [C.u₀_order] at this
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have hnm : u₀ ^ (2 * m) = (u ^ 2) ^ m := by rw [pow_mul, C.u₀_sq]
    rcases h.z_pow_cases m with h1 | h1
    · left
      rw [hs, hnm, h1, mul_one]
    · right
      rw [hs, hnm, h1]
  · rintro (h1 | h1)
    · rw [h1, h.t_mul_t]
      exact one_mem _
    · rw [h1, ← mul_assoc, h.t_mul_t, one_mul, ← C.u₀_sq]
      exact pow_mem (mem_zpowers u₀) 2

theorem mk_mem_centralizer_iff (C : SixAW t u P V v u₀)
    [((zpowers u₀).subgroupOf P).Normal] {t₁ : P} (ht₁ : (t₁ : G) = t) (p : P) :
    (QuotientGroup.mk p : P ⧸ (zpowers u₀).subgroupOf P) ∈
      centralizer ({(QuotientGroup.mk t₁ : P ⧸ (zpowers u₀).subgroupOf P)} :
        Set (P ⧸ (zpowers u₀).subgroupOf P)) ↔ (p : G) ∈ nsub t u P := by
  rw [mem_centralizer_singleton_iff, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    QuotientGroup.eq, mem_subgroupOf]
  have e : (((p * t₁)⁻¹ * (t₁ * p) : P) : G) = (p * t)⁻¹ * (t * p) := by
    simp [ht₁]
  rw [e]
  exact comm_mem_zpowers_iff C p.2

theorem card_centralizer (C : SixAW t u P V v u₀)
    [((zpowers u₀).subgroupOf P).Normal] {t₁ : P} (ht₁ : (t₁ : G) = t) :
    Nat.card (centralizer ({(QuotientGroup.mk t₁ : P ⧸ (zpowers u₀).subgroupOf P)} :
      Set (P ⧸ (zpowers u₀).subgroupOf P))) = 4 := by
  set φ := QuotientGroup.mk' ((zpowers u₀).subgroupOf P) with hφ
  set Z := centralizer ({(QuotientGroup.mk t₁ : P ⧸ (zpowers u₀).subgroupOf P)} :
    Set (P ⧸ (zpowers u₀).subgroupOf P))
  have hNP : nsub t u P ≤ P := inf_le_left
  have hcomap : Z.comap φ = (nsub t u P).subgroupOf P := by
    ext p
    simp only [mem_comap, mem_subgroupOf, hφ, QuotientGroup.mk'_apply]
    exact mk_mem_centralizer_iff C ht₁ p
  have h1 : Nat.card Z = φ.ker.relIndex (Z.comap φ) := by
    rw [relIndex_ker, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  rw [h1, hcomap, hφ, QuotientGroup.ker_mk', relIndex_subgroupOf hNP]
  exact relIndex_zpowers_nsub C

theorem sq_mem_zpowers (C : SixAW t u P V v u₀) {p : G} (hp : p ∈ nsub t u P) :
    p ^ 2 ∈ zpowers u₀ := by
  obtain ⟨a, b, c, rfl⟩ := C.N_nf hp
  rw [C.nrel.nf_sq a b c]
  exact pow_mem (mem_zpowers u₀) _

end CFSG.LocalAnalysis.EvenBN.Tits.I21.Quot

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open

theorem quot_shape {G : Type} [Group G] [Finite G] {t u : G} {P V : Subgroup G} {v u₀ y₀ : G}
    (C : SixAY t u P V v u₀ y₀)
    (hU : ∀ p ∈ P, ∀ w ∈ zpowers u₀, p * w * p⁻¹ ∈ zpowers u₀) :
    ∃ (_ : ((zpowers u₀).subgroupOf P).Normal),
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty ((P ⧸ (zpowers u₀).subgroupOf P) ≃* DihedralGroup (2 ^ m))) ∨
        ∃ k : ℕ, 4 ≤ k ∧ Nonempty ((P ⧸ (zpowers u₀).subgroupOf P) ≃* SemidihedralGroup k) := by
  have hle : zpowers u₀ ≤ P := zpowers_le.mpr C.u₀_mem_P
  have hN : ((zpowers u₀).subgroupOf P).Normal :=
    (normal_subgroupOf_iff hle).mpr fun w p hw hp => hU p hp w hw
  refine ⟨hN, ?_⟩
  have hP2 : IsPGroup 2 (P ⧸ (zpowers u₀).subgroupOf P) := C.pgroup.to_quotient _
  have htP : t ∈ P := C.R_le SecTwoHyp.t_mem_R
  set t' : P ⧸ (zpowers u₀).subgroupOf P := QuotientGroup.mk (⟨t, htP⟩ : P)
  have hcard : Nat.card (centralizer ({t'} : Set (P ⧸ (zpowers u₀).subgroupOf P))) = 4 :=
    I21.Quot.card_centralizer C.toSixAW (t₁ := ⟨t, htP⟩) rfl
  have hexp : ∀ x ∈ centralizer ({t'} : Set (P ⧸ (zpowers u₀).subgroupOf P)), x ^ 2 = 1 := by
    intro x hx
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    have hpN := (I21.Quot.mk_mem_centralizer_iff C.toSixAW (t₁ := ⟨t, htP⟩) rfl p).mp hx
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact I21.Quot.sq_mem_zpowers C.toSixAW hpN
  rcases CFSG.ComponentClassification.AschbacherToolkit.suzuki_two_group hP2 hcard hexp with
    ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact Or.inl ⟨n - 1, by omega, ⟨e⟩⟩
  · exact Or.inr ⟨n, hn, ⟨e⟩⟩

end CFSG.LocalAnalysis.EvenBN.Tits
