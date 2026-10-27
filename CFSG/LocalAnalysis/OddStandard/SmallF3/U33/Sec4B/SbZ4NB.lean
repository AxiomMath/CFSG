module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Prod

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma card_sup_le_mul_of_comm {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K := by
  have hnorm : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H := by
    intro k hk h hh
    rw [← hcomm h hh k hk, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  have hsurj : Function.Surjective
      (fun p : ↥H × ↥K =>
        (⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(H ⊔ K))) := by
    intro x
    obtain ⟨h, hh, k, hk, hx⟩ :=
      (S4B.mem_sup_iff_of_normalizes (H := H) (K := K) hnorm).mp x.2
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hx.symm⟩
  calc Nat.card ↥(H ⊔ K) ≤ Nat.card (↥H × ↥K) :=
        Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card H * Nat.card K := Nat.card_prod (↥H) (↥K)

private lemma card_closure_pair_le {a b : G} (hab : a * b = b * a)
    (ha4 : a ^ 4 = 1) (hb4 : b ^ 4 = 1) :
    Nat.card ↥(Subgroup.closure ({a, b} : Set G)) ≤ 16 := by
  have hcomm : ∀ h ∈ Subgroup.zpowers a, ∀ k ∈ Subgroup.zpowers b, h * k = k * h := by
    intro h hh k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact (Commute.zpow_zpow ((commute_iff_eq a b).mpr hab) m n).eq
  have hcl : Subgroup.closure ({a, b} : Set G) =
      Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    rw [← Set.singleton_union, Subgroup.closure_union,
      Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
  rw [hcl]
  have hza : Nat.card ↥(Subgroup.zpowers a) ≤ 4 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) ha4
  have hzb : Nat.card ↥(Subgroup.zpowers b) ≤ 4 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) hb4
  calc Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b)
      ≤ Nat.card ↥(Subgroup.zpowers a) * Nat.card ↥(Subgroup.zpowers b) :=
        card_sup_le_mul_of_comm hcomm
    _ ≤ 4 * 4 := Nat.mul_le_mul hza hzb
    _ = 16 := by norm_num

namespace Ctx4Z

variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
include hz

theorem comm_W_t_mul {w₁ w₂ : G} (h₁ : w₁ ∈ ctxWN t tau x₁ x₂ rho)
    (h₂ : w₂ ∈ ctxWN t tau x₁ x₂ rho) :
    (w₁ * w₂) * t * (w₁ * w₂)⁻¹ * t⁻¹ =
      (w₁ * t * w₁⁻¹ * t⁻¹) * (w₂ * t * w₂⁻¹ * t⁻¹) := by
  obtain ⟨hw₁C, hc₁⟩ := hz.mem_ctxWN_iff.mp h₁
  obtain ⟨_, hc₂⟩ := hz.mem_ctxWN_iff.mp h₂
  have hc₂' : (w₂ * t * w₂⁻¹ * t⁻¹) * t = w₂ * t * w₂⁻¹ := by group
  have hw₁c₂ : w₁ * (w₂ * t * w₂⁻¹ * t⁻¹) * w₁⁻¹ = w₂ * t * w₂⁻¹ * t⁻¹ := by
    rw [ctxCQ_comm hw₁C hc₂]
    group
  calc (w₁ * w₂) * t * (w₁ * w₂)⁻¹ * t⁻¹
      = w₁ * (w₂ * t * w₂⁻¹) * w₁⁻¹ * t⁻¹ := by group
    _ = w₁ * ((w₂ * t * w₂⁻¹ * t⁻¹) * t) * w₁⁻¹ * t⁻¹ := by rw [hc₂']
    _ = (w₁ * (w₂ * t * w₂⁻¹ * t⁻¹) * w₁⁻¹) * (w₁ * t * w₁⁻¹ * t⁻¹) := by group
    _ = (w₂ * t * w₂⁻¹ * t⁻¹) * (w₁ * t * w₁⁻¹ * t⁻¹) := by rw [hw₁c₂]
    _ = (w₁ * t * w₁⁻¹ * t⁻¹) * (w₂ * t * w₂⁻¹ * t⁻¹) :=
          (hz.Q_comm _ hc₁ _ hc₂).symm

theorem comm_W_t_mem_Qm {w : G} (hw : w ∈ ctxWN t tau x₁ x₂ rho) :
    w * t * w⁻¹ * t⁻¹ ∈ ctxQm t tau x₁ x₂ rho := by
  obtain ⟨_, hcQ⟩ := hz.mem_ctxWN_iff.mp hw
  refine ⟨hcQ, (hz.nGood.mem_cent_ttau_iff hz.tau_inv_Q hcQ).mpr ?_⟩
  have h1 : (w * t * w⁻¹ * t⁻¹) * (t * (w * t * w⁻¹ * t⁻¹) * t) = 1 := by
    rw [show (w * t * w⁻¹ * t⁻¹) * (t * (w * t * w⁻¹ * t⁻¹) * t) =
      (w * t * w⁻¹) * (w * t * w⁻¹) by group]
    have h2 : (w * t * w⁻¹) * (w * t * w⁻¹) = w * (t * t) * w⁻¹ := by group
    rw [h2, hz.t_mul_self, mul_one, mul_inv_cancel]
  have h2 : (w * t * w⁻¹ * t⁻¹)⁻¹ = t * (w * t * w⁻¹ * t⁻¹) * t :=
    inv_eq_of_mul_eq_one_right h1
  rw [h2, inv_eq_of_mul_eq_one_right hz.t_mul_self]

theorem card_ctxQm_le : Nat.card (ctxQm t tau x₁ x₂ rho) ≤ 16 := by
  obtain ⟨V', v₁, v₂, hV⟩ := hz.data_V
  obtain ⟨hVea, _, hVQ, _, _, _, hv₁, hv₂, _, _, _, _, _, _, hQm⟩ := hV
  rw [show ctxQm t tau x₁ x₂ rho = closure {x₁ * v₁, x₂ * v₂} from hQm]
  have hv₁Q : v₁ ∈ ctxQ t tau x₁ x₂ rho := by
    rw [hVQ]; exact Subgroup.mem_sup_right hv₁
  have hv₂Q : v₂ ∈ ctxQ t tau x₁ x₂ rho := by
    rw [hVQ]; exact Subgroup.mem_sup_right hv₂
  have haQ : x₁ * v₁ ∈ ctxQ t tau x₁ x₂ rho := mul_mem hz.x₁_mem_Q hv₁Q
  have hbQ : x₂ * v₂ ∈ ctxQ t tau x₁ x₂ rho := mul_mem hz.x₂_mem_Q hv₂Q
  have hv₁sq : v₁ * v₁ = 1 := by simpa [pow_two] using hVea.2 v₁ hv₁
  have hv₂sq : v₂ * v₂ = 1 := by simpa [pow_two] using hVea.2 v₂ hv₂
  have ha4 : (x₁ * v₁) ^ 4 = 1 := by
    rw [Commute.mul_pow ((commute_iff_eq x₁ v₁).mpr (hz.Q_comm x₁ hz.x₁_mem_Q v₁ hv₁Q)) 4,
      hz.x₁_pow_four]
    have hv : v₁ ^ 4 = 1 := by
      calc v₁ ^ 4 = v₁ ^ 2 * v₁ ^ 2 := by
            rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
        _ = (v₁ * v₁) * (v₁ * v₁) := by rw [pow_two]
        _ = 1 := by rw [hv₁sq, one_mul]
    rw [hv, mul_one]
  have hb4 : (x₂ * v₂) ^ 4 = 1 := by
    rw [Commute.mul_pow ((commute_iff_eq x₂ v₂).mpr (hz.Q_comm x₂ hz.x₂_mem_Q v₂ hv₂Q)) 4,
      hz.x₂_pow_four]
    have hv : v₂ ^ 4 = 1 := by
      calc v₂ ^ 4 = v₂ ^ 2 * v₂ ^ 2 := by
            rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
        _ = (v₂ * v₂) * (v₂ * v₂) := by rw [pow_two]
        _ = 1 := by rw [hv₂sq, one_mul]
    rw [hv, mul_one]
  exact card_closure_pair_le (hz.Q_comm _ haQ _ hbQ) ha4 hb4

theorem exists_phiW :
    ∃ φ : ↥(ctxWN t tau x₁ x₂ rho) →* ↥(ctxQ t tau x₁ x₂ rho),
      ∀ w : ↥(ctxWN t tau x₁ x₂ rho), (φ w : G) = (w : G) * t * (w : G)⁻¹ * t⁻¹ := by
  refine ⟨MonoidHom.mk' (fun w : ↥(ctxWN t tau x₁ x₂ rho) =>
      ⟨(w : G) * t * (w : G)⁻¹ * t⁻¹, (hz.mem_ctxWN_iff.mp w.2).2⟩) ?_, ?_⟩
  · intro a b
    apply Subtype.ext
    simpa using hz.comm_W_t_mul a.2 b.2
  · intro w
    rfl

private lemma card_ker_phi (φ : ↥(ctxWN t tau x₁ x₂ rho) →* ↥(ctxQ t tau x₁ x₂ rho))
    (hφ : ∀ w : ↥(ctxWN t tau x₁ x₂ rho),
      (φ w : G) = (w : G) * t * (w : G)⁻¹ * t⁻¹) :
    Nat.card φ.ker = 16 := by
  have hker : φ.ker = (baseGrp x₁ x₂).subgroupOf (ctxWN t tau x₁ x₂ rho) := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : (w : G) * t * (w : G)⁻¹ * t⁻¹ = 1 := by
        have hh := congrArg (fun x : ↥(ctxQ t tau x₁ x₂ rho) => (x : G)) h
        rw [hφ w] at hh
        simpa using hh
      have h2 : (w : G) * t = t * (w : G) := by
        have h3 : (w : G) * t * (w : G)⁻¹ = t := by
          have := mul_eq_one_iff_eq_inv.mp h1
          simpa using this
        calc (w : G) * t = (w : G) * t * (w : G)⁻¹ * (w : G) := by group
          _ = t * (w : G) := by rw [h3]
      have hmem : (w : G) ∈ ctxWN t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
        ⟨w.2, mem_centralizer_iff.mpr (fun g hg => by
          rw [Set.mem_singleton_iff.mp hg]; exact h2.symm)⟩
      rwa [hz.ctxWN_inf_centralizer_t] at hmem
    · intro h
      have hb : (w : G) ∈ baseGrp x₁ x₂ := h
      apply Subtype.ext
      rw [hφ w]
      change (w : G) * t * (w : G)⁻¹ * t⁻¹ = (1 : G)
      rw [hz.nPre.B_comm_t (w : G) hb]
      group
  rw [hker]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hz.base_le_ctxWN).toEquiv).trans
    hz.nPre.card_B

private lemma card_range_le (φ : ↥(ctxWN t tau x₁ x₂ rho) →* ↥(ctxQ t tau x₁ x₂ rho))
    (hφ : ∀ w : ↥(ctxWN t tau x₁ x₂ rho),
      (φ w : G) = (w : G) * t * (w : G)⁻¹ * t⁻¹) :
    Nat.card φ.range ≤ 16 := by
  have himage : ∀ x : ↥φ.range, ((x : ↥(ctxQ t tau x₁ x₂ rho)) : G) ∈
      ctxQm t tau x₁ x₂ rho := by
    intro x
    obtain ⟨w, hw⟩ := (MonoidHom.mem_range (f := φ)).mp x.2
    have hwW : (w : G) ∈ ctxWN t tau x₁ x₂ rho := w.2
    have hxw : ((x : ↥(ctxQ t tau x₁ x₂ rho)) : G) =
        (w : G) * t * (w : G)⁻¹ * t⁻¹ := by
      rw [← hw, hφ w]
    rw [hxw]
    exact hz.comm_W_t_mem_Qm hwW
  let f : ↥φ.range → ↥(ctxQm t tau x₁ x₂ rho) :=
    fun x => ⟨((x : ↥(ctxQ t tau x₁ x₂ rho)) : G), himage x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(ctxQm t tau x₁ x₂ rho) => (z : G)) hxy
  exact (Nat.card_le_card_of_injective f hf).trans hz.card_ctxQm_le

theorem isPGroup_ctxWN : IsPGroup 2 (ctxWN t tau x₁ x₂ rho) := by
  obtain ⟨φ, hφ⟩ := hz.exists_phiW
  have hcard := Subgroup.card_ker_mul_card_range φ
  have hker : Nat.card φ.ker = 16 := hz.card_ker_phi φ hφ
  have hrange_dvd : Nat.card φ.range ∣ 2 ^ 6 := by
    rw [← hz.card_Q]
    exact Subgroup.card_subgroup_dvd_card φ.range
  refine IsPGroup.of_card_dvd_pow (n := 10) ?_
  rw [← hcard, hker]
  calc 16 * Nat.card φ.range ∣ 16 * 2 ^ 6 := Nat.mul_dvd_mul_left 16 hrange_dvd
    _ = 2 ^ 10 := by norm_num

theorem card_ctxWN_le : Nat.card (ctxWN t tau x₁ x₂ rho) ≤ 256 := by
  obtain ⟨φ, hφ⟩ := hz.exists_phiW
  have hcard := Subgroup.card_ker_mul_card_range φ
  have hker : Nat.card φ.ker = 16 := hz.card_ker_phi φ hφ
  have hrange : Nat.card φ.range ≤ 16 := hz.card_range_le φ hφ
  rw [← hcard, hker]
  calc 16 * Nat.card φ.range ≤ 16 * 16 := Nat.mul_le_mul_left 16 hrange
    _ = 256 := by norm_num

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
