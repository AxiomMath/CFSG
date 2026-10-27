module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuPf3B
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A03

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu

namespace Pf3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Asc77.Star3T CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.Q3NL

section Alg

variable {G : Type} [Group G]

theorem no_central_comm {W : Subgroup G} (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {r t a b : G}
    (hrN : r ∈ Subgroup.normalizer (W : Set G)) (htN : t ∈ Subgroup.normalizer (W : Set G))
    (ha : a ∈ W) (hb : b ∈ W) (ha4 : orderOf a = 4) (hb4 : b ^ 4 = 1)
    (hra : r * a * r⁻¹ ∈ Subgroup.zpowers a) (h1 : t * a * t⁻¹ = a * b)
    (h2 : r * b * r⁻¹ = b * a)
    (hg : ∀ w ∈ W, (r * t * r⁻¹ * t⁻¹) * w = w * (r * t * r⁻¹ * t⁻¹)) : False := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hra
  have hra' : r * a * r⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hrN a).mp ha
  have hb₀ : t * (r * a * r⁻¹) * t⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp htN _).mp hra'
  have hE : r * (t * a * t⁻¹) * r⁻¹ = t * (r * a * r⁻¹) * t⁻¹ := by
    have := hg _ hb₀
    calc r * (t * a * t⁻¹) * r⁻¹
        = (r * t * r⁻¹ * t⁻¹) * (t * (r * a * r⁻¹) * t⁻¹) * (r * t * r⁻¹ * t⁻¹)⁻¹ := by group
      _ = t * (r * a * r⁻¹) * t⁻¹ := by rw [this]; group
  have hab : a * b = b * a := hW a ha b hb
  have hL : r * (t * a * t⁻¹) * r⁻¹ = a ^ k * (b * a) := by
    rw [h1, show r * (a * b) * r⁻¹ = (r * a * r⁻¹) * (r * b * r⁻¹) by group, ← hk, h2]
  have hR : t * (r * a * r⁻¹) * t⁻¹ = a ^ k * b ^ k := by
    rw [← hk, show t * a ^ k * t⁻¹ = (t * a * t⁻¹) ^ k from (conj_zpow).symm, h1]
    exact (Commute.mul_zpow (show Commute a b from hab) k)
  have h3 : b * a = b ^ k := by
    have := hE
    rw [hL, hR] at this
    exact mul_left_cancel this
  have ha2 : a ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have ha4' : a ^ 4 = 1 := by rw [← ha4]; exact pow_orderOf_eq_one a
  have hpow4 : ∀ (x : G), x ^ 4 = 1 → ∀ m : ℤ, x ^ (4 * m) = 1 := by
    intro x hx m
    rw [zpow_mul]
    norm_num [hx]
  have hsq : (r * a * r⁻¹) ^ 2 ≠ 1 := by
    intro h
    apply ha2
    have h5 : (r * a * r⁻¹) ^ 2 = r * a ^ 2 * r⁻¹ := by
      rw [sq, sq]; group
    rw [h5] at h
    exact conj_eq_one_iff.mp h
  have hodd : ∃ m : ℤ, k = 2 * m + 1 := by
    rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
    · exfalso
      apply hsq
      rw [← hk, ← zpow_natCast, ← zpow_mul, hm]
      have := hpow4 a ha4' m
      rw [show (2 * m) * ((2 : ℕ) : ℤ) = 4 * m by push_cast; ring]
      exact this
    · exact ⟨m, hm⟩
  obtain ⟨m, hm⟩ := hodd
  have h4 : a = b ^ (2 * m) := by
    calc a = b⁻¹ * (b * a) := by group
      _ = b⁻¹ * b ^ (2 * m + 1) := by rw [h3, hm]
      _ = b ^ (2 * m) := by rw [zpow_add_one]; group
  apply ha2
  rw [h4, ← zpow_natCast, ← zpow_mul]
  have := hpow4 b hb4 m
  rw [show (2 * m) * ((2 : ℕ) : ℤ) = 4 * m by push_cast; ring]
  exact this

end Alg


section Rep

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem card_inf_W_eq_four (ctx : Q3CL.Thompson.Ctx Ω W)
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2))
    (ρ : Rep Ω W) : Nat.card ↥(ρ.R ⊓ W) = 4 := by
  obtain ⟨e⟩ := hq ρ.K ρ.hK ρ.R ρ.hRK
  have h8 : Nat.card ↥ρ.R = 8 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have := (Q3CL.Thompson.inf_W_of_mem_D ctx.hΩ ctx.hW ρ.hR ρ.hK ρ.hRK).2.2.2.2
  omega

theorem not_commutes_secImg [hcl : Fact (Q3CL.ClassicalClause Ω)] (ctx : Q3CL.Thompson.Ctx Ω W)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2))
    {u : G} (hc2 : IsPGroup 2 (Subgroup.zpowers u)) (hu : u ∈ W) (ρ σ : Rep Ω W)
    (hρu : ρ.R ≤ Subgroup.centralizer ({u} : Set G)) (hσu : σ.R ≤ Subgroup.centralizer ({u} : Set G))
    (hnc : ρ.img * σ.img ≠ σ.img * ρ.img) :
    ¬ Commutes (secImg Ω u ρ.K) (secImg Ω u σ.K) := by
  intro hcomm
  have hne : ρ.K ≠ σ.K := fun h => hnc (by rw [Q3T6.Mu.ctx_img_eq_of_K_eq ctx ρ σ h])
  have hnot : σ.K ∉ omegaNbr Ω ρ.K := fun h => hnc (Q3T6.Mu.ctx_comm_of_omega ctx ρ σ h)
  have hρtq : ρ.K ∈ tqMembers3 Ω u :=
    ⟨ρ.hK, TwinADescent3.mem_tq_of_sylCent ctx.hΩ h2 ρ.hK ⟨ρ.R, ρ.hRK, hρu⟩⟩
  have hσtq : σ.K ∈ tqMembers3 Ω u :=
    ⟨σ.hK, TwinADescent3.mem_tq_of_sylCent ctx.hΩ h2 σ.hK ⟨σ.R, σ.hRK, hσu⟩⟩
  obtain ⟨a, ha⟩ := Q3T8.Asc77.Thompson.exists_zpowers_eq_inf_W ctx.hΩ ctx.hW ρ.hR
  obtain ⟨b, hb⟩ := Q3T8.Asc77.Thompson.exists_zpowers_eq_inf_W ctx.hΩ ctx.hW σ.hR
  obtain ⟨b', hb', rel1, rel2⟩ := ctx.rel_exact hne hnot ha hb
  have haW : a ∈ ρ.R ⊓ W := ha ▸ Subgroup.mem_zpowers a
  have hb'W : b' ∈ σ.R ⊓ W := hb ▸ hb' ▸ Subgroup.mem_zpowers b'
  have ha4 : orderOf a = 4 := by
    rw [← Nat.card_zpowers, ha]; exact card_inf_W_eq_four ctx hq ρ
  have hb'4 : b' ^ 4 = 1 := by
    have : orderOf b' = 4 := by
      rw [← Nat.card_zpowers, hb', hb]; exact card_inf_W_eq_four ctx hq σ
    rw [← this]; exact pow_orderOf_eq_one b'
  have hrN : ρ.r ∈ Subgroup.normalizer (W : Set G) := ρ.r_mem_normalizer
  have htN : σ.r ∈ Subgroup.normalizer (W : Set G) := σ.r_mem_normalizer
  have hra : ρ.r * a * ρ.r⁻¹ ∈ Subgroup.zpowers a := by
    rw [ha]
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ ρ.hr (haW.1)) (Subgroup.inv_mem _ ρ.hr),
      (Subgroup.mem_normalizer_iff.mp hrN a).mp haW.2⟩
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet ctx.hW
  have hWc : W ≤ Subgroup.centralizer ({u} : Set G) := fun w hw => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (ctx.comm_W u hu w hw).symm
  have hgN : ρ.r * σ.r * ρ.r⁻¹ * σ.r⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN htN) (Subgroup.inv_mem _ hrN))
      (Subgroup.inv_mem _ htN)
  have hρr : ρ.r ∈ TwinADescent.coreAt u ρ.K :=
    ((TwinADescent.isSylow2In_coreAt_iff hc2 hρtq.2).mpr ⟨ρ.hRK, hρu⟩).1 ρ.hr
  have hσr : σ.r ∈ TwinADescent.coreAt u σ.K :=
    ((TwinADescent.isSylow2In_coreAt_iff hc2 hσtq.2).mpr ⟨σ.hRK, hσu⟩).1 σ.hr
  have hgO := comm_mem_oddCoreOf_of_commutes hρtq hσtq hρr hσr hcomm
  have hg := centralizes_of_mem_oddCoreOf ctx.hΩ hc2 hW2 hWc hgN hgO
  exact no_central_comm ctx.comm_W hrN htN haW.2 hb'W.2 ha4 hb'4 hra rel1 rel2 hg

end Rep

end Pf3

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu
