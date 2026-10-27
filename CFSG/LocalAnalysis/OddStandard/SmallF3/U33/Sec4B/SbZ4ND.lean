module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4ST3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Pow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17CosB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cnt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma comm_of_commutator_eq_one {a b : G} (h : a * b * a⁻¹ * b⁻¹ = 1) : a * b = b * a := by
  have h1 : a * b * a⁻¹ = b := by
    calc a * b * a⁻¹ = a * b * a⁻¹ * b⁻¹ * b := by group
      _ = 1 * b := by rw [h]
      _ = b := by group
  calc a * b = a * b * a⁻¹ * a := by group
    _ = b * a := by rw [h1]

private lemma inv_comm {a b : G} (h : a * b = b * a) : a⁻¹ * b = b * a⁻¹ := by
  have h2 : b * a⁻¹ = a⁻¹ * b := by
    calc b * a⁻¹ = a⁻¹ * (a * b) * a⁻¹ := by group
      _ = a⁻¹ * (b * a) * a⁻¹ := by rw [h]
      _ = a⁻¹ * b := by group
  exact h2.symm

private lemma conj_mul_comm {a b c : G} (hb : b * c = c * b) (ha : a * c = c * a) :
    (a * b * a⁻¹) * c = c * (a * b * a⁻¹) := by
  have ha' : a⁻¹ * c = c * a⁻¹ := inv_comm ha
  calc (a * b * a⁻¹) * c = a * (b * (a⁻¹ * c)) := by group
    _ = a * (b * (c * a⁻¹)) := by rw [ha']
    _ = a * (b * c) * a⁻¹ := by group
    _ = a * (c * b) * a⁻¹ := by rw [hb]
    _ = (a * c) * b * a⁻¹ := by group
    _ = (c * a) * b * a⁻¹ := by rw [ha]
    _ = c * (a * b * a⁻¹) := by group

namespace Ctx4Z

variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
include hz

theorem rho_cent_ctxWN :
    ∀ w ∈ ctxWN t tau x₁ x₂ rho, rho * w * rho⁻¹ = w → w = 1 := by
  intro w hw hfix
  let F : Subgroup G := ctxWN t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G)
  let P0 : Subgroup G := closure ({t, tau} : Set G)
  have hF2 : IsPGroup 2 F := IsPGroup.to_le hz.isPGroup_ctxWN inf_le_left
  have hP02 : IsPGroup 2 P0 := hz.nGood.isPGroup_P0
  have hP0norm : P0 ≤ Subgroup.normalizer (F : Set G) := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with hg | hg
    · rw [hg]
      apply Subgroup.mem_normalizer_fintype
      intro n hn
      refine Subgroup.mem_inf.mpr ⟨hz.t_conj_ctxWN hn.1, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact conj_mul_comm (Subgroup.mem_centralizer_singleton_iff.mp hn.2) hz.rho_comm_t.symm
    · rw [hg]
      apply Subgroup.mem_normalizer_fintype
      intro n hn
      refine Subgroup.mem_inf.mpr ⟨hz.tau_conj_ctxWN hn.1, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact conj_mul_comm (Subgroup.mem_centralizer_singleton_iff.mp hn.2) hz.rho_comm_tau.symm
  have hsup2 := IsPGroup.to_sup_of_normal_left' hF2 hP02 hP0norm
  have hsup_le : F ⊔ P0 ≤ ctxNQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) := by
    refine sup_le (fun x hx => Subgroup.mem_inf.mpr ⟨?_, hx.2⟩) hz.nGood.P0_le
    exact Subgroup.centralizer_le_normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G)
      (ctxWN_le_ctxCQ t tau x₁ x₂ rho hx.1)
  have hEq : F ⊔ P0 = P0 :=
    S4A.eq_of_isPGroup_of_odd_relIndex le_sup_right hsup_le hsup2 hz.tt_sylow.2.2
  have hFleP0 : F ≤ P0 := by rw [← hEq]; exact le_sup_left
  have hwF : w ∈ F := by
    refine Subgroup.mem_inf.mpr ⟨hw, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : rho * w = w * rho := by
      calc rho * w = (rho * w * rho⁻¹) * rho := by group
        _ = w * rho := by rw [hfix]
    exact h1.symm
  exact hz.P0_inf_ctxCQ w (hFleP0 hwF) (ctxWN_le_ctxCQ t tau x₁ x₂ rho hw)

end Ctx4Z

namespace ZNW

variable (hw : ZNW t L S x₁ x₂ lam rho tau)
include hw

theorem relIndex_eq_four :
    (ctxQ t tau x₁ x₂ rho).relIndex (ctxWN t tau x₁ x₂ rho) = 4 ∧
      Nat.card (ctxWN t tau x₁ x₂ rho) = 256 := by
  have hmod : (ctxQ t tau x₁ x₂ rho).relIndex (ctxWN t tau x₁ x₂ rho) % 3 = 1 :=
    S4B.relIndex_mod_three hw.toCtx4Z.Q_le_ctxWN hw.toCtx4Z.toCtx4Q.rho_pow_three
      (fun x hx => hw.toCtx4Z.rho_conj_ctxWN hx)
      (fun x hx => hw.normal_Q.2 rho hw.rho_mem_M x hx)
      (fun x hx hfx => hw.toCtx4Z.rho_cent_ctxWN x hx hfx)
      (by rw [hw.card_Q]; norm_num)
  exact S4B.relIndex_eq_four_of_le hw.toCtx4Z.isPGroup_ctxWN hw.Q_lt_W
    (by rw [hw.card_Q]; norm_num) hw.toCtx4Z.card_ctxWN_le hmod

theorem card_ctxWN : Nat.card (ctxWN t tau x₁ x₂ rho) = 256 :=
  hw.relIndex_eq_four.2

theorem fpfSetting : S4B.FpfSetting (ctxWN t tau x₁ x₂ rho) (ctxQ t tau x₁ x₂ rho) rho :=
  { QP := hw.toCtx4Z.Q_le_ctxWN
    cen := fun p hp q hq => ctxCQ_comm (ctxWN_le_ctxCQ t tau x₁ x₂ rho hp) hq
    rho3 := hw.toCtx4Z.toCtx4Q.rho_pow_three
    rhoP := fun x hx => hw.toCtx4Z.rho_conj_ctxWN hx
    rhoQ := fun x hx => hw.normal_Q.2 rho hw.rho_mem_M x hx
    fix := fun x hx hfx => hw.toCtx4Z.rho_cent_ctxWN x hx hfx
    cardQ := by rw [hw.card_Q]; norm_num
    idx := hw.relIndex_eq_four.1 }

theorem W_comm : ∀ a ∈ ctxWN t tau x₁ x₂ rho, ∀ b ∈ ctxWN t tau x₁ x₂ rho, a * b = b * a :=
  hw.fpfSetting.comm

theorem W_sq_mem_Q : ∀ x ∈ ctxWN t tau x₁ x₂ rho, x ^ 2 ∈ ctxQ t tau x₁ x₂ rho :=
  hw.fpfSetting.sq_mem

theorem W_pow_four_mem_V : ∀ x ∈ ctxWN t tau x₁ x₂ rho, x ^ 4 ∈ fourGrp x₁ x₂ := by
  intro x hx
  have h := hw.toCtx4Z.nPre.sq_mem_V (hw.W_sq_mem_Q x hx)
  rw [show x ^ 4 = (x ^ 2) ^ 2 by group]
  exact h

private theorem psi_exists :
    Nat.card (ctxQm t tau x₁ x₂ rho) = 16 ∧
      ∃ ψ : ↥(ctxWN t tau x₁ x₂ rho) →* ↥(ctxQm t tau x₁ x₂ rho),
        ψ.range = ⊤ ∧ ∀ w, (ψ w : G) = (w : G) * t * (w : G)⁻¹ * t⁻¹ := by
  obtain ⟨φ, hφ⟩ := Ctx4Z.exists_phiW hw.toCtx4Z
  have hmem_iff : ∀ w : ↥(ctxWN t tau x₁ x₂ rho),
      w ∈ φ.ker ↔ (w : G) ∈ baseGrp x₁ x₂ := by
    intro w
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : (w : G) * t * (w : G)⁻¹ * t⁻¹ = 1 := by
        have hh := congrArg (fun z : ↥(ctxQ t tau x₁ x₂ rho) => (z : G)) h
        simpa [hφ w] using hh
      have hwt : (w : G) * t = t * (w : G) := comm_of_commutator_eq_one h1
      have h2 : (w : G) ∈ ctxWN t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
        ⟨w.2, Subgroup.mem_centralizer_singleton_iff.mpr hwt⟩
      rwa [hw.toCtx4Z.ctxWN_inf_centralizer_t] at h2
    · intro hb
      have h2 : (w : G) ∈ ctxWN t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := by
        rw [hw.toCtx4Z.ctxWN_inf_centralizer_t]
        exact hb
      have hwt : (w : G) * t = t * (w : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp h2.2
      apply Subtype.ext
      rw [hφ w]
      change (w : G) * t * (w : G)⁻¹ * t⁻¹ = 1
      rw [hwt]
      group
  have hker_eq : φ.ker =
      (baseGrp x₁ x₂).subgroupOf (ctxWN t tau x₁ x₂ rho) := by
    ext w
    rw [Subgroup.mem_subgroupOf]
    exact hmem_iff w
  have hker_card : Nat.card φ.ker = 16 := by
    rw [hker_eq]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hw.toCtx4Z.base_le_ctxWN).toEquiv]
    exact hw.toCtx4Z.nPre.card_B
  have hrange_card : Nat.card φ.range = 16 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hker_card, hw.card_ctxWN] at h
    omega
  let ψ : ↥(ctxWN t tau x₁ x₂ rho) →* ↥(ctxQm t tau x₁ x₂ rho) :=
    { toFun := fun w => ⟨(φ w : G), by rw [hφ w]; exact hw.toCtx4Z.comm_W_t_mem_Qm w.2⟩
      map_one' := Subtype.ext (by
        show (φ 1 : G) = ((1 : ↥(ctxQm t tau x₁ x₂ rho)) : G)
        simp)
      map_mul' := fun a b => Subtype.ext (by
        show (φ (a * b) : G) = (φ a : G) * (φ b : G)
        exact congrArg Subtype.val (map_mul φ a b)) }
  have hψ : ∀ w : ↥(ctxWN t tau x₁ x₂ rho),
      (ψ w : G) = (w : G) * t * (w : G)⁻¹ * t⁻¹ := by
    intro w
    show (φ w : G) = (w : G) * t * (w : G)⁻¹ * t⁻¹
    exact hφ w
  have hpsi_mem_iff : ∀ w : ↥(ctxWN t tau x₁ x₂ rho),
      w ∈ ψ.ker ↔ (w : G) ∈ baseGrp x₁ x₂ := by
    intro w
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : (w : G) * t * (w : G)⁻¹ * t⁻¹ = 1 := by
        have hh := congrArg (fun z : ↥(ctxQm t tau x₁ x₂ rho) => (z : G)) h
        rw [hψ w] at hh
        simpa using hh
      have hwt : (w : G) * t = t * (w : G) := comm_of_commutator_eq_one h1
      have h2 : (w : G) ∈ ctxWN t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
        ⟨w.2, Subgroup.mem_centralizer_singleton_iff.mpr hwt⟩
      rwa [hw.toCtx4Z.ctxWN_inf_centralizer_t] at h2
    · intro hb
      have h2 : (w : G) ∈ ctxWN t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := by
        rw [hw.toCtx4Z.ctxWN_inf_centralizer_t]
        exact hb
      have hwt : (w : G) * t = t * (w : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp h2.2
      apply Subtype.ext
      rw [hψ w]
      change (w : G) * t * (w : G)⁻¹ * t⁻¹ = 1
      rw [hwt]
      group
  have hpsi_ker : Nat.card ψ.ker = 16 := by
    have hker_eq' : ψ.ker =
        (baseGrp x₁ x₂).subgroupOf (ctxWN t tau x₁ x₂ rho) := by
      ext w
      rw [Subgroup.mem_subgroupOf]
      exact hpsi_mem_iff w
    rw [hker_eq']
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hw.toCtx4Z.base_le_ctxWN).toEquiv]
    exact hw.toCtx4Z.nPre.card_B
  have hpsi_range_card : Nat.card ψ.range = 16 := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hpsi_ker, hw.card_ctxWN] at h
    omega
  have hQm_card : Nat.card (ctxQm t tau x₁ x₂ rho) = 16 := by
    refine le_antisymm hw.toCtx4Z.card_ctxQm_le ?_
    calc 16 = Nat.card ψ.range := hpsi_range_card.symm
      _ ≤ Nat.card (ctxQm t tau x₁ x₂ rho) := Subgroup.card_le_card_group ψ.range
  have htop : ψ.range = ⊤ :=
    Subgroup.eq_top_of_card_eq ψ.range (by rw [hpsi_range_card, hQm_card])
  exact ⟨hQm_card, ψ, htop, hψ⟩

theorem phi_surj : ∀ c ∈ ctxQm t tau x₁ x₂ rho,
    ∃ w ∈ ctxWN t tau x₁ x₂ rho, w * t * w⁻¹ * t⁻¹ = c := by
  obtain ⟨-, ψ, htop, hψ⟩ := psi_exists hw
  intro c hc
  have hmem : (⟨c, hc⟩ : ↥(ctxQm t tau x₁ x₂ rho)) ∈ ψ.range := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨w, hw_eq⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨(w : G), w.2, ?_⟩
  have h := congrArg (fun z : ↥(ctxQm t tau x₁ x₂ rho) => (z : G)) hw_eq
  rw [hψ w] at h
  simpa using h

end ZNW

end CFSG.OddStandard.SmallF3.HarrisU33
