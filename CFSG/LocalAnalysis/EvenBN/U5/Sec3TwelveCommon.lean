module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3TwelveBar
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3TwelvePD
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusNine
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedParts

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups commutatorElement

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec312_exists_S (hp : d.CaseHyp) :
    ∃ S : Subgroup G, IsSylowOf 2 S d.L₂ ∧ d.P ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL := hp.hyp.P_le_L₂ hp.gms
  have hP2 : IsPGroup 2 (d.P.subgroupOf d.L₂) := d.isPGroup_P.comap_subtype
  obtain ⟨Q, hQ⟩ := hP2.exists_le_sylow
  exact ⟨(Q : Subgroup d.L₂).map d.L₂.subtype, ⟨Q, rfl⟩, fun x hx => ⟨⟨x, hPL hx⟩, hQ hx, rfl⟩⟩

theorem sec312_centerIn_D (hp : d.CaseHyp) (k : d.Know10) :
    CFSG.centerIn d.D = d.F := by
  obtain ⟨S, hS, hP⟩ := sec312_exists_S hp
  exact (k.s9_2 S hS hP).2.2.2.1

theorem sec312_F_le_D (hp : d.CaseHyp) (k : d.Know10) : d.F ≤ d.D := by
  rw [← sec312_centerIn_D hp k]
  exact inf_le_left

theorem sec312_D_le_centralizer_F (hp : d.CaseHyp) (k : d.Know10) :
    d.D ≤ centralizer (d.F : Set G) := by
  rw [← sec312_centerIn_D hp k]
  intro x hx
  exact mem_centralizer_iff.2 fun z hz =>
    (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 x hx).symm

theorem sec312_sq_mem_F (hp : d.CaseHyp) (k : d.Know10) : ∀ x ∈ d.D, x * x ∈ d.F := by
  obtain ⟨S, hS, hP⟩ := sec312_exists_S hp
  exact (k.s9_2 S hS hP).2.2.2.2

theorem sec312_L₁_eq (k : d.Know10) : d.L₁ = d.D ⊔ d.M₁ := k.s9_3.1

theorem sec312_M₁_le_L₁ (k : d.Know10) : d.M₁ ≤ d.L₁ := by
  rw [sec312_L₁_eq k]
  exact le_sup_right

theorem sec312_L₁_le_N_D (hp : d.CaseHyp) : d.L₁ ≤ normalizer (d.D : Set G) :=
  hp.hyp.L₁_le_normalizer_D

theorem sec312_L₁_le_N_F (hp : d.CaseHyp) (k : d.Know10) :
    d.L₁ ≤ normalizer (d.F : Set G) := by
  rw [← sec312_centerIn_D hp k]
  exact (sec312_L₁_le_N_D hp).trans (normalizer_le_normalizer_centerIn _)

theorem sec312_D_inf_M₁ (k : d.Know10) : d.D ⊓ d.M₁ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ d.D ⊓ centralizer (d.I₁ : Set G) :=
    Subgroup.mem_inf.2 ⟨hx.1, d.M₁_le_centralizer_I₁ hx.2⟩
  rw [k.s9e.centralizer_I₁] at h1
  exact h1

theorem sec312_card_D (k : d.Know10) : Nat.card d.D = (2 ^ f) ^ 16 := k.s9e.card_D

theorem sec312_card_F (hp : d.CaseHyp) : Nat.card d.F = (2 ^ f) ^ 8 :=
  hp.hyp.card_F hp.gms

theorem sec312_two_le (hp : d.CaseHyp) : 2 ≤ f := hp.hyp.two_le

section SLevel

variable (hp : d.CaseHyp) (k : d.Know10) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
  (hP : d.P ≤ S)
include hp k hS hP

theorem sec312_S_eq : S = d.E ⊔ d.D := (k.s9_1 S hS hP).1

theorem sec312_D_le_S : d.D ≤ S := by
  rw [sec312_S_eq hp k hS hP]
  exact le_sup_right

theorem sec312_F_le_S : d.F ≤ S := (sec312_F_le_D hp k).trans (sec312_D_le_S hp k hS hP)

theorem sec312_S_le_L₁ : S ≤ d.L₁ :=
  ((k.s10_2 S hS hP).2.2.2.2.2.2.1).le

theorem sec312_S_eq_D_sup_R : S = d.D ⊔ (S ⊓ d.M₁) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, c12⟩ := k.s10_1 S hS hP
  have h1 := c12.1
  rwa [(k.s10_2 S hS hP).1.1] at h1

theorem sec312_isSylowOf_R : IsSylowOf 2 (S ⊓ d.M₁) d.M₁ := (k.s10_2 S hS hP).1.2

theorem sec312_Q_eq : (d.E ⊓ d.D) ⊔ d.F = d.F ⊔ (S ⊓ centralizer (d.I₅ : Set G)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, c10, -, -⟩ := k.s10_1 S hS hP
  rw [sup_comm]
  exact c10

theorem sec312_Q_card : Nat.card ((d.E ⊓ d.D) ⊔ d.F : Subgroup G) = (2 ^ f) ^ 12 := by
  have hO := k.s10_o S hS hP
  have hFS := sec312_F_le_S hp k hS hP
  have hN : (S ⊓ centralizer (d.I₅ : Set G)) ≤ normalizer (d.F : Set G) :=
    inf_le_left.trans ((sec312_S_le_L₁ hp k hS hP).trans (sec312_L₁_le_N_F hp k))
  have hprod := Common.card_sup_mul_card_inf_eq (A := d.F)
    (B := S ⊓ centralizer (d.I₅ : Set G)) hN
  have hinf : d.F ⊓ (S ⊓ centralizer (d.I₅ : Set G)) = d.F ⊓ centralizer (d.I₅ : Set G) := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨a, _, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨a, hFS a, c⟩⟩
  rw [hinf, hO.cF₅, hO.c₅, sec312_card_F hp] at hprod
  rw [sec312_Q_eq hp k hS hP]
  have hq : 0 < (2 ^ f) ^ 2 := by positivity
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [hprod]
  ring

theorem sec312_Q_le_D : (d.E ⊓ d.D) ⊔ d.F ≤ d.D := sup_le inf_le_right (sec312_F_le_D hp k)

theorem sec312_Q_comm : ∀ q ∈ (d.E ⊓ d.D) ⊔ d.F, ∀ r ∈ S, r⁻¹ * (q * r * q⁻¹) ∈ d.F := by
  intro q hq r hr
  have h1 : q ∈ S ⊓ centralizerSection S d.F := by
    rw [k.s10_3 S hS hP]
    exact hq
  exact (Subgroup.mem_inf.1 h1).2.2.2 r hr

end SLevel

section Bar

variable (hp : d.CaseHyp) (k : d.Know10)
include hp k

theorem sec312_D_le_N_F : d.D ≤ normalizer (d.F : Set G) :=
  d.D_le_L₁.trans (sec312_L₁_le_N_F hp k)

theorem sec312_M₁_le_N_F : d.M₁ ≤ normalizer (d.F : Set G) :=
  (sec312_M₁_le_L₁ k).trans (sec312_L₁_le_N_F hp k)

theorem sec312_bar_sq : ∀ v ∈ bar d.F d.D, v * v = 1 := by
  intro v hv
  obtain ⟨z, hz, rfl⟩ := Sec312.mem_bar_iff_exists.1 hv
  rw [← map_mul, proj_eq_one_iff]
  exact sec312_sq_mem_F hp k z hz

theorem sec312_bar_card : Nat.card (bar d.F d.D) = (2 ^ f) ^ 8 := by
  have h1 := card_bar_mul (sec312_F_le_D hp k) (sec312_D_le_N_F hp k)
  rw [sec312_card_D k, sec312_card_F hp] at h1
  have hq : 0 < (2 ^ f) ^ 8 := by positivity
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [h1]
  ring

theorem sec312_nt : ¬ bar d.F d.M₁ ≤
    centralizer ((bar d.F d.D : Subgroup (Bar d.F)) : Set (Bar d.F)) := by
  intro hM
  obtain ⟨S, hS, hP⟩ := sec312_exists_S hp
  have hDN := sec312_D_le_N_F hp k
  have hMN := sec312_M₁_le_N_F hp k
  have hVsq := sec312_bar_sq hp k
  have hDQ : d.D ≤ (d.E ⊓ d.D) ⊔ d.F := by
    intro x hx
    have hxS : x ∈ S := sec312_D_le_S hp k hS hP hx
    set y₀ : Bar d.F := proj d.F ⟨x, hDN hx⟩ with hy₀
    have hy₀V : y₀ ∈ bar d.F d.D := proj_mem_bar (A := d.F) (x := ⟨x, hDN hx⟩) hx
    set Cx : Subgroup G := lift (centralizer ({y₀} : Set (Bar d.F))) with hCx
    have hDCx : d.D ≤ Cx := fun s hs => mem_lift_of_proj_mem (x := ⟨s, hDN hs⟩)
      (mem_centralizer_singleton_iff.2
        (Common.mul_comm_of_mul_self hVsq (proj_mem_bar (A := d.F) (x := ⟨s, hDN hs⟩) hs) hy₀V))
    have hRCx : S ⊓ d.M₁ ≤ Cx := fun s hs => mem_lift_of_proj_mem (x := ⟨s, hMN hs.2⟩)
      (mem_centralizer_singleton_iff.2
        ((mem_centralizer_iff.1 (hM (proj_mem_bar (A := d.F) (x := ⟨s, hMN hs.2⟩) hs.2)) y₀
          hy₀V).symm))
    have hSCx : S ≤ Cx := (sec312_S_eq_D_sup_R hp k hS hP).le.trans (sup_le hDCx hRCx)
    have hxQ : x ∈ S ⊓ centralizerSection S d.F := by
      refine Subgroup.mem_inf.2 ⟨hxS, ?_⟩
      refine ⟨le_normalizer hxS, hDN hx, fun s hs => ?_⟩
      have hsN : s ∈ normalizer (d.F : Set G) :=
        (sec312_S_le_L₁ hp k hS hP |>.trans (sec312_L₁_le_N_F hp k)) hs
      have hcomm := mem_centralizer_singleton_iff.1
        (proj_mem_of_mem_lift (x := ⟨s, hsN⟩) (hSCx hs))
      have e : proj d.F ⟨s⁻¹ * (x * s * x⁻¹), mul_mem (inv_mem hsN)
          (mul_mem (mul_mem (hDN hx) hsN) (inv_mem (hDN hx)))⟩ = 1 := by
        change (proj d.F ⟨s, hsN⟩)⁻¹ * (y₀ * proj d.F ⟨s, hsN⟩ * y₀⁻¹) = 1
        rw [← hcomm, mul_inv_cancel_right, inv_mul_cancel]
      exact proj_eq_one_iff.1 e
    rwa [k.s10_3 S hS hP] at hxQ
  have hle := Subgroup.card_le_of_le hDQ
  rw [sec312_card_D k, sec312_Q_card hp k hS hP] at hle
  have h2 : 2 ≤ 2 ^ f := Nat.le_self_pow (by have := sec312_two_le hp; omega) 2
  have : (2 ^ f) ^ 12 < (2 ^ f) ^ 16 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem sec312_fixed {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) :
    (2 ^ f) ^ 4 ≤ Nat.card (bar d.F d.D ⊓
      centralizer ((bar d.F (S ⊓ d.M₁) : Subgroup (Bar d.F)) : Set (Bar d.F)) :
        Subgroup (Bar d.F)) := by
  set Q : Subgroup G := (d.E ⊓ d.D) ⊔ d.F with hQ
  have hFQ : d.F ≤ Q := le_sup_right
  have hQD := sec312_Q_le_D hp k hS hP
  have hQN : Q ≤ normalizer (d.F : Set G) := hQD.trans (sec312_D_le_N_F hp k)
  have hcard : Nat.card (bar d.F Q) = (2 ^ f) ^ 4 := by
    have h1 := card_bar_mul hFQ hQN
    rw [sec312_Q_card hp k hS hP, sec312_card_F hp] at h1
    have hq : 0 < (2 ^ f) ^ 8 := by positivity
    apply Nat.eq_of_mul_eq_mul_right hq
    rw [h1]
    ring
  have hle : bar d.F Q ≤ bar d.F d.D ⊓
      centralizer ((bar d.F (S ⊓ d.M₁) : Subgroup (Bar d.F)) : Set (Bar d.F)) := by
    refine le_inf (bar_mono hQD) ?_
    intro v hv
    obtain ⟨z, hz, rfl⟩ := Sec312.mem_bar_iff_exists.1 hv
    rw [mem_centralizer_iff]
    intro r hr
    obtain ⟨w, hw, rfl⟩ := Sec312.mem_bar_iff_exists.1 hr
    have h1 := sec312_Q_comm hp k hS hP z hz w hw.1
    have e : proj d.F (w⁻¹ * (z * w * z⁻¹)) = 1 := proj_eq_one_iff.2 h1
    rw [map_mul, map_inv, map_mul, map_mul, map_inv] at e
    have e' := inv_mul_eq_one.1 e
    calc proj d.F w * proj d.F z = (proj d.F z * proj d.F w * (proj d.F z)⁻¹) * proj d.F z := by
          rw [← e']
      _ = proj d.F z * proj d.F w := by group
  have := Subgroup.card_le_of_le hle
  rwa [hcard] at this

end Bar

section Psi

variable {κ : Type} [Field κ] [Fintype κ]

theorem sec312_card_eq (hκ : Fintype.card κ = (2 ^ f) ^ 2) : Nat.card κ = 2 ^ (2 * f) := by
  rw [Nat.card_eq_fintype_card, hκ, ← pow_mul, mul_comm]

theorem sec312_charP (hκ : Fintype.card κ = (2 ^ f) ^ 2) : CharP κ 2 :=
  U4.charP_two_of_card (sec312_card_eq hκ)

theorem sec312_four_le (hp : d.CaseHyp) (hκ : Fintype.card κ = (2 ^ f) ^ 2) :
    4 ≤ Nat.card κ := by
  rw [sec312_card_eq hκ]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by have := sec312_two_le hp; omega)

theorem sec312_swap (hp : d.CaseHyp) (k : d.Know11) (hκ : Fintype.card κ = (2 ^ f) ^ 2)
    (ψ : d.M₁ ≃* SL(2, κ) × SL(2, κ)) :
    (Common.prodFactorOne ψ).map (MulAut.conj d.t).toMonoidHom = Common.prodFactorTwo ψ ∧
      (Common.prodFactorTwo ψ).map (MulAut.conj d.t).toMonoidHom = Common.prodFactorOne ψ := by
  obtain ⟨k₀, _, _, hk₀, ψ₀, α, hdiag, hswap⟩ := k.s11
  haveI hc₀ : CharP k₀ 2 := sec312_charP hk₀
  haveI hc : CharP κ 2 := sec312_charP hκ
  have h4₀ := sec312_four_le hp hk₀
  have h4 := sec312_four_le hp hκ
  haveI : Nontrivial (SL(2, κ)) := (Common.sl2_isSimpleGroup_of_charTwo h4).toNontrivial
  have ht := hp.hyp.t_mem_normalizer_M₁
  have hX₀ : (Common.prodFactorOne ψ₀).map (MulAut.conj d.t).toMonoidHom =
      Common.prodFactorTwo ψ₀ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have := Common.conj_mem_prodFactorTwo_of_swap ψ₀ ht hswap hx
      change d.t * x * d.t⁻¹ ∈ Common.prodFactorTwo ψ₀
      rw [hp.hyp.t_inv'] at this ⊢
      exact this
    · intro y hy
      refine ⟨d.t⁻¹ * y * d.t, Common.conj_mem_prodFactorOne_of_swap ψ₀ ht hswap hy, ?_⟩
      change d.t * (d.t⁻¹ * y * d.t) * d.t⁻¹ = y
      group
  have hY₀ : (Common.prodFactorTwo ψ₀).map (MulAut.conj d.t).toMonoidHom =
      Common.prodFactorOne ψ₀ := by
    rw [← hX₀, Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id (Common.prodFactorOne ψ₀)]
    congr 1
    ext x
    change d.t * (d.t * x * d.t⁻¹) * d.t⁻¹ = x
    rw [hp.hyp.t_inv']
    calc d.t * (d.t * x * d.t) * d.t = (d.t * d.t) * x * (d.t * d.t) := by group
      _ = x := by rw [hp.hyp.t_mul_t, one_mul, mul_one]
  have hXne : Common.prodFactorOne ψ ≠ ⊥ := Common.prodFactorOne_ne_bot ψ
  have hYne : Common.prodFactorTwo ψ ≠ ⊥ := Common.prodFactorTwo_ne_bot ψ
  have hXY : Common.prodFactorOne ψ ⊓ Common.prodFactorTwo ψ = ⊥ :=
    Common.prodFactorOne_inf_prodFactorTwo ψ
  have hXnM : Common.prodFactorOne ψ ≠ d.M₁ := by
    intro hx
    have : Common.prodFactorTwo ψ ≤ Common.prodFactorOne ψ := (Common.prodFactorTwo_le ψ).trans hx.symm.le
    exact hYne (by rw [← hXY, inf_eq_right.2 this])
  have hYnM : Common.prodFactorTwo ψ ≠ d.M₁ := by
    intro hy
    have : Common.prodFactorOne ψ ≤ Common.prodFactorTwo ψ := (Common.prodFactorOne_le ψ).trans hy.symm.le
    exact hXne (by rw [← hXY, inf_eq_left.2 this])
  have hXc : Common.prodFactorOne ψ = Common.prodFactorOne ψ₀ ∨
      Common.prodFactorOne ψ = Common.prodFactorTwo ψ₀ := by
    rcases Common.eq_prodFactor_of_le_normalizer h4₀ ψ₀ (Common.prodFactorOne_le ψ)
      (Common.le_normalizer_prodFactorOne ψ) with h | h | h | h
    · exact absurd h hXne
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hXnM
  have hYc : Common.prodFactorTwo ψ = Common.prodFactorOne ψ₀ ∨
      Common.prodFactorTwo ψ = Common.prodFactorTwo ψ₀ := by
    rcases Common.eq_prodFactor_of_le_normalizer h4₀ ψ₀ (Common.prodFactorTwo_le ψ)
      (Common.le_normalizer_prodFactorTwo ψ) with h | h | h | h
    · exact absurd h hYne
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hYnM
  rcases hXc with hx | hx <;> rcases hYc with hy | hy
  · exfalso
    have h5 : Common.prodFactorOne ψ ⊓ Common.prodFactorTwo ψ = Common.prodFactorOne ψ := by
      rw [hy, ← hx]
      exact inf_idem _
    exact hXne (h5.symm.trans hXY)
  · rw [hx, hy]
    exact ⟨hX₀, hY₀⟩
  · rw [hx, hy]
    exact ⟨hY₀, hX₀⟩
  · exfalso
    have h5 : Common.prodFactorOne ψ ⊓ Common.prodFactorTwo ψ = Common.prodFactorOne ψ := by
      rw [hy, ← hx]
      exact inf_idem _
    exact hXne (h5.symm.trans hXY)

end Psi

section SettingD

variable {κ : Type} [Field κ] [Fintype κ]

theorem sec312_inf_F_of_le_M₁ (hp : d.CaseHyp) (k : d.Know10) {H : Subgroup G}
    (hH : H ≤ d.M₁) : H ⊓ d.F = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ d.D ⊓ d.M₁ := Subgroup.mem_inf.2 ⟨sec312_F_le_D hp k hx.2, hH hx.1⟩
  rw [sec312_D_inf_M₁ k] at h1
  exact h1

theorem sec312_t_mem_N_S (hp : d.CaseHyp) (k : d.Know10) {S : Subgroup G}
    (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) : d.t ∈ normalizer (S : Set G) := by
  rw [sec312_S_eq hp k hS hP]
  exact Common.mem_normalizer_sup (hp.hyp.t_mem_normalizer_E_caseB hp.gms)
    hp.hyp.t_mem_normalizer_D

theorem sec312_map_conj_R (hp : d.CaseHyp) (k : d.Know10) {S : Subgroup G}
    (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) :
    (S ⊓ d.M₁).map (MulAut.conj d.t).toMonoidHom = S ⊓ d.M₁ := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj d.t).injective,
    map_conj_eq_of_mem_normalizer (sec312_t_mem_N_S hp k hS hP),
    map_conj_eq_of_mem_normalizer hp.hyp.t_mem_normalizer_M₁]

theorem sec312_setting (hp : d.CaseHyp) (k : d.Know11) {S : Subgroup G}
    (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) (hκ : Fintype.card κ = (2 ^ f) ^ 2)
    (ψ : d.M₁ ≃* SL(2, κ) × SL(2, κ)) :
    Sec312.Setting (2 * f) (bar d.F d.D) (bar d.F (Common.prodFactorOne ψ))
      (bar d.F (Common.prodFactorTwo ψ)) (bar d.F (S ⊓ d.M₁ ⊓ Common.prodFactorOne ψ))
      (bar d.F (S ⊓ d.M₁ ⊓ Common.prodFactorTwo ψ))
      (proj d.F ⟨d.t, hp.hyp.t_mem_normalizer_F⟩) := by
  have k10 : d.Know10 := k.toKnow10
  have ht : d.t ∈ normalizer (d.F : Set G) := hp.hyp.t_mem_normalizer_F
  have hFD := sec312_F_le_D hp k10
  have hDN := sec312_D_le_N_F hp k10
  have hMN := sec312_M₁_le_N_F hp k10
  have hL := sec312_L₁_le_N_D hp
  have hXM := Common.prodFactorOne_le ψ
  have hYM := Common.prodFactorTwo_le ψ
  have hXN : Common.prodFactorOne ψ ≤ normalizer (d.F : Set G) := hXM.trans hMN
  have hYN : Common.prodFactorTwo ψ ≤ normalizer (d.F : Set G) := hYM.trans hMN
  have hsw := sec312_swap hp k hκ ψ
  have hVt : (bar d.F d.D).map (MulAut.conj (proj d.F ⟨d.t, ht⟩)).toMonoidHom = bar d.F d.D := by
    rw [← Sec312.bar_map_conj ht, map_conj_eq_of_mem_normalizer hp.hyp.t_mem_normalizer_D]
  have hX' : (bar d.F (Common.prodFactorOne ψ)).map
      (MulAut.conj (proj d.F ⟨d.t, ht⟩)).toMonoidHom = bar d.F (Common.prodFactorTwo ψ) := by
    rw [← Sec312.bar_map_conj ht, hsw.1]
  have hY' : (bar d.F (Common.prodFactorTwo ψ)).map
      (MulAut.conj (proj d.F ⟨d.t, ht⟩)).toMonoidHom = bar d.F (Common.prodFactorOne ψ) := by
    rw [← Sec312.bar_map_conj ht, hsw.2]
  have hR' : (bar d.F (S ⊓ d.M₁ ⊓ Common.prodFactorOne ψ)).map
      (MulAut.conj (proj d.F ⟨d.t, ht⟩)).toMonoidHom =
        bar d.F (S ⊓ d.M₁ ⊓ Common.prodFactorTwo ψ) := by
    rw [← Sec312.bar_map_conj ht, Subgroup.map_inf _ _ _ (MulAut.conj d.t).injective,
      sec312_map_conj_R hp k10 hS hP, hsw.1]
  refine ⟨sec312_bar_sq hp k10, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hX', hY', hR'⟩
  · rw [sec312_bar_card hp k10, ← pow_mul]
    ring_nf
  · exact bar_le_normalizer_bar hFD (hXM.trans ((sec312_M₁_le_L₁ k10).trans hL))
  · exact bar_le_normalizer_bar hFD (hYM.trans ((sec312_M₁_le_L₁ k10).trans hL))
  · intro x hx y hy
    obtain ⟨z₁, hz₁, rfl⟩ := Sec312.mem_bar_iff_exists.1 hx
    obtain ⟨z₂, hz₂, rfl⟩ := Sec312.mem_bar_iff_exists.1 hy
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_iff.1 (Common.prodFactorOne_le_centralizer ψ hz₁) z₂ hz₂).symm
  · exact Sec312.isSylowOf_bar
      ((sec312_isSylowOf_R hp k10 hS hP).inf_of_le_normalizer hXM
        (Common.le_normalizer_prodFactorOne ψ)) hXN (sec312_inf_F_of_le_M₁ hp k10 hXM)
  · exact Sec312.isSylowOf_bar
      ((sec312_isSylowOf_R hp k10 hS hP).inf_of_le_normalizer hYM
        (Common.le_normalizer_prodFactorTwo ψ)) hYN (sec312_inf_F_of_le_M₁ hp k10 hYM)
  · intro hX
    have hY'' : bar d.F (Common.prodFactorTwo ψ) ≤
        centralizer ((bar d.F d.D : Subgroup (Bar d.F)) : Set (Bar d.F)) := by
      have := Sec312.map_conj_le_centralizer (proj d.F ⟨d.t, ht⟩) hX
      rwa [hX', hVt] at this
    apply sec312_nt hp k10
    rw [← Common.prodFactorOne_sup_prodFactorTwo ψ, Sec312.bar_sup hXN hYN]
    exact sup_le hX hY''
  · have h1 := sec312_fixed hp k10 hS hP
    have h2 : bar d.F (S ⊓ d.M₁ ⊓ Common.prodFactorOne ψ) ⊔
        bar d.F (S ⊓ d.M₁ ⊓ Common.prodFactorTwo ψ) ≤ bar d.F (S ⊓ d.M₁) :=
      sup_le (bar_mono inf_le_left) (bar_mono inf_le_left)
    have h3 : (2 : ℕ) ^ (2 * (2 * f)) = (2 ^ f) ^ 4 := by
      rw [← pow_mul]; ring_nf
    rw [h3]
    exact h1.trans (Subgroup.card_le_of_le (inf_le_inf_left _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 h2))))
  · exact bar_le_normalizer_bar hFD (zpowers_le.2 hp.hyp.t_mem_normalizer_D)
      (proj_mem_bar (A := d.F) (x := ⟨d.t, ht⟩) (mem_zpowers d.t))

theorem sec312_bar_D_inf_M₁ (hp : d.CaseHyp) (k : d.Know10) :
    bar d.F d.D ⊓ bar d.F d.M₁ = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨z₁, hz₁, rfl⟩ := Sec312.mem_bar_iff_exists.1 hy.1
  obtain ⟨z₂, hz₂, hz⟩ := Sec312.mem_bar_iff_exists.1 hy.2
  have h1 := proj_eq_proj_iff.1 hz
  have h3 : ((z₂ : G)⁻¹ * z₁)⁻¹ ∈ d.D := inv_mem (sec312_F_le_D hp k h1)
  have hz₂D : (z₂ : G) ∈ d.D := by
    have e : (z₂ : G) = z₁ * ((z₂ : G)⁻¹ * z₁)⁻¹ := by group
    rw [e]
    exact mul_mem hz₁ h3
  have h4 : (z₂ : G) ∈ d.D ⊓ d.M₁ := Subgroup.mem_inf.2 ⟨hz₂D, hz₂⟩
  rw [sec312_D_inf_M₁ k, Subgroup.mem_bot] at h4
  have hz₂1 : z₂ = 1 := Subtype.ext h4
  rw [hz₂1, map_one] at hz
  rw [← hz]
  exact one_mem _

end SettingD

end Data

end CFSG.LocalAnalysis.EvenBN.U5
