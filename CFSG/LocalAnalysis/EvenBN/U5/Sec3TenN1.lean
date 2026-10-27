module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3TenCoprime
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedParts

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

section Generic

variable {G : Type} [Group G] [Finite G]

theorem n1_factor_of_commute {A B : Subgroup G} (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hc).2
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  rw [hset] at hx'
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hx'
  exact ⟨a, ha, b, hb, hab.symm⟩

theorem n1_solvable_of_le_comm {F X : Subgroup G} (hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x)
    (hX : X ≤ F) : Group.IsSolvable X :=
  Group.isSolvable_of_comm fun u w => Subtype.ext (hFc _ (hX u.2) _ (hX w.2))

theorem n1_inf_centralizer_eq_of_le {A P H : Subgroup G} (hAP : A ≤ P)
    (hPA : P ⊓ centralizer (H : Set G) ≤ A) :
    A ⊓ centralizer (H : Set G) = P ⊓ centralizer (H : Set G) := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2 ⟨hAP h1, h2⟩
  · obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2 ⟨hPA hx, h2⟩

theorem n1_mem_centralizer_sup {H₁ H₂ : Subgroup G} {x : G} :
    x ∈ centralizer ((H₁ ⊔ H₂ : Subgroup G) : Set G) ↔
      x ∈ centralizer (H₁ : Set G) ∧ x ∈ centralizer (H₂ : Set G) := by
  constructor
  · intro hx
    exact ⟨Subgroup.mem_centralizer_iff.2 fun g (hg : g ∈ H₁) =>
        Subgroup.mem_centralizer_iff.1 hx g (Subgroup.mem_sup_left hg),
      Subgroup.mem_centralizer_iff.2 fun g (hg : g ∈ H₂) =>
        Subgroup.mem_centralizer_iff.1 hx g (Subgroup.mem_sup_right hg)⟩
  · rintro ⟨h₁, h₂⟩
    have hle : H₁ ⊔ H₂ ≤ Subgroup.centralizer ({x} : Set G) :=
      sup_le
        (fun g hg => Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 h₁ g hg))
        (fun g hg => Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 h₂ g hg))
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

end Generic

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem n1_I₆_le_I (d : Data G h) : d.I₆ ≤ d.I := d.pull_mono (torusEq_le _)

theorem n1_coprime_I (d : Data G h) {H : Subgroup G} (hH : H ≤ d.I) (k : ℕ) :
    Nat.Coprime (Nat.card H) (2 ^ k) :=
  Nat.Coprime.pow_right k
    (Nat.coprime_two_left.2 (Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le hH))).symm

theorem n1_A₁_le_F (hp : d.CaseHyp) : d.A₁ ≤ d.F := by
  obtain ⟨-, -, -, -, -, -, hFB3, -⟩ := hp.hyp.sec3_4 hp.gms
  rw [← hFB3]
  exact inf_le_left

theorem n1_sec2 (hp : d.CaseHyp) :
    d.Zp ≤ d.P ∧ d.Zp ≤ d.Z₂p ∧ d.P ⊓ centralizer (d.I₄ : Set G) ≤ d.Z₂p ∧
      d.Z₂p ⊓ (d.P ⊓ centralizer (d.I₆ : Set G)) = ⊥ ∧
      d.A₁ = d.Z₂p ⊔ (d.P ⊓ centralizer (d.I₆ : Set G)) ∧
      d.A₁ = (d.P ⊓ centralizer (d.I₄ : Set G)) ⊔
        (d.P ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G)) ∧
      (d.P ⊓ centralizer (d.I₄ : Set G)) ⊓
        (d.P ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G)) = ⊥ := by
  obtain ⟨hZp, ⟨hZ₂, -⟩, ⟨hA₁6, hZ₂C6⟩, ⟨hA₁36, hC4C36⟩, -⟩ := d.sec2_1_two hp.hyp.two_le
  refine ⟨?_, ?_, ?_, hZ₂C6, hA₁6, hA₁36, hC4C36⟩
  · rw [hZp]
    exact inf_le_left
  · rw [hZ₂]
    exact le_sup_left
  · rw [hZ₂]
    exact le_sup_right

theorem n1_P_C6_le_A₁ (hp : d.CaseHyp) :
    d.P ⊓ centralizer (d.I₆ : Set G) ≤ d.A₁ := by
  obtain ⟨-, -, -, -, hA₁6, -, -⟩ := n1_sec2 hp
  rw [hA₁6]
  exact le_sup_right

theorem n1_P_C36_le_A₁ (hp : d.CaseHyp) :
    d.P ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G) ≤ d.A₁ := by
  obtain ⟨-, -, -, -, -, hA₁36, -⟩ := n1_sec2 hp
  rw [hA₁36]
  exact le_sup_right

theorem n1_P_C4_inf_C6 (hp : d.CaseHyp) :
    (d.P ⊓ centralizer (d.I₄ : Set G)) ⊓ (d.P ⊓ centralizer (d.I₆ : Set G)) = ⊥ := by
  obtain ⟨-, -, hC4Z₂, hZ₂6, -, -, -⟩ := n1_sec2 hp
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
  have hb : x ∈ d.Z₂p ⊓ (d.P ⊓ centralizer (d.I₆ : Set G)) :=
    Subgroup.mem_inf.2 ⟨hC4Z₂ h1, h2⟩
  rw [hZ₂6] at hb
  exact hb

theorem n1_P_C4_inf_C36 (hp : d.CaseHyp) :
    (d.P ⊓ centralizer (d.I₄ : Set G)) ⊓
      (d.P ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G)) = ⊥ := by
  obtain ⟨-, -, -, -, -, -, hC4C36⟩ := n1_sec2 hp
  exact hC4C36

theorem n1_Zp_inf_C6 (hp : d.CaseHyp) :
    d.Zp ⊓ centralizer (d.I₆ : Set G) = ⊥ := by
  obtain ⟨hZpP, hZpZ₂, -, hZ₂6, -, -, -⟩ := n1_sec2 hp
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
  have hb : x ∈ d.Z₂p ⊓ (d.P ⊓ centralizer (d.I₆ : Set G)) :=
    Subgroup.mem_inf.2 ⟨hZpZ₂ h1, Subgroup.mem_inf.2 ⟨hZpP h1, h2⟩⟩
  rw [hZ₂6] at hb
  exact hb

theorem n1_A₁_inf_C_eq {H : Subgroup G} (hPH : d.P ⊓ centralizer (H : Set G) ≤ d.A₁) :
    d.A₁ ⊓ centralizer (H : Set G) = d.P ⊓ centralizer (H : Set G) :=
  n1_inf_centralizer_eq_of_le d.A₁_le_P hPH

theorem n1_card_F (hp : d.CaseHyp) {H : Subgroup G} (hH : H ≤ d.I) :
    Nat.card (d.F ⊓ centralizer (H : Set G) : Subgroup G) =
      Nat.card (d.A₁ ⊓ centralizer (H : Set G) : Subgroup G) *
        Nat.card (d.A₁ ⊓ centralizer (H : Set G) : Subgroup G) := by
  have hd := hp.hyp
  have hGMS := hp.gms
  obtain ⟨-, -, -, -, -, -, -, -, hFcard, ψ, hψs, hker, -, hequ⟩ := hd.sec3_4 hGMS
  have hFc := hd.F_comm hGMS
  have hXc : Nat.Coprime (Nat.card H) (Nat.card d.F) := by
    rw [hFcard]
    exact Nat.Coprime.pow_right 8 (n1_coprime_I d hH f)
  have hAc : Nat.Coprime (Nat.card H) (Nat.card d.A₁) := by
    rw [d.card_A₁]
    exact Nat.Coprime.pow_right 4 (n1_coprime_I d hH f)
  have hequ' : ∀ c ∈ H, ∀ x : d.F, ∃ hx : c * x * c⁻¹ ∈ d.F,
      (ψ ⟨c * x * c⁻¹, hx⟩ : G) = c * (ψ x : G) * c⁻¹ :=
    fun c hc x => hequ c (hd.I_le_normalizer_B₁ (hH hc)) x
  exact s4o_card_of_equivariant_subgroup (n1_A₁_le_F hp) (hH.trans (hd.I_le_normalizer_F hGMS))
    (hH.trans d.I_le_normalizer_A₁) (hH.trans d.I_le_normalizer_A₁)
    (n1_solvable_of_le_comm hFc le_rfl) (n1_solvable_of_le_comm hFc (n1_A₁_le_F hp))
    hXc hAc ψ hψs hker hequ'

theorem n1_card_V (hp : d.CaseHyp) {H : Subgroup G} (hH : H ≤ d.I) :
    Nat.card (d.V ⊓ centralizer (H : Set G) : Subgroup G) =
      Nat.card (d.Zp ⊓ centralizer (H : Set G) : Subgroup G) *
        Nat.card (d.Zp ⊓ centralizer (H : Set G) : Subgroup G) := by
  have hd := hp.hyp
  have hGMS := hp.gms
  obtain ⟨-, hcardV, hZpV, -, -, -, -, -, ψ, hψs, hker, -, hequ⟩ := hd.sec3_3_one hGMS
  have hFc := hd.F_comm hGMS
  have hVW : d.V ≤ d.W := by
    rw [hd.W_eq hGMS]
    exact le_sup_left
  have hVF : d.V ≤ d.F := hVW.trans (hd.W_le_F hGMS)
  have hZpF : d.Zp ≤ d.F := hZpV.trans hVF
  have hXc : Nat.Coprime (Nat.card H) (Nat.card d.V) := by
    rw [hcardV]
    exact Nat.Coprime.pow_right 2 (n1_coprime_I d hH f)
  have hYc : Nat.Coprime (Nat.card H) (Nat.card d.Zp) := by
    rw [d.card_Zp]
    exact n1_coprime_I d hH f
  have hequ' : ∀ c ∈ H, ∀ v : d.V, ∃ hv : c * v * c⁻¹ ∈ d.V,
      (ψ ⟨c * v * c⁻¹, hv⟩ : G) = c * (ψ v : G) * c⁻¹ :=
    fun c hc v => hequ c
      (Subgroup.mem_inf.2 ⟨d.I_le_normalizer_Zp (hH hc),
        (Subgroup.mem_inf.1 (hd.I_le_normalizer_B₁ (hH hc))).2⟩) v
  exact s4o_card_of_equivariant_subgroup hZpV (hH.trans hd.I_le_normalizer_V)
    (hH.trans d.I_le_normalizer_Zp) (hH.trans d.I_le_normalizer_Zp)
    (n1_solvable_of_le_comm hFc hVF) (n1_solvable_of_le_comm hFc hZpF) hXc hYc ψ hψs hker hequ'

theorem n1_card_P_C6 (hp : d.CaseHyp) :
    Nat.card (d.P ⊓ centralizer (d.I₆ : Set G) : Subgroup G) = 2 ^ f := by
  obtain ⟨-, -, -, hZ₂6, hA₁6, -, -⟩ := n1_sec2 hp
  have hFc := hp.hyp.F_comm hp.gms
  have hZ₂A : d.Z₂p ≤ d.A₁ := by
    rw [hA₁6]
    exact le_sup_left
  have hc : ∀ x ∈ d.Z₂p, ∀ y ∈ d.P ⊓ centralizer (d.I₆ : Set G), x * y = y * x :=
    fun x hx y hy => hFc x (n1_A₁_le_F hp (hZ₂A hx)) y (n1_A₁_le_F hp (n1_P_C6_le_A₁ hp hy))
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).1
  rw [← hA₁6, hZ₂6, Subgroup.card_bot, d.card_A₁, d.card_Z₂p, mul_one] at hcard
  have h3 : (2 ^ f) ^ 3 * 2 ^ f =
      (2 ^ f) ^ 3 * Nat.card (d.P ⊓ centralizer (d.I₆ : Set G) : Subgroup G) := by
    rw [← hcard]
    ring
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) h3).symm

theorem n1_card_P_C36 (hp : d.CaseHyp) :
    Nat.card (d.P ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G) : Subgroup G) = (2 ^ f) ^ 2 := by
  obtain ⟨-, -, -, -, -, hA₁36, hC4C36⟩ := n1_sec2 hp
  have hFc := hp.hyp.F_comm hp.gms
  have hC4A : d.P ⊓ centralizer (d.I₄ : Set G) ≤ d.A₁ := by
    rw [hA₁36]
    exact le_sup_left
  have hc : ∀ x ∈ d.P ⊓ centralizer (d.I₄ : Set G),
      ∀ y ∈ d.P ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G), x * y = y * x :=
    fun x hx y hy => hFc x (n1_A₁_le_F hp (hC4A hx)) y (n1_A₁_le_F hp (n1_P_C36_le_A₁ hp hy))
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).1
  rw [← hA₁36, hC4C36, Subgroup.card_bot, d.card_A₁, hp.hyp.card_C₄, mul_one] at hcard
  have h3 : (2 ^ f) ^ 2 * (2 ^ f) ^ 2 =
      (2 ^ f) ^ 2 * Nat.card (d.P ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G) : Subgroup G) := by
    rw [← hcard]
    ring
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) h3).symm

theorem n1_le_normalizer_F_inf_C4 (hp : d.CaseHyp) {H : Subgroup G} (hH : H ≤ d.I) :
    H ≤ normalizer ((d.F ⊓ centralizer (d.I₄ : Set G) : Subgroup G) : Set G) := by
  have hd := hp.hyp
  have hGMS := hp.gms
  have key : ∀ g ∈ H, ∀ x ∈ d.F ⊓ centralizer (d.I₄ : Set G),
      g * x * g⁻¹ ∈ d.F ⊓ centralizer (d.I₄ : Set G) := by
    intro g hg x hx
    obtain ⟨hxF, hxC⟩ := Subgroup.mem_inf.1 hx
    have hgI : g ∈ d.I := hH hg
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hd.I_le_normalizer_F hGMS hgI) x).1 hxF, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    have hig : i * g = g * i := d.I_comm (d.I₄_le_I hi) hgI
    have hai : i * x = x * i := Subgroup.mem_centralizer_iff.1 hxC i hi
    have hgi : i * g⁻¹ = g⁻¹ * i := by
      calc i * g⁻¹ = g⁻¹ * (g * i) * g⁻¹ := by group
        _ = g⁻¹ * (i * g) * g⁻¹ := by rw [hig]
        _ = g⁻¹ * i := by group
    calc i * (g * x * g⁻¹) = (i * g) * x * g⁻¹ := by group
      _ = (g * i) * x * g⁻¹ := by rw [hig]
      _ = g * (i * x) * g⁻¹ := by group
      _ = g * (x * i) * g⁻¹ := by rw [hai]
      _ = g * x * (i * g⁻¹) := by group
      _ = g * x * (g⁻¹ * i) := by rw [hgi]
      _ = g * x * g⁻¹ * i := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key g hg x hx
  · intro hx
    have h' := key g⁻¹ (H.inv_mem hg) _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e] at h'
    exact h'

theorem n1_F_inf_C_eq_bot (hp : d.CaseHyp) {J : Subgroup G} (hJ : J ≤ d.I)
    (hA : d.A₁ ⊓ centralizer (J : Set G) = ⊥) :
    d.F ⊓ centralizer (J : Set G) = ⊥ := by
  have hcard : Nat.card (d.F ⊓ centralizer (J : Set G) : Subgroup G) = 1 := by
    rw [n1_card_F hp hJ, hA, Subgroup.card_bot, mul_one]
  exact Subgroup.card_eq_one.1 hcard

theorem n1_A₁_inf_C_join_eq_bot (hp : d.CaseHyp) {H : Subgroup G}
    (hPH : d.P ⊓ centralizer (H : Set G) ≤ d.A₁)
    (hbot : (d.P ⊓ centralizer (d.I₄ : Set G)) ⊓ (d.P ⊓ centralizer (H : Set G)) = ⊥) :
    d.A₁ ⊓ centralizer ((d.I₄ ⊔ H : Subgroup G) : Set G) = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxA, hxJ⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hx4, hxH⟩ := n1_mem_centralizer_sup.1 hxJ
  have hAH : x ∈ d.A₁ ⊓ centralizer (H : Set G) := Subgroup.mem_inf.2 ⟨hxA, hxH⟩
  rw [n1_A₁_inf_C_eq hPH] at hAH
  have hxP4 : x ∈ d.P ⊓ centralizer (d.I₄ : Set G) :=
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hAH).1, hx4⟩
  have hb : x ∈ (d.P ⊓ centralizer (d.I₄ : Set G)) ⊓ (d.P ⊓ centralizer (H : Set G)) :=
    Subgroup.mem_inf.2 ⟨hxP4, hAH⟩
  rw [hbot] at hb
  exact hb

theorem sec3101_RA (hp : d.CaseHyp) :
    Nat.card (d.F ⊓ centralizer (d.I₆ : Set G) : Subgroup G) = (2 ^ f) ^ 2 := by
  rw [n1_card_F hp (n1_I₆_le_I d), n1_A₁_inf_C_eq (n1_P_C6_le_A₁ hp), n1_card_P_C6 hp, pow_two]

theorem sec3101_RB (hp : d.CaseHyp) :
    Nat.card (d.F ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G) : Subgroup G) = (2 ^ f) ^ 4 := by
  have hH : d.I₃ ⊓ d.I₆ ≤ d.I := inf_le_left.trans d.I₃_le_I
  rw [n1_card_F hp hH, n1_A₁_inf_C_eq (n1_P_C36_le_A₁ hp), n1_card_P_C36 hp]
  ring

theorem sec3101_RC (hp : d.CaseHyp) :
    d.W ⊓ centralizer (d.I₆ : Set G) = ⊥ := by
  have hd := hp.hyp
  have hGMS := hp.gms
  have hFc := hd.F_comm hGMS
  have hW := hd.W_eq hGMS
  have hVW : d.V ≤ d.W := by
    rw [hW]
    exact le_sup_left
  have hBW : d.F ⊓ centralizer (d.I₄ : Set G) ≤ d.W := by
    rw [hW]
    exact le_sup_right
  have hVF : d.V ≤ d.F := hVW.trans (hd.W_le_F hGMS)
  have hcomm : ∀ x ∈ d.V, ∀ y ∈ d.F ⊓ centralizer (d.I₄ : Set G), x * y = y * x :=
    fun x hx y hy => hFc x (hVF hx) y (Subgroup.mem_inf.1 hy).1
  have hX : ∀ x ∈ d.W, ∃ a ∈ d.V, ∃ b ∈ d.F ⊓ centralizer (d.I₄ : Set G), x = a * b := by
    intro x hx
    rw [hW] at hx
    exact n1_factor_of_commute hcomm hx
  have hT3 := s4o_card_inf_centralizer_mul d.I₆ hVW hBW hd.V_inf_F_I₄ hX
    (le_trans (n1_I₆_le_I d) hd.I_le_normalizer_V) (n1_le_normalizer_F_inf_C4 hp (n1_I₆_le_I d))
  have hV6 : Nat.card (d.V ⊓ centralizer (d.I₆ : Set G) : Subgroup G) = 1 := by
    rw [n1_card_V hp (n1_I₆_le_I d), n1_Zp_inf_C6 hp, Subgroup.card_bot, mul_one]
  have hB6 : (d.F ⊓ centralizer (d.I₄ : Set G)) ⊓ centralizer (d.I₆ : Set G) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxB, hx6⟩ := Subgroup.mem_inf.1 hx
    have hxJ : x ∈ d.F ⊓ centralizer ((d.I₄ ⊔ d.I₆ : Subgroup G) : Set G) :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hxB).1,
        n1_mem_centralizer_sup.2 ⟨(Subgroup.mem_inf.1 hxB).2, hx6⟩⟩
    rw [n1_F_inf_C_eq_bot hp (sup_le d.I₄_le_I (n1_I₆_le_I d))
      (n1_A₁_inf_C_join_eq_bot hp (n1_P_C6_le_A₁ hp) (n1_P_C4_inf_C6 hp))] at hxJ
    exact hxJ
  have hB6card : Nat.card ((d.F ⊓ centralizer (d.I₄ : Set G)) ⊓ centralizer (d.I₆ : Set G) :
      Subgroup G) = 1 := by
    rw [hB6, Subgroup.card_bot]
  have hcard : Nat.card (d.W ⊓ centralizer (d.I₆ : Set G) : Subgroup G) = 1 := by
    rw [hT3, hV6, hB6card, mul_one]
  exact Subgroup.card_eq_one.1 hcard

theorem sec3101_RD (hp : d.CaseHyp) :
    (d.F ⊓ centralizer (d.I₄ : Set G)) ⊓
      (d.F ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G)) = ⊥ := by
  have hJ : d.I₄ ⊔ (d.I₃ ⊓ d.I₆) ≤ d.I :=
    sup_le d.I₄_le_I (inf_le_left.trans d.I₃_le_I)
  have hA1J := n1_A₁_inf_C_join_eq_bot hp (n1_P_C36_le_A₁ hp) (n1_P_C4_inf_C36 hp)
  have hFJ := n1_F_inf_C_eq_bot hp hJ hA1J
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hx4, hx36⟩ := Subgroup.mem_inf.1 hx
  have hxJ : x ∈ d.F ⊓ centralizer ((d.I₄ ⊔ (d.I₃ ⊓ d.I₆) : Subgroup G) : Set G) :=
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx4).1,
      n1_mem_centralizer_sup.2 ⟨(Subgroup.mem_inf.1 hx4).2, (Subgroup.mem_inf.1 hx36).2⟩⟩
  rw [hFJ] at hxJ
  exact hxJ

end Data

end CFSG.LocalAnalysis.EvenBN.U5
