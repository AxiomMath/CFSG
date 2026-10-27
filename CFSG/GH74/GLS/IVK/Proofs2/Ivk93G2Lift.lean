module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Lift
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93OrdG
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ComponentClassification CFSG.Blueprint

section Pair2

variable {G : Type} [Group G] [Finite G]

structure Pair2Data (G : Type) [Group G] [Finite G] (z : G) (r₁ r₂ : ℕ)
    (L₁ L₂ : Subgroup (CentralizerBar z)) : Prop where
  odd₁ : Odd r₁
  odd₂ : Odd r₂
  gt₁ : 3 < r₁
  gt₂ : 3 < r₂
  ne : L₁ ≠ L₂
  prod : IsCentralProd L₁ L₂ (LBar z)
  sl₁ : HasSL2Model ↥L₁ (fun r => r = r₁)
  sl₂ : HasSL2Model ↥L₂ (fun r => r = r₂)
  comp₁ : IsComponent L₁
  comp₂ : IsComponent L₂
  fitting : generalizedFitting (CentralizerBar z) = LBar z

variable {z : G} {r₁ r₂ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem isQuasisimple_of_hasSL2Model {K : Type} [Group K] {r : ℕ} (h4 : 4 ≤ r)
    (hK : HasSL2Model K (fun s => s = r)) : CFSG.IsQuasisimple K := by
  obtain ⟨F, _, _, hFq, ⟨e⟩⟩ := exists_sl2_equiv_of_hasSL2Model hK
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e (GHInv.isQuasisimple_sl2 (by omega))

omit [Finite G] in
theorem isComponent_of_prod {A B : Subgroup (CentralizerBar z)} {r : ℕ} (h4 : 4 ≤ r)
    (hsl : HasSL2Model ↥A (fun s => s = r)) (hprod : IsCentralProd A B (LBar z))
    (hfit : generalizedFitting (CentralizerBar z) = LBar z) (hAN : LBar z ≤ normalizer (A : Set (CentralizerBar z))) :
    IsComponent A := by
  have hAL : A ≤ LBar z := hprod.1 ▸ le_sup_left
  have hLN : (LBar z).Normal := by
    rw [← hfit]
    exact LocalCores.generalized_fitting_characteristic.2
  have hAn : (A.subgroupOf (LBar z)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAL).mpr hAN
  exact ⟨isQuasisimple_of_hasSL2Model h4 hsl,
    Subgroup.IsSubnormal.trans hAL hAn.isSubnormal hLN.isSubnormal⟩

theorem pair2_of_g2Shape {S : Subgroup G} (h : G2Shape z S r₁ r₂ L₁ L₂) (h3 : 3 < r₂) :
    Pair2Data G z r₁ r₂ L₁ L₂ := by
  obtain ⟨hodd₁, hodd₂, hgt, hprod, hsl₁, hsl₂, -, -, hfit, -⟩ := h
  have hN := LBar_le_normalizer hprod
  have hfit' := (hfit h3).2
  refine ⟨hodd₁, hodd₂, hgt, h3, ?_, hprod, hsl₁, hsl₂,
    isComponent_of_prod (by omega) hsl₁ hprod hfit' hN.1,
    isComponent_of_prod (A := L₂) (B := L₁) (by omega) hsl₂
      ⟨by rw [sup_comm]; exact hprod.1, fun a ha b hb => (hprod.2.1 b hb a ha).symm,
        by rw [inf_comm]; exact hprod.2.2⟩ hfit' hN.2, hfit'⟩
  intro heq
  have h2 : Nat.card ↥(L₁ ⊓ L₂) = 2 := hprod.2.2
  rw [← heq, inf_idem, card_of_hasSL2Model hsl₁] at h2
  have : 120 ≤ r₁ * (r₁ ^ 2 - 1) := by
    have h4 : 4 ≤ r₁ := by omega
    calc 120 ≤ 5 * (5 ^ 2 - 1) := by norm_num
      _ ≤ r₁ * (r₁ ^ 2 - 1) := by
        have h5 : 5 ≤ r₁ := by
          obtain ⟨m, hm⟩ := hodd₁
          omega
        exact Nat.mul_le_mul h5 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h5 2) 1)
  omega

theorem zbarC_mem_inf2 (hp : Pair2Data G z r₁ r₂ L₁ L₂) :
    toBar z ⟨z, mem_Cen_self z⟩ ∈ L₁ ⊓ L₂ := by
  have hc := toBar_z_mem_center z
  have hF : toBar z ⟨z, mem_Cen_self z⟩ ∈ generalizedFitting (CentralizerBar z) := by
    refine CFSG.centralizer_generalizedFitting_le (CentralizerBar z) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro f _
    exact Subgroup.mem_center_iff.mp hc f
  rw [hp.fitting, ← hp.prod.1] at hF
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute' hp.prod.2.1 hF
  have hcen := Subgroup.mem_center_iff.mp hc
  have hacen : ∀ c ∈ L₁, a * c = c * a := by
    intro c hc1
    have h1 := hcen c
    rw [hab] at h1
    have h2 : b * c = c * b := (hp.prod.2.1 c hc1 b hb).symm
    have : a * c * b = c * a * b := by
      calc a * c * b = a * (c * b) := by rw [mul_assoc]
        _ = a * (b * c) := by rw [h2]
        _ = a * b * c := by rw [mul_assoc]
        _ = c * (a * b) := h1.symm
        _ = c * a * b := by rw [mul_assoc]
    exact mul_right_cancel this
  have hbcen : ∀ d ∈ L₂, b * d = d * b := by
    intro d hd
    have h1 := hcen d
    rw [hab] at h1
    have h2 : a * d = d * a := hp.prod.2.1 a ha d hd
    have : a * (b * d) = a * (d * b) := by
      calc a * (b * d) = a * b * d := by rw [mul_assoc]
        _ = d * (a * b) := h1.symm
        _ = d * a * b := by rw [mul_assoc]
        _ = a * d * b := by rw [h2]
        _ = a * (d * b) := by rw [mul_assoc]
    exact mul_left_cancel this
  have key : ∀ {L M : Subgroup (CentralizerBar z)} {r : ℕ}, Odd r →
      (∀ a ∈ L, ∀ b ∈ M, a * b = b * a) →
      Nat.card ↥(L ⊓ M) = 2 → HasSL2Model ↥L (fun s => s = r) → ∀ a ∈ L,
      (∀ c ∈ L, a * c = c * a) → a ∈ M := by
    intro L M r hr hLM hW hsl a ha hac
    have hZc : Nat.card ↥((center ↥L).map L.subtype) = 2 := by
      rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact card_center_of_hasSL2Model hr hsl
    have hle : L ⊓ M ≤ (center ↥L).map L.subtype := by
      intro w hw
      refine Subgroup.mem_map.2 ⟨⟨w, hw.1⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (hLM c.1 c.2 w hw.2)
    have heq : L ⊓ M = (center ↥L).map L.subtype :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hW, hZc])
    have haZ : a ∈ (center ↥L).map L.subtype := by
      refine Subgroup.mem_map.2 ⟨⟨a, ha⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (hac c.1 c.2).symm
    rw [← heq] at haZ
    exact haZ.2
  have haL₂ : a ∈ L₂ := key hp.odd₁ hp.prod.2.1 hp.prod.2.2 hp.sl₁ a ha hacen
  have hbL₁ : b ∈ L₁ := by
    refine key (L := L₂) (M := L₁) hp.odd₂ (fun x hx y hy => (hp.prod.2.1 y hy x hx).symm) ?_ hp.sl₂ b hb hbcen
    rw [inf_comm]
    exact hp.prod.2.2
  rw [hab]
  exact ⟨L₁.mul_mem ha hbL₁, L₂.mul_mem haL₂ hb⟩

end Pair2

section Lift2

variable {G : Type} [Group G] [Finite G] {z : G} {r₁ r₂ : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem exists_cfg2 (hz2 : orderOf z = 2) {H : Subgroup G} (hCH : Cen z ≤ H) (hPerf : PerfInJ H)
    (hp : Pair2Data G z r₁ r₂ L₁ L₂) :
    ∃ (hzJ : mkH H ⟨z, hCH (mem_Cen_self z)⟩ ∈ generalizedFitting (HBar H))
      (B₁ B₂ : Subgroup (HBar H)), B₁ ≤ generalizedFitting (HBar H) ∧
      B₂ ≤ generalizedFitting (HBar H) ∧ B₁ ≤ barIn H (Cen z) ∧ B₂ ≤ barIn H (Cen z) ∧
      (B₁.subgroupOf (barIn H (Cen z))).map (cenToBar H hCH) = L₁ ∧
      (B₂.subgroupOf (barIn H (Cen z))).map (cenToBar H hCH) = L₂ ∧
      Ivk93Cfg2 (⟨mkH H ⟨z, hCH (mem_Cen_self z)⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) r₁ r₂
        (B₁.subgroupOf (generalizedFitting (HBar H))) (B₂.subgroupOf (generalizedFitting (HBar H))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzmem : z ∈ H := hCH (mem_Cen_self z)
  set x : HBar H := mkH H ⟨z, hzmem⟩ with hx
  set C' : Subgroup (HBar H) := barIn H (Cen z) with hC'
  have hzbar := zbarC_mem_inf2 hp
  obtain ⟨B₁, hB₁J, hB₁C, hxB₁, hB₁comp, hB₁map⟩ := lift_comp hz2 hCH hPerf hp.comp₁ hzbar.1
  obtain ⟨B₂, hB₂J, hB₂C, hxB₂, hB₂comp, hB₂map⟩ := lift_comp hz2 hCH hPerf hp.comp₂ hzbar.2
  have hxJ : x ∈ generalizedFitting (HBar H) := hB₁J hxB₁
  have hx2 : orderOf x = 2 := orderOf_mk_eq_two H (by rw [← Subgroup.orderOf_coe]; exact hz2)
  have hcent : centralizer ({x} : Set (HBar H)) = C' := centralizer_mk_eq H hz2 hzmem
  have hcJ := centralizer_singleton_subgroupOf (J := generalizedFitting (HBar H)) hxJ
  rw [hcent] at hcJ
  have hr₁ : 5 ≤ r₁ := by
    obtain ⟨m, hm⟩ := hp.odd₁
    have := hp.gt₁
    omega
  have hr₂ : 5 ≤ r₂ := by
    obtain ⟨m, hm⟩ := hp.odd₂
    have := hp.gt₂
    omega
  have hodd : ∀ y ∈ (cenToBar H hCH).ker, Odd (orderOf y) := fun y hy =>
    odd_orderOf_of_cenToBar_eq_one H hCH y hy
  have comp : ∀ {B : Subgroup (HBar H)}, B ≤ generalizedFitting (HBar H) → B ≤ C' →
      IsPComponent 2 (B.subgroupOf C') →
      IsPCompIn 2 (centralizer ({(⟨x, hxJ⟩ : ↥(generalizedFitting (HBar H)))} :
        Set ↥(generalizedFitting (HBar H)))) (B.subgroupOf (generalizedFitting (HBar H))) := by
    intro B hBJ hBC h
    rw [hcJ]
    exact ⟨fun y hy => hBC hy, ComponentClassification.Sp4Rec.isPComponent_subgroupOf_restrict hBC hBJ h⟩
  have sl : ∀ {B : Subgroup (HBar H)} {L : Subgroup (CentralizerBar z)} {r : ℕ},
      Odd r → 5 ≤ r →
      B ≤ generalizedFitting (HBar H) → B ≤ C' → (B.subgroupOf C').map (cenToBar H hCH) = L →
      HasSL2Model ↥L (fun s => s = r) →
      HasSL2Model (↥(B.subgroupOf (generalizedFitting (HBar H))) ⧸
        pPrimeCore 2 ↥(B.subgroupOf (generalizedFitting (HBar H)))) (fun s => s = r) := by
    intro B L r hr h5 hBJ hBC hmap hsl
    exact hasSL2Model_quot_of_equiv
      ((Subgroup.subgroupOfEquivOfLe hBC).trans (Subgroup.subgroupOfEquivOfLe hBJ).symm)
      (hasSL2Model_quot_of_hom (cenToBar H hCH) hodd hmap hr h5 hsl)
  refine ⟨hxJ, B₁, B₂, hB₁J, hB₂J, hB₁C, hB₂C, hB₁map, hB₂map, ?_, hp.odd₁, hp.odd₂, hr₁, hr₂, ?_,
    comp hB₁J hB₁C hB₁comp, comp hB₂J hB₂C hB₂comp,
    Subgroup.mem_subgroupOf.2 hxB₁, Subgroup.mem_subgroupOf.2 hxB₂,
    sl hp.odd₁ hr₁ hB₁J hB₁C hB₁map hp.sl₁, sl hp.odd₂ hr₂ hB₂J hB₂C hB₂map hp.sl₂⟩
  · rw [← Subgroup.orderOf_coe]
    exact hx2
  · intro h
    have hB : B₁ = B₂ := by
      ext y
      constructor
      · intro hy
        have : (⟨y, hB₁J hy⟩ : ↥(generalizedFitting (HBar H))) ∈ B₁.subgroupOf _ :=
          Subgroup.mem_subgroupOf.2 hy
        rw [h] at this
        exact Subgroup.mem_subgroupOf.1 this
      · intro hy
        have : (⟨y, hB₂J hy⟩ : ↥(generalizedFitting (HBar H))) ∈ B₂.subgroupOf _ :=
          Subgroup.mem_subgroupOf.2 hy
        rw [← h] at this
        exact Subgroup.mem_subgroupOf.1 this
    apply hp.ne
    rw [← hB₁map, ← hB₂map, hB]

end Lift2

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
