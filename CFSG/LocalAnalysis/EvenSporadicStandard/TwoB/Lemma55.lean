module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Branch55
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.XStruct
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Co2Lift
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Act55
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Normal55
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Extraspecial

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

section Branch

variable [Finite G] {t z : G}

section Certified

theorem Level55.false_of_P_le (d : Level55 G t z) (h54 : IsTwoConstrained (centZ z))
    (hnc : ¬ centZ z ≤ centralizer ({t} : Set G)) (hPR : Psub z ≤ O2In (centPair z t)) :
    False := by
  have hA := d.O2K_le_P h54
  have hPeq : O2In (centPair z t) = Psub z := le_antisymm hA hPR
  have hKC : centPair z t ≤ centZ z := centPair_le_centZ z t
  have hPC : Psub z ≤ centZ z := O2In_le _
  have hCN : ∀ g ∈ centZ z, g ∈ normalizer ((O2In (centPair z t) : Subgroup G) : Set G) := by
    intro g hg
    rw [hPeq]
    exact mem_normalizer_O2In hg
  have hCz : ∀ g ∈ centZ z, g * z = z * g := fun g hg => mem_centralizer_singleton_iff.1 hg
  have hzz := d.z_mul_self
  have hKiff : ∀ g ∈ centZ z, (g ∈ centPair z t ↔ g * t * g⁻¹ = t) := by
    intro g hg
    rw [mem_centPair_iff]
    constructor
    · rintro ⟨-, h2⟩
      rw [← h2, mul_inv_cancel_right]
    · intro h
      refine ⟨(hCz g hg).symm, ?_⟩
      calc t * g = (g * t * g⁻¹) * g := by rw [h]
        _ = g * t := by group
  obtain ⟨c, hcC, hcnot⟩ := IsConcreteLE.not_le_iff_exists.1 hnc
  have hct : c * t * c⁻¹ = t * z := by
    rcases d.conj_t_eq_or (hCN c hcC) (hCz c hcC) with h | h
    · exfalso
      exact hcnot (centPair_le_centralizer z t ((hKiff c hcC).2 h))
    · exact h
  have hbz : ∀ b ∈ centZ z, b * z * b⁻¹ = z := fun b hb => by
    rw [hCz b hb, mul_inv_cancel_right]
  have hmul : ∀ b ∈ centZ z, (b * c) * t * (b * c)⁻¹ = (b * t * b⁻¹) * z := by
    intro b hb
    calc (b * c) * t * (b * c)⁻¹ = b * (c * t * c⁻¹) * b⁻¹ := by group
      _ = b * (t * z) * b⁻¹ := by rw [hct]
      _ = (b * t * b⁻¹) * (b * z * b⁻¹) := by group
      _ = (b * t * b⁻¹) * z := by rw [hbz b hb]
  have htz_ne : t * z ≠ t := fun h => by
    have h1 : z = 1 := mul_left_cancel (a := t) (h.trans (mul_one t).symm)
    have h2 := d.z_ord
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hidx : (centPair z t).relIndex (centZ z) = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨c, hcC⟩, fun b => ?_⟩
    have hb := b.2
    rcases d.conj_t_eq_or (hCN b hb) (hCz b hb) with h | h
    · right
      refine ⟨mem_subgroupOf.2 ((hKiff b hb).2 h), fun hbc => ?_⟩
      have h1 := (hKiff (b * c) (mul_mem hb hcC)).1 (mem_subgroupOf.1 hbc)
      rw [hmul b hb, h] at h1
      exact htz_ne h1
    · left
      refine ⟨mem_subgroupOf.2 ((hKiff (b * c) (mul_mem hb hcC)).2 ?_), fun hbK => ?_⟩
      · rw [hmul b hb, h, mul_assoc, hzz, mul_one]
      · have h1 := (hKiff b hb).1 (mem_subgroupOf.1 hbK)
        rw [h] at h1
        exact htz_ne h1
  obtain ⟨e⟩ := d.quot
  have hRC : ((O2In (centPair z t)).subgroupOf (centZ z)).Normal := by
    rw [hPeq]
    exact normal_subgroupOf_O2In (centZ z)
  obtain ⟨x, hxC, hxK, hxcomm, hx2⟩ := exists_lift_centralizing_co2 hKC hidx hRC e
  have hxz := hCz x hxC
  have hxN := hCN x hxC
  have hxt : x * t * x⁻¹ = t * z := by
    rcases d.conj_t_eq_or hxN hxz with h | h
    · exact absurd ((hKiff x hxC).2 h) hxK
    · exact h
  have hxn : x ∉ O2In (centPair z t) := fun h => hxK (O2In_le _ h)
  have hxR := d.comm_mem_zpowers hxz hxt hxN hxcomm hx2
  have hxinv : x⁻¹ * t * x = t * z := by
    have hxz' : x⁻¹ * z * x = z := by
      calc x⁻¹ * z * x = x⁻¹ * (z * x) := by rw [mul_assoc]
        _ = x⁻¹ * (x * z) := by rw [hxz]
        _ = z := by group
    have h1 : t = (x⁻¹ * t * x) * z := by
      calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
        _ = x⁻¹ * (t * z) * x := by rw [hxt]
        _ = (x⁻¹ * t * x) * (x⁻¹ * z * x) := by group
        _ = (x⁻¹ * t * x) * z := by rw [hxz']
    calc x⁻¹ * t * x = (x⁻¹ * t * x) * 1 := (mul_one _).symm
      _ = (x⁻¹ * t * x) * (z * z) := by rw [hzz]
      _ = ((x⁻¹ * t * x) * z) * z := by rw [← mul_assoc]
      _ = t * z := by rw [← h1]
  have hxz' : x⁻¹ * z * x = z := by
    calc x⁻¹ * z * x = x⁻¹ * (z * x) := by rw [mul_assoc]
      _ = x⁻¹ * (x * z) := by rw [hxz]
      _ = z := by group
  have hgK : ∀ g ∈ centPair z t, g * x * g⁻¹ ∈ O2In (centPair z t) ⊔ zpowers x := by
    intro g hg
    have h1 := inv_mem (hxcomm g hg)
    have e : (x * g * x⁻¹ * g⁻¹)⁻¹ * x = g * x * g⁻¹ := by group
    rw [← e]
    exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers x))
  have hgC : ∀ g ∈ centZ z, g * x * g⁻¹ ∈ O2In (centPair z t) ⊔ zpowers x := by
    intro g hg
    rcases d.conj_t_eq_or (hCN g hg) (hCz g hg) with h | h
    · exact hgK g ((hKiff g hg).2 h)
    · have hg' : x⁻¹ * g ∈ centPair z t := by
        refine (hKiff _ (mul_mem (inv_mem hxC) hg)).2 ?_
        calc x⁻¹ * g * t * (x⁻¹ * g)⁻¹ = x⁻¹ * (g * t * g⁻¹) * x := by group
          _ = x⁻¹ * (t * z) * x := by rw [h]
          _ = (x⁻¹ * t * x) * (x⁻¹ * z * x) := by group
          _ = (t * z) * z := by rw [hxinv, hxz']
          _ = t := by rw [mul_assoc, hzz, mul_one]
      have h1 := hgK (x⁻¹ * g) hg'
      have e : g * x * g⁻¹ = x * ((x⁻¹ * g) * x * (x⁻¹ * g)⁻¹) * x⁻¹ := by group
      rw [e]
      refine conj_mem_sup_of_invariant (A := O2In (centPair z t)) (B := zpowers x) (k := x)
        (fun a ha => (mem_normalizer_iff.1 hxN a).1 ha) (fun b hb => ?_) _ h1
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
      have hc : x * x ^ j = x ^ j * x := (Commute.zpow_right (Commute.refl x) j).eq
      rw [hc, mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers x) j
  have key : ∀ g ∈ centZ z, ∀ n ∈ O2In (centPair z t) ⊔ zpowers x,
      g * n * g⁻¹ ∈ O2In (centPair z t) ⊔ zpowers x := by
    intro g hg n hn
    have hle : (O2In (centPair z t) ⊔ zpowers x).map (MulAut.conj g).toMonoidHom ≤
        O2In (centPair z t) ⊔ zpowers x := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      refine sup_le ?_ (zpowers_le.2 (hgC g hg))
      rintro _ ⟨a, ha, rfl⟩
      exact mem_sup_left ((mem_normalizer_iff.1 (hCN g hg) a).1 ha)
    exact hle ⟨n, hn, rfl⟩
  have hUC : O2In (centPair z t) ⊔ zpowers x ≤ centZ z :=
    sup_le (O2In_le _ |>.trans hKC) (zpowers_le.2 hxC)
  have hUn : ((O2In (centPair z t) ⊔ zpowers x).subgroupOf (centZ z)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    exact key g g.2 n hn
  have hxn' : x ∉ d.R0 ⊔ zpowers t := d.O2K ▸ hxn
  have hU := isExtraspecialPGroup_sup_zpowers_of_acts d.z_ord d.t_ord d.R0_ext d.R0_card
    d.R0_center (fun r hr => d.R0_comm_t hr) d.t_not_mem hxz hxt
    (by rw [← d.O2K]; exact hxR) (by rw [← d.O2K]; exact hx2) hxn'
  have hUp : IsPGroup 2 ↥(O2In (centPair z t) ⊔ zpowers x) := by
    rw [d.O2K]
    exact hU.1.1
  have hle := le_O2In hUC hUn hUp
  exact hxn (hPeq ▸ hle (mem_sup_right (mem_zpowers x)))

theorem Level55.rsub_structure (d : Level55 G t z) (h54 : IsTwoConstrained (centZ z))
    (hnc : ¬ centZ z ≤ centralizer ({t} : Set G)) :
    CFSG.IsExtraspecialPGroup 2 ↥(Rsub z t) ∧ Nat.card (Rsub z t) = 2 ^ 25 ∧
      Rsub z t ≤ Psub z := by
  have hA := d.O2K_le_P h54
  have hlt : O2In (centPair z t) < Psub z := by
    refine lt_of_le_of_ne hA (fun hEq => ?_)
    exact d.false_of_P_le h54 hnc hEq.ge
  obtain ⟨x, hxP, hxn, hxz, hxt, hxN, hxK, hx2⟩ := d.exists_x_of_lt hlt
  have hxR := d.comm_mem_zpowers hxz hxt hxN hxK hx2
  have hN := d.O2In_normPair_eq h54 hxz hxt hxN hxK hx2 hxn
  have hxn' : x ∉ d.R0 ⊔ zpowers t := d.O2K ▸ hxn
  obtain ⟨hU, hcardU, -⟩ := isExtraspecialPGroup_sup_zpowers_of_acts d.z_ord d.t_ord d.R0_ext
    d.R0_card d.R0_center (fun r hr => d.R0_comm_t hr) d.t_not_mem hxz hxt
    (by rw [← d.O2K]; exact hxR) (by rw [← d.O2K]; exact hx2) hxn'
  have hR : Rsub z t = d.R0 ⊔ zpowers t ⊔ zpowers x := by
    show O2In (normPair z t) = _
    rw [hN, d.O2K]
  refine ⟨?_, ?_, ?_⟩
  · rw [hR]; exact hU
  · rw [hR]; exact hcardU
  · rw [hR]
    exact sup_le (d.O2K ▸ hA) (zpowers_le.2 hxP)

end Certified

end Branch

@[expose] def DS81Lemma55CentralizerEq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t z : G),
    Setting G L t → CentralPair G L t z → IsTwoConstrained (centZ z) →
      centralizer ({t} : Set G) = L

@[expose] def DS81Lemma55Fusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t z : G),
    Setting G L t → CentralPair G L t z → IsTwoConstrained (centZ z) →
      centralizer ({t} : Set G) = L → ¬ centZ z ≤ centralizer ({t} : Set G)

section Assembly

theorem ds81Lemma55_of_residuals (h1 : DS81Lemma55CentralizerEq) (h2 : DS81Lemma55Fusion) :
    DS81Lemma55 := by
  intro G _ _ L t z h hc h54
  have hCt := h1 G L t z h hc h54
  have hnc := h2 G L t z h hc h54 hCt
  obtain ⟨d⟩ := h.exists_level55 hc hCt
  obtain ⟨hext, hcard, hle⟩ := d.rsub_structure h54 hnc
  exact ⟨hCt, d.O2K_le_P h54, hext, hcard, hle⟩

end Assembly

end CFSG.EvenSporadicStandard.TwoB
