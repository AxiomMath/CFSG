module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Cover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped commutatorElement

@[expose] def U43OddAutTwoPlusCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsTwoU43 (X ⧸ oddCore X) →
    ∀ Q₁ Q₂ : Subgroup X,
      Nonempty (↥Q₁ ≃* QuaternionGroup 2) → Nonempty (↥Q₂ ≃* QuaternionGroup 2) →
      ⁅Q₁, Q₂⁆ = ⊥ → Nat.card ↥(Q₁ ⊔ Q₂) = 32 → (Q₁ ⊔ Q₂) ⊓ Subgroup.center X = ⊥ →
      ∀ α : MulAut X, Odd (orderOf α) → (∀ q ∈ Q₁ ⊔ Q₂, α q = q) →
        ∀ x : X,
          QuotientGroup.mk (s := oddCore X) (α x) = QuotientGroup.mk (s := oddCore X) x

theorem asc82FactQCent6_of_finite (hfin : U43OddAutTwoPlusCent) : Asc82FactQCent6 := by
  intro G _ _ L hL Q₁ Q₂ hQ₁L hQ₂L hQ₁ hQ₂ hcomm hcard hinter Y hYodd hYN hYcent
  unfold U43OddAutTwoPlusCent at hfin
  have hq : IsQuasisimple ↥L := hL.1
  have htwo : IsTwoU43 (↥L ⧸ oddCore ↥L) := hL.2
  have hOZ : oddCore ↥L ≤ Subgroup.center ↥L :=
    CFSG.EvenSporadicStandard.Induction.oddCore_le_center_of_isQuasisimple hq
  have hOZ' : oddCoreIn L ≤ centerIn L := by
    rw [oddCoreIn, centerIn, CFSG.inSubgroup]
    exact Subgroup.map_mono hOZ
  have hcenter_le_cent : centerIn L ≤ centralizer (L : Set G) := by
    rintro x ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
  have hQ₁' : Nonempty (↥(Q₁.subgroupOf L) ≃* QuaternionGroup 2) :=
    hQ₁.elim fun e => ⟨(Subgroup.subgroupOfEquivOfLe hQ₁L).trans e⟩
  have hQ₂' : Nonempty (↥(Q₂.subgroupOf L) ≃* QuaternionGroup 2) :=
    hQ₂.elim fun e => ⟨(Subgroup.subgroupOfEquivOfLe hQ₂L).trans e⟩
  have hcomm' : ⁅Q₁.subgroupOf L, Q₂.subgroupOf L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    ext
    exact Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
        (Subgroup.mem_subgroupOf.mp ha)) (b : G) (Subgroup.mem_subgroupOf.mp hb)
  have hcard' : Nat.card ↥((Q₁.subgroupOf L) ⊔ (Q₂.subgroupOf L)) = 32 := by
    rw [← Subgroup.subgroupOf_sup hQ₁L hQ₂L,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hQ₁L hQ₂L)).toEquiv]
    exact hcard
  have hinter' : ((Q₁.subgroupOf L) ⊔ (Q₂.subgroupOf L)) ⊓ Subgroup.center ↥L = ⊥ := by
    rw [← Subgroup.subgroupOf_sup hQ₁L hQ₂L]
    ext z
    constructor
    · intro hz
      have hzK : (z : G) ∈ Q₁ ⊔ Q₂ := hz.1
      have hzC : (z : G) ∈ centerIn L := by
        rw [centerIn]
        exact Subgroup.mem_map_of_mem L.subtype hz.2
      have hzbot : (z : G) ∈ (⊥ : Subgroup G) := by
        rw [← hinter]
        exact ⟨hzK, hzC⟩
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hzbot))
    · intro hz
      rw [Subgroup.mem_bot] at hz
      rw [hz]
      exact Subgroup.one_mem _
  have hcomm_mem : ∀ y ∈ Y, ∀ x ∈ L, ⁅y, x⁆ ∈ oddCoreIn L := by
    intro y hy x hx
    let α : MulAut ↥L := L.normalizerMonoidHom ⟨y, hYN hy⟩
    have hαdvd : orderOf α ∣ orderOf y := by
      calc orderOf α ∣ orderOf (⟨y, hYN hy⟩ : ↥(normalizer (L : Set G))) :=
            orderOf_map_dvd L.normalizerMonoidHom ⟨y, hYN hy⟩
        _ = orderOf y := (Subgroup.orderOf_coe _).symm
    have hoddα : Odd (orderOf α) :=
      (hYodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hy)).of_dvd_nat hαdvd
    have hfix : ∀ q ∈ Q₁.subgroupOf L ⊔ Q₂.subgroupOf L, α q = q := by
      let Fix : Subgroup ↥L :=
        { carrier := {q | α q = q}
          mul_mem' := fun {a b} ha hb => by
            have ha' : α a = a := ha
            have hb' : α b = b := hb
            change α (a * b) = a * b
            rw [map_mul, ha', hb']
          one_mem' := map_one α
          inv_mem' := fun {a} ha => by
            have ha' : α a = a := ha
            change α a⁻¹ = a⁻¹
            rw [map_inv, ha'] }
      have hfix1 : Q₁.subgroupOf L ≤ Fix := by
        intro a ha
        have hqa : y * (a : G) = (a : G) * y :=
          (Subgroup.mem_centralizer_iff.mp (hYcent hy) (a : G)
            (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha))).symm
        show α a = a
        apply Subtype.ext
        calc ((α a : ↥L) : G) = y * (a : G) * y⁻¹ := by simp [α]
          _ = (a : G) * y * y⁻¹ := by rw [hqa]
          _ = (a : G) := by group
      have hfix2 : Q₂.subgroupOf L ≤ Fix := by
        intro b hb
        have hqb : y * (b : G) = (b : G) * y :=
          (Subgroup.mem_centralizer_iff.mp (hYcent hy) (b : G)
            (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hb))).symm
        show α b = b
        apply Subtype.ext
        calc ((α b : ↥L) : G) = y * (b : G) * y⁻¹ := by simp [α]
          _ = (b : G) * y * y⁻¹ := by rw [hqb]
          _ = (b : G) := by group
      intro q hq
      exact (sup_le hfix1 hfix2) hq
    have hquot : ∀ z : ↥L,
        QuotientGroup.mk (s := oddCore ↥L) (α z) =
          QuotientGroup.mk (s := oddCore ↥L) z :=
      hfin (↥L) hq htwo (Q₁.subgroupOf L) (Q₂.subgroupOf L) hQ₁' hQ₂'
        hcomm' hcard' hinter' α hoddα hfix
    have hdiv : (α ⟨x, hx⟩ / ⟨x, hx⟩ : ↥L) ∈ oddCore ↥L :=
      QuotientGroup.eq_iff_div_mem.mp (hquot ⟨x, hx⟩)
    have hmem : L.subtype (α ⟨x, hx⟩ / ⟨x, hx⟩) ∈ (oddCore ↥L).map L.subtype :=
      Subgroup.mem_map_of_mem L.subtype hdiv
    rw [oddCoreIn, CFSG.inSubgroup]
    convert hmem using 1
    simp [α, div_eq_mul_inv, commutatorElement_def]
  have hYL : ⁅Y, L⁆ ≤ oddCoreIn L :=
    Subgroup.commutator_le.mpr hcomm_mem
  have hYLcenter : ⁅Y, L⁆ ≤ centerIn L := hYL.trans hOZ'
  have h2 : ⁅⁅Y, L⁆, L⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hYLcenter.trans hcenter_le_cent)
  have h1 : ⁅⁅L, Y⁆, L⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm L Y]
  haveI : Group.IsPerfect ↥L := hq.1
  have h3 : ⁅⁅L, L⁆, Y⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [Subgroup.commutator_eq_self] at h3
  have hYLbot : ⁅Y, L⁆ = ⊥ := by
    rwa [← Subgroup.commutator_comm Y L] at h3
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hYLbot

end CFSG.OddStandard.SmallF3.Omega
