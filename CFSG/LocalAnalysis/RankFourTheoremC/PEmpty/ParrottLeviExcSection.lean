module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs
public import CFSG.LieType.Chevalley.EvenTorusRank
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardQuasisimple

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

section General

variable {X : Type} [Group X]

theorem subgroupOf_map_subtype_eq_self (Y : Subgroup X) (Z : Subgroup ↥Y) :
    (Z.map Y.subtype).subgroupOf Y = Z :=
  Subgroup.comap_map_eq_self_of_injective Subtype.val_injective Z

theorem s622IsSimpleSection_center_of_isQuasisimple {Y : Subgroup X}
    (hY : CFSG.IsQuasisimple ↥Y) :
    S622IsSimpleSection Y ((Subgroup.center ↥Y).map Y.subtype) := by
  obtain ⟨-, hsimple, a, b, hab⟩ := hY
  haveI := hsimple
  have hsub := subgroupOf_map_subtype_eq_self Y (Subgroup.center ↥Y)
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · rw [hsub]
    infer_instance
  · intro h
    apply hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    have ha' : a' ∈ Subgroup.center ↥Y := by
      have hmem : (a' : X) ∈ (Subgroup.center ↥Y).map Y.subtype := by
        rw [h]
        exact a'.2
      obtain ⟨z, hz, hza⟩ := hmem
      rwa [← Subtype.ext hza]
    rw [(QuotientGroup.eq_one_iff a').2 ha', one_mul, mul_one]
  · intro N hDN hNY hNnorm
    haveI : (N.subgroupOf Y).Normal := hNnorm
    have hZM : Subgroup.center ↥Y ≤ N.subgroupOf Y := fun z hz => hDN ⟨z, hz, rfl⟩
    haveI : ((N.subgroupOf Y).map (QuotientGroup.mk' (Subgroup.center ↥Y))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    have hM : N.subgroupOf Y =
        ((N.subgroupOf Y).map (QuotientGroup.mk' (Subgroup.center ↥Y))).comap
          (QuotientGroup.mk' (Subgroup.center ↥Y)) := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hZM]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((N.subgroupOf Y).map (QuotientGroup.mk' (Subgroup.center ↥Y))) with h | h
    · left
      rw [h, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hM
      rw [← Subgroup.map_subgroupOf_eq_of_le hNY, hM]
    · right
      rw [h, Subgroup.comap_top, Subgroup.subgroupOf_eq_top] at hM
      exact le_antisymm hNY hM
  · intro h
    apply hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨z, hz, hzeq⟩ := h a' a'.2 b' b'.2
    have hz' : (a' * b' * a'⁻¹ * b'⁻¹ : ↥Y) ∈ Subgroup.center ↥Y := by
      have hzy : z = a' * b' * a'⁻¹ * b'⁻¹ := Subtype.ext hzeq
      rwa [← hzy]
    have h1 := (QuotientGroup.eq_one_iff _).2 hz'
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem relIndex_center_map (Y : Subgroup X) :
    ((Subgroup.center ↥Y).map Y.subtype).relIndex Y = Nat.card (↥Y ⧸ Subgroup.center ↥Y) := by
  rw [Subgroup.relIndex, subgroupOf_map_subtype_eq_self, Subgroup.index_eq_card]

end General

section Chevalley

variable {τ : Tag} {K : Type} [Field K]


theorem not_dvd_card_center_subsystemGroup [Finite K] {C : Set (Fin τ.rank)} {p : ℕ}
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card Kˣ) :
    ¬ p ∣ Nat.card (Subgroup.center ↥(subsystemGroup τ K C)) := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL τ K) := finite_modGL
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  apply hpK
  have hzT : ((z : ↥(subsystemGroup τ K C)) : ModGL τ K) ∈ subsystemTorus τ K C :=
    center_le_subsystemTorus ⟨(z : ↥(subsystemGroup τ K C)), z.2, rfl⟩
  have h1 := EvenTorusRank.pow_card_units_eq_one_of_mem_subsystemTorus hzT
  have h2 : orderOf z ∣ Nat.card Kˣ := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (Subtype.ext h1)
  rwa [hz] at h2

theorem card_sl2_dvd_card_quotient_center [Finite K] [CharP K 2] {C : Set (Fin τ.rank)}
    {i : Fin τ.rank} (hi : i ∈ C) :
    Nat.card (SL2 K) ∣
      Nat.card (↥(subsystemGroup τ K C) ⧸ Subgroup.center ↥(subsystemGroup τ K C)) := by
  have hrange : (simpleRootSL2 τ K i).range ≤ subsystemGroup τ K C := by
    rw [range_simpleRootSL2, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact xUnit_mem_subsystemGroup hi c
    · exact yUnit_mem_subsystemGroup hi c
  let ψ : SL2 K →* ↥(subsystemGroup τ K C) :=
    (simpleRootSL2 τ K i).codRestrict _ fun A => hrange ⟨A, rfl⟩
  have hψ : Function.Injective ψ := fun A B h =>
    simpleRootSL2_injective_of_charTwo i (congrArg Subtype.val h)
  refine Subgroup.card_dvd_of_injective
    ((QuotientGroup.mk' (Subgroup.center ↥(subsystemGroup τ K C))).comp ψ) ?_
  rw [injective_iff_map_eq_one]
  intro A hA
  have hcent : ψ A ∈ Subgroup.center ↥(subsystemGroup τ K C) :=
    (QuotientGroup.eq_one_iff _).1 hA
  have hAc : A ∈ Subgroup.center (SL2 K) := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply hψ
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hcent (ψ B)
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hAc
  rw [Fintype.card_fin, pow_two] at hr
  rw [eq_one_of_mul_self_eq_one_of_charTwo hr, map_one] at hrA
  exact Subtype.ext hrA.symm

end Chevalley

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc
