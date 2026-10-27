module

public import CFSG.Yardstones.Md42047359a2a.Definitions
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallReeDescent
import CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.ReeG2Outer
import CFSG.RankThree.Chevalley.SteinbergCFSmallReeComponentCores
public import CFSG.LieType.Ree.Duality

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter

open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

private theorem isQuasisimple_of_simple_nonab {L : Type*} [Group L] (hs : IsSimpleGroup L)
    (hnc : ∃ a b : L, a * b ≠ b * a) : CFSG.IsQuasisimple L := by
  haveI := hs
  have hc : Subgroup.center L = ⊥ := by
    rcases (inferInstance : (Subgroup.center L).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  refine ⟨?_,
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup, ?_⟩
  · refine Group.isPerfect_def.mpr ?_
    rcases (inferInstance : (commutator L).Normal).eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have hmem : ⁅a, b⁆ ∈ commutator L :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hab hmem
    · exact h
  · obtain ⟨a, b, hab⟩ := hnc
    refine ⟨(a : L ⧸ Subgroup.center L), (b : L ⧸ Subgroup.center L), fun h => hab ?_⟩
    have := (QuotientGroup.eq (s := Subgroup.center L) (a := a * b) (b := b * a)).mp (by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, h])
    rw [hc, Subgroup.mem_bot] at this
    exact inv_mul_eq_one.mp this

private theorem perfectInLayer_of_commutator_simple {S : Type*} [Group S] [Finite S]
    (β : MulAut S) {Γ' : Type*} [Group Γ'] (e : ↥(fixSubgroup β) ≃* Γ')
    (hs : IsSimpleGroup ↥(commutator Γ')) (hnc : ∃ x y : ↥(commutator Γ'), x * y ≠ y * x) :
    PerfectInLayer β := by
  set C := fixSubgroup β with hC
  have hmap : (commutator ↥C).map e.toMonoidHom = commutator Γ' := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  let eN : ↥(commutator ↥C) ≃* ↥(commutator Γ') :=
    ((commutator ↥C).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hsC : IsSimpleGroup ↥(commutator ↥C) := eN.isSimpleGroup
  have hncC : ∃ x y : ↥(commutator ↥C), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eN.symm x, eN.symm y, fun h => hxy (by simpa using congrArg eN h)⟩
  let N : Subgroup S := (commutator ↥C).map C.subtype
  have hNC : N.subgroupOf C = commutator ↥C :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  let eN' : ↥(commutator ↥C) ≃* ↥N :=
    (commutator ↥C).equivMapOfInjective C.subtype C.subtype_injective
  have hNn : (N.subgroupOf C).Normal := by rw [hNC]; infer_instance
  refine CFSG.HardMathSupport.Dickson.SuzukiReeB.perfectInLayer_of_normal_quasisimple β
    (N := N) (Subgroup.map_subtype_le _) hNn ?_ ?_
  · haveI := hsC
    have hsN : IsSimpleGroup ↥N := eN'.symm.isSimpleGroup
    have hncN : ∃ x y : ↥N, x * y ≠ y * x := by
      obtain ⟨x, y, hxy⟩ := hncC
      exact ⟨eN' x, eN' y, fun h => hxy (by simpa using congrArg eN'.symm h)⟩
    exact isQuasisimple_of_simple_nonab hsN hncN
  · refine Group.isSolvable_of_comm fun x y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hNC]
    have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [h1, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem mulAut_congr_conj {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.conj_apply]

section Outer


open CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification CFSG.RankThree.PartOne.Sec66T

private theorem perfectInLayer_reeGamma_outer {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {β : MulAut (ReeTag.G2.reeGamma K a)} (hβ : β ^ p = 1)
    (hin : β ∉ (MulAut.conj : ReeTag.G2.reeGamma K a →* MulAut (ReeTag.G2.reeGamma K a)).range) :
    PerfectInLayer β := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, δ, σ, hσord, hδ, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent a ha K hK hp hp2 β
      hβ hin
  obtain ⟨b, -, hbcard, hchar, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.reeG2_fixed_data hK hp hp2 hσord
  haveI := hchar
  obtain ⟨hs, hnc, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components b
      (fixSubfield σ) hbcard
  have hfix : fixSubgroup (ReeTag.G2.reeGammaFieldAut K a σ) =
      fixSub (ReeTag.G2.reeGammaFieldAut K a σ) :=
    Subgroup.ext fun y => by rw [mem_fixSubgroup, mem_fixSub]
  have hσ : PerfectInLayer (ReeTag.G2.reeGammaFieldAut K a σ) :=
    perfectInLayer_of_commutator_simple _ ((MulEquiv.subgroupCongr hfix).trans eC) hs hnc
  have h2 := LieSemisimple.perfectInLayer_conj δ⁻¹ _ hσ
  rwa [← hδ, show δ⁻¹ * (δ * β * δ⁻¹) * δ⁻¹⁻¹ = β by group] at h2

private theorem perfectInLayer_reeG2_outer (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid)
    {S : Type} [Group S]
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {β : MulAut S} (hβ : β ^ p = 1)
    (hout : ∀ a : S, MulAut.conj a ≠ β) : PerfectInLayer β := by
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_reeGamma_G2_of_reeTitsModel
      (CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, he⟩)
  refine LieSemisimple.perfectInLayer_of_congr e β ?_
  refine perfectInLayer_reeGamma_outer ha K hK hp hp2 ?_ ?_
  · rw [← map_pow, hβ, map_one]
  · rintro ⟨g, hg⟩
    apply hout (e.symm g)
    apply (MulAut.congr e).injective
    rw [mulAut_congr_conj, e.apply_symm_apply]
    exact hg

end Outer

theorem lieDefCharOuter_suzukiReeTits
    (idx : TauCeti.ValidLieTypeIndex)
    (hfam : CFSG.Yardstones.Md42047359a2a.lieFamily idx.1 =
        CFSG.Yardstones.Md42047359a2a.LieFamily.suzukiReeTits)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p = idx.1.characteristic)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β ∨ CFSG.Open.GLAPPrimeCoreOf p (fixSubgroup β) = ⊥ := by
  left
  obtain ⟨d, hv⟩ := idx
  cases d with
  | suzuki m => exact absurd (hpc.trans (TauCeti.LieTypeIndex.characteristic_suzuki m)) hp2
  | reeG2 m =>
    have h3 : p = 3 := hpc.trans (TauCeti.LieTypeIndex.characteristic_reeG2 m)
    subst h3
    exact perfectInLayer_reeG2_outer m hv he hp hp2 hβ hout
  | reeF4 m => exact absurd (hpc.trans (TauCeti.LieTypeIndex.characteristic_reeF4 m)) hp2
  | tits => exact absurd (hpc.trans TauCeti.LieTypeIndex.characteristic_tits) hp2
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hfam

end CFSG.HardMathSupport.Dickson.DefCharOuter
