module

public import CFSG.HardMathSupport.Dickson.Bal207.CompShape
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeF4
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4ElementCentralizer
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open scoped commutatorElement

theorem excRee_map_fixSubgroup_of_commute {S : Type} [Group S] (β ω : MulAut S)
    (hω : ω * β = β * ω) : (fixSubgroup β).map ω.toMonoidHom = fixSubgroup β := by
  have hcomm : ∀ x, ω (β x) = β (ω x) := fun x => congrArg (fun φ : MulAut S => φ x) hω
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : β x = x := hx
    show β (ω x) = ω x
    rw [← hcomm, hx']
  · intro hy
    have hy' : β y = y := hy
    refine ⟨ω.symm y, ?_, ω.apply_symm_apply y⟩
    show β (ω.symm y) = ω.symm y
    apply ω.injective
    rw [hcomm, ω.apply_symm_apply]
    exact hy'

theorem excRee_compShape_of_unique {T : ∀ (Q : Type) [Group Q], Prop} {S : Type} [Group S]
    (β : MulAut S) (N : Subgroup S) (hlayer : PerfectInLayer β)
    (hall : ∀ L : Subgroup S, CFSG.Open.IsComponentOf L (fixSubgroup β) → L = N)
    (hT : T (↥N ⧸ Subgroup.center ↥N)) : CompShape T β where
  layer := hlayer
  type := fun L hL => by
    rw [hall L hL]
    exact hT
  norm := fun ω hω L hL => by
    have h1 : CFSG.Open.IsComponentOf (L.map ω.toMonoidHom) ((fixSubgroup β).map ω.toMonoidHom) :=
      CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (ω : S ≃* S) hL
    rw [excRee_map_fixSubgroup_of_commute β ω hω] at h1
    rw [hall _ h1, hall L hL]

theorem excRee_normal_of_commutator_le {G : Type*} [Group G] {H : Subgroup G}
    (h : commutator G ≤ H) : H.Normal :=
  ⟨fun n hn g => by
    have h1 : ⁅g, n⁆ ∈ H :=
      h (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    have h2 : g * n * g⁻¹ = ⁅g, n⁆ * n := by simp [commutatorElement_def]
    rw [h2]
    exact H.mul_mem h1 hn⟩

theorem excRee_quotient_comm_of_commutator_le {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    (h : commutator G ≤ H) : ∀ x y : G ⧸ H, x * y = y * x := by
  intro x y
  induction x using QuotientGroup.induction_on with | H x => ?_
  induction y using QuotientGroup.induction_on with | H y => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
  rw [h1]
  exact h (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

theorem excRee_compShape_of_comm_mem {T : ∀ (Q : Type) [Group Q], Prop} {S : Type} [Group S]
    [Finite S] (β : MulAut S) {N : Subgroup S} (hNC : N ≤ fixSubgroup β)
    (hCN : ∀ c₁ ∈ fixSubgroup β, ∀ c₂ ∈ fixSubgroup β, ⁅c₁, c₂⁆ ∈ N)
    (hq : CFSG.Open.IsQuasisimple ↥N) (hT : T (↥N ⧸ Subgroup.center ↥N)) : CompShape T β := by
  have hCN' : commutator ↥(fixSubgroup β) ≤ N.subgroupOf (fixSubgroup β) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf]
    have : ((⁅x, y⁆ : ↥(fixSubgroup β)) : S) = ⁅(x : S), (y : S)⁆ := by
      simp [commutatorElement_def]
    rw [this]
    exact hCN _ x.2 _ y.2
  haveI hNn : (N.subgroupOf (fixSubgroup β)).Normal := excRee_normal_of_commutator_le hCN'
  have hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ N.subgroupOf (fixSubgroup β)) :=
    Group.isSolvable_of_comm (excRee_quotient_comm_of_commutator_le hCN')
  have hcomp : CFSG.Open.IsComponentOf N (fixSubgroup β) :=
    ⟨hNC, CFSG.Open.IsSubnormal.step hNC hNn (CFSG.Open.IsSubnormal.refl _), hq⟩
  have hperf : ∀ P : Subgroup S, P ≤ fixSubgroup β → ⁅P, P⁆ = P → P ≤ N := fun P hPC hP =>
    LieSemisimple.perfect_le_of_solvable_quotient hNC hsol hPC hP
  have hall : ∀ K : Subgroup S, CFSG.Open.IsComponentOf K (fixSubgroup β) → K = N := by
    intro K hK
    obtain ⟨-, hKN⟩ := component_mem_named_factors (ι := Unit) (fun _ => N) (fun _ => hcomp)
      (fun P hPC hP => by
        rw [iSup_const]
        exact hperf P hPC (Subgroup.isPerfect_iff.1 ⟨hP⟩)) hK
    exact hKN
  exact excRee_compShape_of_unique β N
    (fun P hPC hP => (hperf P hPC hP).trans (le_sSup hcomp)) hall hT

@[expose] def ExcReeType (k : Type) [Field k] (Q : Type) [Group Q] : Prop :=
  Nonempty (Q ≃* suzukiGroup 2 k) ∨
    Nonempty (Q ≃* (TauCeti.CFSGIndex.lie ⟨.tits, tits_valid⟩).Group)

theorem excReeType_isoInvariant (k : Type) [Field k] : IsoInvariant (ExcReeType k) := by
  intro Q Q' _ _ e h
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr ⟨e.symm.trans f⟩

theorem excRee_quotCenter_equiv {N : Type*} [Group N] [IsSimpleGroup N]
    (hnc : ∃ a b : N, a * b ≠ b * a) : Nonempty ((N ⧸ Subgroup.center N) ≃* N) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (b3Lie_center_eq_bot hnc)).trans
    QuotientGroup.quotientBot⟩

theorem excRee_suzuki_simple {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * 2 + 1)) :
    IsSimpleGroup (suzukiGroup 2 K) ∧ ∃ a b : suzukiGroup 2 K, a * b ≠ b * a := by
  obtain ⟨hfin, hnt, hsimp⟩ := suzuki_simple (by norm_num) hK
  refine ⟨hsimp, ?_⟩
  have hperf := (suzuki_perfect (by norm_num) hK).2
  by_contra hcon
  push Not at hcon
  exact Group.IsPerfect.not_isSolvable (suzukiGroup 2 K)
    (Group.isSolvable_of_comm (fun a b => hcon a b))

theorem excRee_congr_self {P : Type} [Group P] (ϕ x : MulAut P) :
    MulAut.congr (ϕ : P ≃* P) x = ϕ * x * ϕ⁻¹ := by
  ext y
  rfl

section Inner


theorem excRee_compShape_inner {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * 2 + 1)) {y : ReeTag.F4.reeGamma K 2} (hy : orderOf y = 5) :
    CompShape (ExcReeType K) (MulAut.conj y) := by
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K 2) := Subtype.finite
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hy5 : y ^ 5 = 1 := by
    rw [← hy]
    exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    omega
  have hEp : IsPGroup 5 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  have hEel : CFSG.Open.IsElemAbelian 5 (Subgroup.zpowers y) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy5, one_zpow]
  obtain ⟨A, S, -, -, hAcyc, hcomm, -, hsup, -, ⟨eS⟩, -⟩ :=
    CFSG.HardMathSupport.Malle.LocalAction.exists_centralizer_decomp hK P _ hEP hEel y
      (Subgroup.mem_zpowers y) hy1
  have hC : fixSubgroup (MulAut.conj y) = Subgroup.centralizer ({y} : Set _) :=
    CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj y
  have hSC : S ≤ fixSubgroup (MulAut.conj y) := by
    rw [hC, ← hsup]
    exact le_sup_right
  obtain ⟨hsimp, hnc⟩ := excRee_suzuki_simple hK
  haveI : IsSimpleGroup ↥S := eS.isSimpleGroup
  have hncS : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨eS.symm a, eS.symm b, fun h => hab (by simpa using congrArg eS h)⟩
  have hq : CFSG.Open.IsQuasisimple ↥S := b3Lie_isQuasisimple_of_simple hncS
  obtain ⟨eZ⟩ := excRee_quotCenter_equiv hncS
  refine excRee_compShape_of_comm_mem (MulAut.conj y) hSC ?_ hq (Or.inl ⟨eZ.trans eS⟩)
  intro c₁ hc₁ c₂ hc₂
  rw [hC, ← hsup] at hc₁ hc₂
  obtain ⟨a₁, ha₁, s₁, hs₁, rfl⟩ :=
    CFSG.HardMathSupport.Malle.LocalAction.mem_sup_of_commute hcomm hc₁
  obtain ⟨a₂, ha₂, s₂, hs₂, rfl⟩ :=
    CFSG.HardMathSupport.Malle.LocalAction.mem_sup_of_commute hcomm hc₂
  haveI := hAcyc
  have hA12 : a₁ * a₂ = a₂ * a₁ :=
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a₁, ha₁⟩ : ↥A) ⟨a₂, ha₂⟩)
  rw [hcomm a₁ ha₁ s₁ hs₁, hcomm a₂ ha₂ s₂ hs₂,
    commutatorElement_mul_mul' (hcomm a₁ ha₁ s₂ hs₂) hA12 (hcomm a₂ ha₂ s₁ hs₁),
    commutatorElement_def]
  exact S.mul_mem (S.mul_mem (S.mul_mem hs₁ hs₂) (S.inv_mem hs₁)) (S.inv_mem hs₂)

end Inner

section Field

set_option linter.unusedSectionVars false


theorem excRee_compShape_field {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * 2 + 1)) {σ : K ≃+* K} (hσ : orderOf σ = 5) :
    CompShape (ExcReeType K) (ReeTag.F4.reeGammaFieldAut K 2 σ) := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K 2) := Subtype.finite
  obtain ⟨b, hkcard, hchar, ⟨eC⟩⟩ :=
    exists_fixSubgroup_fieldAut_equiv' hK Nat.prime_five (by norm_num) σ hσ
  haveI := hchar
  haveI : Finite (fixSubfield σ) := Subtype.finite
  have hfix2 : Nat.card (fixSubfield σ) = 2 := by
    obtain ⟨-, h⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
      (by norm_num : 1 ≤ 2 * 2 + 1) hK σ
    rw [h, hσ]
    norm_num
  have hb0 : b = 0 := by
    have h1 : 2 ^ (2 * b + 1) = 2 ^ 1 := by rw [← hkcard, hfix2, pow_one]
    have h2 := Nat.pow_right_injective (le_refl 2) h1
    omega
  subst hb0
  haveI : Finite (ModGL ReeTag.F4.tag (fixSubfield σ)) := finite_modGL
  haveI : Finite ↥(ReeTag.F4.reeGamma (fixSubfield σ) 0) := Subtype.finite
  obtain ⟨hs, hnc, ⟨hcat⟩⟩ := commutator_reeGamma_F4_zero_data hfix2
  haveI := hs
  set β := ReeTag.F4.reeGammaFieldAut K 2 σ with hβ
  set C := fixSubgroup β with hC
  set D := commutator ↥C with hD
  set N := D.map C.subtype with hN
  have hNC : N ≤ C := Subgroup.map_subtype_le _
  have hmap : D.map eC.toMonoidHom = commutator ↥(ReeTag.F4.reeGamma (fixSubfield σ) 0) := by
    rw [hD, commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ eC.surjective]
  let eD : ↥D ≃* ↥(commutator ↥(ReeTag.F4.reeGamma (fixSubfield σ) 0)) :=
    (D.equivMapOfInjective eC.toMonoidHom eC.injective).trans (MulEquiv.subgroupCongr hmap)
  let eN : ↥D ≃* ↥N := D.equivMapOfInjective C.subtype C.subtype_injective
  let eDN : ↥(commutator ↥(ReeTag.F4.reeGamma (fixSubfield σ) 0)) ≃* ↥N := eD.symm.trans eN
  haveI : IsSimpleGroup ↥N := eDN.symm.isSimpleGroup
  have hncN : ∃ x y : ↥N, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eDN x, eDN y, fun h => hxy (eDN.injective (by
      rw [map_mul, map_mul]
      exact h))⟩
  have hq : CFSG.Open.IsQuasisimple ↥N := b3Lie_isQuasisimple_of_simple hncN
  obtain ⟨eZ⟩ := excRee_quotCenter_equiv hncN
  refine excRee_compShape_of_comm_mem β hNC ?_ hq (Or.inr ⟨eZ.trans (eDN.symm.trans hcat)⟩)
  intro c₁ hc₁ c₂ hc₂
  refine ⟨⁅(⟨c₁, hc₁⟩ : ↥C), ⟨c₂, hc₂⟩⁆, Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
  simp [commutatorElement_def]

theorem excRee_compShape {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * 2 + 1)) {β : MulAut ↥(ReeTag.F4.reeGamma K 2)} (hβ : β ^ 5 = 1)
    (hβ1 : β ≠ 1) : CompShape (ExcReeType K) β := by
  rcases reeF4_inner_or_field (a := 2) (by norm_num) hK Nat.prime_five hβ hβ1 with
    ⟨y, rfl, hy, hy1⟩ | ⟨σ, g, hσ, rfl⟩
  · exact excRee_compShape_inner hK (orderOf_eq_prime hy hy1)
  · refine CompShape.of_congr (excReeType_isoInvariant K)
      ((((MulAut.conj g)⁻¹ : MulAut _) : ↥(ReeTag.F4.reeGamma K 2) ≃* _)) ?_
    rw [excRee_congr_self]
    have : (MulAut.conj g)⁻¹ * (MulAut.conj g * ReeTag.F4.reeGammaFieldAut K 2 σ *
        (MulAut.conj g)⁻¹) * ((MulAut.conj g)⁻¹)⁻¹ = ReeTag.F4.reeGammaFieldAut K 2 σ := by
      group
    rw [this]
    exact excRee_compShape_field hK hσ

end Field

end CFSG.HardMathSupport.Dickson.Bal207

end
