module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableL2
public import CFSG.GH74.Generic.BProg.B2.PumpupTableOut
import CFSG.CGT.PushingUpLit.SolK.GenFour
import CFSG.GH74.GLS.IVK.Proofs2.GHInvRee
import CFSG.LocalAnalysis.ComponentClassification.HSFLitGen
public import CFSG.Walter.J1Props.Facts

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupTableRee

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.GH74.Generic.BProg.B2.PumpupTableBasic CFSG.GH74.Filter.ClassicalOdd
  CFSG.GH74.Generic.BProg.B2.PumpupTableL2

theorem commutative_of_isPGroup_of_sylow {X : Type*} [Group X] [Finite X] (S : Sylow 2 X)
    (hS : ∀ x ∈ (S : Subgroup X), ∀ y ∈ (S : Subgroup X), x * y = y * x) {P : Subgroup X}
    (hP : IsPGroup 2 P) : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  classical
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S Q
  intro x hx y hy
  have hxQ : x ∈ (Q : Subgroup X) := hPQ hx
  have hyQ : y ∈ (Q : Subgroup X) := hPQ hy
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ hyQ
  obtain ⟨x', hx', rfl⟩ := hxQ
  obtain ⟨y', hy', rfl⟩ := hyQ
  have := hS x' hx' y' hy'
  simp only [MulAut.smul_def, MulAut.conj_apply]
  calc g * x' * g⁻¹ * (g * y' * g⁻¹) = g * (x' * y') * g⁻¹ := by group
    _ = g * (y' * x') * g⁻¹ := by rw [this]
    _ = g * y' * g⁻¹ * (g * x' * g⁻¹) := by group

theorem center_eq_bot_of_perfect_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    [Group.IsPerfect X] : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hc : ∀ a b : X, a * b = b * a := fun a b => by
      have ha : a ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
    exact Group.IsPerfect.not_isMulCommutative X ⟨⟨hc⟩⟩

theorem sectionalTwoRankLE_of_card_le {G : Type*} [Group G] [Finite G] {r : ℕ}
    (h : Nat.card G ≤ 2 ^ r) : SectionalTwoRankLE G r := fun P _ =>
  CFSG.ComponentClassification.HSFLit.exists_finset_closure_eq_of_card_le P
    ((Subgroup.card_le_card_group P).trans h)

section Ree


theorem ree_sylow_data {T : Type} [Group T] [Finite T] {f : ℕ}
    (h : ReeTitsModel T .twistedG2 3 f) :
    ∃ S : Sylow 2 T, (∀ x ∈ (S : Subgroup T), ∀ y ∈ (S : Subgroup T), x * y = y * x) ∧
      Nat.card (S : Subgroup T) = 8 := by
  obtain ⟨a, K, _, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.GLS.IVK.GHInv.ree_model_data h
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (CFSG.LieType.Chevalley.coxeterSystem
    CFSG.LieType.Ree.ReeTag.G2.tag).length
  obtain ⟨hE, hcard, S, hS⟩ := CFSG.Walter.Ree.Model.smallRee_E8_sylow hK hw₀
  have hE' : IsElementaryAbelian 2 ↥(S : Subgroup (CFSG.LieType.Ree.ReeTag.G2.reeGamma K a)) := by
    rw [hS]; exact hE
  have hcomm : ∀ x ∈ (S : Subgroup (CFSG.LieType.Ree.ReeTag.G2.reeGamma K a)),
      ∀ y ∈ (S : Subgroup (CFSG.LieType.Ree.ReeTag.G2.reeGamma K a)), x * y = y * x :=
    fun x hx y hy => by
      have := hE'.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
  have hcard' : Nat.card ↥(S : Subgroup (CFSG.LieType.Ree.ReeTag.G2.reeGamma K a)) = 8 := by
    rw [hS]; exact hcard
  let S' : Sylow 2 T := Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective S
  have hS' : (S' : Subgroup T) = (S : Subgroup _).map e.symm.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  refine ⟨S', ?_, ?_⟩
  · intro x hx y hy
    rw [hS', Subgroup.mem_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hcomm x' hx' y' hy']
  · rw [hS', Subgroup.card_map_of_injective e.symm.injective, hcard']

theorem ree_commutative_of_isPGroup {T : Type} [Group T] [Finite T] {f : ℕ}
    (h : ReeTitsModel T .twistedG2 3 f) {P : Subgroup T} (hP : IsPGroup 2 P) :
    ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  obtain ⟨S, hS, -⟩ := ree_sylow_data h
  exact commutative_of_isPGroup_of_sylow S hS hP

theorem ree_no_q8 {T : Type} [Group T] [Finite T] {f : ℕ} (h : ReeTitsModel T .twistedG2 3 f)
    (ψ : Q8 →* T) (hψ : Function.Injective ψ) : False := by
  have hP : IsPGroup 2 ψ.range :=
    isPGroup_q8.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hc := ree_commutative_of_isPGroup h hP
  have : ∀ a b : Q8, a * b = b * a := fun a b => hψ (by
    have := hc (ψ a) ⟨a, rfl⟩ (ψ b) ⟨b, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact this)
  have h1 := this (QuaternionGroup.a 1) (QuaternionGroup.xa 0)
  revert h1
  decide

theorem ree_sectionalTwoRankLE_three {T : Type} [Group T] [Finite T] {f : ℕ}
    (h : ReeTitsModel T .twistedG2 3 f) : SectionalTwoRankLE T 3 := by
  obtain ⟨S, -, hcard⟩ := ree_sylow_data h
  refine CFSG.CGT.PushingUpLit.SolK.sectionalTwoRankLE_of_sylow S ?_
  exact sectionalTwoRankLE_of_card_le (by rw [hcard]; norm_num)

end Ree

theorem false_of_shape45_of_mem {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) (htH : t ∈ H) {Z : Subgroup ↥L} (hZ : Z.Normal)
    (hsimple : IsSimpleGroup (↥L ⧸ Z)) (hZo : Odd (Nat.card ↥Z))
    (hrc : RankCertified (↥L ⧸ Z) 2) (hH3 : SectionalTwoRankLE ↥H 3) : False := by
  have := hZ
  set C : Subgroup N := H ⊓ Subgroup.centralizer ({t} : Set N) with hC
  have hLC : L ≤ C := hs.comp.1
  have htC : t ∈ C := ⟨htH, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have ht2 : t * t = 1 := by
    have := hs.inv
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq this)
  have hperfC : Group.IsPerfect ↥(L.subgroupOf C) := hs.comp.2.1.1
  have hperfL : Group.IsPerfect ↥L :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLC).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLC).surjective
  have := hsimple
  have hcenter : Subgroup.center (↥L ⧸ Z) = ⊥ := center_eq_bot_of_perfect_of_simple
  have htL : t ∉ L := by
    intro htL
    have hcentral : (⟨t, htL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := (Subgroup.mem_centralizer_singleton_iff.mp (hLC y.2).2)
      exact Subtype.ext this
    have himg : (QuotientGroup.mk (⟨t, htL⟩ : ↥L) : ↥L ⧸ Z) ∈ Subgroup.center (↥L ⧸ Z) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact (Subgroup.mem_center_iff.mp hcentral g')
    rw [hcenter, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at himg
    have hdvd : orderOf (⟨t, htL⟩ : ↥L) ∣ Nat.card ↥Z := by
      have := Subgroup.orderOf_dvd_natCard Z himg
      simpa [Subgroup.orderOf_coe] using this
    have ho : orderOf (⟨t, htL⟩ : ↥L) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hs.inv
    rw [ho] at hdvd
    exact (Nat.not_even_iff_odd.mpr hZo) (even_iff_two_dvd.mpr hdvd)
  have hrcK : RankCertified ↥(L.subgroupOf C) 2 :=
    (hrc.of_quotient Z).of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLC).symm
  have hcc : ∀ x : ↥C, x * (⟨t, htC⟩ : ↥C) = (⟨t, htC⟩ : ↥C) * x := by
    intro x
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2.2)
  have hc2 : (⟨t, htC⟩ : ↥C) * (⟨t, htC⟩ : ↥C) = 1 := Subtype.ext ht2
  have hcK : (⟨t, htC⟩ : ↥C) ∉ L.subgroupOf C := by
    rw [Subgroup.mem_subgroupOf]
    exact htL
  have hrc3 : RankCertified ↥C 3 := RankCertified.of_central_involution hcc hc2 hcK hrcK
  exact (hrc3.of_injective (Subgroup.inclusion (inf_le_left : C ≤ H))
    (Subgroup.inclusion_injective _)).not_sectionalTwoRankLE hH3

theorem pumpup_ree
    (f : ℕ) :
    PumpupEmpty (fun X _ => LieModel X .twistedG2 0 3 f) := by
  intro N _ _ H t L hs hH
  have hT : ReeTitsModel ↥H .twistedG2 3 f :=
    CFSG.GH74.Generic.BProg.B1.reeTitsModel_of_lieModel_twistedG2 hH
  have := hs.normal
  obtain ⟨Z, -, hZo, hZn, hsh⟩ := hs.shape
  have hLH : L ≤ H := hs.comp.1.trans inf_le_left
  have ht2 : t * t = 1 := by
    have := hs.inv
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq this)
  have htH : t ∈ H := involution_mem_of_out H hs.faithful t ht2 (fun E hE => by
    simpa using CFSG.GH74.GLS.IVK.GHInv.ree_card_outer_elementary hT E hE)
  rcases hsh with h1 | h3 | h4 | h5
  · obtain ⟨ψ, hψ⟩ := q8_in_H_of_shape hLH hZn hZo (exists_q8_of_shape13 (Or.inl h1))
    exact ree_no_q8 hT ψ hψ
  · obtain ⟨ψ, hψ⟩ := q8_in_H_of_shape hLH hZn hZo (exists_q8_of_shape13 (Or.inr h3))
    exact ree_no_q8 hT ψ hψ
  · obtain ⟨f', hm⟩ := h4
    have hR' : ReeTitsModel (↥L ⧸ Z) .twistedG2 3 f' :=
      CFSG.GH74.Generic.BProg.B1.reeTitsModel_of_lieModel_twistedG2 hm
    have hsimple := (CFSG.LieType.Simplicity.fam_2g2_simplicity _ 3 f' hR').2
    exact false_of_shape45_of_mem hs htH hZn hsimple hZo
      (rankCertified_of_shape45 (Or.inl ⟨f', hm⟩)) (ree_sectionalTwoRankLE_three hT)
  · have h5' := h5
    obtain ⟨e0⟩ := h5'
    have hJ : IsSimpleGroup CFSG.Open.walterJ1 := CFSG.Walter.J1Props.J1_simple
    let e : (↥L ⧸ Z) ≃* CFSG.Open.walterJ1 := e0.trans CFSG.Walter.walterJ1EquivNative.symm
    have hsimple : IsSimpleGroup (↥L ⧸ Z) := e.isSimpleGroup
    exact false_of_shape45_of_mem hs htH hZn hsimple hZo
      (rankCertified_of_shape45 (Or.inr h5)) (ree_sectionalTwoRankLE_three hT)

end CFSG.GH74.Generic.BProg.B2.PumpupTableRee
