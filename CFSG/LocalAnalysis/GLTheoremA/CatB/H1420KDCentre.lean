module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowDefs
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Final
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddFull
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420KDCentreBalance
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420KDCentreL227

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

namespace KDCentre

private theorem kdc_exists_central_order_three {G : Type} [Group G] [Finite G]
    {X J : Subgroup G} (hX : GLAPPrimeCoreOf 3 X = ⊥) (hJ : GLAPComponent 3 X J)
    (hZ : Subgroup.center (PQuot 3 J) ≠ ⊥) :
    ∃ u ∈ J, (∀ j ∈ J, j * u = u * j) ∧ orderOf u = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hOJ : GLAPPrimeCore 3 ↥J = ⊥ := by
    have h1 := CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 3
      hJ.2.1
    rw [hX, le_bot_iff] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).1 h1
  obtain ⟨⟨zb, hzb⟩, hzb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective zb
  have hzc : z ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro j
    have h1 : (QuotientGroup.mk (j * z) : PQuot 3 J) = QuotientGroup.mk (z * j) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact Subgroup.mem_center_iff.1 hzb (QuotientGroup.mk j)
    have h2 := QuotientGroup.eq.1 h1
    rw [hOJ, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact h2
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hzb1 (Subtype.ext (QuotientGroup.mk_one _))
  have hcz : IsPGroup 3 ↥(Subgroup.center ↥J) :=
    CFSG.isPGroup_of_nilpotent_normal (Subgroup.center ↥J) inferInstance inferInstance hOJ
  have hdvd : 3 ∣ Nat.card ↥(Subgroup.center ↥J) := by
    refine hcz.card_eq_or_dvd.resolve_left fun h1 => hz1 ?_
    haveI : Subsingleton ↥(Subgroup.center ↥J) := (Nat.card_eq_one_iff_unique.1 h1).1
    exact congrArg Subtype.val (Subsingleton.elim (⟨z, hzc⟩ : ↥(Subgroup.center ↥J)) 1)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨((w : ↥J) : G), (w : ↥J).2, fun j hj => ?_, ?_⟩
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 w.2 ⟨j, hj⟩)
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]

private theorem kdc_mem_normalizer_zpowers {G : Type*} [Group G] {w y : G}
    (h : w * y = y * w) : y ∈ Subgroup.normalizer ((Subgroup.zpowers w : Subgroup G) : Set G) :=
  Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (SetLike.mem_coe.1 hx)
    exact (Commute.zpow_left h k).eq)

end KDCentre

section Main

open KDCentre
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
  (outerCentAll_holds kdOutCoreFree_holds orderOf_eq_of_pow_eq_one_of_not_inner)
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits
  (conj_injective_of_center_eq_bot)
open CFSG.HardMathSupport.Dickson.I271 (conj_mem_centralizer_iff)


theorem kdOutChevCentre_holds : KDOutChevCentre := by
  intro S _ _ d hd e β hβ3 hout J hJ
  by_contra hZJ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut S) :=
    Finite.of_injective (fun f : MulAut S => (f : S → S)) DFunLike.coe_injective
  obtain ⟨-, hsimp, hnab⟩ := (outerCentAll_holds (CFSG.Yardstones.Md42047359a2a.lieFamily d.1)).1
    d rfl (by rw [hd]; norm_num)
  haveI := hsimp
  have hs : IsSimpleGroup S := e.isSimpleGroup
  have hnabS : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  haveI := hs
  have hZ : Subgroup.center S = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnabS
  have hout' : β ∉ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S := hout
  have hβo : orderOf β = 3 := orderOf_eq_of_pow_eq_one_of_not_inner Nat.prime_three hβ3 hout'
  by_cases h27 : CFSG.HardMathSupport.Solomon.Coordinator.IsLTwoTwentySeven S
  · exact not_glaPComponent_fixSubgroup_of_l227 h27 hβo hout' J hJ
  have hcore : GLAPPrimeCoreOf 3 (fixSubgroup β) = ⊥ :=
    kdOutCoreFree_holds S hs hnabS d ⟨e⟩ 3 Nat.prime_three (by norm_num) hd
      (fun h => h27 h.2) β hβo hout'
  obtain ⟨u, huJ, huc, hu3⟩ := kdc_exists_central_order_three hcore hJ hZJ
  obtain ⟨hON, hEN⟩ := glaPPrimeCoreOf_glaPLayer_normalizer_conj_eq_bot
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.lieQConstrained_odd Nat.prime_three
      (by norm_num)) hs hnabS hd e hu3
  set N : Subgroup (MulAut S) := Subgroup.normalizer
    ((Subgroup.zpowers (MulAut.conj u) : Subgroup (MulAut S)) : Set (MulAut S)) with hN
  set X : Subgroup (MulAut S) := N ⊓ Subgroup.centralizer ({β} : Set (MulAut S)) with hX
  have hβN : β ∈ N := kdc_mem_normalizer_zpowers
    (Subgroup.mem_centralizer_singleton_iff.1 ((conj_mem_centralizer_iff hZ β u).2 (hJ.1 huJ)))
  have hbal : GLAPLayer 3 X = ⊥ :=
    glaPLayer_inf_centralizer_eq_bot_of_core_layer Nat.prime_three hON hEN hβN
      ⟨1, by simpa using hβ3⟩
  set M : Subgroup S := X.comap (MulAut.conj : S →* MulAut S) with hM
  have hJM : J ≤ M := by
    intro j hj
    rw [hM, Subgroup.mem_comap, hX, Subgroup.mem_inf]
    refine ⟨kdc_mem_normalizer_zpowers ?_, (conj_mem_centralizer_iff hZ β j).2 (hJ.1 hj)⟩
    rw [← map_mul, ← map_mul, huc j hj]
  have hMF : M ≤ fixSubgroup β := fun s hs =>
    (conj_mem_centralizer_iff hZ β s).1 (Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hs)).2
  have h1 : GLAPComponent 3 M J :=
    CFSG.LocalAnalysis.GLTheoremB.glaPComponent_of_le Nat.prime_three hJ hJM hMF
  have hker : Nat.Coprime 3 (Nat.card ↥(M ⊓ (MulAut.conj : S →* MulAut S).ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 fun a b h => conj_injective_of_center_eq_bot hZ h,
      inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  have h2 := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map Nat.prime_three
    (MulAut.conj : S →* MulAut S) hker h1
  rw [hM, Subgroup.map_comap_eq] at h2
  have hn : (((MulAut.conj : S →* MulAut S).range ⊓ X).subgroupOf X).Normal := by
    rw [Subgroup.inf_subgroupOf_right]
    exact (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal S).subgroupOf X
  have h3 : GLAPComponent 3 X (J.map (MulAut.conj : S →* MulAut S)) :=
    CFSG.HardMathSupport.Solomon.Proving.glaPComponent_of_normal_overgroup Nat.prime_three
      inf_le_right hn h2
  have h4 : J.map (MulAut.conj : S →* MulAut S) ≤ GLAPLayer 3 X := le_sSup h3
  rw [hbal, le_bot_iff] at h4
  exact glaPComponent_ne_bot' h3 h4

end Main

end CFSG.LocalAnalysis.GLTheoremA
