module

public import CFSG.HardMathSupport.Foote.Coordinator.Interface
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M2
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M4
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.HardMathSupport.Foote.Coordinator

open CFSG CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.CGT6
  CFSG.CGT.PushingUpLit.CGT6M
open CFSG.Quasithin (commV fixV)
open CFSG.RankThree.PartOne (InClassX)

variable {V : Type} [CommGroup V] [Finite V]

theorem inCatalog_layerQ {G T Y : Subgroup (MulAut V)} (h : EndCfg4 G T Y) :
    Assembly.InCatalog (LayerQ G Y) := by
  have hYG : Y ≤ G := h.toEmb4Cfg.adm.hYC.trans inf_le_left
  have hLG : conjClosure Y G ≤ G := conjClosure_le hYG
  let e : ↥((conjClosure Y G).subgroupOf G) ≃* ↥(conjClosure Y G) :=
    Subgroup.subgroupOfEquivOfLe hLG
  let N : Subgroup ↥((conjClosure Y G).subgroupOf G) :=
    (Subgroup.center ↥(conjClosure Y G)).comap e.toMonoidHom
  have hN : N.map e.toMonoidHom = Subgroup.center ↥(conjClosure Y G) :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective _
  let φ : (↥((conjClosure Y G).subgroupOf G) ⧸ N) ≃* LayerQ G Y := QuotientGroup.congr N _ e hN
  have hsimple : IsSimpleGroup (↥((conjClosure Y G).subgroupOf G) ⧸ N) :=
    (MulEquiv.isSimpleGroup_congr φ).mpr h.quasi.2
  obtain ⟨i, ⟨ψ⟩⟩ := h.toEmb4Cfg.kgroup ((conjClosure Y G).subgroupOf G) N hsimple
  exact ⟨i, ⟨φ.symm.trans ψ⟩⟩

theorem footeK_of_endCfg4
    (hV : ∀ v : V, v ^ 2 = 1) {G T Y : Subgroup (MulAut V)}
    (h : EndCfg4 G T Y) (hY5 : YSL5 Y) :
    ∃ z : MulAut V, FooteK (LayerQ G Y) (conjClosure Y G) Y z
      (QuotientGroup.mk' (Subgroup.center ↥(conjClosure Y G))) := by
  have hperf : ⁅Y, Y⁆ = Y := h.toEmb4Cfg.adm.hperf
  have hYG : Y ≤ G := h.toEmb4Cfg.adm.hYC.trans inf_le_left
  have hLG : conjClosure Y G ≤ G := conjClosure_le hYG
  have hX : InClassX ↥(yuHol Y) := by
    rcases h.hcls2 with hX | ⟨n, hn, hΩ⟩
    · exact hX
    · exact (not_natOmegaMinus_of_ysl5 hn hY5 hΩ).elim
  rcases emb_four_five h1NaturalSL2_holds schurMultL2Two_holds V hV Y hperf hX with
    hc | ⟨-, hcard, hsl, hle, hC4⟩
  · exact (center_ne_bot_ysl5 hY5 hc).elim
  obtain ⟨z, hz1⟩ : ∃ z : ↥(Subgroup.center ↥Y), z ≠ 1 := by
    have h1 : 1 < Nat.card ↥(Subgroup.center ↥Y) := by rw [hcard]; norm_num
    have := Finite.one_lt_card_iff_nontrivial.mp h1
    exact exists_ne (1 : ↥(Subgroup.center ↥Y))
  have hz2 : z ^ 2 = 1 := by
    have : orderOf z ∣ 2 := hcard ▸ orderOf_dvd_natCard z
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hz1
    · rw [← h2]
      exact pow_orderOf_eq_one z
  set z0 : MulAut V := ((z : ↥Y) : MulAut V) with hz0
  have hzz : z0 * z0 = 1 := by
    have := congrArg (fun g : ↥(Subgroup.center ↥Y) => ((g : ↥Y) : MulAut V)) hz2
    simpa [sq] using this
  have hz0mem : z0 ∈ (Subgroup.center ↥Y).map Y.subtype := ⟨(z : ↥Y), z.2, rfl⟩
  have hW : Nat.card ↥(commSub z0) ≤ 4 :=
    (Subgroup.card_le_of_le (commSub_le_commV _ hz0mem)).trans (hle.trans hC4)
  have hU' : Nat.card ↥(commV Y) ≤ 2 ^ 4 * Nat.card ↥(commV Y ⊓ fixV Y) := by
    have := card_commV_of_natSL hV hperf hX.1 hsl (by norm_num)
    rw [this, mul_comm]
  have hcentral : ∀ y ∈ Y, z0 * y = y * z0 := fun y hy =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)).symm
  have hne : z0 ≠ 1 := fun h0 => hz1 (Subtype.ext (Subtype.ext h0))
  refine ⟨z0,
    { elem := hV
      quasi := h.quasi
      oddZ := h.oddZ
      surj := QuotientGroup.mk'_surjective _
      ker := QuotientGroup.ker_mk' _
      le := le_conjClosure
      sl5 := hY5
      mem := (z : ↥Y).2
      central := hcentral
      ne_one := hne
      invol := hzz
      commZ := hW
      commFive := ?_
      subnormal := ?_ }⟩
  · intro y hy hy5
    have h16 := card_le_sixteen_fixSub_of_comm hV Y hy hy5 hU'
    have hcm := card_commSub_mul_card_fixSub y
    have hpos : 0 < Nat.card ↥(fixSub y) := Nat.card_pos
    exact Nat.le_of_mul_le_mul_right (hcm.le.trans h16) hpos
  · have hzC : z0 ∈ Subgroup.centralizer (Y : Set (MulAut V)) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => (hcentral y hy).symm
    have hsub := h.toEmb4Cfg.cent z0 ⟨hYG (z : ↥Y).2, hzC⟩ hne (by rw [sq]; exact hzz)
    exact CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (inf_le_inf_right _ hLG) hsub

theorem exists_ne_comm_layerQ {G T Y : Subgroup (MulAut V)} (h : EndCfg4 G T Y) :
    ∃ a b : LayerQ G Y, a * b ≠ b * a := by
  by_contra hab
  push Not at hab
  have hsimple : IsSimpleGroup (LayerQ G Y) := h.quasi.2
  let π := QuotientGroup.mk' (Subgroup.center ↥(conjClosure Y G))
  have hL : ∀ x : ↥(conjClosure Y G), x ∈ Subgroup.center ↥(conjClosure Y G) := by
    intro x
    have hx : x ∈ commutator ↥(conjClosure Y G) := by rw [h.quasi.1]; trivial
    rw [commutator_def] at hx
    rw [← QuotientGroup.ker_mk' (Subgroup.center ↥(conjClosure Y G))]
    refine (Subgroup.commutator_le.mpr ?_) hx
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hab (π a) (π b)
  obtain ⟨a, b, hab'⟩ := exists_pair_ne (LayerQ G Y)
  have h1 : ∀ c : LayerQ G Y, c = 1 := by
    intro c
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(conjClosure Y G)) c
    exact (QuotientGroup.eq_one_iff x).mpr (hL x)
  exact hab' ((h1 a).trans (h1 b).symm)

theorem endFoote_of_targets
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hA : AltTarget) (hS : SporTarget) (hC : ClassicalOffFiveTarget) (hE : ExcOffFiveTarget)
    (hR : ReeTitsSuzukiTarget) (hC5 : ClassicalFiveTarget) (hE5 : ExcFiveTarget) : EndFoote := by
  intro V _ _ hV G T Y h hY5
  obtain ⟨z, hK⟩ := footeK_of_endCfg4 hV h hY5
  have : Finite (LayerQ G Y) :=
    inferInstanceAs (Finite (↥(conjClosure Y G) ⧸ Subgroup.center ↥(conjClosure Y G)))
  have : IsSimpleGroup (LayerQ G Y) := h.quasi.2
  have hnab := exists_ne_comm_layerQ h
  have hcat : Blueprint.Catalog (LayerQ G Y) := hbridge (LayerQ G Y) hnab (inCatalog_layerQ h)
  rcases footeList_or_end415K hA hS hC hE hR hC5 hE5 (LayerQ G Y) hnab hcat with hL | hK'
  · exact hL
  · exact (hK' V _ Y z _ hK).elim

end CFSG.HardMathSupport.Foote.Coordinator
