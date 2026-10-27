module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Hyp
public import CFSG.Quasithin.Vol2.Ch4Sec4L448
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E9Mp
public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4D
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E1Basic

public section

namespace CFSG.SectionRank.QTK.Insp443.Hyp

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.A4 CFSG.Quasithin.H13
  CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443 CFSG.QuasithinUnique
  CFSG.Quasithin.C2Nine CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L B Tp VB K : Subgroup G}

theorem VB_eq_commutator (h : Hyp G T M L B Tp VB K) :
    VB = ⁅VB, perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))⁆ :=
  h.setting.VB_eq_commutator_LB

theorem VB_comm (h : Hyp G T M L B Tp VB K) : IsMulCommutative ↥VB :=
  ⟨⟨fun a b => Subtype.ext (Subgroup.mem_centralizer_iff.mp
    (mem_quasithinOmegaOneCenter_iff.mp (h.setting.hyp.VB_le b.2)).2.1 a
    (mem_quasithinOmegaOneCenter_iff.mp (h.setting.hyp.VB_le a.2)).1)⟩⟩

theorem VB_sq (h : Hyp G T M L B Tp VB K) : ∀ v ∈ VB, v ^ 2 = 1 := fun v hv =>
  (mem_quasithinOmegaOneCenter_iff.mp (h.setting.hyp.VB_le hv)).2.2

theorem LB_le_normalizer_VB (h : Hyp G T M L B Tp VB K) :
    perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ≤
      Subgroup.normalizer (VB : Set G) :=
  (E443.LB_le L T B).trans (le_sup_left.trans h.setting.hyp.VB_normalized)

theorem VB_le_LB (h : Hyp G T M L B Tp VB K) :
    VB ≤ perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) := by
  have hVT : VB ≤ T := E443.VB_le_T h.setting
  have hVCB : VB ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h.setting.hyp.VB_centralizes
  have hVNCB : VB ≤ Subgroup.normalizer (Subgroup.centralizer (B : Set G) : Set G) := fun v hv =>
    mem_normalizer_centralizer (Subgroup.centralizer_le_normalizer (B : Set G) (hVCB hv))
  have hVNMp : VB ≤ Subgroup.normalizer (conjClosure L T : Set G) :=
    hVT.trans (le_normalizer_conjClosure L T)
  have hVN : VB ≤ Subgroup.normalizer
      (conjClosure L T ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) := fun v hv =>
    mem_normalizer_inf (hVNMp hv) (hVNCB hv)
  have hVNLB : VB ≤ Subgroup.normalizer
      (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) : Set G) :=
    hVN.trans (normalizer_le_normalizer_perfectCore _)
  rw [VB_eq_commutator h]
  exact commutator_le_right_of_le_normalizer hVNLB

theorem pCoreOf_le_centralizer (h : Hyp G T M L B Tp VB K) :
    pCoreOf 2 (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) ≤
      Subgroup.centralizer (VB : Set G) :=
  Subgroup.le_centralizer_iff.mp (E443.VB_le_centralizer_pCoreOf_LB h.setting)

theorem LB_perfect (h : Hyp G T M L B Tp VB K) :
    ⁅perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)),
      perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))⁆ =
      perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) :=
  perfectCore_perfect _

theorem LB_le_inf (h : Hyp G T M L B Tp VB K) :
    perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ≤
      M ⊓ Subgroup.normalizer (VB : Set G) := by
  have hLM : perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ≤ M :=
    (le_sup_left.trans h.setting.sup_le_normalizer).trans inf_le_left
  exact le_inf hLM (LB_le_normalizer_VB h)

theorem isSylowTwoOf_inf (h : Hyp G T M L B Tp VB K) :
    IsSylowTwoOf (T ⊓ perfectCore (conjClosure L T ⊓
      Subgroup.centralizer (B : Set G))) (perfectCore (conjClosure L T ⊓
        Subgroup.centralizer (B : Set G))) :=
  G443J4.isSylowTwoOf_inf h.setting.hyp.sylow (le_normalizer_conjClosure L T)
    (lemma_4_4_5_orbit h.setting.hyp.toHyp4_4_1TwoOrbit)

theorem inf_conjClosure_eq (h : Hyp G T M L B Tp VB K) :
    T ⊓ conjClosure L T = (T ⊓ perfectCore (conjClosure L T ⊓
      Subgroup.centralizer (B : Set G))) ⊔ pCoreOf 2 (conjClosure L T) := by
  set Mp := conjClosure L T with hMp
  set LB := perfectCore (Mp ⊓ Subgroup.centralizer (B : Set G)) with hLB
  set Q := pCoreOf 2 Mp with hQ
  have hQT : Q ≤ T := G443J4.pCoreOf_le_of_le_normalizer h.setting.hyp.sylow
    (le_normalizer_conjClosure L T)
  have h445 : Mp = LB ⊔ Q := by
    rw [hMp, hLB, hQ]
    exact lemma_4_4_5_orbit h.setting.hyp.toHyp4_4_1TwoOrbit
  have hLBNQ : LB ≤ Subgroup.normalizer (Q : Set G) :=
    (E443.LB_le L T B).trans (le_normalizer_pCoreOf 2 Mp)
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx' : x ∈ LB ⊔ Q := by rw [← h445]; exact hx.2
    obtain ⟨l, hl, q, hq, rfl⟩ := (mem_sup_of_le_normalizer hLBNQ).mp hx'
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨?_, hl⟩) (Subgroup.mem_sup_right hq)
    have hlT : l ∈ T := by
      have := T.mul_mem hx.1 (T.inv_mem (hQT hq))
      simpa using this
    exact hlT
  · intro x hx
    exact ⟨sup_le inf_le_left hQT hx,
      sup_le (inf_le_right.trans (E443.LB_le L T B)) (pCoreOf_le 2 Mp) hx⟩

theorem odd_card_center (h : Hyp G T M L B Tp VB K) :
    Odd (Nat.card (Subgroup.center ↥K)) := by
  set Z := (Subgroup.center ↥K).map K.subtype with hZ
  have hZK : Z ≤ oddCoreIn (Subgroup.normalizer (B : Set G)) := by
    rintro z hz
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
    have hkNB : (k : G) ∈ Subgroup.normalizer (B : Set G) := h.K_le k.2
    have hkC : (k : G) ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hk ⟨g, hg⟩)
    have hmem : (k : G) ∈ Subgroup.normalizer (B : Set G) ⊓
        Subgroup.centralizer (K : Set G) := ⟨hkNB, hkC⟩
    rwa [h.centralizer_eq] at hmem
  have hdvd : Nat.card (Subgroup.center ↥K) ∣
      Nat.card (oddCoreIn (Subgroup.normalizer (B : Set G))) := by
    rw [← Subgroup.card_map_of_injective K.subtype_injective]
    exact Subgroup.card_dvd_of_le hZK
  exact Odd.of_dvd_nat (C2Nine.odd_card_oddCoreIn (Subgroup.normalizer (B : Set G))) hdvd

end CFSG.SectionRank.QTK.Insp443.Hyp
