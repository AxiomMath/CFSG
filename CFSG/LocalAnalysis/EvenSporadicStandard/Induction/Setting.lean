module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FStar
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Comp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Hyp
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.FS79Setting
public import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

@[expose] def StdBare {H : Type} [Group H] (K : Subgroup H) : Prop :=
  (∀ g : H, ⁅K, K.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) ∧
    ∀ g : H, g ∉ normalizer (K : Set H) →
      Odd (Nat.card (↥(centralizer (K : Set H) ⊓
        (centralizer (K : Set H)).map (MulAut.conj g).toMonoidHom : Subgroup H)))

@[expose] def SolStd {H : Type} [Group H] (L : Subgroup H) : Prop :=
  StdBare L ∧ ∃ t : H, orderOf t = 2 ∧ IsCompIn L (centralizer ({t} : Set H))

@[expose] def OddCover (s : TauCeti.SporadicName) {H : Type} [Group H] (L : Subgroup H) : Prop :=
  CFSG.IsQuasisimple ↥L ∧ Odd (Nat.card ↥(center ↥L)) ∧ IsSporadic (↥L ⧸ center ↥L) s

theorem SolStd.stdBare {H : Type} [Group H] {L : Subgroup H} (h : SolStd L) : StdBare L := h.1

theorem SolStd.exists_involution {H : Type} [Group H] {L : Subgroup H} (h : SolStd L) :
    ∃ t : H, orderOf t = 2 ∧ IsCompIn L (centralizer ({t} : Set H)) := h.2

theorem OddCover.isQuasisimple {s : TauCeti.SporadicName} {H : Type} [Group H] {L : Subgroup H}
    (h : OddCover s L) : CFSG.IsQuasisimple ↥L := h.1

theorem OddCover.odd_center {s : TauCeti.SporadicName} {H : Type} [Group H] {L : Subgroup H}
    (h : OddCover s L) : Odd (Nat.card ↥(center ↥L)) := h.2.1

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.solStd {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (h : StdHyp G L) : SolStd L := by
  obtain ⟨t, ht2, hle, hsub⟩ := h.exists_involution_component
  have hq : CFSG.IsQuasisimple ↥L :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥L).2.2.1.2 h.standard.1
  refine ⟨⟨h.standard.2.2.2.2, fun g hg => ?_⟩, t, ht2, isCompIn_of_subnormal hle hq hsub⟩
  refine h.standard.2.2.1 g fun hgC => hg ?_
  rw [← h.standard.2.2.2.1]
  exact hgC

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.fStarSimple {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (h : StdHyp G L) : FStarSimple (⊤ : Subgroup G) := by
  have := h.simple
  exact fStarSimple_top G h.nonabelian

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.index_top_le_two {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (_ : StdHyp G L) : (⊤ : Subgroup G).index ≤ 2 := by
  rw [Subgroup.index_top]
  norm_num

theorem solStd_of_standardComponentIsStandard {H : Type} [Group H] [Finite H] {L : Subgroup H}
    (h : CFSG.Open.standardComponentIsStandard L) : SolStd L := by
  have hCt : ∀ {t : H}, t ∈ centralizer (L : Set H) → orderOf t = 2 →
      centralizer ({t} : Set H) ≤ normalizer (L : Set H) := fun htC ht2 _ hg =>
    h.mem_normalizer_of_commute htC ht2 (mem_centralizer_singleton_iff.1 hg)
  obtain ⟨t, htC, ht2⟩ := h.exists_involution_centralizer
  obtain ⟨hq, -, htight, hNC, hcomm⟩ := h
  have hq' : CFSG.IsQuasisimple ↥L :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥L).2.2.1.2 hq
  have hstd : StdBare L := by
    refine ⟨hcomm, fun g hg => htight g fun hgC => hg ?_⟩
    rw [← hNC]
    exact hgC
  have hle : L ≤ centralizer ({t} : Set H) := fun x hx =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC x hx)
  exact ⟨hstd, t, ht2, isCompIn_of_normal hle hq'
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 (hCt htC ht2))⟩

@[expose] def Sol78Rows : List TauCeti.SporadicName :=
  [.Suz, .ONan, .Co1, .HN, .B, .M, .Fi22, .Fi23, .Fi24Prime, .Ru]

@[expose] def Sol78Concl {H : Type} [Group H] (N L : Subgroup H) : Prop :=
  IsSporadic ↥L .Fi23 ∧ IsSporadic ↥N .Fi24Prime

abbrev PairClass : Type 1 := ∀ (H : Type) [Group H], Subgroup H → Subgroup H → H → Prop

structure SolomonGlobalQ (H : Type) [Group H] (L K : Subgroup H) (t u : H) : Prop where
  standardL : SolStd L
  cyclicSylow : ∃ S : Sylow 2 (centralizer (L : Set H)),
    IsCyclic (S : Subgroup (centralizer (L : Set H)))
  t_order : orderOf t = 2
  t_mem : t ∈ centralizer (L : Set H)
  u_comm_t : u * t = t * u
  hyp35 : K = componentProduct K u

structure SolomonLocalQ {H : Type} [Group H] (L K : Subgroup H) (u : H) : Prop where
  u_order : orderOf u = 2
  u_mem : u ∈ normalizer (L : Set H)
  u_not_central : u ∉ centralizer (L : Set H)
  K_le : K ≤ L
  u_mem_centralizer_K : u ∈ centralizer (K : Set H)
  standard_in_L : SolStd (K.subgroupOf L)
  autCentralizer_two : twoAdic (autCentralizer L K) ≤ 2

structure SolomonSettingQ (H : Type) [Group H] [Finite H] (N L K : Subgroup H) (t u : H) :
    Prop extends SolomonGlobalQ H L K t u, SolomonLocalQ L K u where
  fstar : FStarSimple N
  index_le_two : N.index ≤ 2
  kProper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H
  quasisimpleL : CFSG.IsQuasisimple ↥L
  centre_odd : Odd (Nat.card ↥(center ↥L))

theorem SolomonSettingQ.of_parts {H : Type} [Group H] [Finite H] {N L K : Subgroup H} {t u : H}
    {s : TauCeti.SporadicName} (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hL : OddCover s L)
    (hg : SolomonGlobalQ H L K t u) (hl : SolomonLocalQ L K u) : SolomonSettingQ H N L K t u :=
  { hg, hl with
    fstar := hN
    index_le_two := hidx
    kProper := hK
    quasisimpleL := hL.isQuasisimple
    centre_odd := hL.odd_center }

structure SolomonHypQ (H : Type) [Group H] [Finite H] (N L K : Subgroup H) (t u : H) : Prop
    extends SolomonSettingQ H N L K t u where
  hyp38_1 : ∀ g ∈ centralizer ({u} : Set H), ∀ w ∈ vPairs L K u, g * w * g⁻¹ ∈ vPairs L K u
  hyp38_2 : centralizer ({u} : Set H) ≤ normalizer (L : Set H)

@[expose] def Sol78SettingLocalQ (s : TauCeti.SporadicName) (Q P : PairClass) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H), OddCover s L → Q H L K u →
    SolomonLocalQ L K u ∧ P H L K u

structure RowSpec where
  types : List TauCeti.SporadicName
  pairs : TauCeti.SporadicName → PairClass

@[expose] def Hyp35At (S : List TauCeti.SporadicName) (Q : TauCeti.SporadicName → PairClass)
    (H : Type) [Group H] [Finite H] : Prop :=
  ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
    ∀ L : Subgroup H, SolStd L → (∃ s ∈ S, OddCover s L) →
      ∃ (s' : TauCeti.SporadicName) (L' K : Subgroup H) (t u : H), s' ∈ S ∧ OddCover s' L' ∧
        SolomonGlobalQ H L' K t u ∧ Q s' H L' K u

@[expose] def Sol78Closing (S : List TauCeti.SporadicName)
    (Q : TauCeti.SporadicName → PairClass) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N L K : Subgroup H) (t u : H) (s : TauCeti.SporadicName),
    s ∈ S → FStarSimple N → N.index ≤ 2 → CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
      OddCover s L →
      SolomonGlobalQ H L K t u → Q s H L K u → False

end CFSG.EvenSporadicStandard.Induction
