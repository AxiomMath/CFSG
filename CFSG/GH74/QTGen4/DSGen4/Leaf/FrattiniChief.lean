module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

theorem frattiniChief_conj_mem {G : Type} [Group G] (Q : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) {x : G} (hx : x ∈ dsFrattini Q) :
    g * x * g⁻¹ ∈ dsFrattini Q := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  set φ : MulAut ↥Q := Q.normalizerMonoidHom ⟨g, hg⟩ with hφ
  have hF : (frattini ↥Q).map φ.toMonoidHom = frattini ↥Q :=
    Subgroup.characteristic_iff_map_eq.1 inferInstance φ
  have hφy : φ y ∈ frattini ↥Q := by
    have h := Subgroup.mem_map_of_mem φ.toMonoidHom hy
    rwa [hF] at h
  exact Subgroup.mem_map.2 ⟨φ y, hφy, rfl⟩

theorem frattiniChief_mem_normalizer {G : Type} [Group G] (Q : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    g ∈ Subgroup.normalizer ((dsFrattini Q : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨frattiniChief_conj_mem Q hg, fun hx => ?_⟩
  have h := frattiniChief_conj_mem Q (Subgroup.inv_mem _ hg) hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h

theorem frattiniChief_comm_mem {G : Type} [Group G] [Finite G] (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    {q e : G} (hq : q ∈ Q) (he : e ∈ Q) : ⁅q, e⁆ ∈ dsFrattini Q := by
  haveI : Fact (IsPGroup 2 ↥Q) := ⟨hQ⟩
  have hc := CFSG.commutator_le_frattini_of_isPGroup (p := 2) (R := ↥Q)
  have hmem : (⁅(⟨q, hq⟩ : ↥Q), ⟨e, he⟩⁆ : ↥Q) ∈ frattini ↥Q :=
    hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  refine Subgroup.mem_map.2 ⟨_, hmem, ?_⟩
  simp [commutatorElement_def]

theorem frattiniChief_sq_mem {G : Type} [Group G] [Finite G] (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    {e : G} (he : e ∈ Q) : e ^ 2 ∈ dsFrattini Q := by
  haveI : Fact (IsPGroup 2 ↥Q) := ⟨hQ⟩
  have h := CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) (R := ↥Q) ⟨e, he⟩
  refine Subgroup.mem_map.2 ⟨_, h, ?_⟩
  simp

theorem frattiniChief_isElemSec {G : Type} [Group G] [Finite G] (Q : Subgroup G) (hQ : IsPGroup 2 Q) :
    IsElemSec (dsFrattini Q) Q := by
  unfold IsElemSec
  refine ⟨?_, ?_, fun e he => frattiniChief_sq_mem Q hQ he⟩
  · exact Subgroup.map_subtype_le _
  · exact Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => frattiniChief_comm_mem Q hQ hg₁ hg₂

theorem leafFrattiniChief [DSLeaf LeafFaithfulA5] [DSLeaf LeafRankBounds] [DSLeaf LeafFrattiniFaithful] :
    LeafFrattiniChief := by
  intro G _ _ L P h
  have hQ : IsPGroup 2 (pCoreOf 2 P) := CFSG.RankThree.PartOne.SectionalRank.isPGroup_pCoreOf 2 P
  have hEP : pCoreOf 2 P ≤ P := Subgroup.map_subtype_le _
  have hcard : (dsFrattini (pCoreOf 2 P)).relIndex (pCoreOf 2 P) ≤ 16 :=
    (CFSG.GH74.QTGen4.DSGen4.rank_bounds (G := G)).1 _ hQ
  have hnt : ∃ l ∈ L, ∃ e ∈ pCoreOf 2 P, ⁅l, e⁆ ∉ dsFrattini (pCoreOf 2 P) := by
    by_contra hcon
    push_neg at hcon
    have hLQ : L ≤ pCoreOf 2 P := fun l hl =>
      CFSG.GH74.QTGen4.DSGen4.frattini_faithful h.charTwo l (h.le hl) (fun q hq => hcon l hl q hq)
    have hL2 : IsPGroup 2 L := hQ.to_le hLQ
    have htop : (⊤ : Subgroup ↥L) ≤ CFSG.pCore 2 ↥L :=
      le_sSup (show (⊤ : Subgroup ↥L).Normal ∧ IsPGroup 2 (⊤ : Subgroup ↥L) from
        ⟨inferInstance, hL2.to_subgroup ⊤⟩)
    have hsub : Subsingleton (oTwoQuot ↥L) :=
      QuotientGroup.subsingleton_iff.2 (eq_top_iff.2 htop)
    haveI := hsub
    have h1 : Nat.card (oTwoQuot ↥L) = 1 := Nat.card_of_subsingleton 1
    have h60 := h.quot.card (by norm_num : 1 ≤ 2)
    rw [h1] at h60
    norm_num at h60
  exact CFSG.GH74.QTGen4.DSGen4.faithful_a5 h.le h.norm hEP
    (CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 P)
    (fun g hg => frattiniChief_mem_normalizer _ (CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 P hg))
    (frattiniChief_isElemSec (pCoreOf 2 P) hQ) hcard h.quot
    (fun q hq e he => frattiniChief_comm_mem (pCoreOf 2 P) hQ hq he) hnt

end CFSG.GH74.QTGen4.DSGen4
