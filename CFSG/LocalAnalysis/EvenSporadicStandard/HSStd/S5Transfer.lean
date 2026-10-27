module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.EvenSporadicStandard.HSStd.Transfer

open Subgroup CFSG.Assembly

theorem kProper_of_injective {C : GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X) {G H : Type} [Group G]
    [Group H] (f : G →* H) (hf : Function.Injective f) (hH : KProper C H) : KProper C G :=
  CFSG.KCore.KProperNonab.of_injective hC hH f hf

theorem card_oddCore_odd (H : Type*) [Group H] [Finite H] : Odd (Nat.card (CFSG.oddCore H)) :=
  CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := H)

theorem oddCore_map_le_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] (e : X ≃* Y) :
    (CFSG.oddCore X).map e.toMonoidHom ≤ CFSG.oddCore Y := by
  refine le_sSup ⟨Subgroup.Normal.map inferInstance _ e.surjective, ?_⟩
  rw [Subgroup.card_map_of_injective e.injective]
  exact card_oddCore_odd X

theorem oddCore_map_subtype_le {Y : Type} [Group Y] [Finite Y] (Q : Subgroup Y) [Q.Normal] :
    (CFSG.oddCore ↥Q).map Q.subtype ≤ CFSG.oddCore Y := by
  have hodd : Odd (Nat.card ((CFSG.oddCore ↥Q).map Q.subtype)) := by
    rw [Subgroup.card_map_of_injective Q.subtype_injective]
    exact card_oddCore_odd Q
  have hnorm : ((CFSG.oddCore ↥Q).map Q.subtype).Normal := by
    refine ⟨fun n hn y => ?_⟩
    obtain ⟨q, hq, rfl⟩ := hn
    have h1 : (MulAut.conjNormal y : MulAut ↥Q) q ∈ CFSG.oddCore ↥Q :=
      oddCore_map_le_mulEquiv (MulAut.conjNormal y : ↥Q ≃* ↥Q) ⟨q, hq, rfl⟩
    exact ⟨_, h1, by simp [MulAut.conjNormal_apply]⟩
  exact le_sSup ⟨hnorm, hodd⟩

theorem oddCore_map_le_of_injective {R Y : Type} [Group R] [Group Y] [Finite R] [Finite Y]
    (f : R →* Y) (hf : Function.Injective f) (hn : f.range.Normal) :
    (CFSG.oddCore R).map f ≤ CFSG.oddCore Y := by
  let e : R ≃* f.range := MonoidHom.ofInjective hf
  have h1 : (CFSG.oddCore R).map f =
      ((CFSG.oddCore R).map e.toMonoidHom).map f.range.subtype := by
    rw [Subgroup.map_map]
    rfl
  rw [h1]
  exact (Subgroup.map_mono (oddCore_map_le_mulEquiv e)).trans (oddCore_map_subtype_le f.range)

theorem exists_noncomm_of_quasisimple_open {G : Type*} [Group G] (h : CFSG.Open.IsQuasisimple G) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := h
  have hbot : commutator G = ⊥ := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun x _ =>
      mem_centralizer_iff.2 fun y _ => hcon y x
  rw [hbot] at h1
  have key : ∀ a : G, a = 1 := fun a => by
    have : a ∈ (⊥ : Subgroup G) := by
      rw [h1]
      exact Subgroup.mem_top a
    exact Subgroup.mem_bot.1 this
  have hsub : Subsingleton G := ⟨fun a b => (key a).trans (key b).symm⟩
  have hsub' : Subsingleton (G ⧸ center G) :=
    Function.Surjective.subsingleton (QuotientGroup.mk_surjective (s := center G))
  exact not_subsingleton _ hsub'

theorem le_commutator_of_quasisimple_open {H : Type} [Group H] (A : Subgroup H)
    (hq : CFSG.Open.IsQuasisimple ↥A) : A ≤ commutator H := by
  intro a ha
  have h1 : (⟨a, ha⟩ : ↥A) ∈ commutator ↥A := by
    rw [hq.1]
    exact Subgroup.mem_top _
  have h2 : ((⟨a, ha⟩ : ↥A) : H) ∈ (commutator ↥A).map A.subtype := ⟨_, h1, rfl⟩
  have h3 : (commutator ↥A).map A.subtype ≤ commutator H := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact h3 h2

theorem cyclic_sylow_of_sylow_card_two {C : Type*} [Group C] [Finite C]
    (h : ∀ S : Sylow 2 C, Nat.card S = 2) : ∃ S : Sylow 2 C, IsCyclic S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 C))
  exact ⟨S, isCyclic_of_prime_card (p := 2) (h S)⟩

section Subgroup

variable {H : Type} [Group H] {N A : Subgroup H}

theorem centralizer_subgroupOf (hAN : A ≤ N) :
    centralizer ((A.subgroupOf N : Subgroup N) : Set N) =
      (centralizer (A : Set H)).subgroupOf N := by
  ext x
  simp only [mem_centralizer_iff, mem_subgroupOf]
  constructor
  · intro h a ha
    have := h ⟨a, hAN ha⟩ ha
    exact congrArg Subtype.val this
  · intro h a ha
    exact Subtype.ext (h (a : H) ha)

theorem sylow_card_centralizer_subgroupOf [Finite H] (hAN : A ≤ N)
    (hCN : centralizer (A : Set H) ≤ N)
    (hsyl : ∀ S : Sylow 2 (centralizer (A : Set H)), Nat.card S = 2)
    (S : Sylow 2 (centralizer ((A.subgroupOf N : Subgroup N) : Set N))) : Nat.card S = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : ↥(centralizer ((A.subgroupOf N : Subgroup N) : Set N)) ≃* ↥(centralizer (A : Set H)) :=
    (MulEquiv.subgroupCongr (centralizer_subgroupOf hAN)).trans
      (Subgroup.subgroupOfEquivOfLe hCN)
  have h := hsyl (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S)
  have h2 : Nat.card ↥(Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S) = Nat.card S :=
    Subgroup.card_map_of_injective e.injective
  exact h2.symm.trans h

theorem mem_normalizer_subgroupOf_iff {X : Subgroup H} (hXN : X ≤ N) (g : N) :
    g ∈ normalizer ((X.subgroupOf N : Subgroup N) : Set N) ↔
      (g : H) ∈ normalizer (X : Set H) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h x
    by_cases hx : x ∈ N
    · have := h ⟨x, hx⟩
      simpa [mem_subgroupOf] using this
    · constructor
      · intro hxX
        exact absurd (hXN hxX) hx
      · intro hconj
        refine absurd ?_ hx
        have h1 : (g : H)⁻¹ * ((g : H) * x * (g : H)⁻¹) * (g : H) ∈ N :=
          N.mul_mem (N.mul_mem (N.inv_mem g.2) (hXN hconj)) g.2
        simpa [mul_assoc] using h1
  · intro h x
    have := h (x : H)
    simpa [mem_subgroupOf] using this

theorem standard_subgroupOf (hAN : A ≤ N) (hCN : centralizer (A : Set H) ≤ N)
    (hA : CFSG.Open.standardComponentIsStandard A) :
    CFSG.Open.standardComponentIsStandard (A.subgroupOf N) :=
  CFSG.Open.standardComponentIsStandard.subgroupOf hA hAN (by rw [inf_eq_left.mpr hCN]; exact hA.2.1)

theorem oddCore_centralizer_subgroupOf [Finite H] (hN : N.Normal)
    (hbal : ∀ t : H, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set H)) = ⊥) (t : N)
    (ht : orderOf t = 2) :
    CFSG.Open.standardComponentOddCore (centralizer ({t} : Set N)) = ⊥ := by
  have ht0 : orderOf (t : H) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have hb := hbal (t : H) ht0
  let f : centralizer ({t} : Set N) →* centralizer ({(t : H)} : Set H) :=
    MonoidHom.codRestrict (N.subtype.comp (centralizer ({t} : Set N)).subtype) _ (fun x => by
      have h1 := mem_centralizer_singleton_iff.1 x.2
      exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val h1))
  have hf : Function.Injective f := fun x y h => by
    have h1 := congrArg (fun z : ↥(centralizer ({(t : H)} : Set H)) => (z : H)) h
    exact Subtype.ext (Subtype.ext h1)
  have hrange : f.range = N.subgroupOf (centralizer ({(t : H)} : Set H)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact x.1.2
    · intro hy
      refine ⟨⟨⟨(y : H), hy⟩, mem_centralizer_singleton_iff.2 (Subtype.ext ?_)⟩, Subtype.ext rfl⟩
      exact (mem_centralizer_singleton_iff.1 y.2)
  have hrn : f.range.Normal := by
    rw [hrange]
    exact hN.subgroupOf _
  have h1 := oddCore_map_le_of_injective f hf hrn
  rw [hb, le_bot_iff] at h1
  exact Subgroup.map_injective hf (h1.trans (Subgroup.map_bot f).symm)

theorem stdHyp_subgroupOf [Finite H] (hN : N.Normal) (hsimple : IsSimpleGroup N)
    (hkp : KProper CFSG.Blueprint.Catalog H) (hAN : A ≤ N) (hCN : centralizer (A : Set H) ≤ N)
    (hA : CFSG.Open.standardComponentIsStandard A)
    (hbal : ∀ t : H, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set H)) = ⊥)
    (hsyl : ∀ S : Sylow 2 (centralizer (A : Set H)), Nat.card S = 2)
    (hcenter : IsPGroup 2 (center (A.subgroupOf N))) :
    StdHyp N (A.subgroupOf N) := by
  have hstd := standard_subgroupOf hAN hCN hA
  refine ⟨hsimple, ?_, ?_, hstd, ?_, ?_, hcenter⟩
  · obtain ⟨a, b, hab⟩ := exists_noncomm_of_quasisimple_open hstd.1
    exact ⟨a, b, fun h => hab (Subtype.ext h)⟩
  · exact kProper_of_injective (fun e h => CFSG.SectionRank.catalog_of_mulEquiv e h) N.subtype
      N.subtype_injective hkp
  · exact fun t ht => oddCore_centralizer_subgroupOf hN hbal t ht
  · exact cyclic_sylow_of_sylow_card_two (sylow_card_centralizer_subgroupOf hAN hCN hsyl)

end Subgroup

end CFSG.EvenSporadicStandard.HSStd.Transfer
