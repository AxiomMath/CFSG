module

public import CFSG.GH74.Uniqueness.SU.SU8Act
public import CFSG.GH74.Uniqueness.SU.SU8BK2

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU8.Setup
  CFSG.GH74.Uniqueness.SU.SU8.Act CFSG.GH74.Uniqueness.SU.SU8.BLift
open scoped commutatorElement Pointwise

section Generic

variable {G : Type} [Group G] {H L A V₀ : Subgroup G}

theorem card_inf_subgroupOf (hVH : V₀ ≤ H) :
    Nat.card ↥(V₀.subgroupOf H ⊓ L.subgroupOf H) = Nat.card ↥(V₀ ⊓ L) := by
  have h : V₀.subgroupOf H ⊓ L.subgroupOf H = (V₀ ⊓ L).subgroupOf H := by
    ext x; simp [Subgroup.mem_subgroupOf]
  rw [h]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hVH : V₀ ⊓ L ≤ H)).toEquiv

theorem CaseB.of_subgroupOf {z : G} (hLH : L ≤ H) (hAH : A ≤ H) (hVH : V₀ ≤ H) (hzH : z ∈ H)
    (hcent : ∀ g : G, g * z = z * g → g ∈ H)
    (cb : CaseB (L.subgroupOf H) (A.subgroupOf H) (V₀.subgroupOf H) ⟨z, hzH⟩) :
    CaseB L A V₀ z := by
  have hmemA : ∀ (a : G) (ha : a ∈ A), (⟨a, hAH ha⟩ : ↥H) ∈ A.subgroupOf H := fun a ha =>
    Subgroup.mem_subgroupOf.mpr ha
  have hnorm : ∀ (g : G) (hg : g ∈ L ⊓ normalizer (A : Set G)),
      (⟨g, hLH hg.1⟩ : ↥H) ∈
        L.subgroupOf H ⊓ normalizer ((A.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro g hg
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hg.1,
      (mem_normalizer_subgroupOf hAH _).mpr hg.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    have := cb.A_exp ⟨a, hAH ha⟩ (hmemA a ha)
    simpa using congrArg Subtype.val this
  · intro a ha b hb
    have := cb.A_comm ⟨a, hAH ha⟩ (hmemA a ha) ⟨b, hAH hb⟩ (hmemA b hb)
    simpa using congrArg Subtype.val this
  · intro v hv
    have h1 : (⟨v, hVH hv⟩ : ↥H) ∈ V₀.subgroupOf H := Subgroup.mem_subgroupOf.mpr hv
    exact Subgroup.mem_subgroupOf.mp (cb.V₀_le h1)
  · exact Subgroup.mem_subgroupOf.mp cb.z_mem
  · intro h
    exact cb.z_ne (Subtype.ext h)
  · have h1 := cb.card_A
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv] at h1
    exact h1
  · intro g hg c hc
    have := cb.act_C ⟨g, hLH hg.1⟩ (hnorm g hg) ⟨c, hVH hc⟩ (Subgroup.mem_subgroupOf.mpr hc)
    simpa using congrArg Subtype.val this
  · have h1 := cb.inf_gt
    rwa [card_inf_subgroupOf hVH] at h1
  · have h1 := cb.inf_le
    rwa [card_inf_subgroupOf hVH] at h1
  · obtain ⟨g₀, hg₀, ⟨e, he⟩, h7, hfpf, htr, hact⟩ := cb.gen
    have hg₀' := Subgroup.mem_inf.mp hg₀
    have hg₀L : (g₀ : G) ∈ L := Subgroup.mem_subgroupOf.mp hg₀'.1
    have hg₀N : (g₀ : G) ∈ normalizer (A : Set G) :=
      (mem_normalizer_subgroupOf hAH g₀).mp hg₀'.2
    refine ⟨(g₀ : G), ⟨hg₀L, hg₀N⟩, ⟨e, ?_⟩, ?_, ?_, ?_, ?_⟩
    · have := congrArg Subtype.val he
      simpa using this
    · intro a ha
      have := h7 ⟨a, hAH ha⟩ (hmemA a ha)
      simpa using congrArg Subtype.val this
    · intro a ha haV j hj0 hj7 hmem
      refine hfpf ⟨a, hAH ha⟩ (hmemA a ha) (fun h => haV (Subgroup.mem_subgroupOf.mp h)) j hj0 hj7 ?_
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hmem)
    · intro a ha haV b hb hbV
      obtain ⟨j, hj⟩ := htr ⟨a, hAH ha⟩ (hmemA a ha) (fun h => haV (Subgroup.mem_subgroupOf.mp h))
        ⟨b, hAH hb⟩ (hmemA b hb) (fun h => hbV (Subgroup.mem_subgroupOf.mp h))
      exact ⟨j, by simpa using Subgroup.mem_subgroupOf.mp hj⟩
    · intro m hm
      obtain ⟨j, hj⟩ := hact ⟨m, hLH hm.1⟩ (hnorm m hm)
      refine ⟨j, fun a ha => ?_⟩
      have := hj ⟨a, hAH ha⟩ (hmemA a ha)
      simpa using Subgroup.mem_subgroupOf.mp this
  · intro hV
    have hV' : Nat.card ↥(V₀.subgroupOf H) = 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv]
      exact hV
    obtain ⟨t, ht, ⟨k, hk⟩, a, ha, hta⟩ := cb.two_elt hV'
    have ht' := Subgroup.mem_inf.mp ht
    refine ⟨(t : G), ⟨Subgroup.mem_subgroupOf.mp ht'.1,
      (mem_normalizer_subgroupOf hAH t).mp ht'.2⟩, ⟨k, ?_⟩, (a : G),
      Subgroup.mem_subgroupOf.mp ha, fun h => hta (Subtype.ext ?_)⟩
    · have := congrArg Subtype.val hk
      simpa using this
    · simpa using h
  · intro hV g hg hgz
    have hV' : Nat.card ↥(V₀.subgroupOf H) = 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv]
      exact hV
    have hgH : g ∈ H := hcent g hgz
    obtain ⟨m, hm, hma⟩ := cb.cent hV' ⟨g, hgH⟩ ((mem_normalizer_subgroupOf hAH _).mpr hg)
      (Subtype.ext (by simpa using hgz))
    have hm' := Subgroup.mem_inf.mp hm
    refine ⟨(m : G), ⟨Subgroup.mem_subgroupOf.mp hm'.1,
      (mem_normalizer_subgroupOf hAH m).mp hm'.2⟩, fun a ha => ?_⟩
    have := hma ⟨a, hAH ha⟩ (hmemA a ha)
    simpa using congrArg Subtype.val this

end Generic

section Hyp

variable {G : Type} [Group G] [Finite G] {z : G} {S L A : Subgroup G}

theorem Hyp20A.preHyp (hyp : Hyp20A z S L A) [(L.subgroupOf (Hz z)).Normal] :
    BK.PreHyp (pPrimeCore 2 ↥(Hz z)) (L.subgroupOf (Hz z)) (A.subgroupOf (Hz z)) := by
  have hAH := hyp.A_le_H
  refine ⟨odd_card_core (Hz z), ?_, ?_, ?_, ?_⟩
  · intro a ha
    have := hyp.A_elem.2 (a : G) (Subgroup.mem_subgroupOf.mp ha)
    exact Subtype.ext (by simpa [sq] using this)
  · intro a ha b hb
    have := hyp.A_elem.1.is_comm.comm
      (⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩ : ↥A) ⟨(b : G), Subgroup.mem_subgroupOf.mp hb⟩
    have h2 : (a : G) * (b : G) = (b : G) * (a : G) := congrArg Subtype.val this
    exact Subtype.ext h2
  · intro a ha
    have ha' : (a : G) ∈ L ⊔ centralizerBar (Hz z) L := hyp.A_le (Subgroup.mem_subgroupOf.mp ha)
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left L (centralizerBar (Hz z) L)
      ((centralizerBar_le _ _).trans hyp.L_normal)
    have ha'' : (a : G) ∈ (L : Set G) * (centralizerBar (Hz z) L : Set G) := by
      rw [← hmul]; exact ha'
    obtain ⟨y, hy, w, hw, hyw⟩ := Set.mem_mul.mp ha''
    have hwH : w ∈ Hz z := centralizerBar_le _ _ hw
    refine ⟨⟨y, hyp.L_le hy⟩, Subgroup.mem_subgroupOf.mpr hy, ⟨w, hwH⟩, ?_, ?_⟩
    · intro m hm
      obtain ⟨hg, hc⟩ := mem_centralizerBar.mp hw
      exact bar_commutator_mem_iff.mpr (hc m (Subgroup.mem_subgroupOf.mp hm)).symm
    · exact Subtype.ext hyw.symm
  · have hSH : S ≤ Hz z := hyp.S_sylow_H.1
    have hSp : IsPGroup 2 ↥(S.subgroupOf (Hz z)) :=
      hyp.S_sylow_H.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
    have hSidx : ¬ 2 ∣ (S.subgroupOf (Hz z)).index := by
      have h1 : Odd (S.relIndex (Hz z)) := hyp.S_sylow_H.2.2
      intro h2
      exact (Nat.not_even_iff_odd.mpr h1) (even_iff_two_dvd.mpr h2)
    refine ⟨hSp.toSylow hSidx, fun s hs hss => ?_⟩
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs.1
    have hsL : (s : G) ∈ L := Subgroup.mem_subgroupOf.mp hs.2
    have hss' : (s : G) * (s : G) = 1 := by simpa using congrArg Subtype.val hss
    have hmem : (s : G) ∈ omegaOne (S ⊓ L) ⊔ zpowers z :=
      Subgroup.mem_sup_left (Subgroup.subset_closure ⟨⟨hsS, hsL⟩, hss'⟩)
    exact Subgroup.mem_subgroupOf.mpr (hyp.A_ge hmem)

omit [Finite G] in
theorem mem_centralizerBar_iff_comm {H L : Subgroup G} (c : ↥H) :
    (c : G) ∈ centralizerBar H L ↔ ∀ m ∈ L.subgroupOf H, ⁅c, m⁆ ∈ pPrimeCore 2 ↥H := by
  rw [mem_centralizerBar]
  constructor
  · rintro ⟨hg, hc⟩ m hm
    exact bar_commutator_mem_iff.mpr (hc m (Subgroup.mem_subgroupOf.mp hm)).symm
  · intro hc
    exact ⟨c.2, fun l hl => (bar_commutator_mem_iff.mp (hc ⟨l, _⟩ hl)).symm⟩

omit [Finite G] in
theorem ACx_eq {H L A : Subgroup G} :
    BLift.ACx (pPrimeCore 2 ↥H) (L.subgroupOf H) (A.subgroupOf H) =
      (A ⊓ centralizerBar H L).subgroupOf H := by
  ext x
  rw [BLift.mem_ACx, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    mem_centralizerBar_iff_comm]

end Hyp

end CFSG.GH74.Uniqueness.SU.SU8
