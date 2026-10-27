module

public import CFSG.GH74.Uniqueness.SU.SU8Lift

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU8.Setup
open CFSG.GH74.Uniqueness.Bender
open scoped commutatorElement Pointwise

namespace Act

variable {G : Type} [Group G] [Finite G]

structure ActData (A L AC : Subgroup G) (n : ℕ) : Prop where
  two_le : 2 ≤ n
  ac_le : AC ≤ A
  card_AL : Nat.card ↥(A ⊓ L) = 2 ^ n
  split : ∀ a ∈ A, ∃ u ∈ A ⊓ L, ∃ c ∈ AC, a = u * c
  inf_bot : ∀ x ∈ A ⊓ L, x ∈ AC → x = 1
  act_C : ∀ g ∈ L ⊓ normalizer (A : Set G), ∀ c ∈ AC, g * c * g⁻¹ = c
  trans : ∀ u ∈ A ⊓ L, u ≠ 1 → ∀ v ∈ A ⊓ L, v ≠ 1 →
    ∃ g ∈ L ⊓ normalizer (A : Set G), g * u * g⁻¹ = v
  cyclic : ∃ g₀ ∈ L ⊓ normalizer (A : Set G),
    (∀ g ∈ L ⊓ normalizer (A : Set G),
      ∃ j : ℤ, ∀ a ∈ A, g * a * g⁻¹ = g₀ ^ j * a * (g₀ ^ j)⁻¹) ∧
    ∃ k : ℕ, Odd k ∧ ∀ a ∈ A, g₀ ^ k * a * (g₀ ^ k)⁻¹ = a
  free : ∀ g ∈ L ⊓ normalizer (A : Set G), ∀ u ∈ A ⊓ L, u ≠ 1 → g * u * g⁻¹ = u →
    ∀ a ∈ A, g * a * g⁻¹ = a

omit [Finite G] in
theorem mem_normalizer_subgroupOf {H A : Subgroup G} (hAH : A ≤ H) (g : ↥H) :
    g ∈ normalizer ((A.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
      (g : G) ∈ normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    by_cases hxH : x ∈ H
    · have := h ⟨x, hxH⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · have h1 : x ∉ A := fun hx => hxH (hAH hx)
      have h2 : (g : G) * x * (g : G)⁻¹ ∉ A := fun hx => by
        apply hxH
        have := hAH hx
        have hg := g.2
        have : x = (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * g := by group
        rw [this]
        exact H.mul_mem (H.mul_mem (H.inv_mem hg) ‹_›) hg
      exact ⟨fun hx => absurd hx h1, fun hx => absurd hx h2⟩
  · intro h x
    have := h (x : G)
    simpa [Subgroup.mem_subgroupOf] using this

omit [Finite G] in
theorem ActData.of_liftOut {H L A : Subgroup G} (hLH : L ≤ H) (hAH : A ≤ H)
    [(L.subgroupOf H).Normal] {n : ℕ}
    (hout : Lift.LiftOut (pPrimeCore 2 ↥H) (L.subgroupOf H) (A.subgroupOf H) n) :
    ActData A L (A ⊓ centralizerBar H L) n := by
  have hcB : ∀ c : ↥H, (c : G) ∈ centralizerBar H L ↔
      ∀ m ∈ L.subgroupOf H, ⁅c, m⁆ ∈ pPrimeCore 2 ↥H := by
    intro c
    rw [mem_centralizerBar]
    constructor
    · rintro ⟨hg, hc⟩ m hm
      exact bar_commutator_mem_iff.mpr (hc m (Subgroup.mem_subgroupOf.mp hm)).symm
    · intro hc
      exact ⟨c.2, fun l hl => (bar_commutator_mem_iff.mp (hc ⟨l, _⟩ hl)).symm⟩
  have hA' : ∀ x : ↥H, x ∈ A.subgroupOf H ↔ (x : G) ∈ A := fun x => Subgroup.mem_subgroupOf
  have hL' : ∀ x : ↥H, x ∈ L.subgroupOf H ↔ (x : G) ∈ L := fun x => Subgroup.mem_subgroupOf
  have hnorm : ∀ g : ↥H, g ∈ normalizer ((A.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
      (g : G) ∈ normalizer (A : Set G) := mem_normalizer_subgroupOf hAH
  refine ⟨hout.two_le, inf_le_left, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := hout.card_AL
    have h2 : (A ⊓ L).subgroupOf H = A.subgroupOf H ⊓ L.subgroupOf H := by
      ext x; simp [Subgroup.mem_subgroupOf]
    rw [← h2] at h1
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hAH : A ⊓ L ≤ H)).toEquiv] at h1
    exact h1
  · intro a ha
    obtain ⟨l, hl, c, hc, hcomm, hac⟩ := hout.split ⟨a, hAH ha⟩ ((hA' _).mpr ha)
    refine ⟨(l : G), ⟨(hA' l).mp hl.1, (hL' l).mp hl.2⟩, (c : G),
      Subgroup.mem_inf.mpr ⟨(hA' c).mp hc, (hcB c).mpr hcomm⟩, ?_⟩
    simpa using congrArg Subtype.val hac
  · intro x hx hxC
    have hxH : x ∈ H := hAH hx.1
    have := hout.inf_bot ⟨x, hxH⟩ ⟨(hA' _).mpr hx.1, (hL' _).mpr hx.2⟩
      ((hcB ⟨x, hxH⟩).mp (Subgroup.mem_inf.mp hxC).2)
    simpa using congrArg Subtype.val this
  · intro g hg c hc
    have hgH : g ∈ H := hLH hg.1
    have hcA := (Subgroup.mem_inf.mp hc).1
    have hcB' := (Subgroup.mem_inf.mp hc).2
    have hcH : c ∈ H := hAH hcA
    have := hout.act_C ⟨g, hgH⟩ ⟨(hL' _).mpr hg.1, (hnorm _).mpr hg.2⟩ ⟨c, hcH⟩
      ((hA' _).mpr hcA) ((hcB ⟨c, hcH⟩).mp hcB')
    simpa using congrArg Subtype.val this
  · intro u hu hu1 v hv hv1
    have huH : u ∈ H := hAH hu.1
    have hvH : v ∈ H := hAH hv.1
    obtain ⟨g, hg, hgu⟩ := hout.trans ⟨u, huH⟩ ⟨(hA' _).mpr hu.1, (hL' _).mpr hu.2⟩
      (fun h => hu1 (congrArg Subtype.val h)) ⟨v, hvH⟩ ⟨(hA' _).mpr hv.1, (hL' _).mpr hv.2⟩
      (fun h => hv1 (congrArg Subtype.val h))
    refine ⟨(g : G), ⟨(hL' g).mp hg.1, (hnorm g).mp hg.2⟩, ?_⟩
    simpa using congrArg Subtype.val hgu
  · obtain ⟨g₀, hg₀, hcyc, k, hk, hkA⟩ := hout.cyclic
    refine ⟨(g₀ : G), ⟨(hL' g₀).mp hg₀.1, (hnorm g₀).mp hg₀.2⟩, ?_, k, hk, ?_⟩
    · intro g hg
      have hgH : g ∈ H := hLH hg.1
      obtain ⟨j, hj⟩ := hcyc ⟨g, hgH⟩ ⟨(hL' _).mpr hg.1, (hnorm _).mpr hg.2⟩
      refine ⟨j, fun a ha => ?_⟩
      have := hj ⟨a, hAH ha⟩ ((hA' _).mpr ha)
      simpa using congrArg Subtype.val this
    · intro a ha
      have := hkA ⟨a, hAH ha⟩ ((hA' _).mpr ha)
      simpa using congrArg Subtype.val this
  · intro g hg u hu hu1 hgu a ha
    have hgH : g ∈ H := hLH hg.1
    have huH : u ∈ H := hAH hu.1
    have := hout.free ⟨g, hgH⟩ ⟨(hL' _).mpr hg.1, (hnorm _).mpr hg.2⟩ ⟨u, huH⟩
      ⟨(hA' _).mpr hu.1, (hL' _).mpr hu.2⟩ (fun h => hu1 (congrArg Subtype.val h))
      (Subtype.ext (by simpa using hgu)) ⟨a, hAH ha⟩ ((hA' _).mpr ha)
    simpa using congrArg Subtype.val this

end Act

open Act

variable {G : Type} [Group G] [Finite G] {z : G} {S L A : Subgroup G}

omit [Finite G] in
theorem Hyp20A.L_le (hyp : Hyp20A z S L A) : L ≤ Hz z := hyp.L_comp.1

omit [Finite G] in
theorem Hyp20A.A_le_H (hyp : Hyp20A z S L A) : A ≤ Hz z :=
  hyp.A_le.trans (sup_le hyp.L_le (centralizerBar_le _ _))

omit [Finite G] in
theorem Hyp20A.normal_subgroupOf (hyp : Hyp20A z S L A) : (L.subgroupOf (Hz z)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hyp.L_le).mpr hyp.L_normal

omit [Finite G] in
theorem Hyp20A.exists_benderType (hyp : Hyp20A z S L A)
    (hZ : center ↥(hbarImage (Hz z) L) = ⊥) :
    ∃ n i e, BenderType ↥(hbarImage (Hz z) L) n i e := by
  rcases hyp.L_bender with h | ⟨⟨e⟩⟩
  · exact isBenderGroup_iff_exists_benderType.mp h
  · have e' : ↥(hbarImage (Hz z) L) ≃* CFSG.Theory.Comparator.SzModel 1 :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
    exact ⟨2 * 1 + 1, 2, 1, BenderType.suzuki 1 le_rfl e'⟩

theorem Hyp20A.liftHyp (hyp : Hyp20A z S L A) [(L.subgroupOf (Hz z)).Normal] {n i e : ℕ}
    (hBT : BenderType ↥(hbarImage (Hz z) L) n i e) :
    Lift.LiftHyp (pPrimeCore 2 ↥(Hz z)) (L.subgroupOf (Hz z)) (A.subgroupOf (Hz z)) n i e := by
  have hAH := hyp.A_le_H
  refine ⟨odd_card_core (Hz z), ?_, ?_, ?_, ?_, hBT⟩
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

theorem Hyp20A.actData (hyp : Hyp20A z S L A) {n i e : ℕ}
    (hBT : BenderType ↥(hbarImage (Hz z) L) n i e) :
    ActData A L (A ⊓ centralizerBar (Hz z) L) n := by
  have := hyp.normal_subgroupOf
  exact ActData.of_liftOut hyp.L_le hyp.A_le_H (hyp.liftHyp hBT).out

end CFSG.GH74.Uniqueness.SU.SU8
