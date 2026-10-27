module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Setting
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BarMNormalizer
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairBlocks

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open CFSG.Open CFSG.AGLEmbedding CFSG.Quasithin
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (barM_mono mem_barM)

variable {G : Type} [Group G] {X S L : Subgroup G}

theorem isPGroup_of_isTwoRadicalIn (hR : IsTwoRadicalIn X S) : IsPGroup 2 S := by
  have h := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (X ⊓ Subgroup.normalizer (S : Set G))
  rw [← hR.2.2] at h
  exact h

theorem inf_le_pCoreOf_normalizer_inf (hA : Asc81bHyp X S) :
    S ⊓ L ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (S : Set G) ⊓ L) := by
  have hS : IsPGroup 2 S := isPGroup_of_isTwoRadicalIn hA.twoRadical
  have hle : S ⊓ L ≤ Subgroup.normalizer (S : Set G) ⊓ L :=
    inf_le_inf_right L Subgroup.le_normalizer
  refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (S ⊓ L) _ hle ?_
    (hS.to_le inf_le_left)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  intro x hx
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hx.1, Subgroup.le_normalizer hx.2⟩

section Equality

variable [Finite G]

theorem pCoreOf_normalizer_inf_le (hA : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L) :
    CFSG.Open.pCoreOf 2 (Subgroup.normalizer (S : Set G) ⊓ L) ≤ S ⊓ L := by
  have hUL : CFSG.Open.pCoreOf 2 (Subgroup.normalizer (S : Set G) ⊓ L) ≤ L :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans inf_le_right
  have hUS : CFSG.Open.pCoreOf 2 (Subgroup.normalizer (S : Set G) ⊓ L) ≤ S := by
    refine CFSG.HardMathSupport.Cooperstein.Coordinator.le_of_le_twoPrimeComponent hA hL hUL
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _) fun g hg => ?_
    have hgY : g ∈ Subgroup.normalizer
        ((Subgroup.normalizer (S : Set G) ⊓ L : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg.1.2, hg.2⟩
    exact CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 _ hgY
  exact le_inf hUS hUL

theorem inf_eq_pCoreOf_normalizer_inf (hA : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L) :
    S ⊓ L = CFSG.Open.pCoreOf 2 (Subgroup.normalizer (S : Set G) ⊓ L) :=
  le_antisymm (inf_le_pCoreOf_normalizer_inf hA) (pCoreOf_normalizer_inf_le hA hL)

end Equality

section BarPCore

variable {Y : Subgroup G}

theorem barM_pCoreOf_le_pCoreOf_barM (hYX : Y ≤ X) :
    barM X (CFSG.Open.pCoreOf 2 Y) ≤ CFSG.Open.pCoreOf 2 (barM X Y) := by
  have hinc : barM X (CFSG.Open.pCoreOf 2 Y) ≤ barM X Y :=
    barM_mono (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 Y)
  have key : ∀ g ∈ barM X Y, ∀ h ∈ barM X (CFSG.Open.pCoreOf 2 Y),
      g * h * g⁻¹ ∈ barM X (CFSG.Open.pCoreOf 2 Y) := by
    intro g hg h hh
    obtain ⟨y, hy, rfl⟩ := (mem_barM _).1 hg
    obtain ⟨o, ho, rfl⟩ := (mem_barM _).1 hh
    refine (mem_barM _).2 ⟨y * o * y⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 Y hy) (o : G)).mp ho
    · simp [map_mul, map_inv]
  have hN : barM X Y ≤ Subgroup.normalizer
      (barM X (CFSG.Open.pCoreOf 2 Y) : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact key g hg h
    · intro hh
      have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hh
      rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this
  refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ hinc
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hinc).mpr hN) ?_
  rintro ⟨x, hx⟩
  obtain ⟨o, ho, rfl⟩ := (mem_barM _).1 hx
  obtain ⟨k, hk⟩ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 Y ⟨o, ho⟩
  have hk' : o ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  refine ⟨k, Subtype.ext ?_⟩
  show (QuotientGroup.mk' (CFSG.pCore 2 ↥X) o) ^ 2 ^ k = 1
  rw [← map_pow, hk', map_one]

theorem pCoreOf_barM_le_barM_pCoreOf (hYX : Y ≤ X) :
    CFSG.Open.pCoreOf 2 (barM X Y) ≤ barM X (CFSG.Open.pCoreOf 2 Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hmk
  set Pb := CFSG.Open.pCoreOf 2 (barM X Y) with hPb
  set P : Subgroup G := ((Pb.comap mk).map X.subtype) ⊓ Y with hP
  have hPY : P ≤ Y := inf_le_right
  have hPb2 : IsPGroup 2 Pb := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _
  have hQ2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥X) := CFSG.pCore_isPGroup
  have hP2 : IsPGroup 2 P := by
    rintro ⟨x, ⟨⟨y, hy, hyx⟩, hxY⟩⟩
    obtain ⟨a, ha⟩ := hPb2 ⟨mk y, hy⟩
    have hya : y ^ 2 ^ a ∈ CFSG.pCore 2 ↥X := by
      have h1 : mk (y ^ 2 ^ a) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val ha
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨b, hb⟩ := hQ2 ⟨_, hya⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : (y ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have : x = (y : G) := hyx.symm
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [this, pow_add, pow_mul]
    have := congrArg Subtype.val hb'
    simpa using this
  have hKP : Y ≤ Subgroup.normalizer (P : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ n ∈ Y, ∀ p ∈ P, n * p * n⁻¹ ∈ P := by
      intro n hn p hp
      obtain ⟨⟨y, hy, hyp⟩, hpY⟩ := hp
      have hnX : n ∈ X := hYX hn
      have hnb : mk ⟨n, hnX⟩ ∈ barM X Y := ⟨⟨n, hnX⟩, hn, rfl⟩
      have hnN' := Subgroup.mem_normalizer_iff.mp
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (barM X Y) hnb)
      refine ⟨⟨⟨n, hnX⟩ * y * ⟨n, hnX⟩⁻¹, ?_, ?_⟩, Y.mul_mem (Y.mul_mem hn hpY) (Y.inv_mem hn)⟩
      · show mk (⟨n, hnX⟩ * y * ⟨n, hnX⟩⁻¹) ∈ Pb
        rw [map_mul, map_mul, map_inv]
        exact (hnN' (mk y)).mp hy
      · have hyp' : (y : G) = p := hyp
        simp [hyp']
    intro p
    constructor
    · exact key n hn p
    · intro hp
      have := key n⁻¹ (Y.inv_mem hn) _ hp
      rwa [show n⁻¹ * (n * p * n⁻¹) * n⁻¹⁻¹ = p by group] at this
  have hPS : P ≤ CFSG.Open.pCoreOf 2 Y :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 P Y hPY
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hPY).mpr hKP) hP2
  intro u hu
  obtain ⟨m, hmY, hmu⟩ := (mem_barM u).1 (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _ hu)
  subst hmu
  exact (mem_barM _).2 ⟨m, hPS ⟨⟨m, hu, rfl⟩, hmY⟩, rfl⟩

end BarPCore

section BarForm

variable [Finite G]

theorem barM_inf_eq_pCoreOf_barM (hA : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L) :
    barM X (S ⊓ L) = CFSG.Open.pCoreOf 2 (barM X (Subgroup.normalizer (S : Set G) ⊓ L)) := by
  have hYX : Subgroup.normalizer (S : Set G) ⊓ L ≤ X := inf_le_right.trans hL.le
  rw [inf_eq_pCoreOf_normalizer_inf hA hL]
  exact le_antisymm (barM_pCoreOf_le_pCoreOf_barM hYX) (pCoreOf_barM_le_barM_pCoreOf hYX)

end BarForm

end CFSG.HardMathSupport.Cooperstein.Proving

end
