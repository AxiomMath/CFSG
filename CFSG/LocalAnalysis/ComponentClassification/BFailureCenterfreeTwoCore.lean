module

public import CFSG.LocalAnalysis.ComponentClassification.BFailureLocalization
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalPComponentCore

public section

namespace CFSG.ComponentClassification.BFailureCenterfree

open CFSG.Open CFSG.ComponentClassification.BFailureLocalization

variable {G : Type*} [Group G] [Finite G]

theorem twoComponent_le_of_sup {S C K : Subgroup G} [C.Normal] (hS2 : IsPGroup 2 S)
    (hKJ : K ≤ S ⊔ C) (hK : TwoComponents.IsTwoComponent (K.subgroupOf (S ⊔ C))) : K ≤ C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X := K.subgroupOf (S ⊔ C)
  have : Group.IsPerfect X := ⟨TwoComponents.perfect hK⟩
  let φ : X →* G ⧸ C := (QuotientGroup.mk' C).comp ((S ⊔ C).subtype.comp X.subtype)
  have hrange : φ.range ≤ S.map (QuotientGroup.mk' C) := by
    rintro _ ⟨x, rfl⟩
    have hxJ : ((x : ↥(S ⊔ C)) : G) ∈ (S ⊔ C : Subgroup G) := (x : ↥(S ⊔ C)).2
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hxJ
    obtain ⟨s, hs, c, hc, hsc⟩ := hxJ
    refine ⟨s, hs, ?_⟩
    change QuotientGroup.mk' C s = QuotientGroup.mk' C ((x : ↥(S ⊔ C)) : G)
    have hc1 : QuotientGroup.mk' C c = 1 := (QuotientGroup.eq_one_iff c).2 hc
    rw [← hsc, map_mul, hc1, mul_one]
  have hp : IsPGroup 2 (X ⧸ φ.ker) :=
    ((hS2.map _).to_le hrange).of_equiv (QuotientGroup.quotientKerEquivRange φ).symm
  have htop := LiteratureLocal.eq_top_of_isPGroup_quotient_of_perfect φ.ker hp
  intro k hk
  have hmem : (⟨⟨k, hKJ hk⟩, hk⟩ : X) ∈ φ.ker := htop ▸ Subgroup.mem_top _
  exact (QuotientGroup.eq_one_iff k).1 hmem

theorem centerfree_minimal_B_failure_two_core_trivial
    (hodd : Odd (Nat.card (Subgroup.center G)))
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X)
    {S : Subgroup G} (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hfail : ¬ (TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G))).map
        (Subgroup.normalizer (S : Set G)).subtype ≤ TwoComponents.badSubgroup G) :
    CFSG.pCore 2 G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 G with hPdef
  set H := Subgroup.normalizer (S : Set G) with hHdef
  set C := Subgroup.centralizer (P : Set G) with hCdef
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup
  have hCn : C.Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [hCdef, Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : g⁻¹ * x * g ∈ P := by
      have := (CFSG.pCore_normal (p := 2) (G := G)).conj_mem x hx g⁻¹
      rwa [inv_inv] at this
    have h := hc _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * x := by group
  have hHC : (TwoComponents.badSubgroup H).map H.subtype ≤ C :=
    LiteratureLocal.badSubgroup_normalizer_le_centralizer_pCore hS2
  have hJ : S ⊔ C = ⊤ := by
    by_contra hJ
    apply hfail
    have hcontained : (TwoComponents.badSubgroup H).map H.subtype ≤
        (TwoComponents.badSubgroup (H ⊓ (S ⊔ C) : Subgroup G)).map (H ⊓ (S ⊔ C)).subtype := by
      rw [BadComponents.ambient_description, BadComponents.ambient_description]
      apply sSup_le
      rintro L ⟨hLH, hL, hnq⟩
      have hLbad : L ≤ (TwoComponents.badSubgroup H).map H.subtype := by
        rw [BadComponents.ambient_description]
        exact le_sSup ⟨hLH, hL, hnq⟩
      have hLJ : L ≤ S ⊔ C := (hLbad.trans hHC).trans le_sup_right
      exact le_sSup ⟨le_inf hLH hLJ, TwoComponentTransport.restrict_nested L (H ⊓ (S ⊔ C)) H
        (le_inf hLH hLJ) inf_le_left hL, hnq⟩
    have hJG : (TwoComponents.badSubgroup (S ⊔ C : Subgroup G)).map (S ⊔ C).subtype ≤
        TwoComponents.badSubgroup G := by
      rw [BadComponents.ambient_description]
      apply sSup_le
      rintro K ⟨hKJ, hK, hnq⟩
      have hKC : K ≤ C := twoComponent_le_of_sup hS2 hKJ hK
      have hKC' : TwoComponents.IsTwoComponent (K.subgroupOf C) :=
        TwoComponentTransport.restrict_nested K C (S ⊔ C) hKC le_sup_right hK
      have hKG := TwoComponentTransport.of_subnormal_subgroup C
        (Components.chain_of_mathlib_subnormal (Subgroup.Normal.isSubnormal hCn)) _ hKC'
      rw [Subgroup.map_subgroupOf_eq_of_le hKC] at hKG
      exact le_sSup ⟨hKG, hnq⟩
    exact (bad_normalizer_le_overgroup S (S ⊔ C) hS2 le_sup_left hS1 (hproper _ hJ)
      hcontained).trans hJG
  by_contra hP1
  have hT2 : IsPGroup 2 (S ⊔ P : Subgroup G) := hS2.to_sup_of_normal_right hP2
  have : Group.IsNilpotent (S ⊔ P : Subgroup G) := hT2.isNilpotent
  have hPT : (P.subgroupOf (S ⊔ P)).Normal := (CFSG.pCore_normal (p := 2) (G := G)).subgroupOf _
  have hPT1 : P.subgroupOf (S ⊔ P) ≠ ⊥ := by
    intro h
    apply hP1
    have := congrArg (Subgroup.map (S ⊔ P).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le le_sup_right, Subgroup.map_bot] at this
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hPT1)
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  obtain ⟨hyP, hyZ⟩ := Subgroup.mem_inf.mp hy
  have hxP : (y : G) ∈ P := hyP
  have hxZ : (y : G) ∈ Subgroup.center G := by
    have hcent : S ⊔ C ≤ Subgroup.centralizer ({(y : G)} : Set G) := by
      refine sup_le (fun s hs => ?_) (fun c hc => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have := Subgroup.mem_center_iff.mp hyZ ⟨s, Subgroup.mem_sup_left hs⟩
        exact congrArg Subtype.val this
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hc _ hxP).symm
    rw [hJ] at hcent
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcent (Subgroup.mem_top g))
  obtain ⟨a, ha⟩ := hP2.exists_card_eq
  have hcop : (Nat.card (Subgroup.center G)).Coprime (Nat.card P) := by
    rw [ha]
    exact Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hodd)
  have hbot := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  have hx' : (y : G) ∈ Subgroup.center G ⊓ P := Subgroup.mem_inf.mpr ⟨hxZ, hxP⟩
  rw [hbot, Subgroup.mem_bot] at hx'
  exact hy1' (Subtype.ext hx')

end CFSG.ComponentClassification.BFailureCenterfree
