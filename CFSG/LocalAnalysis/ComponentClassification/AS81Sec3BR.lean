module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step31
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Lift
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Setup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalQuot
public import CFSG.Sporadic.Suz.Simple
public import CFSG.Foundations
public import CFSG.LargeExtraspecial.Types
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQO
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockOddPairOrbitInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.Blueprint
open scoped Pointwise

namespace Sec3

variable {G : Type} [Group G]

theorem isSylowOf_of_isSylowOf_inf_normalizer' [Finite G] {p : ℕ} [Fact p.Prime]
    {V K : Subgroup G} (hVK : V ≤ K)
    (hsyl : IsSylowOf p V (K ⊓ normalizer (V : Set G))) : IsSylowOf p V K := by
  have hV := hsyl.isPGroup
  obtain ⟨S, hVS⟩ := (hV.comap_subtype : IsPGroup p (V.subgroupOf K)).exists_le_sylow
  set S' : Subgroup G := (S : Subgroup K).map K.subtype with hS'
  have hS'syl : IsSylowOf p S' K := ⟨S, rfl⟩
  have hVS' : V ≤ S' := fun v hv => ⟨⟨v, hVK hv⟩, hVS hv, rfl⟩
  have hN : S' ⊓ normalizer (V : Set G) = V :=
    hsyl.eq_of_le (le_inf hVS' le_normalizer) (inf_le_inf_right _ hS'syl.le)
      (hS'syl.isPGroup.to_le inf_le_left)
  by_cases hVeq : V = S'
  · rw [hVeq]
    exact hS'syl
  exfalso
  have : Group.IsNilpotent ↥S' := hS'syl.isPGroup.isNilpotent
  have hlt : V.subgroupOf S' < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    exact fun h => hVeq (le_antisymm hVS' h)
  have h1 := Group.normalizerCondition_of_isNilpotent _ hlt
  rw [← subgroupOf_normalizer_eq hVS'] at h1
  obtain ⟨y, hy, hyV⟩ := IsConcreteLE.exists_of_lt h1
  apply hyV
  have hy' : (y : G) ∈ S' ⊓ normalizer (V : Set G) := ⟨y.2, hy⟩
  rw [hN] at hy'
  exact hy'

theorem centralizer_le_normalizer_sec3B (A₁ : Subgroup G) (x : G) :
    centralizer ({x} : Set G) ≤ normalizer (sec3B A₁ x : Set G) := by
  have key : ∀ c ∈ centralizer ({x} : Set G), ∀ b ∈ sec3B A₁ x, c * b * c⁻¹ ∈ sec3B A₁ x := by
    rintro c hc _ ⟨b, hb, rfl⟩
    exact ⟨⟨c, hc⟩ * b * ⟨c, hc⟩⁻¹, normalClosure_normal.conj_mem _ hb _, rfl⟩
  intro c hc
  rw [mem_normalizer_iff]
  intro b
  refine ⟨key c hc b, fun h => ?_⟩
  have := key c⁻¹ (inv_mem hc) _ h
  simpa [mul_assoc] using this

theorem sec3B_le_centralizer (A₁ : Subgroup G) (x : G) :
    sec3B A₁ x ≤ centralizer ({x} : Set G) :=
  map_subtype_le _

theorem le_sec3B {A₁ : Subgroup G} {x : G} (h : A₁ ≤ centralizer ({x} : Set G)) :
    A₁ ≤ sec3B A₁ x := fun a ha =>
  ⟨⟨a, h ha⟩, subset_normalClosure (mem_subgroupOf.mpr ha), rfl⟩

theorem mem_of_odd_of_mem_sup [Finite G] {B R : Subgroup G} (hR : IsPGroup 2 R)
    (hRB : R ≤ normalizer (B : Set G)) {k : G} (hk : k ∈ B ⊔ R) (hko : Odd (orderOf k)) :
    k ∈ B := by
  have hk' : k ∈ (B : Set G) * (R : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left B R hRB]
    exact hk
  obtain ⟨b, hb, r, hr, rfl⟩ := hk'
  suffices hrB : r ∈ B from B.mul_mem hb hrB
  have key : ∀ n : ℕ, (b * r) ^ n * r⁻¹ ^ n ∈ B := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : (b * r) ^ (n + 1) * r⁻¹ ^ (n + 1) =
          ((b * r) ^ n * r⁻¹ ^ n) * (r ^ n * b * (r ^ n)⁻¹) := by
        rw [pow_succ, pow_succ, inv_pow]
        group
      rw [e]
      refine B.mul_mem ih ?_
      have hrn : r ^ n ∈ normalizer (B : Set G) := pow_mem (hRB hr) n
      exact (mem_normalizer_iff.mp hrn b).mp hb
  have h1 := key (orderOf (b * r))
  rw [pow_orderOf_eq_one, one_mul, inv_pow] at h1
  have hr2 : r ^ orderOf (b * r) ∈ B := by simpa using B.inv_mem h1
  obtain ⟨m, hm⟩ := hR ⟨r, hr⟩
  have hm' : r ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hcop : (orderOf r).Coprime (orderOf (b * r)) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hm')
    rw [hj]
    exact Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hko)
  have hz : zpowers (r ^ orderOf (b * r)) = zpowers r := by
    refine eq_of_le_of_card_ge (zpowers_le.mpr (pow_mem (mem_zpowers r) _)) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hcop.orderOf_pow]
  have hrz : r ∈ zpowers (r ^ orderOf (b * r)) := hz ▸ mem_zpowers r
  exact zpowers_le.mpr hr2 hrz

end Sec3

@[expose] def sec3K {G : Type} [Group G] (A₁ R : Subgroup G) (x : G) : Subgroup G :=
  sec3B A₁ x ⊔ R

namespace Sec3

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {x : G}

theorem mem_centerIn_A₁ (hS : Sec3Pre G A A₁ R x) : x ∈ centerIn A₁ := by
  rw [hS.center_A₁]
  exact mem_zpowers x

theorem A₁_le_centralizer (hS : Sec3Pre G A A₁ R x) :
    A₁ ≤ centralizer ({x} : Set G) := fun a ha =>
  mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (mem_centerIn_A₁ hS).2 a ha)

theorem R_le_centralizer_A₁ (hS : Sec3Pre G A A₁ R x) :
    R ≤ centralizer (A₁ : Set G) :=
  hS.sylowR.le.trans (centralizer_le hS.le)

theorem R_le_centralizer (hS : Sec3Pre G A A₁ R x) :
    R ≤ centralizer ({x} : Set G) := fun _ hr =>
  mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp (R_le_centralizer_A₁ hS hr) x (mem_centerIn_A₁ hS).1).symm

theorem sec3K_le_centralizer (hS : Sec3Pre G A A₁ R x) :
    sec3K A₁ R x ≤ centralizer ({x} : Set G) :=
  sup_le (sec3B_le_centralizer A₁ x) (R_le_centralizer hS)

theorem sec3K_le_normalizer (hS : Sec3Pre G A A₁ R x) :
    sec3K A₁ R x ≤ normalizer (sec3B A₁ x : Set G) :=
  (sec3K_le_centralizer hS).trans (centralizer_le_normalizer_sec3B A₁ x)

theorem A₁_le_sec3K (hS : Sec3Pre G A A₁ R x) : A₁ ≤ sec3K A₁ R x :=
  (le_sec3B (A₁_le_centralizer hS)).trans le_sup_left

omit [Finite G] in
theorem sec3B_le_sec3K : sec3B A₁ x ≤ sec3K A₁ R x := le_sup_left

omit [Finite G] in
theorem R_le_sec3K : R ≤ sec3K A₁ R x := le_sup_right

theorem isPGroup_R (hS : Sec3Pre G A A₁ R x) : IsPGroup 2 R :=
  hS.sylowR.isPGroup

theorem two_dvd_card_R (hS : Sec3Pre G A A₁ R x) : 2 ∣ Nat.card R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (isPGroup_R hS).exists_card_eq
  have h4 := hS.four_le
  rw [hn] at h4 ⊢
  rcases n with _ | n
  · norm_num at h4
  · exact dvd_pow_self 2 (Nat.succ_ne_zero n)

omit [Finite G] in
theorem isQuasisimple_sec3B
    (hBp : commutator ↥(sec3B A₁ x) = ⊤)
    (hBs : NativeSporadic.IsSporadic (↥(sec3B A₁ x) ⧸ center ↥(sec3B A₁ x)) .Suz) :
    CFSG.Open.IsQuasisimple ↥(sec3B A₁ x) := by
  obtain ⟨e⟩ := hBs
  have : IsSimpleGroup (NativeSporadic.Carrier .Suz) := CFSG.Sporadic.Suz.isSimpleGroup_Suz
  exact ⟨hBp, e.isSimpleGroup⟩

theorem le_center_or_eq_top_of_perfect {H : Type*} [Group H] (hp : commutator H = ⊤)
    (hs : IsSimpleGroup (H ⧸ center H)) (N : Subgroup H) [N.Normal] :
    N ≤ center H ∨ N = ⊤ := by
  have hπ : Function.Surjective (QuotientGroup.mk' (center H)) := QuotientGroup.mk'_surjective _
  have hNorm : (N.map (QuotientGroup.mk' (center H))).Normal :=
    Subgroup.Normal.map inferInstance _ hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (center H))) with
    h | h
  · left
    rw [← QuotientGroup.ker_mk' (center H)]
    exact (Subgroup.map_eq_bot_iff _).mp h
  · right
    have hsup : N ⊔ center H = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : QuotientGroup.mk' (center H) y ∈ N.map (QuotientGroup.mk' (center H)) := by
        rw [h]
        exact mem_top _
      obtain ⟨n, hn, hny⟩ := hy
      have : n⁻¹ * y ∈ center H := by
        rw [← QuotientGroup.eq]
        exact hny
      have e : y = n * (n⁻¹ * y) := by group
      rw [e]
      exact mul_mem (mem_sup_left hn) (mem_sup_right this)
    have hle := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup
      (inferInstance : IsMulCommutative (center H))
    rw [hp] at hle
    exact eq_top_iff.mpr hle

theorem standard_sec3K (hS : Sec3Pre G A A₁ R x) (hstd : Step31Std) :
    standardComponentIsStandard (A₁.subgroupOf (sec3K A₁ R x)) := by
  obtain ⟨hst, -⟩ := hstd G A A₁ R x hS
  have hKC := sec3K_le_centralizer hS
  have hA₁K := A₁_le_sec3K hS
  have hLH : A₁.subgroupOf (centralizer ({x} : Set G)) ≤
      (sec3K A₁ R x).subgroupOf (centralizer ({x} : Set G)) := fun c hc =>
    mem_subgroupOf.mpr (hA₁K (mem_subgroupOf.mp hc))
  have hRle : R.subgroupOf (centralizer ({x} : Set G)) ≤
      centralizer (((A₁.subgroupOf (centralizer ({x} : Set G))) :
        Subgroup ↥(centralizer ({x} : Set G))) : Set ↥(centralizer ({x} : Set G))) ⊓
      (sec3K A₁ R x).subgroupOf (centralizer ({x} : Set G)) := by
    intro c hc
    refine ⟨mem_centralizer_iff.mpr fun a ha => Subtype.ext ?_, mem_subgroupOf.mpr
      (R_le_sec3K (mem_subgroupOf.mp hc))⟩
    exact (mem_centralizer_iff.mp (R_le_centralizer_A₁ hS (mem_subgroupOf.mp hc)) a
      (mem_subgroupOf.mp ha))
  have heven : Even (Nat.card ↥(centralizer (((A₁.subgroupOf (centralizer ({x} : Set G))) :
        Subgroup ↥(centralizer ({x} : Set G))) : Set ↥(centralizer ({x} : Set G))) ⊓
      (sec3K A₁ R x).subgroupOf (centralizer ({x} : Set G)))) := by
    have h2 : 2 ∣ Nat.card ↥(R.subgroupOf (centralizer ({x} : Set G))) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe (R_le_centralizer hS)).toEquiv]
      exact two_dvd_card_R hS
    exact even_iff_two_dvd.mpr (h2.trans (Subgroup.card_dvd_of_le hRle))
  have h1 := GMS78.standard_subgroupOf hst hLH heven
  let e : ↥((sec3K A₁ R x).subgroupOf (centralizer ({x} : Set G))) ≃* ↥(sec3K A₁ R x) :=
    subgroupOfEquivOfLe hKC
  have h2 := RankTwoClassical.standardComponentIsStandard_map_equiv e h1
  convert h2 using 1
  ext k
  constructor
  · intro hk
    refine ⟨⟨⟨k, hKC k.2⟩, k.2⟩, ?_, rfl⟩
    exact mem_subgroupOf.mpr (mem_subgroupOf.mpr (mem_subgroupOf.mp hk))
  · rintro ⟨y, hy, rfl⟩
    exact mem_subgroupOf.mpr (mem_subgroupOf.mp (mem_subgroupOf.mp hy))

theorem oddCore_sec3K_le_zpowers
    (hS : Sec3Pre G A A₁ R x) (hBc : centerIn (sec3B A₁ x) = zpowers x)
    (hBp : commutator ↥(sec3B A₁ x) = ⊤)
    (hBs : NativeSporadic.IsSporadic (↥(sec3B A₁ x) ⧸ center ↥(sec3B A₁ x)) .Suz) :
    (standardComponentOddCore ↥(sec3K A₁ R x)).map (sec3K A₁ R x).subtype ≤ zpowers x := by
  set K := sec3K A₁ R x with hK
  set B := sec3B A₁ x with hB
  set N := standardComponentOddCore ↥K with hN
  have hNodd : Odd (Nat.card N) := RankTwoSporadic.odd_card_standardComponentOddCore
  set NG := N.map K.subtype with hNG
  have hNGB : NG ≤ B := by
    rintro _ ⟨k, hk, rfl⟩
    refine mem_of_odd_of_mem_sup (isPGroup_R hS)
      ((le_sup_right : R ≤ sec3K A₁ R x).trans (sec3K_le_normalizer hS)) k.2 ?_
    show Odd (orderOf (k : G))
    rw [Subgroup.orderOf_coe]
    have hd : orderOf (⟨k, hk⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hd
    exact hNodd.of_dvd_nat hd
  have hnorm : (NG.subgroupOf B).Normal := by
    refine ⟨fun n hn b => ?_⟩
    obtain ⟨k, hk, hkn⟩ := mem_subgroupOf.mp hn
    have hbK : (b : G) ∈ K := sec3B_le_sec3K b.2
    have h1 := (inferInstance : N.Normal).conj_mem k hk ⟨b, hbK⟩
    refine mem_subgroupOf.mpr ⟨_, h1, ?_⟩
    simp only [coe_mul, coe_inv, map_mul, map_inv, subtype_apply]
    rw [show ((k : G)) = (n : G) from hkn]
  have hodd : Odd (Nat.card (NG.subgroupOf B)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hNGB).toEquiv, hNG,
      card_map_of_injective K.subtype_injective]
    exact hNodd
  have hq := isQuasisimple_sec3B hBp hBs
  have hle := (RankTwoSporadic.le_standardComponentOddCore hnorm hodd).trans
    (AS81.oddCore_le_center hq.1 hq.2)
  rw [← hBc]
  intro n hn
  have hnB : (⟨n, hNGB hn⟩ : ↥B) ∈ center ↥B := hle (mem_subgroupOf.mpr hn)
  exact ⟨hNGB hn, mem_centralizer_iff.mpr fun b hb =>
    congrArg Subtype.val (mem_center_iff.mp hnB ⟨b, hb⟩)⟩

theorem oddCore_sec3K_le_center
    (hS : Sec3Pre G A A₁ R x) (hBc : centerIn (sec3B A₁ x) = zpowers x)
    (hBp : commutator ↥(sec3B A₁ x) = ⊤)
    (hBs : NativeSporadic.IsSporadic (↥(sec3B A₁ x) ⧸ center ↥(sec3B A₁ x)) .Suz) :
    standardComponentOddCore ↥(sec3K A₁ R x) ≤ center ↥(sec3K A₁ R x) := by
  intro k hk
  have hkx : (k : G) ∈ zpowers x := oddCore_sec3K_le_zpowers hS hBc hBp hBs ⟨k, hk, rfl⟩
  rw [mem_center_iff]
  intro h
  apply Subtype.ext
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hkx
  have hhx := mem_centralizer_singleton_iff.mp (sec3K_le_centralizer hS h.2)
  simp only [coe_mul, ← hj]
  exact (Commute.zpow_right hhx j).eq

theorem rankTwoHyp_sec3K
    (hS : Sec3Pre G A A₁ R x) (hstd : Step31Std)
    (hBp : commutator ↥(sec3B A₁ x) = ⊤)
    (hBs : NativeSporadic.IsSporadic (↥(sec3B A₁ x) ⧸ center ↥(sec3B A₁ x)) .Suz) :
    RankTwoHypNF ↥(sec3K A₁ R x) (A₁.subgroupOf (sec3K A₁ R x)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨standard_sec3K hS hstd, ?_, ?_⟩
  · intro hn
    obtain ⟨-, hnn⟩ := hstd G A A₁ R x hS
    have hq := isQuasisimple_sec3B hBp hBs
    have hA₁B := le_sec3B (A₁_le_centralizer hS)
    have hnB : (A₁.subgroupOf (sec3B A₁ x)).Normal := ⟨fun a ha b => by
      have h1 := hn.conj_mem ⟨a, sec3B_le_sec3K a.2⟩ (mem_subgroupOf.mpr (mem_subgroupOf.mp ha))
        ⟨b, sec3B_le_sec3K b.2⟩
      exact mem_subgroupOf.mpr (mem_subgroupOf.mp h1)⟩
    rcases le_center_or_eq_top_of_perfect hq.1 hq.2 (A₁.subgroupOf (sec3B A₁ x)) with hc | ht
    ·
      have hcomm : ∀ a b : ↥A₁, a * b = b * a := fun a b => by
        have ha : (⟨a, hA₁B a.2⟩ : ↥(sec3B A₁ x)) ∈ center ↥(sec3B A₁ x) :=
          hc (mem_subgroupOf.mpr a.2)
        have h := congrArg (fun t : ↥(sec3B A₁ x) => (t : G))
          (mem_center_iff.mp ha ⟨b, hA₁B b.2⟩)
        exact Subtype.ext (by simpa using h.symm)
      have : IsMulCommutative ↥A₁ := ⟨⟨hcomm⟩⟩
      have hperf : Group.IsPerfect ↥A₁ := (Group.isPerfect_def).2 hS.quasisimple.1
      have hsub : Subsingleton ↥A₁ := Group.IsPerfect.subsingleton_of_isMulCommutative
      have hx1 : (⟨x, (mem_centerIn_A₁ hS).1⟩ : ↥A₁) = 1 := Subsingleton.elim _ _
      have h3 := hS.order_x
      rw [show x = 1 from congrArg Subtype.val hx1, orderOf_one] at h3
      omega
    ·
      apply hnn
      have hBA : sec3B A₁ x ≤ A₁ := fun b hb => by
        have : (⟨b, hb⟩ : ↥(sec3B A₁ x)) ∈ A₁.subgroupOf (sec3B A₁ x) := ht ▸ mem_top _
        exact mem_subgroupOf.mp this
      have heq : normalClosure ((A₁.subgroupOf (centralizer ({x} : Set G)) :
          Subgroup ↥(centralizer ({x} : Set G))) : Set ↥(centralizer ({x} : Set G))) =
          A₁.subgroupOf (centralizer ({x} : Set G)) := by
        refine le_antisymm (fun c hc => mem_subgroupOf.mpr (hBA ⟨c, hc, rfl⟩))
          subset_normalClosure
      rw [← heq]
      exact normalClosure_normal
  · refine Sec3.two_le_pRank_of_four_le (R := R.subgroupOf (sec3K A₁ R x)) ?_ ?_ ?_
    · intro r hr
      rw [mem_centralizer_iff]
      intro a ha
      exact Subtype.ext (mem_centralizer_iff.mp (R_le_centralizer_A₁ hS (mem_subgroupOf.mp hr))
        a (mem_subgroupOf.mp ha))
    · obtain ⟨⟨hc⟩, h2⟩ := hS.elemR
      refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun r hr => Subtype.ext ?_⟩
      · have := congrArg Subtype.val (hc.comm ⟨a, mem_subgroupOf.mp a.2⟩ ⟨b, mem_subgroupOf.mp b.2⟩)
        simpa using this
      · simpa using h2 _ (mem_subgroupOf.mp hr)
    · rw [Nat.card_congr (subgroupOfEquivOfLe R_le_sec3K).toEquiv]
      exact hS.four_le

theorem isSylowOf_sec3K (hS : Sec3Pre G A A₁ R x) :
    IsSylowOf 2 (R.subgroupOf (sec3K A₁ R x))
      (centralizer ((A₁.subgroupOf (sec3K A₁ R x) : Subgroup ↥(sec3K A₁ R x)) :
        Set ↥(sec3K A₁ R x))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, g₀, T₀, hc⟩ := hS.config
  have h1 := hc.sylow_inf
  rw [hS.layer] at h1
  have hRle : R ≤ centralizer ((zpowers x : Subgroup G) : Set G) ⊓ centralizer (A₁ : Set G) :=
    le_inf (by rw [centralizer_zpowers]; exact R_le_centralizer hS) (R_le_centralizer_A₁ hS)
  have h2 := isSylowOf_of_isSylowOf_inf_normalizer' hRle h1
  have h3 : IsSylowOf 2 R (centralizer (A₁ : Set G) ⊓ sec3K A₁ R x) :=
    h2.of_le (le_inf (R_le_centralizer_A₁ hS) R_le_sec3K) (le_inf (by
      rw [centralizer_zpowers]
      exact inf_le_right.trans (sec3K_le_centralizer hS)) inf_le_left)
  rw [GMS78.centralizer_subgroupOf_eq (A₁_le_sec3K hS),
    ← isSylowOf_map_subtype_iff (sec3K A₁ R x), subgroupOf_map_subtype,
    subgroupOf_map_subtype, inf_eq_left.mpr R_le_sec3K, inf_assoc, inf_idem]
  exact h3

end Sec3

end CFSG.ComponentClassification.AS81
