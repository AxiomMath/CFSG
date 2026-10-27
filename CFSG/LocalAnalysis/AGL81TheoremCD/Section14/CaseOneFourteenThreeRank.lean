module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenThreeTools
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34SylowStructure
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneSetup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoSetup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CoreTwoSL34
import CFSG.GroupTheory.Commutator.JoinNormalizer
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter
import CFSG.RankThree.PartTwo.Sec4.T444.L34Shape
import CFSG.Quasithin.Vol2.Ch6Sec1Lem5R2Case1
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZKFactsL34
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.Literature.GL52Group
import CFSG.Quasithin.Background.S1549CA0
import CFSG.Models.PGLOrders
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {M H N E Q J : Subgroup G}

private theorem card_oTwoZStar (J : Subgroup G) :
    Nat.card (oTwoZStar J) =
      Nat.card (Subgroup.center (threeStar J)) * Nat.card (CFSG.pPrimeCore 3 ↥J) := by
  classical
  haveI : (CFSG.pPrimeCore 3 ↥J).Normal := CFSG.pPrimeCore_normal
  let q : ↥J →* threeStar J := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)
  let H : Subgroup G := oTwoZStar J
  let D : Subgroup G := (CFSG.pPrimeCore 3 ↥J).map J.subtype
  have hHJ : H ≤ J := Subgroup.map_subtype_le _
  have hDH : D ≤ H := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
    have hq1 : q y = 1 := (QuotientGroup.eq_one_iff _).mpr hy
    rw [Subgroup.mem_comap, hq1]
    exact Subgroup.one_mem _
  let φ : ↥H →* threeStar J := q.comp (Subgroup.inclusion hHJ)
  have hrange : φ.range = Subgroup.center (threeStar J) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
      have hxy : Subgroup.inclusion hHJ x = y := Subtype.ext (by simpa using hyx.symm)
      change q (Subgroup.inclusion hHJ x) ∈ Subgroup.center (threeStar J)
      rw [hxy]
      exact hy
    · intro hy
      obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) y
      have hjH : (j : G) ∈ H :=
        Subgroup.mem_map.mpr
          ⟨j, Subgroup.mem_comap.mpr hy, rfl⟩
      refine ⟨⟨(j : G), hjH⟩, ?_⟩
      change q (Subgroup.inclusion hHJ ⟨(j : G), hjH⟩) = q j
      rfl
  have hker : φ.ker = D.subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : ((Subgroup.inclusion hHJ x : ↥J) : G) ∈ D :=
        Subgroup.mem_map.mpr ⟨Subgroup.inclusion hHJ x,
          (QuotientGroup.eq_one_iff _).mp hx, rfl⟩
      simpa using hx'
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hyx' : (y : G) = (x : G) := hyx
      have hxy : Subgroup.inclusion hHJ x = y := Subtype.ext (by simpa using hyx'.symm)
      change q (Subgroup.inclusion hHJ x) = 1
      rw [hxy]
      exact (QuotientGroup.eq_one_iff _).mpr hy
  have hker_card : Nat.card ↥φ.ker = Nat.card (CFSG.pPrimeCore 3 ↥J) := by
    rw [hker]
    calc Nat.card ↥(D.subgroupOf H)
        = Nat.card ↥D := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv
      _ = Nat.card (CFSG.pPrimeCore 3 ↥J) :=
          Subgroup.card_map_of_injective J.subtype_injective
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hrange, hker_card] at hcard
  change Nat.card ↥H = Nat.card (Subgroup.center (threeStar J)) *
    Nat.card (CFSG.pPrimeCore 3 ↥J)
  rw [← hcard]
  ring

theorem relIndex_oTwoZStar (J : Subgroup G) :
    (oTwoZStar J).relIndex J = (Subgroup.center (threeStar J)).index := by
  classical
  let q : ↥J →* threeStar J := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)
  have hsub : (oTwoZStar J).subgroupOf J =
      (Subgroup.center (threeStar J)).comap q := by
    ext x
    rw [Subgroup.mem_subgroupOf, oTwoZStar, Subgroup.mem_map, Subgroup.mem_comap]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hxy : x = y := Subtype.ext (by simpa using hyx.symm)
      rw [hxy]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  calc (oTwoZStar J).relIndex J
      = ((oTwoZStar J).subgroupOf J).relIndex (J.subgroupOf J) :=
          (Subgroup.relIndex_subgroupOf (H := oTwoZStar J) (K := J) (L := J) le_rfl).symm
    _ = ((oTwoZStar J).subgroupOf J).index := by
          rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right]
    _ = ((Subgroup.center (threeStar J)).comap q).index := by rw [hsub]
    _ = (Subgroup.center (threeStar J)).index :=
        Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)

private theorem center_index_of_isL34Type {A : Subgroup G} (h : IsL34Type (threeStar A)) :
    (Subgroup.center (threeStar A)).index = 20160 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_projSL_quotient_center_of_isL34Type h
  rw [Subgroup.index_eq_card]
  calc Nat.card (threeStar A ⧸ Subgroup.center (threeStar A))
      = Nat.card (CFSG.PGLModel.projSL 3 (GaloisField 2 2)) := Nat.card_congr e.toEquiv
    _ = 20160 := CFSG.PGLModel.card_projSL_three_four

private theorem center_index_of_is3A6Star {A : Subgroup G} (h : Is3A6Star A) :
    (Subgroup.center (threeStar A)).index = 360 := by
  have hmul := Subgroup.card_mul_index (Subgroup.center (threeStar A))
  rw [h.2, Is3A6Star.card_threeStar h] at hmul
  omega

private theorem not_nine_dvd_card_oTwoZStar_of_l34 {A : Subgroup G}
    (htype : IsSL34Star A ∨ IsL34Star A) : ¬ 9 ∣ Nat.card (oTwoZStar A) := by
  rw [card_oTwoZStar]
  have hD : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 ↥A)) :=
    CFSG.pPrimeCore_coprime_card
  have hcenter_le3 : Nat.card (Subgroup.center (threeStar A)) ≤ 3 := by
    rcases htype with h | h
    · exact h.2.le
    · exact h.2.le.trans (by norm_num)
  intro h9
  have hcop : Nat.Coprime 9 (Nat.card (CFSG.pPrimeCore 3 ↥A)) := by
    simpa using hD.pow_left 2
  rw [Nat.mul_comm] at h9
  have h9center : 9 ∣ Nat.card (Subgroup.center (threeStar A)) :=
    hcop.dvd_of_dvd_mul_left h9
  have hle := Nat.le_of_dvd Nat.card_pos h9center
  omega

private theorem le_sup_and_inf_le_of_not_le {N₁ A : Subgroup G}
    (hJ : IsKComp M H J) (hA' : IsKComp M N A)
    (htype : IsSL34Star A ∨ IsL34Star A ∨ IsA11Star A ∨ Is3A6Star A)
    (hAN : A ≤ N₁) (hNA : N₁ ≤ Subgroup.normalizer (A : Set G))
    (hJN : J ≤ N₁) (hJX : ¬ J ≤ Xhat N₁ A hAN hNA) :
    J ≤ A ⊔ Xhat N₁ A hAN hNA ∧
      J ⊓ Xhat N₁ A hAN hNA ≤ oTwoZStar J := by
  let X : Subgroup G := Xhat N₁ A hAN hNA
  have hXn : N₁ ≤ Subgroup.normalizer (X : Set G) := by
    simpa [X] using le_normalizer_quotientCentralizer (N := N₁) (L := A)
      (CFSG.pPrimeCore 3 ↥A) hAN hNA
  have hJXn : J ≤ Subgroup.normalizer (X : Set G) := hJN.trans hXn
  have hsup : J ≤ A ⊔ X := by
    simpa [X] using le_sup_quotientCentralizer_of_star hA' htype hAN hNA hJN hJ.isPerfect
  have hnormal : ((J ⊓ X).subgroupOf J).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨J.mul_mem (J.mul_mem g.2 hn.1) (J.inv_mem g.2),
      (Subgroup.mem_normalizer_iff.mp (hJXn g.2) (n : G)).mp hn.2⟩
  have hne : J ⊓ X ≠ J := by
    intro hEq
    apply hJX
    rw [← hEq]
    exact inf_le_right
  exact ⟨hsup, IsKComp.le_oTwoZStar_of_normal hJ inf_le_left hnormal hne⟩

private theorem false_of_is3A6Star {N₁ A : Subgroup G}
    (hJ : IsKComp M H J) (hJSL : IsSL34Star J) (hA' : IsKComp M N A)
    (htype : IsSL34Star A ∨ IsL34Star A ∨ IsA11Star A ∨ Is3A6Star A)
    (h6 : Is3A6Star A) (hAN : A ≤ N₁) (hNA : N₁ ≤ Subgroup.normalizer (A : Set G))
    (hJN : J ≤ N₁) (hJX : ¬ J ≤ Xhat N₁ A hAN hNA) : False := by
  let X : Subgroup G := Xhat N₁ A hAN hNA
  obtain ⟨hJsup, hJinf_le⟩ :=
    le_sup_and_inf_le_of_not_le hJ hA' htype hAN hNA hJN hJX
  have hXn : N₁ ≤ Subgroup.normalizer (X : Set G) := by
    simpa [X] using le_normalizer_quotientCentralizer (N := N₁) (L := A)
      (CFSG.pPrimeCore 3 ↥A) hAN hNA
  have hAXn : A ≤ Subgroup.normalizer (X : Set G) := hAN.trans hXn
  have hJXn : J ≤ Subgroup.normalizer (X : Set G) := hJN.trans hXn
  have hJXleAX : J ⊔ X ≤ A ⊔ X := sup_le hJsup le_sup_right
  haveI : X.IsFiniteRelIndex (A ⊔ X) := Subgroup.isFiniteRelIndex_of_finiteIndex
  haveI : (J ⊓ X).IsFiniteRelIndex J := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hrelJ : X.relIndex (J ⊔ X) = (J ⊓ X).relIndex J :=
    (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hJXn).2
  have hrelA : X.relIndex (A ⊔ X) = (A ⊓ X).relIndex A :=
    (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hAXn).2
  have hmono : X.relIndex (J ⊔ X) ≤ X.relIndex (A ⊔ X) :=
    Subgroup.relIndex_le_of_le_right hJXleAX (Subgroup.relIndex_ne_zero)
  have hAidx : (A ⊓ X).relIndex A = 360 := by
    rw [inf_comm, quotientCentralizer_inf_eq_oTwoZStar hAN hNA, relIndex_oTwoZStar,
      center_index_of_is3A6Star h6]
  have hupper : (J ⊓ X).relIndex J ≤ 360 := by
    rw [hrelJ, hrelA, hAidx] at hmono
    exact hmono
  have hlower : 20160 ≤ (J ⊓ X).relIndex J := by
    have hle := Subgroup.relIndex_le_of_le_left (H := J ⊓ X) (K := oTwoZStar J)
      (L := J) hJinf_le (Subgroup.relIndex_ne_zero)
    rwa [relIndex_oTwoZStar, center_index_of_isL34Type hJSL.1] at hle
  omega

private theorem oTwoZStar_eq_map_pPrimeCore_of_center_eq_bot {J : Subgroup G}
    (h : Subgroup.center (threeStar J) = ⊥) :
    oTwoZStar J = (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
  rw [oTwoZStar, h]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ CFSG.pPrimeCore 3 ↥J := by
      exact (QuotientGroup.eq_one_iff _).mp (by simpa using hy)
    exact Subgroup.mem_map.mpr ⟨y, hy', rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, by simpa [QuotientGroup.eq_one_iff] using hy, rfl⟩

private theorem exists_three_mem_quotientCentralizer_not_mem
    {N₁ A : Subgroup G}
    (hJ : IsKComp M H J) (hJSL : IsSL34Star J) (hA11 : IsA11Star A)
    (hAN : A ≤ N₁) (hNA : N₁ ≤ Subgroup.normalizer (A : Set G))
    (hJN : J ≤ N₁) (hJsup : J ≤ A ⊔ Xhat N₁ A hAN hNA)
    (hJA : ¬ J ≤ A) (hSJ : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ J) J) :
    ∃ f : G, f ∈ Xhat N₁ A hAN hNA ∧ f ^ 3 = 1 ∧ f ∉ A := by
  classical
  let X : Subgroup G := Xhat N₁ A hAN hNA
  let S : Subgroup G := Q ⊓ J
  let D : Subgroup G := (CFSG.pPrimeCore 3 ↥A).map A.subtype
  have hSdata := IsKComp.sylow_three_structure hJ (Or.inl hJSL) hSJ
  obtain ⟨hScard, hSexp, hScenter, hScenterCard⟩ := hSdata
  have hJAnormal : ((J ⊓ A).subgroupOf J).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨J.mul_mem (J.mul_mem g.2 hn.1) (J.inv_mem g.2),
      (Subgroup.mem_normalizer_iff.mp ((hJN.trans hNA) g.2) (n : G)).mp hn.2⟩
  have hJAne : J ⊓ A ≠ J := by
    intro hEq
    apply hJA
    rw [← hEq]
    exact inf_le_right
  have hJA_le : J ⊓ A ≤ oTwoZStar J :=
    IsKComp.le_oTwoZStar_of_normal hJ inf_le_left hJAnormal hJAne
  have hSnotA : ¬ S ≤ A := by
    intro hSA
    have hSleO : S ≤ oTwoZStar J := by
      intro x hxS
      exact hJA_le ⟨(Subgroup.mem_inf.mp hxS).2, hSA hxS⟩
    have hSeq : S = S ⊓ oTwoZStar J := (inf_eq_left.mpr hSleO).symm
    have hcardS3 : Nat.card ↥S = 3 := by
      rw [hSeq, hScenter]
      exact hScenterCard
    rw [hScard] at hcardS3
    norm_num at hcardS3
  obtain ⟨s, hsS, hsA⟩ := Set.not_subset.mp hSnotA
  have hsJ : s ∈ J := (Subgroup.mem_inf.mp hsS).2
  have hs3 : s ^ 3 = 1 := hSexp s hsS
  have hXleN₁ : X ≤ N₁ := quotientCentralizer_le N₁ A _ hAN hNA
  have hAXleN₁ : A ⊔ X ≤ N₁ := sup_le hAN hXleN₁
  have hAXn : A ≤ Subgroup.normalizer (X : Set G) :=
    hAN.trans (by
      simpa [X] using le_normalizer_quotientCentralizer (N := N₁) (L := A)
        (CFSG.pPrimeCore 3 ↥A) hAN hNA)
  haveI : (A.subgroupOf (A ⊔ X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (hAXleN₁.trans hNA)
  have hsAX : s ∈ A ⊔ X := hJsup hsJ
  have hcoe : ((A ⊔ X : Subgroup G) : Set G) = (A : Set G) * (X : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A X hAXn
  have hsmem : s ∈ (A : Set G) * (X : Set G) := by
    rw [← hcoe]
    exact hsAX
  obtain ⟨a, ha, w, hw, haw⟩ := hsmem
  have hwA : w ∉ A := by
    intro hwA
    exact hsA (by rw [← haw]; exact A.mul_mem ha hwA)
  have hXleAX : X ≤ A ⊔ X := le_sup_right
  have hwAX : w ∈ A ⊔ X := hXleAX hw
  let π : ↥(A ⊔ X) →* (↥(A ⊔ X) ⧸ A.subgroupOf (A ⊔ X)) :=
    QuotientGroup.mk' (A.subgroupOf (A ⊔ X))
  have hsAX' : s ∈ A ⊔ X := hsAX
  have haAX : a ∈ A ⊔ X := Subgroup.mem_sup_left ha
  have hπa : π ⟨a, haAX⟩ = 1 := by
    simpa [π] using (QuotientGroup.eq_one_iff (N := A.subgroupOf (A ⊔ X))
      (x := ⟨a, haAX⟩)).mpr (Subgroup.mem_subgroupOf.mpr ha)
  have hπeq : π ⟨w, hwAX⟩ = π ⟨s, hsAX'⟩ := by
    have hs_eq : (⟨s, hsAX'⟩ : ↥(A ⊔ X)) =
        ⟨a, haAX⟩ * ⟨w, hwAX⟩ := Subtype.ext haw.symm
    rw [hs_eq, map_mul, hπa, one_mul]
  have hπs3 : (π ⟨s, hsAX'⟩) ^ 3 = 1 := by
    have h3 : (⟨s, hsAX'⟩ : ↥(A ⊔ X)) ^ 3 = 1 := Subtype.ext hs3
    have h4 := congrArg π h3
    simpa only [map_pow, map_one] using h4
  have hπs1 : π ⟨s, hsAX'⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨s, hsAX'⟩ : ↥(A ⊔ X)) ∈ A.subgroupOf (A ⊔ X) :=
      (QuotientGroup.eq_one_iff (N := A.subgroupOf (A ⊔ X))
        (x := ⟨s, hsAX'⟩)).mp (by simpa [π] using h1)
    exact hsA (Subgroup.mem_subgroupOf.mp hmem)
  have hπord : orderOf (π ⟨s, hsAX'⟩) = 3 :=
    orderOf_eq_prime hπs3 hπs1
  have hw3AX : w ^ 3 ∈ A ⊔ X := hXleAX (X.pow_mem hw 3)
  have hw3A : w ^ 3 ∈ A := by
    have h1 : π ⟨w ^ 3, hw3AX⟩ = 1 := by
      have hpow : (⟨w ^ 3, hw3AX⟩ : ↥(A ⊔ X)) = ⟨w, hwAX⟩ ^ 3 := Subtype.ext rfl
      rw [hpow, map_pow, hπeq, hπs3]
    have hmem : (⟨w ^ 3, hw3AX⟩ : ↥(A ⊔ X)) ∈ A.subgroupOf (A ⊔ X) :=
      (QuotientGroup.eq_one_iff (N := A.subgroupOf (A ⊔ X))
        (x := ⟨w ^ 3, hw3AX⟩)).mp (by simpa [π] using h1)
    exact Subgroup.mem_subgroupOf.mp hmem
  have hD3 : ¬ 3 ∣ Nat.card D := by
    rw [show Nat.card D = Nat.card (CFSG.pPrimeCore 3 ↥A) from
      Subgroup.card_map_of_injective A.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hw3D : w ^ 3 ∈ D := by
    have hXinfA : X ⊓ A = oTwoZStar A := by
      simpa [X, inf_comm] using (quotientCentralizer_inf_eq_oTwoZStar hAN hNA)
    have hO : oTwoZStar A = D :=
      oTwoZStar_eq_map_pPrimeCore_of_center_eq_bot hA11.center_eq_bot
    rw [← hO, ← hXinfA]
    exact Subgroup.mem_inf.mpr ⟨X.pow_mem hw 3, hw3A⟩
  have hw3pow : (w ^ 3) ^ Nat.card D = 1 := by
    have := pow_card_eq_one' (G := ↥D) (x := ⟨w ^ 3, hw3D⟩)
    exact congrArg Subtype.val this
  have hpowD : w ^ (3 * Nat.card D) = 1 := by
    rw [pow_mul]
    exact hw3pow
  refine ⟨w ^ Nat.card D, ?_, ?_, ?_⟩
  · exact X.pow_mem hw _
  · rw [← pow_mul, Nat.mul_comm, hpowD]
  · intro hfA
    have hfAX : w ^ Nat.card D ∈ A ⊔ X := Subgroup.mem_sup_left hfA
    have h1 : π ⟨w ^ Nat.card D, hfAX⟩ = 1 := by
      simpa [π] using (QuotientGroup.eq_one_iff (N := A.subgroupOf (A ⊔ X))
        (x := ⟨w ^ Nat.card D, hfAX⟩)).mpr (Subgroup.mem_subgroupOf.mpr hfA)
    have h2 : (π ⟨w, hwAX⟩) ^ Nat.card D = 1 := by
      have hpow : (⟨w ^ Nat.card D, hfAX⟩ : ↥(A ⊔ X)) =
          ⟨w, hwAX⟩ ^ Nat.card D := Subtype.ext rfl
      rw [hpow, map_pow] at h1
      exact h1
    rw [hπeq, ← orderOf_dvd_iff_pow_eq_one, hπord] at h2
    exact hD3 h2

private theorem false_of_isA11Star
    {N₁ A : Subgroup G}
    (h : S14Choice G M H E Q J) (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    (hJ : IsKComp M H J) (hJSL : IsSL34Star J) (hA' : IsKComp M N A)
    (hA11 : IsA11Star A)
    (htype : IsSL34Star A ∨ IsL34Star A ∨ IsA11Star A ∨ Is3A6Star A)
    (hAN : A ≤ N₁) (hNA : N₁ ≤ Subgroup.normalizer (A : Set G))
    (hJN : J ≤ N₁) (hJX : ¬ J ≤ Xhat N₁ A hAN hNA) (hJA : ¬ J ≤ A)
    (hrank : CFSG.Open.pRank 3 N₁ ≤ 3) : False := by
  let X : Subgroup G := Xhat N₁ A hAN hNA
  let D : Subgroup G := (CFSG.pPrimeCore 3 ↥A).map A.subtype
  have hSJ : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ J) J := h.isSylowOf_inf_J hpre hU
  obtain ⟨hJsup, -⟩ := le_sup_and_inf_le_of_not_le hJ hA' htype hAN hNA hJN hJX
  obtain ⟨f, hfX, hf3, hfA⟩ :=
    exists_three_mem_quotientCentralizer_not_mem hJ hJSL hA11 hAN hNA hJN hJsup hJA hSJ
  obtain ⟨E, hEA, hEelem, hEcard⟩ := hA11.exists_elemAbelian_le
  have hXleN₁ : X ≤ N₁ := quotientCentralizer_le N₁ A _ hAN hNA
  have hD3 : ¬ 3 ∣ Nat.card D := by
    rw [show Nat.card D = Nat.card (CFSG.pPrimeCore 3 ↥A) from
      Subgroup.card_map_of_injective A.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hDnorm : N₁ ≤ Subgroup.normalizer (D : Set G) :=
    hNA.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pPrimeCore 3 ↥A))
  have hcomm : ⁅E, Subgroup.zpowers f⁆ ≤ D := by
    refine CFSG.GroupTheory.commutator_zpowers_le_of_forall_mem
      (A := E) (N := D) (c := f) (hDnorm (hXleN₁ hfX)) ?_
    intro e he
    have hmem := commutator_mem_map_of_mem_quotientCentralizer
      (Q := CFSG.pPrimeCore 3 ↥A) hAN hNA hfX (hEA he)
    have hEq : ⁅e, f⁆ = (f * e * f⁻¹ * e⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hEq]
    exact D.inv_mem hmem
  have hfE : f ∉ E ⊔ D := by
    intro hf
    exact hfA (sup_le hEA (Subgroup.map_subtype_le _) hf)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrank4 : 4 ≤ CFSG.Open.pRank 3 N₁ := by
    have h := CFSG.Quasithin.succ_le_pRank_of_commute_mod (p := 3) (X := N₁)
      (Q := D) (E := E) (a := 3) (f := f) hD3
      ((hEA.trans hAN).trans hDnorm) (hDnorm (hXleN₁ hfX)) hEelem
      (by rw [hEcard]) hf3 hcomm hfE (hEA.trans hAN) (hXleN₁ hfX)
      (Subgroup.map_subtype_le _ |>.trans hAN)
    simpa using h
  omega

private theorem inf_eq_oTwoZStar_and_sup_eq_of_l34 {N₁ A : Subgroup G}
    (hJ : IsKComp M H J) (hJSL : IsSL34Star J) (hA' : IsKComp M N A)
    (htype : IsSL34Star A ∨ IsL34Star A ∨ IsA11Star A ∨ Is3A6Star A)
    (h34 : IsL34Type (threeStar A))
    (hAN : A ≤ N₁) (hNA : N₁ ≤ Subgroup.normalizer (A : Set G))
    (hJN : J ≤ N₁) (hJX : ¬ J ≤ Xhat N₁ A hAN hNA) :
    J ⊓ Xhat N₁ A hAN hNA = oTwoZStar J ∧
      J ⊔ Xhat N₁ A hAN hNA = A ⊔ Xhat N₁ A hAN hNA := by
  let X : Subgroup G := Xhat N₁ A hAN hNA
  obtain ⟨hJsup, hJinf_le⟩ :=
    le_sup_and_inf_le_of_not_le hJ hA' htype hAN hNA hJN hJX
  have hXn : N₁ ≤ Subgroup.normalizer (X : Set G) := by
    simpa [X] using le_normalizer_quotientCentralizer (N := N₁) (L := A)
      (CFSG.pPrimeCore 3 ↥A) hAN hNA
  have hAXn : A ≤ Subgroup.normalizer (X : Set G) := hAN.trans hXn
  have hJXn : J ≤ Subgroup.normalizer (X : Set G) := hJN.trans hXn
  have hJXleAX : J ⊔ X ≤ A ⊔ X := sup_le hJsup le_sup_right
  haveI : X.IsFiniteRelIndex (A ⊔ X) := Subgroup.isFiniteRelIndex_of_finiteIndex
  haveI : (J ⊓ X).IsFiniteRelIndex J := Subgroup.isFiniteRelIndex_of_finiteIndex
  haveI : (J ⊔ X).IsFiniteRelIndex (A ⊔ X) :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hrelJ : X.relIndex (J ⊔ X) = (J ⊓ X).relIndex J :=
    (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hJXn).2
  have hrelA : X.relIndex (A ⊔ X) = (A ⊓ X).relIndex A :=
    (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hAXn).2
  have hmono : X.relIndex (J ⊔ X) ≤ X.relIndex (A ⊔ X) :=
    Subgroup.relIndex_le_of_le_right hJXleAX (Subgroup.relIndex_ne_zero)
  have hAidx : (A ⊓ X).relIndex A = 20160 := by
    rw [inf_comm, quotientCentralizer_inf_eq_oTwoZStar hAN hNA, relIndex_oTwoZStar,
      center_index_of_isL34Type h34]
  have hupper : (J ⊓ X).relIndex J ≤ 20160 := by
    rw [hrelJ, hrelA, hAidx] at hmono
    exact hmono
  have hlower : 20160 ≤ (J ⊓ X).relIndex J := by
    have hle := Subgroup.relIndex_le_of_le_left (H := J ⊓ X) (K := oTwoZStar J)
      (L := J) hJinf_le (Subgroup.relIndex_ne_zero)
    rwa [relIndex_oTwoZStar, center_index_of_isL34Type hJSL.1] at hle
  have hidx : (J ⊓ X).relIndex J = (oTwoZStar J).relIndex J := by
    rw [relIndex_oTwoZStar, center_index_of_isL34Type hJSL.1]
    omega
  have hO_le_J : oTwoZStar J ≤ J := Subgroup.map_subtype_le _
  haveI : (oTwoZStar J).IsFiniteRelIndex J := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hinf : J ⊓ X = oTwoZStar J := by
    have hmul := Subgroup.relIndex_mul_relIndex (J ⊓ X) (oTwoZStar J) J
      hJinf_le hO_le_J
    rw [hidx] at hmul
    have h1 : (J ⊓ X).relIndex (oTwoZStar J) = 1 := by
      have hmul' : (J ⊓ X).relIndex (oTwoZStar J) * (oTwoZStar J).relIndex J =
          1 * (oTwoZStar J).relIndex J := by
        rw [one_mul]
        exact hmul
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero
        (Subgroup.relIndex_ne_zero (H := oTwoZStar J) (K := J))) hmul'
    exact le_antisymm hJinf_le (Subgroup.relIndex_eq_one.mp h1)
  have hrel_eq : X.relIndex (J ⊔ X) = X.relIndex (A ⊔ X) := by
    rw [hrelJ, hrelA, hAidx, hinf, relIndex_oTwoZStar,
      center_index_of_isL34Type hJSL.1]
  have hsup : J ⊔ X = A ⊔ X := by
    have hmul := Subgroup.relIndex_mul_relIndex X (J ⊔ X) (A ⊔ X) le_sup_right
      hJXleAX
    rw [hrel_eq] at hmul
    have h1 : (J ⊔ X).relIndex (A ⊔ X) = 1 := by
      have hmul' : (J ⊔ X).relIndex (A ⊔ X) * X.relIndex (A ⊔ X) =
          1 * X.relIndex (A ⊔ X) := by
        rw [one_mul, mul_comm]
        exact hmul
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero
        (Subgroup.relIndex_ne_zero (H := X) (K := A ⊔ X))) hmul'
    exact le_antisymm hJXleAX (Subgroup.relIndex_eq_one.mp h1)
  exact ⟨hinf, hsup⟩

private theorem q0_commutator_mem_X {N₁ A Q₀ X : Subgroup G}
    (hJsup : A ≤ J ⊔ X) (hJXn : J ≤ Subgroup.normalizer (X : Set G))
    (hQ0J : ⁅Q₀, J⁆ ≤ X) {p a : G} (hpQ0 : p ∈ Q₀) (hpN₁ : p ∈ N₁)
    (hXn : N₁ ≤ Subgroup.normalizer (X : Set G)) (ha : a ∈ A) :
    p * a * p⁻¹ * a⁻¹ ∈ X := by
  have hpaX : p * a * p⁻¹ * a⁻¹ ∈ X := by
    have haJX : a ∈ J ⊔ X := hJsup ha
    have hcoe : ((J ⊔ X : Subgroup G) : Set G) = (J : Set G) * (X : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right J X hJXn
    have haJX' : a ∈ (J : Set G) * (X : Set G) := by
      rwa [← hcoe]
    obtain ⟨j, hj, x, hx, hjx⟩ := haJX'
    have hcommPJ : ⁅p, j⁆ ∈ X := hQ0J (Subgroup.commutator_mem_commutator hpQ0 hj)
    have hcommPX : ⁅p, x⁆ ∈ X := by
      have hconj : p * x * p⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hXn hpN₁) x).mp hx
      exact X.mul_mem hconj (X.inv_mem (by
        simpa using hx))
    have hconjPX : j * ⁅p, x⁆ * j⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hJXn hj) _).mp hcommPX
    have hformula : ⁅p, a⁆ = ⁅p, j⁆ * (j * ⁅p, x⁆ * j⁻¹) := by
      rw [← hjx, commutatorElement_mul_right_eq_mul_conj]
      group
    change ⁅p, a⁆ ∈ X
    rw [hformula]
    exact X.mul_mem hcommPJ hconjPX
  simpa only [commutatorElement_def] using hpaX

private theorem q0_le_quotientCentralizer
    {N₁ A Q₀ : Subgroup G}
    (hqJ : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (hA' : IsKComp M N A)
    (hAN : A ≤ N₁) (hNA : N₁ ≤ Subgroup.normalizer (A : Set G))
    (hJ : IsKComp M H J) (hJSL : IsSL34Star J)
    (hQ0Q : Q₀ ≤ Q) (hQ0J : ⁅Q₀, J⁆ ≤ CFSG.Open.pCoreOf 2 J)
    (hQN : Q ≤ N₁) (hJN : J ≤ N₁)
    (hJsup : A ≤ J ⊔ Xhat N₁ A hAN hNA)
    (hJXeq : J ⊓ Xhat N₁ A hAN hNA = oTwoZStar J) :
    Q₀ ≤ Xhat N₁ A hAN hNA := by
  classical
  let X : Subgroup G := Xhat N₁ A hAN hNA
  let D : Subgroup ↥A := CFSG.pPrimeCore 3 ↥A
  have hXn : N₁ ≤ Subgroup.normalizer (X : Set G) := by
    simpa [X] using le_normalizer_quotientCentralizer (N := N₁) (L := A) D hAN hNA
  have hJXn : J ≤ Subgroup.normalizer (X : Set G) := hJN.trans hXn
  have hcore_eq : CFSG.Open.pCoreOf 2 J = (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    rw [pCore_two_eq_pPrimeCore_three_of_isL34Type hqJ hJSL.1]
  have hcore_le : CFSG.Open.pCoreOf 2 J ≤ oTwoZStar J := by
    rw [hcore_eq]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hq1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) y = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hy
    rw [hq1]
    exact Subgroup.one_mem _
  have hQ0J_le_X : ⁅Q₀, J⁆ ≤ X := by
    rw [← hJXeq] at hcore_le
    exact (hQ0J.trans hcore_le).trans inf_le_right
  intro p hpQ0
  have hpQ : p ∈ Q := hQ0Q hpQ0
  have hpN₁ : p ∈ N₁ := hQN hpQ
  have hpA : p ∈ Subgroup.normalizer (A : Set G) := hNA hpN₁
  have hcommO : ∀ a ∈ A, p * a * p⁻¹ * a⁻¹ ∈ oTwoZStar A := by
    intro a ha
    have hcommX : p * a * p⁻¹ * a⁻¹ ∈ X :=
      q0_commutator_mem_X hJsup hJXn hQ0J_le_X hpQ0 hpN₁ hXn ha
    have hpaA : p * a * p⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hpA) a).mp ha
    have hcommA : p * a * p⁻¹ * a⁻¹ ∈ A := A.mul_mem hpaA (A.inv_mem ha)
    have hXinfA : X ⊓ A = oTwoZStar A := by
      simpa [X, inf_comm] using (quotientCentralizer_inf_eq_oTwoZStar hAN hNA)
    rw [← hXinfA]
    exact Subgroup.mem_inf.mpr ⟨hcommX, hcommA⟩
  refine (mem_quotientCentralizer D hAN hNA).mpr ⟨⟨p, hpN₁⟩, rfl, ?_⟩
  let β : MulAut (threeStar A) := conjQuotAction N₁ A D hAN hNA ⟨p, hpN₁⟩
  change β = 1
  have hquot : CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient β = 1 := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (threeStar A)) y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective D x
    rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk,
      MulAut.one_apply]
    have hpaA : p * (a : G) * p⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hpA (a : G)).mp a.2
    have hβa : β (QuotientGroup.mk' D a) =
        QuotientGroup.mk' D ⟨p * (a : G) * p⁻¹, hpaA⟩ := by
      simpa [β] using conjQuotAction_apply_mk N₁ A D hAN hNA ⟨p, hpN₁⟩ a
    rw [hβa]
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [div_eq_mul_inv]
    change (QuotientGroup.mk (⟨p * (a : G) * p⁻¹, hpaA⟩ : ↥A) : threeStar A) *
      (QuotientGroup.mk a : threeStar A)⁻¹ ∈ Subgroup.center (threeStar A)
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    have hcomm := hcommO (a : G) a.2
    obtain ⟨c, hc, hceq⟩ := Subgroup.mem_map.mp hcomm
    have hc' : QuotientGroup.mk' D c ∈ Subgroup.center (threeStar A) :=
      Subgroup.mem_comap.mp hc
    have hceq' : c = ⟨p * (a : G) * p⁻¹ * (a : G)⁻¹, A.mul_mem hpaA (A.inv_mem a.2)⟩ :=
      Subtype.ext hceq
    rwa [hceq'] at hc'
  haveI : Group.IsPerfect (threeStar A) := hA'.isQuasisimple.1
  exact CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_eq_one_imp β hquot

private theorem mem_oTwoZStar_of_commutator_le {J : Subgroup G} (hJSL : IsSL34Star J)
    {s : G} (hsJ : s ∈ J)
    (hcomm : ∀ j ∈ J, s * j * s⁻¹ * j⁻¹ ∈ oTwoZStar J) : s ∈ oTwoZStar J := by
  classical
  let q : ↥J →* threeStar J := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)
  let bar : ↥J →* (threeStar J ⧸ Subgroup.center (threeStar J)) :=
    (QuotientGroup.mk' (Subgroup.center (threeStar J))).comp q
  have hbar_center : Subgroup.center (threeStar J ⧸ Subgroup.center (threeStar J)) = ⊥ := by
    obtain ⟨e⟩ := nonempty_mulEquiv_projSL_quotient_center_of_isL34Type hJSL.1
    rw [← Subgroup.map_center_eq e.symm,
      CFSG.RankThree.PartTwo.Sec4.center_projSL_eq_bot, Subgroup.map_bot]
  have hbar_ker : bar.ker = (oTwoZStar J).subgroupOf J := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, oTwoZStar]
    constructor
    · intro hx
      refine Subgroup.mem_map.mpr ⟨x, Subgroup.mem_comap.mpr ?_, rfl⟩
      have hx' : QuotientGroup.mk' (Subgroup.center (threeStar J)) (q x) = 1 := by
        simpa [bar] using hx
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center (threeStar J))
        (x := q x)).mp hx'
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hxy : x = y := Subtype.ext hyx.symm
      rw [hxy]
      simp only [bar, MonoidHom.comp_apply]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_comap.mp hy)
  have hbar_s_center : bar ⟨s, hsJ⟩ ∈
      Subgroup.center (threeStar J ⧸ Subgroup.center (threeStar J)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (threeStar J)) y
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) x
    have hsj : s * (j : G) * s⁻¹ * (j : G)⁻¹ ∈ oTwoZStar J := hcomm j j.2
    let w : ↥J := ⟨s * (j : G) * s⁻¹ * (j : G)⁻¹,
      J.mul_mem (J.mul_mem (J.mul_mem hsJ j.2) (J.inv_mem hsJ)) (J.inv_mem j.2)⟩
    have hwker : w ∈ bar.ker := by
      rw [hbar_ker]
      exact Subgroup.mem_subgroupOf.mpr hsj
    have hw1 : bar w = 1 := hwker
    have hprod : bar ⟨s, hsJ⟩ * bar j * (bar ⟨s, hsJ⟩)⁻¹ * (bar j)⁻¹ = 1 := by
      have hw' : w = ⟨s, hsJ⟩ * j * ⟨s, hsJ⟩⁻¹ * j⁻¹ := Subtype.ext rfl
      rw [hw'] at hw1
      simpa only [map_mul, map_inv] using hw1
    exact ((commutatorElement_eq_one_iff_mul_comm.mp hprod).symm)
  have hbar_s1 : bar ⟨s, hsJ⟩ = 1 := by
    have h := hbar_s_center
    rw [hbar_center] at h
    exact Subgroup.mem_bot.mp h
  have hker : (⟨s, hsJ⟩ : ↥J) ∈ bar.ker := hbar_s1
  rw [hbar_ker] at hker
  exact Subgroup.mem_subgroupOf.mp hker

private theorem S_inf_A_le_center {N₁ A S : Subgroup G}
    (hJSL : IsSL34Star J) (hS_def : S = Q ⊓ J)
    (hJA_le : J ⊓ A ≤ oTwoZStar J)
    (hNA : N₁ ≤ Subgroup.normalizer (A : Set G)) (hJN : J ≤ N₁)
    (hSleJ : S ≤ J) (hQN_J : Q ≤ Subgroup.normalizer (J : Set G))
    (hScenter : S ⊓ oTwoZStar J = (Subgroup.center ↥S).map S.subtype) :
    S ⊓ A ≤ (Subgroup.center ↥S).map S.subtype := by
  intro s hs
  obtain ⟨hsS, hsA⟩ := Subgroup.mem_inf.mp hs
  have hsJ : s ∈ J := hSleJ hsS
  have hcomm : ∀ j ∈ J, s * j * s⁻¹ * j⁻¹ ∈ oTwoZStar J := by
    intro j hj
    have hjsA : j * s * j⁻¹ * s⁻¹ ∈ A := by
      exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNA (hJN hj)) s).mp hsA)
        (A.inv_mem hsA)
    have hjsJ : j * s * j⁻¹ * s⁻¹ ∈ J := by
      exact J.mul_mem (J.mul_mem (J.mul_mem hj hsJ) (J.inv_mem hj)) (J.inv_mem hsJ)
    have hjs : j * s * j⁻¹ * s⁻¹ ∈ J ⊓ A := Subgroup.mem_inf.mpr ⟨hjsJ, hjsA⟩
    have hsj : s * j * s⁻¹ * j⁻¹ = (j * s * j⁻¹ * s⁻¹)⁻¹ := by
      simp only [mul_inv_rev, inv_inv]
      group
    rw [hsj]
    exact hJA_le ((J ⊓ A).inv_mem hjs)
  have hsO : s ∈ oTwoZStar J := mem_oTwoZStar_of_commutator_le hJSL hsJ hcomm
  have hmem : s ∈ S ⊓ oTwoZStar J := Subgroup.mem_inf.mpr ⟨hsS, hsO⟩
  rwa [hScenter] at hmem

private theorem eq_sup_Q0_S {Q Q₀ S Z : Subgroup G}
    (hQ0Q : Q₀ ≤ Q) (hS_eq : S = Q ⊓ J)
    (hQ0card : Nat.card Q₀ = 27) (hScard : Nat.card S = 27)
    (hZcard : Nat.card Z = 3) (hQcard : Nat.card Q = 3 ^ 5)
    (hQQ : ⁅Q, Q⁆ ≤ Q₀) (hQ0C : Q₀ ≤ Subgroup.centralizer (S : Set G))
    (hQN_J : Q ≤ Subgroup.normalizer (J : Set G)) (hQ0J_eq : Q₀ ⊓ J = Z) :
    Q = Q₀ ⊔ S := by
  classical
  have hQ0normal : (Q₀.subgroupOf Q).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (g : G) * (n : G) * (g : G)⁻¹ * (n : G)⁻¹ ∈ Q₀ :=
      hQQ (Subgroup.commutator_mem_commutator g.2 (hQ0Q hn))
    have heq : (g : G) * (n : G) * (g : G)⁻¹ =
        ((g : G) * (n : G) * (g : G)⁻¹ * (n : G)⁻¹) * (n : G) := by group
    change (g : G) * (n : G) * (g : G)⁻¹ ∈ Q₀
    rw [heq]
    exact Q₀.mul_mem hc hn
  have hSnormal : (S.subgroupOf Q).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [hS_eq] at hn ⊢
    have hnQ : (n : G) ∈ Q := (Subgroup.mem_inf.mp hn).1
    have hnJ : (n : G) ∈ J := (Subgroup.mem_inf.mp hn).2
    change (g : G) * (n : G) * (g : G)⁻¹ ∈ Q ⊓ J
    refine Subgroup.mem_inf.mpr ⟨Q.mul_mem (Q.mul_mem g.2 hnQ) (Q.inv_mem g.2), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hQN_J g.2) (n : G)).mp hnJ
  have hZS : Q₀ ⊓ S = Z := by
    rw [hS_eq, ← inf_assoc, inf_eq_left.mpr hQ0Q, hQ0J_eq]
  have hN : Q₀ ≤ Subgroup.normalizer (S : Set G) :=
    hQ0C.trans (Subgroup.centralizer_le_normalizer _)
  have hcard := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := Q₀) (K := S) hN
  rw [hZS, hZcard, hQ0card, hScard] at hcard
  have hsupcard : Nat.card ↥(Q₀ ⊔ S) = 243 := by omega
  have hle : Q₀ ⊔ S ≤ Q := sup_le hQ0Q (by rw [hS_eq]; exact inf_le_left)
  have heq : Q₀ ⊔ S = Q :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hQcard, hsupcard]; norm_num)
  exact heq.symm

private theorem le_normalizer_oTwoZStar_of_le_normalizer_J {Q J : Subgroup G}
    (hQ : Q ≤ Subgroup.normalizer (J : Set G)) :
    Q ≤ Subgroup.normalizer (oTwoZStar J : Set G) := by
  classical
  let q : ↥J →* threeStar J := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)
  let H : Subgroup ↥J := (Subgroup.center (threeStar J)).comap q
  have hHchar : H.Characteristic :=
    Subgroup.Characteristic.comap_quotient_mk (H := CFSG.pPrimeCore 3 ↥J)
      (K := Subgroup.center (threeStar J)) (inferInstance)
  have hmap : H.map J.subtype = oTwoZStar J := rfl
  rw [← hmap]
  exact hQ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic H)

private theorem inf_A_le_center_of_l34 {N₁ A Q₀ S X ZQ : Subgroup G}
    (hJSL : IsSL34Star J) (hQeq : Q = Q₀ ⊔ S) (hS_eq : S = Q ⊓ J)
    (hQ0Q : Q₀ ≤ Q)
    (hQ0C : Q₀ ≤ Subgroup.centralizer (S : Set G))
    (hQN_J : Q ≤ Subgroup.normalizer (J : Set G))
    (hJNA : J ≤ Subgroup.normalizer (A : Set G))
    (hQ0J : ⁅Q₀, J⁆ ≤ CFSG.Open.pCoreOf 2 J)
    (hcore_le : CFSG.Open.pCoreOf 2 J ≤ oTwoZStar J)
    (hJA_le : J ⊓ A ≤ oTwoZStar J)
    (hQ0_le_X : Q₀ ≤ X) (hXinfA : X ⊓ A = oTwoZStar A)
    (hScenter : S ⊓ oTwoZStar J = (Subgroup.center ↥S).map S.subtype)
    (hSZQ : (Subgroup.center ↥S).map S.subtype = ZQ)
    (hZQcard : Nat.card ZQ = 3) (hAQ0 : ZQ ≤ Q₀) (hZA : ZQ ≤ A)
    (hQp : IsPGroup 3 Q) (h9A : ¬ 9 ∣ Nat.card (oTwoZStar A)) :
    Q ⊓ A ≤ ZQ := by
  classical
  intro q hq
  obtain ⟨hqQ, hqA⟩ := Subgroup.mem_inf.mp hq
  have hQ0N_S : Q₀ ≤ Subgroup.normalizer (S : Set G) :=
    hQ0C.trans (Subgroup.centralizer_le_normalizer _)
  have hcoe : ((Q₀ ⊔ S : Subgroup G) : Set G) = (Q₀ : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Q₀ S hQ0N_S
  have hqQ' : q ∈ Q₀ ⊔ S := by rwa [hQeq] at hqQ
  have hqmem : q ∈ (Q₀ : Set G) * (S : Set G) := by rwa [← hcoe]
  obtain ⟨p, hpQ0, s, hsS, hps⟩ := hqmem
  have hpQ : p ∈ Q := hQ0Q hpQ0
  have hsQ : s ∈ Q := (Subgroup.mem_inf.mp (hS_eq ▸ hsS)).1
  have hsJ : s ∈ J := (Subgroup.mem_inf.mp (hS_eq ▸ hsS)).2
  have hs_eq : s = p⁻¹ * q := by
    calc s = p⁻¹ * (p * s) := by group
      _ = p⁻¹ * q := by rw [show p * s = q from hps]
  have hQnO : Q ≤ Subgroup.normalizer (oTwoZStar J : Set G) :=
    le_normalizer_oTwoZStar_of_le_normalizer_J hQN_J
  have hcomm : ∀ j ∈ J, s * j * s⁻¹ * j⁻¹ ∈ oTwoZStar J := by
    intro j hj
    have hjqA : j * q * j⁻¹ * q⁻¹ ∈ A := by
      exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hJNA hj) q).mp hqA)
        (A.inv_mem hqA)
    have hjqJ : j * q * j⁻¹ * q⁻¹ ∈ J := by
      have hqjJ : q * j * q⁻¹ * j⁻¹ ∈ J :=
        J.mul_mem ((Subgroup.mem_normalizer_iff.mp (hQN_J hqQ) j).mp hj) (J.inv_mem hj)
      have heq : j * q * j⁻¹ * q⁻¹ = (q * j * q⁻¹ * j⁻¹)⁻¹ := by
        simp only [mul_inv_rev, inv_inv]
        group
      rw [heq]
      exact J.inv_mem hqjJ
    have hqj : ⁅q, j⁆ ∈ oTwoZStar J := by
      have h1 := hJA_le (Subgroup.mem_inf.mpr ⟨hjqJ, hjqA⟩)
      have heq : ⁅q, j⁆ = ⁅j, q⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [heq]
      exact (oTwoZStar J).inv_mem h1
    have hconj : p⁻¹ * ⁅q, j⁆ * p ∈ oTwoZStar J := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hQnO (Q.inv_mem hpQ)) _).mp hqj
    have hpj : ⁅p⁻¹, j⁆ ∈ oTwoZStar J :=
      hcore_le (hQ0J (Subgroup.commutator_mem_commutator (Q₀.inv_mem hpQ0) hj))
    have hformula : ⁅s, j⁆ = p⁻¹ * ⁅q, j⁆ * p * ⁅p⁻¹, j⁆ := by
      rw [hs_eq, commutatorElement_mul_left_eq_conj_mul]
      group
    have hmem : ⁅s, j⁆ ∈ oTwoZStar J := by
      rw [hformula]
      exact (oTwoZStar J).mul_mem hconj hpj
    simpa only [commutatorElement_def] using hmem
  have hsO : s ∈ oTwoZStar J := mem_oTwoZStar_of_commutator_le hJSL hsJ hcomm
  have hsZQ : s ∈ ZQ := by
    have hmem : s ∈ S ⊓ oTwoZStar J := Subgroup.mem_inf.mpr ⟨hsS, hsO⟩
    rw [hScenter] at hmem
    rwa [hSZQ] at hmem
  have hsA : s ∈ A := hZA hsZQ
  have hpA : p ∈ A := by
    have hp_eq : p = q * s⁻¹ := by
      rw [← hps]
      group
    rw [hp_eq]
    exact A.mul_mem hqA (A.inv_mem hsA)
  have hQ0A_sub : Q₀ ⊓ A ≤ oTwoZStar A := by
    rw [← hXinfA]
    exact le_inf (inf_le_left.trans hQ0_le_X) inf_le_right
  have hQ0A_pg : IsPGroup 3 ↥(Q₀ ⊓ A) :=
    hQp.to_le (inf_le_left.trans hQ0Q)
  have hQ0A_card : Nat.card ↥(Q₀ ⊓ A) ≤ 3 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ0A_pg
    have hk1 : k ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ k := by omega
      have h9 : 9 ∣ Nat.card ↥(Q₀ ⊓ A) := by
        rw [hk]
        exact pow_dvd_pow 3 h2
      exact h9A (h9.trans (Subgroup.card_dvd_of_le hQ0A_sub))
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 3 := by norm_num
  have hZle : ZQ ≤ Q₀ ⊓ A := le_inf hAQ0 hZA
  have hQ0A_eq : Q₀ ⊓ A = ZQ := by
    exact (Subgroup.eq_of_le_of_card_ge hZle (by rw [hZQcard]; exact hQ0A_card)).symm
  have hpZQ : p ∈ ZQ := hQ0A_eq ▸ Subgroup.mem_inf.mpr ⟨hpQ0, hpA⟩
  rw [← hps]
  exact ZQ.mul_mem hpZQ hsZQ

private theorem commutator_le_map_center_of_card_27 {S : Subgroup G}
    (hScard : Nat.card ↥S = 27) :
    ⁅S, S⁆ ≤ (Subgroup.center ↥S).map S.subtype := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  refine Subgroup.mem_map.mpr
    ⟨⟨⁅x, y⁆, Subgroup.commutator_le_self S (Subgroup.commutator_mem_commutator hx hy)⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro z
  have h := CFSG.Quasithin.H13.R2.comm_comm_of_card_27 hScard
    (⟨x, hx⟩ : ↥S) (⟨y, hy⟩ : ↥S) z
  exact (commutatorElement_eq_one_iff_mul_comm.mp h).symm

private theorem center_S_eq_center_Q_of_l34 {Q Q₀ S ZQ : Subgroup G}
    (hScard : Nat.card ↥S = 27) (hZsCard : Nat.card ↥((Subgroup.center ↥S).map S.subtype) = 3)
    (hZQcard : Nat.card ↥ZQ = 3)
    (hcenter_le_comm : ZQ ≤ ⁅S, S⁆) :
    (Subgroup.center ↥S).map S.subtype = ZQ := by
  have hSS : ⁅S, S⁆ ≤ (Subgroup.center ↥S).map S.subtype :=
    commutator_le_map_center_of_card_27 hScard
  exact (Subgroup.eq_of_le_of_card_ge (hcenter_le_comm.trans hSS)
    (by rw [hZQcard, hZsCard])).symm

private theorem exists_elemAbelian_nine_le_of_l34 {A : Subgroup G}
    (hA' : IsKComp M N A) (h34 : IsL34Type (threeStar A)) :
    ∃ E : Subgroup G, E ≤ A ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 := CFSG.LocalAnalysis.RankThreeUC.AGL81C.kFactThreeRankL34_holds
    (threeStar A) hA'.isQuasisimple h34
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank 3 (⊤ : Subgroup (threeStar A))] at h2
  obtain ⟨Ebar, -, hEbarelem, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (H := ⊤) (k := 2) h2
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥A) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  obtain ⟨S, -, hSelem, hScard⟩ :=
    CFSG.RankThree.Classical2.exists_elemAbelian_lift (p := 3)
      (N := CFSG.pPrimeCore 3 ↥A) hN hEbarelem
  exact ⟨S.map A.subtype, Subgroup.map_subtype_le S,
    CFSG.SectionRank.isElemAbelian_map hSelem _, by
      rw [Subgroup.card_map_of_injective A.subtype_injective, hScard, hEcard]
      norm_num⟩

private theorem inf_eq_bot_of_not_center_le {Q A : Subgroup G} (hQp : IsPGroup 3 Q)
    (hQA : Q ≤ Subgroup.normalizer (A : Set G))
    (hZQcard : Nat.card ((Subgroup.center ↥Q).map Q.subtype) = 3)
    (hZA : ¬ (Subgroup.center ↥Q).map Q.subtype ≤ A) : Q ⊓ A = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (A.subgroupOf Q).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hQA g.2) (n : G)).mp hn
  by_contra hne
  have hN : A.subgroupOf Q ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxQ, hxA⟩ := Subgroup.mem_inf.mp hx
    have hx' : (⟨x, hxQ⟩ : ↥Q) ∈ A.subgroupOf Q := Subgroup.mem_subgroupOf.mpr hxA
    rw [hbot, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot
      hQp (A.subgroupOf Q) hN)
  have hzA : ((z : ↥Q) : G) ∈ A :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp z.2).1
  have hzZ : ((z : ↥Q) : G) ∈ (Subgroup.center ↥Q).map Q.subtype :=
    Subgroup.mem_map_of_mem Q.subtype (Subgroup.mem_inf.mp z.2).2
  have hz1' : ((z : ↥Q) : G) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  apply hZA
  rw [CFSG.Literature.GL52.eq_zpowers_of_card_prime Nat.prime_three hZQcard hzZ hz1']
  exact Subgroup.zpowers_le.mpr hzA

private theorem exists_elemAbelian_nine_inf_eq_bot_of_not_center_le
    {N₁ A Q Q₀ X : Subgroup G} (hQp : IsPGroup 3 Q) (hQ0Q : Q₀ ≤ Q)
    (hQ0card : Nat.card Q₀ = 27) (hQexp : ∀ x ∈ Q, x ^ 3 = 1)
    (hQ0_le_X : Q₀ ≤ X) (hQA : Q ≤ Subgroup.normalizer (A : Set G))
    (hZQcard : Nat.card ((Subgroup.center ↥Q).map Q.subtype) = 3)
    (hZA : ¬ (Subgroup.center ↥Q).map Q.subtype ≤ A) :
    ∃ F : Subgroup G, F ≤ X ∧ IsElemAbelian 3 F ∧ Nat.card F = 9 ∧ F ⊓ A = ⊥ := by
  classical
  have hQAbot : Q ⊓ A = ⊥ :=
    inf_eq_bot_of_not_center_le hQp hQA hZQcard hZA
  obtain ⟨E, hEelem, hEcard⟩ :=
    CFSG.Quasithin.S1549C.exists_elemAbelian_nine (P := ↥Q₀)
      (by intro x; exact Subtype.ext (by simpa using hQexp (x : G) (hQ0Q x.2)))
      (by rw [hQ0card]; norm_num)
  let F : Subgroup G := E.map Q₀.subtype
  have hFQ0 : F ≤ Q₀ := Subgroup.map_subtype_le _
  have hFX : F ≤ X := hFQ0.trans hQ0_le_X
  have hFelem : IsElemAbelian 3 F := CFSG.SectionRank.isElemAbelian_map hEelem _
  have hFcard : Nat.card F = 9 := by
    rw [Subgroup.card_map_of_injective Q₀.subtype_injective, hEcard]
  have hFA : F ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxQ : x ∈ Q := hQ0Q (hFQ0 hx.1)
    have hxQA : x ∈ Q ⊓ A := Subgroup.mem_inf.mpr ⟨hxQ, hx.2⟩
    rw [hQAbot] at hxQA
    exact hxQA
  exact ⟨F, hFX, hFelem, hFcard, hFA⟩

private theorem exists_elemAbelian_nine_inf_eq_bot_of_center_le
    {N₁ A Q : Subgroup G} (hAN : A ≤ N₁)
    (hNA : N₁ ≤ Subgroup.normalizer (A : Set G))
    (hQAX : Q ≤ A ⊔ Xhat N₁ A hAN hNA) (hQp : IsPGroup 3 Q)
    (hQexp : ∀ x ∈ Q, x ^ 3 = 1)
    (hQQeq : ⁅Q, Q⁆ = (Subgroup.center ↥Q).map Q.subtype)
    (hZQcard : Nat.card ((Subgroup.center ↥Q).map Q.subtype) = 3)
    (hZA : (Subgroup.center ↥Q).map Q.subtype ≤ A)
    (hQinfA : Q ⊓ A = (Subgroup.center ↥Q).map Q.subtype)
    (hQcard : Nat.card Q = 3 ^ 5)
    (h9A : ¬ 9 ∣ Nat.card (oTwoZStar A)) :
    ∃ F : Subgroup G, F ≤ Xhat N₁ A hAN hNA ∧ IsElemAbelian 3 F ∧
      Nat.card F = 9 ∧ F ⊓ A = ⊥ := by
  have hPA : Nat.card ↥(Q ⊓ A) ≤ 3 := by
    rw [hQinfA]
    exact le_of_eq hZQcard
  have hcube : ∀ x ∈ Q, x ^ 3 ∈ A := by
    intro x hx
    rw [hQexp x hx]
    exact A.one_mem
  have hcomm : ⁅Q, Q⁆ ≤ A := by
    rw [hQQeq]
    exact hZA
  have h81 : 81 * Nat.card ↥(Q ⊓ A) ≤ Nat.card Q := by
    rw [hQinfA, hZQcard, hQcard]
    norm_num
  exact exists_elemAbelian_nine_inf_eq_bot hAN hNA hQp hQAX hcube hcomm h81 h9A

private theorem four_le_pRank_of_l34 {N₁ A E F : Subgroup G}
    (hAN : A ≤ N₁) (hNA : N₁ ≤ Subgroup.normalizer (A : Set G))
    (hEA : E ≤ A) (hEelem : IsElemAbelian 3 E) (hEcard : Nat.card E = 9)
    (hFX : F ≤ Xhat N₁ A hAN hNA) (hFelem : IsElemAbelian 3 F)
    (hFcard : Nat.card F = 9) (hFA : F ⊓ A = ⊥) :
    4 ≤ CFSG.Open.pRank 3 N₁ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let D : Subgroup G := (CFSG.pPrimeCore 3 ↥A).map A.subtype
  have hXleN₁ : Xhat N₁ A hAN hNA ≤ N₁ := quotientCentralizer_le N₁ A _ hAN hNA
  have hD3 : ¬ 3 ∣ Nat.card D := by
    rw [show Nat.card D = Nat.card (CFSG.pPrimeCore 3 ↥A) from
      Subgroup.card_map_of_injective A.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hDnorm : N₁ ≤ Subgroup.normalizer (D : Set G) :=
    hNA.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pPrimeCore 3 ↥A))
  have hcomm : ⁅E, F⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro e he f' hf'
    have hmem := commutator_mem_map_of_mem_quotientCentralizer
      (Q := CFSG.pPrimeCore 3 ↥A) hAN hNA (hFX hf') (hEA he)
    have heq : ⁅e, f'⁆ = (f' * e * f'⁻¹ * e⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [heq]
    exact D.inv_mem hmem
  have hint : (E ⊔ D) ⊓ (F ⊔ D) ≤ D := by
    intro x hx
    obtain ⟨hxED, hxFD⟩ := Subgroup.mem_inf.mp hx
    have hFDnorm : F ≤ Subgroup.normalizer (D : Set G) :=
      (hFX.trans hXleN₁).trans hDnorm
    have hxFD' : x ∈ (F : Set G) * (D : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right F D hFDnorm]
      exact hxFD
    obtain ⟨f', hf', d, hd, hfd⟩ := hxFD'
    have hxA : x ∈ A := (sup_le hEA (Subgroup.map_subtype_le _)) hxED
    have hf'A : f' ∈ A := by
      have : f' = x * d⁻¹ := by rw [← hfd]; group
      rw [this]
      exact A.mul_mem hxA (A.inv_mem (Subgroup.map_subtype_le _ hd))
    have hf'bot : f' ∈ F ⊓ A := Subgroup.mem_inf.mpr ⟨hf', hf'A⟩
    rw [hFA] at hf'bot
    rw [Subgroup.mem_bot] at hf'bot
    rw [← hfd, hf'bot]
    simpa using hd
  have h := CFSG.Quasithin.add_le_pRank_of_commute_mod (p := 3) (X := N₁)
    (Q := D) (E := E) (F := F) (a := 2) (b := 2) hD3
    (hEA.trans hAN |>.trans hDnorm) (hFX.trans hXleN₁ |>.trans hDnorm) hEelem hFelem
    (by rw [hEcard]; norm_num) (by rw [hFcard]; norm_num) hcomm hint
    (hEA.trans hAN) (hFX.trans hXleN₁) (Subgroup.map_subtype_le _ |>.trans hAN)
  simpa using h

private theorem false_of_l34
    {N₁ A : Subgroup G}
    (h : S14Choice G M H E Q J) (hA : TypeA M H) (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) (h142 : FourteenTwoCaseOneAt M)
    (hA' : IsKComp M N A) (hAN : A ≤ N₁)
    (hNA : N₁ ≤ Subgroup.normalizer (A : Set G))
    (hJN : J ≤ N₁) (hQN : Q ≤ N₁) (hJX : ¬ J ≤ Xhat N₁ A hAN hNA)
    (hJA : ¬ J ≤ A) (h34 : IsSL34Star A ∨ IsL34Star A)
    (hrank : CFSG.Open.pRank 3 N₁ ≤ 3) : False := by
  classical
  let X : Subgroup G := Xhat N₁ A hAN hNA
  let S : Subgroup G := Q ⊓ J
  let ZQ : Subgroup G := (Subgroup.center ↥Q).map Q.subtype
  have hJ : IsKComp M H J := h.isKComp
  have hJSL : IsSL34Star J := h.isSL34Star_of_typeA hpre hU hA
  have hqJ : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) := h.J_comp.2.2.1
  have htype : IsSL34Star A ∨ IsL34Star A ∨ IsA11Star A ∨ Is3A6Star A :=
    h34.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))
  have hL34 : IsL34Type (threeStar A) := h34.elim (fun h => h.1) (fun h => h.1)
  have hSJ : CFSG.ABGLocalTools.IsSylowOf 3 S J := h.isSylowOf_inf_J hpre hU
  obtain ⟨hScard, hSexp, hScenter, hScenterCard⟩ :=
    IsKComp.sylow_three_structure hJ (Or.inl hJSL) hSJ
  have hJAnormal : ((J ⊓ A).subgroupOf J).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨J.mul_mem (J.mul_mem g.2 hn.1) (J.inv_mem g.2),
      (Subgroup.mem_normalizer_iff.mp ((hJN.trans hNA) g.2) (n : G)).mp hn.2⟩
  have hJAne : J ⊓ A ≠ J := by
    intro hEq
    apply hJA
    rw [← hEq]
    exact inf_le_right
  have hJA_le : J ⊓ A ≤ oTwoZStar J :=
    IsKComp.le_oTwoZStar_of_normal hJ inf_le_left hJAnormal hJAne
  obtain ⟨hJXeq, hJsup_eq⟩ :=
    inf_eq_oTwoZStar_and_sup_eq_of_l34 hJ hJSL hA' htype hL34 hAN hNA hJN hJX
  have hJsupA : A ≤ J ⊔ X := by
    rw [hJsup_eq]
    exact le_sup_left
  have hJ_le_AX : J ≤ A ⊔ X := by
    rw [← hJsup_eq]
    exact le_sup_left
  obtain ⟨R, T, c⟩ := exists_caseOneCtx h hA hpre hU hL
  obtain ⟨Q₀, hQ0Q, hQ0card, hQ0J, hAQ0, hQ0C, hQ0Jeq, f, hfQ0, hfJ⟩ :=
    c.exists_Q₀ h142
  have hQ0_le_X : Q₀ ≤ X :=
    q0_le_quotientCentralizer hqJ hA' hAN hNA hJ hJSL hQ0Q hQ0J hQN hJN hJsupA hJXeq
  have h142' := h142 H E Q J h hA
  have hQcard : Nat.card Q = 3 ^ 5 := h142'.1.1
  have hQexp : ∀ x ∈ Q, x ^ 3 = 1 := h142'.1.2.1
  have hQQeq : ⁅Q, Q⁆ = ZQ := by simpa [ZQ] using h142'.1.2.2.1
  have hZQcard : Nat.card ZQ = 3 := by simpa [ZQ] using h142'.1.2.2.2
  have hQQ : ⁅Q, Q⁆ ≤ Q₀ := by rw [hQQeq]; exact hAQ0
  have hQNJ : Q ≤ Subgroup.normalizer (J : Set G) := h.Q_le_normalizer_J hpre hU
  have hQeq : Q = Q₀ ⊔ S :=
    eq_sup_Q0_S hQ0Q rfl hQ0card hScard hZQcard hQcard hQQ hQ0C hQNJ hQ0Jeq
  have hQAX : Q ≤ A ⊔ X := by
    rw [hQeq]
    exact sup_le (hQ0_le_X.trans le_sup_right) (hSJ.le.trans hJ_le_AX)
  have hXinfA : X ⊓ A = oTwoZStar A := by
    simpa [X, inf_comm] using (quotientCentralizer_inf_eq_oTwoZStar hAN hNA)
  have h9A : ¬ 9 ∣ Nat.card (oTwoZStar A) := not_nine_dvd_card_oTwoZStar_of_l34 h34
  have hcore_le : CFSG.Open.pCoreOf 2 J ≤ oTwoZStar J := by
    have heq : CFSG.Open.pCoreOf 2 J = (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
      rw [CFSG.openPCoreOf_eq_map_pCore]
      rw [pCore_two_eq_pPrimeCore_three_of_isL34Type hqJ hJSL.1]
    rw [heq]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) y = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hy
    rw [h1]
    exact Subgroup.one_mem _
  have hFexists : ∃ F : Subgroup G, F ≤ X ∧ IsElemAbelian 3 F ∧ Nat.card F = 9 ∧
      F ⊓ A = ⊥ := by
    by_cases hZA : ZQ ≤ A
    · have hQinfA : Q ⊓ A = ZQ := by
        have hZS : (Subgroup.center ↥S).map S.subtype = ZQ :=
          center_S_eq_center_Q_of_l34 (Q := Q) (Q₀ := Q₀) hScard hScenterCard hZQcard
            (c.center_le_commutator h142)
        have hle := inf_A_le_center_of_l34 (N₁ := N₁) (A := A) (Q₀ := Q₀) (S := S)
          (X := X) (ZQ := ZQ) hJSL hQeq rfl hQ0Q hQ0C hQNJ (hJN.trans hNA)
          hQ0J hcore_le
          hJA_le hQ0_le_X hXinfA hScenter hZS hZQcard hAQ0 hZA h.sylow.isPGroup h9A
        exact le_antisymm hle (le_inf (hAQ0.trans hQ0Q) hZA)
      exact exists_elemAbelian_nine_inf_eq_bot_of_center_le hAN hNA hQAX
        h.sylow.isPGroup hQexp hQQeq hZQcard hZA hQinfA hQcard h9A
    · exact exists_elemAbelian_nine_inf_eq_bot_of_not_center_le (N₁ := N₁) (A := A)
        (Q := Q) (Q₀ := Q₀) (X := X) h.sylow.isPGroup hQ0Q
        hQ0card hQexp hQ0_le_X (hQN.trans hNA) hZQcard hZA
  obtain ⟨F, hFX, hFelem, hFcard, hFA⟩ := hFexists
  obtain ⟨E, hEA, hEelem, hEcard⟩ := exists_elemAbelian_nine_le_of_l34 hA' hL34
  have h4 := four_le_pRank_of_l34 hAN hNA hEA hEelem hEcard hFX hFelem hFcard hFA
  omega

theorem S14Choice.le_of_not_le_quotientCentralizer
    (h : S14Choice G M H E Q J) (hA : TypeA M H)
    (hpre : PreambleTypes M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (h142 : FourteenTwoCaseOneAt M) {N₁ A : Subgroup G} (hAN : A ≤ N₁)
    (hNA : N₁ ≤ Subgroup.normalizer (A : Set G)) (hA' : IsKComp M N A)
    (htype : IsSL34Star A ∨ IsL34Star A ∨ IsA11Star A ∨ Is3A6Star A)
    (hrank : CFSG.Open.pRank 3 N₁ ≤ 3) (hJN : J ≤ N₁) (hQN : Q ≤ N₁)
    (hJX : ¬ J ≤ Xhat N₁ A hAN hNA) : J ≤ A := by
  by_contra hJA
  have hJ : IsKComp M H J := h.isKComp
  have hJSL : IsSL34Star J := h.isSL34Star_of_typeA hpre hU hA
  have htypeFull := htype
  rcases htype with h34SL | h34L | h34A11 | h34A6
  · exact false_of_l34 h hA hpre hU hL h142 hA' hAN hNA hJN hQN hJX hJA
      (Or.inl h34SL) hrank
  · exact false_of_l34 h hA hpre hU hL h142 hA' hAN hNA hJN hQN hJX hJA
      (Or.inr h34L) hrank
  · exact false_of_isA11Star h hpre hU hJ hJSL hA' h34A11 htypeFull hAN hNA hJN hJX hJA hrank
  · exact false_of_is3A6Star hJ hJSL hA' htypeFull h34A6 hAN hNA hJN hJX

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
