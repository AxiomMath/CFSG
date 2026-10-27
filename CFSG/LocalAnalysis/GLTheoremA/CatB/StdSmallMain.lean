module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.StdSmallDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.StdSmallBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatB.StdSmallCore
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_of_center {K : Subgroup G} (h2 : IsPGroup 2 ↥(Subgroup.center ↥K))
    (hne : Subgroup.center ↥K ≠ ⊥) :
    ∃ z ∈ K, z ^ 2 = 1 ∧ z ≠ 1 ∧ ∀ k ∈ K, k * z = z * k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥K) := by
    rcases h2.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hne
    · exact h1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  refine ⟨((z : ↥K) : G), (z : ↥K).2, ?_, ?_, ?_⟩
  · have := congrArg (fun w : ↥(Subgroup.center ↥K) => (((w : ↥K)) : G)) hz2
    simpa using this
  · intro h1
    have : z = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hz
    omega
  · intro k hk
    have := Subgroup.mem_center_iff.1 z.2 ⟨k, hk⟩
    exact congrArg Subtype.val this

theorem stdSubSmallAt_of_cover_facts (hcov : StdSubCoverAt G) (hinn4 : StdSubInnerD4At G)
    (hrank : Rank23At G) (hd4 : D4Rank4At) : StdSubSmallAt G := by
  intro B x L D K hS hB4 hqs hchev hinnM hpre hsmall
  have hKcomp := hpre.2.2.2.2.2.1
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hKL : K ≤ L := hKcomp.1.trans inf_le_left
  by_cases hZ : Subgroup.center ↥K = ⊥
  · exact glaSmall_of_center_bot hKq hZ hsmall
  exfalso
  obtain ⟨hZ2, hZL, hhost⟩ := hcov B x L D K hS hB4 hqs hchev hinnM hpre hsmall hZ
  obtain ⟨z, hzK, hz2, hz1, hzc⟩ := exists_involution_of_center hZ2 hZ
  have hzL : z ∈ L := hKL hzK
  have hzcL : ∀ l ∈ L, l * z = z * l := hZL z hzK hzc
  have hBel : IsElemAbelian 3 B := (IsSStarMax.bmax hS).1
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := IsSStarMax.normalizes hS
  have hcomp : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) L := IsSStarMax.component hS
  have hlist : catalogIs (PSimple 3 L) S9.isList94 :=
    S10.catalogIs_imp (fun i hi => by
      rcases hi with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))) hhost
  obtain ⟨hZb, hbinn, hc⟩ := hrank (Subgroup.centralizer ({x} : Set G)) L hcomp hlist
  have hperf : ⁅L, L⁆ = L := glaPComponent_perfect hcomp
  have hOz : ∀ o ∈ GLAPPrimeCoreOf 3 L, ∀ l ∈ L, l * o = o * l := by
    have hbar : CFSG.Open.IsQuasisimple (PQuot 3 L) :=
      isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hcomp
    have hne : GLAPPrimeCore 3 ↥L ≠ ⊤ := by
      intro htop
      haveI : Subsingleton (PQuot 3 L) := by
        show Subsingleton (↥L ⧸ GLAPPrimeCore 3 ↥L)
        rw [htop]
        exact QuotientGroup.subsingleton_quotient_top
      haveI : Nontrivial (PQuot 3 L ⧸ Subgroup.center (PQuot 3 L)) := hbar.2.toNontrivial
      haveI : Subsingleton (PQuot 3 L ⧸ Subgroup.center (PQuot 3 L)) :=
        Function.Surjective.subsingleton (QuotientGroup.mk'_surjective (Subgroup.center (PQuot 3 L)))
      exact not_subsingleton _ ‹_›
    have hle : GLAPPrimeCore 3 ↥L ≤ Subgroup.center ↥L :=
      le_center_of_normal_of_isQuasisimple hqs inferInstance hne
    intro o ho l hl
    obtain ⟨o', ho', rfl⟩ := Subgroup.mem_map.1 ho
    have := Subgroup.mem_center_iff.1 (hle ho') ⟨l, hl⟩
    exact congrArg Subtype.val this
  have hZ3 : ∀ z' ∈ L, (∀ l ∈ L, l * z' = z' * l) → ¬ 3 ∣ orderOf z' := by
    intro z' hz'L hz'c h3
    have hcent : z' ∈ Subgroup.centralizer (L : Set G) := Subgroup.mem_centralizer_iff.2 hz'c
    have hcm : CentMod 3 L z' := centMod_of_mem_centralizer hcent
    have hO : z' ∈ GLAPPrimeCoreOf 3 L := mem_glaPPrimeCoreOf_of_centMod hZb hz'L hcm
    have hd : orderOf z' ∣ Nat.card ↥(GLAPPrimeCoreOf 3 L) := Subgroup.orderOf_dvd_natCard _ hO
    exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three L (h3.trans hd)
  have hinn' : ∀ b ∈ B, InducesInnerMod 3 L b := by
    by_cases hD4 : catalogIs (PSimple 3 L) S9.isD4two
    · exact hinn4 B L hqs hD4 hBel hinnM
    · intro b hb
      by_contra hnb
      exact hD4 (hbinn b (hBN hb) (hBel.2 b hb) hnb)
  obtain ⟨hxnL, hcard, T, hTL, hT2, hT1, hBT, hTO⟩ := cover_core hS hperf hOz hZ3 hinn'
  have hAel : IsElemAbelian 3 (B ⊓ L) := isElemAbelian_mono hBel inf_le_left
  have hAN : B ⊓ L ≤ Subgroup.normalizer (T : Set G) := inf_le_left.trans hBT
  obtain ⟨hc27, hc9⟩ := hc (B ⊓ L) T inf_le_right hAel hTL hT2 hTO hAN
  have hB81 : 81 ≤ Nat.card B := by simpa using hB4
  by_cases hSU : catalogIs (PSimple 3 L) (fun i => S9.isSp6two i ∨ S9.isU4two i)
  · have h9 := hc9 hSU
    omega
  · have hD4 : catalogIs (PSimple 3 L) S9.isD4two := by
      obtain ⟨i, hi, hiso⟩ := hhost
      rcases hi with h | h | h
      · exact absurd ⟨i, Or.inl h, hiso⟩ hSU
      · exact absurd ⟨i, Or.inr h, hiso⟩ hSU
      · exact ⟨i, h, hiso⟩
    obtain ⟨E₀, hE₀, hE₀c⟩ := hd4 (PSimple 3 L) hD4
    obtain ⟨π, hπs, hπk⟩ := CatB.exists_hom_of_simple_equiv (p := 3) (J := L)
      (MulEquiv.refl (PSimple 3 L))
    have hker : ¬ 3 ∣ Nat.card π.ker := CatB.not_three_dvd_card_ker L hπk hZb
    obtain ⟨W, hW3, hWmap, hWinj⟩ := CatB.exists_pSubgroup_lift Nat.prime_three π hker
      (isPGroup_of_isElemAbelian hE₀) (by rw [MonoidHom.range_eq_top.2 hπs]; exact le_top)
    obtain ⟨hEel, hEcard⟩ := CatB.map_subtype_isElemAbelian_card π hWmap hWinj hE₀
    have hsq := three_mul_card_le hS hxnL hz2 hz1 hzL hzcL hEel (Subgroup.map_subtype_le W)
    rw [hEcard, hE₀c] at hsq
    omega

end CFSG.LocalAnalysis.GLTheoremA
