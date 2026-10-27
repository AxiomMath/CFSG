module

public import CFSG.Open.LocalVocabulary

import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.LocalAnalysis.PreuniquenessRankFour.PrimeCore
import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.LocalAnalysis.SectionRank.TwoGenerators

public section

namespace CFSG.GroupTheory.CentralQuotient

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G] {p s : ℕ}

theorem exists_pow_eq_one_not_mem_of_card_eq_cube {Q : Type*} [Group Q] [Finite Q]
    [Fact p.Prime] (hp : p ≠ 2) {Z : Subgroup Q} (hZc : Z ≤ Subgroup.center Q)
    (hZ : Nat.card Z = p) (hQ : Nat.card Q = p ^ 3) (hcomm : ∀ x y : Q, ⁅x, y⁆ ∈ Z)
    (hpow : ∀ x : Q, x ^ p ∈ Z) : ∃ x : Q, x ^ p = 1 ∧ x ∉ Z := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hcen : ∀ z ∈ Z, ∀ g : Q, Commute z g := fun z hz g =>
    (Subgroup.mem_center_iff.1 (hZc hz) g).symm
  have hc : ∀ x y z : Q, Commute ⁅x, y⁆ z := fun x y z => hcen _ (hcomm x y) z
  have hZpow : ∀ z ∈ Z, z ^ p = 1 := fun z hz => by
    have h1 := pow_card_eq_one' (G := ↥Z) (x := ⟨z, hz⟩)
    rw [hZ] at h1
    exact congrArg Subtype.val h1
  have hcp : ∀ x y : Q, ⁅x, y⁆ ^ p = 1 := fun x y => hZpow _ (hcomm x y)
  set φ := CFSG.SectionRank.powHom hc (Fact.out : p.Prime) hp hcp with hφ
  have hrange : φ.range ≤ Z := by
    rintro _ ⟨x, rfl⟩
    exact hpow x
  have h1 : Nat.card Q = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv]
  have h3 := Subgroup.card_le_of_le hrange
  rw [hZ] at h3
  obtain ⟨x, hxK, hxZ⟩ : ∃ x : Q, x ∈ φ.ker ∧ x ∉ Z := by
    by_contra hall
    push Not at hall
    have hle : φ.ker ≤ Z := fun x hx => hall x hx
    have h4 := Subgroup.card_le_of_le hle
    rw [hZ] at h4
    have h5 : p ^ 3 ≤ p * p := by rw [← hQ, h1]; exact Nat.mul_le_mul h3 h4
    have h6 : p * p < p ^ 3 := by
      calc p * p < p * p * p := by nlinarith
        _ = p ^ 3 := by ring
    omega
  exact ⟨x, hxK, hxZ⟩

theorem two_le_pRank_top_of_central_cube {Q : Type*} [Group Q] [Finite Q]
    [Fact p.Prime] (hp : p ≠ 2) {Z : Subgroup Q} (hZc : Z ≤ Subgroup.center Q)
    (hZ : Nat.card Z = p) (hQ : Nat.card Q = p ^ 3) (hcomm : ∀ x y : Q, ⁅x, y⁆ ∈ Z)
    (hpow : ∀ x : Q, x ^ p ∈ Z) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Q) := by
  obtain ⟨x, hx, hxZ⟩ := exists_pow_eq_one_not_mem_of_card_eq_cube hp hZc hZ hQ hcomm hpow
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr hall
    rw [this, Subgroup.card_bot] at hZ
    exact hp1.ne hZ
  have hZpow : z ^ p = 1 := by
    have h1 := pow_card_eq_one' (G := ↥Z) (x := ⟨z, hzZ⟩)
    rw [hZ] at h1
    exact congrArg Subtype.val h1
  exact CFSG.SectionRank.two_le_pRank_top_of_commute hZpow hx
    (Subgroup.mem_center_iff.1 (hZc hzZ) x).symm hz1 fun n hn => hxZ (hn ▸ Z.pow_mem hzZ n)

theorem two_le_pRank_comap_mk_of_central [Finite G] [Fact p.Prime] (hp : p ≠ 2)
    {N : Subgroup G} [N.Normal] (hNc : N ≤ Subgroup.center G) (hN : Nat.card N = p)
    {E : Subgroup (G ⧸ N)} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) :
    2 ≤ CFSG.Open.pRank p (E.comap (QuotientGroup.mk' N)) := by
  have := hE.1
  set π := QuotientGroup.mk' N with hπ
  set P : Subgroup G := E.comap π with hP
  have hNP : N ≤ P := fun z hz => by
    show π z ∈ E
    rw [show π z = 1 from (QuotientGroup.eq_one_iff z).mpr hz]
    exact E.one_mem
  set Z : Subgroup P := N.subgroupOf P with hZdef
  have hZc : Z ≤ Subgroup.center P := fun a ha => Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (Subgroup.mem_center_iff.1 (hNc ha) g)
  have hZcard : Nat.card Z = p := by
    rw [hZdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv, hN]
  have hPcard : Nat.card P = p ^ 3 := by
    have h1 : Nat.card P = Nat.card N * Nat.card E :=
      QuotientGroup.card_preimage_mk N (E : Set (G ⧸ N))
    rw [h1, hN, hEc]
    ring
  have hcomm : ∀ x y : P, ⁅x, y⁆ ∈ Z := by
    intro x y
    rw [hZdef, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    have h1 : (⟨π x, x.2⟩ : E) * ⟨π y, y.2⟩ = ⟨π y, y.2⟩ * ⟨π x, x.2⟩ := mul_comm' _ _
    have h2 := congrArg Subtype.val h1
    change π ((x : G) * y * (x : G)⁻¹ * (y : G)⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    change π x * π y = π y * π x at h2
    rw [h2]
    group
  have hpow : ∀ x : P, x ^ p ∈ Z := by
    intro x
    rw [hZdef, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    change π ((x : G) ^ p) = 1
    rw [map_pow]
    exact hE.2 _ x.2
  have h := two_le_pRank_top_of_central_cube hp hZc hZcard hPcard hcomm hpow
  rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h

theorem two_le_pRank_of_two_le_pRank_map_of_central [Finite G] [Fact p.Prime] (hp : p ≠ 2)
    {N : Subgroup G} [N.Normal] (hNc : N ≤ Subgroup.center G) (hN : Nat.card N = p)
    {C : Subgroup G} (hNC : N ≤ C) (h : 2 ≤ CFSG.Open.pRank p (C.map (QuotientGroup.mk' N))) :
    2 ≤ CFSG.Open.pRank p C := by
  obtain ⟨E, hEC, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h
  refine (two_le_pRank_comap_mk_of_central hp hNc hN hE hEc).trans
    (CFSG.SectionRank.pRank_mono (Fact.out : p.Prime).one_lt ?_)
  intro x hx
  obtain ⟨c, hcC, hcx⟩ := hEC hx
  have hcn : c⁻¹ * x ∈ N := QuotientGroup.eq.1 hcx
  have := C.mul_mem hcC (hNC hcn)
  rwa [mul_inv_cancel_left] at this

theorem two_le_pRank_centralizer_of_quotient [Finite G] [Fact s.Prime] [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hs : ¬ s ∣ Nat.card N)
    (hN : ¬ p ∣ Nat.card N ∨ (p ≠ 2 ∧ N ≤ Subgroup.center G ∧ Nat.card N = p))
    {E : Subgroup G} (hE : IsPGroup s E)
    (h : 2 ≤ CFSG.Open.pRank p (Subgroup.centralizer
      ((E.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)))) :
    2 ≤ CFSG.Open.pRank p (Subgroup.centralizer (E : Set G)) := by
  rw [CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := s) hs hE] at h
  rcases hN with hN | ⟨hp2, hNc, hNp⟩
  · rwa [CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal p Fact.out N hN _]
      at h
  · exact two_le_pRank_of_two_le_pRank_map_of_central hp2 hNc hNp
      (hNc.trans (Subgroup.center_le_centralizer _)) h

theorem pRank_le_pRank_map_mk_add_one [Finite G] [Fact p.Prime] {N : Subgroup G} [N.Normal]
    (hN : Nat.card N = p) (C : Subgroup G) :
    CFSG.Open.pRank p C ≤ CFSG.Open.pRank p (C.map (QuotientGroup.mk' N)) + 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, hEC, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt C
  have h1 := CFSG.PreuniquenessRankFour.Helpers.elementary_rank_le_kernel_rank_add_image_rank p hp
    (QuotientGroup.mk' N) hE _ hEc
  have h2 : pRank p (QuotientGroup.mk' N).ker ≤ 1 := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨F, hFN, -, hFc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt N
    have hd : p ^ pRank p N ∣ p ^ 1 := by
      rw [← hFc, pow_one, ← hN]
      exact Subgroup.card_dvd_of_le hFN
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hd
  have h3 : pRank p (E.map (QuotientGroup.mk' N)) ≤ pRank p (C.map (QuotientGroup.mk' N)) :=
    CFSG.SectionRank.pRank_mono hp.one_lt (Subgroup.map_mono hEC)
  omega

end CFSG.GroupTheory.CentralQuotient
