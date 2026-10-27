module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockPerfectCoreThreeLie
import CFSG.ClassicalInvolution.Orders.Classical
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIICenter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding

theorem isSolvable_of_card_dvd_two_pow_mul_prime_pow {X : Type*} [Group X] [Finite X] {a b p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : Nat.card X ∣ 2 ^ a * p ^ b) : Group.IsSolvable X := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hk₂
  have : Fintype X := Fintype.ofFinite X
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two hp
    (Ne.symm hp2) (by rw [← Nat.card_eq_fintype_card, ← hk])

theorem perfectCoreThree_of_card_quotient {P Q : Type*} [Group P] [Finite P] [Group Q] [Finite Q]
    (g : P →* Q) (hg : ∀ x ∈ g.ker, x ∈ Subgroup.center P) {a b k p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hQ : Nat.card Q ∣ 2 ^ a * 3 ^ k * p ^ b) : PerfectCoreThree P := by
  intro j hj
  set D := derivedSeries P j with hD
  by_cases h3 : 3 ∣ Nat.card D
  · exact Or.inr h3
  left
  have hDD : ⁅D, D⁆ = D := by rw [hD, ← derivedSeries_succ]; exact hj
  haveI hperf : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr hDD
  let f : ↥D →* Q := g.comp D.subtype
  have hRD : Nat.card f.range ∣ Nat.card D := Subgroup.card_range_dvd f
  have hRQ : Nat.card f.range ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card _
  have h3R : ¬ 3 ∣ Nat.card f.range := fun h => h3 (h.trans hRD)
  have hcop : Nat.Coprime (Nat.card f.range) (3 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3R).symm
  have hR2p : Nat.card f.range ∣ 2 ^ a * p ^ b := by
    have h1 : Nat.card f.range ∣ (2 ^ a * p ^ b) * 3 ^ k := by
      have := hRQ.trans hQ
      rwa [show 2 ^ a * 3 ^ k * p ^ b = (2 ^ a * p ^ b) * 3 ^ k by ring] at this
    exact hcop.dvd_of_dvd_mul_right h1
  haveI hsolv : Group.IsSolvable f.range := isSolvable_of_card_dvd_two_pow_mul_prime_pow hp hp2 hR2p
  haveI hRperf : Group.IsPerfect f.range :=
    Group.IsPerfect.ofSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  have hRsub : Subsingleton f.range := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable f.range hsolv
  have hDc : D ≤ Subgroup.center P := by
    intro x hx
    apply hg
    have : (⟨g x, ⟨⟨x, hx⟩, rfl⟩⟩ : f.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  have hcomm : ⁅D, D⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2
    (hDc.trans (Subgroup.center_le_centralizer (D : Set P)))
  rw [← hDD, hcomm]

theorem perfectCoreThree_of_small_card {Y : Type*} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hPL : P ≤ L)
    (h : Nat.card (↥L ⧸ Subgroup.center ↥L) = 60 ∨ Nat.card (↥L ⧸ Subgroup.center ↥L) = 360 ∨
      Nat.card (↥L ⧸ Subgroup.center ↥L) = 168 ∨ Nat.card (↥L ⧸ Subgroup.center ↥L) = 6048) :
    PerfectCoreThree ↥P := by
  have hg : ∀ x ∈ ((QuotientGroup.mk' (Subgroup.center ↥L)).comp
      (Subgroup.inclusion hPL)).ker, x ∈ Subgroup.center ↥P := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subgroup.inclusion_injective hPL
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hx (Subgroup.inclusion hPL y)
  rcases h with h | h | h | h
  · exact perfectCoreThree_of_card_quotient _ hg (a := 2) (b := 1) (k := 1) (p := 5)
      (by norm_num) (by norm_num) (h ▸ by norm_num)
  · exact perfectCoreThree_of_card_quotient _ hg (a := 3) (b := 1) (k := 2) (p := 5)
      (by norm_num) (by norm_num) (h ▸ by norm_num)
  · exact perfectCoreThree_of_card_quotient _ hg (a := 3) (b := 1) (k := 1) (p := 7)
      (by norm_num) (by norm_num) (h ▸ by norm_num)
  · exact perfectCoreThree_of_card_quotient _ hg (a := 5) (b := 1) (k := 3) (p := 7)
      (by norm_num) (by norm_num) (h ▸ by norm_num)

theorem card_small_cases_or_alt_eight {X : Type} [Group X] (hS : IsSmallTwoOrG2 X) :
    (Nat.card X = 60 ∨ Nat.card X = 360 ∨ Nat.card X = 168 ∨ Nat.card X = 6048) ∨
      Nonempty (X ≃* alternatingGroup (Fin 8)) := by
  rcases hS with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨d, hv⟩, ⟨q, hq7, hdq⟩ | ⟨q, hq3, hdq⟩, ⟨e⟩⟩
  · rcases hn with rfl | rfl | rfl
    · left
      left
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    · left
      right
      left
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    · exact Or.inr ⟨e⟩
  · left
    right
    right
    left
    simp only at hdq
    subst hdq
    obtain ⟨hp, hf⟩ : q.p = 7 ∧ q.exponent = 1 := by
      rw [TauCeti.PrimePower.card_def] at hq7
      exact (Nat.Prime.pow_eq_iff (by norm_num)).1 hq7
    have hc := statedClassicalModel_of_typeA hv e
    rw [hp, hf] at hc
    have := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (by norm_num) hc).1 rfl
    rw [this]
    unfold ordA
    decide
  · left
    right
    right
    right
    simp only at hdq
    subst hdq
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := by
      rw [TauCeti.PrimePower.card_def] at hq3
      exact (Nat.Prime.pow_eq_iff (by norm_num)).1 hq3
    have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    rw [hp, hf] at hc
    have := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (by norm_num) hc).2.1 rfl
    rw [this]
    unfold ordTwistedA
    decide

theorem perfectCoreThree_of_alt_eight
    (hGA : GriessAllModelsStatement) {Y : Type} [Group Y]
    [Finite Y] {L P : Subgroup Y} (hCP : CompParab L P)
    (e8 : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) : PerfectCoreThree ↥P := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      ((CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).2 ⟨e8⟩)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  obtain ⟨ρ, hρs, -, hρ⟩ :=
    kFactCoverLinear_of_griess hGA Y L hCP.comp hCP.odd 4 K (by norm_num) e
  obtain ⟨σ, -, I, hσs, -, -, hcomap, -, -⟩ :=
    exists_comap_eq_flagStabilizer hCP.odd (by norm_num) e hρs hρ hCP.parab
  have hQ : HasLeviBlocks ↥((P.subgroupOf L).comap σ) (linBlockOrders K) :=
    hcomap ▸ hasLeviBlocks_flagStabilizer (by norm_num) I
  exact perfectCoreThree_of_cover hCP.parab.1 σ hσs hQ fun N hN _ =>
    three_dvd_of_mem_linBlockOrders hK hN

theorem kFactCompParabPerfectCoreThreeOn_small
    (hGA : GriessAllModelsStatement) :
    KFactCompParabPerfectCoreThreeOn IsSmallTwoOrG2 := by
  intro Y _ _ L P hCP hS
  rcases card_small_cases_or_alt_eight hS with h | ⟨⟨e8⟩⟩
  · exact perfectCoreThree_of_small_card hCP.parab.1 h
  · exact perfectCoreThree_of_alt_eight hGA hCP e8

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
