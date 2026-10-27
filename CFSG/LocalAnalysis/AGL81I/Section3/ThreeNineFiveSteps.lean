module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineFiveFamilies
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSetup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwo
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm47Statement
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoJ3
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoONan
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Induction
public import CFSG.RankThree.PartOne.Mult.Sec68
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.OrderCheckF
public import CFSG.Sporadic.Fi24
public import CFSG.Sporadic.Recognition.HNMultiplier
public import CFSG.Sporadic.Recognition.LyonsAmalgamModelYAut
public import CFSG.Sporadic.Recognition.LyonsFinalDist2
public import CFSG.Sporadic.Suz

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaIn gammaOver)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem normalizer_inf_le_gammaIn {G : Type} [Group G] [Finite G] {k p : ℕ}
    {F R T : Subgroup G} (hp : 1 < p) (hFR : F ≤ R) (hRT : R ≤ T)
    (hk : k ≤ CFSG.Open.pRank p F) :
    Subgroup.normalizer (F : Set G) ⊓ T ≤ gammaIn k p R T := by
  rintro n ⟨hnN, hnT⟩
  have hFT : F ≤ T := hFR.trans hRT
  have hrank : k ≤ CFSG.Open.pRank p (F.subgroupOf T) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) (F.subgroupOf T),
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp (Subgroup.subgroupOfEquivOfLe hFT),
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) F]
    exact hk
  have hmem : (⟨n, hnT⟩ : T) ∈
      Subgroup.normalizer ((F.subgroupOf T : Subgroup T) : Set T) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hnN h
  have hle : F.subgroupOf T ≤ R.subgroupOf T := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hFR (Subgroup.mem_subgroupOf.mp hx))
  exact ⟨⟨n, hnT⟩, CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le k p _ _ hle hrank hmem,
    rfl⟩

theorem one_le_pRank_of_isPGroup {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {F : Subgroup G} (hF : IsPGroup p F) (hF1 : F ≠ ⊥) : 1 ≤ CFSG.Open.pRank p F := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card F :=
    hF.card_eq_or_dvd.resolve_left fun h => hF1 (Subgroup.card_eq_one.mp h)
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) F]
  exact CFSG.one_le_pRank_of_dvd_card hp hdvd

namespace ThreeNineHyp

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {p d : ℕ}

theorem gammaInE (h : ThreeNineHyp K E D X₁ p d) : gammaIn 1 p E (K ⊔ D) ≤ X₁ :=
  (gammaIn_le_gammaOver h.prime.one_lt E (K ⊔ D)).trans h.gammaE

theorem isPGroup_D (h : ThreeNineHyp K E D X₁ p d) : IsPGroup d D := by
  have : Fact d.Prime := ⟨h.d_prime⟩
  exact h.sylow.isPGroup

theorem normalizer_inf_le_of_le_D (h : ThreeNineHyp K E D X₁ p d) {F : Subgroup X}
    (hFD : F ≤ D) (hF1 : F ≠ ⊥) : Subgroup.normalizer (F : Set X) ⊓ (K ⊔ D) ≤ X₁ :=
  (normalizer_inf_le_gammaIn h.d_prime.one_lt hFD le_sup_right
    (one_le_pRank_of_isPGroup h.d_prime (h.isPGroup_D.to_le hFD) hF1)).trans h.gammaD

theorem D_le (h : ThreeNineHyp K E D X₁ p d) : D ≤ X₁ :=
  fun x hx => h.normalizer_inf_le_of_le_D le_rfl h.D_ne_bot
    ⟨Subgroup.le_normalizer hx, (le_sup_right : D ≤ K ⊔ D) hx⟩

theorem not_K_le (h : ThreeNineHyp K E D X₁ p d) : ¬ K ≤ X₁ := fun hK =>
  (ne_of_lt h.lt) (le_antisymm h.lt.le (sup_le hK h.D_le))

theorem not_le_gammaOver (h : ThreeNineHyp K E D X₁ p d) : ¬ K ≤ gammaOver 1 p E K :=
  threeNine_not_le_gammaOver K E D X₁ p d h.prime h.d_prime h.sylow h.D_ne_bot h.lt h.gammaE
    h.gammaD

theorem mem_of_commute_E (h : ThreeNineHyp K E D X₁ p d) {x c : X} (hxE : x ∈ E)
    (hx1 : x ≠ 1) (hc : c ∈ K ⊔ D) (hxc : x * c = c * x) : c ∈ X₁ :=
  h.gammaE (mem_gammaOver_of_commute h.prime hxE hx1 (h.elem.2 x hxE) hc hxc)

theorem E_faithful (h : ThreeNineHyp K E D X₁ p d) {x : X} (hxE : x ∈ E)
    (hxc : ∀ c ∈ K, x * c = c * x) : x = 1 := by
  by_contra hx1
  exact h.not_le_gammaOver fun c hcK =>
    mem_gammaOver_of_commute h.prime hxE hx1 (h.elem.2 x hxE) hcK (hxc c hcK)

theorem mem_of_commute_D (h : ThreeNineHyp K E D X₁ p d) {g c : X} (hgD : g ∈ D)
    (hg1 : g ≠ 1) (hc : c ∈ K ⊔ D) (hgc : g * c = c * g) : c ∈ X₁ := by
  refine h.normalizer_inf_le_of_le_D ((Subgroup.zpowers_le).mpr hgD) ?_ ⟨?_, hc⟩
  · exact fun hbot => hg1 ((Subgroup.zpowers_eq_bot).mp hbot)
  · exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr (by
        rintro _ ⟨n, rfl⟩
        exact (Commute.zpow_left (show Commute g c from hgc) n).eq))

theorem D_faithful (h : ThreeNineHyp K E D X₁ p d) :
    D ⊓ Subgroup.centralizer (K : Set X) = ⊥ :=
  threeNine_D_faithful X K E D X₁ p d h.prime h.ne_two h.quasisimple h.core h.kgroup h.normal
    h.one_lt_rank h.rank_le h.elem h.card_E h.d_prime h.d_ne_two h.d_ne h.sylow h.D_ne_bot h.lt
    h.gammaInE h.gammaD h.normQ

theorem inf_K_le (h : ThreeNineHyp K E D X₁ p d) {Q : Subgroup X} (hQ : IsPGroup p Q)
    (hEQ : E ≤ Q) : Q ⊓ K ≤ X₁ :=
  fun x hx => h.normQ Q hQ hEQ ⟨Subgroup.le_normalizer hx.1, (le_sup_left : K ≤ K ⊔ D) hx.2⟩

theorem D_le_K_of_inner (h : ThreeNineHyp K E D X₁ p d) (hZ : Subgroup.center ↥K = ⊥)
    (hinn : ∀ x ∈ D, ∃ k ∈ K, ∀ c ∈ K, x * c * x⁻¹ = k * c * k⁻¹) : D ≤ K := by
  have : Fact d.Prime := ⟨h.d_prime⟩
  have : K.Normal := h.normal
  intro x hxD
  obtain ⟨k, hkK, hk⟩ := hinn x hxD
  set C : Subgroup X := Subgroup.centralizer (K : Set X)
  have hyC : k⁻¹ * x ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have h1 := hk c hc
    calc c * (k⁻¹ * x) = k⁻¹ * (k * c * k⁻¹) * x := by group
      _ = k⁻¹ * (x * c * x⁻¹) * x := by rw [h1]
      _ = k⁻¹ * x * c := by group
  obtain ⟨a, ha⟩ := h.isPGroup_D ⟨x, hxD⟩
  have hxa : x ^ d ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hcomm : Commute k (k⁻¹ * x) := Subgroup.mem_centralizer_iff.mp hyC k hkK
  have hsplit : x = k * (k⁻¹ * x) := by group
  have hpow : k ^ d ^ a * (k⁻¹ * x) ^ d ^ a = 1 := by
    rw [← hcomm.mul_pow, ← hsplit, hxa]
  have hkC : k ^ d ^ a ∈ C := by
    have : k ^ d ^ a = ((k⁻¹ * x) ^ d ^ a)⁻¹ := eq_inv_of_mul_eq_one_left hpow
    rw [this]
    exact C.inv_mem (C.pow_mem hyC _)
  have hk1 : k ^ d ^ a = 1 := by
    have hmem : (⟨k ^ d ^ a, K.pow_mem hkK _⟩ : K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hkC c c.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hy1 : (k⁻¹ * x) ^ d ^ a = 1 := by
    rw [hk1, one_mul] at hpow
    exact hpow
  have hsylC : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ C) C :=
    h.sylow.inf_of_le_normalizer le_top (by
      rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : C.Normal)])
  have hcardC : ¬ d ∣ Nat.card C := by
    intro hdvd
    have hc := hsylC.card_eq
    rw [h.D_faithful, Subgroup.card_bot] at hc
    have hpos : 0 < (Nat.card C).factorization d :=
      (Nat.Prime.factorization_pos_of_dvd h.d_prime Nat.card_pos.ne' hdvd)
    have : 1 < d ^ (Nat.card C).factorization d :=
      Nat.one_lt_pow hpos.ne' h.d_prime.one_lt
    omega
  have hord : orderOf (⟨k⁻¹ * x, hyC⟩ : C) ∣ d ^ a :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hy1))
  obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow h.d_prime).1 hord
  have hy : k⁻¹ * x = 1 := by
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [pow_zero, orderOf_eq_one_iff] at hio
      exact congrArg Subtype.val hio
    · exfalso
      apply hcardC
      have hdo : d ∣ orderOf (⟨k⁻¹ * x, hyC⟩ : C) := by
        rw [hio]
        exact dvd_pow_self d hipos.ne'
      exact hdo.trans (orderOf_dvd_natCard _)
  have hxk : x = k := by
    calc x = k * (k⁻¹ * x) := hsplit
      _ = k := by rw [hy, mul_one]
  rw [hxk]
  exact hkK

theorem D_le_K_of_not_dvd (h : ThreeNineHyp K E D X₁ p d) (hZ : Subgroup.center ↥K = ⊥)
    (hout : ¬ d ∣ Nat.card (Outer ↥K)) : D ≤ K := by
  have : K.Normal := h.normal
  refine h.D_le_K_of_inner hZ fun x hxD => ?_
  have : Fact d.Prime := ⟨h.d_prime⟩
  obtain ⟨a, ha⟩ := h.isPGroup_D ⟨x, hxD⟩
  have hxa : x ^ d ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  set α : MulAut ↥K := MulAut.conjNormal x
  have hα : α ^ d ^ a = 1 := by
    rw [← map_pow, hxa, map_one]
  set o : Outer ↥K := QuotientGroup.mk α
  have ho : o ^ d ^ a = 1 := by
    rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have ho1 : o = 1 := by
    have hdvd : orderOf o ∣ d ^ a := orderOf_dvd_of_pow_eq_one ho
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow h.d_prime).1 hdvd
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [pow_zero] at hi
      exact orderOf_eq_one_iff.mp hi
    · exfalso
      apply hout
      have : d ∣ orderOf o := by
        rw [hi]
        exact dvd_pow_self d hipos.ne'
      exact this.trans (orderOf_dvd_natCard o)
  obtain ⟨b, hbk⟩ := (QuotientGroup.eq_one_iff α).mp ho1
  refine ⟨b, b.2, fun c hc => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨c, hc⟩ : ↥K) : X)) hbk
  simp only [MulAut.conj_apply, α, MulAut.conjNormal_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h1
  exact h1.symm

end ThreeNineHyp

end CFSG.LocalAnalysis.AGL81I.Section3
