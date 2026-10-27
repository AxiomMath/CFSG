module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.T3Lift
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.PGroup.RankTwoCommute
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open CFSG.GH74.GLS.Stage2.Bender.Thm2.T3

@[expose] def HasRankTwoPair {G : Type*} [Group G] (H : Subgroup G) (ℓ : ℕ) : Prop :=
  ∃ x ∈ H, ∃ y ∈ H, orderOf x = ℓ ∧ orderOf y = ℓ ∧ Commute x y ∧ y ∉ Subgroup.zpowers x

theorem two_le_pRank_of_hasRankTwoPair {G : Type*} [Group G] [Finite G] {ℓ : ℕ} [Fact ℓ.Prime]
    {H : Subgroup G} (h : HasRankTwoPair H ℓ) : 2 ≤ CFSG.Open.pRank ℓ H := by
  obtain ⟨x, hx, y, hy, hxo, hyo, hc, hyz⟩ := h
  exact CFSG.GroupTheory.two_le_pRank_of_commute hx hy hxo hyo hc hyz

theorem HasRankTwoPair.of_map {G G' : Type*} [Group G] [Group G'] (d : G →* G')
    (hd : Function.Injective d) {H : Subgroup G} {ℓ : ℕ} (h : HasRankTwoPair (H.map d) ℓ) :
    HasRankTwoPair H ℓ := by
  obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxo, hyo, hc, hyz⟩ := h
  refine ⟨x, hx, y, hy, ?_, ?_, ?_, ?_⟩
  · rw [← orderOf_injective d hd x]; exact hxo
  · rw [← orderOf_injective d hd y]; exact hyo
  · exact hd (by simpa using hc.eq)
  · intro hmem
    apply hyz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by simp⟩

theorem mulAutConj_eq_one_iff_mem_center {G : Type*} [Group G] (g : G) :
    (MulAut.conj g : MulAut G) = 1 ↔ g ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h x
    have := DFunLike.congr_fun h x
    change g * x * g⁻¹ = x at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · intro h
    refine MulEquiv.ext fun x => ?_
    change g * x * g⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact (h x).symm

theorem hasRankTwoPair_of_central_pair {G : Type*} [Group G] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (a b : G)
    (ha : a ^ ℓ ∈ Subgroup.center G) (hb : b ^ ℓ ∈ Subgroup.center G)
    (hab : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center G) (ha' : a ∉ Subgroup.center G)
    (hb' : ∀ m : ℕ, b⁻¹ * a ^ m ∉ Subgroup.center G) {J : Subgroup (MulAut G)}
    (hJ : (MulAut.conj : G →* MulAut G).range ≤ J) : HasRankTwoPair J ℓ := by
  have hb1 : b ∉ Subgroup.center G := by
    intro h
    exact hb' 0 (by simpa using Subgroup.inv_mem _ h)
  have hao : orderOf (MulAut.conj a : MulAut G) = ℓ := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]; exact (mulAutConj_eq_one_iff_mem_center _).mpr ha
    · exact fun h => ha' ((mulAutConj_eq_one_iff_mem_center _).mp h)
  have hbo : orderOf (MulAut.conj b : MulAut G) = ℓ := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]; exact (mulAutConj_eq_one_iff_mem_center _).mpr hb
    · exact fun h => hb1 ((mulAutConj_eq_one_iff_mem_center _).mp h)
  refine ⟨MulAut.conj a, hJ ⟨a, rfl⟩, MulAut.conj b, hJ ⟨b, rfl⟩, hao, hbo, ?_, ?_⟩
  · have hz : ∀ g, g * (a * b * a⁻¹ * b⁻¹) = (a * b * a⁻¹ * b⁻¹) * g :=
      Subgroup.mem_center_iff.mp hab
    refine MulEquiv.ext fun x => ?_
    change a * (b * x * b⁻¹) * a⁻¹ = b * (a * x * a⁻¹) * b⁻¹
    have h1 := hz (b * a * x * a⁻¹ * b⁻¹)
    calc a * (b * x * b⁻¹) * a⁻¹
        = (a * b * a⁻¹ * b⁻¹) * (b * a * x * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹)⁻¹ := by
          group
      _ = b * (a * x * a⁻¹) * b⁻¹ := by
          rw [← h1]; group
  · intro hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hm' : (MulAut.conj a : MulAut G) ^ (m % (ℓ : ℤ)).toNat = MulAut.conj b := by
      rw [← hm, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hℓ.out.ne_zero))]
      have := zpow_mod_orderOf (MulAut.conj a : MulAut G) m
      rwa [hao] at this
    apply hb' (m % (ℓ : ℤ)).toNat
    rw [← mulAutConj_eq_one_iff_mem_center, map_mul, map_inv, map_pow, hm', inv_mul_cancel]

theorem exists_conj_mem_sup_zpowers_of_quotient {G : Type} [Group G] [Finite G] (I D : Subgroup G)
    [I.Normal] [D.Normal] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hD : ¬ ℓ ∣ Nat.card (D.map (QuotientGroup.mk' I))) {f α : G}
    (hf : orderOf (f : G ⧸ I) = ℓ) (hα : orderOf (α : G ⧸ I) = ℓ) (hfα : α * f⁻¹ ∈ D) :
    ∃ γ : G, γ * f * γ⁻¹ ∈ I ⊔ Subgroup.zpowers α := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set N : Subgroup (G ⧸ I) := D.map (QuotientGroup.mk' I) with hN
  have : N.Normal := Subgroup.Normal.map ‹D.Normal› _ (QuotientGroup.mk'_surjective I)
  have hfN : ((f : G ⧸ I)) ∉ N := by
    intro hmem
    apply hD
    have := Subgroup.orderOf_dvd_natCard N hmem
    rwa [hf] at this
  have hx : orderOf ((((f : G ⧸ I)) : (G ⧸ I) ⧸ N)) = ℓ := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, ← hf, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h1
      exact hfN ((QuotientGroup.eq_one_iff _).mp h1)
  have hcard := card_comap_zpowers_quotient N hx
  set B := (Subgroup.zpowers ((((f : G ⧸ I)) : (G ⧸ I) ⧸ N))).comap (QuotientGroup.mk' N) with hB
  have hfB : ((f : G ⧸ I)) ∈ B := by
    rw [hB, Subgroup.mem_comap]
    exact Subgroup.mem_zpowers _
  have hαB : ((α : G ⧸ I)) ∈ B := by
    rw [hB, Subgroup.mem_comap]
    have h1 : ((α : G ⧸ I)) * ((f : G ⧸ I))⁻¹ ∈ N := ⟨α * f⁻¹, hfα, by simp⟩
    have h5 : ((α : G ⧸ I))⁻¹ * (f : G ⧸ I) ∈ N := by
      have h6 := (inferInstance : N.Normal).conj_mem _ (N.inv_mem h1) ((α : G ⧸ I))⁻¹
      have h7 : ((α : G ⧸ I))⁻¹ * ((α : G ⧸ I) * (f : G ⧸ I)⁻¹)⁻¹ * ((α : G ⧸ I))⁻¹⁻¹ =
          ((α : G ⧸ I))⁻¹ * (f : G ⧸ I) := by group
      rwa [h7] at h6
    have h2 : (((α : G ⧸ I) : (G ⧸ I) ⧸ N)) = (((f : G ⧸ I) : (G ⧸ I) ⧸ N)) :=
      QuotientGroup.eq.mpr h5
    show (((α : G ⧸ I) : (G ⧸ I) ⧸ N)) ∈ _
    rw [h2]
    exact Subgroup.mem_zpowers _
  obtain ⟨g, k, hgk⟩ := exists_conj_mem_zpowers_of_card hℓ hcard hD
    (a := (⟨(f : G ⧸ I), hfB⟩ : ↥B)) (b := (⟨(α : G ⧸ I), hαB⟩ : ↥B))
    (by rw [Subgroup.orderOf_mk, hf]) (by rw [Subgroup.orderOf_mk, hα])
  have hgk' : ((g : ↥B) : G ⧸ I) * (f : G ⧸ I) * ((g : ↥B) : G ⧸ I)⁻¹ = (α : G ⧸ I) ^ k := by
    have := congrArg Subtype.val hgk
    simpa using this
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_surjective ((g : ↥B) : G ⧸ I)
  refine ⟨γ, ?_⟩
  have h3 : ((γ * f * γ⁻¹ : G) : G ⧸ I) = ((α ^ k : G) : G ⧸ I) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hγ, hgk',
      QuotientGroup.mk_zpow]
  rw [QuotientGroup.eq] at h3
  have h4 : (α ^ k) * ((γ * f * γ⁻¹)⁻¹ * α ^ k)⁻¹ = γ * f * γ⁻¹ := by group
  rw [← h4]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers α) _))
    (Subgroup.mem_sup_left (Subgroup.inv_mem _ h3))

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H
