module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35Lift
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.Open.RankThreeDefs
public import CFSG.HardMathSupport.Timmesfeld.Proving.PRankCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddFixedNormalizer
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35

open CFSG.Open Subgroup CFSG.RankThree.PartOne.OutStructure
open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient centerQuotientHom)

@[expose] def K35Good (M : Type*) [Group M] : Prop :=
  ∀ A : Subgroup (MulAut M), IsElemAbelian 3 A → Nat.card A = 9 →
    (∃ α ∈ A, α ≠ 1 ∧ α ∈ Inn M) ∨ (∃ α ∈ A, α ≠ 1 ∧ FixedBlocks 3 α 4) ∨
      ∃ t : M, t ^ 2 = 1 ∧ t ≠ 1 ∧ FixedBlocks 3 (MulAut.conj t) 4

theorem K35Good.of_mulEquiv {M N : Type*} [Group M] [Group N] (e : M ≃* N) (h : K35Good N) :
    K35Good M := by
  intro A hA hA9
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  rcases h (A.map (MulAut.congr e).toMonoidHom) (CFSG.SectionRank.isElemAbelian_map hA _)
      (by rw [Subgroup.card_map_of_injective hinj, hA9]) with
    ⟨_, ⟨α, hα, rfl⟩, hα1, hinn⟩ | ⟨_, ⟨α, hα, rfl⟩, hα1, hfb⟩ | ⟨t, ht2, ht1, hfb⟩
  · refine Or.inl ⟨α, hα, fun h1 => hα1 (by rw [h1, map_one]), ?_⟩
    have hinn' : (MulAut.congr e).toMonoidHom α ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner N := hinn
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e] at hinn'
    obtain ⟨β, hβ, hβα⟩ := Subgroup.mem_map.1 hinn'
    rwa [← hinj hβα]
  · refine Or.inr (Or.inl ⟨α, hα, fun h1 => hα1 (by rw [h1, map_one]), ?_⟩)
    exact hfb.map e.symm.toMonoidHom e.symm.injective fun x => by simp [MulAut.congr_apply]
  · refine Or.inr (Or.inr ⟨e.symm t, by rw [← map_pow, ht2, map_one], fun h1 => ht1 ?_, ?_⟩)
    · simpa using congrArg e h1
    · exact hfb.map e.symm.toMonoidHom e.symm.injective fun x => by simp [MulAut.conj_apply]

theorem exists_pair_of_card_nine {G : Type*} [Group G] {A : Subgroup G} (hA : IsElemAbelian 3 A)
    (hA9 : Nat.card A = 9) : ∃ α ∈ A, α ≠ 1 ∧ ∃ β ∈ A, β ∉ zpowers α := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases A.bot_or_exists_ne_one with hbot | ⟨α, hαA, hα1⟩
  · rw [hbot, Subgroup.card_bot] at hA9
    omega
  refine ⟨α, hαA, hα1, ?_⟩
  by_contra hcon
  push Not at hcon
  have hc : Nat.card (zpowers α) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hA.2 α hαA) hα1]
  haveI : Finite (zpowers α) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have := Subgroup.card_le_of_le (show A ≤ zpowers α from hcon)
  omega

theorem mul_zpow_ne_one {G : Type*} [Group G] {α β : G} (hα3 : α ^ 3 = 1) (hβ3 : β ^ 3 = 1)
    (hα1 : α ≠ 1) (hβ : β ∉ zpowers α) (m : ℤ) : α * β ^ m ≠ 1 ∧ β * α ^ m ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨fun h => ?_, fun h => hβ (mem_zpowers_iff.2
    ⟨-m, by rw [zpow_neg, eq_inv_of_mul_eq_one_left h]⟩)⟩
  have hβ1 : β ≠ 1 := fun h1 => hβ (h1 ▸ one_mem _)
  have hαβ : zpowers α ≤ zpowers β :=
    zpowers_le.2 (mem_zpowers_iff.2 ⟨-m, by rw [zpow_neg, eq_inv_of_mul_eq_one_left h]⟩)
  have hcβ : Nat.card (zpowers β) = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime hβ3 hβ1]
  haveI : Finite (zpowers β) := Nat.finite_of_card_ne_zero (by rw [hcβ]; norm_num)
  have heq := Subgroup.eq_of_le_of_card_ge hαβ
    (by rw [hcβ, Nat.card_zpowers, orderOf_eq_prime hα3 hα1])
  exact hβ (heq ▸ mem_zpowers β)

theorem k35Good_of_outPChain {M : Type*} [Group M] (h : OutPChain 3 M) : K35Good M := by
  intro A hA hA9
  obtain ⟨α, hαA, hα1, β, hβA, hβ⟩ := exists_pair_of_card_nine hA hA9
  have hα3 := hA.2 α hαA
  have hβ3 := hA.2 β hβA
  have hαβ : α * β = β * α := by
    haveI := hA.1
    exact congrArg Subtype.val (mul_comm' (⟨α, hαA⟩ : A) ⟨β, hβA⟩)
  have hinn : ∀ γ : MulAut M, γ ^ 3 = 1 → γ ^ (3 ^ 1) ∈ Inn M := fun γ hγ => by
    rw [pow_one, hγ]
    exact (Inn M).one_mem
  rcases h.comparable hαβ (hinn α hα3) (hinn β hβ3) with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact Or.inl ⟨α * β ^ m, mul_mem hαA (zpow_mem hβA m),
      (mul_zpow_ne_one hα3 hβ3 hα1 hβ m).1, hm⟩
  · exact Or.inl ⟨β * α ^ m, mul_mem hβA (zpow_mem hαA m),
      (mul_zpow_ne_one hα3 hβ3 hα1 hβ m).2, hm⟩

theorem k35Good_of_not_nine_dvd {M : Type*} [Group M]
    (h : ¬ 9 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer M)) :
    K35Good M := by
  intro A hA hA9
  by_contra hcon
  have hinj : Function.Injective ((QuotientGroup.mk' (Inn M)).comp A.subtype) :=
    (injective_iff_map_eq_one _).2 fun α hα => by
      by_contra hα1
      exact hcon (Or.inl ⟨α, α.2, fun h1 => hα1 (Subtype.ext h1),
        (QuotientGroup.eq_one_iff _).1 hα⟩)
  have h9 : Nat.card A ∣ Nat.card (MulAut M ⧸ Inn M) := Subgroup.card_dvd_of_injective _ hinj
  rw [hA9] at h9
  exact h h9

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem exists_conj_eq_of_mem_sup_centralizer (K : Subgroup X) {e : X}
    (he : e ∈ K ⊔ centralizer (K : Set X)) : ∃ k ∈ K, ∀ y ∈ K, e * y * e⁻¹ = k * y * k⁻¹ := by
  obtain ⟨j, hj, z, hz, rfl⟩ := (mem_sup_centralizer_iff K).1 he
  refine ⟨j, hj, fun y hy => ?_⟩
  have hzy : z * y = y * z := (mem_centralizer_iff.1 hz y hy).symm
  calc j * z * y * (j * z)⁻¹ = j * (z * y) * z⁻¹ * j⁻¹ := by group
    _ = j * y * j⁻¹ := by rw [hzy]; group

omit [Finite X] in
theorem mem_sup_centralizer_of_inner (K : Subgroup X) [Group.IsPerfect K] {g : X}
    (hg : g ∈ normalizer (K : Set X))
    (h : onCenterQuotient (K.normalizerMonoidHom ⟨g, hg⟩) ∈ Inn (K ⧸ center K)) :
    g ∈ K ⊔ centralizer (K : Set X) := by
  have hα : K.normalizerMonoidHom ⟨g, hg⟩ ∈ Inn K := by
    have h2 : CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom K
        (QuotientGroup.mk (K.normalizerMonoidHom ⟨g, hg⟩)) = 1 := by
      rw [CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom,
        QuotientGroup.map_mk]
      exact (QuotientGroup.eq_one_iff _).mpr h
    exact (QuotientGroup.eq_one_iff _).mp
      (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_outer_injective K
        (h2.trans (map_one _).symm))
  obtain ⟨j, hj⟩ := hα
  rw [mem_sup_centralizer_iff]
  refine ⟨j, j.2, (j : X)⁻¹ * g, mem_centralizer_iff.2 fun y hy => ?_, by simp⟩
  have h4 := congrArg (fun f : MulAut K => ((f ⟨y, hy⟩ : K) : X)) hj
  rw [MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] at h4
  have h5 : (j : X) * y * (j : X)⁻¹ = g * y * g⁻¹ := by simpa using h4
  calc y * ((j : X)⁻¹ * g) = (j : X)⁻¹ * ((j : X) * y * (j : X)⁻¹) * g := by group
    _ = (j : X)⁻¹ * (g * y * g⁻¹) * g := by rw [h5]
    _ = (j : X)⁻¹ * g * y := by group

theorem centralizer_le_gamma {E : Subgroup X} (hE : IsElemAbelian 3 E) {e : X} (he : e ∈ E)
    (he1 : e ≠ 1) : centralizer {e} ≤ rankThreeGamma 1 3 E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : IsElemAbelian 3 (zpowers e) := ⟨inferInstance, fun x hx => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hE.2 e he, one_zpow]⟩
  have hrk : 1 ≤ CFSG.Open.pRank 3 (zpowers e) := CFSG.SectionRank.le_pRank (by norm_num) le_rfl hZ
    (by rw [Nat.card_zpowers, orderOf_eq_prime (hE.2 e he) he1, pow_one])
  refine CFSG.HardMathSupport.Timmesfeld.Proving.le_GLBCore_of_le_normalizer (zpowers_le.2 he)
    hrk ?_
  rw [← centralizer_closure, ← zpowers_eq_closure]
  exact centralizer_le_normalizer _

omit [Finite X] in
theorem onCenterQuotient_of_mem (K : Subgroup X) {y : X} (hy : y ∈ K)
    (hyN : y ∈ normalizer (K : Set X)) :
    onCenterQuotient (K.normalizerMonoidHom ⟨y, hyN⟩) =
      MulAut.conj (QuotientGroup.mk' (center K) ⟨y, hy⟩) := by
  have h1 : K.normalizerMonoidHom ⟨y, hyN⟩ = MulAut.conj ⟨y, hy⟩ :=
    MulEquiv.ext fun z => Subtype.ext (by
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
      rfl)
  change centerQuotientHom K (K.normalizerMonoidHom ⟨y, hyN⟩) = _
  rw [h1, CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_conj]

theorem exists_inner_of_k35Good (K E : Subgroup X) [K.Normal] [Group.IsPerfect K]
    (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (h23 : ∀ T : Subgroup X, T ≠ ⊥ → IsPGroup 2 T → CFSG.pRank 3 (normalizer (T : Set X)) ≤ 3)
    (hΓ : CFSG.pRank 3 (rankThreeGamma 1 3 E) ≤ 3) (hgood : K35Good (K ⧸ center K)) :
    ∃ e ∈ E, e ≠ 1 ∧ ∃ k ∈ K, ∀ y ∈ K, e * y * e⁻¹ = k * y * k⁻¹ := by
  have hN : ∀ x : X, x ∈ normalizer (K : Set X) := fun x => by
    rw [normalizer_eq_top]
    exact mem_top x
  have hc : ∀ H : Subgroup X, CFSG.pRank 3 H = CFSG.Open.pRank 3 H := fun H =>
    (CFSG.SectionRank.pRank_eq_open_pRank_top 3 H).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup H).symm
  have hinner : ∀ e ∈ E, e ≠ 1 →
      onCenterQuotient (K.normalizerMonoidHom ⟨e, hN e⟩) ∈ Inn (K ⧸ center K) →
      ∃ e ∈ E, e ≠ 1 ∧ ∃ k ∈ K, ∀ y ∈ K, e * y * e⁻¹ = k * y * k⁻¹ := fun e he he1 hinn =>
    ⟨e, he, he1, exists_conj_eq_of_mem_sup_centralizer K (mem_sup_centralizer_of_inner K _ hinn)⟩
  have hrank : ∀ y : X, FixedBlocks 3 (onCenterQuotient (K.normalizerMonoidHom ⟨y, hN y⟩)) 4 →
      4 ≤ CFSG.Open.pRank 3 (centralizer {y}) := fun y h =>
    (le_pRank_of_fixedBlocks Nat.prime_three K (hN y) h).trans
      (CFSG.SectionRank.pRank_mono (by norm_num) inf_le_right)
  let φ : E →* MulAut (K ⧸ center K) :=
    (centerQuotientHom K).comp (K.normalizerMonoidHom.comp (inclusion fun x _ => hN x))
  by_cases hinj : Function.Injective φ
  · have hEtop : IsElemAbelian 3 (⊤ : Subgroup E) := by
      haveI := hE.1
      exact ⟨⟨⟨fun a b => Subtype.ext (mul_comm' (a : E) (b : E))⟩⟩,
        fun x _ => Subtype.ext (by simpa using hE.2 x x.2)⟩
    have hA : IsElemAbelian 3 φ.range := by
      rw [MonoidHom.range_eq_map]
      exact CFSG.SectionRank.isElemAbelian_map hEtop φ
    have hA9 : Nat.card φ.range = 9 := by
      rw [← hE9]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rcases hgood φ.range hA hA9 with ⟨_, ⟨e, rfl⟩, hα1, hinn⟩ | ⟨_, ⟨e, rfl⟩, hα1, hfb⟩ |
        ⟨t, ht2, ht1, hfb⟩
    · exact hinner e e.2 (fun h => hα1 (by rw [show e = 1 from Subtype.ext h, map_one])) hinn
    · have he1 : (e : X) ≠ 1 := fun h => hα1 (by rw [show e = 1 from Subtype.ext h, map_one])
      have h4 := (hrank e hfb).trans (CFSG.SectionRank.pRank_mono (by norm_num)
        (centralizer_le_gamma hE e.2 he1))
      have := hc (rankThreeGamma 1 3 E)
      omega
    · obtain ⟨y, hyt, a, ha⟩ := CFSG.ComponentClassification.UnbalancedLayer.exists_two_power_lift
        (orderOf_eq_prime ht2 ht1)
      have hy1 : y ≠ 1 := fun h => ht1 (by rw [← hyt, h, map_one])
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one ha)
      have hfb' : FixedBlocks 3 (onCenterQuotient (K.normalizerMonoidHom ⟨y, hN y⟩)) 4 := by
        have hy : QuotientGroup.mk' (center K) ⟨(y : X), y.2⟩ = t := hyt
        rw [onCenterQuotient_of_mem K y.2 (hN y), hy]
        exact hfb
      have hT : zpowers (y : X) ≠ ⊥ := fun h => hy1 (Subtype.ext (zpowers_eq_bot.1 h))
      have hT2 : IsPGroup 2 (zpowers (y : X)) :=
        IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hk])
      have h4 := (hrank y hfb').trans (CFSG.SectionRank.pRank_mono (by norm_num)
        (show centralizer {(y : X)} ≤ normalizer ((zpowers (y : X) : Subgroup X) : Set X) by
          rw [← centralizer_closure, ← zpowers_eq_closure]
          exact centralizer_le_normalizer _))
      have := h23 _ hT hT2
      have := hc (normalizer ((zpowers (y : X) : Subgroup X) : Set X))
      omega
  · rw [injective_iff_map_eq_one] at hinj
    push Not at hinj
    obtain ⟨e, he, he1⟩ := hinj
    exact hinner e e.2 (fun h => he1 (Subtype.ext h)) (by
      change φ e ∈ _
      rw [he]
      exact one_mem _)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35
