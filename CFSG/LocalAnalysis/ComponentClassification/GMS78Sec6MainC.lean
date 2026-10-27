module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6Main
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Facts
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Push29Defs
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6Local

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

abbrev oddQuotImageC (K X : Subgroup G) :
    Subgroup (↥(centralizer (K : Set G)) ⧸
      standardComponentOddCore ↥(centralizer (K : Set G))) :=
  (X.subgroupOf (centralizer (K : Set G))).map (QuotientGroup.mk' _)

abbrev u3G₁Bar (K : Subgroup G) : Type :=
  ↥(centralizer (K : Set G)) ⧸ standardComponentOddCore ↥(centralizer (K : Set G))

abbrev u3X₀CentralizerC (L K : Subgroup G) : Subgroup (u3G₁Bar K) :=
  centralizer (oddQuotImageC K (u3X₀ L K) : Set (u3G₁Bar K))

@[expose] def GMS61InductionC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T K : Subgroup G) (f : ℕ),
    2 ≤ f → Nonempty (rankTwoQuot L ≃* PSU3 2 f) → Sec3 G L T → K ≤ L → Odd (Nat.card K) →
    (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G) →
    standardComponentIsStandard (oddQuotImageC K (u3X₀ L K)) ∧
      ¬ (oddQuotImageC K (u3X₀ L K)).Normal

@[expose] def GMS61QuasisimpleC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T K : Subgroup G) (f : ℕ),
    2 ≤ f → Nonempty (rankTwoQuot L ≃* PSU3 2 f) → Sec3 G L T → K ≤ L → Odd (Nat.card K) →
    (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G) →
    Open.IsQuasisimple (oddQuotImageC K (u3X₀ L K))

@[expose] def GMS61TightC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T K : Subgroup G) (f : ℕ),
    2 ≤ f → Nonempty (rankTwoQuot L ≃* PSU3 2 f) → Sec3 G L T → K ≤ L → Odd (Nat.card K) →
    (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G) →
    (∀ g : u3G₁Bar K, g ∉ normalizer (u3X₀CentralizerC L K : Set (u3G₁Bar K)) →
      Odd (Nat.card (u3X₀CentralizerC L K ⊓
        (u3X₀CentralizerC L K).map (MulAut.conj g).toMonoidHom : Subgroup (u3G₁Bar K)))) ∧
    normalizer (u3X₀CentralizerC L K : Set (u3G₁Bar K)) =
      normalizer (oddQuotImageC K (u3X₀ L K) : Set (u3G₁Bar K))

@[expose] def GMS61NotNormalC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T K : Subgroup G) (f : ℕ),
    2 ≤ f → Nonempty (rankTwoQuot L ≃* PSU3 2 f) → Sec3 G L T → K ≤ L → Odd (Nat.card K) →
    (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G) →
    ¬ (oddQuotImageC K (u3X₀ L K)).Normal

@[expose] def GMS61CaseOneC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T K : Subgroup G) (f : ℕ),
    2 ≤ f → Nonempty (rankTwoQuot L ≃* PSU3 2 f) → Sec3 G L T → K ≤ L → Odd (Nat.card K) →
    (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G) →
    ∀ g : u3G₁Bar K,
      ⁅oddQuotImageC K (u3X₀ L K), (oddQuotImageC K (u3X₀ L K)).map (MulAut.conj g).toMonoidHom⁆ ≠
        ⊥

namespace Sec3

variable {L T : Subgroup G}

theorem exists_four_le_centralizer_oddQuotImageC (h3 : Sec3 G L T) {K : Subgroup G}
    (hKL : K ≤ L) :
    ∃ E : Subgroup (u3G₁Bar K), E ≤ u3X₀CentralizerC L K ∧ IsElemAbelian 2 E ∧
      Nat.card E = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hET, hE, hE4⟩ := h3.exists_four_le
  set G₁ := centralizer (K : Set G)
  have hEG₁ : E ≤ G₁ := fun x hx => mem_centralizer_iff.mpr fun k hk =>
    (mem_centralizer_iff.mp (mem_inf.mp (hET hx)).2 k (hKL hk))
  set π := QuotientGroup.mk' (standardComponentOddCore G₁)
  set E' : Subgroup G₁ := E.subgroupOf G₁
  have hE'4 : Nat.card E' = 4 := by
    rw [← hE4]
    exact Nat.card_congr (subgroupOfEquivOfLe hEG₁).toEquiv
  have hE'el : IsElemAbelian 2 E' := by
    refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · show ((x : G₁) : G) * ((y : G₁) : G) = ((y : G₁) : G) * ((x : G₁) : G)
      exact congrArg (fun z : E => (z : G)) (hE.1.is_comm.comm ⟨_, x.2⟩ ⟨_, y.2⟩)
    · exact hE.2 _ hx
  set ι : E' →* (↥G₁ ⧸ standardComponentOddCore ↥G₁) := π.comp E'.subtype
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : (x : G₁) ∈ standardComponentOddCore G₁ := by
      rw [← QuotientGroup.eq_one_iff]
      exact hx
    have hbot : E' ⊓ standardComponentOddCore G₁ = ⊥ := by
      have h2 : IsPGroup 2 E' := IsPGroup.of_card (n := 2) (by rw [hE'4]; norm_num)
      exact AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ _ h2.to_inf_left
        odd_card_standardComponentOddCore' inf_le_right
    have h3' : (x : G₁) ∈ E' ⊓ standardComponentOddCore G₁ := mem_inf.mpr ⟨x.2, hxO⟩
    rw [hbot, mem_bot] at h3'
    exact Subtype.ext h3'
  have hĒ : ι.range = E'.map π := by
    rw [MonoidHom.range_comp, range_subtype]
  refine ⟨E'.map π, ?_, isElemAbelian_map π hE'el, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hyL : (y : G) ∈ L := (inf_le_left : L ⊓ centralizer (K : Set G) ≤ L)
      ((commutator_le.mpr fun a ha b hb => ?_) hy)
    · exact (mem_centralizer_iff.mp (mem_inf.mp (hET hx)).2 (y : G) hyL)
    · exact mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem (mem_inf.mp ha).1 (mem_inf.mp hb).1)
        (inv_mem (mem_inf.mp ha).1)) (inv_mem (mem_inf.mp hb).1),
        mul_mem (mul_mem (mul_mem (mem_inf.mp ha).2 (mem_inf.mp hb).2)
        (inv_mem (mem_inf.mp ha).2)) (inv_mem (mem_inf.mp hb).2)⟩
  · rw [← hĒ, ← hE'4]
    exact (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm

theorem even_card_centralizer_oddQuotImageC (h3 : Sec3 G L T) {K : Subgroup G} (hKL : K ≤ L) :
    Even (Nat.card (u3X₀CentralizerC L K)) := by
  obtain ⟨E, hEC, -, hE4⟩ := h3.exists_four_le_centralizer_oddQuotImageC hKL
  have h := Subgroup.card_dvd_of_le hEC
  rw [hE4] at h
  exact even_iff_two_dvd.mpr ((show (2 : ℕ) ∣ 4 by norm_num).trans h)

end Sec3

theorem gms61InductionC_of (hq : GMS61QuasisimpleC) (ht : GMS61TightC) (hn : GMS61NotNormalC)
    (hc : GMS61CaseOneC) : GMS61InductionC := by
  intro G _ _ L T K f hf he h3 hKL hKo hKH
  obtain ⟨htight, hnorm⟩ := ht G L T K f hf he h3 hKL hKo hKH
  exact ⟨⟨hq G L T K f hf he h3 hKL hKo hKH, h3.even_card_centralizer_oddQuotImageC hKL, htight,
    hnorm, hc G L T K f hf he h3 hKL hKo hKH⟩, hn G L T K f hf he h3 hKL hKo hKH⟩

theorem false_of_u3MinCounterC (h61 : GMS61InductionC) (hL2 : L2Res) {L : Subgroup G} {f : ℕ}
    (hM : U3MinCounter G L f) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (normalizer (L : Set G))
  have h3 : Sec3 G L T := ⟨hM.hyp, hT⟩
  obtain ⟨e⟩ := hM.iso
  have hf2 : 2 ≤ f := le_trans (by norm_num) hM.three_le
  have hZ : Odd (Nat.card (center L)) :=
    odd_card_center_of_psu3 hM.hyp.standard.1.1 hf2 e
  obtain ⟨K, hKL, hKo, hKH, F, _, _, _, hF, ⟨eX⟩⟩ := exists_u3TorusK hZ hf2 e h3.isSylowOf_T₁
  obtain ⟨hstd, hnn⟩ := h61 G L T K f hf2 hM.iso h3 hKL hKo hKH
  set G₁ := centralizer (K : Set G)
  set X₀ := u3X₀ L K
  set X₀' : Subgroup G₁ := X₀.subgroupOf G₁
  have hX₀G₁ : X₀ ≤ G₁ := by
    refine (commutator_le).mpr fun x hx y hy => ?_
    exact mul_mem (mul_mem (mul_mem (mem_inf.mp hx).2 (mem_inf.mp hy).2)
      (inv_mem (mem_inf.mp hx).2)) (inv_mem (mem_inf.mp hy).2)
  have eX' : rankTwoQuot X₀' ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (quotCenterCongr (subgroupOfEquivOfLe hX₀G₁)).trans eX
  have hFc : 4 ≤ Nat.card F := by
    rw [hF]
    exact le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hf2)
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have : Fintype F := Fintype.ofFinite F
    have hc : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact hFc
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hc
    exact ⟨s, hs⟩
  have hsimp : IsSimpleGroup (rankTwoQuot X₀') := by
    have := u3_isSimpleGroup_SL2 F h4
    exact eX'.isSimpleGroup
  have hcen : center (rankTwoQuot X₀') = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : eX' z ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨w, rfl⟩ := eX'.surjective y
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) w]
    rw [u3_center_SL2_eq_bot, mem_bot] at h1
    rw [mem_bot]
    exact eX'.injective (h1.trans (map_one eX').symm)
  have heven : Even (Nat.card (rankTwoQuot X₀')) := by
    rw [Nat.card_congr eX'.toEquiv]
    exact u3_even_card_SL2 F
  obtain ⟨eq⟩ := nonempty_quotCenter_map_equiv (N := standardComponentOddCore G₁)
    odd_card_standardComponentOddCore' hsimp hcen heven
  obtain ⟨eP⟩ := nonempty_SL2_equiv_galois F (by omega) hF
  have eL2 : rankTwoQuot (oddQuotImageC K X₀) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField 2 f) := (eq.symm.trans eX').trans eP
  obtain ⟨Ē, hĒC, hĒel, hĒ4⟩ := h3.exists_four_le_centralizer_oddQuotImageC hKL
  have hB : BenderHyp (↥G₁ ⧸ standardComponentOddCore ↥G₁) (oddQuotImageC K X₀) :=
    ⟨hstd, standardComponentOddCore_quot_eq_bot, hnn, two_le_pRank_of_le hĒC hĒel hĒ4,
      Or.inl ⟨f, hM.three_le, stated_psl2_of_mulEquiv hM.three_le eL2⟩⟩
  exact hL2 _ (oddQuotImageC K X₀) hB f hM.three_le ⟨eL2⟩

theorem u3_case_of_eight_leC (h61 : GMS61InductionC) (hL2 : L2Res) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
      standardComponentOddCore G = ⊥ → ∀ m : ℕ, 3 ≤ m →
        StatedClassicalModel (rankTwoQuot A) .PSU 3 2 m → False := by
  intro G _ _ A hA hO m hm hs
  have hB : BenderHyp G A :=
    ⟨hA.standard, hO, hA.not_normal, hA.rank, Or.inr (Or.inl ⟨m, by omega, hs⟩)⟩
  exact u3Res_of_u3MinCounter (fun G _ _ L f hM => false_of_u3MinCounterC h61 hL2 hM) G A hB m
    hm (nonempty_mulEquiv_psu3_of_stated (by omega) hs)

end CFSG.ComponentClassification.GMS78
