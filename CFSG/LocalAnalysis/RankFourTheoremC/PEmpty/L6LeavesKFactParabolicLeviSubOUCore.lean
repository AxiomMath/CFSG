module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubSection
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympHas
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubSympRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup CFSG.AGLEmbedding.LeviBlock

section General

variable {Q : Type} [Group Q] {ι : Type} [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)]

theorem exists_levi_section_of_blocks_gen [Finite Q] {β : Q →* ∀ j, G j}
    (hker : IsPGroup 2 β.ker) {S : ∀ j, Subgroup (G j)}
    (hS : Subgroup.pi Set.univ S ≤ β.range) (j₀ : ι) (hq : CFSG.Open.IsQuasisimple ↥(S j₀))
    {A : Type} [Group A] (ρ : Q →* A)
    (hcen : ∀ y ∈ blockPreOf β S j₀, ρ y = 1 → β y j₀ ∈ Subgroup.center (G j₀)) :
    ∃ Y W : Subgroup A, Y ≤ ρ.range ∧ S622IsSimpleSection Y W ∧
      W.relIndex Y = Nat.card (↥(S j₀) ⧸ Subgroup.center ↥(S j₀)) ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥(S j₀)) →
        ¬ r ∣ Nat.card W := by
  classical
  set ρ' : ↥(blockPreOf β S j₀) →* A := ρ.comp (blockPreOf β S j₀).subtype with hρ'
  haveI : Finite ↥(blockPreOf β S j₀) := inferInstance
  haveI : Finite ↥ρ'.range := Finite.of_surjective _ ρ'.rangeRestrict_surjective
  let θ : ↥(blockPreOf β S j₀) →* ↥(S j₀) ⧸ Subgroup.center ↥(S j₀) :=
    (QuotientGroup.mk' (Subgroup.center ↥(S j₀))).comp (blockHomOf β S j₀)
  have hkerle : ρ'.rangeRestrict.ker ≤ θ.ker := by
    intro y hy
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hy
    rw [MonoidHom.mem_ker]
    have h2 : β (y : Q) j₀ ∈ Subgroup.center (G j₀) := hcen y y.2 hy
    refine (QuotientGroup.eq_one_iff _).2 ?_
    rw [Subgroup.mem_center_iff]
    intro s
    refine Subtype.ext ?_
    have h3 := Subgroup.mem_center_iff.1 h2 (s : G j₀)
    simpa [coe_blockHomOf] using h3
  let θ' : ↥ρ'.range →* ↥(S j₀) ⧸ Subgroup.center ↥(S j₀) :=
    ρ'.rangeRestrict.liftOfSurjective ρ'.rangeRestrict_surjective ⟨θ, hkerle⟩
  have hθθ' : ∀ y, θ' (ρ'.rangeRestrict y) = θ y := fun y =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨θ, hkerle⟩ y
  have hθ'surj : Function.Surjective θ' := by
    intro t
    obtain ⟨y, rfl⟩ := (QuotientGroup.mk'_surjective _).comp (blockHomOf_surjective hS j₀) t
    exact ⟨ρ'.rangeRestrict y, hθθ' y⟩
  haveI : IsSimpleGroup (↥(S j₀) ⧸ Subgroup.center ↥(S j₀)) := hq.2
  have hsec := S622IsSimpleSection.of_surjective θ' hθ'surj
    (CFSG.AGLEmbedding.LeviBlock.exists_noncomm_centerQuotient hq)
  refine ⟨ρ'.range, θ'.ker.map ρ'.range.subtype, ?_, hsec, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨((y : ↥(blockPreOf β S j₀)) : Q), rfl⟩
  · have h1 := Subgroup.relIndex_map_map_of_injective θ'.ker ⊤ ρ'.range.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.relIndex_top_right] at h1
    rw [h1, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hθ'surj, Subgroup.card_top]
  · intro r hr hr2 hrZ hdvd
    rw [Subgroup.card_map_of_injective ρ'.range.subtype_injective] at hdvd
    have hker' : θ'.ker = θ.ker.map ρ'.rangeRestrict := by
      ext w
      constructor
      · intro hw
        obtain ⟨y, rfl⟩ := ρ'.rangeRestrict_surjective w
        have hw' : θ' (ρ'.rangeRestrict y) = 1 := hw
        refine ⟨y, ?_, rfl⟩
        change θ y = 1
        rw [← hθθ']
        exact hw'
      · rintro ⟨y, hy, rfl⟩
        rw [MonoidHom.mem_ker, hθθ']
        exact hy
    have hdvd' : r ∣ Nat.card ↥θ.ker := by
      refine hdvd.trans ?_
      rw [hker']
      exact Subgroup.card_map_dvd θ.ker ρ'.rangeRestrict
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥θ.ker) r hdvd'
    set y : ↥(blockPreOf β S j₀) := z.1 with hy
    have hyker : y ∈ θ.ker := z.2
    have hordy : orderOf y = r := by
      rw [hy, Subgroup.orderOf_coe, hz]
    have hyc : blockHomOf β S j₀ y ∈ Subgroup.center ↥(S j₀) :=
      (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hyker)
    have hyr : (blockHomOf β S j₀ y) ^ r = 1 := by
      rw [← map_pow, ← hordy, pow_orderOf_eq_one, map_one]
    set u : ↥(Subgroup.center ↥(S j₀)) := ⟨blockHomOf β S j₀ y, hyc⟩ with hu
    have hur : u ^ r = 1 := Subtype.ext (by simpa [hu] using hyr)
    have hdvd1 : orderOf u ∣ r := orderOf_dvd_of_pow_eq_one hur
    have hdvd2 : orderOf u ∣ Nat.card (Subgroup.center ↥(S j₀)) := orderOf_dvd_natCard u
    rcases (Nat.dvd_prime hr).1 hdvd1 with h1 | h1
    · have hu1 : u = 1 := orderOf_eq_one_iff.1 h1
      have hyk : y ∈ (blockHomOf β S j₀).ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val hu1
      obtain ⟨k, hk⟩ := isPGroup_ker_blockHomOf hker S j₀ ⟨y, hyk⟩
      have hyk2 : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hr2k : r ∣ 2 ^ k := hordy ▸ orderOf_dvd_of_pow_eq_one hyk2
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hr2k))
    · exact hrZ (h1 ▸ hdvd2)

end General

section Assembly

variable {S Q : Type} [Group S] [Finite S] [Group Q] [Finite Q] {ι : Type} [DecidableEq ι]
  {G : ι → Type} [∀ j, Group (G j)]

theorem leviAt_of_blocks {K₀ : Subgroup S} (ρ : Q →* S) (hρK : ρ.range ≤ K₀) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) (hpQ : p ∣ Nat.card Q) (β : Q →* ∀ j, G j)
    (hker : IsPGroup 2 β.ker) (Sj : ∀ j, Subgroup (G j))
    (hpi : Subgroup.pi Set.univ Sj ≤ β.range)
    (hblk : ∀ g : Q, g ^ p = 1 → g ≠ 1 → ∃ j, CFSG.Open.IsQuasisimple ↥(Sj j) ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥(Sj j)) ∧
      p ∣ Nat.card (↥(Sj j) ⧸ Subgroup.center ↥(Sj j)) ∧
      3 ∣ Nat.card (↥(Sj j) ⧸ Subgroup.center ↥(Sj j)))
    (hcen : ∀ y : Q, ρ y = 1 → ∀ j, β y j ∈ Subgroup.center (G j))
    (hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S)) :
    ∃ (f : ℕ) (Y W : Subgroup S), f.Prime ∧ f ≠ 2 ∧ f ≠ p ∧
      2 ≤ CFSG.Open.pRank f (⊤ : Subgroup S) ∧
      Y ≤ K₀ ∧ S622IsSimpleSection Y W ∧ f ∣ W.relIndex Y ∧
      p ∣ W.relIndex Y ∧ ¬ p ∣ Nat.card W := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Q) p hpQ
  have hgp : g ^ p = 1 := hg ▸ pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hg, h, orderOf_one])
  obtain ⟨j, hq, hpZ, hpT, h3T⟩ := hblk g hgp hg1
  obtain ⟨Y, W, hYQ, hsec, hrel, hWr⟩ := exists_levi_section_of_blocks_gen hker hpi j hq ρ
    (fun y _ hy => hcen y hy j)
  have hp2 : p ≠ 2 := by omega
  refine ⟨3, Y, W, Nat.prime_three, by norm_num, by omega, hrank, hYQ.trans hρK, hsec, ?_, ?_,
    hWr p hp hp2 hpZ⟩
  · rw [hrel]
    exact h3T
  · rw [hrel]
    exact hpT

end Assembly

section Elements

theorem map_eq_one_of_pow_eq_one_of_not_dvd {G H : Type*} [Group G] [Group H] (φ : G →* H)
    {p : ℕ} (hp : p.Prime) (hcop : ¬ p ∣ Nat.card H) {x : G} (hx : x ^ p = 1) : φ x = 1 := by
  have h1 : orderOf (φ x) ∣ p := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  rcases (Nat.dvd_prime hp).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ orderOf_dvd_natCard (φ x)) hcop

theorem mem_of_pow_eq_one_of_index_two {G : Type*} [Group G] {H : Subgroup G}
    (hH : H.index = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G} (hx : x ^ p = 1) :
    x ∈ H := by
  haveI : H.Normal := Subgroup.normal_of_index_eq_two hH
  have hcard : Nat.card (G ⧸ H) = 2 := hH
  haveI : Finite (G ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hp2' : ¬ p ∣ Nat.card (G ⧸ H) := by
    rw [hcard]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  exact (QuotientGroup.eq_one_iff x).1
    (map_eq_one_of_pow_eq_one_of_not_dvd (QuotientGroup.mk' H) hp hp2' hx)

theorem det_eq_one_of_pow_eq_one {K : Type} [Field K] [Finite K] {k : ℕ} {p : ℕ} (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card K - 1) {x : GL (Fin k) K} (hx : x ^ p = 1) :
    Matrix.GeneralLinearGroup.det x = 1 :=
  map_eq_one_of_pow_eq_one_of_not_dvd Matrix.GeneralLinearGroup.det hp
    (by rwa [Nat.card_units]) hx

end Elements

section SLBlock

abbrev slRange (K : Type) [Field K] (k : ℕ) : Subgroup (GL (Fin k) K) :=
  (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin k) K →* GL (Fin k) K).range

theorem slBlock_data {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ} (hk2 : 2 ≤ k)
    (hq : 3 ≤ k ∨ 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K - 1)
    {x : GL (Fin k) K} (hx : x ^ p = 1) (hx1 : x ≠ 1) :
    x ∈ slRange K k ∧ CFSG.Open.IsQuasisimple ↥(slRange K k) ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥(slRange K k)) ∧
      p ∣ Nat.card (↥(slRange K k) ⧸ Subgroup.center ↥(slRange K k)) ∧
      3 ∣ Nat.card (↥(slRange K k) ⧸ Subgroup.center ↥(slRange K k)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let e := slEquivToGLRange (K := K) k
  have hxR : x ∈ slRange K k := by
    change x ∈ (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin k) K →* GL (Fin k) K).range
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    exact det_eq_one_of_pow_eq_one hp hpK hx
  have hQS : CFSG.Open.IsQuasisimple ↥(slRange K k) :=
    isQuasisimple_of_mulEquiv e (spFlag_isQuasisimple_SL hk2 hq)
  have hZ : Nat.card (Subgroup.center ↥(slRange K k)) =
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin k) K)) := by
    have h := map_center_mulEquiv e
    rw [← h, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  have hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥(slRange K k)) := by
    rw [hZ]
    exact fun h => hpK (h.trans (card_center_SL_dvd (by omega)))
  have hQ : Nat.card (↥(slRange K k) ⧸ Subgroup.center ↥(slRange K k)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin k) K ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin k) K)) :=
    (spFlag_card_center_congr e).symm
  refine ⟨hxR, hQS, hpZ, ?_, ?_⟩
  · have hdvd : p ∣ Nat.card ↥(slRange K k) := by
      have h1 : orderOf (⟨x, hxR⟩ : ↥(slRange K k)) = p := by
        refine orderOf_eq_prime ?_ ?_
        · exact Subtype.ext (by simpa using hx)
        · exact fun h => hx1 (congrArg Subtype.val h)
      exact h1 ▸ orderOf_dvd_natCard _
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(slRange K k))
    rw [hmul] at hdvd
    exact ((Nat.Prime.dvd_mul hp).1 hdvd).resolve_right hpZ
  · rw [hQ]
    obtain ⟨f, hf, hqf⟩ := spFlag_card_eq_two_pow (K := K)
    by_cases hK2 : Nat.card K = 2
    · exact three_dvd_card_slQuot hk2 hK2
    · have h3 : 3 ∣ Nat.card K ^ 2 - 1 := by
        rw [hqf, ← pow_mul, mul_comm, pow_mul]
        have := Nat.sub_one_dvd_pow_sub_one (2 ^ 2) f
        simpa using this
      by_cases h3q : 3 ∣ Nat.card K - 1
      · exact dvd_card_slQuot_of_dvd_sub_one hk2 h3q
      · exact dvd_card_slQuot hk2 Nat.prime_three le_rfl hk2 h3 h3q

theorem blk_of_trivial_center {B : Type} [Group B] [Finite B] (hq : CFSG.Open.IsQuasisimple B)
    (hZ : Subgroup.center B = ⊥) {p : ℕ} (hp : p.Prime) (hpB : p ∣ Nat.card B)
    (h3 : 3 ∣ Nat.card B) :
    CFSG.Open.IsQuasisimple B ∧ ¬ p ∣ Nat.card (Subgroup.center B) ∧
      p ∣ Nat.card (B ⧸ Subgroup.center B) ∧ 3 ∣ Nat.card (B ⧸ Subgroup.center B) := by
  have hc : Nat.card (Subgroup.center B) = 1 := by rw [hZ]; exact Subgroup.card_bot
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center B)
  rw [hc, mul_one] at hmul
  refine ⟨hq, ?_, ?_, ?_⟩
  · rw [hc]
    exact fun h => hp.one_lt.ne' (Nat.dvd_one.1 h)
  · rw [← hmul]
    exact hpB
  · rw [← hmul]
    exact h3

end SLBlock

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
