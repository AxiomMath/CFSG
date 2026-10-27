module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalSixSetup

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal.Five

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

@[expose] def zStar (D : Subgroup G) (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    Subgroup G :=
  D ⊓ ⨅ k, centralizing D (Abar k)

omit [Finite G] in
theorem mem_zStar_iff {y : G} : y ∈ zStar D Abar ↔ y ∈ D ∧ ∀ k,
    aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar k)) y := by
  simp only [zStar, Subgroup.mem_inf, Subgroup.mem_iInf, mem_centralizing_iff]
  exact ⟨fun h => ⟨h.1, fun k => (h.2 k).2⟩, fun h => ⟨h.1, fun k => ⟨h.1, h.2 k⟩⟩⟩

omit [Finite G] in
theorem zStar_le : zStar D Abar ≤ D :=
  inf_le_left

omit [Finite G] in
theorem zStar_le_normalizer : zStar D Abar ≤ Subgroup.normalizer (D : Set G) :=
  zStar_le.trans Subgroup.le_normalizer

theorem factorZStar_le_zStar (hyp : Hyp61 G D r Abar) (i : Fin r) :
    factorZStar D Abar i ≤ zStar D Abar := by
  rintro y ⟨hyA, hyc⟩
  refine mem_zStar_iff.mpr ⟨preimage_le D _ hyA, fun k => ?_⟩
  by_cases hk : k = i
  · subst hk
    exact centralizes_of_mem_centralizing hyc
  · exact centralizes_of_mem_centralizing (factor_le_centralizing hyp.hcomm hk hyA)

omit [Finite G] in
theorem zStar_conj (g : G) :
    zStar (rightConjugate D g) (conjFactors D Abar g) = rightConjugate (zStar D Abar) g := by
  ext y
  simp only [mem_zStar_iff, mem_rightConjugate_iff, centralizes_conj_iff]

theorem normalizer_le_normalizer_zStar (hyp : Hyp61 G D r Abar) :
    Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (zStar D Abar : Set G) := by
  intro h hh
  apply AschbacherToolkit.mem_normalizer_of_conj_le
  intro y hy
  obtain ⟨hyD, hyc⟩ := mem_zStar_iff.mp hy
  refine mem_zStar_iff.mpr ⟨(Subgroup.mem_normalizer_iff.mp hh y).mp hyD, fun k => ?_⟩
  intro w hw
  obtain ⟨j, hj⟩ := hyp.hperm h⁻¹ (Subgroup.inv_mem _ hh) k
  have hw' : h⁻¹ * w * h ∈ aschbacherThm5Preimage D (Abar j) := by
    rw [← hj]
    exact ⟨w, hw, by simp⟩
  have h2 := (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_core D hh) _).mp
    (hyc j _ hw')
  have h3 : h * (y⁻¹ * (h⁻¹ * w * h)⁻¹ * y * (h⁻¹ * w * h)) * h⁻¹ =
      (h * y * h⁻¹)⁻¹ * w⁻¹ * (h * y * h⁻¹) * w := by group
  rwa [h3] at h2

theorem centralizer_le_of_mem_zStar (hC : Counterexample G D r Abar) {t : G}
    (ht : t ∈ zStar D Abar) (ht2 : ∃ n : ℕ, t ^ (2 ^ n) = 1) (ht1 : t ≠ 1) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (D : Set G) :=
  centralizer_le hC ⟨0, by have := two_le hC; omega⟩ ht2 ht1 ((mem_zStar_iff.mp ht).2 _)

theorem mem_normalizer_of_zStar (hC : Counterexample G D r Abar) {t y : G}
    (ht : t ∈ zStar D Abar) (hty : y⁻¹ * t * y ∈ zStar D Abar)
    (ht2 : ∃ n : ℕ, t ^ (2 ^ n) = 1) (ht1 : t ≠ 1) : y ∈ Subgroup.normalizer (D : Set G) :=
  mem_normalizer_of_fusion hC ⟨0, by have := two_le hC; omega⟩ ⟨0, by have := two_le hC; omega⟩
    ht2 ht1 ((mem_zStar_iff.mp ht).2 _) ((mem_zStar_iff.mp hty).2 _)

theorem eq_one_of_mem_zStar_inf (hC : Counterexample G D r Abar) {g t : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) (ht : t ∈ zStar D Abar)
    (htg : t ∈ rightConjugate (zStar D Abar) g) (ht2 : ∃ n : ℕ, t ^ (2 ^ n) = 1) : t = 1 := by
  by_contra ht1
  rw [mem_rightConjugate_iff] at htg
  apply hg
  obtain ⟨n, hn⟩ := ht2
  refine mem_normalizer_of_zStar hC (t := g * t * g⁻¹) (y := g) htg ?_ ⟨n, ?_⟩ ?_
  · simpa [mul_assoc] using ht
  · rw [conj_pow, hn]
    group
  · intro h
    apply ht1
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group

theorem normalizer_le_of_le_zStar (hC : Counterexample G D r Abar) {P : Subgroup G}
    (hP : P ≤ zStar D Abar) (hP2 : IsPGroup 2 P) (hP1 : P ≠ ⊥) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (D : Set G) := by
  obtain ⟨⟨t, htP⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
  obtain ⟨n, hn⟩ := hP2 ⟨t, htP⟩
  intro y hy
  refine mem_normalizer_of_zStar hC (hP htP) (hP ?_) ⟨n, ?_⟩ ?_
  · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) t).mp htP
    simpa using this
  · have := congrArg Subtype.val hn
    simpa using this
  · exact fun h => ht1 (Subtype.ext h)

theorem normalizer_zStar (hC : Counterexample G D r Abar)
    (heven : Even (Nat.card (zStar D Abar))) :
    Subgroup.normalizer (zStar D Abar : Set G) = Subgroup.normalizer (D : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (fun y hy => ?_) (normalizer_le_normalizer_zStar hC.hyp)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  refine mem_normalizer_of_zStar hC t.2 ?_ ⟨1, ?_⟩ ?_
  · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) t).mp t.2
    simpa using this
  · rw [pow_one, ← ht']
    exact pow_orderOf_eq_one _
  · intro h
    rw [h, orderOf_one] at ht'
    omega

theorem tightlyEmbedded_zStar (hC : Counterexample G D r Abar)
    (heven : Even (Nat.card (zStar D Abar))) : TightlyEmbedded (zStar D Abar) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨heven, fun x hx => ?_⟩
  rw [normalizer_zStar hC heven] at hx
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hodd)
  have hw' : orderOf (w : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hw
  have hwQ : (w : G) ∈ zStar D Abar := w.2.1
  have hwQx : (w : G) ∈ rightConjugate (zStar D Abar) x := w.2.2
  rw [mem_rightConjugate_iff] at hwQx
  apply hx
  refine mem_normalizer_of_zStar hC (t := x * w * x⁻¹) (y := x) hwQx ?_ ⟨1, ?_⟩ ?_
  · simpa [mul_assoc] using hwQ
  · rw [pow_one, conj_pow, ← hw', pow_orderOf_eq_one]
    group
  · intro h
    have h1 : (w : G) = 1 := by
      calc (w : G) = x⁻¹ * (x * w * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    rw [h1, orderOf_one] at hw'
    omega

theorem centralizer_le_of_mem_zStar_conj (hC : Counterexample G D r Abar) (g : G) {t : G}
    (ht : t ∈ rightConjugate (zStar D Abar) g) (ht2 : ∃ n : ℕ, t ^ (2 ^ n) = 1) (ht1 : t ≠ 1) :
    Subgroup.centralizer ({t} : Set G) ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g := by
  have h := centralizer_le_of_mem_zStar (hC.conj g) (t := t) (by rwa [zStar_conj]) ht2 ht1
  rwa [normalizer_rightConjugate] at h

theorem mem_conj_normalizer_of_zStar (hC : Counterexample G D r Abar) (g : G) {t y : G}
    (ht : t ∈ rightConjugate (zStar D Abar) g)
    (hty : y⁻¹ * t * y ∈ rightConjugate (zStar D Abar) g)
    (ht2 : ∃ n : ℕ, t ^ (2 ^ n) = 1) (ht1 : t ≠ 1) :
    y ∈ rightConjugate (Subgroup.normalizer (D : Set G)) g := by
  have h := mem_normalizer_of_zStar (hC.conj g) (t := t) (y := y) (by rwa [zStar_conj])
    (by rwa [zStar_conj]) ht2 ht1
  rwa [normalizer_rightConjugate] at h

theorem pRank_le_of_part_one (Q : Subgroup G) (htight : TightlyEmbedded Q) {x : G}
    (hx : x ∉ Subgroup.normalizer (Q : Set G)) {T S : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate Q x ⊓ Subgroup.normalizer (Q : Set G)))
    (hS : IsSylowOf 2 S (Q ⊔ T)) (hTS : T ≤ S) (hT1 : T ≠ ⊥) :
    CFSG.Open.pRank 2 T ≤ CFSG.Open.pRank 2 (Subgroup.normalizer (T : Set G) ⊓ Q) := by
  obtain ⟨T', rfl⟩ := hT
  obtain ⟨S', rfl⟩ := hS
  obtain ⟨-, -, -, -, factor, -, -, -⟩ := theorem_2_part_one Q htight x hx T' S' hTS hT1
  have h1 := CFSG.RankThreeEvenClassification.Helpers.pRank_eq_of_subgroup_equiv 2
    Nat.prime_two _ _ factor
  calc CFSG.Open.pRank 2 _ = _ := h1
    _ ≤ _ := CFSG.SectionRank.pRank_mono (by norm_num) (inf_le_inf_right _ inf_le_left)

theorem pRank_overlap_le (hC : Counterexample G D r Abar)
    (heven : Even (Nat.card (zStar D Abar))) {x : G}
    (hx : x ∉ Subgroup.normalizer (D : Set G)) :
    CFSG.Open.pRank 2 (rightConjugate (zStar D Abar) x ⊓ Subgroup.normalizer (D : Set G)) ≤
      CFSG.Open.pRank 2 (zStar D Abar ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN := normalizer_zStar hC heven
  have htight := tightlyEmbedded_zStar hC heven
  have hxQ : x ∉ Subgroup.normalizer (zStar D Abar : Set G) := by rwa [hN]
  obtain ⟨T, hT⟩ := exists_isSylowOf 2
    (rightConjugate (zStar D Abar) x ⊓ Subgroup.normalizer (zStar D Abar : Set G))
  have hT' := hT
  rw [hN] at hT'
  refine (Strong.pRank_le_of_isSylowOf hT').trans ?_
  by_cases hT1 : T = ⊥
  · rw [hT1]
    exact CFSG.SectionRank.pRank_mono (by norm_num) bot_le
  obtain ⟨S, hS, hTS⟩ := AschbacherTheorem3.exists_isSylowOf_le hT.isPGroup
    (le_sup_right : T ≤ zStar D Abar ⊔ T)
  refine (pRank_le_of_part_one _ htight hxQ hT hS hTS hT1).trans
    (CFSG.SectionRank.pRank_mono (by norm_num) (le_inf inf_le_right (inf_le_left.trans ?_)))
  have hTZ : T ≤ zStar (rightConjugate D x) (conjFactors D Abar x) := by
    rw [zStar_conj]
    exact hT.le.trans inf_le_left
  have h := normalizer_le_of_le_zStar (hC.conj x) hTZ hT.isPGroup hT1
  rwa [normalizer_rightConjugate] at h

theorem pRank_zStar_le (hC : Counterexample G D r Abar)
    (heven : Even (Nat.card (zStar D Abar))) {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) :
    CFSG.Open.pRank 2 (zStar D Abar ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) g) ≤
      CFSG.Open.pRank 2 (rightConjugate (zStar D Abar) g ⊓ Subgroup.normalizer (D : Set G)) := by
  have heven' : Even (Nat.card (zStar (rightConjugate D g) (conjFactors D Abar g))) := by
    rwa [zStar_conj, rightConjugate_card]
  have hg' : g⁻¹ ∉ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := by
    rw [normalizer_rightConjugate, mem_rightConjugate_iff]
    simpa using hg
  have h := pRank_overlap_le (hC.conj g) heven' hg'
  rwa [zStar_conj, rightConjugate_mul, mul_inv_cancel, rightConjugate_one,
    Six.conj_normalizer_inv, normalizer_rightConjugate] at h

end DeltaLocal.Five

end CFSG.ComponentClassification.AschbacherTheorem5
