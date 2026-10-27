module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCriterion

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

@[expose] def NoCentralizerNormalized (W : Type*) [Group W] : Prop :=
  ∀ H₀ P : Subgroup W, IsSylowOf 2 P H₀ → IsElemAbelian 2 P → 4 ≤ Nat.card P →
    (∀ a ∈ P, a ≠ 1 → centralizer ({a} : Set W) ≤ normalizer (H₀ : Set W)) → False

theorem false_of_noCentralizerNormalized (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} (hA : AS76b.Hyp31 A) {X₀ W : Type*}
    [Group X₀] [Group W] [Finite W] (hW : AutModel X₀ W ⊤) (hZ : center ↥A = ⊥)
    (e : ↥A ⧸ center ↥A ≃* X₀) (hN : NoCentralizerNormalized W) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg, T, hT1, hT2⟩ := h33 G A hA
  have hR := h32 G A hA
  obtain ⟨ψ, hψ⟩ := exists_isActionHom hW hA.standard.1.1 e
  have hK := tightlyEmbedded_centralizer_of_standard hA.standard
  have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := by
    rw [hA.standard.2.2.2.1]
    exact hg
  have hTab : ∀ x ∈ T, x ^ 2 = 1 := by
    intro x hx
    have hxK : g * x * g⁻¹ ∈ centralizer (A : Set G) :=
      (mem_rightConjugate_iff _ g x).mp (hT2.le hx)
    have h2 : IsPGroup 2 (zpowers (g * x * g⁻¹)) := by
      have hx2 : IsPGroup 2 (zpowers x) := hT2.isPGroup.to_le (zpowers_le.mpr hx)
      have := hx2.map (MulAut.conj g).toMonoidHom
      rwa [MonoidHom.map_zpowers] at this
    have hsq := sq_eq_one_of_isPGroup_zpowers hR hxK h2
    have hc' : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := conj_pow
    rw [hc'] at hsq
    have := congrArg (fun y => g⁻¹ * y * g) hsq
    simpa [mul_assoc] using this
  have hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c →
      c ∈ normalizer (rightConjugate (centralizer (A : Set G)) g : Set G) :=
    fun t ht ht1 c _ hct => mem_normalizer_of_commute_of_tightlyEmbedded
      (tightlyEmbedded_rightConjugate' hK g) (hT2.le ht) ht1 (hTab t ht) hct
  have hTN : T ≤ normalizer (A : Set G) := hT1.le.trans inf_le_right
  have hTC : T ⊓ centralizer (A : Set G) = ⊥ := by
    refine two_subgroup_of_odd_eq_bot _ (centralizer (A : Set G) ⊓
      rightConjugate (centralizer (A : Set G)) g) (hT2.isPGroup.to_inf_left) (hK.2 g hgK) ?_
    exact le_inf inf_le_right (inf_le_left.trans hT2.le)
  refine hN (((rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)).subgroupOf
      (normalizer (A : Set G))).map ψ) ((T.subgroupOf (normalizer (A : Set G))).map ψ) ?_ ?_ ?_ ?_
  ·
    refine IsSylowOf.map ?_ ψ
    rw [← isSylowOf_map_subtype_iff (normalizer (A : Set G)), subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_eq_left.mpr hTN, inf_assoc, inf_idem]
    exact hT1
  ·
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
      apply Subtype.ext
      simp only [coe_mul]
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact commute_of_sq_eq_one hTab hx hy
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hTab _ hx)
      rw [this, map_one]
  ·
    rw [card_map_eq_of_inf_centralizer hψ hTC,
      Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv, hT2.card_eq, rightConjugate_card]
    have h4 := four_dvd_card_of_one_lt_pRank hA.rank
    have hpos : Nat.card (centralizer (A : Set G)) ≠ 0 := Nat.card_pos.ne'
    have hle : 2 ≤ (Nat.card (centralizer (A : Set G))).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hpos).mp (by simpa using h4)
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hle
  ·
    intro a ha ha1 w hw
    obtain ⟨t, ht, rfl⟩ := ha
    have htT : (t : G) ∈ T := ht
    have ht1 : (t : G) ≠ 1 := fun h => ha1 (by rw [show t = 1 from Subtype.ext h, map_one])
    obtain ⟨c, hcA, hc⟩ := hψ.exists_eq w (mem_top w)
    have hwt : w * ψ t = ψ t * w := mem_centralizer_singleton_iff.mp hw
    have hct : c * (t : G) = t * c := by
      have h1 : ψ (⟨c, le_normalizer hcA⟩ * t * (⟨c, le_normalizer hcA⟩ : normalizer
          (A : Set G))⁻¹ * t⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc, hwt]
        group
      have hnK := (hψ.eq_one_iff _).mp h1
      simp only [coe_mul, coe_inv] at hnK
      have htA : (t : G) * c⁻¹ * (t : G)⁻¹ ∈ A :=
        (mem_normalizer_iff.mp t.2 _).mp (A.inv_mem hcA)
      have hnA : c * (t : G) * c⁻¹ * (t : G)⁻¹ ∈ A := by
        have : c * (t : G) * c⁻¹ * (t : G)⁻¹ = c * ((t : G) * c⁻¹ * (t : G)⁻¹) := by group
        rw [this]
        exact A.mul_mem hcA htA
      have hn1 : c * (t : G) * c⁻¹ * (t : G)⁻¹ = 1 := by
        have hmem : (⟨_, hnA⟩ : A) ∈ center ↥A := by
          rw [mem_center_iff]
          intro y
          exact Subtype.ext ((mem_centralizer_iff.mp hnK) y y.2)
        rw [hZ, mem_bot] at hmem
        exact congrArg Subtype.val hmem
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hn1)
    have hcQ := hQ (t : G) htT ht1 c hcA hct
    have hc'Q : (⟨c, le_normalizer hcA⟩ : normalizer (A : Set G)) ∈ normalizer
        (((rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)).subgroupOf
          (normalizer (A : Set G)) : Subgroup (normalizer (A : Set G))) :
            Set (normalizer (A : Set G))) := by
      rw [mem_normalizer_iff]
      intro h
      simp only [mem_subgroupOf, mem_inf, coe_mul, coe_inv]
      have hh : ((h : normalizer (A : Set G)) : G) ∈ normalizer (A : Set G) := h.2
      have hch : c * (h : G) * c⁻¹ ∈ normalizer (A : Set G) :=
        mul_mem (mul_mem (le_normalizer hcA) hh) (inv_mem (le_normalizer hcA))
      rw [← mem_normalizer_iff.mp hcQ]
      exact ⟨fun h1 => ⟨h1.1, hch⟩, fun h1 => ⟨h1.1, hh⟩⟩
    rw [← hc]
    exact le_normalizer_map ψ ⟨_, hc'Q, rfl⟩

end CFSG.ComponentClassification.RankTwoSporadic
