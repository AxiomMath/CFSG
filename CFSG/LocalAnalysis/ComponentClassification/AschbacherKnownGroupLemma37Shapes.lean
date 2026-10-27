module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Printed
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma38

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup

open CFSG.Open Subgroup

namespace Lemma37

variable {G : Type*} [Group G]

theorem pRank_eq_one_of_unique [Finite G] {A : Subgroup G} (hA : aschbacherThm5IsSemisimple A)
    (S₀ : Sylow 2 A)
    (hinv : ∀ x₁ x₂ : G, x₁ ∈ (S₀ : Subgroup A).map A.subtype →
      x₂ ∈ (S₀ : Subgroup A).map A.subtype → x₁ ^ 2 = 1 → x₂ ^ 2 = 1 → x₁ ≠ 1 → x₂ ≠ 1 →
      x₁ = x₂) :
    Open.pRank 2 A = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrankS : Open.pRank 2 ((S₀ : Subgroup A).map A.subtype) = Open.pRank 2 A :=
    Lemma38.pRank_sylow_map S₀
  apply le_antisymm
  · rw [← hrankS]
    apply SectionRank.pRank_le (by norm_num)
    intro E hES hE
    by_cases hEb : E = ⊥
    · rw [hEb, card_bot]
      norm_num
    · obtain ⟨⟨e, heE⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hEb
      have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
      have hle : E ≤ zpowers e := by
        intro y hy
        by_cases hy1 : y = 1
        · rw [hy1]
          exact one_mem _
        · rw [hinv y e (hES hy) (hES heE) (hE.2 y hy) (hE.2 e heE) hy1 he1']
          exact mem_zpowers e
      calc Nat.card E ≤ Nat.card (zpowers e) := card_le_of_le hle
        _ = 2 := by rw [Nat.card_zpowers]; exact orderOf_eq_prime (hE.2 e heE) he1'
        _ = 2 ^ 1 := by norm_num
  · obtain ⟨k, K, hk, hKq, -, -⟩ := hA
    have hev := Lemma38.even_card_of_isQuasisimple (hKq ⟨0, hk⟩).2
    have h2A : 2 ∣ Nat.card A :=
      (even_iff_two_dvd.1 hev).trans (Subgroup.card_dvd_of_le (hKq ⟨0, hk⟩).1)
    obtain ⟨⟨y, hyA⟩, hy⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 h2A
    have hyo : orderOf y = 2 := by rw [← Subgroup.orderOf_mk y hyA]; exact hy
    have hy2 : y ^ 2 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
    refine SectionRank.le_pRank (by norm_num) (zpowers_le.2 hyA) ⟨inferInstance, ?_⟩
      (by rw [Nat.card_zpowers, hyo]; norm_num)
    intro w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy2, one_zpow]

theorem dihedral_eight [Finite G] {A : Subgroup G} (hA : aschbacherThm5IsSemisimple A)
    (S₀ : Sylow 2 A) {x s : G} (hxS : x ∈ (S₀ : Subgroup A).map A.subtype)
    (hsS : s ∈ (S₀ : Subgroup A).map A.subtype) (hx4 : orderOf x = 4) (hs2 : s ^ 2 = 1)
    (hsx : s * x * s⁻¹ = x⁻¹) (hsn : s ∉ zpowers x)
    (hcard : Nat.card ((S₀ : Subgroup A).map A.subtype) = 8) :
    Open.IsQuasisimple A ∧ HasDihedralSylowTwo A := by
  classical
  set S := (S₀ : Subgroup A).map A.subtype with hS
  have hsinv : ∀ k : ℤ, s * x ^ k * s⁻¹ = x ^ (-k) := by
    intro k
    rw [← conj_zpow, hsx, inv_zpow']
  have hsN : s ∈ normalizer (zpowers x : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
      rw [hsinv]
      exact zpow_mem (mem_zpowers x) _
    · intro hh
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hh
      have hsinv' : s⁻¹ = s := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hs2]
      have : h = s * x ^ k * s⁻¹ := by
        rw [hk]
        calc h = (s * s) * h * (s⁻¹ * s⁻¹) := by
              rw [← pow_two, hs2, one_mul, hsinv', ← pow_two, hs2, mul_one]
          _ = s * (s * h * s⁻¹) * s⁻¹ := by rw [hsinv']; group
      rw [this, hsinv]
      exact zpow_mem (mem_zpowers x) _
  have hs2x : s ^ 2 ∈ zpowers x := by rw [hs2]; exact one_mem _
  have hcard' : Nat.card (zpowers x ⊔ zpowers s : Subgroup G) = 8 := by
    rw [card_sup_zpowers hsN hs2x hsn, Nat.card_zpowers, hx4]
  have hle : zpowers x ⊔ zpowers s ≤ S := sup_le (zpowers_le.2 hxS) (zpowers_le.2 hsS)
  have hSeq : zpowers x ⊔ zpowers s = S := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcard'])
  have hout : ∀ w ∈ S, w ∉ zpowers x → w * x * w⁻¹ = x⁻¹ := by
    intro w hw hwx
    rw [← hSeq] at hw
    rcases (mem_sup_zpowers_iff hsN hs2x).1 hw with h | h
    · exact absurd h hwx
    · obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
      have : w = s * x ^ k := by rw [hk]; group
      rw [this]
      calc s * x ^ k * x * (s * x ^ k)⁻¹ = s * x * s⁻¹ := by group
        _ = x⁻¹ := hsx
  have hind : ((zpowers x).subgroupOf S).index = 2 := by
    have h1 := Subgroup.card_mul_index ((zpowers x).subgroupOf S)
    rw [Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.2 hxS)).toEquiv, Nat.card_zpowers, hx4,
      hcard] at h1
    omega
  have hcent : ∀ w ∈ S, w ∉ zpowers x → ∀ h ∈ zpowers x, w * h = h * w →
      h = 1 ∨ h = x ^ 2 := by
    intro w hw hwx h hh hwh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
    have h1 : w * x ^ k * w⁻¹ = x ^ (-k) := by rw [← conj_zpow, hout w hw hwx, inv_zpow']
    have h2 : w * x ^ k * w⁻¹ = x ^ k := by
      calc w * x ^ k * w⁻¹ = x ^ k * w * w⁻¹ := by rw [hwh]
        _ = x ^ k := by group
    have hsq : (x ^ k) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← h2]
      rw [h1, ← zpow_add, neg_add_cancel, zpow_zero]
    exact mem_zpowers_sq_eq_one hx4 (zpow_mem (mem_zpowers x) k) hsq
  have hcmp : ∀ Y₁ Y₂ : Subgroup G, Y₁ ≤ S → Y₂ ≤ S → ¬ IsCyclic Y₁ → ¬ IsCyclic Y₂ →
      (∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, y₁ * y₂ = y₂ * y₁) → Y₂ ≤ Y₁ :=
    fun Y₁ Y₂ h1 h2 hc1 hc2 hcomm =>
      TwoGroup.commuting_noncyclic_le inferInstance hind hcent h1 h2 hc1 hc2 hcomm
  refine ⟨Lemma38.quasisimple_of_comparable hA S₀ hcmp, ?_⟩
  set x' : S := ⟨x, hxS⟩ with hx'
  set s' : S := ⟨s, hsS⟩ with hs'
  have hgen : (⊤ : Subgroup S) = zpowers x' ⊔ zpowers s' := by
    apply le_antisymm _ le_top
    intro w _
    have hw : (w : G) ∈ zpowers x ⊔ zpowers s := by rw [hSeq]; exact w.2
    have hmap : (zpowers x' ⊔ zpowers s').map S.subtype = zpowers x ⊔ zpowers s := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      rfl
    rw [← hmap] at hw
    obtain ⟨w', hw', hw'w⟩ := hw
    rw [← Subtype.ext hw'w]
    exact hw'
  have hσ2 : s' ^ 2 = 1 := Subtype.ext (by simpa using hs2)
  have hrel : s' * x' * s'⁻¹ = x'⁻¹ := Subtype.ext (by simpa using hsx)
  have hσρ : s' ∉ zpowers x' := by
    intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    apply hsn
    have : s = ((x' ^ k : S) : G) := by rw [hk]
    rw [this, Subgroup.coe_zpow]
    exact zpow_mem (mem_zpowers x) k
  obtain ⟨e⟩ := GorensteinWalter.dihedral_of_generators_of_not_mem x' s' hgen hσ2 hrel hσρ
  have hx'o : orderOf x' = 2 ^ (3 - 1) := by
    rw [← Subgroup.orderOf_coe, hx4]
    norm_num
  rw [hx'o] at e
  have hiso : (S₀ : Subgroup A) ≃* S :=
    (S₀ : Subgroup A).equivMapOfInjective A.subtype A.subtype_injective
  exact ⟨S₀, 3, by norm_num, ⟨hiso.trans e⟩⟩

namespace Good

variable {P S : Subgroup G} {t x : G} {T : Set G} {ρ : G} {m : ℕ}

theorem y_sq (hg : Good S t x ρ m) (hm : 3 ≤ m) : (ρ ^ 2 ^ (m - 3)) ^ 2 = x ^ 2 := by
  rw [← pow_mul, ← pow_succ, show m - 3 + 1 = m - 2 by omega]
  exact hg.2.2.2.2.2

theorem e_sq (hc : Ctx P S t x T) (hg : Good S t x ρ m) (hm : 3 ≤ m) :
    (ρ ^ 2 ^ (m - 3) * x) ^ 2 = 1 := by
  have hc' : ρ ^ 2 ^ (m - 3) * x = x * ρ ^ 2 ^ (m - 3) := hg.x_comm_pow _
  rw [pow_two]
  calc ρ ^ 2 ^ (m - 3) * x * (ρ ^ 2 ^ (m - 3) * x)
      = ρ ^ 2 ^ (m - 3) * (x * ρ ^ 2 ^ (m - 3)) * x := by group
    _ = ρ ^ 2 ^ (m - 3) * (ρ ^ 2 ^ (m - 3) * x) * x := by rw [hc']
    _ = (ρ ^ 2 ^ (m - 3)) ^ 2 * x ^ 2 := by rw [pow_two, pow_two]; group
    _ = 1 := by rw [hg.y_sq hm, ← pow_add]; exact hc.x_pow_four

theorem e_not_mem (hc : Ctx P S t x T) (hg : Good S t x ρ m) :
    ρ ^ 2 ^ (m - 3) * x ∉ zpowers ρ := by
  intro h
  apply hg.x_not_mem hc
  have : x = (ρ ^ 2 ^ (m - 3))⁻¹ * (ρ ^ 2 ^ (m - 3) * x) := by group
  rw [this]
  exact mul_mem (inv_mem (pow_mem (mem_zpowers ρ) _)) h

theorem e_comm (hg : Good S t x ρ m) : ρ * (ρ ^ 2 ^ (m - 3) * x) = ρ ^ 2 ^ (m - 3) * x * ρ := by
  calc ρ * (ρ ^ 2 ^ (m - 3) * x) = ρ ^ 2 ^ (m - 3) * (ρ * x) := by
        rw [← mul_assoc, ← pow_succ', pow_succ, mul_assoc]
    _ = ρ ^ 2 ^ (m - 3) * (x * ρ) := by rw [hg.2.2.2.1]
    _ = ρ ^ 2 ^ (m - 3) * x * ρ := by group

theorem elem_le_four [Finite G] (hc : Ctx P S t x T) (hg : Good S t x ρ m) (hm : 3 ≤ m)
    (F : Subgroup G) (hFM : F ≤ zpowers ρ ⊔ zpowers x) (hF : ∀ f ∈ F, f ^ 2 = 1) :
    Nat.card F ≤ 4 := by
  classical
  set y := ρ ^ 2 ^ (m - 3) with hy
  set r := x ^ 2 with hr
  have hyρ : y ∈ zpowers ρ := pow_mem (mem_zpowers ρ) _
  have hrρ : r ∈ zpowers ρ := hg.x_sq_mem
  have hr2 : r ^ 2 = 1 := by rw [hr, ← pow_mul]; exact hc.x_pow_four
  have hcyc : IsCyclic (zpowers ρ) := inferInstance
  have hinvρ : ∀ w ∈ zpowers ρ, w ^ 2 = 1 → w = 1 ∨ w = r := by
    intro w hw hw2
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (TwoGroup.involution_unique_of_isCyclic hcyc hw hrρ hw2 hw1 hr2
        hc.x_sq_ne_one)
  have hsub : (F : Set G) ⊆ {1, r, y * x, y * x * r} := by
    intro f hf
    have hf2 := hF f hf
    rcases hg.mem_M.1 (hFM hf) with h | h
    · rcases hinvρ f h hf2 with h1 | h1
      · rw [h1]; simp
      · rw [h1]; simp
    · set w := x⁻¹ * f with hw
      have hfw : f = x * w := by rw [hw]; group
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
      have hwx : w * x = x * w := by rw [← hk]; exact hg.x_comm_zpow k
      have hw2 : w ^ 2 = r := by
        have : f ^ 2 = x ^ 2 * w ^ 2 := by
          rw [hfw, pow_two, pow_two, pow_two]
          calc x * w * (x * w) = x * (w * x) * w := by group
            _ = x * (x * w) * w := by rw [hwx]
            _ = x * x * (w * w) := by group
        rw [hf2] at this
        have h4 : x ^ 2 * x ^ 2 = 1 := by rw [← pow_add]; exact hc.x_pow_four
        calc w ^ 2 = x ^ 2 * x ^ 2 * w ^ 2 := by rw [h4, one_mul]
          _ = x ^ 2 * (x ^ 2 * w ^ 2) := by group
          _ = x ^ 2 := by rw [← this, mul_one]
      have hwy : w * y = y * w := by
        rw [← hk, hy]
        exact (((Commute.refl ρ).zpow_left k).pow_right _).eq
      have hwy2 : (w * y⁻¹) ^ 2 = 1 := by
        have hy2 : y ^ 2 = r := by rw [hy, hr]; exact hg.y_sq hm
        rw [pow_two]
        have hwyinv : w * y⁻¹ = y⁻¹ * w := by
          calc w * y⁻¹ = y⁻¹ * (y * w) * y⁻¹ := by group
            _ = y⁻¹ * (w * y) * y⁻¹ := by rw [hwy]
            _ = y⁻¹ * w := by group
        calc w * y⁻¹ * (w * y⁻¹) = w * (y⁻¹ * w) * y⁻¹ := by group
          _ = w * (w * y⁻¹) * y⁻¹ := by rw [hwyinv]
          _ = w ^ 2 * (y ^ 2)⁻¹ := by rw [pow_two, pow_two]; group
          _ = 1 := by rw [hw2, hy2, mul_inv_cancel]
      have hwyρ : w * y⁻¹ ∈ zpowers ρ := mul_mem h (inv_mem hyρ)
      have hxy : x * y = y * x := (hg.x_comm_pow _).symm
      rcases hinvρ _ hwyρ hwy2 with h1 | h1
      · have : w = y := by
          calc w = w * y⁻¹ * y := by group
            _ = y := by rw [h1, one_mul]
        rw [hfw, this, hxy]
        simp
      · have : w = r * y := by
          calc w = w * y⁻¹ * y := by group
            _ = r * y := by rw [h1]
        have hrx : r * y = y * r := by
          obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hrρ
          rw [← hj, hy]
          exact (((Commute.refl ρ).zpow_left j).pow_right _).eq
        rw [hfw, this, hrx]
        have : x * (y * r) = y * x * r := by rw [← mul_assoc, hxy]
        rw [this]
        simp
  calc Nat.card F = Nat.card (F : Set G) := rfl
    _ ≤ Nat.card ({1, r, y * x, y * x * r} : Set G) := Nat.card_mono (Set.toFinite _) hsub
    _ ≤ 4 := by
        rw [Nat.card_coe_set_eq]
        refine (Set.ncard_insert_le _ _).trans ?_
        refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
        refine (Nat.add_le_add_right (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1) 1).trans ?_
        rw [Set.ncard_singleton]

end Good

end Lemma37

end CFSG.ComponentClassification.AschbacherKnownGroup
