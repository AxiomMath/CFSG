module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47Prop27
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem_of_lt {H U : Subgroup G} (hU : IsPGroup 2 U) (hHU : H < U) :
    ∃ u ∈ U, u ∉ H ∧ u ∈ normalizer (H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent U := hU.isNilpotent
  have hlt : H.subgroupOf U < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hHU.ne
    apply le_antisymm hHU.le
    intro x hx
    have h1 : (⟨x, hx⟩ : U) ∈ H.subgroupOf U := htop ▸ mem_top _
    exact mem_subgroupOf.mp h1
  obtain ⟨u, hu, hnot⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  exact ⟨u, u.2, fun h => hnot (mem_subgroupOf.mpr h),
    mem_normalizer_of_subgroupOf hHU.le hu⟩

omit [Finite G] in
theorem conj_eq_mul_sq_of_inv {y c : G} (hy : y * y = 1) (hc : y * c * y = c⁻¹) :
    c⁻¹ * y * c = y * (c * c) := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : y * c⁻¹ * y = c := by
    have h2 : (y * c * y)⁻¹ = y * c⁻¹ * y := by rw [mul_inv_rev, mul_inv_rev, hyi, mul_assoc]
    rw [← h2, hc, inv_inv]
  calc c⁻¹ * y * c = (y * y) * c⁻¹ * y * c := by rw [hy, one_mul]
    _ = y * (y * c⁻¹ * y) * c := by group
    _ = y * (c * c) := by rw [h1, mul_assoc]

omit [Finite G] in
theorem exists_conj_mul_of_not_commute {Q : Subgroup G} (hQ : IsPGroup 2 Q) {y : G}
    (hy : y * y = 1) (hyQ : y ∈ normalizer (Q : Set G)) (hnc : ∃ q ∈ Q, q * y ≠ y * q) :
    ∃ w ∈ Q, w ≠ 1 ∧ w * y = y * w ∧ ∃ c ∈ Q, c⁻¹ * y * c = y * w := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  obtain ⟨q, hq, hqy⟩ := hnc
  set w₀ := y * q⁻¹ * y * q with hw₀
  have hw₀Q : w₀ ∈ Q := by
    have h1 := (mem_normalizer_iff.mp hyQ _).mp (inv_mem hq)
    rw [hyi] at h1
    exact mul_mem h1 hq
  have hw₀1 : w₀ ≠ 1 := fun h1 => hqy (by
    have h2 : q⁻¹ * y * q = y := by
      calc q⁻¹ * y * q = y * (y * q⁻¹ * y * q) := by
            rw [show y * (y * q⁻¹ * y * q) = (y * y) * q⁻¹ * y * q by group, hy, one_mul]
        _ = y := by rw [← hw₀, h1, mul_one]
    calc q * y = q * (q⁻¹ * y * q) := by rw [h2]
      _ = y * q := by group)
  have hinv : ∀ c ∈ zpowers w₀, y * c * y = c⁻¹ := by
    have h0 : y * w₀ * y = w₀⁻¹ := by
      rw [hw₀, show y * (y * q⁻¹ * y * q) * y = (y * y) * q⁻¹ * y * q * y by group, hy,
        one_mul, mul_inv_rev, mul_inv_rev, mul_inv_rev, hyi, inv_inv]
      group
    rintro _ ⟨k, rfl⟩
    have h1 : y * w₀ ^ k * y = (y * w₀ * y) ^ k := by
      calc y * w₀ ^ k * y = y * w₀ ^ k * y⁻¹ := by rw [hyi]
        _ = (y * w₀ * y⁻¹) ^ k := conj_zpow.symm
        _ = (y * w₀ * y) ^ k := by rw [hyi]
    rw [h1, h0, inv_zpow]
  have hw₀y : y * q⁻¹ * y * q = w₀ := rfl
  have hconj : q⁻¹ * y * q = y * w₀ := by
    rw [hw₀, show y * (y * q⁻¹ * y * q) = (y * y) * q⁻¹ * y * q by group, hy, one_mul]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨w₀, hw₀Q⟩
  rw [Subgroup.orderOf_mk] at hk
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  ·
    have hk1 : k = 1 := by
      rcases k with _ | _ | k
      · rw [pow_zero, orderOf_eq_one_iff] at hk
        exact absurd hk hw₀1
      · rfl
      · omega
    have hw₀2 : w₀ * w₀ = 1 := by rw [← sq, ← pow_one 2, ← hk1, ← hk, pow_orderOf_eq_one]
    have hw₀i : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right hw₀2
    refine ⟨w₀, hw₀Q, hw₀1, ?_, q, hq, hconj⟩
    have h1 := hinv w₀ (mem_zpowers w₀)
    rw [hw₀i] at h1
    calc w₀ * y = y * (y * w₀ * y) := by
          rw [show y * (y * w₀ * y) = (y * y) * w₀ * y by group, hy, one_mul]
      _ = y * w₀ := by rw [h1]
  ·
    set c := w₀ ^ (2 ^ (k - 2)) with hc
    have hcQ : c ∈ Q := pow_mem hw₀Q _
    have hcord : orderOf c = 4 := by
      rw [hc, orderOf_pow_of_dvd (by positivity) (by rw [hk]; exact Nat.pow_dvd_pow 2 (by omega)),
        hk, Nat.pow_div (by omega) (by norm_num), show k - (k - 2) = 2 by omega]
    have hcy := hinv c (pow_mem (mem_zpowers w₀) _)
    have hc4 : c ^ 4 = 1 := by rw [← hcord, pow_orderOf_eq_one]
    have hcc1 : c * c ≠ 1 := by
      intro h1
      have h2 := orderOf_dvd_of_pow_eq_one (show c ^ 2 = 1 by rw [sq]; exact h1)
      rw [hcord] at h2
      norm_num at h2
    refine ⟨c * c, mul_mem hcQ hcQ, hcc1, ?_, c, hcQ, conj_eq_mul_sq_of_inv hy hcy⟩
    have h1 : y * (c * c) * y = c⁻¹ * c⁻¹ := by
      rw [show y * (c * c) * y = (y * c * y) * (y * c * y) by
        rw [show (y * c * y) * (y * c * y) = y * c * (y * y) * c * y by group, hy]; group, hcy]
    have h2 : c⁻¹ * c⁻¹ = c * c := by
      have h3 : c * c * (c * c) = 1 := by
        rw [← hc4]
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [← mul_inv_rev, inv_eq_of_mul_eq_one_right h3]
    calc c * c * y = y * (y * (c * c) * y) := by
          rw [show y * (y * (c * c) * y) = (y * y) * (c * c) * y by group, hy, one_mul]
      _ = y * (c * c) := by rw [h1, h2]

theorem oddCore_eq_bot_of_simple [IsSimpleGroup G] {t : G} (ht : orderOf t = 2) :
    oddCore G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (oddCore G) with h | h
  · exact h
  · exact absurd (h ▸ mem_top t) (Adapters.not_mem_oddCore_of_orderOf_eq_two ht)

theorem isSylowOf_top_of_isolated {t : G} (ht : orderOf t = 2) {P : Subgroup G}
    (hP : IsSylowOf 2 P (centralizer ({t} : Set G))) (hiso : ∀ x ∈ P, IsConj t x → x = t) :
    IsSylowOf 2 P ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  obtain ⟨S, hS, hPS⟩ := exists_isSylowOf_ge_of_le (le_top : P ≤ ⊤) hP.isPGroup
  have hlt : P < S := lt_of_le_of_ne hPS fun h => hnot (h ▸ hS)
  obtain ⟨s, hsS, hsP, hsN⟩ := exists_mem_normalizer_not_mem_of_lt hS.isPGroup hlt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htP : t ∈ P := Foote47.mem_of_isSylowOf ht2 hP
  have h1 : s * t * s⁻¹ ∈ P := (mem_normalizer_iff.mp hsN t).mp htP
  have h2 := hiso _ h1 (isConj_iff.mpr ⟨s, rfl⟩)
  have hsC : s ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr (by
    calc s * t = s * t * s⁻¹ * s := by group
      _ = t * s := by rw [h2])
  have hs2 : IsPGroup 2 (zpowers s) := hS.isPGroup.to_le (zpowers_le.mpr hsS)
  have hp : IsPGroup 2 ↥(P ⊔ zpowers s) :=
    hP.isPGroup.to_sup_of_normal_left' hs2 (zpowers_le.mpr hsN)
  have heq := hP.eq_of_le le_sup_left (sup_le hP.le (zpowers_le.mpr hsC)) hp
  exact hsP (heq ▸ mem_sup_right (mem_zpowers s))

theorem exists_conj_mem_ne [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a) {t : G}
    (ht : orderOf t = 2) {P : Subgroup G} (hP : IsSylowOf 2 P (centralizer ({t} : Set G)))
    (t' : G) : ∃ x ∈ P, IsConj t x ∧ x ≠ t ∧ x ≠ t' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  have hno' : ∀ x ∈ P, IsConj t x → x = t ∨ x = t' := by
    intro x hx hc
    by_contra h
    push Not at h
    exact hno ⟨x, hx, hc, h.1, h.2⟩
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht; omega
  have htP : t ∈ P := Foote47.mem_of_isSylowOf ht2 hP
  by_cases ht' : t' ∈ P ∧ IsConj t t' ∧ t' ≠ t
  · obtain ⟨Psyl, hPsyl⟩ := hP
    have hiff : ∀ x : G, (x ∈ (Psyl : Subgroup _).map (centralizer ({t} : Set G)).subtype ∧
        IsConj t x) ↔ x = t ∨ x = t' := by
      intro x
      rw [hPsyl]
      constructor
      · rintro ⟨hx, hc⟩
        exact hno' x hx hc
      · rintro (rfl | rfl)
        · exact ⟨htP, IsConj.refl _⟩
        · exact ⟨ht'.1, ht'.2.1⟩
    have hnot := footeThompsonFusion_holds G t t' ht Psyl hiff
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (normalClosure ({t * t'} : Set G)) with
      h1 | h1
    · have h2 : t * t' ∈ normalClosure ({t * t'} : Set G) :=
        subset_normalClosure (Set.mem_singleton _)
      rw [h1, mem_bot] at h2
      apply ht'.2.2
      calc t' = t * (t * t') := by rw [← mul_assoc, ht2, one_mul]
        _ = t := by rw [h2, mul_one]
    · exact hnot (h1 ▸ mem_top t)
  · have hiso : ∀ x ∈ P, IsConj t x → x = t := by
      intro x hx hc
      rcases hno' x hx hc with h1 | h1
      · exact h1
      · by_contra hxt
        exact ht' ⟨h1 ▸ hx, h1 ▸ hc, h1 ▸ hxt⟩
    have hPG := isSylowOf_top_of_isolated ht hP hiso
    obtain ⟨-, hSp, hidx⟩ := isSylowOf_iff.mp hPG
    rw [Subgroup.relIndex_top_right] at hidx
    set S' := hSp.toSylow hidx with hS'
    have hS'P : (S' : Subgroup G) = P := IsPGroup.toSylow_coe hSp hidx
    have htS' : t ∈ (S' : Subgroup G) := hS'P ▸ htP
    have hzZ : (⟨t, htS'⟩ : (S' : Subgroup G)) ∈ center (S' : Subgroup G) := by
      rw [mem_center_iff]
      intro s
      apply Subtype.ext
      have hsP : (s : G) ∈ P := hS'P ▸ s.2
      exact mem_centralizer_singleton_iff.mp (hP.le hsP)
    have hzord : orderOf (⟨t, htS'⟩ : (S' : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact ht
    obtain ⟨hcov, -⟩ := Adapters.glauberman_zStar S' ⟨t, htS'⟩ hzZ hzord fun g hg =>
      hiso _ (hS'P ▸ hg) (isConj_iff.mpr ⟨g⁻¹, by group⟩)
    have hO := oddCore_eq_bot_of_simple ht
    have htZ : t ∈ center G := by
      rw [mem_center_iff]
      intro g
      obtain ⟨c, hc, k, hk, rfl⟩ := hcov g
      rw [hO, mem_bot] at hk
      rw [hk, mul_one]
      exact mem_centralizer_singleton_iff.mp hc
    rw [center_eq_bot_of_isSimpleGroup hna, mem_bot] at htZ
    exact ht1 htZ

end CFSG.ComponentClassification.Foote5
