module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeInner
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveRankTools
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux
import CFSG.LocalAnalysis.ComponentInitial.GroupComponents

public section
namespace CFSG.AGLEmbedding

open CFSG.Open

variable {Y : Type} [Group Y] [Finite Y]

theorem one_le_pRank_three_zpowers {y : Y} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 3 Nat.prime_three _)
    ⟨Subgroup.zpowers y, le_rfl, isElemAbelian_zpowers_three hy3,
      by rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1, pow_one]⟩

theorem pRank_succ_of_mem_component {A L : Subgroup Y}
    (hZ3 : ∀ w ∈ L, w ∈ Subgroup.centralizer (L : Set Y) → IsPGroup 3 (Subgroup.zpowers w) →
      w = 1)
    (hAL : A ≤ Subgroup.centralizer (L : Set Y)) {y : Y} (hyL : y ∈ L) (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) (hyA : y ∈ Subgroup.centralizer (A : Set Y)) :
    CFSG.Open.pRank 3 A + 1 ≤ CFSG.Open.pRank 3 (A ⊔ Subgroup.zpowers y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  refine CFSG.AGLEmbeddingD2.pRank_succ_le_sup_zpowers A hy3 hy1 hyA
    (zpowers_inf_eq_bot_of_not_mem' Nat.prime_three hord fun hyA' =>
      hy1 (hZ3 y hyL (hAL hyA') ?_))
  exact CFSG.AGLEmbedding.isPGroup_zpowers_of_pow_eq_one (k := 1) (by rwa [pow_one])

omit [Finite Y] in
theorem mul_inv_mul_mul_inv {a b c d : Y} (hbc : Commute b c) (hbd : Commute b d) :
    a * (b * c * d)⁻¹ = a * b⁻¹ * (c * d)⁻¹ := by
  have key : Commute b⁻¹ (d⁻¹ * c⁻¹) := hbd.inv_inv.mul_right hbc.inv_inv
  calc a * (b * c * d)⁻¹ = a * ((d⁻¹ * c⁻¹) * b⁻¹) := by group
    _ = a * (b⁻¹ * (d⁻¹ * c⁻¹)) := by rw [key.eq]
    _ = a * b⁻¹ * (c * d)⁻¹ := by group

theorem exists_inner_pow_three_of_coprime {L B A : Subgroup Y}
    (hZ3 : ∀ w ∈ L, w ∈ Subgroup.centralizer (L : Set Y) → IsPGroup 3 (Subgroup.zpowers w) →
      w = 1)
    (hA : IsElemAbelian 3 A) (hAB : A ≤ B) (hAL : A ≤ Subgroup.normalizer (L : Set Y))
    {z : Y} (hzA : z ∈ A) (hzL : z ∉ Subgroup.centralizer (L : Set Y)) {j : Y} (hj : j ∈ L ⊓ B)
    (hzj : z * j⁻¹ ∈ Subgroup.centralizer (L : Set Y)) :
    ∃ y ∈ L ⊓ B, y ∈ Subgroup.centralizer (A : Set Y) ∧
      z * y⁻¹ ∈ Subgroup.centralizer (L : Set Y) ∧ y ^ 3 = 1 ∧ y ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hz3 : z ^ 3 = 1 := hA.2 z hzA
  have hAp : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by rw [pow_one]; exact hA.2 a a.2)⟩
  obtain ⟨c, hcLB, hcA, hzc⟩ := exists_fixed_inner_of_coprime hAp hA.1 hAB hAL
    (fun w hw hwC hw3 => hZ3 w hw.1 hwC
      (CFSG.AGLEmbedding.isPGroup_zpowers_of_pow_eq_one (k := 1) (by rwa [pow_one])))
    hzA hj hzj
  obtain ⟨a, n', hn', hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c).ne' 3
    (by norm_num)
  have hn'3 : Nat.Coprime n' 3 :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp3).mpr hn')
  obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hn'3 (by norm_num)
  set e := n' * m' with he
  set y₀ := c ^ e with hy₀
  have hzpow : ∀ t : ℕ, t % 3 = 1 → z ^ t = z := fun t ht => by
    rw [← Nat.div_add_mod t 3, ht, pow_add, pow_mul, hz3, one_pow, one_mul, pow_one]
  set d := z * c⁻¹ with hd
  have hdc : d * c = c * d := (Subgroup.mem_centralizer_iff.mp hzc c hcLB.1).symm
  have hzy₀ : z * y₀⁻¹ ∈ Subgroup.centralizer (L : Set Y) := by
    have hze : z ^ e = d ^ e * y₀ := by
      have : z = d * c := by rw [hd, inv_mul_cancel_right]
      conv_lhs => rw [this]
      rw [(Commute.mul_pow hdc), hy₀]
    have : z * y₀⁻¹ = d ^ e := by
      rw [← hzpow e hm', hze, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.pow_mem _ hzc e
  have hy₀LB : y₀ ∈ L ⊓ B := Subgroup.pow_mem _ hcLB e
  have hy₀A : y₀ ∈ Subgroup.centralizer (A : Set Y) := Subgroup.pow_mem _ hcA e
  have hy₀3a : y₀ ^ 3 ^ a = 1 := by
    rw [hy₀, ← pow_mul, he, show n' * m' * 3 ^ a = (3 ^ a * n') * m' by ring, pow_mul, ← hk,
      pow_orderOf_eq_one, one_pow]
  have hd'y : (z * y₀⁻¹) * y₀ = y₀ * (z * y₀⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp hzy₀ y₀ hy₀LB.1).symm
  have hy₀3C : y₀ ^ 3 ∈ Subgroup.centralizer (L : Set Y) := by
    have h1 : z ^ 3 = (z * y₀⁻¹) ^ 3 * y₀ ^ 3 := by
      have : z = (z * y₀⁻¹) * y₀ := by rw [inv_mul_cancel_right]
      conv_lhs => rw [this]
      rw [Commute.mul_pow hd'y]
    rw [hz3] at h1
    have : y₀ ^ 3 = ((z * y₀⁻¹) ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h1.symm
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hzy₀ 3)
  have hy₀3 : y₀ ^ 3 = 1 := hZ3 _ (L.pow_mem hy₀LB.1 3) hy₀3C
    (CFSG.AGLEmbedding.isPGroup_zpowers_of_pow_eq_one (k := a) (by
      rw [← pow_mul, mul_comm, pow_mul, hy₀3a, one_pow]))
  have hy₀1 : y₀ ≠ 1 := fun h => hzL (by
    have : z = z * y₀⁻¹ := by rw [h, inv_one, mul_one]
    rw [this]
    exact hzy₀)
  exact ⟨y₀, hy₀LB, hy₀A, hzy₀, hy₀3, hy₀1⟩

theorem eq_mul_mul_of_three_components {L₀ L₁ L₂ B : Subgroup Y}
    (hZ3 : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → ∀ w ∈ L',
      w ∈ Subgroup.centralizer (L' : Set Y) → IsPGroup 3 (Subgroup.zpowers w) → w = 1)
    (hL₀ : IsComponentOf L₀ ⊤) (hL₁ : IsComponentOf L₁ ⊤) (hL₂ : IsComponentOf L₂ ⊤)
    (h01 : L₀ ≠ L₁) (h02 : L₀ ≠ L₂) (h12 : L₁ ≠ L₂) (hB : CFSG.Open.pRank 3 B ≤ 3)
    {y₀ y₁ y₂ z : Y} (hy₀ : y₀ ∈ L₀) (hy₁ : y₁ ∈ L₁) (hy₂ : y₂ ∈ L₂) (hy₀B : y₀ ∈ B)
    (hy₁B : y₁ ∈ B) (hy₂B : y₂ ∈ B) (hzB : z ∈ B) (hy₀3 : y₀ ^ 3 = 1) (hy₁3 : y₁ ^ 3 = 1)
    (hy₂3 : y₂ ^ 3 = 1) (hy₀1 : y₀ ≠ 1) (hy₁1 : y₁ ≠ 1) (hy₂1 : y₂ ≠ 1) (hz3 : z ^ 3 = 1)
    (hzc0 : Commute z y₀) (hzc1 : Commute z y₁) (hzc2 : Commute z y₂)
    (hzy₀ : z * y₀⁻¹ ∈ Subgroup.centralizer (L₀ : Set Y))
    (hzy₁ : z * y₁⁻¹ ∈ Subgroup.centralizer (L₁ : Set Y))
    (hzy₂ : z * y₂⁻¹ ∈ Subgroup.centralizer (L₂ : Set Y)) : z = y₀ * y₁ * y₂ := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hC01 := le_centralizer_of_component_ne hL₀ hL₁ h01
  have hC02 := le_centralizer_of_component_ne hL₀ hL₂ h02
  have hC10 := le_centralizer_of_component_ne hL₁ hL₀ h01.symm
  have hC12 := le_centralizer_of_component_ne hL₁ hL₂ h12
  have hC20 := le_centralizer_of_component_ne hL₂ hL₀ h02.symm
  have hC21 := le_centralizer_of_component_ne hL₂ hL₁ h12.symm
  have hc01 : Commute y₀ y₁ := (Subgroup.mem_centralizer_iff.mp (hC01 hy₀) y₁ hy₁).symm
  have hc02 : Commute y₀ y₂ := (Subgroup.mem_centralizer_iff.mp (hC02 hy₀) y₂ hy₂).symm
  have hc12 : Commute y₁ y₂ := (Subgroup.mem_centralizer_iff.mp (hC12 hy₁) y₂ hy₂).symm
  set T := Subgroup.closure ({z, y₀, y₁, y₂} : Set Y) with hT
  have hTc : IsMulCommutative T := Subgroup.isMulCommutative_closure (by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      first
      | exact Commute.refl _
      | exact hzc0 | exact hzc0.symm | exact hzc1 | exact hzc1.symm | exact hzc2
      | exact hzc2.symm | exact hc01 | exact hc01.symm | exact hc02 | exact hc02.symm
      | exact hc12 | exact hc12.symm)
  have hcommT : ∀ a ∈ T, ∀ b ∈ T, Commute a b := fun a ha b hb =>
    congrArg Subtype.val (hTc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hzT : z ∈ T := Subgroup.subset_closure (by simp)
  have hy₀T : y₀ ∈ T := Subgroup.subset_closure (by simp)
  have hy₁T : y₁ ∈ T := Subgroup.subset_closure (by simp)
  have hy₂T : y₂ ∈ T := Subgroup.subset_closure (by simp)
  have hCT : ∀ {K : Subgroup Y}, K ≤ T → ∀ y ∈ T, y ∈ Subgroup.centralizer (K : Set Y) :=
    fun hKT y hy => Subgroup.mem_centralizer_iff.mpr fun a ha => (hcommT a (hKT ha) y hy).eq
  have hTB : T ≤ B := by
    rw [hT, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact hzB
    · exact hy₀B
    · exact hy₁B
    · exact hy₂B
  have hzpT : ∀ g : Y, Subgroup.zpowers g ≤ T ↔ g ∈ T := fun g => Subgroup.zpowers_le
  by_contra hne
  set c' := z * (y₀ * y₁ * y₂)⁻¹ with hc'
  have hc'1 : c' ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  have hc'T : c' ∈ T := T.mul_mem hzT (T.inv_mem (T.mul_mem (T.mul_mem hy₀T hy₁T) hy₂T))
  have hc'0 : c' = (z * y₀⁻¹) * (y₁ * y₂)⁻¹ := mul_inv_mul_mul_inv hc01 hc02
  have hc'L1 : c' = (z * y₁⁻¹) * (y₀ * y₂)⁻¹ := by
    rw [hc', show y₀ * y₁ * y₂ = y₁ * y₀ * y₂ by rw [hc01.eq]]
    exact mul_inv_mul_mul_inv hc01.symm hc12
  have hc'L2 : c' = (z * y₂⁻¹) * (y₀ * y₁)⁻¹ := by
    rw [hc', show y₀ * y₁ * y₂ = y₂ * y₀ * y₁ by
      rw [mul_assoc y₂, ← (hcommT _ (T.mul_mem hy₀T hy₁T) _ hy₂T).eq]]
    exact mul_inv_mul_mul_inv hc02.symm hc12.symm
  have hcC0 : c' ∈ Subgroup.centralizer (L₀ : Set Y) := by
    rw [hc'0]
    exact Subgroup.mul_mem _ hzy₀ (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hC10 hy₁)
      (hC20 hy₂)))
  have hcC1 : c' ∈ Subgroup.centralizer (L₁ : Set Y) := by
    rw [hc'L1]
    exact Subgroup.mul_mem _ hzy₁ (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hC01 hy₀)
      (hC21 hy₂)))
  have hcC2 : c' ∈ Subgroup.centralizer (L₂ : Set Y) := by
    rw [hc'L2]
    exact Subgroup.mul_mem _ hzy₂ (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hC02 hy₀)
      (hC12 hy₁)))
  have hw3 : (y₀ * y₁ * y₂) ^ 3 = 1 := by
    rw [(hcommT _ (T.mul_mem hy₀T hy₁T) _ hy₂T).mul_pow, hc01.mul_pow, hy₀3, hy₁3, hy₂3,
      one_mul, one_mul]
  have hc'3 : c' ^ 3 = 1 := by
    rw [hc', ((hcommT _ hzT _ (T.mul_mem (T.mul_mem hy₀T hy₁T) hy₂T)).inv_right).mul_pow,
      inv_pow, hw3, inv_one, mul_one, hz3]
  set A₁ := Subgroup.zpowers c' with hA₁
  set A₂ := A₁ ⊔ Subgroup.zpowers y₀ with hA₂
  set A₃ := A₂ ⊔ Subgroup.zpowers y₁ with hA₃
  have hA₁T : A₁ ≤ T := (hzpT c').mpr hc'T
  have hA₂T : A₂ ≤ T := sup_le hA₁T ((hzpT y₀).mpr hy₀T)
  have hA₃T : A₃ ≤ T := sup_le hA₂T ((hzpT y₁).mpr hy₁T)
  have r1 : 1 ≤ CFSG.Open.pRank 3 A₁ := one_le_pRank_three_zpowers hc'3 hc'1
  have r2 : CFSG.Open.pRank 3 A₁ + 1 ≤ CFSG.Open.pRank 3 A₂ :=
    pRank_succ_of_mem_component (A := A₁) (L := L₀) (hZ3 L₀ hL₀)
      (Subgroup.zpowers_le.mpr hcC0) hy₀ hy₀3 hy₀1 (hCT hA₁T y₀ hy₀T)
  have r3 : CFSG.Open.pRank 3 A₂ + 1 ≤ CFSG.Open.pRank 3 A₃ :=
    pRank_succ_of_mem_component (A := A₂) (L := L₁) (hZ3 L₁ hL₁)
      (sup_le (Subgroup.zpowers_le.mpr hcC1) (Subgroup.zpowers_le.mpr (hC01 hy₀))) hy₁ hy₁3
      hy₁1 (hCT hA₂T y₁ hy₁T)
  have r4 : CFSG.Open.pRank 3 A₃ + 1 ≤ CFSG.Open.pRank 3 (A₃ ⊔ Subgroup.zpowers y₂) :=
    pRank_succ_of_mem_component (A := A₃) (L := L₂) (hZ3 L₂ hL₂)
      (sup_le (sup_le (Subgroup.zpowers_le.mpr hcC2) (Subgroup.zpowers_le.mpr (hC02 hy₀)))
        (Subgroup.zpowers_le.mpr (hC12 hy₁))) hy₂ hy₂3 hy₂1 (hCT hA₃T y₂ hy₂T)
  have r5 := CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 hp3
    ((sup_le hA₃T ((hzpT y₂).mpr hy₂T)).trans hTB)
  omega

theorem le_sup_zpowers_of_three_components {L₀ L₁ L₂ B X₀ : Subgroup Y}
    (hZ3 : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → ∀ w ∈ L',
      w ∈ Subgroup.centralizer (L' : Set Y) → IsPGroup 3 (Subgroup.zpowers w) → w = 1)
    (hL₀ : IsComponentOf L₀ ⊤) (hL₁ : IsComponentOf L₁ ⊤) (hL₂ : IsComponentOf L₂ ⊤)
    (h01 : L₀ ≠ L₁) (h02 : L₀ ≠ L₂) (h12 : L₁ ≠ L₂) (hB : CFSG.Open.pRank 3 B ≤ 3)
    {y₀ y₁ y₂ : Y} (hy₀ : y₀ ∈ L₀) (hy₁ : y₁ ∈ L₁) (hy₂ : y₂ ∈ L₂) (hy₀B : y₀ ∈ B)
    (hy₁B : y₁ ∈ B) (hy₂B : y₂ ∈ B) (hy₀3 : y₀ ^ 3 = 1) (hy₁3 : y₁ ^ 3 = 1)
    (hy₂3 : y₂ ^ 3 = 1) (hy₀1 : y₀ ≠ 1) (hy₁1 : y₁ ≠ 1) (hy₂1 : y₂ ≠ 1)
    (hX₀B : X₀ ≤ B) (hX₀p : ∀ w ∈ X₀, w ^ 3 = 1)
    (hX₀y : ∀ w ∈ X₀, Commute w y₀ ∧ Commute w y₁ ∧ Commute w y₂) :
    X₀ ≤ Subgroup.zpowers y₀ ⊔ Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hC01 := le_centralizer_of_component_ne hL₀ hL₁ h01
  have hC02 := le_centralizer_of_component_ne hL₀ hL₂ h02
  have hC12 := le_centralizer_of_component_ne hL₁ hL₂ h12
  have hc01 : Commute y₀ y₁ := (Subgroup.mem_centralizer_iff.mp (hC01 hy₀) y₁ hy₁).symm
  have hc02 : Commute y₀ y₂ := (Subgroup.mem_centralizer_iff.mp (hC02 hy₀) y₂ hy₂).symm
  have hc12 : Commute y₁ y₂ := (Subgroup.mem_centralizer_iff.mp (hC12 hy₁) y₂ hy₂).symm
  set T := Subgroup.closure ({y₀, y₁, y₂} : Set Y) with hT
  have hTc : IsMulCommutative T := Subgroup.isMulCommutative_closure (by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
      | exact Commute.refl _
      | exact hc01 | exact hc01.symm | exact hc02 | exact hc02.symm | exact hc12
      | exact hc12.symm)
  have hcommT : ∀ a ∈ T, ∀ b ∈ T, Commute a b := fun a ha b hb =>
    congrArg Subtype.val (hTc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hy₀T : y₀ ∈ T := Subgroup.subset_closure (by simp)
  have hy₁T : y₁ ∈ T := Subgroup.subset_closure (by simp)
  have hy₂T : y₂ ∈ T := Subgroup.subset_closure (by simp)
  have hCT : ∀ {K : Subgroup Y}, K ≤ T → ∀ y ∈ T, y ∈ Subgroup.centralizer (K : Set Y) :=
    fun hKT y hy => Subgroup.mem_centralizer_iff.mpr fun a ha => (hcommT a (hKT ha) y hy).eq
  have hzpT : ∀ g : Y, Subgroup.zpowers g ≤ T ↔ g ∈ T := fun g => Subgroup.zpowers_le
  set W := Subgroup.zpowers y₀ ⊔ Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ with hW
  have hW01T : Subgroup.zpowers y₀ ⊔ Subgroup.zpowers y₁ ≤ T :=
    sup_le ((hzpT y₀).mpr hy₀T) ((hzpT y₁).mpr hy₁T)
  have hWB : W ≤ B := sup_le (sup_le (Subgroup.zpowers_le.mpr hy₀B)
    (Subgroup.zpowers_le.mpr hy₁B)) (Subgroup.zpowers_le.mpr hy₂B)
  have hW3 : 3 ≤ CFSG.Open.pRank 3 W := by
    have r1 : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers y₀) := one_le_pRank_three_zpowers hy₀3 hy₀1
    have r2 : CFSG.Open.pRank 3 (Subgroup.zpowers y₀) + 1 ≤
        CFSG.Open.pRank 3 (Subgroup.zpowers y₀ ⊔ Subgroup.zpowers y₁) :=
      pRank_succ_of_mem_component (L := L₁) (hZ3 L₁ hL₁) (Subgroup.zpowers_le.mpr (hC01 hy₀))
        hy₁ hy₁3 hy₁1 (hCT ((hzpT y₀).mpr hy₀T) y₁ hy₁T)
    have r3 : CFSG.Open.pRank 3 (Subgroup.zpowers y₀ ⊔ Subgroup.zpowers y₁) + 1 ≤
        CFSG.Open.pRank 3 W :=
      pRank_succ_of_mem_component (L := L₂) (hZ3 L₂ hL₂)
        (sup_le (Subgroup.zpowers_le.mpr (hC02 hy₀)) (Subgroup.zpowers_le.mpr (hC12 hy₁)))
        hy₂ hy₂3 hy₂1 (hCT hW01T y₂ hy₂T)
    omega
  intro w hw
  by_contra hwW
  have hw1 : w ≠ 1 := fun h => hwW (h ▸ W.one_mem)
  obtain ⟨hw0, hw1', hw2⟩ := hX₀y w hw
  have hWw : W ≤ Subgroup.centralizer ({w} : Set Y) := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le] <;>
      rw [Subgroup.mem_centralizer_singleton_iff]
    · exact hw0.eq.symm
    · exact hw1'.eq.symm
    · exact hw2.eq.symm
  have h1 := CFSG.AGLEmbeddingD2.pRank_succ_le_sup_zpowers W (hX₀p w hw) hw1
    (CFSG.LocalAnalysis.ComponentInitial.mem_centralizer_of_le_centralizer_singleton hWw)
    (zpowers_inf_eq_bot_of_not_mem' hp3 (orderOf_eq_prime (hX₀p w hw) hw1) hwW)
  have h2 := CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 hp3
    (sup_le hWB (Subgroup.zpowers_le.mpr (hX₀B hw)))
  omega

theorem zpow_eq_of_three_components {L₀ L₁ L₂ : Subgroup Y}
    (hZ3 : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → ∀ w ∈ L',
      w ∈ Subgroup.centralizer (L' : Set Y) → IsPGroup 3 (Subgroup.zpowers w) → w = 1)
    (hL₀ : IsComponentOf L₀ ⊤) (hL₁ : IsComponentOf L₁ ⊤) (hL₂ : IsComponentOf L₂ ⊤)
    (h01 : L₀ ≠ L₁) (h02 : L₀ ≠ L₂) (h12 : L₁ ≠ L₂) {y₀ y₁ y₂ : Y} (hy₀ : y₀ ∈ L₀)
    (hy₁ : y₁ ∈ L₁) (hy₂ : y₂ ∈ L₂) (hy₀3 : y₀ ^ 3 = 1) (hy₁3 : y₁ ^ 3 = 1)
    {k₀ k₁ k₂ l₀ l₁ l₂ : ℤ} (h : y₀ ^ k₀ * y₁ ^ k₁ * y₂ ^ k₂ = y₀ ^ l₀ * y₁ ^ l₁ * y₂ ^ l₂) :
    y₀ ^ k₀ = y₀ ^ l₀ ∧ y₁ ^ k₁ = y₁ ^ l₁ ∧ y₂ ^ k₂ = y₂ ^ l₂ := by
  have hC10 := le_centralizer_of_component_ne hL₁ hL₀ h01.symm
  have hC20 := le_centralizer_of_component_ne hL₂ hL₀ h02.symm
  have hC21 := le_centralizer_of_component_ne hL₂ hL₁ h12.symm
  have hcube : ∀ (y : Y), y ^ 3 = 1 → ∀ k : ℤ, (y ^ k) ^ 3 = 1 := fun y hy k => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have hp3 : ∀ {g : Y}, g ^ 3 = 1 → IsPGroup 3 (Subgroup.zpowers g) := fun hg =>
    CFSG.AGLEmbedding.isPGroup_zpowers_of_pow_eq_one (k := 1) (by rwa [pow_one])
  have h0 : (y₀ ^ l₀)⁻¹ * y₀ ^ k₀ = (y₁ ^ l₁ * y₂ ^ l₂) * (y₁ ^ k₁ * y₂ ^ k₂)⁻¹ := by
    have h' : y₀ ^ k₀ * (y₁ ^ k₁ * y₂ ^ k₂) = y₀ ^ l₀ * (y₁ ^ l₁ * y₂ ^ l₂) := by
      simpa [mul_assoc] using h
    calc (y₀ ^ l₀)⁻¹ * y₀ ^ k₀ =
          (y₀ ^ l₀)⁻¹ * (y₀ ^ k₀ * (y₁ ^ k₁ * y₂ ^ k₂)) * (y₁ ^ k₁ * y₂ ^ k₂)⁻¹ := by group
      _ = (y₀ ^ l₀)⁻¹ * (y₀ ^ l₀ * (y₁ ^ l₁ * y₂ ^ l₂)) * (y₁ ^ k₁ * y₂ ^ k₂)⁻¹ := by rw [h']
      _ = (y₁ ^ l₁ * y₂ ^ l₂) * (y₁ ^ k₁ * y₂ ^ k₂)⁻¹ := by group
  have hL0 : (y₀ ^ l₀)⁻¹ * y₀ ^ k₀ ∈ L₀ :=
    L₀.mul_mem (L₀.inv_mem (L₀.zpow_mem hy₀ _)) (L₀.zpow_mem hy₀ _)
  have hC0 : (y₀ ^ l₀)⁻¹ * y₀ ^ k₀ ∈ Subgroup.centralizer (L₀ : Set Y) := by
    rw [h0]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) (Subgroup.inv_mem _
      (Subgroup.mul_mem _ ?_ ?_))
    · exact Subgroup.zpow_mem _ (hC10 hy₁) _
    · exact Subgroup.zpow_mem _ (hC20 hy₂) _
    · exact Subgroup.zpow_mem _ (hC10 hy₁) _
    · exact Subgroup.zpow_mem _ (hC20 hy₂) _
  have h3 : ((y₀ ^ l₀)⁻¹ * y₀ ^ k₀) ^ 3 = 1 := by
    rw [← zpow_neg, ← zpow_add]
    exact hcube y₀ hy₀3 _
  have e0 : y₀ ^ k₀ = y₀ ^ l₀ := by
    have := hZ3 L₀ hL₀ _ hL0 hC0 (hp3 h3)
    exact (inv_mul_eq_one.mp this).symm
  have h12' : y₁ ^ k₁ * y₂ ^ k₂ = y₁ ^ l₁ * y₂ ^ l₂ := by
    rw [mul_assoc, mul_assoc, e0] at h
    exact mul_left_cancel h
  have h1' : (y₁ ^ l₁)⁻¹ * y₁ ^ k₁ = y₂ ^ l₂ * (y₂ ^ k₂)⁻¹ := by
    calc (y₁ ^ l₁)⁻¹ * y₁ ^ k₁ = (y₁ ^ l₁)⁻¹ * (y₁ ^ k₁ * y₂ ^ k₂) * (y₂ ^ k₂)⁻¹ := by group
      _ = (y₁ ^ l₁)⁻¹ * (y₁ ^ l₁ * y₂ ^ l₂) * (y₂ ^ k₂)⁻¹ := by rw [h12']
      _ = y₂ ^ l₂ * (y₂ ^ k₂)⁻¹ := by group
  have hL1 : (y₁ ^ l₁)⁻¹ * y₁ ^ k₁ ∈ L₁ :=
    L₁.mul_mem (L₁.inv_mem (L₁.zpow_mem hy₁ _)) (L₁.zpow_mem hy₁ _)
  have hC1 : (y₁ ^ l₁)⁻¹ * y₁ ^ k₁ ∈ Subgroup.centralizer (L₁ : Set Y) := by
    rw [h1']
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (hC21 hy₂) _)
      (Subgroup.inv_mem _ (Subgroup.zpow_mem _ (hC21 hy₂) _))
  have h3' : ((y₁ ^ l₁)⁻¹ * y₁ ^ k₁) ^ 3 = 1 := by
    rw [← zpow_neg, ← zpow_add]
    exact hcube y₁ hy₁3 _
  have e1 : y₁ ^ k₁ = y₁ ^ l₁ := by
    have := hZ3 L₁ hL₁ _ hL1 hC1 (hp3 h3')
    exact (inv_mul_eq_one.mp this).symm
  refine ⟨e0, e1, ?_⟩
  rw [e1] at h12'
  exact mul_left_cancel h12'

end CFSG.AGLEmbedding
