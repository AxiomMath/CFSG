module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_15Two
public import CFSG.GH74.GLS.Stage2.Final.L26.Pair

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L20

open Subgroup CFSG CFSG.ABGLocalTools

section Cnt

variable {G : Type} [Group G]

theorem card_sup_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hd : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  let φ : ↥A × ↥B →* G :=
    { toFun := fun p => (p.1 : G) * p.2
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        have h1 := h q.1 q.1.2 p.2 p.2.2
        calc (p.1 : G) * q.1 * ((p.2 : G) * q.2) = p.1 * (q.1 * p.2) * q.2 := by group
          _ = p.1 * (p.2 * q.1) * q.2 := by rw [h1]
          _ = ((p.1 : G) * p.2) * ((q.1 : G) * q.2) := by group }
  have hinj : Function.Injective φ := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
    have hab' : a * b = a' * b' := hab
    have h1 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [hab']
        _ = b' * b⁻¹ := by group
    have hmemA : a'⁻¹ * a ∈ A := A.mul_mem (A.inv_mem ha') ha
    have hmemB : a'⁻¹ * a ∈ B := by rw [h1]; exact B.mul_mem hb' (B.inv_mem hb)
    have hbot : a'⁻¹ * a ∈ (⊥ : Subgroup G) := by rw [← hd]; exact ⟨hmemA, hmemB⟩
    rw [Subgroup.mem_bot] at hbot
    have haa : a = a' := (inv_mul_eq_one.mp hbot).symm
    subst haa
    have : b' * b⁻¹ = 1 := by rw [← h1, hbot]
    have hbb : b = b' := (mul_inv_eq_one.mp this).symm
    subst hbb
    rfl
  have hrange : φ.range = A ⊔ B := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
    · refine sup_le ?_ ?_
      · intro a ha
        exact ⟨(⟨a, ha⟩, 1), by simp [φ]⟩
      · intro b hb
        exact ⟨(1, ⟨b, hb⟩), by simp [φ]⟩
  calc Nat.card ↥(A ⊔ B) = Nat.card ↥φ.range := by rw [hrange]
    _ = Nat.card (↥A × ↥B) := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _


theorem elementary_sup {A B : Subgroup G} (hA : ∀ a ∈ A, a * a = 1) (hB : ∀ b ∈ B, b * b = 1)
    (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    (∀ x ∈ A ⊔ B, x * x = 1) ∧ (∀ x ∈ A ⊔ B, ∀ x' ∈ A ⊔ B, x * x' = x' * x) := by
  have hdec : ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, x = a * b := fun x hx =>
    CFSG.GH74.GLS.Stage2.Final.L26.exists_mul_of_mem_sup_of_commute h hx
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
    have hba : b * a = a * b := (h a ha b hb).symm
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hba]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [hA a ha, hB b hb, one_mul]
  · intro x hx x' hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hdec x' hx'
    have h1 : b * a' = a' * b := (h a' ha' b hb).symm
    have h2 : b' * a = a * b' := (h a ha b' hb').symm
    have e1 : a * b * (a' * b') = (a * a') * (b * b') := by
      calc a * b * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [h1]
        _ = (a * a') * (b * b') := by group
    have e2 : a' * b' * (a * b) = (a' * a) * (b' * b) := by
      calc a' * b' * (a * b) = a' * (b' * a) * b := by group
        _ = a' * (a * b') * b := by rw [h2]
        _ = (a' * a) * (b' * b) := by group
    rw [e1, e2, hAc a ha a' ha', hBc b hb b' hb']


theorem count16 {z c : G} {S R : Subgroup G} (hSR : ∀ a ∈ S, ∀ b ∈ S, a ∉ R → b ∉ R → a⁻¹ * b ∈ R)
    (hzR : ∀ w ∈ R, w * w = 1 → IsConj z w → w = z) {X Y : Subgroup G}
    (hX2 : ∀ x ∈ X, x * x = 1) (hY2 : ∀ y ∈ Y, y * y = 1) (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hbot : ∀ g ∈ X, g ∈ Y → g = 1) (hXS : ∀ x ∈ X, c * x * c⁻¹ ∈ S) (hYS : ∀ y ∈ Y, c * y * c⁻¹ ∈ S)
    (hX3 : ∃ x₁ ∈ X, ∃ x₂ ∈ X, x₁ ≠ 1 ∧ x₂ ≠ 1 ∧ x₁ ≠ x₂)
    (hY3 : ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, y₁ ≠ 1 ∧ y₂ ≠ 1 ∧ y₁ ≠ y₂)
    (hmix : ∀ x ∈ X, ∀ y ∈ Y, x ≠ 1 → y ≠ 1 → IsConj z (x * y)) : False := by
  have hinvX : ∀ x ∈ X, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hX2 x hx)
  have hinvY : ∀ y ∈ Y, y⁻¹ = y := fun y hy => inv_eq_of_mul_eq_one_right (hY2 y hy)
  have hconjc : ∀ a b : G, c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := fun a b => by group
  have hcinj : ∀ a b : G, c * a * c⁻¹ = c * b * c⁻¹ → a = b := fun a b h => by
    calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
      _ = c⁻¹ * (c * b * c⁻¹) * c := by rw [h]
      _ = b := by group
  have hexX : ∃ x₀ ∈ X, x₀ ≠ 1 ∧ c * x₀ * c⁻¹ ∈ R := by
    obtain ⟨x₁, hx₁, x₂, hx₂, h1, h2, h12⟩ := hX3
    by_cases hr₁ : c * x₁ * c⁻¹ ∈ R
    · exact ⟨x₁, hx₁, h1, hr₁⟩
    by_cases hr₂ : c * x₂ * c⁻¹ ∈ R
    · exact ⟨x₂, hx₂, h2, hr₂⟩
    refine ⟨x₁ * x₂, X.mul_mem hx₁ hx₂, ?_, ?_⟩
    · intro h
      apply h12
      have : x₁⁻¹ = x₂ := inv_eq_of_mul_eq_one_right h
      rw [← this, hinvX x₁ hx₁]
    · have := hSR _ (hXS x₁ hx₁) _ (hXS x₂ hx₂) hr₁ hr₂
      have e : (c * x₁ * c⁻¹)⁻¹ * (c * x₂ * c⁻¹) = c * (x₁⁻¹ * x₂) * c⁻¹ := by group
      rw [e, hinvX x₁ hx₁] at this
      exact this
  have hexY : ∃ y₀ ∈ Y, y₀ ≠ 1 ∧ c * y₀ * c⁻¹ ∈ R := by
    obtain ⟨y₁, hy₁, y₂, hy₂, h1, h2, h12⟩ := hY3
    by_cases hr₁ : c * y₁ * c⁻¹ ∈ R
    · exact ⟨y₁, hy₁, h1, hr₁⟩
    by_cases hr₂ : c * y₂ * c⁻¹ ∈ R
    · exact ⟨y₂, hy₂, h2, hr₂⟩
    refine ⟨y₁ * y₂, Y.mul_mem hy₁ hy₂, ?_, ?_⟩
    · intro h
      apply h12
      have : y₁⁻¹ = y₂ := inv_eq_of_mul_eq_one_right h
      rw [← this, hinvY y₁ hy₁]
    · have := hSR _ (hYS y₁ hy₁) _ (hYS y₂ hy₂) hr₁ hr₂
      have e : (c * y₁ * c⁻¹)⁻¹ * (c * y₂ * c⁻¹) = c * (y₁⁻¹ * y₂) * c⁻¹ := by group
      rw [e, hinvY y₁ hy₁] at this
      exact this
  obtain ⟨x₀, hx₀, hx₀1, hx₀R⟩ := hexX
  obtain ⟨y₀, hy₀, hy₀1, hy₀R⟩ := hexY
  have hmixR : ∀ x ∈ X, ∀ y ∈ Y, x ≠ 1 → y ≠ 1 → c * (x * y) * c⁻¹ ∈ R → c * (x * y) * c⁻¹ = z := by
    intro x hx y hy hx1 hy1 hR
    refine hzR _ hR ?_ ?_
    · have e : c * (x * y) * c⁻¹ * (c * (x * y) * c⁻¹) = c * ((x * y) * (x * y)) * c⁻¹ := by group
      rw [e]
      have : (x * y) * (x * y) = 1 := by
        calc (x * y) * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [← hXY x hx y hy]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hX2 x hx, hY2 y hy, one_mul]
      rw [this]; group
    · exact (hmix x hx y hy hx1 hy1).trans (isConj_iff.mpr ⟨c, rfl⟩)
  have hd₀ := hmixR x₀ hx₀ y₀ hy₀ hx₀1 hy₀1 (by rw [hconjc]; exact R.mul_mem hx₀R hy₀R)
  have hinj : ∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y, ∀ y' ∈ Y, x * y = x' * y' → x = x' := by
    intro x hx x' hx' y hy y' hy' h
    have h1 : x'⁻¹ * x = y' * y⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
        _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [h]
        _ = y' * y⁻¹ := by group
    have h2 : x'⁻¹ * x ∈ Y := by rw [h1]; exact Y.mul_mem hy' (Y.inv_mem hy)
    have h3 := hbot _ (X.mul_mem (X.inv_mem hx') hx) h2
    exact (inv_mul_eq_one.mp h3).symm
  have hinj' : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ x ∈ X, ∀ x' ∈ X, x * y = x' * y' → y = y' := by
    intro y hy y' hy' x hx x' hx' h
    have hxx := hinj x hx x' hx' y hy y' hy' h
    subst hxx
    exact mul_left_cancel h
  obtain ⟨x', hx', hx'1, hx'0⟩ : ∃ x' ∈ X, x' ≠ 1 ∧ x' ≠ x₀ := by
    obtain ⟨x₁, hx₁, x₂, hx₂, h1, h2, h12⟩ := hX3
    by_cases h : x₁ = x₀
    · exact ⟨x₂, hx₂, h2, fun h' => h12 (h.trans h'.symm)⟩
    · exact ⟨x₁, hx₁, h1, h⟩
  obtain ⟨y', hy', hy'1, hy'0⟩ : ∃ y' ∈ Y, y' ≠ 1 ∧ y' ≠ y₀ := by
    obtain ⟨y₁, hy₁, y₂, hy₂, h1, h2, h12⟩ := hY3
    by_cases h : y₁ = y₀
    · exact ⟨y₂, hy₂, h2, fun h' => h12 (h.trans h'.symm)⟩
    · exact ⟨y₁, hy₁, h1, h⟩
  by_cases hx'R : c * x' * c⁻¹ ∈ R
  · have h1 := hmixR x' hx' y₀ hy₀ hx'1 hy₀1 (by rw [hconjc]; exact R.mul_mem hx'R hy₀R)
    have h3 : x' * y₀ = x₀ * y₀ := hcinj _ _ (h1.trans hd₀.symm)
    exact hx'0 (hinj x' hx' x₀ hx₀ y₀ hy₀ y₀ hy₀ h3)
  · by_cases hy'R : c * y' * c⁻¹ ∈ R
    · have h1 := hmixR x₀ hx₀ y' hy' hx₀1 hy'1 (by rw [hconjc]; exact R.mul_mem hx₀R hy'R)
      have h3 : x₀ * y' = x₀ * y₀ := hcinj _ _ (h1.trans hd₀.symm)
      exact hy'0 (hinj' y' hy' y₀ hy₀ x₀ hx₀ x₀ hx₀ h3)
    · have hR : c * (x' * y') * c⁻¹ ∈ R := by
        have := hSR _ (hXS x' hx') _ (hYS y' hy') hx'R hy'R
        have e : (c * x' * c⁻¹)⁻¹ * (c * y' * c⁻¹) = c * (x'⁻¹ * y') * c⁻¹ := by group
        rw [e, hinvX x' hx'] at this
        exact this
      have h1 := hmixR x' hx' y' hy' hx'1 hy'1 hR
      have h3 : x' * y' = x₀ * y₀ := hcinj _ _ (h1.trans hd₀.symm)
      exact hx'0 (hinj x' hx' x₀ hx₀ y' hy' y₀ hy₀ h3)

section Sylow

variable [Finite G]

theorem exists_conj_le_sylow {S D : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hD : IsPGroup 2 D) :
    ∃ c : G, ∀ d ∈ D, c * d * c⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp := isSylowOf_iff.mp hS
  have hidx : ¬ 2 ∣ S.index := by
    have := hSp.2.2
    rwa [Subgroup.relIndex_top_right] at this
  let S' : Sylow 2 G := hSp.2.1.toSylow hidx
  obtain ⟨Q, hQ⟩ := hD.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S'
  refine ⟨g, fun d hd => ?_⟩
  have hsm : g * d * g⁻¹ ∈ (g • Q : Sylow 2 G) := (Sylow.equivSMul Q g ⟨d, hQ hd⟩).property
  rw [hg] at hsm
  exact hsm


theorem le_pRank_of_elem {E : Subgroup G} (hE : IsElementaryAbelian 2 E) {k : ℕ} (hk : Nat.card E = 2 ^ k) :
    k ≤ pRank 2 G := by
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, hE, hk⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group B

omit [Finite G] in
theorem mem_zpowers_involution {t : G} (ht2 : t * t = 1) {b : G} (hb : b ∈ zpowers t) : b = 1 ∨ b = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht2
  have hk : t ^ k = t ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [hk, h]; simp
  · right; rw [hk, h]; simp

theorem central_involution_mem_D (hrank : pRank 2 G ≤ 4) {X Y : Subgroup G}
    (hX2 : ∀ x ∈ X, x * x = 1) (hY2 : ∀ y ∈ Y, y * y = 1) (hXc : ∀ x ∈ X, ∀ x' ∈ X, x * x' = x' * x)
    (hYc : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y) (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hbot : ∀ g ∈ X, g ∈ Y → g = 1) (hXcard : Nat.card X = 4) (hYcard : Nat.card Y = 4) :
    ∃ t ∈ X ⊔ Y, t * t = 1 ∧ t ≠ 1 ∧ ∃ T : Sylow 2 G, t ∈ (T : Subgroup G) ∧ ∀ s ∈ (T : Subgroup G), s * t = t * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXYbot : X ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    exact Subgroup.mem_bot.mpr (hbot g hg.1 hg.2)
  obtain ⟨hD2, hDc⟩ := elementary_sup hX2 hY2 hXc hYc hXY
  have hDcard : Nat.card ↥(X ⊔ Y) = 16 := by
    rw [card_sup_commute hXY hXYbot, hXcard, hYcard]
  have hDp : IsPGroup 2 ↥(X ⊔ Y) := fun d => ⟨1, by
    apply Subtype.ext
    show (d : G) ^ (2 ^ 1) = 1
    rw [pow_one, sq]
    exact hD2 d d.2⟩
  obtain ⟨T, hT⟩ := hDp.exists_le_sylow
  have hTcard : 16 ≤ Nat.card (T : Subgroup G) := by
    rw [← hDcard]; exact Subgroup.card_le_of_le hT
  obtain ⟨t, htT, htc, ht2, ht1⟩ := exists_central_involution T.isPGroup' (by omega)
  by_cases htD : t ∈ X ⊔ Y
  · exact ⟨t, htD, ht2, ht1, T, htT, htc⟩
  exfalso
  have hB2 : ∀ b ∈ zpowers t, b * b = 1 := fun b hb => by
    rcases mem_zpowers_involution ht2 hb with rfl | rfl
    · simp
    · exact ht2
  have hBc : ∀ b ∈ zpowers t, ∀ b' ∈ zpowers t, b * b' = b' * b := fun b hb b' hb' => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
    rw [← zpow_add, ← zpow_add, add_comm]
  have hDB : ∀ a ∈ X ⊔ Y, ∀ b ∈ zpowers t, a * b = b * a := fun a ha b hb => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hcomm : Commute a t := htc a (hT ha)
    exact (hcomm.zpow_right k).eq
  obtain ⟨hE2, hEc⟩ := elementary_sup hD2 hB2 hDc hBc hDB
  have hDBbot : (X ⊔ Y) ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rcases mem_zpowers_involution ht2 hg.2 with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hg.1 htD
  have hEcard : Nat.card ↥((X ⊔ Y) ⊔ zpowers t) = 2 ^ 5 := by
    rw [card_sup_commute hDB hDBbot, hDcard, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact ht2) ht1]
    norm_num
  have hEA : IsElementaryAbelian 2 ↥((X ⊔ Y) ⊔ zpowers t) := by
    refine { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hEc a a.2 b b.2)⟩⟩, exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => ?_
    apply Subtype.ext
    show (a : G) ^ 2 = 1
    rw [sq]; exact hE2 a a.2
  have := le_pRank_of_elem hEA hEcard
  omega

end Sylow

end Cnt

end CFSG.GH74.GLS.Stage2.Final.Thm6.L20
