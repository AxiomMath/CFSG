module

public import CFSG.CGT.PushingUpLit.T2KR.Count4
public import CFSG.CGT.Timmesfeld75.Involutions
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.JonesParshall CFSG.CGT.Timmesfeld75
open scoped commutatorElement LinearAlgebra.Projectivization
open MData (QM)

section SL2

variable {F : Type} [Field F]

theorem diag_conj_unipotent (a s : F) (ha : a ≠ 0) :
    ∃ d : Matrix.SpecialLinearGroup (Fin 2) F,
      d * CFSG.SL2MinimalFaithful.unipotent s * d⁻¹ =
        CFSG.SL2MinimalFaithful.unipotent (a ^ 2 * s) := by
  obtain ⟨d, hd⟩ : ∃ d : Matrix.SpecialLinearGroup (Fin 2) F,
      (d : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, a⁻¹] :=
    ⟨⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, ha]⟩, rfl⟩
  refine ⟨d, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hd,
    CFSG.SL2MinimalFaithful.coe_unipotent, CFSG.SL2MinimalFaithful.coe_unipotent]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

end SL2

theorem sl2_involution_form {n : ℕ} (hn : n ≠ 0)
    {g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)} (hg1 : g ≠ 1) (hg2 : g * g = 1) :
    ∃ (x₀ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) (s : Fq n), s ≠ 0 ∧
      x₀ * CFSG.SL2MinimalFaithful.unipotent s * x₀⁻¹ = g := by
  have hX : ∀ x ∈ Subgroup.zpowers g, x * x = 1 := by
    rintro _ ⟨k, rfl⟩
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hg2, one_zpow]
  obtain ⟨p, hp⟩ := exists_rootGrp_le (f := n) (GaloisField.card 2 n hn) hX
  obtain ⟨x₀, hx₀⟩ := exists_smul_pt0 p
  have hgp : g ∈ rootGrp p := hp (Subgroup.mem_zpowers g)
  rw [← hx₀, mem_rootGrp_smul_iff, rootGrp_pt0] at hgp
  obtain ⟨t, ht⟩ := hgp
  refine ⟨x₀, t.toAdd, ?_, ?_⟩
  · intro h0
    apply hg1
    have : CFSG.SL2MinimalFaithful.unipotentHom t = 1 := by
      have : CFSG.SL2MinimalFaithful.unipotentHom t = CFSG.SL2MinimalFaithful.unipotent t.toAdd := rfl
      rw [this, h0]
      apply Subtype.ext
      simp [CFSG.SL2MinimalFaithful.coe_unipotent, Matrix.one_fin_two]
    rw [this] at ht
    have : g = x₀ * 1 * x₀⁻¹ := by
      rw [show (1 : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) = x₀⁻¹ * g * x₀ from ht]
      group
    simpa using this
  · have ht' : CFSG.SL2MinimalFaithful.unipotent t.toAdd = x₀⁻¹ * g * x₀ := ht
    rw [ht']
    group

theorem sl2_involutions_conj {n : ℕ} (hn : n ≠ 0)
    {g₁ g₂ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)} (h₁ : g₁ ≠ 1) (h₂ : g₂ ≠ 1)
    (h₁2 : g₁ * g₁ = 1) (h₂2 : g₂ * g₂ = 1) :
    ∃ c : Matrix.SpecialLinearGroup (Fin 2) (Fq n), c * g₁ * c⁻¹ = g₂ := by
  obtain ⟨x₁, s₁, hs₁, e₁⟩ := sl2_involution_form hn h₁ h₁2
  obtain ⟨x₂, s₂, hs₂, e₂⟩ := sl2_involution_form hn h₂ h₂2
  have hchar : ringChar (Fq n) = 2 := ringChar.eq (Fq n) 2
  obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two hchar (s₂ / s₁)
  have ha0 : a ≠ 0 := by
    rintro rfl
    have : s₂ / s₁ = 0 := by rw [ha]; ring
    rcases div_eq_zero_iff.1 this with h | h
    · exact hs₂ h
    · exact hs₁ h
  have hsq : a ^ 2 * s₁ = s₂ := by
    have : s₂ = a * a * s₁ := by
      have := ha
      field_simp at this
      linear_combination this
    rw [this]; ring
  obtain ⟨d, hd⟩ := diag_conj_unipotent a s₁ ha0
  rw [hsq] at hd
  refine ⟨x₂ * d * x₁⁻¹, ?_⟩
  rw [← e₁, ← e₂, ← hd]
  group

namespace MData

variable {G : Type} [Group G] [Finite G] {L M : Subgroup G} {n : ℕ} (H : MData G L M n)

include H in
theorem card_CV_of_involution {β : G} (hβM : β ∈ M) (hβ2 : β * β = 1) (hβQ : β ∉ QM L M) :
    Nat.card ↥(blockU L ⊓ Subgroup.centralizer ({β} : Set G)) = Nat.card (Fq n) := by
  by_cases hLQ : β ∈ L ⊔ QM L M
  · have hX : Subgroup.zpowers β ≤ L ⊔ QM L M := (Subgroup.zpowers_le).2 hLQ
    have hX2 : ∀ x ∈ Subgroup.zpowers β, x * x = 1 := by
      rintro _ ⟨k, rfl⟩
      rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hβ2, one_zpow]
    have hne : ¬ Subgroup.zpowers β ≤ QM L M := fun h => hβQ (h (Subgroup.mem_zpowers β))
    have := H.card_CV_eq (Subgroup.zpowers β) hX hX2 hne
    rwa [centralizer_zpowers_eq] at this
  · have hb2 : (⟨β, hβM⟩ : ↥M) * ⟨β, hβM⟩ = 1 := Subtype.ext hβ2
    exact H.card_CV_involution (b := ⟨β, hβM⟩) hb2 (H.chi_ne_one_of_not_mem hb2 hLQ)

include H in
theorem exists_conj_of_involution_mem_coset {β : G} (hβM : β ∈ M) (hβ2 : β * β = 1)
    (hβQ : β ∉ QM L M) {t : G} (ht : t ∈ blockU L) (hbt : (β * t) ^ 2 = 1) :
    ∃ s ∈ blockU L, β * t = s⁻¹ * β * s := by
  have hT : CFSG.Open.IsElemAbelian 2 (blockU L) := H.nat.isElemAbelian_blockU
  have hβ2' : β ^ 2 = 1 := by rw [pow_two]; exact hβ2
  have hN : β ∈ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_blockU (H.normal hβM) hy, fun hy => ?_⟩
    have := conj_mem_blockU (H.normal (M.inv_mem hβM)) hy
    simpa [mul_assoc] using this
  have h1 := card_commSub_mul_card_centralizer hT hβ2' hN
  have h2 := H.card_CV_of_involution hβM hβ2 hβQ
  have h3 := H.card_V
  have hq : 0 < Nat.card (Fq n) := Nat.card_pos
  have hcomm : Nat.card ↥(commSub β (blockU L)) = Nat.card (Fq n) := by
    rw [h2, h3] at h1
    exact Nat.eq_of_mul_eq_mul_right hq (h1.trans (sq _))
  have := (card_commSub_eq_iff hT hβ2' hN).1 (hcomm.trans h2.symm) t ht hbt
  exact this

include H in
theorem exists_conj_of_involution_in_L (hQL : QM L M ⊓ L ≤ blockU L) {ε y : G} (hεL : ε ∈ L)
    (hε2 : ε * ε = 1) (hεM : ε ∈ M) (hεQ : ε ∉ QM L M) (hyL : y ∈ L) (hy2 : y * y = 1)
    (hyV : y ∉ blockU L) : ∃ c ∈ L, y = c⁻¹ * ε * c := by
  have hLLQ : L ≤ L ⊔ QM L M := le_sup_left
  have hyQ : y ∉ QM L M := fun h => hyV (hQL ⟨h, hyL⟩)
  set ρy := H.rho ⟨y, hLLQ hyL⟩ with hρy
  set ρε := H.rho ⟨ε, hLLQ hεL⟩ with hρε
  have hρy1 : ρy ≠ 1 := fun h => hyQ ((H.rho_eq_one_iff _).1 h)
  have hρε1 : ρε ≠ 1 := fun h => hεQ ((H.rho_eq_one_iff _).1 h)
  have hρy2 : ρy * ρy = 1 := by
    rw [hρy, ← map_mul]
    have : (⟨y, hLLQ hyL⟩ : ↥(L ⊔ QM L M)) * ⟨y, hLLQ hyL⟩ = 1 := Subtype.ext hy2
    rw [this, map_one]
  have hρε2 : ρε * ρε = 1 := by
    rw [hρε, ← map_mul]
    have : (⟨ε, hLLQ hεL⟩ : ↥(L ⊔ QM L M)) * ⟨ε, hLLQ hεL⟩ = 1 := Subtype.ext hε2
    rw [this, map_one]
  obtain ⟨c₀, hc₀⟩ := sl2_involutions_conj H.n_ne_zero hρy1 hρε1 hρy2 hρε2
  obtain ⟨l, hl, hρl⟩ := H.rho_surj_L c₀
  set y' := l * y * l⁻¹ with hy'
  have hy'L : y' ∈ L := L.mul_mem (L.mul_mem hl hyL) (L.inv_mem hl)
  have hy'2 : y' * y' = 1 := by
    have : y' * y' = l * (y * y) * l⁻¹ := by rw [hy']; group
    rw [this, hy2]; group
  have hρy' : H.rho ⟨y', hLLQ hy'L⟩ = ρε := by
    have : (⟨y', hLLQ hy'L⟩ : ↥(L ⊔ QM L M)) =
        ⟨l, hLLQ hl⟩ * ⟨y, hLLQ hyL⟩ * ⟨l, hLLQ hl⟩⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hρl, ← hρy]
    exact hc₀
  have hkerV : ε⁻¹ * y' ∈ blockU L := by
    apply hQL
    refine ⟨?_, L.mul_mem (L.inv_mem hεL) hy'L⟩
    have : H.rho ⟨ε⁻¹ * y', hLLQ (L.mul_mem (L.inv_mem hεL) hy'L)⟩ = 1 := by
      have e : (⟨ε⁻¹ * y', hLLQ (L.mul_mem (L.inv_mem hεL) hy'L)⟩ : ↥(L ⊔ QM L M)) =
          ⟨ε, hLLQ hεL⟩⁻¹ * ⟨y', hLLQ hy'L⟩ := Subtype.ext rfl
      rw [e, map_mul, map_inv, hρy', ← hρε, inv_mul_cancel]
    exact (H.rho_eq_one_iff _).1 this
  obtain ⟨t, ht, hεt⟩ : ∃ t ∈ blockU L, y' = ε * t := ⟨ε⁻¹ * y', hkerV, by group⟩
  have hbt : (ε * t) ^ 2 = 1 := by rw [pow_two, ← hεt]; exact hy'2
  obtain ⟨s, hs, hεs⟩ := H.exists_conj_of_involution_mem_coset hεM hε2 hεQ ht hbt
  have hsL : s ∈ L := CFSG.CGT.PushingUpLit.blockU_le L hs
  refine ⟨s * l, L.mul_mem hsL hl, ?_⟩
  have : y = l⁻¹ * y' * l := by rw [hy']; group
  rw [this, hεt, hεs]
  group

end MData

end CFSG.CGT.PushingUpLit.T2KR
