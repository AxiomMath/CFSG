module

import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_RankAux
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_RankAuxComm
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped commutatorElement

theorem zjr_mem_normalizer_center {Y : Type*} [Group Y] {R : Subgroup Y} {g : Y}
    (hg : g ∈ normalizer (R : Set Y)) :
    g ∈ normalizer ((R ⊓ centralizer (R : Set Y) : Subgroup Y) : Set Y) := by
  have key : ∀ k : Y, k ∈ normalizer (R : Set Y) → ∀ h : Y, h ∈ R ⊓ centralizer (R : Set Y) →
      k * h * k⁻¹ ∈ R ⊓ centralizer (R : Set Y) := by
    intro k hk h hh
    obtain ⟨hhR, hhc⟩ := mem_inf.1 hh
    refine mem_inf.2 ⟨(mem_normalizer_iff.1 hk h).1 hhR, ?_⟩
    rw [mem_centralizer_iff]
    intro r hr
    have hr' : k⁻¹ * r * k ∈ R := by
      have := (mem_normalizer_iff.1 (inv_mem hk) r).1 hr
      simpa using this
    have := mem_centralizer_iff.1 hhc _ hr'
    calc r * (k * h * k⁻¹) = k * ((k⁻¹ * r * k) * h) * k⁻¹ := by group
      _ = k * (h * (k⁻¹ * r * k)) * k⁻¹ := by rw [this]
      _ = (k * h * k⁻¹) * r := by group
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun h1 => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ h1
  simpa [mul_assoc] using this

theorem zjr_main {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Type*} [Group Y] [Finite Y]
    {D R : Subgroup Y} (hDp : ∀ d ∈ D, d ^ p = 1) (hDc : Nat.card D = p ^ 2)
    (hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDR : D ≤ normalizer (R : Set Y))
    (hfaith : D ⊓ centralizer (R : Set Y) = ⊥) (hexp : ∀ x ∈ R, x ^ 3 = 1)
    (hcl : ⁅R, R⁆ ≤ centralizer (R : Set Y)) :
    ∃ A : Subgroup Y, A ≤ R ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ x ∈ A, x ^ 3 = 1) ∧
      3 ^ 4 ≤ Nat.card A := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : p ≠ 3 := by omega
  have hR3 : IsPGroup 3 R := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  by_cases hab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a
  · exact ⟨R, le_rfl, hab, hexp, zjr_three_pow_four_le_card hp hp5 hDp hDc hR3 hDR hfaith⟩
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy⟩ : ∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x := by
    by_contra h
    exact hab fun a ha b hb => by
      by_contra hne
      exact h ⟨a, ha, b, hb, hne⟩
  set Z : Subgroup Y := R ⊓ centralizer (R : Set Y) with hZdef
  have hZR : Z ≤ R := inf_le_left
  have hZc : ∀ z ∈ Z, ∀ b ∈ R, z * b = b * z := fun z hz b hb =>
    (mem_centralizer_iff.1 (mem_inf.1 hz).2 b hb).symm
  have hZ3 : IsPGroup 3 Z := hR3.to_le hZR
  have hx₀Z : x₀ ∉ Z := fun h => hxy (mem_centralizer_iff.1 (mem_inf.1 h).2 y₀ hy₀).symm
  have hZnt : 3 ≤ Nat.card Z := by
    have hx₀1 : x₀ ≠ 1 := by
      rintro rfl
      exact hxy (by simp)
    have : Nontrivial R := ⟨⟨⟨x₀, hx₀⟩, 1, fun h => hx₀1 (congrArg Subtype.val h)⟩⟩
    have : Nontrivial (center R) := hR3.center_nontrivial
    obtain ⟨c, hc⟩ := exists_ne (1 : center R)
    have hcZ : ((c : R) : Y) ∈ Z := by
      refine mem_inf.2 ⟨(c : R).2, mem_centralizer_iff.2 fun h hh => ?_⟩
      exact congrArg Subtype.val (mem_center_iff.1 c.2 ⟨h, hh⟩)
    obtain ⟨k, hk⟩ := hZ3.exists_card_eq
    rw [hk]
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, card_eq_one] at hk
      apply hc
      apply Subtype.ext
      apply Subtype.ext
      have := hk ▸ hcZ
      simpa using this
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hk0)
  by_cases hZ27 : 27 ≤ Nat.card Z
  · have hAR : Z ⊔ zpowers x₀ ≤ R := sup_le hZR ((zpowers_le).2 hx₀)
    have hZA : Z < Z ⊔ zpowers x₀ :=
      lt_of_le_of_ne le_sup_left fun h => hx₀Z (h ▸ mem_sup_right (mem_zpowers x₀))
    refine ⟨Z ⊔ zpowers x₀, hAR, ?_, fun x hx => hexp x (hAR hx), ?_⟩
    · exact zjr_comm_sup (fun a ha b hb => hZc a ha b (hZR hb)) (zjr_comm_zpowers x₀)
        (fun a ha b hb => hZc a ha b ((zpowers_le).2 hx₀ hb))
    · have := zjr_three_mul_card_le (hR3.to_le hAR) hZA
      omega
  have hZD : ∀ a ∈ D, Z ≤ centralizer ({a} : Set Y) := by
    intro a ha
    by_contra hnc
    have h27 := zjr_card_fixed_mul_le hp hp5 hZ3 (hDp a ha) (zjr_mem_normalizer_center (hDR ha))
      hnc
    have hpos : 0 < Nat.card (Z ⊓ centralizer ({a} : Set Y) : Subgroup Y) := Nat.card_pos
    omega
  obtain ⟨a₁, ha₁D, ha₁1, a₂, ha₂D, ha₂n, h₁, h₂⟩ := zjr_exists_pair hp hp3 hDp hDc hR3 hDR hfaith
  have ha₁p : a₁ ^ p = 1 := hDp a₁ ha₁D
  have ha₂p : a₂ ^ p = 1 := hDp a₂ ha₂D
  have hn₁ : a₁ ∈ normalizer (R : Set Y) := hDR ha₁D
  have hn₂ : a₂ ∈ normalizer (R : Set Y) := hDR ha₂D
  have h12 : a₁ * a₂ = a₂ * a₁ := hDcomm a₁ ha₁D a₂ ha₂D
  have ha₂1 : a₂ ≠ 1 := fun h => ha₂n (h ▸ one_mem _)
  have ha₁n : a₁ ∉ zpowers a₂ := by
    intro h
    have hle : zpowers a₁ ≤ zpowers a₂ := (zpowers_le).2 h
    have heq : zpowers a₁ = zpowers a₂ := Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime ha₂p ha₂1,
        orderOf_eq_prime ha₁p ha₁1])
    exact ha₂n (heq ▸ mem_zpowers a₂)
  have hZa₁ := hZD a₁ ha₁D
  have hZa₂ := hZD a₂ ha₂D
  set S₁ : Subgroup Y := R ⊓ centralizer ({a₁} : Set Y) with hS₁
  set S₂ : Subgroup Y := R ⊓ centralizer ({a₂} : Set Y) with hS₂
  set B₁ : Subgroup Y := ⁅S₁, zpowers a₂⁆ with hB₁
  set B₂ : Subgroup Y := ⁅S₂, zpowers a₁⁆ with hB₂
  have hcomm : ⁅B₁, B₂⁆ = ⊥ := zjr_comm_B_pair hn₂ h12 hcl hZa₁
  have hnc₁ : ¬ B₁ ≤ centralizer ({a₂} : Set Y) :=
    zjr_B_not_centralized hp hp3 hR3 ha₂p hn₂ h12 ha₂n (h₁ a₂ ha₂D)
  have hnc₂ : ¬ B₂ ≤ centralizer ({a₁} : Set Y) :=
    zjr_B_not_centralized hp hp3 hR3 ha₁p hn₁ h12.symm ha₁n (h₂ a₁ ha₁D)
  have hnormS₁ : zpowers a₂ ≤ normalizer (S₁ : Set Y) := by
    rw [zpowers_le]
    exact zjr_mem_normalizer_inf_centralizer hn₂ h12.symm
  have hnormS₂ : zpowers a₁ ≤ normalizer (S₂ : Set Y) := by
    rw [zpowers_le]
    exact zjr_mem_normalizer_inf_centralizer hn₁ h12
  have hB₁S₁ : B₁ ≤ S₁ := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ _ hnormS₁
  have hB₂S₂ : B₂ ≤ S₂ := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ _ hnormS₂
  have hB₂N : B₂ ≤ ⁅R, zpowers a₁⁆ := commutator_mono inf_le_left le_rfl
  have hNS : ⁅R, zpowers a₁⁆ ⊓ S₁ ≤ Z := zjr_comm_inf_centralizer_le hp hp3 hR3 ha₁p hn₁ hcl hZa₁
  set U : Subgroup Y := Z ⊔ B₁ with hU
  have hUS₁ : U ≤ S₁ := sup_le (le_inf hZR hZa₁) hB₁S₁
  have hUR : U ≤ R := hUS₁.trans inf_le_left
  have hZU : Z ≤ U := le_sup_left
  have hB₁U : B₁ ≤ U := le_sup_right
  have hnormB₁ : a₂ ∈ normalizer (B₁ : Set Y) :=
    CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized _ _ hnormS₁ (mem_zpowers a₂)
  have hnormU : a₂ ∈ normalizer (U : Set Y) :=
    inf_normalizer_le_normalizer_sup Z B₁ ⟨zjr_mem_normalizer_center hn₂, hnormB₁⟩
  have hnU : ¬ U ≤ centralizer ({a₂} : Set Y) := fun h => hnc₁ (hB₁U.trans h)
  have hUcard := zjr_card_fixed_mul_le hp hp5 (hR3.to_le hUR) ha₂p hnormU hnU
  have hZUc : Nat.card Z ≤ Nat.card (U ⊓ centralizer ({a₂} : Set Y) : Subgroup Y) :=
    Subgroup.card_le_of_le (le_inf hZU hZa₂)
  have hU27 : 27 * Nat.card Z ≤ Nat.card U := by omega
  obtain ⟨M, hMU, hZM, hMcomm, hM27⟩ := zjr_exists_abelian_ambient hZU
    (fun b hb => hexp b (hUR hb)) (fun z hz b hb => hZc z hz b (hUR hb))
    (fun b hb b' hb' => mem_inf.2 ⟨zjr_commutator_le_self R
      (commutator_mem_commutator (hUR hb) (hUR hb')),
      hcl (commutator_mem_commutator (hUR hb) (hUR hb'))⟩) hZnt hU27
  obtain ⟨x₂, hx₂B, hx₂Z⟩ : ∃ x ∈ B₂, x ∉ Z := by
    by_contra h
    exact hnc₂ fun x hx => hZa₁ (by
      by_contra hxZ
      exact h ⟨x, hx, hxZ⟩)
  have hx₂R : x₂ ∈ R := (hB₂S₂ hx₂B |> fun h => (mem_inf.1 h).1)
  have hx₂U : x₂ ∉ U := fun h => hx₂Z (hNS ⟨hB₂N hx₂B, hUS₁ h⟩)
  have hUx₂ : ∀ u ∈ U, u * x₂ = x₂ * u := by
    have : U ≤ centralizer ({x₂} : Set Y) := by
      refine sup_le (fun z hz => ?_) (fun b hb => ?_)
      · rw [zjr_mem_centralizer_singleton]
        exact (hZc z hz x₂ hx₂R).symm
      · have h1 : b ∈ centralizer ((B₂ : Subgroup Y) : Set Y) :=
          commutator_eq_bot_iff_le_centralizer.1 hcomm hb
        rw [zjr_mem_centralizer_singleton]
        exact (mem_centralizer_iff.1 h1 x₂ hx₂B)
    intro u hu
    exact (zjr_mem_centralizer_singleton.1 (this hu)).symm
  have hAR : M ⊔ zpowers x₂ ≤ R := sup_le (hMU.trans hUR) ((zpowers_le).2 hx₂R)
  have hMA : M < M ⊔ zpowers x₂ :=
    lt_of_le_of_ne le_sup_left fun h => hx₂U (hMU (h ▸ mem_sup_right (mem_zpowers x₂)))
  refine ⟨M ⊔ zpowers x₂, hAR, ?_, fun x hx => hexp x (hAR hx), ?_⟩
  · refine zjr_comm_sup hMcomm (zjr_comm_zpowers x₂) ?_
    intro a ha b hb
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (show Commute a x₂ from hUx₂ a (hMU ha)) n).eq
  · have := zjr_three_mul_card_le (hR3.to_le hAR) hMA
    omega

theorem exists_isElemAbelian_card_three_pow_four {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {Y : Type} [Group Y] [Finite Y] {D Q : Subgroup Y} (hD : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) (hQ : IsPGroup 3 Q) (hDQ : D ≤ normalizer (Q : Set Y))
    (hfaith : D ⊓ centralizer (Q : Set Y) = ⊥) :
    ∃ A : Subgroup Y, A ≤ Q ∧ IsElemAbelian 3 A ∧ 3 ^ 4 ≤ Nat.card A := by
  have : IsMulCommutative D := hD.1
  obtain ⟨R, hRQ, hDR, hRfaith, hexp, hcl⟩ := zjr_exists_reduction hp hp5 hD.2 hQ hDQ hfaith
  obtain ⟨A, hAR, hAcomm, hAexp, hA⟩ := zjr_main hp hp5 hD.2 hDc
    (fun a ha b hb => congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : D) ⟨b, hb⟩))
    hDR hRfaith hexp hcl
  exact ⟨A, hAR.trans hRQ, ⟨⟨⟨fun a b => Subtype.ext (hAcomm a a.2 b b.2)⟩⟩, hAexp⟩, hA⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
