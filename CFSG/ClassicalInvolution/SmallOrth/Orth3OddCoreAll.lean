module

public import CFSG.ClassicalInvolution.SmallOrth.Orth3OddCore
public import CFSG.ClassicalInvolution.SmallOrth.PlusFourMain
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Small

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap CFSG.ClassicalInvolution.Q3 CFSG.ComponentClassification
open scoped MatrixGroups

variable {K : Type} {V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eq_one_of_mem_elementaryGroup_of_finrank_le_two [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (hdim : Module.finrank K V ≤ 2) {g : V ≃ₗ[K] V}
    (hg : g ∈ elementaryGroup Q) : g = 1 := by
  have : elementaryGroup Q ≤ ⊥ := by
    apply elementaryGroup_le_of_eichler_mem
    intro u w hu hw
    rw [eichler_eq_one_of_finrank_le_two hQ hdim hu hw]
    exact one_mem _
  simpa using this hg

theorem exists_mul_of_mem_sup_of_commute {G : Type*} [Group G] {L R : Subgroup G}
    (hcomm : ∀ l ∈ L, ∀ r ∈ R, l * r = r * l) {x : G} (hx : x ∈ L ⊔ R) :
    ∃ l ∈ L, ∃ r ∈ R, x = l * r := by
  let M : Subgroup G :=
    { carrier := {x | ∃ l ∈ L, ∃ r ∈ R, x = l * r}
      mul_mem' := by
        rintro _ _ ⟨l₁, hl₁, r₁, hr₁, rfl⟩ ⟨l₂, hl₂, r₂, hr₂, rfl⟩
        refine ⟨l₁ * l₂, mul_mem hl₁ hl₂, r₁ * r₂, mul_mem hr₁ hr₂, ?_⟩
        have := hcomm l₂ hl₂ r₁ hr₁
        calc l₁ * r₁ * (l₂ * r₂) = l₁ * (r₁ * l₂) * r₂ := by group
          _ = l₁ * (l₂ * r₁) * r₂ := by rw [this]
          _ = l₁ * l₂ * (r₁ * r₂) := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨l, hl, r, hr, rfl⟩
        refine ⟨l⁻¹, inv_mem hl, r⁻¹, inv_mem hr, ?_⟩
        have := hcomm l⁻¹ (inv_mem hl) r hr
        calc (l * r)⁻¹ = r⁻¹ * l⁻¹ := by group
          _ = l⁻¹ * r⁻¹ := by
            have h2 : r⁻¹ * l⁻¹ = (l * r)⁻¹ := by group
            rw [h2, show l * r = r * l from (hcomm l hl r hr), mul_inv_rev] }
  exact (sup_le (fun l hl => ⟨l, hl, 1, one_mem _, (mul_one l).symm⟩)
    (fun r hr => ⟨1, one_mem _, r, hr, (one_mul r).symm⟩) : L ⊔ R ≤ M) hx

theorem comap_eq_bot_of_odd_normal {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3)
    {G : Type*} [Group G] (θ : SL(2, F) →* G) (hθ : Function.Injective θ) (N : Subgroup G)
    [N.Normal] (hodd : Odd (Nat.card N)) : N.comap θ = ⊥ := by
  have hdvd : Nat.card (N.comap θ) ∣ Nat.card N :=
    Subgroup.card_dvd_of_injective (θ.subgroupComap N)
      (fun x y h => Subtype.ext (hθ (congrArg Subtype.val h)))
  have hnorm : (N.comap θ).Normal := inferInstance
  have h1 := OddCore.maximal SL(2, F) (N.comap θ) hnorm (Odd.of_dvd_nat hodd hdvd)
  rw [componentOddCore_sl2_eq_bot hF] at h1
  exact le_bot_iff.mp h1

theorem central_sq_eq_one {F : Type} [Field F] {A : SL(2, F)}
    (hA : ∀ X : SL(2, F), X * A * X⁻¹ * A⁻¹ = 1) : A ^ 2 = 1 := by
  have hcen : A ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := hA g
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
  have hr' : r ^ 2 = 1 := by simpa using hr
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrA, ← map_pow, hr', map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem eq_one_of_mul_self_eq_one_of_odd {G : Type*} [Group G] (N : Subgroup G)
    (hodd : Odd (Nat.card N)) {n : G} (hn : n ∈ N) (h : n * n = 1) : n = 1 := by
  set m : N := ⟨n, hn⟩ with hm
  have hm2 : m ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using h)
  have h1 : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one hm2
  have h2 : Odd (orderOf m) := Odd.of_dvd_nat hodd (orderOf_dvd_natCard m)
  have h3 : orderOf m = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd h2 (by decide)
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h3)

section PlusFour

variable [FiniteDimensional K V] {P P' : HypPair Q} (h : P.Orth P')
  (hdim : Module.finrank K V = 4)

theorem thetaL_commutator_formula (X A B : SL(2, K)) :
    thetaL h hdim (X * A * X⁻¹ * A⁻¹) =
      thetaL h hdim X * (thetaL h hdim A * thetaR h hdim B) * (thetaL h hdim X)⁻¹ *
        (thetaL h hdim A * thetaR h hdim B)⁻¹ := by
  have c1 : thetaR h hdim B * (thetaL h hdim X)⁻¹ = (thetaL h hdim X)⁻¹ * thetaR h hdim B := by
    rw [← map_inv]
    exact (thetaL_thetaR_comm h hdim X⁻¹ B).symm
  simp only [map_mul, map_inv]
  calc thetaL h hdim X * thetaL h hdim A * (thetaL h hdim X)⁻¹ * (thetaL h hdim A)⁻¹
      = thetaL h hdim X * thetaL h hdim A * ((thetaL h hdim X)⁻¹ * thetaR h hdim B) *
        (thetaR h hdim B)⁻¹ * (thetaL h hdim A)⁻¹ := by group
    _ = thetaL h hdim X * thetaL h hdim A * (thetaR h hdim B * (thetaL h hdim X)⁻¹) *
        (thetaR h hdim B)⁻¹ * (thetaL h hdim A)⁻¹ := by rw [c1]
    _ = _ := by group

theorem thetaR_commutator_formula (A Y B : SL(2, K)) :
    thetaR h hdim (Y * B * Y⁻¹ * B⁻¹) =
      thetaR h hdim Y * (thetaL h hdim A * thetaR h hdim B) * (thetaR h hdim Y)⁻¹ *
        (thetaL h hdim A * thetaR h hdim B)⁻¹ := by
  have c1 : thetaL h hdim A * thetaR h hdim Y = thetaR h hdim Y * thetaL h hdim A :=
    thetaL_thetaR_comm h hdim A Y
  have c3 := (thetaL_thetaR_comm h hdim A (Y * B * Y⁻¹ * B⁻¹)).symm
  simp only [map_mul, map_inv] at c3 ⊢
  calc thetaR h hdim Y * thetaR h hdim B * (thetaR h hdim Y)⁻¹ * (thetaR h hdim B)⁻¹
      = (thetaR h hdim Y * thetaR h hdim B * (thetaR h hdim Y)⁻¹ * (thetaR h hdim B)⁻¹ *
        thetaL h hdim A) * (thetaL h hdim A)⁻¹ := by group
    _ = (thetaL h hdim A * (thetaR h hdim Y * thetaR h hdim B * (thetaR h hdim Y)⁻¹ *
        (thetaR h hdim B)⁻¹)) * (thetaL h hdim A)⁻¹ := by rw [c3]
    _ = (thetaL h hdim A * thetaR h hdim Y) * thetaR h hdim B * (thetaR h hdim Y)⁻¹ *
        (thetaR h hdim B)⁻¹ * (thetaL h hdim A)⁻¹ := by group
    _ = (thetaR h hdim Y * thetaL h hdim A) * thetaR h hdim B * (thetaR h hdim Y)⁻¹ *
        (thetaR h hdim B)⁻¹ * (thetaL h hdim A)⁻¹ := by rw [c1]
    _ = _ := by group

include h hdim in
theorem eq_bot_of_odd_normal_plusFour [Finite K] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (N : Subgroup (elementaryGroup Q)) [hN : N.Normal]
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have hE := elementaryGroup_eq_sup h hdim hQ
  have hcomm : ∀ l ∈ (thetaL h hdim).range, ∀ r ∈ (thetaR h hdim).range, l * r = r * l := by
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact thetaL_thetaR_comm h hdim A B
  let θL : SL(2, K) →* elementaryGroup Q :=
    (thetaL h hdim).codRestrict _ (thetaL_mem_elementaryGroup h hdim)
  let θR : SL(2, K) →* elementaryGroup Q :=
    (thetaR h hdim).codRestrict _ (thetaR_mem_elementaryGroup h hdim)
  have hθL : Function.Injective θL := fun A B hAB =>
    thetaL_injective h hdim (congrArg Subtype.val hAB)
  have hθR : Function.Injective θR := fun A B hAB =>
    thetaR_injective h hdim (congrArg Subtype.val hAB)
  have hN1 := comap_eq_bot_of_odd_normal hK θL hθL N hodd
  have hN2 := comap_eq_bot_of_odd_normal hK θR hθR N hodd
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hnmem : (n : V ≃ₗ[K] V) ∈ (thetaL h hdim).range ⊔ (thetaR h hdim).range := by
    rw [← hE]
    exact n.2
  obtain ⟨_, ⟨A, rfl⟩, _, ⟨B, rfl⟩, hnlr⟩ := exists_mul_of_mem_sup_of_commute hcomm hnmem
  have hA : ∀ X : SL(2, K), X * A * X⁻¹ * A⁻¹ = 1 := by
    intro X
    have hmem : (X * A * X⁻¹ * A⁻¹) ∈ N.comap θL := by
      rw [Subgroup.mem_comap]
      have h1 : θL (X * A * X⁻¹ * A⁻¹) = θL X * n * (θL X)⁻¹ * n⁻¹ := by
        apply Subtype.ext
        show thetaL h hdim (X * A * X⁻¹ * A⁻¹) = _
        rw [thetaL_commutator_formula h hdim X A B]
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hnlr]
        rfl
      rw [h1]
      exact N.mul_mem (hN.conj_mem n hn (θL X)) (N.inv_mem hn)
    rw [hN1] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hB : ∀ Y : SL(2, K), Y * B * Y⁻¹ * B⁻¹ = 1 := by
    intro Y
    have hmem : (Y * B * Y⁻¹ * B⁻¹) ∈ N.comap θR := by
      rw [Subgroup.mem_comap]
      have h1 : θR (Y * B * Y⁻¹ * B⁻¹) = θR Y * n * (θR Y)⁻¹ * n⁻¹ := by
        apply Subtype.ext
        show thetaR h hdim (Y * B * Y⁻¹ * B⁻¹) = _
        rw [thetaR_commutator_formula h hdim A Y B]
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hnlr]
        rfl
      rw [h1]
      exact N.mul_mem (hN.conj_mem n hn (θR Y)) (N.inv_mem hn)
    rw [hN2] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hA2 := central_sq_eq_one hA
  have hB2 := central_sq_eq_one hB
  have hnn : n * n = 1 := by
    apply Subtype.ext
    have hc := thetaL_thetaR_comm h hdim A B
    have e1 : thetaL h hdim A * thetaL h hdim A = 1 := by rw [← map_mul, ← pow_two, hA2, map_one]
    have e2 : thetaR h hdim B * thetaR h hdim B = 1 := by rw [← map_mul, ← pow_two, hB2, map_one]
    show (n : V ≃ₗ[K] V) * n = 1
    rw [hnlr]
    calc thetaL h hdim A * thetaR h hdim B * (thetaL h hdim A * thetaR h hdim B)
        = thetaL h hdim A * (thetaR h hdim B * thetaL h hdim A) * thetaR h hdim B := by group
      _ = thetaL h hdim A * (thetaL h hdim A * thetaR h hdim B) * thetaR h hdim B := by rw [hc]
      _ = (thetaL h hdim A * thetaL h hdim A) * (thetaR h hdim B * thetaR h hdim B) := by group
      _ = 1 := by rw [e1, e2, one_mul]
  exact eq_one_of_mul_self_eq_one_of_odd N hodd hn hnn

end PlusFour

theorem three_eq_zero_two_ne_zero_of_card_eq_three [Finite K] (hK : Nat.card K = 3) :
    (3 : K) = 0 ∧ (2 : K) ≠ 0 := by
  have h3 : (3 : K) = 0 := by
    have : Fintype K := Fintype.ofFinite K
    have h := Nat.cast_card_eq_zero K
    rw [← Nat.card_eq_fintype_card, hK] at h
    exact_mod_cast h
  refine ⟨h3, fun h => ?_⟩
  have : (1 : K) = 0 := by linear_combination h3 - h
  exact one_ne_zero this

open CFSG.ComponentClassification.CatalogueBOddQuadratic in
theorem eq_bot_of_odd_normal_of_card_three [Finite K] [FiniteDimensional K V]
    (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate) (N : Subgroup (elementaryGroup Q))
    [N.Normal] (hodd : Odd (Nat.card N)) : N = ⊥ := by
  obtain ⟨h3, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  have hodd3 : Odd (Nat.card K) := by rw [hK]; decide
  by_cases hd : Module.finrank K V ≤ 2
  · rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    exact Subtype.ext (eq_one_of_mem_elementaryGroup_of_finrank_le_two hQ hd n.2)
  push Not at hd
  have hA : HasAnisoPerp Q := hasAnisoPerp_of_three_le_finrank hQ (by omega)
  by_cases hW : ∃ P P' : HypPair Q, P.Orth P'
  · obtain ⟨P, P', hP⟩ := hW
    by_cases h4 : Module.finrank K V = 4
    · exact eq_bot_of_odd_normal_plusFour hP h4 hK hQ N hodd
    · have h5 : 5 ≤ Module.finrank K V := by
        have := four_le_finrank_of_orth hP
        omega
      obtain ⟨P₂, h₁₂⟩ := exists_orth_hypPair_of_five_le_finrank hodd3 hQ h5 P
      have hdim' : 3 ≤ Module.finrank K P.perp := by
        have := finrank_le_two_add_finrank_perp P
        omega
      have hA' : HasAnisoPerp (Q.restrict P.perp) :=
        hasAnisoPerp_of_three_le_finrank
          (nondegenerate_polarBilin_restrict (P.polarNondegOn_perp hQ)) hdim'
      exact eq_bot_of_odd_normal h3 h2 hA P
        (isPreprimitive_singularLines_of_orth h₁₂ hQ hA hA') N hodd
  · push Not at hW
    obtain ⟨v, hv0, hvQ⟩ := exists_isotropic_of_three_le hodd3 Q hQ (by omega)
    obtain ⟨P₀, -⟩ := exists_hypPair hQ hvQ hv0
    exact eq_bot_of_odd_normal h3 h2 hA P₀
      (isPreprimitive_singularLines_of_noOrth hQ hA (fun P P' => hW P P') P₀) N hodd

end CFSG.ClassicalGroups.Orthogonal.Small
