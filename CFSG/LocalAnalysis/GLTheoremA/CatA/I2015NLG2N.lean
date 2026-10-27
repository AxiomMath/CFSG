module

public import CFSG.RankThree.PartOne.S11c.Sec66G2Sub

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.Sec66T

theorem g2N_two_pow_arith {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ 3 ∣ 2 ^ p ∧ ¬ 3 ∣ 2 ^ p - 1 ∧ ¬ 27 ∣ 2 ^ p + 1 := by
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have h9 : p % 18 ≠ 9 := by
    intro h
    have h3 : 3 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3
    omega
  have hmod : 2 ^ p % 27 = 2 ^ (p % 18) % 27 := by
    conv_lhs => rw [← Nat.div_add_mod p 18, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hr : p % 18 < 18 := Nat.mod_lt _ (by norm_num)
  have hr2 : (p % 18) % 2 = 1 := by omega
  generalize p % 18 = r at hmod hr hr2 h9
  have key : 2 ^ p % 27 = 2 ∨ 2 ^ p % 27 = 8 ∨ 2 ^ p % 27 = 5 ∨ 2 ^ p % 27 = 20 ∨ 2 ^ p % 27 = 23 ∨
      2 ^ p % 27 = 11 ∨ 2 ^ p % 27 = 17 ∨ 2 ^ p % 27 = 14 := by
    interval_cases r <;> simp_all
  generalize 2 ^ p = N at key ⊢
  omega

theorem g2N_not_dvd_card_parabolic
    {K : Type} [Field K] [Finite K]
    (h0 : ¬ 3 ∣ Nat.card K) (h1 : ¬ 3 ∣ Nat.card K - 1) (h2 : ¬ 27 ∣ Nat.card K + 1)
    {J : Set (Fin Tag.G2.rank)} (hJ : J ≠ Set.univ) :
    ¬ 27 ∣ Nat.card (parabolicSubgroup Tag.G2 K J) := by
  obtain ⟨j, hj⟩ := g2Sub_exists_subset_singleton hJ
  obtain ⟨-, -, -, -, -, -, hcell⟩ := standard_parabolic_cells Tag.G2 K
  rw [hcell J]
  intro hdvd
  have hc3 : ∀ n : ℕ, ¬ 3 ∣ n → Nat.Coprime 27 n := fun n hn =>
    Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hn)
  have hT : Nat.Coprime 27 (Nat.card (torusGroup Tag.G2 K)) :=
    hc3 _ (g2Sub_not_dvd_card_torusGroup Nat.prime_three h1)
  have hK : Nat.Coprime 27
      (Nat.card K ^ {α : Fin Tag.G2.rank → ℤ | IsRoot Tag.G2 α ∧ 0 < height α}.ncard) :=
    Nat.Coprime.pow_right _ (hc3 _ h0)
  have hs := (hT.mul_right hK).dvd_of_dvd_mul_left hdvd
  rcases g2Sub_finsum_parabolicWeyl hj (Nat.card K) with h | h
  · rw [h] at hs
    exact absurd (Nat.le_of_dvd one_pos hs) (by norm_num)
  · rw [h, add_comm] at hs
    exact h2 hs

theorem g2N_no_normalized_two_subgroup
    {K : Type} [Field K] [Finite K]
    [CharP K 2] (h1 : ¬ 3 ∣ Nat.card K - 1) (h2 : ¬ 27 ∣ Nat.card K + 1)
    (A : Subgroup (adjointGroup Tag.G2 K)) (hA : 27 ∣ Nat.card A)
    (R : Subgroup (adjointGroup Tag.G2 K)) (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hAR : A ≤ Subgroup.normalizer (R : Set (adjointGroup Tag.G2 K))) : False := by
  have hfin : Finite (ModGL Tag.G2 K) := finite_modGL
  have hBC : borelGroup Tag.G2 K ≤ adjointGroup Tag.G2 K := g2Sub_borel_le_adjointGroup
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := le_sup_right.trans hBC
  have h0 : ¬ 3 ∣ Nat.card K := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hn]
    exact fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow h)
      omega
  obtain ⟨S, P, hPtop, hNR, -, -, hNS⟩ := holds_adjointGroup_tag Tag.G2 K 2 R hR hR2
  have hAP : A ≤ P := hAR.trans hNR
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 hUC card_posUnipotent
  have hUc := IsPGroup.toSylow_coe hUp hUi
  obtain ⟨g, hg⟩ := g2Sub_exists_conj_le (hUp.toSylow hUi) S
    ((borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) P
    (by rw [hUc]; exact g2Sub_borel_le_normalizer) hNS
  have hP₁top : P.comap (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro h
    apply hPtop
    rw [eq_top_iff]
    intro y _
    have hy : (MulAut.conj g).toMonoidHom ((MulAut.conj g).symm y) ∈ P :=
      Subgroup.mem_comap.1 (h ▸ Subgroup.mem_top _)
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hy
  obtain ⟨J, hJ, hJP⟩ := g2Sub_exists_parabolic _ hg hP₁top
  set A₁ : Subgroup (adjointGroup Tag.G2 K) := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hA₁card : Nat.card A₁ = Nat.card A :=
    Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
  have hA₁P : ∀ y ∈ A₁, y ∈ P.comap (MulAut.conj g).toMonoidHom := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_comap]
    have : (MulAut.conj g).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom a) = a := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hAP ha
  set A₂ : Subgroup (ModGL Tag.G2 K) := A₁.map (adjointGroup Tag.G2 K).subtype
  have hA₂card : Nat.card A₂ = Nat.card A₁ :=
    Subgroup.card_map_of_injective (adjointGroup Tag.G2 K).subtype_injective
  have hA₂le : A₂ ≤ parabolicSubgroup Tag.G2 K J := by
    rintro _ ⟨y, hy, rfl⟩
    exact hJP y (hA₁P y hy)
  have hdvd : 27 ∣ Nat.card (parabolicSubgroup Tag.G2 K J) := by
    have := Subgroup.card_dvd_of_le hA₂le
    rw [hA₂card, hA₁card] at this
    exact hA.trans this
  exact g2N_not_dvd_card_parabolic h0 h1 h2 hJ hdvd

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
