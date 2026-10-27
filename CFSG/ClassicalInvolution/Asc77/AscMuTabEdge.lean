module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabStar

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.LieType.Steinberg CFSG.LieType.BorelTits
open scoped MatrixGroups

namespace MuTab

section TwoPart

theorem exists_orderOf_two_part (C : Type*) [Group C] [Finite C] [IsCyclic C] :
    ∃ x : C, orderOf x = 2 ^ (Nat.card C).factorization 2 := by
  classical
  have : Fintype C := Fintype.ofFinite C
  have hd : 2 ^ (Nat.card C).factorization 2 ∣ Fintype.card C := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.ordProj_dvd _ _
  have h := IsCyclic.card_orderOf_eq_totient hd
  have hpos : 0 <
      (Finset.univ.filter fun a : C => orderOf a = 2 ^ (Nat.card C).factorization 2).card := by
    rw [h]
    exact Nat.totient_pos.mpr (by positivity)
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  exact ⟨a, (Finset.mem_filter.mp ha).2⟩

theorem factorization_two_succ (q : ℕ) (h : q % 4 = 1) : (q + 1).factorization 2 = 1 := by
  have hm : q + 1 = 2 * ((q + 1) / 2) := by omega
  have hodd : ¬ 2 ∣ (q + 1) / 2 := by omega
  have hne : (q + 1) / 2 ≠ 0 := by omega
  rw [hm, Nat.factorization_mul (by norm_num) hne, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hodd]

theorem factorization_two_pred (q : ℕ) (h : q % 4 = 3) : (q - 1).factorization 2 = 1 := by
  have hm : q - 1 = 2 * ((q - 1) / 2) := by omega
  have hodd : ¬ 2 ∣ (q - 1) / 2 := by omega
  have hne : (q - 1) / 2 ≠ 0 := by omega
  rw [hm, Nat.factorization_mul (by norm_num) hne, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hodd]

theorem card_sl2_mul (F : Type) [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * ((Nat.card F - 1) * (Nat.card F + 1)) := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  congr 1
  zify [hq, Nat.one_le_pow 2 (Nat.card F) hq]
  ring

theorem two_pow_sl2_one_mod_four (F : Type) [Field F] [Finite F] (hq : Nat.card F % 4 = 1) :
    2 ^ (Nat.card SL(2, F)).factorization 2 = 2 * 2 ^ (Nat.card F - 1).factorization 2 := by
  have hpos : 1 < Nat.card F := Finite.one_lt_card
  have hq1 : Nat.card F - 1 ≠ 0 := by omega
  have hodd : ¬ 2 ∣ Nat.card F := by omega
  rw [card_sl2_mul, Nat.factorization_mul (by omega) (Nat.mul_ne_zero hq1 (by omega)),
    Nat.factorization_mul hq1 (by omega), Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd, factorization_two_succ _ hq]
  rw [zero_add, pow_add, pow_one, mul_comm]

theorem two_pow_sl2_three_mod_four (F : Type) [Field F] [Finite F] (hq : Nat.card F % 4 = 3) :
    2 ^ (Nat.card SL(2, F)).factorization 2 = 2 * 2 ^ (Nat.card F + 1).factorization 2 := by
  have hpos : 1 < Nat.card F := Finite.one_lt_card
  have hq1 : Nat.card F - 1 ≠ 0 := by omega
  have hodd : ¬ 2 ∣ Nat.card F := by omega
  rw [card_sl2_mul, Nat.factorization_mul (by omega) (Nat.mul_ne_zero hq1 (by omega)),
    Nat.factorization_mul hq1 (by omega), Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd, factorization_two_pred _ hq]
  rw [zero_add, pow_add, pow_one]

theorem natCard_galoisField_eq' {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) :
    Nat.card (GaloisField p f) = p ^ f :=
  GaloisField.card p f (by omega)

end TwoPart

theorem mem_omegaStarNbr_of_cyclic_two' {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime]
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) {K J T : Subgroup G} (hJ : J ∈ Ω)
    (hne : J ≠ K) (hTJ : T ≤ J) (hT2 : IsPGroup 2 T) (hTc : IsCyclic ↥T)
    (hcard : 2 * Nat.card T = 2 ^ (Nat.card SL(2, GaloisField p f)).factorization 2)
    (hTN : T ≤ Subgroup.normalizer (K : Set G)) : J ∈ omegaStarNbr Ω K := by
  obtain ⟨R, -, hRJ, hTR⟩ := exists_mem_RSet_ge hJ hT2 hTJ
  have hRcard := hΩ.natCard_isSylow2In hJ hRJ
  have hU : T ∈ USet Ω := mem_USet_of_natCard hJ hRJ hTR hTc (by rw [hRcard, ← hcard])
  exact ⟨hJ, hne, T, hU, hTJ, hTN⟩

end MuTab

section Torus

variable {F : Type} [Field F] {X : Type} [Group X]

theorem LinearBlockStandardPair.muTab_exists_torus_elt {W U V : Subgroup X}
    (h : WeakCT.LinearBlockStandardPair F W U V) (x : Fˣ) :
    ∃ v ∈ V, v ∈ Subgroup.normalizer (U : Set X) ∧ orderOf v = orderOf x := by
  obtain ⟨θ, -, hker, hU, hV⟩ := WeakCT.pair_normalize h
  set c : SL(3, F) := WeakCT.blockSL F 3 2 1 (by omega) (WeakCT.torusHom F x) with hc
  have hcD : c ∈ WeakCT.D23 F := WeakCT.mem_D23_iff.mpr ⟨x, rfl⟩
  have key : ∀ d ∈ WeakCT.D23 F, ∀ u ∈ U, θ d * u * (θ d)⁻¹ ∈ U := by
    intro d hd u hu
    rw [← hU] at hu
    obtain ⟨m, hm, rfl⟩ := hu
    rw [← hU]
    refine ⟨d * m * d⁻¹, WeakCT.D23_conj_mem_B12 hd hm, ?_⟩
    simp [map_mul, map_inv]
  refine ⟨θ c, ?_, ?_, ?_⟩
  · rw [← hV]
    exact ⟨c, WeakCT.D23_le_B23 hcD, rfl⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun hu => key c hcD u hu, fun hu => ?_⟩
    have := key c⁻¹ (inv_mem hcD) _ hu
    simpa [map_inv, mul_assoc] using this
  · have hinj : Function.Injective (θ.comp (WeakCT.blockSL F 3 2 1 (by omega))) :=
      WeakCT.comp_blockSL_injective hker (by omega) (by omega)
    calc orderOf (θ c) = orderOf ((θ.comp (WeakCT.blockSL F 3 2 1 (by omega)))
          (WeakCT.torusHom F x)) := rfl
      _ = orderOf (WeakCT.torusHom F x) := orderOf_injective _ hinj _
      _ = orderOf x := orderOf_injective _ (WeakCT.torusHom_injective (K := F)) x

end Torus

section TorusUnitary

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {X : Type} [Group X]

theorem UnitaryBlockStandardPair.muTab_exists_torus_elt (hK : Nat.card K = (p ^ f) ^ 2)
    {W U V : Subgroup X} (h : Phan.UnitaryBlockStandardPair K p f W U V)
    (u : normOne (unitaryInvolution K p f)) :
    ∃ v ∈ V, v ∈ Subgroup.normalizer (U : Set X) ∧ orderOf v = orderOf u := by
  obtain ⟨θ, -, hker, hU, hV⟩ := Phan.pair_normalize h
  set c : Phan.Su K p f 3 := embSUid (unitaryInvolution K p f) 0
    (torusTwo (unitaryInvolution K p f) u) with hc
  have hcD : c ∈ Phan.D23 K p f := Phan.mem_D23_iff.mpr ⟨u, rfl⟩
  have key : ∀ d ∈ Phan.D23 K p f, ∀ w ∈ U, θ d * w * (θ d)⁻¹ ∈ U := by
    intro d hd w hw
    rw [← hU] at hw
    obtain ⟨m, hm, rfl⟩ := hw
    rw [← hU]
    refine ⟨d * m * d⁻¹, Phan.D23_conj_mem_B12 hK hd hm, ?_⟩
    simp [map_mul, map_inv]
  refine ⟨θ c, ?_, ?_, ?_⟩
  · rw [← hV]
    exact ⟨c, Phan.D23_le_B23 hcD, rfl⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => key c hcD w hw, fun hw => ?_⟩
    have := key c⁻¹ (inv_mem hcD) _ hw
    simpa [map_inv, mul_assoc] using this
  · have hinj : Function.Injective (θ.comp (embSUid (unitaryInvolution K p f) 0)) :=
      Phan.comp_embSUid_injective hK hker 0
    calc orderOf (θ c) = orderOf ((θ.comp (embSUid (unitaryInvolution K p f) 0))
          (torusTwo (unitaryInvolution K p f) u)) := rfl
      _ = orderOf (torusTwo (unitaryInvolution K p f) u) := orderOf_injective _ hinj _
      _ = orderOf u := orderOf_injective _ (torusTwo_injective (unitaryInvolution K p f)) u

end TorusUnitary

namespace Ih8Model

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {t : StatedLieTag} {k e : ℕ} (M : Ih8Model p f Ω t k e)

include M

theorem muTab_dstarAdj_of_torus (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hD4 : t ≠ .trialityD4) (hnpsl : ¬ (t = .PSL ∧ k = 2))
    {R₁ R₂ : Subgroup (modelUniv t k p e Fact.out).K} (hR₁ : R₁ ∈ M.cls) (hR₂ : R₂ ∈ M.cls)
    (hne : R₁ ≠ R₂) {v : (modelUniv t k p e Fact.out).K} (hv : v ∈ R₂)
    (hvN : v ∈ Subgroup.normalizer (R₁ : Set _)) {a : ℕ} (hva : orderOf v = 2 ^ a)
    (hcard : 2 * 2 ^ a = 2 ^ (Nat.card SL(2, GaloisField p f)).factorization 2) :
    dstarAdj Ω (R₁.map M.ψ) (R₂.map M.ψ) := by
  have hord : orderOf (M.ψ v) = 2 ^ a := by
    rw [M.muTab_orderOf_map hnpsl hR₂ hv, hva]
  have hcardT : Nat.card (Subgroup.zpowers (M.ψ v)) = 2 ^ a := by
    rw [Nat.card_zpowers, hord]
  have hT2 : IsPGroup 2 (Subgroup.zpowers (M.ψ v)) := IsPGroup.of_card hcardT
  have hne' : R₂.map M.ψ ≠ R₁.map M.ψ := fun h =>
    hne (ih8_eq_of_map_eq M.ψ M.ker_le_center (M.cls_perfect hp2 hD4 hq hR₂)
      (M.cls_perfect hp2 hD4 hq hR₁) h).symm
  exact ⟨M.map_mem hR₂, Or.inl (MuTab.mem_omegaStarNbr_of_cyclic_two' hΩ (M.map_mem hR₂) hne'
    (Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ hv)) hT2 inferInstance
    (by rw [hcardT]; exact hcard)
    (Subgroup.zpowers_le.mpr (muTab_mem_normalizer_map M.ψ hvN)))⟩

omit [Finite G] in
theorem muTab_linear_ne_nc (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hD4 : t ≠ .trialityD4)
    {R₁ R₂ : Subgroup (modelUniv t k p e Fact.out).K} (hR₁ : R₁ ∈ M.cls) (hR₂ : R₂ ∈ M.cls)
    {W : Subgroup (modelUniv t k p e Fact.out).K}
    (hW : WeakCT.LinearBlockStandardPair (GaloisField p e) W R₁ R₂) :
    R₁ ≠ R₂ ∧ ¬ Commutes R₁ R₂ := by
  have hq' : 5 ≤ p ^ e := (M.exp_eq_f hD4) ▸ hq
  have h4 := M.four_le_natCard_galoisField hD4 hq
  have hne : R₁ ≠ R₂ := by
    intro h
    refine not_commutes_self_modelFund hp2 M.isFundTag hq' M.admissible (M.cls_sub hR₂)
      fun x hx y hy => ?_
    have hN : ∀ z ∈ R₂, z ∈ Subgroup.normalizer (R₁ : Set _) := fun z hz => by
      rw [h]
      exact Subgroup.le_normalizer hz
    exact LinearBlockStandardPair.comm_of_normalizes h4 hW hx hy (hN x hx) (hN y hy)
  refine ⟨hne, fun hc => ?_⟩
  have hbot : R₁ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact LinearBlockStandardPair.eq_one_of_centralizes h4 hW hx fun y hy => hc x hx y hy
  refine not_commutes_self_modelFund hp2 M.isFundTag hq' M.admissible (M.cls_sub hR₁) ?_
  intro a ha b hb
  rw [hbot, Subgroup.mem_bot] at ha
  rw [ha, one_mul, mul_one]

omit [Finite G] in
theorem muTab_unitary_ne_nc (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hD4 : t ≠ .trialityD4)
    {R₁ R₂ : Subgroup (modelUniv t k p e Fact.out).K} (hR₁ : R₁ ∈ M.cls) (hR₂ : R₂ ∈ M.cls)
    {W : Subgroup (modelUniv t k p e Fact.out).K}
    (hW : Phan.UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂) :
    R₁ ≠ R₂ ∧ ¬ Commutes R₁ R₂ := by
  have hq' : 5 ≤ p ^ e := (M.exp_eq_f hD4) ▸ hq
  have hf1 : 1 ≤ e := M.admissible.2.1
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul p e hf1
  have hne : R₁ ≠ R₂ := by
    intro h
    refine not_commutes_self_modelFund hp2 M.isFundTag hq' M.admissible (M.cls_sub hR₂)
      fun x hx y hy => ?_
    have hN : ∀ z ∈ R₂, z ∈ Subgroup.normalizer (R₁ : Set _) := fun z hz => by
      rw [h]
      exact Subgroup.le_normalizer hz
    exact UnitaryBlockStandardPair.comm_of_normalizes hK hq' hW hx hy (hN x hx) (hN y hy)
  refine ⟨hne, fun hc => ?_⟩
  have hbot : R₁ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact UnitaryBlockStandardPair.eq_one_of_centralizes hK hq' hW hx fun y hy => hc x hx y hy
  refine not_commutes_self_modelFund hp2 M.isFundTag hq' M.admissible (M.cls_sub hR₁) ?_
  intro a ha b hb
  rw [hbot, Subgroup.mem_bot] at ha
  rw [ha, one_mul, mul_one]

theorem muTab_dstarAdj_linear (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hD4 : t ≠ .trialityD4) (hnpsl : ¬ (t = .PSL ∧ k = 2)) (hq4 : p ^ f % 4 = 1)
    {R₁ R₂ : Subgroup (modelUniv t k p e Fact.out).K} (hR₁ : R₁ ∈ M.cls) (hR₂ : R₂ ∈ M.cls)
    {W : Subgroup (modelUniv t k p e Fact.out).K}
    (hW : WeakCT.LinearBlockStandardPair (GaloisField p e) W R₁ R₂) :
    dstarAdj Ω (R₁.map M.ψ) (R₂.map M.ψ) := by
  have he := M.exp_eq_f hD4
  have hf1 : 1 ≤ e := M.admissible.2.1
  have hne := (M.muTab_linear_ne_nc hp2 hq hD4 hR₁ hR₂ hW).1
  obtain ⟨x, hx⟩ := MuTab.exists_orderOf_two_part (GaloisField p e)ˣ
  obtain ⟨v, hvV, hvN, hvo⟩ := LinearBlockStandardPair.muTab_exists_torus_elt hW x
  have hcardF : Nat.card (GaloisField p e) = p ^ e := MuTab.natCard_galoisField_eq' hf1
  refine M.muTab_dstarAdj_of_torus hΩ hp2 hq hD4 hnpsl hR₁ hR₂ hne hvV hvN
    (a := (Nat.card (GaloisField p e)ˣ).factorization 2) (hvo.trans hx) ?_
  subst he
  rw [MuTab.two_pow_sl2_one_mod_four (GaloisField p e) (by rw [hcardF]; exact hq4),
    MuTab.natCard_units_eq']

theorem muTab_dstarAdj_unitary (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hD4 : t ≠ .trialityD4) (hnpsl : ¬ (t = .PSL ∧ k = 2)) (hq3 : p ^ f % 4 = 3)
    {R₁ R₂ : Subgroup (modelUniv t k p e Fact.out).K} (hR₁ : R₁ ∈ M.cls) (hR₂ : R₂ ∈ M.cls)
    {W : Subgroup (modelUniv t k p e Fact.out).K}
    (hW : Phan.UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂) :
    dstarAdj Ω (R₁.map M.ψ) (R₂.map M.ψ) := by
  have he := M.exp_eq_f hD4
  have hf1 : 1 ≤ e := M.admissible.2.1
  have hne := (M.muTab_unitary_ne_nc hp2 hq hD4 hR₁ hR₂ hW).1
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul p e hf1
  have hcardF : Nat.card (GaloisField p e) = p ^ e := MuTab.natCard_galoisField_eq' hf1
  obtain ⟨u, hu⟩ := MuTab.exists_orderOf_two_part
    (normOne (unitaryInvolution (GaloisField p (2 * e)) p e))
  obtain ⟨v, hvV, hvN, hvo⟩ := UnitaryBlockStandardPair.muTab_exists_torus_elt hK hW u
  refine M.muTab_dstarAdj_of_torus hΩ hp2 hq hD4 hnpsl hR₁ hR₂ hne hvV hvN
    (a := (Nat.card (normOne (unitaryInvolution (GaloisField p (2 * e)) p e))).factorization 2)
    (hvo.trans hu) ?_
  subst he
  rw [Phan.card_normOne hK, MuTab.two_pow_sl2_three_mod_four (GaloisField p e)
    (by rw [hcardF]; exact hq3), hcardF]

omit [Finite G] in
theorem muTab_pair_of_partner (hne : Ω.Nonempty) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {γ : Fin (modelUniv t k p e Fact.out).D.rank → ℤ}
    (hγ : ModelFacts.IsLongestRoot (modelUniv t k p e Fact.out).D γ)
    (h : ∃ δ : Fin (modelUniv t k p e Fact.out).D.rank → ℤ,
      ModelFacts.IsLongestRoot (modelUniv t k p e Fact.out).D δ ∧
      ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W
        ((modelUniv t k p e Fact.out).D.rootGroup γ ⊔
          (modelUniv t k p e Fact.out).D.rootGroup (-γ))
        ((modelUniv t k p e Fact.out).D.rootGroup δ ⊔
          (modelUniv t k p e Fact.out).D.rootGroup (-δ))) :
    ∃ R₁ ∈ M.cls, ∃ R₂ ∈ M.cls, ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W R₁ R₂ := by
  obtain ⟨δ, hδ, W, hW⟩ := h
  exact ⟨_, M.fund_subset_cls hne hG2 hD4 ⟨1, γ, Or.inl hγ, (conjSub_one _).symm⟩, _,
    M.fund_subset_cls hne hG2 hD4 ⟨1, δ, Or.inl hδ, (conjSub_one _).symm⟩, W, hW⟩

end Ih8Model

section Pairs

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {k e : ℕ}

theorem Ih8Model.muTab_linearPair_psl (M : Ih8Model p f Ω .PSL k e) (hne : Ω.Nonempty)
    (hk : 3 ≤ k) :
    ∃ R₁ ∈ M.cls, ∃ R₂ ∈ M.cls, ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W R₁ R₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : 0 < m := by omega
  let i₀ : Fin (modelUniv .PSL (m + 1) p e Fact.out).D.rank := ⟨0, by show 0 < m; omega⟩
  have hγ : ModelFacts.IsLongestRoot (modelUniv .PSL (m + 1) p e Fact.out).D (Pi.single i₀ 1) :=
    ModelFacts.isLongestRoot_single .PSL (m + 1) p e Fact.out trivial M.admissible i₀ trivial
  obtain ⟨δ, hδ, -, hW⟩ := ModelFacts.exists_standardPair_partner_PSL (m + 1) p e M.admissible hk hγ
  exact M.muTab_pair_of_partner hne (by decide) (by decide) hγ ⟨δ, hδ, hW⟩

theorem Ih8Model.muTab_linearPair_pOmegaOdd (M : Ih8Model p f Ω .POmegaOdd k e)
    (hne : Ω.Nonempty) :
    ∃ R₁ ∈ M.cls, ∃ R₂ ∈ M.cls, ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W R₁ R₂ := by
  have hn : 3 ≤ k := M.admissible.2.2.1
  let i₀ : Fin (modelUniv .POmegaOdd k p e Fact.out).D.rank := ⟨0, by show 0 < k; omega⟩
  have hγ : ModelFacts.IsLongestRoot (modelUniv .POmegaOdd k p e Fact.out).D (Pi.single i₀ 1) :=
    ModelFacts.isLongestRoot_single .POmegaOdd k p e Fact.out trivial M.admissible i₀
      (by show 0 + 1 < k; omega)
  obtain ⟨δ, hδ, -, hW⟩ := ModelFacts.exists_standardPair_partner_POmegaOdd p e k M.admissible hγ
  exact M.muTab_pair_of_partner hne (by decide) (by decide) hγ ⟨δ, hδ, hW⟩

theorem Ih8Model.muTab_linearPair_pOmegaMinus (M : Ih8Model p f Ω .POmegaMinus k e)
    (hp2 : p ≠ 2) (hne : Ω.Nonempty) :
    ∃ R₁ ∈ M.cls, ∃ R₂ ∈ M.cls, ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W R₁ R₂ := by
  have hn : 4 ≤ k := M.admissible.2.2
  let i₀ : Fin (modelUniv .POmegaMinus k p e Fact.out).D.rank := ⟨0, by show 0 < k - 1; omega⟩
  have hγ : ModelFacts.IsLongestRoot (modelUniv .POmegaMinus k p e Fact.out).D (Pi.single i₀ 1) :=
    ModelFacts.isLongestRoot_single .POmegaMinus k p e Fact.out trivial M.admissible i₀
      (by show 0 + 2 < k; omega)
  obtain ⟨δ, hδ, -, hW⟩ :=
    ModelFacts.exists_standardPair_partner_POmegaMinus k p e hp2 M.admissible hγ
  exact M.muTab_pair_of_partner hne (by decide) (by decide) hγ ⟨δ, hδ, hW⟩

theorem muTab_map_equiv_symm_map {G H : Type} [Group G] [Group H] (φ : G ≃* H)
    (R : Subgroup H) : (R.map φ.symm.toMonoidHom).map φ.toMonoidHom = R := by
  rw [Subgroup.map_map]
  have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id H := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem Ih8Model.muTab_unitaryPair_psu (M : Ih8Model p f Ω .PSU k e) (hp2 : p ≠ 2)
    (hne : Ω.Nonempty) :
    ∃ R₁ ∈ M.cls, ∃ R₂ ∈ M.cls, ∃ W,
      Phan.UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂ := by
  have hk3 : 3 ≤ k := M.admissible.2.2.1
  have hf1 : 1 ≤ e := M.admissible.2.1
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul p e hf1
  have hq2 : p ^ e ≠ 2 := by
    intro h
    have hd : p ∣ 2 := h ▸ dvd_pow_self p (by omega : e ≠ 0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hd)
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 M.admissible
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hpair := (Phan.weakPhanA_standard hK hq2 n).pair ⟨0, h0⟩ ⟨1, h1⟩ rfl
  have h' := Models.unitaryBlockStandardPair_map hpair φ.symm.toMonoidHom φ.symm.injective
  have hmem : ∀ i : Fin n, (Phan.standardU (GaloisField p (2 * e)) p e n i).map φ.symm.toMonoidHom ∈
      fundamentalSubgroups .PSU (modelUniv .PSU (n + 1) p e Fact.out).D := fun i => by
    rw [hφ, muTab_map_equiv_symm_map]
    exact ⟨_, Models.isLongRootSU2_range_blockEmb hK hp2 (by omega : (i : ℕ) + 2 ≤ n + 1)⟩
  exact ⟨_, M.fund_subset_cls hne (by decide) (by decide) (hmem ⟨0, h0⟩), _,
    M.fund_subset_cls hne (by decide) (by decide) (hmem ⟨1, h1⟩), _, h'⟩

end Pairs

end CFSG.ClassicalInvolution.Asc77
