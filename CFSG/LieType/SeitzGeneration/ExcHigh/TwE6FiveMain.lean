module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveCover
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveSylow
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveToral
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveFrame
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveOrder
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTw
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.TwFive

open scoped MatrixGroups

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.Chevalley.E6GraphLevi CFSG.Open
  CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

section Orders

variable {K : Type} [Field K] [Finite K]

theorem exists_mulEquiv_sl2_su2 {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nonempty (SL(2, RingHom.eqLocusField σ (RingHom.id K)) ≃* unitarySU ℓ f K 2) := by
  obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two (K := K) (r := ℓ)
    (f := f) hK
  have hk : CFSG.LieType.Steinberg.fixedSubfield K ℓ f =
      RingHom.eqLocusField σ (RingHom.id K) := by
    ext c
    rw [CFSG.LieType.Steinberg.mem_fixedSubfield, RingHom.mem_eqLocusField,
      CFSG.LieType.BorelTits.unitaryInvolution_apply, hσ, RingHom.id_apply]
  rw [← hk]
  exact ⟨e⟩

end Orders

section Hord


variable {K : Type} [Field K] [Finite K]

theorem five_hord {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h5 : 5 ∣ ℓ ^ f + 1) :
    (Nat.card ↥(twistedE6RootGroup K σ)).factorization 5 ≤
      (Nat.card (SL(2, RingHom.eqLocusField σ.toRingHom (RingHom.id K)) ×
        unitarySL σ.toRingHom)).factorization 5 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hU : UnitaryFieldData ℓ f K := ⟨hℓ, hf, hK'⟩
  haveI : CharP K ℓ := hU.charP
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  have hG :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.factorization_five_card_twistedE6_of_dvd_add_one
      hℓ hf K hK σ hσ h5
  have hkcard : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = ℓ ^ f :=
    CFSG.RankThree.Chevalley.card_eqLocusField_of_pow hℓ hf hK hσ'
  have hSL := factorization_card_SL2_of_dvd_add_one Nat.prime_five (by norm_num)
    (K := RingHom.eqLocusField σ.toRingHom (RingHom.id K)) (by rw [hkcard]; exact h5)
  have hSU : 5 ^ (5 * (ℓ ^ f + 1).factorization 5 + 1) ∣ Nat.card (unitarySL σ.toRingHom) := by
    rw [Nat.card_congr (TwSU6.unitarySLEquivStated hK hσ').toEquiv]
    exact five_pow_dvd_card_statedSU_six hU h5
  have hSU0 : Nat.card (unitarySL σ.toRingHom) ≠ 0 := Nat.card_pos.ne'
  have hSL0 : Nat.card (SL(2, RingHom.eqLocusField σ.toRingHom (RingHom.id K))) ≠ 0 :=
    Nat.card_pos.ne'
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five hSU0).1 hSU
  rw [Nat.card_prod, Nat.factorization_mul hSL0 hSU0, Finsupp.add_apply, hSL, hkcard, hG]
  omega

end Hord

section Main


theorem hasTwoCovers_five {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (h5 : 5 ∣ ℓ ^ f + 1) :
    HasTwoCovers (twistedE6RootGroup K σ) 5 fun E₀ => ¬ NormalizesRGroup ℓ E₀ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hU : UnitaryFieldData ℓ f K := ⟨hℓ, hf, hK'⟩
  haveI : CharP K ℓ := hU.charP
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  obtain ⟨ψ₁, hk₁, hH₁, hX₁⟩ := twE6SU6Cover_five K σ ℓ f hℓ hf hK hσ 5 le_rfl h5
  obtain ⟨H₂, _, _, ψ₂, hk₂, hH₂, hX₂⟩ := twE6D4Cover_five K σ ℓ f hℓ hf hK hσ 5 le_rfl h5
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hX₁' : ∀ y : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      y ∈ leviRootGroups σ.toRingHom → y ∈ ψ₁.range := fun y hy =>
    hX₁ (Subgroup.mem_sup_right hy)
  have hX₂' : ∀ y : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      y ∈ centerRootGroup σ.toRingHom → y ∈ ψ₂.range := fun y hy =>
    hX₂ (Subgroup.mem_sup_right hy)
  have hclose : ∀ M : Subgroup ↥(twistedE6RootGroup K σ), ψ₁.range ≤ M → ψ₂.range ≤ M →
      M = ⊤ := by
    intro M hM₁ hM₂
    refine eq_top_of_orbitRankOneGroup_le M fun a => ?_
    refine le_map_subtype_of_mem (orbitRankOneGroup_le_graphFixedRootGroup' _ _) fun y hy => ?_
    match a, hy with
    | ⟨0, _⟩, hy =>
      exact hM₁ (hX₁' y (Subgroup.mem_subgroupOf.2
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left hy))))
    | ⟨1, _⟩, hy =>
      exact hM₁ (hX₁' y (Subgroup.mem_subgroupOf.2
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right hy))))
    | ⟨2, _⟩, hy =>
      exact hM₁ (hX₁' y (Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right hy)))
    | ⟨3, _⟩, hy => exact hM₂ (hX₂' y (Subgroup.mem_subgroupOf.2 hy))
    | ⟨n + 4, h⟩, _ => exact absurd h (by change ¬ n + 4 < 4; omega)
  obtain ⟨e₂⟩ := exists_mulEquiv_sl2_su2 (K := K) hK σ.toRingHom hσ'
  let θ : SL(2, RingHom.eqLocusField σ.toRingHom (RingHom.id K)) × unitarySL σ.toRingHom ≃*
      unitarySU ℓ f K 2 × unitarySU ℓ f K 6 :=
    e₂.prodCongr (TwSU6.unitarySLEquivStated hK hσ')
  obtain ⟨Ew, hEwe, hEwc, hEwle⟩ := exists_elemAbelian_six hℓ hf K hK σ hσ h5
  have hEwr : Ew ≤ ψ₁.range := hEwle.trans (le_sup_left.trans hX₁)
  obtain ⟨Ew', hEw'e, hEw'm, hEw'c⟩ := exists_lift_of_le_range ψ₁ hk₁ hEwr hEwe
  have hord := five_hord hℓ hf hK σ hσ h5
  refine ⟨_, H₂, inferInstance, inferInstance, inferInstance, inferInstance, ψ₁, ψ₂,
    frameTorusGroup σ.toRingHom, hk₁, hk₂, hH₁, hH₂, hclose, le_sup_left.trans hX₁,
    le_sup_left.trans hX₂, ?_⟩
  intro E₀ hE₀p hE₀c _
  have hcomm : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup E₀ := IsPGroup.commGroupOfCardEqPrimeSq hE₀c
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E₀) ⟨b, hb⟩)
  have hE₀e : IsElemAbelian 5 E₀ :=
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a a.2 b b.2), hE₀p⟩
  obtain ⟨g, E', hE'e, hE'm⟩ := exists_conj_lift_elemAbelian ψ₁ hk₁ hord E₀ hE₀e
  obtain ⟨c, hc⟩ := exists_conj_le_toral_of_equiv hU h5 θ Ew' hEw'e (hEw'c.trans hEwc) E' hE'e
  refine ⟨(ψ₁ c)⁻¹ * g, ?_⟩
  rintro y ⟨e, he, rfl⟩
  have h1 : g * e * g⁻¹ ∈ E₀.map (MulAut.conj g).toMonoidHom :=
    ⟨e, he, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  rw [← hE'm] at h1
  obtain ⟨y', hy', hy'e⟩ := h1
  obtain ⟨z, hz, hzy⟩ := hc hy'
  have hzψ : ψ₁ z ∈ Ew := hEw'm ▸ ⟨z, hz, rfl⟩
  have hψ : g * e * g⁻¹ = ψ₁ c * ψ₁ z * (ψ₁ c)⁻¹ := by
    rw [← hy'e, ← hzy]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  have hconj : (MulAut.conj ((ψ₁ c)⁻¹ * g)).toMonoidHom e = ψ₁ z := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv]
    calc (ψ₁ c)⁻¹ * g * e * (g⁻¹ * ψ₁ c) = (ψ₁ c)⁻¹ * (g * e * g⁻¹) * ψ₁ c := by group
      _ = ψ₁ z := by rw [hψ]; group
  rw [hconj]
  exact hEwle hzψ

theorem twE6TwoNative_five : TwE6TwoNative fun p => p = 5 := by
  refine twE6TwoNative_of_covers fun K _ _ σ ℓ f hℓ hf hK hσ p _ _ hR hpq => ?_
  subst hR
  exact hasTwoCovers_five hℓ hf K hK σ hσ hpq

theorem seitzExcHighTwE6TwoFive : SeitzExcHighTwE6TwoFive :=
  seitzExcHighTwE6Two_of_native_for twE6TwoNative_five

end Main

end CFSG.LieType.SeitzGeneration.ExcHigh.TwFive
