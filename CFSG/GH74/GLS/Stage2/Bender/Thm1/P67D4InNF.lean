module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4VNormal
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4WeylCases
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneLeaf
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67InnerTools
public import CFSG.LieType.Chevalley.GraphFixedBorelCoreCenter
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LinearAlgebra.OddSolvableUnitary.HomologySaturation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import CFSG.RankThree.PartOne.KGD.D4QFrame
public import CFSG.RankThree.PartOne.KGD.D4T36Frame
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.OddAut

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

theorem d4_exists_aut_mono_plane {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 1) (E : Subgroup 𝒞[K, σ])
    (hEcard : Nat.card E = 3 ^ 2) :
    ∃ β : MulAut 𝒞[K, σ], ∀ e ∈ E,
      ((β⁻¹ e : 𝒞[K, σ]) : ModGL TwistTag.D4.tag K) ∈
        graphFixedMonomial TwistTag.D4 K σ.toRingHom := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcen : Subgroup.center 𝒞[K, σ] = ⊥ := center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj : Function.Injective (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]) :=
    mulAut_conj_injective_of_center_bot hcen
  set V : Subgroup (MulAut 𝒞[K, σ]) := E.map (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]) with hV
  have hVp : IsPGroup 3 V := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [hV, Subgroup.card_map_of_injective hinj]
    exact hEcard
  obtain ⟨-, -, ⟨Θ, hΘ, -, hΘker, -⟩, -, -, -, -, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  obtain ⟨β, hβ⟩ := d4_exists_conj_le_B0 hp hp2 hf K hK σ hσ hq V hVp
  refine ⟨β, fun e he => ?_⟩
  obtain ⟨g, δ, hgN, hgδ⟩ := hβ (MulAut.conj e) ⟨e, he, rfl⟩
  have hconj : β⁻¹ * MulAut.conj e * β = MulAut.conj (β⁻¹ e) := by
    refine MulEquiv.ext fun y => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply_self]
  have hΘ1 : Θ (MulAut.conj (β⁻¹ e)) = 1 := by
    have : MulAut.conj (β⁻¹ e) ∈ Θ.ker := by
      rw [hΘker]
      exact ⟨β⁻¹ e, rfl⟩
    exact this
  rw [hconj] at hgδ
  have hΘδ : Θ (MulAut.conj (β⁻¹ e)) = δ := hΘ _ g δ hgδ
  have hδ1 : δ = 1 := hΘδ.symm.trans hΘ1
  rw [hδ1, fieldActor_one, mul_one] at hgδ
  have : β⁻¹ e = g := hinj hgδ
  rw [this]
  exact hgN

theorem d4_plane_mono_cases (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (E : Subgroup 𝒞[K, σ]) (hEcard : Nat.card E = 3 ^ 2)
    (hN : ∀ e ∈ E, (e : ModGL TwistTag.D4.tag K) ∈
      graphFixedMonomial TwistTag.D4 K σ.toRingHom) :
    (∀ e ∈ E, (e : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom) ∨
    ∃ v ∈ E, ∃ n ∈ E, v ≠ 1 ∧
      (v : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom ∧
      (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom ∧
      (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom := by
  classical
  have hmono : ∀ e ∈ E, e ∈ monoY σ := fun e he => hN e he
  have hweyl1 : ∀ x : monoY σ, weylY σ x = 1 ↔
      ((x : 𝒞[K, σ]) : ModGL TwistTag.D4.tag K) ∈
        graphFixedTorus TwistTag.D4 K σ.toRingHom := fun x => by
    change graphFixedWeylHom TwistTag.D4 K σ.toRingHom ⟨(x : 𝒞[K, σ]).1, x.2⟩ = 1 ↔ _
    rw [← MonoidHom.mem_ker, graphFixedWeylHom_ker, Subgroup.mem_subgroupOf]
  by_cases hall : ∀ e ∈ E, (e : ModGL TwistTag.D4.tag K) ∈
      graphFixedTorus TwistTag.D4 K σ.toRingHom
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨n, hnE, hnT⟩ := hall
  let φ : E →* WeylGroup TwistTag.D4.tag :=
    (weylY σ).comp (Subgroup.inclusion (fun e he => hmono e he))
  have hφ1 : ∀ e : E, φ e = 1 ↔
      ((e : 𝒞[K, σ]) : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom :=
    fun e => hweyl1 ⟨e, hmono e e.2⟩
  have hrange_le : φ.range ≤ relWeylTwist TwistTag.D4 := by
    rintro _ ⟨e, rfl⟩
    exact graphFixedWeylHom_mem TwistTag.D4 K σ.toRingHom ⟨((e : 𝒞[K, σ])).1,
      (hmono e e.2)⟩
  have hdvd12 : Nat.card φ.range ∣ 12 := by
    rw [← card_relWeylTwist_D4]
    exact Subgroup.card_dvd_of_le hrange_le
  have h1 := φ.ker.card_mul_index
  rw [Subgroup.index_ker, hEcard] at h1
  have hdvd9 : Nat.card φ.range ∣ 9 := Dvd.intro_left _ (by omega)
  have hdvd3 : Nat.card φ.range ∣ 3 := by
    have := Nat.dvd_gcd hdvd9 hdvd12
    simpa using this
  have hne : Nat.card φ.range ≠ 1 := by
    intro h1'
    have hrb : φ.range = ⊥ := (Subgroup.card_eq_one).1 h1'
    have : φ ⟨n, hnE⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [hrb, Subgroup.mem_bot] at this
    exact hnT ((hφ1 ⟨n, hnE⟩).1 this)
  have hr3 : Nat.card φ.range = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd3 with h | h
    · exact absurd h hne
    · exact h
  have hk3 : Nat.card φ.ker = 3 := by
    rw [hr3] at h1
    omega
  have hker1 : φ.ker ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hk3
    omega
  obtain ⟨⟨v, hvker⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hker1
  refine ⟨(v : 𝒞[K, σ]), v.2, n, hnE, ?_, (hφ1 v).1 (MonoidHom.mem_ker.1 hvker), hN n hnE, hnT⟩
  intro hv
  apply hv1
  exact Subtype.ext (Subtype.ext hv)

theorem d4_torus_plane_not_aniso {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (E : Subgroup 𝒞[K, σ])
    (hT : ∀ e ∈ E, (e : ModGL TwistTag.D4.tag K) ∈
      graphFixedTorus TwistTag.D4 K σ.toRingHom) :
    ∃ R : Subgroup 𝒞[K, σ], IsPGroup p R ∧ R ≠ ⊥ ∧ E ≤ Subgroup.normalizer (R : Set 𝒞[K, σ]) := by
  classical
  obtain ⟨-, -, hU⟩ := triality_both_orientations_exact_finite_order p f hp hf K hK 1
    (Or.inl rfl) σ.toRingHom (by simpa using hσ)
  have hRcard : Nat.card ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = (p ^ f) ^ 12 := by
    rw [card_subgroupOf_of_le
      (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom), hU]
  have hq1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
  refine ⟨(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ?_, ?_, ?_⟩
  · exact IsPGroup.of_card (n := f * 12) (by rw [hRcard, pow_mul])
  · intro h
    rw [h, Subgroup.card_bot] at hRcard
    have : 1 < (p ^ f) ^ 12 := Nat.one_lt_pow (by norm_num) hq1
    omega
  · intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hrt : (e : ModGL TwistTag.D4.tag K) ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom :=
      Subgroup.mem_inf.2 ⟨hT e he, e.2⟩
    have hn := Subgroup.mem_normalizer_iff.1
      (graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent hrt) (x : ModGL TwistTag.D4.tag K)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hn

theorem d4_aniso_plane_q1 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 1) (E : Subgroup 𝒞[K, σ])
    (hEcard : Nat.card E = 3 ^ 2)
    (hanis : ∀ R : Subgroup 𝒞[K, σ], IsPGroup p R → R ≠ ⊥ →
      ¬ E ≤ Subgroup.normalizer (R : Set 𝒞[K, σ])) :
    ∃ β : MulAut 𝒞[K, σ], ∃ v ∈ E.map (β⁻¹).toMonoidHom, ∃ n ∈ E.map (β⁻¹).toMonoidHom,
      v ≠ 1 ∧ (v : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom ∧
      (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom ∧
      (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom := by
  classical
  obtain ⟨β, hβ⟩ := d4_exists_aut_mono_plane hp hp2 hf K hK σ hσ hq E hEcard
  refine ⟨β, ?_⟩
  have hcard' : Nat.card (E.map (β⁻¹).toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective (β⁻¹).injective]
    exact hEcard
  have hmono : ∀ x ∈ E.map (β⁻¹).toMonoidHom, (x : ModGL TwistTag.D4.tag K) ∈
      graphFixedMonomial TwistTag.D4 K σ.toRingHom := by
    rintro _ ⟨e, he, rfl⟩
    exact hβ e he
  rcases d4_plane_mono_cases K σ _ hcard' hmono with hT | h
  · exfalso
    obtain ⟨R, hRp, hR1, hER⟩ := d4_torus_plane_not_aniso hp hf K hK σ hσ _ hT
    have hmem : ∀ x : 𝒞[K, σ], x ∈ R.map β.toMonoidHom ↔ β⁻¹ x ∈ R := fun x => by
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨r, hr, rfl⟩
        show β⁻¹ (β r) ∈ R
        rw [MulAut.inv_apply_self]
        exact hr
      · intro h
        refine ⟨β⁻¹ x, h, ?_⟩
        show β (β⁻¹ x) = x
        rw [MulAut.apply_inv_self]
    refine hanis (R.map β.toMonoidHom) (hRp.map _) ?_ ?_
    · intro hbot
      exact hR1 ((Subgroup.map_eq_bot_iff_of_injective R β.injective).1 hbot)
    · intro e he
      have h1 := Subgroup.mem_normalizer_iff.1 (hER ⟨e, he, rfl⟩)
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [hmem, hmem]
      have h2 : β⁻¹ x ∈ R ↔ β⁻¹ e * β⁻¹ x * (β⁻¹ e)⁻¹ ∈ R := h1 (β⁻¹ x)
      rw [map_mul, map_mul, map_inv]
      exact h2
  · exact h

end CFSG.GH74.GLS.Stage2.Bender.Thm1
