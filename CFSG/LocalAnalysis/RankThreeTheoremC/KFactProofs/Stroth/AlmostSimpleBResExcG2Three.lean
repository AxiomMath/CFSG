module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcG2
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti CFSG.RankThree.PartOne.K128
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.EvenG2
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancedCatalog (g2a g2v)
open CFSG.RankThree.PartOne

section


theorem exists_injective_G2_split_any (K : Type) [Field K] [Finite K] {d : ℕ}
    (hd : d ∣ Nat.card K - 1) :
    ∃ Ψ : (Fin 2 → Multiplicative (ZMod d)) →* adjointGroup .G2 K, Function.Injective Ψ := by
  obtain ⟨φ, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) K
  obtain ⟨ι, hι⟩ := exists_injective_units (K := K) hd
  let π₂ : (Fin 2 → Multiplicative (ZMod d)) →* (Fin Tag.G2.rank → Kˣ) :=
    MonoidHom.pi fun i =>
      ι.comp (Pi.evalMonoidHom (fun _ : Fin 2 => Multiplicative (ZMod d)) i)
  have hπ₂ : Function.Injective π₂ := fun x y h => funext fun i => hι (congrFun h i)
  have hle : torusGroup .G2 K ≤ adjointGroup .G2 K := torusGroup_le_adjointGroup'
  refine ⟨(Subgroup.inclusion hle).comp (φ.toMonoidHom.comp π₂), ?_⟩
  exact (Subgroup.inclusion_injective hle).comp (φ.injective.comp hπ₂)

set_option maxHeartbeats 400000 in
theorem even_G2_qplus_torus_basic (K : Type) [Field K] [Finite K] [CharP K 2] (K₂ : Type)
    [Field K₂] [Algebra K K₂] (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂)
    (hσ : ∀ c, σ c = c ^ Nat.card K) :
    ∃ g : ModGL .G2 K₂, g ∈ adjointGroup .G2 K₂ ∧
      Nonempty ((torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g : Subgroup (ModGL .G2 K₂)) ≃*
        Multiplicative (ZMod (Nat.card K + 1)) × Multiplicative (ZMod (Nat.card K + 1))) := by
  classical
  obtain ⟨hfin, -, -⟩ := CFSG.RankThree.QuadraticSL2.quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
  have : Finite (Module.End K₂ (RootModule .G2 K₂)) := Module.finite_of_finite K₂
  have hq2 := CFSG.RankThree.Chevalley.natCard_eq_sq_of_finrank_eq_two hdeg
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hdvd₂ : Nat.card K + 1 ∣ Nat.card K₂ - 1 := by
    refine ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  obtain ⟨hinv, ω, hσω⟩ := exists_frobenius_eq_add_one hdeg σ hσ
  have hPn := evenQuadraticP_mul_nSL σ hσω
  have hρC : ∀ (β : Fin Tag.G2.rank → ℤ) (A : SL2 K₂),
      rootSL2 .G2 K₂ β A ∈ adjointGroup .G2 K₂ :=
    fun β A => (exceptional_Lang_root_rank_one_data .G2 K₂ β).2.2.2.2.1 A
  obtain ⟨g, hgdef⟩ : ∃ g : ModGL .G2 K₂, g = rootSL2 .G2 K₂ g2a (evenQuadraticP ω)⁻¹ *
      rootSL2 .G2 K₂ g2v (evenQuadraticP ω)⁻¹ := ⟨_, rfl⟩
  have hg : g ∈ adjointGroup .G2 K₂ := by
    rw [hgdef]
    exact mul_mem (hρC _ _) (hρC _ _)
  obtain ⟨z, hzdef⟩ : ∃ z, z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ := ⟨_, rfl⟩
  have hzeq : z = rootWeylSL2 .G2 K₂ g2a 1 * rootWeylSL2 .G2 K₂ g2v 1 := by
    rw [hzdef, hgdef]
    exact rootSL2_pair_mul_entrywise_inv_eq (σ : K₂ →+* K₂) hPn
  obtain ⟨hzN, hw⟩ : ∃ hz : z ∈ monomialSubgroup .G2 K₂,
      ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v := by
    rw [hzeq]
    exact rootWeylSL2_pair_mem_monomial _
  have hΓ := conjEntrywiseImage_eq_fixed σ hσ hg hzdef
  have hT := torusGroup_inf_eq_torusTorsion hzN hw (σ : K₂ →+* K₂) hσ hΓ
  refine ⟨g, hg, ?_⟩
  rw [hT]
  exact nonempty_torusTorsion_mulEquiv hdvd₂

theorem exists_injective_G2_qplus_any (K : Type) [Field K] [Finite K] [CharP K 2] {d : ℕ}
    (hd : d ∣ Nat.card K + 1) :
    ∃ Ψ : (Fin 2 → Multiplicative (ZMod d)) →* adjointGroup .G2 K, Function.Injective Ψ := by
  obtain ⟨g, -, ⟨φ⟩⟩ := even_G2_qplus_torus_basic K (KFQ.Qext K) KFQ.finrank_qext
    (KFQ.frobQ K).toRingEquiv fun c => KFQ.frobQ_apply c
  have hm : Nat.card K + 1 ≠ 0 := Nat.succ_ne_zero _
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_injective_of_dvd hm hm hd hd
  let ψ : ModGL .G2 K →* ModGL .G2 (KFQ.Qext K) :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K (KFQ.Qext K)))
  have hψ : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := .G2) (algebraMap K (KFQ.Qext K)))
  let ε : adjointGroup .G2 K ≃* conjEntrywiseImage K g :=
    Subgroup.equivMapOfInjective (adjointGroup .G2 K) ψ hψ
  have hle : torusGroup .G2 (KFQ.Qext K) ⊓ conjEntrywiseImage K g ≤ conjEntrywiseImage K g :=
    inf_le_right
  refine ⟨ε.symm.toMonoidHom.comp ((Subgroup.inclusion hle).comp
    (φ.symm.toMonoidHom.comp Ψ₀)), ?_⟩
  exact ε.symm.injective.comp ((Subgroup.inclusion_injective hle).comp
    (φ.symm.injective.comp hΨ₀))

theorem hasIndepPair_adjointG2_three {m : ℕ} (k : Type) [Field k] [Finite k] [CharP k 2]
    (hk : Nat.card k = 2 ^ m) : HasIndepPair 3 (adjointGroup .G2 k) := by
  have h3 : ¬ 3 ∣ Nat.card k := by
    rw [hk]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow hd)
    omega
  have hQ : 1 ≤ Nat.card k := Nat.card_pos
  rcases (show Nat.card k % 3 = 1 ∨ Nat.card k % 3 = 2 by omega) with h | h
  · obtain ⟨Ψ, hΨ⟩ := exists_injective_G2_split_any k (d := 3 ^ 1) (by rw [pow_one]; omega)
    exact hasIndepPair_of_injective_pi Nat.prime_three le_rfl Ψ hΨ
  · obtain ⟨Ψ, hΨ⟩ := exists_injective_G2_qplus_any k (d := 3 ^ 1) (by rw [pow_one]; omega)
    exact hasIndepPair_of_injective_pi Nat.prime_three le_rfl Ψ hΨ

theorem fixesPair_adjointG2_three {f : ℕ} (hf : 2 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ f) {α : MulAut (adjointGroup Tag.G2 K)} (hαp : α ^ 3 = 1)
    (hα : α ∉ inner (adjointGroup Tag.G2 K)) : FixesIndepPair 3 α := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hαo : orderOf α = 3 := orderOf_eq_prime hαp (fun h1 => hα (h1 ▸
    (CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.G2 K)).one_mem))
  obtain ⟨x, σ, hσ, hασ⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.G2_form_even hf K hK Nat.prime_three α hαo hα
  obtain ⟨δ, hδ⟩ := CFSG.HardMathSupport.Lang.E6Descent.exists_conj_eq_entrywiseAdjointAut_of_form
    Tag.G2 Nat.prime_two (by omega) K hK Nat.prime_three α hαo x σ hσ hασ
  obtain ⟨hdvd, hc⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
    (by omega) hK σ
  rw [hσ] at hdvd hc
  haveI : Finite (fixSubfield σ) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact (pow_pos (by norm_num) _).ne')
  haveI : CharP (fixSubfield σ) 2 := RingHom.charP (fixSubfield σ).subtype
    (fixSubfield σ).subtype_injective 2
  exact fixesPair_of_entrywise_conj (r := 1) (j := 1) σ (by simp) (by rw [pow_one]; exact hδ)
    (hasIndepPair_adjointG2_three (fixSubfield σ) hc)

theorem chevTwoOuterFixesPair_G2_three :
    ChevTwoOuterFixesPairAt (fun p => p = 3) LieIndexG2 := by
  intro p hp hp2 hp3 L _ _ hrk ⟨d, hchar, hF, ⟨e⟩⟩ hne α hα hαp
  subst hp3
  obtain ⟨d, hv⟩ := d
  cases d with
  | G2 q =>
    have hq2 : q.p = 2 := hchar
    obtain ⟨K, _, _, hK, hchK, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
    haveI : CharP K 2 := hq2 ▸ hchK
    let θ : L ≃* adjointGroup Tag.G2 K := e.trans eK
    have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, PrimePower.card_def, hq2]
    have h3 : 3 ≤ q.card := (LieTypeIndex.inStandardRange_iff _).1
      ((LieTypeIndex.valid_iff _).1 hv).1
    have hf2 : 2 ≤ q.exponent := by
      by_contra h
      have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
      rw [PrimePower.card_def, hq2, h1] at h3
      omega
    exact FixesIndepPair.of_mulEquiv θ
      (fixesPair_adjointG2_three hf2 K hK2 (α := MulAut.congr θ α)
        (by rw [← map_pow, hαp, map_one]) ((congr_mem_inner_iff θ α).not.2 hα))
  | A _ _ => exact absurd hF (by simp [LieIndexG2])
  | twistedA _ _ => exact absurd hF (by simp [LieIndexG2])
  | B _ _ => exact absurd hF (by simp [LieIndexG2])
  | C _ _ => exact absurd hF (by simp [LieIndexG2])
  | D _ _ => exact absurd hF (by simp [LieIndexG2])
  | twistedD _ _ => exact absurd hF (by simp [LieIndexG2])
  | E6 _ => exact absurd hF (by simp [LieIndexG2])
  | E7 _ => exact absurd hF (by simp [LieIndexG2])
  | E8 _ => exact absurd hF (by simp [LieIndexG2])
  | F4 _ => exact absurd hF (by simp [LieIndexG2])
  | twistedE6 _ => exact absurd hF (by simp [LieIndexG2])
  | trialityD4 _ => exact absurd hF (by simp [LieIndexG2])
  | suzuki _ => exact absurd hF (by simp [LieIndexG2])
  | reeG2 _ => exact absurd hF (by simp [LieIndexG2])
  | reeF4 _ => exact absurd hF (by simp [LieIndexG2])
  | tits => exact absurd hF (by simp [LieIndexG2])

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
