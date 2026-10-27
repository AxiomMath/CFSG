module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneE6OuterSquareBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneE6Outer

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.E6GraphLevi (thetaRootGroup mem_thetaRootGroup thetaTorusHom
  thetaTorusHom_apply rootTorusSL2_conj_pinnedX_map commutator_pinnedX_of_two)
open CFSG.LieType.Chevalley.E6SecondGraphFull (embeddedFieldAut coe_embeddedFieldAut
  embeddedFieldAut_refl secondGraphFullCentralizer_graphFixedRootGroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.RankThree.Chevalley (center_eq_bot_of_mulEquiv_adjointGroup pinnedX_e6HighestRoot_one_sq)
open scoped commutatorElement

@[expose] def e6RootTwo : Fin TwistTag.E6.tag.rank → ℤ :=
  (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)

@[expose] def e6HighestRootSubTwo : Fin TwistTag.E6.tag.rank → ℤ :=
  (![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ)

theorem e6RootTwo_facts :
    IsRoot TwistTag.E6.tag e6RootTwo ∧ IsRoot TwistTag.E6.tag e6HighestRootSubTwo ∧
      e6RootTwo ≠ e6HighestRootSubTwo ∧ e6RootTwo ≠ -e6HighestRootSubTwo ∧
      e6RootTwo + e6HighestRootSubTwo = e6HighestRoot ∧
      0 < height e6RootTwo ∧ 0 < height e6HighestRootSubTwo ∧
      permLattice TwistTag.E6.perm e6RootTwo = e6RootTwo ∧
      permLattice TwistTag.E6.perm e6HighestRootSubTwo = e6HighestRootSubTwo :=
  ⟨mem_rootFinset.1 (by decide +kernel), mem_rootFinset.1 (by decide +kernel), by decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem eq_refl_of_conj_pinnedX_e6HighestRoot
    {f : ℕ} (hf : 1 ≤ f) (k K : Type) [Field k] [Field K] [Algebra k K]
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {y : ModGL TwistTag.E6.tag K}
    (hy : y ∈ graphFixedRootGroup TwistTag.E6 K σ) {φ : k ≃+* k}
    (h : ∀ a : k, y * pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K (φ a)) * y⁻¹ =
      pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K a)) :
    φ = RingEquiv.refl k := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Fintype k := Fintype.ofFinite k
  have hk2 : ringChar k = 2 := FiniteField.even_card_iff_char_two.2 (by
    rw [← Nat.card_eq_fintype_card, hk, ← Nat.sub_add_cancel hf, pow_succ, Nat.mul_mod_left])
  have h2K : (2 : K) = 0 := by
    have := congrArg (algebraMap k K) (two_eq_zero_of_ringChar hk2)
    rwa [map_ofNat, map_zero] at this
  obtain ⟨-, hT⟩ := even_E6_graph_highest_root_normalizer f hf k K hk hK σ hσ
  obtain ⟨-, -, -, hfac, -, hC, -⟩ := hT
  set ι := algebraMap k K
  have hyN : y ∈ Subgroup.normalizer (thetaRootGroup ι : Set (ModGL TwistTag.E6.tag K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨c, rfl⟩ := (mem_thetaRootGroup ι).1 hg
      refine (mem_thetaRootGroup ι).2 ⟨φ.symm c, ?_⟩
      rw [← h (φ.symm c), RingEquiv.apply_symm_apply]
    · intro hg
      obtain ⟨c, hc⟩ := (mem_thetaRootGroup ι).1 hg
      refine (mem_thetaRootGroup ι).2 ⟨φ c, ?_⟩
      have e := h c
      rw [hc] at e
      exact mul_left_cancel (mul_right_cancel e)
  obtain ⟨⟨q, l, _⟩, ⟨hq, hl, ⟨a₀, rfl⟩, hyql⟩, -⟩ := hfac y (Subgroup.mem_inf.2 ⟨hyN, hy⟩)
  have hqC : q ∈ Subgroup.centralizer (thetaRootGroup ι : Set (ModGL TwistTag.E6.tag K)) := by
    have h1 : q ∈ Subgroup.centralizer (thetaRootGroup ι : Set (ModGL TwistTag.E6.tag K)) ⊓
        graphFixedRootGroup TwistTag.E6 K σ := by
      rw [hC]
      exact Subgroup.mem_sup_left hq
    exact (Subgroup.mem_inf.1 h1).1
  have hlC : l ∈ Subgroup.centralizer (thetaRootGroup ι : Set (ModGL TwistTag.E6.tag K)) := by
    have h1 : l ∈ Subgroup.centralizer (thetaRootGroup ι : Set (ModGL TwistTag.E6.tag K)) ⊓
        graphFixedRootGroup TwistTag.E6 K σ := by
      rw [hC]
      exact Subgroup.mem_sup_right hl
    exact (Subgroup.mem_inf.1 h1).1
  have hact : ∀ c : k, y * pinnedX TwistTag.E6.tag K e6HighestRoot (ι c) * y⁻¹ =
      pinnedX TwistTag.E6.tag K e6HighestRoot (ι ((a₀ : k) ^ 2 * c)) := by
    intro c
    have hX : pinnedX TwistTag.E6.tag K e6HighestRoot (ι ((a₀ : k) ^ 2 * c)) ∈ thetaRootGroup ι :=
      (mem_thetaRootGroup ι).2 ⟨_, rfl⟩
    have hqX := Subgroup.mem_centralizer_iff.1 hqC _ hX
    have hlX := Subgroup.mem_centralizer_iff.1 hlC _ hX
    have hhX := rootTorusSL2_conj_pinnedX_map h2K ι a₀ c
    rw [← thetaTorusHom_apply] at hhX
    rw [hyql]
    calc q * (l * ((thetaTorusHom K).comp (Units.map ι.toMonoidHom) a₀)) *
          pinnedX TwistTag.E6.tag K e6HighestRoot (ι c) *
          (q * (l * ((thetaTorusHom K).comp (Units.map ι.toMonoidHom) a₀)))⁻¹ =
        q * (l * (thetaTorusHom K (Units.map ι.toMonoidHom a₀) *
          pinnedX TwistTag.E6.tag K e6HighestRoot (ι c) *
          (thetaTorusHom K (Units.map ι.toMonoidHom a₀))⁻¹) * l⁻¹) * q⁻¹ := by
          rw [MonoidHom.comp_apply]
          group
      _ = pinnedX TwistTag.E6.tag K e6HighestRoot (ι ((a₀ : k) ^ 2 * c)) := by
          rw [hhX, ← hlX, mul_inv_cancel_right, ← hqX, mul_inv_cancel_right]
  have e1 : ∀ a : k, (a₀ : k) ^ 2 * φ a = a := fun a =>
    ι.injective (pinnedX_injective (τ := TwistTag.E6.tag) (R := K) e6HighestRoot
      ((hact (φ a)).symm.trans (h a)))
  have ha₀ : (a₀ : k) ^ 2 = 1 := by simpa using e1 1
  exact RingEquiv.ext fun a => by simpa [ha₀] using e1 a

theorem conj_mul_embeddedFieldAut_mem_inner_of_fix
    {f : ℕ} (hf : 1 ≤ f) (k K : Type) [Field k] [Field K] [Algebra k K]
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (y : ↥((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K))))
    (φ : k ≃+* k)
    (hfix : ∀ u v : ↥((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
        (baseChangeGL (algebraMap k K))),
      (u : ModGL TwistTag.E6.tag K) * pinnedX TwistTag.E6.tag K e6HighestRoot 1 =
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 * u →
      (v : ModGL TwistTag.E6.tag K) * pinnedX TwistTag.E6.tag K e6HighestRoot 1 =
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 * v →
      (MulAut.conj y * embeddedFieldAut (algebraMap k K) φ) ⁅u, v⁆ = ⁅u, v⁆) :
    MulAut.conj y * embeddedFieldAut (algebraMap k K) φ ∈
      inner ↥((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
        (baseChangeGL (algebraMap k K))) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Fintype k := Fintype.ofFinite k
  have hk2 : ringChar k = 2 := FiniteField.even_card_iff_char_two.2 (by
    rw [← Nat.card_eq_fintype_card, hk, ← Nat.sub_add_cancel hf, pow_succ, Nat.mul_mod_left])
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  have h2K : (2 : K) = 0 := by
    have := congrArg (algebraMap k K) h2
    rwa [map_ofNat, map_zero] at this
  obtain ⟨hα, hβ, hne, hne', hab, hαp, hβp, hαρ, hβρ⟩ := e6RootTwo_facts
  have hfixι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c => by
    rw [hσ, ← map_pow, ← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hJC := map_baseChangeGL_le_graphFixedRootGroup hfixι
  have hmemΓ : ∀ {γ : Fin TwistTag.E6.tag.rank → ℤ}, IsRoot TwistTag.E6.tag γ →
      permLattice TwistTag.E6.perm γ = γ → ∀ c : k,
        pinnedX TwistTag.E6.tag k γ c ∈ twistedFixedGroup TwistTag.E6 k (RingHom.id k) :=
    fun hγ hγρ c => (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 k (RingHom.id k)).2
      ⟨pinnedX_mem_adjointGroup _ c, by rw [twistHom_id_pinnedX (t := TwistTag.E6) h2 hγ, hγρ]⟩
  have hmemJ : ∀ {γ : Fin TwistTag.E6.tag.rank → ℤ}, IsRoot TwistTag.E6.tag γ →
      permLattice TwistTag.E6.perm γ = γ → ∀ c : k,
        pinnedX TwistTag.E6.tag K γ (algebraMap k K c) ∈
          (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)) :=
    fun hγ hγρ c => ⟨_, hmemΓ hγ hγρ c, baseChangeGL_pinnedX _ _ c⟩
  have hφ : φ = RingEquiv.refl k := by
    refine eq_refl_of_conj_pinnedX_e6HighestRoot hf k K hk hK σ hσ (hJC y.2) fun a => ?_
    have hu : pinnedX TwistTag.E6.tag K e6RootTwo (algebraMap k K a) *
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 = pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
          pinnedX TwistTag.E6.tag K e6RootTwo (algebraMap k K a) :=
      (commute_pinnedX_e6HighestRoot K hα hαp _ 1).eq
    have hv : pinnedX TwistTag.E6.tag K e6HighestRootSubTwo (algebraMap k K 1) *
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 = pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
          pinnedX TwistTag.E6.tag K e6HighestRootSubTwo (algebraMap k K 1) :=
      (commute_pinnedX_e6HighestRoot K hβ hβp _ 1).eq
    have h1 := congrArg Subtype.val (hfix ⟨_, hmemJ hα hαρ a⟩ ⟨_, hmemJ hβ hβρ 1⟩ hu hv)
    have hw : ((⁅(⟨_, hmemJ hα hαρ a⟩ : ↥((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
        (baseChangeGL (algebraMap k K)))), ⟨_, hmemJ hβ hβρ 1⟩⁆ : ↥((twistedFixedGroup
          TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)))) :
            ModGL TwistTag.E6.tag K) =
        pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K a) := by
      change ⁅pinnedX TwistTag.E6.tag K e6RootTwo (algebraMap k K a),
        pinnedX TwistTag.E6.tag K e6HighestRootSubTwo (algebraMap k K 1)⁆ = _
      rw [commutator_pinnedX_of_two h2K hα hβ hne hne' (by rw [hab]; exact isRoot_e6HighestRoot),
        hab, map_one, mul_one]
    have hwΓ : pinnedX TwistTag.E6.tag k e6HighestRoot a ∈
        twistedFixedGroup TwistTag.E6 k (RingHom.id k) :=
      hmemΓ isRoot_e6HighestRoot permLattice_e6HighestRoot a
    have hφw := coe_embeddedFieldAut (algebraMap k K) φ ⟨_, hwΓ⟩ _
      (hw.trans (baseChangeGL_pinnedX _ _ a).symm)
    have hent : Units.map (entrywiseHom φ.toRingHom) (pinnedX TwistTag.E6.tag k e6HighestRoot a) =
        pinnedX TwistTag.E6.tag k e6HighestRoot (φ a) :=
      Units.ext (entrywise_pinnedX _ _ _)
    change _ = baseChangeGL (algebraMap k K)
      (Units.map (entrywiseHom φ.toRingHom) (pinnedX TwistTag.E6.tag k e6HighestRoot a)) at hφw
    rw [hent, baseChangeGL_pinnedX] at hφw
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hφw, hw] at h1
    exact h1
  rw [hφ, embeddedFieldAut_refl, mul_one]
  exact ⟨y, rfl⟩

theorem noNormalZ4OrZ2xZ4_twistedE6_second_graph_class' {f : ℕ} (hf : 1 ≤ f) (k K : Type)
    [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) (hF4 : InnerInvolutionInput (adjointGroup Tag.F4 k))
    (H : Subgroup (MulAut (graphFixedRootGroup TwistTag.E6 K σ)))
    (hIH : inner (graphFixedRootGroup TwistTag.E6 K σ) ≤ H)
    (ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 K σ)
    (η : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hη : ∀ g, (η g : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹)
    {α φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ)}
    (hαI : α ∉ inner (graphFixedRootGroup TwistTag.E6 K σ))
    (hφ : φ * α * φ⁻¹ = MulAut.conj (⟨_, ht⟩ : graphFixedRootGroup TwistTag.E6 K σ) * η) :
    NoNormalZ4OrZ2xZ4
      ↥(H ⊓ centralizer ({α} : Set (MulAut (graphFixedRootGroup TwistTag.E6 K σ)))) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Fintype k := Fintype.ofFinite k
  have hk2 : ringChar k = 2 := FiniteField.even_card_iff_char_two.2 (by
    rw [← Nat.card_eq_fintype_card, hk, ← Nat.sub_add_cancel hf, pow_succ, Nat.mul_mod_left])
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  have h2K : (2 : K) = 0 := by
    have := congrArg (algebraMap k K) h2
    rwa [map_ofNat, map_zero] at this
  obtain ⟨htJ, -, -⟩ := secondGraphFullCentralizer_graphFixedRootGroup hf k K hk hK σ hσ
  obtain ⟨ht2, ht1⟩ := pinnedX_e6HighestRoot_one_sq h2K
  have hF4' := fun τJ hτJ L hL => noNormalZ4OrZ2xZ4_inf_centralizer_inner_of_F4 k hF4
    (graphFixedImageF4Equiv (algebraMap k K) h2) htJ ht2 ht1 τJ hτJ L hL
  have hξ : ∀ g, ((MulAut.conj (⟨_, ht⟩ : graphFixedRootGroup TwistTag.E6 K σ) * η) g :
      ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
        (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) *
          (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹ := fun g => by
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hη]
  have hZJ := center_eq_bot_of_mulEquiv_adjointGroup k
    (graphFixedImageF4Equiv (algebraMap k K) h2)
  have hξI := not_mem_inner_of_conj hαI hφ
  have hηI : η ∉ inner (graphFixedRootGroup TwistTag.E6 K σ) := fun ⟨c, hc⟩ =>
    hξI ⟨⟨_, ht⟩ * c, by rw [map_mul, hc]⟩
  exact NoNormalZ4OrZ2xZ4.of_conj hφ (noNormalZ4OrZ2xZ4_inf_centralizer_xi_of_rigid
    (secondGraphFullCentralizer_graphFixedRootGroup hf k K hk hK σ hσ) diagramMap_E6_mul_self hZJ
    η hη hηI _ hξ hF4'
    (fun y φ _ hfix => conj_mul_embeddedFieldAut_mem_inner_of_fix hf k K hk hK σ hσ y φ hfix) _
    (inner_le_map_conj_of_le hIH φ))

theorem outerInvolutionInput_twistedE6' {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hF4 : ∀ (k : Type) [Field k], Nat.card k = 2 ^ f →
      InnerInvolutionInput (adjointGroup .F4 k)) :
    OuterInvolutionInput (graphFixedRootGroup .E6 K σ.toRingHom) := by
  intro H hIH α _ hαI hα
  have hk := CFSG.RankThree.Chevalley.card_eqLocusField_of_pow Nat.prime_two hf hK
    (σ := σ.toRingHom) hσ
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  obtain ⟨ht, η, hη, -, -, hnoninner, -, -⟩ :=
    (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).2 K hK σ.toRingHom hσ
  have hnc : ∀ c, α ≠ MulAut.conj c := fun c h => hαI ⟨c, h.symm⟩
  rcases hnoninner α hα2 hnc with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · exact (abelianNormalCardLeTwo_twistedE6_graph_class hf
      (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) K hk hK σ.toRingHom hσ η hη H hIH hαI
        hφ).noNormalZ4OrZ2xZ4
  · exact noNormalZ4OrZ2xZ4_twistedE6_second_graph_class' hf
      (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) K hk hK σ.toRingHom hσ (hF4 _ hk) H hIH
      ht η hη hαI hφ

theorem exceptionalHypothesisOneInputs_of_inner'
    (hin : ∀ (τ : Tag) (f : ℕ) (K : Type) [Field K], 1 ≤ f → Nat.card K = 2 ^ f →
      (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → InnerInvolutionInput (adjointGroup τ K))
    (hinT : ∀ (f : ℕ) (K : Type) [Field K] (σ : K ≃+* K), 1 ≤ f → Nat.card K = (2 ^ f) ^ 2 →
      (∀ c, σ c = c ^ 2 ^ f) → InnerInvolutionInput (graphFixedRootGroup .E6 K σ.toRingHom)) :
    ExceptionalHypothesisOneInputs :=
  ⟨hin, fun f K _ hf hK => outerInvolutionInput_E6 hf K hK (hin .F4 f K hf hK (.inl rfl)),
    fun f K _ σ hf hK hσ => ⟨hinT f K σ hf hK hσ,
      outerInvolutionInput_twistedE6' hf K hK σ hσ fun k _ hk => hin .F4 f k hf hk (.inl rfl)⟩⟩

theorem exceptionalHypothesisOne_of_inner'
    (hin : ∀ (τ : Tag) (f : ℕ) (K : Type) [Field K], 1 ≤ f → Nat.card K = 2 ^ f →
      (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → InnerInvolutionInput (adjointGroup τ K))
    (hinT : ∀ (f : ℕ) (K : Type) [Field K] (σ : K ≃+* K), 1 ≤ f → Nat.card K = (2 ^ f) ^ 2 →
      (∀ c, σ c = c ^ 2 ^ f) → InnerInvolutionInput (graphFixedRootGroup .E6 K σ.toRingHom)) :
    ExceptionalHypothesisOne :=
  exceptionalHypothesisOne_of_inputs (exceptionalHypothesisOneInputs_of_inner' hin hinT)

end CFSG.SeitzReduction
