module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256r
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256q2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256r

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.RecipeExcLang

theorem ringEquiv_eq_one_of_pow_three_of_card_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (σ : F ≃+* F) (hσ3 : σ ^ 3 = 1) : σ = 1 := by
  have h2 := Inputs256q.ringEquiv_sq_eq_one_of_card_four hF σ
  calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
    _ = 1 := by rw [hσ3, h2]; group

theorem exists_inndiag_FG_gf4 {τ : Tag} (hτ : τ = .F4 ∨ τ = .G2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (β : MulAut ↥(adjointGroup τ K)) (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) :
    ∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) ∧
      h ^ 3 = 1 ∧ h ≠ 1 := by
  classical
  obtain ⟨g, σ, hβe, hσp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.exists_form_FG hτ
    (fun _ => by rw [hK]; norm_num) Nat.prime_three (by norm_num) β hβ3
  obtain rfl : σ = 1 := ringEquiv_eq_one_of_pow_three_of_card_four hK σ hσp
  rw [exactNormalAut_one_one_zero, mul_one] at hβe
  subst hβe
  have hgp : g ^ 3 = 1 := by
    have : MulAut.conj (g ^ 3) = MulAut.conj 1 := by rw [map_pow, hβ3, map_one]
    exact mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot this
  have hg1 : (g : ModGL τ K) ≠ 1 := fun h1 => hβ1 (by
    have : g = 1 := Subtype.ext h1
    rw [this, map_one])
  refine ⟨(g : ModGL τ K), adjointGroup_le_inndiagGroup g.2, fun c => ?_, ?_, hg1⟩
  · simp [MulAut.conj_apply]
  · rw [← Subgroup.coe_pow, hgp]
    rfl

theorem exists_inndiag_E_gf4 {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (β : MulAut ↥(adjointGroup τ K)) (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) :
    ∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) ∧
      h ^ 3 = 1 ∧ h ≠ 1 := by
  classical
  obtain ⟨g, a, σ, hβe, hσp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.exists_form_E hτ
    Nat.prime_three (by norm_num) β hβ3
  obtain rfl : σ = 1 := ringEquiv_eq_one_of_pow_three_of_card_four hK σ hσp
  have hβw : ∀ c : adjointGroup τ K, (β c : ModGL τ K) =
      ((g : ModGL τ K) * rootDiagUnit τ a) * c * ((g : ModGL τ K) * rootDiagUnit τ a)⁻¹ := by
    intro c
    have e : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (c : ModGL τ K) = c :=
      Units.ext (entrywise_id _)
    rw [hβe, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_exactNormalAut, exactQ_zero, inv_one, mul_inv_rev, e]
    simp only [mul_assoc, mul_one]
  have hw : (g : ModGL τ K) * rootDiagUnit τ a ∈ inndiagGroup τ K :=
    mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a)
  obtain ⟨h', hh', hβh', hh'p⟩ := exists_inndiag_pow_eq_one hτ Nat.prime_three β hβ3 hw hβw
  refine ⟨h', hh', hβh', hh'p, ?_⟩
  rintro rfl
  apply hβ1
  refine MulEquiv.ext fun c => Subtype.ext ?_
  rw [hβh' c]
  simp

theorem twoElt_mem_glaLayer_of_langSetup_congr {τ : Tag} {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2)
    {p₀ : ℕ} (S' : LangSetup τ (AlgebraicClosure K) p₀) (hq4 : 4 ≤ S'.D.q) {S C : Type} [Group S] [Group C]
    (e : S ≃* C) (ι : C →* ModGL τ (AlgebraicClosure K)) (hι : Function.Injective ι)
    (hrange : ι.range = S'.Γ) (β : MulAut S) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hβ : ∀ c, ι (MulAut.congr e β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S'.D.torus) (hap : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S'.ρ S'.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S'.ρ S'.Γ (rootCharHom a) i))
    {s : S} (hs : β s = s) {m : ℕ} (hsm : s ^ 2 ^ m = 1) :
    s ∈ GLALayer (fixSubgroup β) := by
  have hrange' : (ι.comp e.toMonoidHom).range = S'.Γ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map, hrange]
  refine charElem_mem_glaLayer_of_langSetup S' hK2 Nat.prime_two hq4 Nat.prime_three (by norm_num)
    (ι.comp e.toMonoidHom) (hι.comp e.injective) hrange' β (fun c => ?_) hT hap h1 hTame hs hsm
  have h := hβ (e c)
  change ι (e (β (e.symm (e c)))) = _ at h
  rw [MulEquiv.symm_apply_apply] at h
  exact h

theorem twoElt_mem_glaLayer_adjoint_gf4 {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) {S : Type} [Group S]
    (e : S ≃* ↥(adjointGroup τ K)) (β : MulAut S) (hβ : orderOf β = 3) {s : S} (hs : β s = s) {m : ℕ}
    (hsm : s ^ 2 ^ m = 1) : s ∈ GLALayer (fixSubgroup β) := by
  classical
  have hK2 : ringChar K = 2 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow (n := 2) Nat.prime_two
      (by norm_num) (by rw [hK]; norm_num)
  have hβ3 : β ^ 3 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hβ1 : β ≠ 1 := fun h => by
    rw [h, orderOf_one] at hβ
    norm_num at hβ
  have hβ'3 : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hβ'1 : MulAut.congr e β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨h, hh, hβh, hp1, hh1⟩ : ∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K,
      ((MulAut.congr e β) c : ModGL τ K) = h * c * h⁻¹) ∧ h ^ 3 = 1 ∧ h ≠ 1 := by
    rcases hτ with h' | h' | h' | h' | h'
    · exact exists_inndiag_FG_gf4 (Or.inr h') hK _ hβ'3 hβ'1
    · exact exists_inndiag_FG_gf4 (Or.inl h') hK _ hβ'3 hβ'1
    · exact exists_inndiag_E_gf4 (Or.inl h') hK _ hβ'3 hβ'1
    · exact exists_inndiag_E_gf4 (Or.inr (Or.inl h')) hK _ hβ'3 hβ'1
    · exact exists_inndiag_E_gf4 (Or.inr (Or.inr h')) hK _ hβ'3 hβ'1
  have hpK : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    norm_num
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with h' | h' | h' | h' | h'
    · subst h'
      exact (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K (by omega)).commutator_eq_top
    all_goals exact single_edge_perfect τ K (by simp [h'])
  have hmon : MonomialToralAt τ 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with h' | h' | h' | h' | h' <;> simp [h']) Nat.prime_three (by norm_num)
  obtain ⟨S', a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw hτ Nat.prime_three hpK (Or.inr hK.ge) hmon hperf _ h
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  exact twoElt_mem_glaLayer_of_langSetup_congr hK2 S' (by rw [hSq, hK]) e ι hinj hrange β hconj hT hap h1
    (langSetup_hTame S' hT hap h1) hs hsm

theorem twoElt_mem_glaLayer_twE6_gf4 {K : Type} [Field K] (hK : Nat.card K = (2 ^ 2) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ 2)) {S : Type} [Group S] (e : S ≃* ↥(twistedE6RootGroup K σ))
    (β : MulAut S) (hβ : orderOf β = 3) {s : S} (hs : β s = s) {m : ℕ} (hsm : s ^ 2 ^ m = 1) :
    s ∈ GLALayer (fixSubgroup β) := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hK2 : ringChar K = 2 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow (n := 2 * 2) Nat.prime_two
      (by norm_num) (by rw [hK, ← pow_mul])
  have hβ3 : β ^ 3 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hβ1 : β ≠ 1 := fun h => by
    rw [h, orderOf_one] at hβ
    norm_num at hβ
  have hβ'3 : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hβ'1 : MulAut.congr e β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two (by norm_num : 1 ≤ 2) K hK σ hσ
  have hΘβ : Θ (MulAut.congr e β) = 1 := by
    have h3 : Θ (MulAut.congr e β) ^ 3 = 1 := by rw [← map_pow, hβ'3, map_one]
    have hcard : Nat.card (RingAut K) = 4 :=
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K (n := 4)
        (by rw [hK]; norm_num)).1
    have h4 : Θ (MulAut.congr e β) ^ 4 = 1 := by
      have h0 := pow_card_eq_one' (G := RingAut K) (x := Θ (MulAut.congr e β))
      rwa [hcard] at h0
    calc Θ (MulAut.congr e β) = Θ (MulAut.congr e β) ^ 4 * (Θ (MulAut.congr e β) ^ 3)⁻¹ := by group
      _ = 1 := by rw [h3, h4]; group
  have hmem : MulAut.congr e β ∈ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj, ← hker, MonoidHom.mem_ker]
    exact hΘβ
  obtain ⟨h, hh⟩ := hmem
  have hp1 : h ^ 3 = 1 :=
    twistedE6InndiagConj_injective Nat.prime_two (by norm_num) hK σ hσ (by rw [map_pow, hh, hβ'3, map_one])
  have hh1 : h ≠ 1 := fun h' => hβ'1 (by rw [← hh, h', map_one])
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) Nat.prime_three
      (by norm_num)
  obtain ⟨S', a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime Nat.prime_two (by norm_num) hK σ hσ Nat.prime_three (by norm_num)
      Nat.prime_three (by norm_num) (Or.inr (by norm_num)) hmon (twistedE6InndiagConj K σ h)
      (h : ModGL TwistTag.E6.tag K) h.2 (twistedE6InndiagConj_apply h) (by rw [← Subgroup.coe_pow, hp1]; rfl)
      (fun h' => hh1 (Subtype.ext h'))
  rw [hh] at hconj
  exact twoElt_mem_glaLayer_of_langSetup_congr hK2 S' (by rw [hSq]; norm_num) e ι hinj hrange β hconj hT hap h1
    (langSetup_hTame S' hT hap h1) hs hsm

theorem twoElt_mem_glaLayer_triD4_inner_gf4 {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 2) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ 2)) {S : Type} [Group S]
    (e : S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (β : MulAut S) (hβ : orderOf β = 3)
    (hinn : β ∈ (MulAut.conj : S →* MulAut S).range) {s : S} (hs : β s = s) {m : ℕ}
    (hsm : s ^ 2 ^ m = 1) : s ∈ GLALayer (fixSubgroup β) := by
  classical
  have hK2 : ringChar K = 2 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow (n := 2 * 3) Nat.prime_two
      (by norm_num) (by rw [hK, ← pow_mul])
  have hβ3 : β ^ 3 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hβ1 : β ≠ 1 := fun h => by
    rw [h, orderOf_one] at hβ
    norm_num at hβ
  obtain ⟨y, rfl⟩ := hinn
  have hβ' : MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
    refine MulEquiv.ext fun c => ?_
    show e (y * e.symm c * y⁻¹) = e y * c * (e y)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hxp : e y ^ 3 = 1 :=
    mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, ← hβ', ← map_pow, hβ3, map_one, map_one])
  have hx1 : e y ≠ 1 := fun h' => hβ1 ((MulAut.congr e).injective (by rw [hβ', h', map_one, map_one]))
  have hmon : MonomialToralAt Tag.D4 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) Nat.prime_three
      (by norm_num)
  obtain ⟨S', a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_triD4 Nat.prime_two (by norm_num) hK σ hσ Nat.prime_three (by norm_num)
      (Or.inr (by norm_num)) hmon (e y) hxp hx1
  rw [← hβ'] at hconj
  exact twoElt_mem_glaLayer_of_langSetup_congr hK2 S' (by rw [hSq]; norm_num) e ι hinj hrange _ hconj hT hap h1
    (langSetup_hTame S' hT hap h1) hs hsm

theorem twoEltLayerRest_holds : Inputs256q.TwoEltLayerRest := by
  intro S _ _ d hd he β hβ hinn s hs hs2
  obtain ⟨eS⟩ := he
  obtain ⟨m, hm⟩ := hs2
  obtain ⟨⟨hd2, hd4, hnA, hnU, hnB⟩, hnO⟩ := hd
  obtain ⟨d, hv⟩ := d
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | A n q => exact (hnA ⟨n, q, rfl⟩).elim
  | twistedA n q => exact (hnU ⟨n, q, rfl⟩).elim
  | B n q => exact (hnB ⟨n, q, rfl⟩).elim
  | C n q => exact (hr.2 ((TauCeti.LieTypeIndex.characteristic_C n q).symm.trans hd2)).elim
  | D n q => exact (hnO ⟨n, q, Or.inl rfl, hd4⟩).elim
  | twistedD n q => exact (hnO ⟨n, q, Or.inr rfl, hd4⟩).elim
  | E6 q =>
    obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
    exact twoElt_mem_glaLayer_adjoint_gf4 (τ := .E6) (by simp) (hK.trans hd4) (eS.trans eK) β hβ hs hm
  | E7 q =>
    obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
    exact twoElt_mem_glaLayer_adjoint_gf4 (τ := .E7) (by simp) (hK.trans hd4) (eS.trans eK) β hβ hs hm
  | E8 q =>
    obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
    exact twoElt_mem_glaLayer_adjoint_gf4 (τ := .E8) (by simp) (hK.trans hd4) (eS.trans eK) β hβ hs hm
  | F4 q =>
    obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
    exact twoElt_mem_glaLayer_adjoint_gf4 (τ := .F4) (by simp) (hK.trans hd4) (eS.trans eK) β hβ hs hm
  | G2 q =>
    obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
    exact twoElt_mem_glaLayer_adjoint_gf4 (τ := .G2) (by simp) (hK.trans hd4) (eS.trans eK) β hβ hs hm
  | twistedE6 q =>
    obtain ⟨hp2, he2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 2)
      Nat.prime_two (by norm_num) (hd4.trans (by norm_num))
    obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
    rw [hp2, he2] at hK hσ
    exact twoElt_mem_glaLayer_twE6_gf4 hK σ hσ (eS.trans eK) β hβ hs hm
  | trialityD4 q =>
    obtain ⟨hp2, he2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 2)
      Nat.prime_two (by norm_num) (hd4.trans (by norm_num))
    obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
    rw [hp2, he2] at hK hσ
    exact twoElt_mem_glaLayer_triD4_inner_gf4 hK σ hσ (eS.trans eK) β hβ (hinn ⟨q, rfl⟩) hs hm
  | suzuki k =>
    have h4 : 2 ^ (2 * k + 1) = 2 ^ 2 := hd4
    have := Nat.pow_right_injective (le_refl 2) h4
    omega
  | reeG2 k =>
    have h3 : (3 : ℕ) = 2 := (TauCeti.LieTypeIndex.characteristic_reeG2 k).symm.trans hd2
    omega
  | reeF4 k =>
    have h4 : 2 ^ (2 * k + 1) = 2 ^ 2 := hd4
    have := Nat.pow_right_injective (le_refl 2) h4
    omega
  | tits =>
    have h4 : (2 : ℕ) = 4 := hd4
    omega

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256r

end
