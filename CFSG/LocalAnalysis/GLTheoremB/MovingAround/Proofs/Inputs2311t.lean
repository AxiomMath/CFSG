module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311g2
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddGType
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.Plane9

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311t

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Fischer CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartTwo.Sec19 CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c

set_option linter.unusedSectionVars false

section G2


theorem g2_closure_rElements_eq_top_inputs2311t {K : Type} [Field K] [Finite K]
    (hnd : ¬ 3 ∣ Nat.card K) (hK5 : 5 ≤ Nat.card K)
    (E₀ : Subgroup ↥(adjointGroup .G2 K)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1)
    (hcard : Nat.card E₀ = 3 ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} = ⊤ := by
  classical
  rcases (by omega : 3 ∣ Nat.card K + 1 ∨ 3 ∣ Nat.card K - 1) with h | h
  · exact Inputs2311g.g2ThreeUniNative_plus h (by omega) E₀ hexp hcard
  obtain ⟨R, hR1, hRp, hRn⟩ := Inputs2311g.g2ThreeNormalizesR_minus h E₀ hexp hcard
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := Fintype.ofFinite K
  obtain ⟨n, hr, hKn⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hr⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hr3 : ringChar K ≠ 3 := by
    intro h3
    apply hnd
    rw [Nat.card_eq_fintype_card, hKn, h3]
    exact dvd_pow_self 3 (PNat.ne_zero n)
  haveI : IsSimpleGroup ↥(adjointGroup .G2 K) :=
    isSimpleGroup_adjointGroup_of_isQuasisimple
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K (by omega))
  set S := {k : ↥(adjointGroup .G2 K) | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧
    ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} with hS
  set A : Subgroup (ModGL .G2 K) := E₀.map (adjointGroup .G2 K).subtype with hA
  set R' : Subgroup (ModGL .G2 K) := R.map (adjointGroup .G2 K).subtype with hR'
  have hEcomm : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val
      ((IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  haveI hAea : CFSG.IsElementaryAbelian 3 A := by
    refine isElementaryAbelian_three_of ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hEcomm a ha b hb)
    · rintro _ ⟨a, ha, rfl⟩
      have h1 := congrArg Subtype.val (hexp a ha)
      simpa using h1
  have hAcard : Nat.card A = 3 ^ 2 := by
    rw [hA, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcard]
  have hA1 : A ≠ ⊥ := by
    intro hA0
    rw [hA0, Subgroup.card_bot] at hAcard
    norm_num at hAcard
  have hR'1 : R' ≠ ⊥ := by
    intro h0
    apply hR1
    rw [eq_bot_iff]
    intro r hr
    have hmem : (r : ModGL .G2 K) ∈ R' := ⟨r, hr, rfl⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hR'p : IsPGroup (ringChar K) R' := hRp.map _
  have hAR : A ≤ Subgroup.normalizer (R' : Set (ModGL .G2 K)) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    ext z
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      have hmem : (MulAut.conj g).toMonoidHom r ∈ R := by
        rw [← hRn g hg]
        exact ⟨r, hr, rfl⟩
      exact ⟨_, hmem, by simp [MulAut.conj_apply]⟩
    · rintro ⟨r, hr, rfl⟩
      have hmem : (MulAut.conj g⁻¹).toMonoidHom r ∈ R := by
        rw [← hRn g hg] at hr
        obtain ⟨r', hr', rfl⟩ := hr
        have e : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom r') = r' := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          group
        rw [e]
        exact hr'
      refine ⟨_, ⟨_, hmem, rfl⟩, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hgen := CFSG.LieType.Chevalley.ordinary_root_invariant_prime_subgroup_hyperplane_generation_r
    .G2 K (ringChar K) 3 hr3 A (Subgroup.map_subtype_le _) hA1 R' (Subgroup.map_subtype_le _) hR'p
    hR'1 hAR
  have hsub : CFSG.LieType.Chevalley.hyperRSet (adjointGroup .G2 K) A (ringChar K) 3 ⊆
      (adjointGroup .G2 K).subtype '' S := by
    rintro y ⟨hyC, ⟨m, hm⟩, B, hBA, hBi, hyB⟩
    obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hB : B = ⊥ := (Subgroup.eq_bot_iff_forall B).2 hcon
      rw [hB, Subgroup.relIndex_bot_left, hAcard] at hBi
      norm_num at hBi
    obtain ⟨x, hx, rfl⟩ := hBA hbB
    refine ⟨⟨y, hyC⟩, ⟨x, hx, ?_, ?_, m, ?_⟩, rfl⟩
    · rintro rfl
      exact hb1 (by simp)
    · apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.1 hyB _ hbB).symm
    · apply Subtype.ext
      simpa using hm
  rw [eq_top_iff]
  intro z _
  have hz : (z : ModGL .G2 K) ∈ Subgroup.closure ((adjointGroup .G2 K).subtype '' S) :=
    Subgroup.closure_mono hsub (hgen z.2)
  rw [← MonoidHom.map_closure] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  have hwz' : w = z := Subtype.ext hwz
  rw [← hwz']
  exact hw

theorem rGen_of_mulEquiv_inputs2311t {G L : Type*} [Group G] [Group L] (H : Subgroup G) (Ψ : ↥H ≃* L)
    {r : ℕ}
    (hgen : ∀ E : Subgroup L, (∀ x ∈ E, x ^ 3 = 1) → Nat.card E = 3 ^ 2 →
      Subgroup.closure {k : L | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} = ⊤)
    (F : Subgroup G) (hFH : F ≤ H) (hF3 : ∀ a ∈ F, a ^ 3 = 1) (hcard : Nat.card F = 3 ^ 2) :
    H ≤ Subgroup.closure
      {j : G | j ∈ H ∧ (∃ n : ℕ, j ^ (r ^ n) = 1) ∧ ∃ f ∈ F, f ≠ 1 ∧ j * f = f * j} := by
  set E : Subgroup L := (F.subgroupOf H).map Ψ.toMonoidHom with hE
  have hmemE : ∀ x ∈ E, ((Ψ.symm x : H) : G) ∈ F := by
    rintro _ ⟨y, hy, rfl⟩
    have h : Ψ.symm (Ψ.toMonoidHom y) = y := Ψ.symm_apply_apply y
    rw [h]
    exact hy
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    apply Ψ.symm.injective
    apply Subtype.ext
    rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hF3 _ (hmemE x hx)
  have hEcard : Nat.card E = 3 ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective Ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFH).toEquiv]
    exact hcard
  have htop := hgen E hE3 hEcard
  intro h hh
  have h1 : Ψ ⟨h, hh⟩ ∈ Subgroup.closure
      {k : L | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} := by
    rw [htop]
    exact Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem (H.subtype.comp Ψ.symm.toMonoidHom) h1
  rw [MonoidHom.map_closure] at h2
  have h3 : (H.subtype.comp Ψ.symm.toMonoidHom) (Ψ ⟨h, hh⟩) = h := by
    show ((Ψ.symm (Ψ ⟨h, hh⟩) : H) : G) = h
    rw [Ψ.symm_apply_apply]
  rw [h3] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨k, ⟨x, hx, hx1, hkx, n, hn⟩, rfl⟩
  refine ⟨(Ψ.symm k).2, ⟨n, ?_⟩, ((Ψ.symm x : H) : G), hmemE x hx, ?_, ?_⟩
  · show ((Ψ.symm k : H) : G) ^ (r ^ n) = 1
    rw [← Subgroup.coe_pow, ← map_pow, hn, map_one, Subgroup.coe_one]
  · intro h0
    apply hx1
    have h4 : Ψ.symm x = 1 := Subtype.ext h0
    rw [← Ψ.apply_symm_apply x, h4, map_one]
  · show ((Ψ.symm k : H) : G) * ((Ψ.symm x : H) : G) =
      ((Ψ.symm x : H) : G) * ((Ψ.symm k : H) : G)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hkx.eq]

end G2

section Gsub


variable {X : Type} [Field X] [Finite X]

theorem gsub_le_closure_rElements_inputs2311t {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3) (σ : X ≃+* X) (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f))
    (F : Subgroup (C0 σ)) (hFG : F ≤ Gsub σ) (hF3 : ∀ a ∈ F, a ^ 3 = 1)
    (hcard : Nat.card F = 3 ^ 2) :
    Gsub σ ≤ Subgroup.closure {j : C0 σ | j ∈ Gsub σ ∧ (∃ n : ℕ, j ^ (ℓ ^ n) = 1) ∧
      ∃ f ∈ F, f ≠ 1 ∧ j * f = f * j} := by
  classical
  have hq2 : 2 ≤ ℓ ^ f := triOdd_two_le_pow hℓ hf
  have hℓ5 : 5 ≤ ℓ := by
    have h2 := hℓ.two_le
    rcases (by omega : ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 4 ∨ 5 ≤ ℓ) with h | h | h | h
    · exact absurd h hℓ2
    · exact absurd h hℓ3
    · subst h
      exact absurd hℓ (by norm_num)
    · exact h
  have hq5 : 5 ≤ ℓ ^ f := le_trans hℓ5 (by
    calc ℓ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf)
  have hX' : Nat.card X = ℓ ^ (3 * f) := by rw [hX, ← pow_mul]; ring_nf
  haveI : CharP X ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (k := 3 * f) (by omega) hX'
  have hK2 : ringChar X ≠ 2 := by rw [ringChar.eq X ℓ]; exact hℓ2
  have hσ3 : ∀ c, σ (σ (σ c)) = c := CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card
    (σ := σ.toRingHom) hX hσ
  have hF : Nat.card (fixSubfield σ) = ℓ ^ f :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom hq2 hX hσ
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    rw [ENat.card_eq_coe_natCard]
    exact_mod_cast (by omega : 3 ≤ Nat.card (fixSubfield σ))
  have hG : Gsub σ = (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.FixedSub σ).map
      (triOddEqRoot σ hK2 hq2 hX hσ).toMonoidHom := by
    rw [← triOdd_fixedSubgroup_tau_eq_map σ hσ3 hK2 hq2 hX hσ]
    exact triOdd_gsub_eq_fixedSubgroup σ
  have h3q : ¬ 3 ∣ Nat.card (fixSubfield σ) := by
    rw [hF]
    intro h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hchar : ringChar (fixSubfield σ) = ℓ := by
    rw [Algebra.ringChar_eq (fixSubfield σ) X, ringChar.eq X ℓ]
  have hgen : ∀ E : Subgroup ↥(adjointGroup .G2 (fixSubfield σ)), (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E = 3 ^ 2 →
      Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (ℓ ^ n) = 1} = ⊤ := by
    intro E hE3 hEc
    have h := g2_closure_rElements_eq_top_inputs2311t h3q (by omega) E hE3 hEc
    rwa [hchar] at h
  exact rGen_of_mulEquiv_inputs2311t (Gsub σ)
    (((MulEquiv.subgroupCongr hG).trans
      (Subgroup.equivMapOfInjective (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.FixedSub σ)
        (triOddEqRoot σ hK2 hq2 hX hσ).toMonoidHom
        (triOddEqRoot σ hK2 hq2 hX hσ).injective).symm).trans
      (triOddJDict σ hK2 hq2 hX hσ hσ3 hk3)) hgen F hFG hF3 hcard

end Gsub

section Central


variable {X : Type} [Field X] [Finite X]

theorem gsub_le_uniPlaneClosure_of_central_tau_inputs2311t {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3) (σ : X ≃+* X)
    (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut (C0 σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hcomm : ∀ α ∈ E, α * tauAut σ = tauAut σ * α)
    (hτE : tauAut σ ∉ E) :
    Gsub σ ≤ uniPlaneClosure ℓ E := by
  classical
  have hσ3 : σ ^ 3 = 1 := triOdd_sigma_pow_three σ (ℓ ^ f) hX hσ
  have hq2 : 2 ≤ ℓ ^ f := triOdd_two_le_pow hℓ hf
  have hσ1 : σ ≠ 1 := triOdd_sigma_ne_one σ (ℓ ^ f) hq2 hX hσ
  have hσ2 : σ ^ 2 ≠ 1 := nf1_sq_ne_one σ hσ3 hσ1
  obtain ⟨-, hdec, ⟨Θ, hΘ, -, -, -⟩, hcyc, hcard3, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf X hX σ hσ
  haveI : Finite (X ≃+* X) := Nat.finite_of_card_ne_zero (by rw [hcard3]; omega)
  have hinj : Function.Injective (MulAut.conj : C0 σ →* MulAut (C0 σ)) := nf1_conj_injective hZ
  have hτ3 : tauAut σ ^ 3 = 1 := triOdd_tauAut_pow_three σ hσ3
  obtain ⟨nf, hnf, huniq⟩ : ∃ nf : MulAut (C0 σ) → C0 σ × (X ≃+* X),
      (∀ α, α = MulAut.conj (nf α).1 * fieldActor (t := TwistTag.D4) σ (nf α).2) ∧
      ∀ α (y : C0 σ × (X ≃+* X)),
        α = MulAut.conj y.1 * fieldActor (t := TwistTag.D4) σ y.2 → y = nf α :=
    ⟨fun α => Classical.choose (hdec α), fun α => (Classical.choose_spec (hdec α)).1,
      fun α y h => (Classical.choose_spec (hdec α)).2 y h⟩
  have hΘnf : ∀ α, Θ α = (nf α).2 := fun α => hΘ α _ _ (hnf α)
  have hEcube : ∀ α ∈ E, α ^ 3 = 1 := fun α hα =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) α hα
  have hδ : ∀ α ∈ E, ∃ k : ℕ, k < 3 ∧ (nf α).2 = σ ^ k := by
    intro α hα
    have hψ : (nf α).2 ^ 3 = 1 := by rw [← hΘnf, ← map_pow, hEcube α hα, map_one]
    rcases mem_of_cube_eq_one_cyclic σ hσ3 hσ1 hσ2 _ hψ with h | h | h
    · exact ⟨0, by norm_num, by rw [h]; simp⟩
    · exact ⟨1, by norm_num, by rw [h]; simp⟩
    · exact ⟨2, by norm_num, h⟩
  have hcommσ : ∀ k : ℕ, σ * σ ^ k = σ ^ k * σ := fun k => (pow_mul_comm' σ k).symm
  have hgJ : ∀ α ∈ E, tauAut σ (nf α).1 = (nf α).1 := by
    intro α hα
    obtain ⟨k, -, hk⟩ := hδ α hα
    have h1 := hcomm α hα
    rw [hnf α, hk] at h1
    have e1 : MulAut.conj (nf α).1 * fieldActor (t := TwistTag.D4) σ (σ ^ k) * tauAut σ =
        MulAut.conj (nf α).1 * fieldActor (t := TwistTag.D4) σ (σ ^ k * σ) := by
      rw [fieldActor_mul]; rfl
    have e2 : tauAut σ * (MulAut.conj (nf α).1 * fieldActor (t := TwistTag.D4) σ (σ ^ k)) =
        MulAut.conj (tauAut σ (nf α).1) * fieldActor (t := TwistTag.D4) σ (σ * σ ^ k) := by
      have hc := aut_conj_conj (tauAut σ) (nf α).1
      calc tauAut σ * (MulAut.conj (nf α).1 * fieldActor (t := TwistTag.D4) σ (σ ^ k))
          = (tauAut σ * MulAut.conj (nf α).1 * (tauAut σ)⁻¹) *
              (tauAut σ * fieldActor (t := TwistTag.D4) σ (σ ^ k)) := by group
        _ = _ := by rw [hc, fieldActor_mul]
    rw [e1, e2, ← hcommσ k] at h1
    have h2 : MulAut.conj (nf α).1 = MulAut.conj (tauAut σ (nf α).1) := mul_right_cancel h1
    exact (hinj h2).symm
  have hπmul : ∀ α ∈ E, ∀ β ∈ E, (nf (α * β)).1 = (nf α).1 * (nf β).1 := by
    intro α hα β hβ
    obtain ⟨k, -, hk⟩ := hδ α hα
    have hmul := triOdd_mul_normal_form σ (hnf α) (hnf β) ⟨k, hk⟩ (hgJ β hβ)
    have h := huniq (α * β) ((nf α).1 * (nf β).1, (nf α).2 * (nf β).2) hmul
    exact congrArg Prod.fst h.symm
  let π : E →* C0 σ := MonoidHom.mk' (fun α => (nf α.1).1) (fun α β => hπmul α.1 α.2 β.1 β.2)
  have hπker : ∀ α : E, π α = 1 → α = 1 := by
    intro α hα
    have hg1 : (nf α.1).1 = 1 := hα
    obtain ⟨k, hk3, hk⟩ := hδ α.1 α.2
    have hαeq : (α : MulAut (C0 σ)) = tauAut σ ^ k := by
      have h := hnf α.1
      rwa [hg1, hk, map_one, one_mul, triOdd_fieldActor_pow] at h
    interval_cases k
    · exact Subtype.ext (by rw [hαeq]; simp)
    · exact absurd (by simpa [hαeq] using α.2) hτE
    · refine absurd ?_ hτE
      have h2 : tauAut σ ^ 2 ∈ E := hαeq ▸ α.2
      have h4 : tauAut σ = (tauAut σ ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hτ3, one_mul]
      rw [h4]
      exact E.pow_mem h2 2
  have hπinj : Function.Injective π := (injective_iff_map_eq_one π).2 hπker
  have hFG : π.range ≤ Gsub σ := by
    rintro _ ⟨α, rfl⟩
    exact hgJ α.1 α.2
  have hF3 : ∀ a ∈ π.range, a ^ 3 = 1 := by
    rintro _ ⟨α, rfl⟩
    rw [← map_pow]
    have : α ^ 3 = 1 := Subtype.ext (hEcube α.1 α.2)
    rw [this, map_one]
  have hcardF : Nat.card π.range = 3 ^ 2 :=
    (Nat.card_congr (MonoidHom.ofInjective hπinj).toEquiv).symm.trans hcard
  have hgen := gsub_le_closure_rElements_inputs2311t hℓ hℓ2 hℓ3 hf hX σ hσ π.range hFG hF3 hcardF
  refine hgen.trans ((Subgroup.closure_le _).2 ?_)
  rintro j ⟨hjG, ⟨n, hn⟩, _, ⟨α, rfl⟩, hf1, hjf⟩
  have hα1 : (α : MulAut (C0 σ)) ≠ 1 := fun h => hf1 (by
    have : α = 1 := Subtype.ext h
    rw [this, map_one])
  obtain ⟨k, -, hk⟩ := hδ α.1 α.2
  have hjτ : tauAut σ j = j := hjG
  have hfix : (α : MulAut (C0 σ)) j = j := by
    have h1 : (α : MulAut (C0 σ)) = MulAut.conj (nf α.1).1 * tauAut σ ^ k := by
      have h := hnf α.1
      rwa [hk, triOdd_fieldActor_pow] at h
    have hjf' : j * (nf α.1).1 = (nf α.1).1 * j := hjf
    rw [h1, MulAut.mul_apply, triOdd_tauPow_apply_fix σ k hjτ, MulAut.conj_apply, ← hjf',
      mul_assoc, mul_inv_cancel, mul_one]
  exact mem_uniPlaneClosure α.2 hα1 hfix hn

theorem central_tau_of_central_gline_inputs2311t (σ : X ≃+* X) (E : Subgroup (MulAut (C0 σ)))
    {γ φ : MulAut (C0 σ)} (hφ : φ * γ * φ⁻¹ = tauAut σ ∨ φ * γ * φ⁻¹ = (tauAut σ)⁻¹)
    (hcomm : ∀ α ∈ E, α * γ = γ * α) (hγE : γ ∉ E) :
    (∀ α' ∈ E.map (MulAut.congr φ).toMonoidHom, α' * tauAut σ = tauAut σ * α') ∧
      tauAut σ ∉ E.map (MulAut.congr φ).toMonoidHom := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨α, hα, rfl⟩
    have h1 : (φ * α * φ⁻¹) * (φ * γ * φ⁻¹) = (φ * γ * φ⁻¹) * (φ * α * φ⁻¹) := by
      calc (φ * α * φ⁻¹) * (φ * γ * φ⁻¹) = φ * (α * γ) * φ⁻¹ := by group
        _ = φ * (γ * α) * φ⁻¹ := by rw [hcomm α hα]
        _ = (φ * γ * φ⁻¹) * (φ * α * φ⁻¹) := by group
    show (MulAut.congr φ) α * tauAut σ = tauAut σ * (MulAut.congr φ) α
    rw [congr_apply_eq]
    rcases hφ with h | h
    · rw [h] at h1
      exact h1
    · rw [h] at h1
      have h3 : Commute (φ * α * φ⁻¹) (tauAut σ)⁻¹ := h1
      simpa using (Commute.inv_right h3).eq
  · intro hτ
    apply hγE
    have hiff : (MulAut.congr φ).toMonoidHom γ ∈ E.map (MulAut.congr φ).toMonoidHom ↔ γ ∈ E :=
      Subgroup.mem_map_iff_mem (MulAut.congr φ).injective
    rw [← hiff]
    show (MulAut.congr φ) γ ∈ _
    rw [congr_apply_eq]
    rcases hφ with h | h
    · rw [h]
      exact hτ
    · rw [h]
      exact Subgroup.inv_mem _ hτ

theorem fixedSubgroup_le_uniPlaneClosure_of_central_gline_inputs2311t {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3) (σ : X ≃+* X)
    (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut (C0 σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) {γ : MulAut (C0 σ)} (hγ : TriOddIsGLine σ γ)
    (hcomm : ∀ α ∈ E, α * γ = γ * α) (hγE : γ ∉ E) :
    fixedSubgroup γ ≤ uniPlaneClosure ℓ E := by
  classical
  obtain ⟨φ, hφ⟩ := hγ
  obtain ⟨hcomm', hτE'⟩ := central_tau_of_central_gline_inputs2311t σ E hφ hcomm hγE
  have hE' : CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr φ).toMonoidHom) :=
    isElementaryAbelian_map_three hE (MulAut.congr φ)
  have hcard' : Nat.card (E.map (MulAut.congr φ).toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective, hcard]
  have hG := gsub_le_uniPlaneClosure_of_central_tau_inputs2311t hℓ hℓ2 hℓ3 hf hX σ hσ _ hE' hcard'
    hcomm' hτE'
  rw [uniPlaneClosure_map_congr] at hG
  intro y hy
  have hγy : γ y = y := hy
  have hφy : φ y ∈ Gsub σ := by
    show tauAut σ (φ y) = φ y
    rcases hφ with h | h
    · rw [← h, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hγy]
    · have h1 : (tauAut σ)⁻¹ (φ y) = φ y := by
        rw [← h, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hγy]
      calc tauAut σ (φ y) = tauAut σ ((tauAut σ)⁻¹ (φ y)) := by rw [h1]
        _ = φ y := MulAut.apply_inv_self _ _ _
  obtain ⟨z, hz, hzy⟩ := hG hφy
  have hzy' : z = y := φ.injective hzy
  rw [← hzy']
  exact hz

theorem isGLine_conj_mul_tauAut_of_asub_inputs2311t {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3) (σ : X ≃+* X)
    (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f)) {a : C0 σ} (haA : a ∈ Asub σ) (ha3 : a ^ 3 = 1)
    (hτa : tauAut σ a = a) :
    TriOddIsGLine σ (MulAut.conj a * tauAut σ) := by
  classical
  obtain ⟨ι, hιinj, hιA, hιτ⟩ := triOdd_asub_chart σ hℓ hℓ2 hℓ3 hf hX hσ
  have hσ3 : σ ^ 3 = 1 := triOdd_sigma_pow_three σ (ℓ ^ f) hX hσ
  have hq2 : 2 ≤ ℓ ^ f := triOdd_two_le_pow hℓ hf
  have hσ1 : σ ≠ 1 := triOdd_sigma_ne_one σ (ℓ ^ f) hq2 hX hσ
  obtain ⟨M, rfl⟩ := (hιA a).1 haA
  have hMσ : Matrix.SpecialLinearGroup.map σ.toRingHom M = M := hιinj (by rw [← hιτ]; exact hτa)
  have hM3 : M ^ 3 = 1 := hιinj (by rw [map_pow, ha3, map_one])
  obtain ⟨y, hy⟩ := Inputs2311g.exists_sl2_fixSubfield_of_map_eq_excD4 σ M hMσ
  have hmapinj : Function.Injective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (fixSubfield σ).subtype) := by
    intro A B h
    apply Subtype.ext
    ext i j
    have := congrArg (fun Y : Matrix.SpecialLinearGroup (Fin 2) X =>
      (Y : Matrix (Fin 2) (Fin 2) X) i j) h
    exact this
  have hy3 : y ^ 3 = 1 := hmapinj (by rw [map_pow, hy, hM3, map_one])
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec19.sl2_lang σ hσ3 hσ1 y hy3
  rw [hy] at hg
  set t := ι g with ht
  have htτ : tauAut σ t = ι (Matrix.SpecialLinearGroup.map σ.toRingHom g) := hιτ g
  have hβ : MulAut.conj (ι M) * tauAut σ = MulAut.conj t * tauAut σ * (MulAut.conj t)⁻¹ := by
    have h2 : ι M = t * (tauAut σ t)⁻¹ := by rw [htτ, ← map_inv, ← map_mul, ← hg]
    refine MulEquiv.ext fun z => ?_
    have h3 : (MulAut.conj t)⁻¹ z = t⁻¹ * z * t := by
      rw [← map_inv, MulAut.conj_apply, inv_inv]
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, h3, MulAut.conj_apply,
      MulAut.conj_apply, map_mul, map_mul, map_inv, h2]
    group
  refine ⟨(MulAut.conj t)⁻¹, Or.inl ?_⟩
  rw [hβ]
  group

theorem exists_gsub_conj_mem_Bsub_or_Asub_inputs2311t {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3) (σ : X ≃+* X)
    (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f)) {x : C0 σ} (hxG : x ∈ Gsub σ) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) :
    ∃ y ∈ Gsub σ, y * x * y⁻¹ ∈ Bsub σ ∨ y * x * y⁻¹ ∈ Asub σ := by
  classical
  have hq2 : 2 ≤ ℓ ^ f := triOdd_two_le_pow hℓ hf
  have hℓ5 : 5 ≤ ℓ := by
    have h2 := hℓ.two_le
    rcases (by omega : ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 4 ∨ 5 ≤ ℓ) with h | h | h | h
    · exact absurd h hℓ2
    · exact absurd h hℓ3
    · subst h
      exact absurd hℓ (by norm_num)
    · exact h
  have hq5 : 5 ≤ ℓ ^ f := le_trans hℓ5 (by
    calc ℓ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf)
  have hX' : Nat.card X = ℓ ^ (3 * f) := by rw [hX, ← pow_mul]; ring_nf
  haveI : CharP X ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (k := 3 * f) (by omega) hX'
  have hK2 : ringChar X ≠ 2 := by rw [ringChar.eq X ℓ]; exact hℓ2
  have hK3 : ringChar X ≠ 3 := by rw [ringChar.eq X ℓ]; exact hℓ3
  have hσ3 : ∀ c, σ (σ (σ c)) = c := CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card
    (σ := σ.toRingHom) hX hσ
  have hσ3' : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := hσ3
  have hF : Nat.card (CFSG.LieType.Steinberg.TwistedD4.fixedField σ.toRingHom) = ℓ ^ f :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom hq2 hX hσ
  have h3 : Module.finrank (CFSG.LieType.Steinberg.TwistedD4.fixedField σ.toRingHom) X = 3 := by
    haveI : Module.Finite (CFSG.LieType.Steinberg.TwistedD4.fixedField σ.toRingHom) X :=
      Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank
      (K := CFSG.LieType.Steinberg.TwistedD4.fixedField σ.toRingHom) (V := X)
    rw [hX, hF] at h
    exact Nat.pow_right_injective hq2 h.symm
  set ε := triOddEqRoot σ (triOdd_ringChar_ne_two hℓ hℓ2 hf hX) (triOdd_two_le_pow hℓ hf) hX hσ
    with hε
  have hfixτ := triOdd_fixedSubgroup_tau_eq_map σ hσ3 (triOdd_ringChar_ne_two hℓ hℓ2 hf hX)
    (triOdd_two_le_pow hℓ hf) hX hσ
  have hGε : ∀ g ∈ CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.FixedSub σ, ε g ∈ Gsub σ := by
    intro g hg
    rw [triOdd_gsub_eq_fixedSubgroup σ, hfixτ]
    exact ⟨g, hg, rfl⟩
  have hx0 : x ∈ fixedSubgroup (tauAut σ) := hxG
  rw [hfixτ] at hx0
  obtain ⟨xt, hxtJ, hxtx⟩ := hx0
  have hxtx' : ε xt = x := hxtx
  have hxt3 : xt ^ 3 = 1 := ε.injective (by rw [map_pow, hxtx', hx3, map_one])
  have hxt1 : xt ≠ 1 := by
    rintro rfl
    apply hx1
    rw [← hxtx', map_one]
  have hS := triOdd_jClassSplitAll X σ hσ3 hK3 (by omega : 4 ≤ ℓ ^ f) hX hσ
  obtain ⟨j, hjJ, hcase⟩ := hS hK2 (by rw [hF]; omega) h3 xt hxtJ hxt3 hxt1
  rcases hcase with ⟨M, hM⟩ | ⟨M, hM⟩
  ·
    have hgJ : triOddNhat σ * j ∈ CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.FixedSub σ :=
      mul_mem (triOddNhat_mem_fixedSub σ hσ3) hjJ
    refine ⟨ε (triOddNhat σ * j), hGε _ hgJ, Or.inl ?_⟩
    have hgx : ε (triOddNhat σ * j) * x * (ε (triOddNhat σ * j))⁻¹ =
        ε (triOddNhat σ * (j * xt * j⁻¹) * (triOddNhat σ)⁻¹) := by
      rw [← hxtx', ← map_inv, ← map_mul, ← map_mul,
        show triOddNhat σ * j * xt * (triOddNhat σ * j)⁻¹ =
          triOddNhat σ * (j * xt * j⁻¹) * (triOddNhat σ)⁻¹ by group]
    rw [hgx, hM]
    show _ ∈ Subgroup.centralizer ((Asub σ : Subgroup (C0 σ)) : Set (C0 σ))
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨N, rfl⟩ := triOdd_Asub_eq_eqRoot_slShort σ hℓ hℓ2 hℓ3 hf hX hσ hσ3' a ha
    rw [← map_mul, ← map_mul]
    congr 1
    exact triOdd_slShort_le_centralizer_conj_slLong σ hσ3 M
      (CFSG.LieType.Steinberg.TwistedD4.slShort σ.toRingHom hσ3' N) ⟨N, rfl⟩
  ·
    refine ⟨ε j, hGε j hjJ, Or.inr ?_⟩
    have hjx : ε j * x * (ε j)⁻¹ = ε (j * xt * j⁻¹) := by
      rw [← hxtx', ← map_inv, ← map_mul, ← map_mul]
    rw [hjx, hM]
    exact triOdd_eqRoot_slShort_mem_Asub σ hℓ hℓ2 hℓ3 hf hX hσ hσ3' _

theorem uniPlaneClosure_eq_top_of_central_tau_inputs2311t {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3) (σ : X ≃+* X)
    (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut (C0 σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hout : ¬ E ≤ innerAut (C0 σ))
    (hcomm : ∀ α ∈ E, α * tauAut σ = tauAut σ * α) (hτE : tauAut σ ∉ E) :
    uniPlaneClosure ℓ E = ⊤ := by
  classical
  have hq2 : 2 ≤ ℓ ^ f := triOdd_two_le_pow hℓ hf
  have hX' : Nat.card X = ℓ ^ (3 * f) := by rw [hX, ← pow_mul]; ring_nf
  haveI : CharP X ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (k := 3 * f) (by omega) hX'
  have hring : ringChar X = ℓ := ringChar.eq X ℓ
  have hσ3 : σ ^ 3 = 1 := triOdd_sigma_pow_three σ (ℓ ^ f) hX hσ
  have hτ3 : tauAut σ ^ 3 = 1 := triOdd_tauAut_pow_three σ hσ3
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf X hX σ hσ
  have hinj : Function.Injective (MulAut.conj : C0 σ →* MulAut (C0 σ)) := nf1_conj_injective hZ
  obtain ⟨x, hx3, hx1, _g, _e, -, -, -, hEeq⟩ :=
    triOdd_plane_shape σ hℓ hℓ2 hf hX hσ E hE hcard hout
  have hcx : MulAut.conj x ∈ E := by rw [hEeq]; exact Subgroup.subset_closure (by simp)
  have hτx : tauAut σ x = x := by
    have h1 := hcomm _ hcx
    have h2 := aut_conj_conj (tauAut σ) x
    apply hinj
    rw [← h2, ← h1, mul_inv_cancel_right]
  obtain ⟨y, hyG, hy⟩ :=
    exists_gsub_conj_mem_Bsub_or_Asub_inputs2311t hℓ hℓ2 hℓ3 hf hX σ hσ hτx hx3 hx1
  have hτy : tauAut σ y = y := hyG
  set ψ : MulAut (C0 σ) := MulAut.conj y with hψ
  set E' := E.map (MulAut.congr ψ).toMonoidHom with hE'
  suffices h : uniPlaneClosure ℓ E' = ⊤ from (uniPlaneGen_map_congr ψ ℓ E).1 h
  have hψτ : ψ * tauAut σ * ψ⁻¹ = tauAut σ := by
    refine MulEquiv.ext fun z => ?_
    have h3 : (MulAut.conj y)⁻¹ z = y⁻¹ * z * y := by rw [← map_inv, MulAut.conj_apply, inv_inv]
    rw [hψ, MulAut.mul_apply, MulAut.mul_apply, h3, MulAut.conj_apply, map_mul, map_mul, map_inv,
      hτy]
    group
  obtain ⟨hE'ab, hcard', -⟩ := triOdd_map_congr_plane σ ψ E hE hcard hout
  obtain ⟨hcomm', hτE'⟩ := central_tau_of_central_gline_inputs2311t σ E (Or.inl hψτ) hcomm hτE
  set x' := y * x * y⁻¹ with hx'
  have hcx' : MulAut.conj x' ∈ E' := by
    refine ⟨MulAut.conj x, hcx, ?_⟩
    show (MulAut.congr ψ) (MulAut.conj x) = MulAut.conj x'
    rw [congr_apply_eq, aut_conj_conj, hψ, MulAut.conj_apply]
  have hx'3 : x' ^ 3 = 1 := by rw [hx', conj_pow, hx3]; group
  have hx'1 : x' ≠ 1 := by
    intro h
    apply hx1
    have e : x = y⁻¹ * x' * y := by rw [hx']; group
    rw [e, h]
    group
  have hτx' : tauAut σ x' = x' := by rw [hx', map_mul, map_mul, map_inv, hτy, hτx]
  have hcx'1 : MulAut.conj x' ≠ 1 := fun h => hx'1 (hinj (h.trans (map_one _).symm))
  have hJ := gsub_le_uniPlaneClosure_of_central_tau_inputs2311t hℓ hℓ2 hℓ3 hf hX σ hσ E' hE'ab
    hcard' hcomm' hτE'
  obtain ⟨-, hAgen, hsup, -⟩ := Inputs2311g.triality_tau_facts_excD4 hℓ hℓ2 hℓ3 hf hX σ hσ
  rcases hy with hB | hA
  ·
    have hAH : Asub σ ≤ uniPlaneClosure ℓ E' := by
      refine hAgen.trans ((Subgroup.closure_le _).2 ?_)
      rintro s ⟨hs, hsr⟩
      refine mem_uniPlaneClosure (n := 1) hcx' hcx'1 ?_ (by rw [pow_one, ← hring]; exact hsr)
      have hc : s * x' = x' * s := Subgroup.mem_centralizer_iff.1 hB s hs
      rw [MulAut.conj_apply, ← hc, mul_inv_cancel_right]
    rw [eq_top_iff, ← hsup]
    exact sup_le (by rw [← triOdd_gsub_eq_fixedSubgroup]; exact hJ) hAH
  ·
    set E₁ := Subgroup.closure ({tauAut σ, MulAut.conj x'} : Set (MulAut (C0 σ))) with hE₁
    have hτE₁ : tauAut σ ∈ E₁ := Subgroup.subset_closure (by simp)
    have hcxE₁ : MulAut.conj x' ∈ E₁ := Subgroup.subset_closure (by simp)
    have htop₁ := Inputs2311g.uniPlaneClosure_triality_tauA_excD4 hℓ hℓ2 hℓ3 hf hX σ hσ hτE₁ hA
      hx'1 hx'3 hτx' hcxE₁
    rw [hring] at htop₁
    rw [eq_top_iff, ← htop₁]
    refine (Subgroup.closure_le _).2 ?_
    rintro s ⟨e₁, he₁, he₁1, hs, n, hn⟩
    have hcx'3 : MulAut.conj x' ^ 3 = 1 := by rw [← map_pow, hx'3, map_one]
    have hτc : tauAut σ * MulAut.conj x' = MulAut.conj x' * tauAut σ := by
      have h2 := aut_conj_conj (tauAut σ) x'
      rw [hτx'] at h2
      exact mul_inv_eq_iff_eq_mul.1 h2
    have hτc' : Commute (tauAut σ) (MulAut.conj x') := hτc
    have hGline : ∀ m : ℕ,
        fixedSubgroup (MulAut.conj x' ^ m * tauAut σ) ≤ uniPlaneClosure ℓ E' := by
      intro m
      refine fixedSubgroup_le_uniPlaneClosure_of_central_gline_inputs2311t hℓ hℓ2 hℓ3 hf hX σ hσ E'
        hE'ab hcard' ?_ ?_ ?_
      · rw [← map_pow MulAut.conj x' m]
        exact isGLine_conj_mul_tauAut_of_asub_inputs2311t hℓ hℓ2 hℓ3 hf hX σ hσ (pow_mem hA m)
          (by rw [← pow_mul, mul_comm, pow_mul, hx'3, one_pow]) (by rw [map_pow, hτx'])
      · intro α hα
        have h1 : Commute α (MulAut.conj x') := elemAb_comm hE'ab _ hα _ hcx'
        have h2 : Commute α (tauAut σ) := hcomm' α hα
        exact ((h1.pow_right m).mul_right h2).eq
      · intro hmem
        apply hτE'
        have e : tauAut σ = (MulAut.conj x' ^ m)⁻¹ * (MulAut.conj x' ^ m * tauAut σ) := by group
        rw [e]
        exact mul_mem (inv_mem (pow_mem hcx' m)) hmem
    obtain ⟨a, b, ha, hb, rfl⟩ :=
      Parrott.ClosingMinus.Escape.closure_pair_normal_form hτ3 hcx'3 hτc he₁
    have hs' : (tauAut σ ^ a * MulAut.conj x' ^ b) s = s := hs
    interval_cases a
    ·
      have hb' : b = 1 ∨ b = 2 := by
        rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with h | h | h
        · exfalso
          apply he₁1
          rw [h, pow_zero, pow_zero, one_mul]
        · exact Or.inl h
        · exact Or.inr h
      have hfix : MulAut.conj x' s = s := by
        rcases hb' with rfl | rfl
        · simpa using hs'
        · have h2 : (MulAut.conj x' ^ 2) s = s := by
            rw [pow_zero, one_mul] at hs'
            exact hs'
          have h4 : MulAut.conj x' = (MulAut.conj x' ^ 2) ^ 2 := by
            rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hcx'3, one_mul]
          rw [h4, pow_two (MulAut.conj x' ^ 2), MulAut.mul_apply, h2, h2]
      exact mem_uniPlaneClosure hcx' hcx'1 hfix hn
    ·
      have e : tauAut σ ^ 1 * MulAut.conj x' ^ b = MulAut.conj x' ^ b * tauAut σ := by
        rw [pow_one]
        exact (hτc'.pow_right b).eq
      rw [e] at hs'
      exact hGline b hs'
    ·
      have hsq : (tauAut σ ^ 2 * MulAut.conj x' ^ b) ^ 2 = MulAut.conj x' ^ (2 * b) * tauAut σ := by
        have hc : Commute (tauAut σ ^ 2) (MulAut.conj x' ^ b) := hτc'.pow_pow 2 b
        rw [hc.mul_pow, ← pow_mul (tauAut σ) 2 2, ← pow_mul (MulAut.conj x') b 2,
          show 2 * 2 = 3 + 1 from rfl, pow_succ, hτ3, one_mul, mul_comm b 2]
        exact (hτc'.pow_right (2 * b)).eq
      have hfix2 : (MulAut.conj x' ^ (2 * b) * tauAut σ) s = s := by
        rw [← hsq, pow_two, MulAut.mul_apply, hs', hs']
      exact hGline (2 * b) hfix2

theorem uniPlaneClosure_eq_top_of_central_gline_inputs2311t {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3) (σ : X ≃+* X)
    (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut (C0 σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hout : ¬ E ≤ innerAut (C0 σ)) {γ : MulAut (C0 σ)}
    (hγ : TriOddIsGLine σ γ) (hcomm : ∀ α ∈ E, α * γ = γ * α) (hγE : γ ∉ E) :
    uniPlaneClosure ℓ E = ⊤ := by
  obtain ⟨φ, hφ⟩ := hγ
  obtain ⟨hcomm', hτE'⟩ := central_tau_of_central_gline_inputs2311t σ E hφ hcomm hγE
  obtain ⟨hE', hcard', hout'⟩ := triOdd_map_congr_plane σ φ E hE hcard hout
  exact (uniPlaneGen_map_congr φ ℓ E).1
    (uniPlaneClosure_eq_top_of_central_tau_inputs2311t hℓ hℓ2 hℓ3 hf hX σ hσ _ hE' hcard' hout'
      hcomm' hτE')

end Central

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311t
