module

public import CFSG.ClassicalInvolution.Q3.Q3TJStmt
public import CFSG.ClassicalInvolution.Q3.Q3ExcTwD4
public import CFSG.ClassicalInvolution.AschTight.S19FChartD4

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
open CFSG.ComponentClassification
open scoped MatrixGroups

abbrev F27 : Type := GaloisField 3 (3 * 1)

noncomputable abbrev σe27 : F27 ≃+* F27 := iterateFrobeniusEquiv F27 3 1

noncomputable abbrev σ27 : F27 →+* F27 := iterateFrobenius F27 3 1

theorem σ27_apply (c : F27) : σ27 c = c ^ 3 := by
  rw [iterateFrobenius_def, pow_one]

theorem σ27_cube (c : F27) : σ27 (σ27 (σ27 c)) = c := sigma_three_td4 (p := 3) 1 le_rfl c

theorem trace_glConjSL {F : Type} [Field F] (D : GL (Fin 2) F) (A : SL(2, F)) :
    Matrix.trace ((glConjSL D A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) := by
  rw [glConjSL_coe, Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul]

noncomputable def traceSL (s : F27) : SL(2, F27) :=
  ⟨!![s, -1; 1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

theorem eq_conj_of_fix_slShort_td4 (β : MulAut (twistedGroup σ27))
    (hβ : ∀ A : SL(2, F27), β (slShort σ27 σ27_cube A) = slShort σ27 σ27_cube A) :
    ∃ g : twistedGroup σ27, β = MulAut.conj g := by
  have hσ' : ∀ c, σe27 c = c ^ (3 ^ 1) := fun c => iterateFrobeniusEquiv_def F27 3 1 c
  have hK : Nat.card F27 = (3 ^ 1) ^ 3 := by
    rw [GaloisField.card 3 (3 * 1) (by norm_num)]
    norm_num
  obtain ⟨hfa, hnf, ⟨Θ, hΘ, -, hker, -⟩, -⟩ := odd_triality_exact_automorphism_normal_form
    Nat.prime_three (by norm_num) le_rfl F27 hK σe27 hσ'
  have hrange : (twistedIncl σ27).range = graphFixedRootGroup TwistTag.D4 F27 σ27 :=
    range_twistedIncl_eq (p := 3) (by norm_num) 1 le_rfl
  have hC : graphFixedRootGroup TwistTag.D4 F27 σ27 =
      graphFixedRootGroup TwistTag.D4 F27 σe27.toRingHom := rfl
  let ι : twistedGroup σ27 ≃* ↥(graphFixedRootGroup TwistTag.D4 F27 σe27.toRingHom) :=
    (MonoidHom.ofInjective (twistedIncl_injective σ27)).trans
      (MulEquiv.subgroupCongr (hrange.trans hC))
  have hι : ∀ x, ((ι x : graphFixedRootGroup TwistTag.D4 F27 σe27.toRingHom) : ModGL d4 F27) =
      twistedIncl σ27 x := fun x => by
    show ((MonoidHom.ofInjective (twistedIncl_injective σ27) x : (twistedIncl σ27).range) :
      ModGL d4 F27) = _
    rw [MonoidHom.ofInjective_apply]
  let γ : MulAut ↥(graphFixedRootGroup TwistTag.D4 F27 σe27.toRingHom) := MulAut.congr ι β
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hnf γ
  have hδσ : ∀ c, δ (σ27 c) = σ27 (δ c) := fun c => by
    rw [σ27_apply, σ27_apply, map_pow]
  have hfix : ∀ A : SL(2, F27), (g : ModGL d4 F27) *
      twistedIncl σ27 (slShort σ27 σ27_cube (Matrix.SpecialLinearGroup.map δ.toRingHom A)) *
        (g : ModGL d4 F27)⁻¹ = twistedIncl σ27 (slShort σ27 σ27_cube A) := by
    intro A
    have h1 : γ (ι (slShort σ27 σ27_cube A)) = ι (slShort σ27 σ27_cube A) := by
      show ι (β (ι.symm (ι (slShort σ27 σ27_cube A)))) = ι (slShort σ27 σ27_cube A)
      rw [MulEquiv.symm_apply_apply, hβ]
    rw [hgδ, MulAut.mul_apply, MulAut.conj_apply] at h1
    have h2 := congrArg (fun y : graphFixedRootGroup TwistTag.D4 F27 σe27.toRingHom =>
      (y : ModGL d4 F27)) h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [hfa δ (ι (slShort σ27 σ27_cube A)), hι,
      Disconnected.AschTight.S19F.slShort_entrywise σ27_cube δ hδσ A] at h2
    exact h2
  set g' := ι.symm g with hg'def
  have hg' : (g : ModGL d4 F27) = twistedIncl σ27 g' := by
    calc (g : ModGL d4 F27) =
        ((ι (ι.symm g) : graphFixedRootGroup TwistTag.D4 F27 σe27.toRingHom) : ModGL d4 F27) := by
          rw [MulEquiv.apply_symm_apply]
      _ = twistedIncl σ27 g' := hι _
  have hconjA : ∀ A : SL(2, F27), g' * slShort σ27 σ27_cube
      (Matrix.SpecialLinearGroup.map δ.toRingHom A) * g'⁻¹ = slShort σ27 σ27_cube A := by
    intro A
    apply twistedIncl_injective σ27
    rw [map_mul, map_mul, map_inv, ← hg', hfix A]
  have hneg : Matrix.SpecialLinearGroup.map δ.toRingHom (-1 : SL(2, F27)) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hcomm : g' * slShort σ27 σ27_cube (-1) = slShort σ27 σ27_cube (-1) * g' := by
    have h := hconjA (-1)
    rw [hneg] at h
    calc g' * slShort σ27 σ27_cube (-1) = g' * slShort σ27 σ27_cube (-1) * g'⁻¹ * g' := by group
      _ = slShort σ27 σ27_cube (-1) * g' := by rw [h]
  have hK1 := neg_one_ne_one_galoisField_td4 (p := 3) (by norm_num) (3 * 1)
  have h2 : (2 : F27) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F27) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F27 3] at h'
    norm_num at h'
  have hC₀ : graphFixedRootGroup TwistTag.D4 F27 σ27 ≤ (twistedIncl σ27).range := hrange.ge
  have hgF : ∀ x : twistedGroup σ27, twistedIncl σ27 x ∈ graphFixedRootGroup TwistTag.D4 F27 σ27 :=
    fun x => hrange ▸ ⟨x, rfl⟩
  obtain ⟨D, hD⟩ := linAct_of_centralizes_short σ27_cube hK1 h2 hC₀ hgF hcomm
  have hA : ∀ A : SL(2, F27), A = glConjSL D (Matrix.SpecialLinearGroup.map δ.toRingHom A) := by
    intro A
    apply slShort_injective σ27_cube
    rw [← hD, hconjA]
  have hδ : δ = 1 := by
    ext s
    have h := congrArg (fun B : SL(2, F27) => Matrix.trace (B : Matrix (Fin 2) (Fin 2) F27))
      (hA (traceSL s))
    simp only [trace_glConjSL] at h
    have h1 : Matrix.trace ((traceSL s : SL(2, F27)) : Matrix (Fin 2) (Fin 2) F27) = s := by
      simp [traceSL, Matrix.trace_fin_two]
    have h2 : Matrix.trace ((Matrix.SpecialLinearGroup.map δ.toRingHom (traceSL s) : SL(2, F27)) :
        Matrix (Fin 2) (Fin 2) F27) = δ s := by
      rw [Matrix.trace_fin_two, Matrix.SpecialLinearGroup.map_apply_coe]
      simp [traceSL]
    rw [h1, h2] at h
    exact h.symm
  have hγ : γ ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 F27 σe27.toRingHom →* _).range := by
    rw [← hker, MonoidHom.mem_ker, hΘ γ g δ hgδ, hδ]
  obtain ⟨c, hc⟩ := hγ
  refine ⟨ι.symm c, (MulAut.congr ι).injective ?_⟩
  rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, hc]

theorem eq_conj_of_centralizes_td4 {X : Type} [Group X] (e : twistedGroup σ27 ≃* X) {z : X}
    (hz2 : orderOf z = 2) (α : MulAut X)
    (hcent : ∀ c ∈ Subgroup.centralizer ({z} : Set X), α c = c) :
    ∃ g : X, α = MulAut.conj g := by
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = slShort σ27 σ27_cube (-1) := ⟨_, rfl⟩
  have hτ2 : τ * τ = 1 := by rw [hτ, ← map_mul, neg_one_mul_neg_one_SL2, map_one]
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [hτ, ← map_one (slShort σ27 σ27_cube)] at h
    have h2 := congrArg (fun B : SL(2, F27) => (B : Matrix (Fin 2) (Fin 2) F27) 0 0)
      (slShort_injective σ27_cube h)
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h2
    have hK1 := neg_one_ne_one_galoisField_td4 (p := 3) (by norm_num) (3 * 1)
    exact hK1 (Units.ext (by simpa using h2))
  have hcen : ∀ A : SL(2, F27), A * (-1) = (-1) * A := fun A => by
    ext i j
    simp
  obtain ⟨z', hz'⟩ : ∃ z', z' = e.symm z := ⟨_, rfl⟩
  have hz'2 : z' * z' = 1 := by
    rw [hz', ← map_mul, ← pow_two, ← hz2, pow_orderOf_eq_one, map_one]
  have hz'1 : z' ≠ 1 := by
    intro h
    have h1 : z = 1 := by rw [← e.apply_symm_apply z, ← hz', h, map_one]
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  obtain ⟨h, hh⟩ := CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj
    (p := 3) (by norm_num) le_rfl hz'2 hτ2 hz'1 hτ1
  obtain ⟨ε, hε⟩ : ∃ ε : X ≃* twistedGroup σ27, ε = e.symm.trans (MulAut.conj h) := ⟨_, rfl⟩
  have hεz : ε z = τ := by
    rw [hε, MulEquiv.trans_apply, ← hz', MulAut.conj_apply]
    exact hh
  have hcg : ∀ y, MulAut.congr ε α y = ε (α (ε.symm y)) := fun y => rfl
  have hβ : ∀ A : SL(2, F27), MulAut.congr ε α (slShort σ27 σ27_cube A) =
      slShort σ27 σ27_cube A := by
    intro A
    have h1 : slShort σ27 σ27_cube A * τ = τ * slShort σ27 σ27_cube A := by
      rw [hτ]
      calc slShort σ27 σ27_cube A * slShort σ27 σ27_cube (-1) =
          slShort σ27 σ27_cube (A * -1) := (map_mul _ _ _).symm
        _ = slShort σ27 σ27_cube (-1 * A) := by rw [hcen A]
        _ = slShort σ27 σ27_cube (-1) * slShort σ27 σ27_cube A := map_mul _ _ _
    have h2 : ε.symm τ = z := by rw [← hεz, MulEquiv.symm_apply_apply]
    have hc : ε.symm (slShort σ27 σ27_cube A) ∈ Subgroup.centralizer ({z} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ε.symm (slShort σ27 σ27_cube A) * z =
          ε.symm (slShort σ27 σ27_cube A) * ε.symm τ := by rw [h2]
        _ = ε.symm (slShort σ27 σ27_cube A * τ) := (map_mul _ _ _).symm
        _ = ε.symm (τ * slShort σ27 σ27_cube A) := by rw [h1]
        _ = ε.symm τ * ε.symm (slShort σ27 σ27_cube A) := map_mul _ _ _
        _ = z * ε.symm (slShort σ27 σ27_cube A) := by rw [h2]
    rw [hcg, hcent _ hc, MulEquiv.apply_symm_apply]
  obtain ⟨g, hg⟩ := eq_conj_of_fix_slShort_td4 (MulAut.congr ε α) hβ
  refine ⟨ε.symm g, (MulAut.congr ε).injective ?_⟩
  rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, ← hg]

theorem trialityD4OddAutInner3_proved : TrialityD4OddAutInner3 := by
  intro X _ _ hX hZ f hf hker z K hKz α hodd hfix
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .trialityD4 0 3 1 :=
    ⟨Nat.prime_three, le_rfl, rfl⟩
  have hz2 := hKz.orderOf_eq_two
  have hOC : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set X)) = ⊥ :=
    oddCentralizerFreeTag_trialityD4 0 Nat.prime_three trivial hadm X f hf hker z hz2
  have hcent : ∀ c ∈ Subgroup.centralizer ({z} : Set X), α c = c := by
    intro c hc
    have h := hfix c hc
    rw [hOC, Subgroup.mem_bot] at h
    calc α c = c * (c⁻¹ * α c) := by group
      _ = c := by rw [h, mul_one]
  have hZ0 := exc3_center_trialityD4 0 Nat.prime_three
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [hZ0] at hker
    exact le_bot_iff.mp hker
  exact eq_conj_of_centralizes_td4 (MulEquiv.ofBijective f ⟨hinj, hf⟩) hz2 α hcent

end CFSG.ClassicalInvolution.Q3.Q3T
