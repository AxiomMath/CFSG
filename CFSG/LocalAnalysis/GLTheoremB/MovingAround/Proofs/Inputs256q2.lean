module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256q
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256p2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256q

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256p (TwoEltLayerOn IsGF4RestIdx IsOrthIdxGF4)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

section Models

theorem statedClassicalModel_D_gf4 {S : Type} [Group S] {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) (hq4 : q.card = 4)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group) :
    StatedClassicalModel S .POmegaPlus r 2 2 := by
  obtain ⟨hp2, he2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 2)
    Nat.prime_two (by norm_num) (hq4.trans (by norm_num))
  obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_D r q hv eS
  · rw [hp2, he2] at hSC
    exact hSC
  · have h4 : 4 ≤ r := hadm.2.2
    omega

theorem statedClassicalModel_twistedD_gf4 {S : Type} [Group S] {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (hq4 : q.card = 4)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group) :
    StatedClassicalModel S .POmegaMinus r 2 2 := by
  obtain ⟨hp2, he2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 2)
    Nat.prime_two (by norm_num) (hq4.trans (by norm_num))
  obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_twistedD r q hv eS
  · rw [hp2, he2] at hSC
    exact hSC
  · have h4 : 4 ≤ r := hadm.2.2
    omega

end Models

section Inner

theorem twoEltLayer_orth_of_inner {S : Type} [Group S] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsOrthIdxGF4 d) (eS : S ≃* (TauCeti.CFSGIndex.lie d).Group) (β : MulAut S)
    (hβ : orderOf β = 3) (hinn : β ∈ (MulAut.conj : S →* MulAut S).range) (s : S) (hs : β s = s)
    (hs2 : ∃ n : ℕ, s ^ (2 ^ n) = 1) : s ∈ GLALayer (fixSubgroup β) := by
  obtain ⟨n, hn⟩ := hs2
  obtain ⟨d, hv⟩ := d
  obtain ⟨r, q, hdq | hdq, hq4⟩ := hd
  · simp only at hdq
    subst hdq
    exact twoElement_mem_glaLayer_inner_omega_gf4 (Or.inl rfl)
      (statedClassicalModel_D_gf4 hv hq4 eS) β hβ hinn hs hn
  · simp only at hdq
    subst hdq
    exact twoElement_mem_glaLayer_inner_omega_gf4 (Or.inr rfl)
      (statedClassicalModel_twistedD_gf4 hv hq4 eS) β hβ hinn hs hn

end Inner

section AllInner

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData


theorem mem_inner_of_orthIdxGF4 {S : Type} [Group S] [Finite S] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsOrthIdxGF4 d) (hnD4 : ¬ ∃ q : TauCeti.PrimePower, d.1 = .D 4 q)
    (eS : S ≃* (TauCeti.CFSGIndex.lie d).Group) (β : MulAut S) (hβ : orderOf β = 3) :
    β ∈ (MulAut.conj : S →* MulAut S).range := by
  have hβ3 : β ^ 3 = 1 := hβ ▸ pow_orderOf_eq_one β
  obtain ⟨r, q, hdq, hq4⟩ := hd
  obtain ⟨hp2, -⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 2)
    Nat.prime_two (by norm_num) (hq4.trans (by norm_num))
  have hd2 : d.1.characteristic = 2 := by
    rcases hdq with h | h <;> rw [h]
    · rw [TauCeti.LieTypeIndex.characteristic_D, hp2]
    · rw [TauCeti.LieTypeIndex.characteristic_twistedD, hp2]
  have hd4 : Inputs256c.defField d.1 = 4 := by
    rcases hdq with h | h <;> rw [h] <;> exact hq4
  have hnot : ¬ ∃ q' : TauCeti.PrimePower, d.1 = .trialityD4 q' := by
    rintro ⟨q', hq'⟩
    rcases hdq with h | h <;> rw [h] at hq' <;> cases hq'
  have hmem := Inputs256p.mem_innAutDerived_of_orderOf_three_gf4 hd2 hd4 hnot eS β hβ
  obtain ⟨d, hv⟩ := d
  rcases hdq with hdq | hdq
  · simp only at hdq
    subst hdq
    have hr4 : 4 ≤ r :=
      ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    have hr5 : 5 ≤ r := by
      rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | h
      · exact absurd ⟨q, rfl⟩ hnD4
      · exact h
    have hSC := statedClassicalModel_D_gf4 hv hq4 eS
    have hSC0 := hSC
    obtain ⟨-, K, hKf, hKfin, hK, ⟨e₀⟩⟩ := hSC0
    letI := hKf
    letI := hKfin
    obtain ⟨-, -, -, hinner⟩ := matrixModel_facts_pomegaPlus hSC hr5 hK e₀
    have h1 : MulAut.congr (coordinatePlusWitnessEquiv K e₀) β ∈
        innAutDerived (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveDerived
          (coordinateQuadPlus r K)) := (mem_innAutDerived_congr _).mpr hmem
    obtain ⟨g, hg⟩ := hinner 3 Nat.prime_three (by norm_num) _ h1
      (by rw [← map_pow, hβ3, map_one])
    obtain ⟨a, ha⟩ := Inputs256p.exists_conj_eq_of_conj_eq_mulAutCongr _ hg
    exact ⟨a, ha⟩
  · simp only at hdq
    subst hdq
    have hr4 : 4 ≤ r :=
      ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    have hSC := statedClassicalModel_twistedD_gf4 hv hq4 eS
    have hSC0 := hSC
    obtain ⟨-, K, hKf, hKfin, hK, b, c, hirr, ⟨e₀⟩⟩ := hSC0
    letI := hKf
    letI := hKfin
    have hn1 : 1 ≤ r := by omega
    obtain ⟨-, -, -, hinner⟩ := matrixModel_facts_pomegaMinus hSC hK hn1 b c hirr e₀
    have h1 : MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e₀) β ∈
        innAutDerived (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveDerived
          (coordinateQuadMinus r K hn1 b c)) := (mem_innAutDerived_congr _).mpr hmem
    obtain ⟨g, hg⟩ := hinner 3 Nat.prime_three (by norm_num) _ h1
      (by rw [← map_pow, hβ3, map_one])
    obtain ⟨a, ha⟩ := Inputs256p.exists_conj_eq_of_conj_eq_mulAutCongr _ hg
    exact ⟨a, ha⟩

theorem twoEltLayerOn_orthNoD4 :
    TwoEltLayerOn fun d => IsOrthIdxGF4 d ∧ ¬ ∃ q : TauCeti.PrimePower, d.1 = .D 4 q := by
  intro S _ _ d hd ⟨eS⟩ β hβ s hs hs2
  exact twoEltLayer_orth_of_inner hd.1 eS β hβ (mem_inner_of_orthIdxGF4 hd.1 hd.2 eS β hβ) s hs hs2

end AllInner

section Statements

@[expose] def IsExcGF4RestIdx (d : TauCeti.ValidLieTypeIndex) : Prop :=
  IsGF4RestIdx d ∧ ¬ IsOrthIdxGF4 d

@[expose] def TwoEltLayerRest : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), IsExcGF4RestIdx d →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ β : MulAut S, orderOf β = 3 →
      ((∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q) → β ∈ (MulAut.conj : S →* MulAut S).range) →
      ∀ s : S, β s = s → (∃ n : ℕ, s ^ (2 ^ n) = 1) → s ∈ GLALayer (fixSubgroup β)

end Statements

section TwoEltPerfect

open CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def TwoEltInPerfect (X : Type*) [Group X] : Prop :=
  ∀ x : X, (∃ n : ℕ, x ^ 2 ^ n = 1) → ∃ P : Subgroup X, ⁅P, P⁆ = P ∧ x ∈ P

theorem TwoEltInPerfect.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : TwoEltInPerfect Y) : TwoEltInPerfect X := by
  rintro x ⟨n, hn⟩
  obtain ⟨P, hP, hxP⟩ := h (e x) ⟨n, by rw [← map_pow, hn, map_one]⟩
  exact ⟨P.map e.symm.toMonoidHom, by rw [← Subgroup.map_commutator, hP], ⟨e x, hxP, by simp⟩⟩

theorem twoEltInPerfect_of_isPerfect {X : Type*} [Group X] (h : Group.IsPerfect X) :
    TwoEltInPerfect X := by
  intro x _
  haveI := h
  exact ⟨⊤, by rw [← commutator_def, Group.IsPerfect.commutator_eq_top], Subgroup.mem_top x⟩

theorem mem_glaLayer_of_twoEltInPerfect {S : Type*} [Group S] {β : MulAut S}
    (hL : PerfectInLayer β) (h : TwoEltInPerfect ↥(fixSubgroup β)) {s : S} (hs : β s = s)
    {m : ℕ} (hsm : s ^ 2 ^ m = 1) : s ∈ GLALayer (fixSubgroup β) := by
  obtain ⟨P, hP, hsP⟩ := h ⟨s, mem_fixSubgroup.mpr hs⟩ ⟨m, Subtype.ext (by simpa using hsm)⟩
  refine hL (P.map (fixSubgroup β).subtype) (Subgroup.map_subtype_le _) ?_ ⟨_, hsP, rfl⟩
  rw [← Subgroup.map_commutator, hP]

end TwoEltPerfect

section PGLThree

open CFSG.RankThree.PartTwo CFSG.PGLModel

theorem twoEltInPerfect_projImage_glPi_four {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ 2) :
    TwoEltInPerfect ↥(projImage (Sec4.glPi true 3 (2 ^ 2) F)) := by
  classical
  rintro g ⟨n, hn⟩
  have hK : Sec4.PiField true 2 2 F := ⟨Nat.prime_two, by norm_num, hF⟩
  have hSP : projImage (Sec4.slPi true 3 (2 ^ 2) F) ≤ projImage (Sec4.glPi true 3 (2 ^ 2) F) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi (fun h => absurd h (by decide)))
  haveI : Group.IsPerfect ↥(projImage (Sec4.slPi true 3 (2 ^ 2) F)) :=
    Sec13.isPerfect_projImage_slPi hK (by norm_num)
  refine ⟨(projImage (Sec4.slPi true 3 (2 ^ 2) F)).subgroupOf
    (projImage (Sec4.glPi true 3 (2 ^ 2) F)), ?_, ?_⟩
  · have e := Subgroup.subgroupOfEquivOfLe hSP
    exact Subgroup.isPerfect_iff.1
      (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)
  · rw [Subgroup.mem_subgroupOf]
    obtain ⟨A, -, hA⟩ := g.2
    have hgn : (g : Matrix.ProjGenLinGroup (Fin 3) F) ^ 2 ^ n = 1 := by
      simpa using congrArg Subtype.val hn
    rw [← hA, ← map_pow, Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.center_eq_range_scalar] at hgn
    obtain ⟨u, hu⟩ := hgn
    have hu3 : u ^ 3 = 1 := by
      have h1 : u ^ Nat.card Fˣ = 1 := pow_card_eq_one'
      rwa [Nat.card_units, hF] at h1
    have hdet2 : Matrix.GeneralLinearGroup.det A ^ 2 ^ n = 1 := by
      rw [← map_pow, ← hu, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, hu3]
    have hdet3 : Matrix.GeneralLinearGroup.det A ^ 3 = 1 := by
      have h1 : Matrix.GeneralLinearGroup.det A ^ Nat.card Fˣ = 1 := pow_card_eq_one'
      rwa [Nat.card_units, hF] at h1
    have hcop : Nat.gcd (2 ^ n) 3 = 1 := Nat.Coprime.pow_left n (by norm_num)
    have hdet : Matrix.GeneralLinearGroup.det A = 1 := by
      have h1 := pow_gcd_eq_one.mpr ⟨hdet2, hdet3⟩
      rwa [hcop, pow_one] at h1
    have hdet' : (A : Matrix (Fin 3) (Fin 3) F).det = 1 := by
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using congrArg Units.val hdet
    exact ⟨A, Subgroup.subset_closure hdet', hA⟩

theorem ringEquiv_sq_eq_one_of_card_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (σ : F ≃+* F) : σ ^ 2 = 1 := by
  classical
  haveI := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hcard : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]
  have key : ∀ x : F, σ x = x ∨ σ x = x + 1 := by
    intro x
    have hx4 : x ^ 4 = x := by
      have := FiniteField.pow_card x
      rwa [hcard] at this
    have hy : (x ^ 2 + x) * (x ^ 2 + x - 1) = 0 := by
      linear_combination hx4 + x ^ 3 * h2
    have hσy : σ x ^ 2 + σ x = x ^ 2 + x := by
      rcases mul_eq_zero.mp hy with h | h
      · have h' := congrArg σ h
        rw [map_add, map_pow, map_zero] at h'
        rw [h', h]
      · have h' := congrArg σ (sub_eq_zero.mp h)
        rw [map_add, map_pow, map_one] at h'
        rw [h', sub_eq_zero.mp h]
    have h0 : (σ x - x) * (σ x - x - 1) = 0 := by
      linear_combination hσy + (x ^ 2 + x - σ x - σ x * x) * h2
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · right
      linear_combination h
  refine RingEquiv.ext fun x => ?_
  show σ (σ x) = x
  rcases key x with h | h
  · rw [h, h]
  · rw [h, map_add, map_one, h]
    linear_combination h2

end PGLThree

section Triality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple


theorem twoEltInPerfect_fixSubgroup_triality_outer_four {K₃ : Type} [Field K₃] [Finite K₃]
    (hK₃ : Nat.card K₃ = (2 ^ 2) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (2 ^ 2))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    TwoEltInPerfect ↥(fixSubgroup φ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite K₃
  haveI : CharP K₃ 2 := charP_of_card_eq_prime_pow (f := 6)
    (by rw [← Nat.card_eq_fintype_card, hK₃]; norm_num)
  have hK2 : ringChar K₃ = 2 := ringChar.eq K₃ 2
  set σ₀ := fieldActor (t := TwistTag.D4) Fr Fr with hσ₀
  have hG2 : TwoEltInPerfect ↥(fixSubgroup σ₀) := by
    obtain ⟨e⟩ := KFacts.nonempty_fixedPoints_fieldActor_mulEquiv_g2 (σ := Fr) hK2
    have hfix : fixSubgroup σ₀ = σ₀.toMonoidHom.eqLocus (MonoidHom.id _) :=
      Subgroup.ext fun _ => Iff.rfl
    have hcard := KFacts.card_fixSubfield_of_cube (f := 2) (by norm_num) hK₃ hFr
    have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (fixSubfield Fr)
      (by rw [hcard]; norm_num)
    exact (twoEltInPerfect_of_isPerfect hq.1).of_mulEquiv ((MulEquiv.subgroupCongr hfix).trans e)
  have hconj : ∀ β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom),
      MulAut.congr β σ₀ = β * σ₀ * β⁻¹ := fun β => MulEquiv.ext fun _ => rfl
  rcases Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv (f := 2) (by norm_num)
      hK₃ hFr hφ3 hφ with ⟨β, hβ | hβ⟩ | he₂
  · have hfix : fixSubgroup φ = fixSubgroup (MulAut.congr β σ₀) := by rw [hconj, hβ]
    exact hG2.of_mulEquiv
      ((MulEquiv.subgroupCongr hfix).trans (LieComp.fixSubgroupCongrEquiv β σ₀).symm)
  · have hfix : fixSubgroup φ = fixSubgroup (MulAut.congr β σ₀⁻¹) := by
      rw [show MulAut.congr β σ₀⁻¹ = β * σ₀⁻¹ * β⁻¹ from MulEquiv.ext fun _ => rfl, hβ]
    have hG2' : TwoEltInPerfect ↥(fixSubgroup σ₀⁻¹) :=
      hG2.of_mulEquiv (MulEquiv.subgroupCongr (fixSubgroup_inv_eq σ₀))
    exact hG2'.of_mulEquiv
      ((MulEquiv.subgroupCongr hfix).trans (LieComp.fixSubgroupCongrEquiv β σ₀⁻¹).symm)
  · obtain ⟨e₂⟩ := he₂
    obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ :=
      Sec8.kF82D4SecondCentY0Even_holds 2 (by decide) (by norm_num) K₃ Fr hK₃ hFr
    have hfix : fixSubgroup φ = Sec4.autFix φ := Subgroup.ext fun _ => Iff.rfl
    exact (twoEltInPerfect_projImage_glPi_four hF).of_mulEquiv
      ((MulEquiv.subgroupCongr hfix).trans (e₂.trans e₃))

theorem twoEltInPerfect_fixSubgroup_d4_noninner_four {S : Type} [Group S]
    (hS : StatedClassicalModel S .POmegaPlus 4 2 2) (β : MulAut S) (hβ3 : β ^ 3 = 1)
    (hinn : β ∉ (MulAut.conj : S →* MulAut S).range) : TwoEltInPerfect ↥(fixSubgroup β) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, hFf, hFfin, hF, ⟨eG⟩⟩ := hS
  letI := hFf
  letI := hFfin
  haveI := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨eC⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup F
  set e₂ : S ≃* ↥(adjointGroup Tag.D4 F) := eG.trans eC with he₂
  have hα : MulAut.congr e₂ β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  obtain ⟨g, a, σ, ε, hε, hσ3, hαeq⟩ := exists_cube_normal_form_sigma _ hα
  have hσ1 : σ = 1 := by
    have h2 := ringEquiv_sq_eq_one_of_card_four (by rw [hF]; norm_num) σ
    calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hσ3, h2]; group
  subst hσ1
  have hchar : ringChar F ≠ 3 := by rw [ringChar.eq F 2]; norm_num
  have hd0 : d4Graph F 0 = 1 := by
    ext h
    simp [coe_d4Graph]
  have hT : ∀ {ε : ℕ}, (ε = 1 ∨ ε = 2) →
      MulAut.congr e₂ β = MulAut.conj g * (exactNormalAut Tag.D4 F a 1 0 * d4Graph F ε) →
      TwoEltInPerfect ↥(fixSubgroup β) := by
    intro ε hε' hαeq'
    obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
      D4Dual.exists_dual_fixEquiv (ℓ := 2) (f := 2) (by norm_num) F hF _ hα g a hε' hαeq'
    exact ((twoEltInPerfect_fixSubgroup_triality_outer_four hK₃ Fr hFr φ hφ3 hφout).of_mulEquiv
      e).of_mulEquiv (LieComp.fixSubgroupCongrEquiv e₂ β)
  interval_cases ε
  · exfalso
    rw [hd0, mul_one] at hαeq
    obtain ⟨h, hh⟩ := d4_inner_of_diag hchar g a (hαeq ▸ hα)
    obtain ⟨b, hb⟩ := Inputs256p.exists_conj_eq_of_conj_eq_mulAutCongr e₂ (hh.symm.trans hαeq.symm)
    exact hinn ⟨b, hb⟩
  · exact hT (Or.inl rfl) hαeq
  · exact hT (Or.inr rfl) hαeq

theorem twoElement_mem_glaLayer_d4_noninner_four {S : Type} [Group S] [Finite S]
    (hS : StatedClassicalModel S .POmegaPlus 4 2 2) (β : MulAut S) (hβ : orderOf β = 3)
    (hinn : β ∉ (MulAut.conj : S →* MulAut S).range) {s : S} (hs : β s = s) {m : ℕ}
    (hsm : s ^ 2 ^ m = 1) : s ∈ GLALayer (fixSubgroup β) := by
  have hβ3 : β ^ 3 = 1 := hβ ▸ pow_orderOf_eq_one β
  exact mem_glaLayer_of_twoEltInPerfect (perfectInLayer_omega_D4_three hS (by norm_num) β hβ3)
    (twoEltInPerfect_fixSubgroup_d4_noninner_four hS β hβ3 hinn) hs hsm

theorem twoElement_mem_glaLayer_triality_outer_four {S : Type} [Group S]
    {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq4 : q.card = 4)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) (β : MulAut S)
    (hβ : orderOf β = 3) (hinn : β ∉ (MulAut.conj : S →* MulAut S).range) {s : S} (hs : β s = s)
    {m : ℕ} (hsm : s ^ 2 ^ m = 1) : s ∈ GLALayer (fixSubgroup β) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp2, he2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 2)
    Nat.prime_two (by norm_num) (hq4.trans (by norm_num))
  obtain ⟨F, _, _, σ, hF, hσ, -, ⟨eF⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  rw [hp2, he2] at hF hσ
  set e' := eS.trans eF with he'
  have hβ3 : β ^ 3 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hφ3 : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hφ : MulAut.congr e' β ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 F σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 F σ.toRingHom)).range := by
    rintro ⟨y, hy⟩
    exact hinn (Inputs256p.exists_conj_eq_of_conj_eq_mulAutCongr e' hy)
  have hL : PerfectInLayer β := perfectInLayer_of_congr e' β
    (D4Dual.perfectInLayer_triality_outer_three (ℓ := 2) (f := 2) (by norm_num) (by norm_num) hF σ hσ
      _ hφ3 hφ)
  exact mem_glaLayer_of_twoEltInPerfect hL
    ((twoEltInPerfect_fixSubgroup_triality_outer_four hF σ hσ _ hφ3 hφ).of_mulEquiv
      (LieComp.fixSubgroupCongrEquiv e' β)) hs hsm

theorem twoEltLayerD4Outer_holds :
    ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex),
      (∃ q : TauCeti.PrimePower, d.1 = .D 4 q ∧ q.card = 4) →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ β : MulAut S, orderOf β = 3 → β ∉ (MulAut.conj : S →* MulAut S).range →
        ∀ s : S, β s = s → (∃ n : ℕ, s ^ (2 ^ n) = 1) → s ∈ GLALayer (fixSubgroup β) := by
  intro S _ _ d ⟨q, hq, hq4⟩ ⟨eS⟩ β hβ hinn s hs ⟨m, hm⟩
  obtain ⟨d, hv⟩ := d
  simp only at hq
  subst hq
  exact twoElement_mem_glaLayer_d4_noninner_four (statedClassicalModel_D_gf4 hv hq4 eS) β hβ hinn hs hm

end Triality

section Residual


theorem twoEltLayerOn_orthGF4 : TwoEltLayerOn IsOrthIdxGF4 := by
  intro S _ _ d hd he β hβ s hs hs2
  by_cases hD4 : ∃ q : TauCeti.PrimePower, d.1 = .D 4 q
  · obtain ⟨eS⟩ := he
    by_cases hinn : β ∈ (MulAut.conj : S →* MulAut S).range
    · exact twoEltLayer_orth_of_inner hd eS β hβ hinn s hs hs2
    · obtain ⟨q, hq⟩ := hD4
      have hq4 : q.card = 4 := by
        obtain ⟨r, q', hdq, hq4'⟩ := hd
        rcases hdq with h | h
        · rw [h] at hq
          injection hq with h1 h2
          rw [← h2]
          exact hq4'
        · rw [h] at hq
          cases hq
      exact twoEltLayerD4Outer_holds S d ⟨q, hq, hq4⟩ ⟨eS⟩ β hβ hinn s hs hs2
  · exact twoEltLayerOn_orthNoD4 S d ⟨hd, hD4⟩ he β hβ s hs hs2

theorem twoEltLayerOn_gf4Rest_of_rest (h : TwoEltLayerRest) : TwoEltLayerOn IsGF4RestIdx := by
  intro S _ _ d hd he β hβ s hs hs2
  by_cases ho : IsOrthIdxGF4 d
  · exact twoEltLayerOn_orthGF4 S d ho he β hβ s hs hs2
  · by_cases h3 : (∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q) ∧
        β ∉ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨⟨q, hq⟩, hinn⟩ := h3
      obtain ⟨eS⟩ := he
      obtain ⟨m, hm⟩ := hs2
      obtain ⟨d, hv⟩ := d
      simp only at hq
      subst hq
      have hq4 : q.card = 4 := hd.2.1
      exact twoElement_mem_glaLayer_triality_outer_four hv hq4 eS β hβ hinn hs hm
    · refine h S d ⟨hd, ho⟩ he β hβ (fun hq => ?_) s hs hs2
      by_contra hinn
      exact h3 ⟨hq, hinn⟩

theorem gf4CompsRest2_of_rest (h : TwoEltLayerRest) (hc : Inputs256p.ExcCompFieldIdx) :
    Inputs256p.GF4CompsRest2 :=
  ⟨twoEltLayerOn_gf4Rest_of_rest h, hc⟩

end Residual

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256q

end
