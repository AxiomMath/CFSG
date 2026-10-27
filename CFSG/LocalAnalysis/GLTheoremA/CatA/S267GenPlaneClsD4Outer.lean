module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenOuterBase
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.D4Outer
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenOuterTriD4
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenOuterUntw
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientForm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent

set_option linter.unusedSectionVars false


section GraphField

variable {K : Type} [Field K] [Finite K]

theorem compsNormal_fixSubgroup_twistedEntrywiseAut_D4 {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (he : 1 ≤ e) (hK : Nat.card K = ℓ ^ (e * 3)) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e))
    (j : ℤ) (hj : j % 3 = 1 ∨ j % 3 = 2) :
    CompsNormal ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hq3 : ∀ c : K, c ^ ((ℓ ^ e) ^ 3) = c := fun c => by
    rw [← pow_mul, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hT3 : T ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change T (T (T c)) = c
    rw [hT, hT, hT, ← pow_mul, ← pow_mul, show ℓ ^ e * (ℓ ^ e * ℓ ^ e) = (ℓ ^ e) ^ 3 by ring, hq3]
  have hinv : ∀ c, T⁻¹ c = c ^ ((ℓ ^ e) ^ 2) := by
    have h1 : T⁻¹ = T ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)
    intro c
    rw [h1, pow_two]
    change T (T c) = _
    rw [hT, hT, ← pow_mul, sq]
  have hper : twistedEntrywiseAut TwistTag.D4 j T = twistedEntrywiseAut TwistTag.D4 (j % 3) T := by
    have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (j % 3) (j / 3) T
    rw [show j % 3 + j / 3 * ((TwistTag.D4.order : ℕ) : ℤ) = j by
      change j % 3 + j / 3 * 3 = j
      omega] at h
    exact h
  rw [hper]
  rcases hj with h | h
  · rw [h]
    obtain ⟨hs, -, ⟨eF⟩⟩ := LieComp.exists_fixSubgroup_twistedOne_equiv he hK T 1 (Or.inl rfl)
      (fun c => by rw [hT, pow_one])
    haveI := hs
    exact (compsNormal_of_isSimpleGroup).of_mulEquiv eF
  · rw [h]
    obtain ⟨hs, -, ⟨eF⟩⟩ := LieComp.exists_fixSubgroup_twistedOne_equiv he hK T⁻¹ 2
      (Or.inr rfl) hinv
    haveI := hs
    exact ((compsNormal_of_isSimpleGroup).of_mulEquiv eF).of_mulEquiv
      (MulEquiv.subgroupCongr (fixedSubgroup_twistedEntrywiseAut_D4_two T))

theorem compsNormal_of_lang_D4 {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ (e * 3)) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e))
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K)
    (hσT : σ = T ∨ σ = T⁻¹) (ε : ℕ)
    (hP : ∀ j : ℤ, (j = (ε : ℤ) ∨ j = -(ε : ℤ)) →
      CompsNormal ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)))
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) ^ 3 = 1) :
    CompsNormal
      ↥(fixSubgroup (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))) := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left (Fact.out : ℓ.Prime).two_le 2
      _ ≤ ℓ ^ (e * 3) := Nat.pow_le_pow_right (Fact.out : ℓ.Prime).pos (by omega)
  set α := MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) with hαdef
  rcases hσT with hσT | hσT
  · subst hσT
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he rfl σ hT α hα
      g a ε hαdef
    refine compsNormal_fixSubgroup_of_conj ψ α ?_
    rw [hψ]
    exact hP _ (Or.inl rfl)
  · subst hσT
    obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he rfl T T⁻¹
      hT (mul_inv_cancel T) α hα g a ε hαdef
    refine compsNormal_fixSubgroup_of_eq
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq α)
      (compsNormal_fixSubgroup_of_conj ψ α⁻¹ ?_)
    rw [hψ]
    exact hP _ (Or.inr rfl)

end GraphField

section Outer

theorem compsNormal_d4_graph_type {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    {F : Type} [Field F] [Finite F] [CharP F ℓ] (hF : Nat.card F = ℓ ^ f)
    (g : adjointGroup Tag.D4 F) (a : Fin Tag.D4.rank → Fˣ) (σ : F ≃+* F) (hσ3 : σ ^ 3 = 1)
    {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 F a σ 0 * d4Graph F ε)) ^ 3 = 1) :
    CompsNormal
      ↥(fixSubgroup (MulAut.conj g * (exactNormalAut Tag.D4 F a σ 0 * d4Graph F ε))) := by
  classical
  by_cases hσ1 : σ = 1
  · subst hσ1
    obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
      D4Dual.exists_dual_fixEquiv hf F hF _ hα g a hε rfl
    have hq3 : ¬ 3 ∣ ℓ ^ f := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : ℓ.Prime)).1
        (Nat.prime_three.dvd_of_dvd_pow h)
      omega
    rcases (show (ℓ ^ f) % 3 = 1 ∨ (ℓ ^ f) % 3 = 2 by omega) with h1 | h1
    · exact (compsNormal_outer_three_odd_one hℓ5 hf h1 hK₃ Fr hFr φ hφ3 hφout).of_mulEquiv e
    · exact (compsNormal_outer_three_odd_two hℓ5 hf h1 hK₃ Fr hFr φ hφ3 hφout).of_mulEquiv e
  · obtain ⟨ℓ', e, T, -, hchar', he, hK, hT, hσT⟩ := LieComp.exists_frobenius_data_D4 σ hσ1 hσ3
    obtain rfl : ℓ' = ℓ := CharP.eq F hchar' ‹CharP F ℓ›
    refine compsNormal_of_lang_D4 he hK T hT g a σ hσT ε (fun j hj => ?_) hα
    refine compsNormal_fixSubgroup_twistedEntrywiseAut_D4 he hK T hT j ?_
    rcases hε with rfl | rfl <;> rcases hj with rfl | rfl <;> omega

theorem compsNormal_d4_outer {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = ℓ ^ f) (α : MulAut ↥(adjointGroup Tag.D4 F))
    (hα : α ^ 3 = 1) (hout : ∀ h : adjointGroup Tag.D4 F, MulAut.conj h ≠ α) :
    CompsNormal ↥(fixSubgroup α) := by
  classical
  have hchF : CharP F ℓ := by
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  have hchar : ringChar F ≠ 3 := by
    rw [ringChar.eq F ℓ]
    omega
  have hG0 : d4Graph F 0 = 1 := MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_d4Graph, pow_zero, one_mul, inv_one, mul_one]; rfl)
  obtain ⟨g, a, σ, ε, hε, hσ3, hαeq⟩ := exists_cube_normal_form_sigma α hα
  interval_cases ε
  · have hα' : α = MulAut.conj g * exactNormalAut Tag.D4 F a σ 0 := by
      rw [hαeq, hG0, mul_one]
    by_cases hσ1 : σ = 1
    ·
      exfalso
      subst hσ1
      rw [hα'] at hα
      obtain ⟨h, hh⟩ := d4_inner_of_diag hchar g a hα
      exact hout h (by rw [hα', hh])
    ·
      rw [hα'] at hα ⊢
      obtain ⟨ψ, hψ⟩ := LieComp.ExcCopy.exists_conj_eq_entrywiseAdjointAut .D4 Nat.prime_three g
        a σ hσ1 hσ3 hα
      refine compsNormal_fixSubgroup_of_conj ψ _ ?_
      rw [hψ]
      exact compsNormal_entrywiseAdjointAut .D4 σ fun h => absurd h (by decide)
  · rw [hαeq]
    exact compsNormal_d4_graph_type hℓ5 hf hF g a σ hσ3 (Or.inl rfl) (hαeq ▸ hα)
  · rw [hαeq]
    exact compsNormal_d4_graph_type hℓ5 hf hF g a σ hσ3 (Or.inr rfl) (hαeq ▸ hα)

end Outer

theorem d4OuterCompNormal_holds : D4OuterCompNormal := by
  classical
  intro T _ _ d hT hq β hβ hout
  obtain ⟨q, hq⟩ := hq
  obtain ⟨d, hv⟩ := d
  change d = TauCeti.LieTypeIndex.D 4 q at hq
  subst hq
  obtain ⟨e⟩ := hT.iso
  let F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩)
  haveI : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hFcard : Nat.card F = q.p ^ q.exponent := by
    change Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) = q.p ^ q.exponent
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
      TauCeti.LieTypeIndex.characteristic_D, TauCeti.LieTypeIndex.fieldExponent_D]
  have hc : (TauCeti.LieTypeIndex.D 4 q).characteristic = q.p :=
    TauCeti.LieTypeIndex.characteristic_D 4 q
  have h2 : q.p ≠ 2 := fun h => hT.charOdd (hc.trans h)
  have h3 : q.p ≠ 3 := fun h => hT.ne (h.symm.trans hc.symm)
  have hℓ5 : 5 ≤ q.p := by
    have h2le := q.prime_p.two_le
    have h4 : q.p ≠ 4 := fun h => by
      have hp := q.prime_p
      rw [h] at hp
      exact absurd hp (by norm_num)
    omega
  let e' : T ≃* ↥(adjointGroup Tag.D4 F) :=
    e.trans ((CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q
      hv).trans
      (CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup
        F).some)
  refine compNormal_of_compsNormal (compsNormal_fixSubgroup_of_congr e' ?_)
  have hβ' : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hout' : ∀ h : adjointGroup Tag.D4 F, MulAut.conj h ≠ MulAut.congr e' β := fun h hh => by
    apply hout (e'.symm h)
    have hc' : MulAut.congr e'.symm (MulAut.conj h) = MulAut.conj (e'.symm h) := by
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]
    rw [← hc', hh]
    ext y
    simp [MulAut.congr_apply]
  exact compsNormal_d4_outer hℓ5 q.exponent_pos hFcard _ hβ' hout'

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
