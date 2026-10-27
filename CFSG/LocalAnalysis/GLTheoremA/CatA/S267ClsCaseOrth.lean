module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseOrthTools
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsOrthInv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsInnerProd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsFieldExp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsOrthTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt
  CFSG.Yardstones.Md0ec50421ce4 QuadraticMap
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Module
open scoped IsMulCommutative

private theorem char_facts {K : Type} [Field K] [Fintype K] {p q : ℕ} (hp : p.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) {Q₀ : TauCeti.PrimePower} (hQ₀ : Q₀.p = q)
    (hK : Nat.card K = Q₀.card) : (2 : K) ≠ 0 ∧ (p : K) ≠ 0 ∧ Odd (Nat.card K) := by
  have hq : q.Prime := hQ₀ ▸ Q₀.prime_p
  have hcK : Nat.card K = q ^ Q₀.exponent := by rw [hK, TauCeti.PrimePower.card_def, hQ₀]
  haveI := ringChar.charP K
  obtain ⟨n, hr, hcard⟩ := FiniteField.card K (ringChar K)
  have hrq : ringChar K = q := by
    have h1 : ringChar K ∣ q ^ Q₀.exponent := by
      rw [← hcK, Nat.card_eq_fintype_card, hcard]
      exact dvd_pow_self _ n.ne_zero
    exact (Nat.prime_dvd_prime_iff_eq hr hq).1 (hr.dvd_of_dvd_pow h1)
  have hcast : ∀ k : ℕ, (k : K) = 0 ↔ q ∣ k := fun k => by
    rw [← hrq]
    exact ringChar.spec K k
  refine ⟨fun h => ?_, fun h => ?_, ?_⟩
  · have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 ((hcast 2).1 h'))
  · exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 ((hcast p).1 h))
  · rw [hcK]
    exact (hq.odd_of_ne_two hq2).pow

private theorem center_pQuot_eq_bot {Ω : Type} [Group Ω] {S : Subgroup Ω} {p : ℕ}
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥) :
    Subgroup.center (PQuot p S) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  have hs : s ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := Subgroup.mem_center_iff.1 hx (g : PQuot p S)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hcore,
      Subgroup.mem_bot] at h
    exact (inv_mul_eq_one.1 h)
  rw [hZ, Subgroup.mem_bot] at hs
  rw [hs]
  exact Subgroup.one_mem _

private theorem dvd_card_sq_sub_one {K : Type} {p : ℕ} {Q₀ : TauCeti.PrimePower}
    (hK : Nat.card K = Q₀.card)
    (h : (p : ℤ) ∣ (Nat.card K : ℤ) - 1 ∨ (p : ℤ) ∣ (Nat.card K : ℤ) + 1) :
    p ∣ Q₀.card ^ 2 - 1 := by
  have hc : 0 < Q₀.card := by
    rw [TauCeti.PrimePower.card_def]
    exact pow_pos Q₀.prime_p.pos _
  have h1 : 1 ≤ Q₀.card ^ 2 := Nat.one_le_pow _ _ hc
  have hz : ((Q₀.card ^ 2 - 1 : ℕ) : ℤ) = ((Q₀.card : ℤ) - 1) * ((Q₀.card : ℤ) + 1) := by
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have hd : (p : ℤ) ∣ ((Q₀.card ^ 2 - 1 : ℕ) : ℤ) := by
    rw [hz, ← hK]
    rcases h with h | h
    · exact Dvd.dvd.mul_right h _
    · exact Dvd.dvd.mul_left h _
  exact_mod_cast hd

private theorem invol_facts {K : Type} [Field K] [Finite K] {m p : ℕ} {Ω : Type} [Group Ω]
    {S B : Subgroup Ω} (hp : p.Prime) (h2 : (2 : K) ≠ 0) (hpK : (p : K) ≠ 0)
    {Q : QuadraticForm K (Fin m → K)} (Dat : ClsInner p S B (matrixDerived Q) (polarBilin Q))
    {Aε : Subgroup (GL (Fin m) K)} [IsMulCommutative Aε] (hA : ∀ a : ↥Aε, a ^ p = 1)
    (hAεL : Aε = liftGroup Dat) (hAε𝒮 : Aε ≤ centGL (fieldSet Dat))
    {I : Finset (Hyperplane ↥Aε p)} {Ha Hc : Hyperplane ↥Aε p} (ha : Ha ∈ I) (hc : Hc ∉ I)
    (hWa : weightSpace (glRep Aε) Ha.1 ≠ ⊥) (hWc : weightSpace (glRep Aε) Hc.1 ≠ ⊥)
    (hzH : glEquiv.symm (invol (glRep Aε) hp hA hpK I) ∈ matrixDerived Q) :
    glEquiv.symm (invol (glRep Aε) hp hA hpK I) ^ 2 = 1 ∧ Dat.φ ⟨_, hzH⟩ ≠ 1 ∧
      glEquiv.symm (invol (glRep Aε) hp hA hpK I) ∈ centGL (fieldSet Dat) ∧
      ∀ y ∈ liftGroup Dat, glEquiv.symm (invol (glRep Aε) hp hA hpK I) * y =
        y * glEquiv.symm (invol (glRep Aε) hp hA hpK I) := by
  set ρ := glRep Aε with hρdef
  have hgz : glEquiv (glEquiv.symm (invol ρ hp hA hpK I)) = invol ρ hp hA hpK I :=
    MulEquiv.apply_symm_apply _ _
  have h𝒮 : ∀ s ∈ fieldSet Dat, ∀ a v, s (ρ a v) = ρ a (s v) := by
    intro s hs a v
    rw [glRep_apply_eq_glEquiv, glRep_apply_eq_glEquiv]
    exact ((mem_centGL.mp (hAε𝒮 a.2)) s hs v).symm
  have h𝒮W : ∀ s ∈ fieldSet Dat, ∀ i, ∀ v ∈ weightFamily (p := p) ρ i,
      s v ∈ weightFamily (p := p) ρ i := by
    rintro s ⟨hF, rfl⟩ i v hv
    exact preserves_weightFamily_of_semilinear ρ (Dat.σ : K →+* K) _
      (fun c v => ModelGen.semiMap_smul Dat.A Dat.σ c v) (h𝒮 _ ⟨hF, rfl⟩) i hv
  have hρW : ∀ (a : ↥Aε) i, ∀ v ∈ weightFamily (p := p) ρ i,
      (ρ a).toAddMonoidHom v ∈ weightFamily (p := p) ρ i := fun a i v hv =>
    preserves_weightFamily_of_semilinear ρ (RingHom.id K) (ρ a).toAddMonoidHom
      (fun c v => map_smul (ρ a) c v)
      (fun a' v => by
        show ρ a (ρ a' v) = ρ a' (ρ a v)
        rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]) i hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pow_two]
    apply glEquiv.injective
    rw [map_mul, hgz, map_one]
    exact LinearEquiv.ext fun v => invol_invol ρ hp hA hpK I v
  · intro h
    have hk : (⟨_, hzH⟩ : ↥(matrixDerived Q)) ∈ Dat.φ.ker := h
    rw [Dat.ker_eq, Subgroup.mem_subgroupOf] at hk
    obtain ⟨c, hc'⟩ := hk
    have hc'' : Matrix.GeneralLinearGroup.scalar (Fin m) c =
        glEquiv.symm (invol ρ hp hA hpK I) := hc'
    refine invol_ne_smul ρ hp hA hpK h2 ha hc hWa hWc (c : K) fun v => ?_
    rw [← hgz, ← hc'', glEquiv_apply]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_mulVec, Matrix.one_mulVec]
  · rw [mem_centGL]
    intro s hs v
    rw [hgz]
    exact invol_comm ρ hp hA hpK I s (h𝒮W s hs) v
  · intro y hy
    rw [← hAεL] at hy
    apply glEquiv.injective
    refine LinearEquiv.ext fun v => ?_
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgz]
    have := invol_comm ρ hp hA hpK I (ρ ⟨y, hy⟩).toAddMonoidHom (hρW ⟨y, hy⟩) v
    simp only [LinearMap.toAddMonoidHom_coe, hρdef, glRep_apply_eq_glEquiv] at this
    exact this

theorem concl_of_clsInner_orth
    {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hqp : q ≠ p) {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} [hSn : S.Normal]
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥)
    {d : TauCeti.ValidLieTypeIndex}
    (eS : Nonempty (PSimple p S ≃* (TauCeti.CFSGIndex.lie d).Group)) (hB : IsElemAbelian p B)
    (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B) (h4 : p ^ 4 ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B)
    {K : Type} [Field K] [Fintype K] [DecidableEq K] {m : ℕ} (Q : QuadraticForm K (Fin m → K))
    (hQ : (polarBilin Q).Nondegenerate) {Q₀ : TauCeti.PrimePower} (hQ₀ : Q₀.p = q)
    (hK : Nat.card K = Q₀.card)
    (hab : ∃ k : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ k)
    (hd : (∃ n, 3 ≤ n ∧ d.1 = .B n Q₀ ∧ m = 2 * n + 1) ∨
      (∃ n, 4 ≤ n ∧ d.1 = .D n Q₀ ∧ m = 2 * n ∧ CFSG.GroupTheory.WeirSylow.IsPlusType Q) ∨
      (∃ n, 4 ≤ n ∧ d.1 = .twistedD n Q₀ ∧ m = 2 * n ∧
        ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q))
    (Dat : ClsInner p S B (matrixDerived Q) (polarBilin Q)) :
    S267ConcA p S B ∨ S267ConcBCDE p q S B := by
  classical
  obtain ⟨h2, hpK, hodd⟩ := char_facts hp hq2 hqp hQ₀ hK
  have hHβ : matrixDerived Q ≤ isomGL (polarBilin Q) := ModelGen.matrixDerived_le_isomGL Q
  obtain ⟨Aε, hle, hAε, hAεβ, hAε𝒮, hmax⟩ := exists_maximal_engine Dat hHβ
  haveI : IsMulCommutative Aε := hAε.1
  have hA : ∀ a : ↥Aε, a ^ p = 1 := fun a => Subtype.ext (hAε.2 a a.2)
  haveI : Fintype (Hyperplane ↥Aε p) := Fintype.ofFinite _
  have hinf : Aε ⊓ matrixDerived Q = liftGroup Dat :=
    inf_eq_liftGroup hp hB hrank hBC hcore hZ h4 h2 hpK Dat hHβ hle hAε hAεβ hAε𝒮 hmax hA
      (fun H₁ H₂ H₃ h12 h13 h23 _ _ _ =>
        invol_mem_matrixDerived_of_three h2 hp hp2 hpK Q hQ hAεβ hA H₁ H₂ H₃ h12 h13 h23)
  have hAH : Aε ≤ matrixDerived Q := fun g hg =>
    ModelGen.mem_matrixDerived_of_pow_eq_one_of_odd Q hab
      (ModelGen.mem_matrixIsometries_of_mem_isomGL Q h2 (hAεβ hg)) (hp.odd_of_ne_two hp2)
      (hAε.2 g hg)
  have hAεL : Aε = liftGroup Dat := by rw [← hinf, inf_eq_left.2 hAH]
  set ρ := glRep Aε with hρdef
  have hρ : IsIsomRep (polarBilin Q) ρ := isIsomRep_glRep hAεβ
  have hρQ : ∀ (a : ↥Aε) (v : Fin m → K), Q (ρ a v) = Q v := quad_glRep_apply_of_le Q h2 hAεβ
  have hmaxE : IsMaxElem (polarBilin Q) ρ p (fieldSet Dat) :=
    isMaxElem_of_maximal (polarBilin Q) (fieldSet Dat) Aε hAε hAεβ hAε𝒮 hmax
  have h𝒮 : ∀ s ∈ fieldSet Dat, ∀ a v, s (ρ a v) = ρ a (s v) := by
    intro s hs a v
    rw [glRep_apply_eq_glEquiv, glRep_apply_eq_glEquiv]
    exact ((mem_centGL.mp (hAε𝒮 a.2)) s hs v).symm
  have h𝒮W : ∀ s ∈ fieldSet Dat, ∀ i, ∀ v ∈ weightFamily (p := p) ρ i,
      s v ∈ weightFamily (p := p) ρ i := by
    rintro s ⟨hF, rfl⟩ i v hv
    exact preserves_weightFamily_of_semilinear ρ (Dat.σ : K →+* K) _
      (fun c v => ModelGen.semiMap_smul Dat.A Dat.σ c v) (h𝒮 _ ⟨hF, rfl⟩) i hv
  set T : Finset (Hyperplane ↥Aε p) := Finset.univ.filter fun H' => weightSpace ρ H'.1 ≠ ⊥
    with hTdef
  have hT : ∀ H' : Hyperplane ↥Aε p, H' ∈ T ↔ weightSpace ρ H'.1 ≠ ⊥ := fun H' => by
    simp [hTdef]
  have hcardA : Nat.card ↥Aε = p ^ T.card :=
    card_eq_pow_support (polarBilin Q) ρ hp hA hpK hρ hmaxE h𝒮 h𝒮W (glRep_injective Aε) T hT
  have hθ : Nat.card Dat.θ.range = p ^ T.card := by
    rw [← hcardA, hAεL]
    exact (Subgroup.card_map_of_injective (matrixDerived Q).subtype_injective).symm
  have hBC' : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = p := by
    rw [← ModelGen.inf_centMod_eq_inf_centralizer hSn hcore]
    exact hBC
  have hθcard := ModelGen.card_range_mul_card_inf Dat.θ Dat.θ_eq_one
  have hinfC : innerPart S B ⊓ Subgroup.centralizer (S : Set Ω) =
      B ⊓ Subgroup.centralizer (S : Set Ω) := by
    rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Subgroup.centralizer (S : Set Ω) ≤
      S ⊔ Subgroup.centralizer (S : Set Ω))]
  have hB₁ : Nat.card ↥(innerPart S B) = p ^ (T.card + 1) := by
    rw [← hθcard, hinfC, hBC', hθ, pow_succ]
  have hsplit : (innerPart S B = B ∧ fieldSet Dat = ∅ ∧ Nat.card B = p ^ (T.card + 1)) ∨
      (FieldElt p S B Dat.φ (polarBilin Q) Dat.θ Dat.b Dat.A Dat.σ ∧
        Nat.card B = p ^ (T.card + 2)) := by
    rcases Dat.split with hBB | hF
    · refine Or.inl ⟨hBB, ?_, by rw [← hBB, hB₁]⟩
      ext s
      simp only [fieldSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hF
      have hb : Dat.b ∈ innerPart S B := by rw [hBB]; exact hF.1
      exact absurd hb.2 hF.2.1
    · refine Or.inr ⟨hF, ?_⟩
      obtain ⟨hbB, hbN, hBb, hbout, -, -, -⟩ := hF
      have hord : orderOf Dat.b = p := by
        haveI : Fact p.Prime := ⟨hp⟩
        exact orderOf_eq_prime (hB.2 _ hbB) (fun h => hbN (h ▸ Subgroup.one_mem _))
      have hcardB := card_eq_of_inner_split hB hBC' hbB hBb hbout hθcard
      rw [Nat.card_zpowers, hord, hθ] at hcardB
      rw [hcardB]
      ring
  have hdimF : m = finrank K ↥(fixedSpace ρ ⊤) + ∑ H ∈ T, finrank K ↥(weightSpace ρ H.1) := by
    have h : finrank K (Fin m → K) = finrank K ↥(fixedSpace ρ ⊤) +
        ∑ H : Hyperplane ↥Aε p, finrank K ↥(weightSpace ρ H.1) :=
      finrank_eq_fixedSpace_add_sum ρ hp hA hpK
    rw [Module.finrank_fin_fun] at h
    rw [Finset.sum_subset (Finset.subset_univ T) (fun H _ hH => by
      have hbot : weightSpace ρ H.1 = ⊥ := by
        by_contra hne
        exact hH ((hT H).2 hne)
      rw [hbot, finrank_bot])]
    exact h
  have hge2 : ∀ H ∈ T, 2 ≤ finrank K ↥(weightSpace ρ H.1) := fun H hH =>
    two_le_finrank_weightSpace ρ hp hA hpK Q hQ h2 hρQ hp2 H ((hT H).1 hH)
  have hev : ∀ H : Hyperplane ↥Aε p, Even (finrank K ↥(weightSpace ρ H.1)) := fun H =>
    even_finrank_weightSpace ρ hp hA hpK Q hQ h2 hρQ hp2 H
  have hsubsum : ∀ s ⊆ T, ∑ H ∈ s, finrank K ↥(weightSpace ρ H.1) ≤ m := by
    intro s hs
    have h : ∑ H ∈ s, finrank K ↥(weightSpace ρ H.1) ≤
        finrank K ↥(fixedSpace ρ ⊤) + ∑ H ∈ T, finrank K ↥(weightSpace ρ H.1) :=
      le_add_left (Finset.sum_le_sum_of_subset hs)
    omega
  have hconcA : ∀ Ha Hb Hc : Hyperplane ↥Aε p, Ha ∈ T → Hb ∈ T → Hc ∈ T → Ha ≠ Hb →
      Ha ≠ Hc → Hb ≠ Hc → glEquiv.symm (invol ρ hp hA hpK {Ha, Hb}) ∈ matrixDerived Q →
      finrank K ↥(weightSpace ρ Ha.1) + finrank K ↥(weightSpace ρ Hb.1) + 5 ≤ m →
      p ^ 3 ≤ Nat.card ↥Aε → p ^ 5 ≤ Nat.card B → S267ConcA p S B := by
    intro Ha Hb Hc ha hb hc hab hac hbc hzH hdim h3 h5
    have hUW := isCompl_ker_range_projI ρ hp hA hpK ({Ha, Hb} : Finset (Hyperplane ↥Aε p))
    have hfr := Submodule.finrank_add_eq_of_isCompl hUW
    have hW := finrank_range_projI ρ hp hA hpK ({Ha, Hb} : Finset (Hyperplane ↥Aε p))
    rw [Finset.sum_pair hab] at hW
    rw [Module.finrank_fin_fun] at hfr
    exact concA_of_pair_orth hp hp2 hB hBC hcore hodd h2 hpK Q hQ Dat hA hAεL hAεβ hAε𝒮 hmaxE
      hab hac hbc ((hT Ha).1 ha) ((hT Hb).1 hb) ((hT Hc).1 hc) h3 h5 hzH
      (show 5 ≤ finrank K ↥(LinearMap.ker (projI ρ ({Ha, Hb} : Finset (Hyperplane ↥Aε p))))
        by omega)
  have hthree : ∀ H₁ H₂ H₃ : Hyperplane ↥Aε p, H₁ ∈ T → H₂ ∈ T → H₃ ∈ T → H₁ ≠ H₂ →
      H₁ ≠ H₃ → H₂ ≠ H₃ → (∀ Ha Hb : Hyperplane ↥Aε p, (Ha = H₁ ∨ Ha = H₂ ∨ Ha = H₃) →
        (Hb = H₁ ∨ Hb = H₂ ∨ Hb = H₃) → Ha ≠ Hb →
        finrank K ↥(weightSpace ρ Ha.1) + finrank K ↥(weightSpace ρ Hb.1) + 5 ≤ m) →
      p ^ 3 ≤ Nat.card ↥Aε → p ^ 5 ≤ Nat.card B → S267ConcA p S B := by
    intro H₁ H₂ H₃ h1 h2' h3 h12 h13 h23 hdim hA3 h5
    rcases invol_mem_matrixDerived_of_three h2 hp hp2 hpK Q hQ hAεβ hA H₁ H₂ H₃ h12 h13 h23 with
      h | h | h
    · exact hconcA H₁ H₂ H₃ h1 h2' h3 h12 h13 h23 h
        (hdim _ _ (Or.inl rfl) (Or.inr (Or.inl rfl)) h12) hA3 h5
    · exact hconcA H₁ H₃ H₂ h1 h3 h2' h13 h12 h23.symm h
        (hdim _ _ (Or.inl rfl) (Or.inr (Or.inr rfl)) h13) hA3 h5
    · exact hconcA H₂ H₃ H₁ h2' h3 h1 h23 h12.symm h13.symm h
        (hdim _ _ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) h23) hA3 h5
  have hinvol : ∀ H₁ H₂ H₃ : Hyperplane ↥Aε p, H₁ ∈ T → H₂ ∈ T → H₃ ∈ T → H₁ ≠ H₂ →
      H₁ ≠ H₃ → H₂ ≠ H₃ → innerPart S B = (B ⊓ centModSubgroup p S) ⊔ (B ⊓ S) ∧
        (B ⊓ centModSubgroup p S) ⊓ (B ⊓ S) = ⊥ ∧
        Nat.card ↥(B ⊓ S) = Nat.card Dat.θ.range := by
    intro H₁ H₂ H₃ h1 h2' h3 h12 h13 h23
    have key : ∀ Ha Hb Hc : Hyperplane ↥Aε p, Ha ∈ T → Hc ∈ T → Ha ≠ Hc → Hb ≠ Hc →
        glEquiv.symm (invol ρ hp hA hpK {Ha, Hb}) ∈ matrixDerived Q →
        innerPart S B = (B ⊓ centModSubgroup p S) ⊔ (B ⊓ S) ∧
          (B ⊓ centModSubgroup p S) ⊓ (B ⊓ S) = ⊥ ∧
          Nat.card ↥(B ⊓ S) = Nat.card Dat.θ.range := by
      intro Ha Hb Hc ha hc hac hbc hzH
      have hcI : Hc ∉ ({Ha, Hb} : Finset (Hyperplane ↥Aε p)) := by
        simp [Ne.symm hac, Ne.symm hbc]
      obtain ⟨hz2, hz1, hzF, hzA⟩ := invol_facts hp h2 hpK Dat hA hAεL hAε𝒮
        (Finset.mem_insert_self Ha {Hb}) hcI ((hT Ha).1 ha) ((hT Hc).1 hc) hzH
      exact innerPart_eq_sup_of_involution hp hcore hZ hB hrank Dat hzH hz2 hz1 hzF hzA
    rcases invol_mem_matrixDerived_of_three h2 hp hp2 hpK Q hQ hAεβ hA H₁ H₂ H₃ h12 h13 h23 with
      h | h | h
    · exact key H₁ H₂ H₃ h1 h3 h13 h23 h
    · exact key H₁ H₃ H₂ h1 h2' h12 h23.symm h
    · exact key H₂ H₃ H₁ h2' h1 h12.symm h13.symm h
  have hdvdQ : ∀ H ∈ T, finrank K ↥(weightSpace ρ H.1) = 2 →
      (p : ℤ) ∣ (Nat.card K : ℤ) - 1 ∨ (p : ℤ) ∣ (Nat.card K : ℤ) + 1 := by
    intro H hH h2d
    have h := CFSG.LocalAnalysis.GLTheoremA.H81Orth.int_dvd_of_weightPlane ρ hp hA hpK Q hQ hρQ
      hp2 ((hT H).1 hH) h2d
    by_cases hx : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (weightSpace ρ H.1).subtype)
    · exact Or.inl (h.1 hx)
    · exact Or.inr (h.2 hx)
  by_cases ht4 : 4 ≤ T.card
  ·
    have hA3 : p ^ 3 ≤ Nat.card ↥Aε := by
      rw [hcardA]
      exact Nat.pow_le_pow_right hp.pos (by omega)
    have h5 : p ^ 5 ≤ Nat.card B := by
      have h' : p ^ 5 ≤ p ^ (T.card + 1) := Nat.pow_le_pow_right hp.pos (by omega)
      rcases hsplit with ⟨-, -, hc⟩ | ⟨-, hc⟩
      · rw [hc]; exact h'
      · rw [hc]; exact h'.trans (Nat.pow_le_pow_right hp.pos (by omega))
    by_cases hbig : ∃ Hg ∈ T, 4 ≤ finrank K ↥(weightSpace ρ Hg.1)
    ·
      left
      obtain ⟨Hg, hg, hg4⟩ := hbig
      have hc3 : 2 < (T.erase Hg).card := by
        rw [Finset.card_erase_of_mem hg]
        omega
      obtain ⟨H₁, h1, H₂, h2', H₃, h3, h12, h13, h23⟩ := Finset.two_lt_card.1 hc3
      rw [Finset.mem_erase] at h1 h2' h3
      refine hthree H₁ H₂ H₃ h1.2 h2'.2 h3.2 h12 h13 h23 (fun Ha Hb ha hb hab => ?_) hA3 h5
      have hmemT : ∀ H, (H = H₁ ∨ H = H₂ ∨ H = H₃) → H ∈ T ∧ H ≠ Hg := by
        rintro H (rfl | rfl | rfl)
        · exact ⟨h1.2, h1.1⟩
        · exact ⟨h2'.2, h2'.1⟩
        · exact ⟨h3.2, h3.1⟩
      obtain ⟨haT, hag⟩ := hmemT Ha ha
      obtain ⟨hbT, hbg⟩ := hmemT Hb hb
      have hHbm : Hb ∈ T.erase Ha := Finset.mem_erase.2 ⟨hab.symm, hbT⟩
      have hHgm : Hg ∈ (T.erase Ha).erase Hb :=
        Finset.mem_erase.2 ⟨hbg.symm, Finset.mem_erase.2 ⟨hag.symm, hg⟩⟩
      have hc4 : 0 < (((T.erase Ha).erase Hb).erase Hg).card := by
        rw [Finset.card_erase_of_mem hHgm, Finset.card_erase_of_mem hHbm,
          Finset.card_erase_of_mem haT]
        omega
      obtain ⟨Hd, hd'⟩ := Finset.card_pos.1 hc4
      simp only [Finset.mem_erase] at hd'
      obtain ⟨hdg, hdb, hda, hdT⟩ := hd'
      have hs : ({Ha, Hb, Hg, Hd} : Finset (Hyperplane ↥Aε p)) ⊆ T := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> assumption
      have hsum := hsubsum _ hs
      rw [Finset.sum_insert (by simp [hab, hag, Ne.symm hda]),
        Finset.sum_insert (by simp [hbg, Ne.symm hdb]), Finset.sum_pair (Ne.symm hdg)] at hsum
      have := hge2 Hd hdT
      omega
    · push Not at hbig
      have hpl : ∀ H ∈ T, finrank K ↥(weightSpace ρ H.1) = 2 := by
        intro H hH
        have h1 := hbig H hH
        have h1' := hge2 H hH
        obtain ⟨k, hk⟩ := hev H
        omega
      have hsumT : ∑ H ∈ T, finrank K ↥(weightSpace ρ H.1) = 2 * T.card := by
        rw [Finset.sum_congr rfl hpl, Finset.sum_const, smul_eq_mul, mul_comm]
      obtain ⟨H₁, h1, H₂, h2', H₃, h3, h12, h13, h23⟩ :=
        Finset.two_lt_card.1 (by omega : 2 < T.card)
      by_cases h9 : 9 ≤ m
      ·
        left
        refine hthree H₁ H₂ H₃ h1 h2' h3 h12 h13 h23 (fun Ha Hb ha hb _ => ?_) hA3 h5
        have hmemT : ∀ H, (H = H₁ ∨ H = H₂ ∨ H = H₃) → H ∈ T := by
          rintro H (rfl | rfl | rfl) <;> assumption
        rw [hpl Ha (hmemT Ha ha), hpl Hb (hmemT Hb hb)]
        omega
      ·
        have hdimF' := hdimF
        rw [hsumT] at hdimF'
        have hm8 : m = 8 := by omega
        have ht : T.card = 4 := by omega
        have hplus := CFSG.LocalAnalysis.GLTheoremA.H81Orth.isPlusType_of_four_planes ρ hp hA hpK
          Q hQ hρQ hp2 (by rw [Module.finrank_fin_fun]; exact hm8) hT ht hpl
        rcases hd with ⟨n, hn, -, hmn⟩ | ⟨n, hn, hdD, hmn, -⟩ | ⟨n, hn, -, hmn, hnp⟩
        · omega
        · right
          have hn4 : n = 4 := by omega
          subst hn4
          have hIP := hinvol H₁ H₂ H₃ h1 h2' h3 h12 h13 h23
          unfold S267ConcBCDE
          refine Or.inr (Or.inr (Or.inr ⟨?_, by rw [hIP.2.2, hθ, ht], center_pQuot_eq_bot hcore hZ,
            Q₀, hQ₀, ⟨TauCeti.CFSGIndex.lie d, hdD, eS⟩,
            dvd_card_sq_sub_one hK (hdvdQ H₁ h1 (hpl H₁ h1))⟩))
          rcases hsplit with ⟨-, -, hc⟩ | ⟨-, hc⟩
          · left; rw [hc, ht]
          · right; rw [hc, ht]
        · exact absurd hplus hnp
  ·
    push Not at ht4
    have hB5 : CFSG.Open.pRank p B ≤ 5 := by
      apply CFSG.SectionRank.pRank_le hp.one_lt
      intro E hEB _
      refine (Subgroup.card_le_of_le hEB).trans ?_
      rcases hsplit with ⟨-, -, hc⟩ | ⟨-, hc⟩ <;> rw [hc] <;>
        exact Nat.pow_le_pow_right hp.pos (by omega)
    have hnot : ¬ HqRank.HqSixIdx q d.1 := fun h6 => HqRank.not_hq_of_pQuot hq2 h6 eS hB5 hHq
    rcases hsplit with ⟨hBB, h𝒮0, hBc⟩ | ⟨hF, -⟩
    swap
    ·
      exfalso
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have h3e : 3 ≤ Q₀.exponent :=
        hp3.trans (Nat.le_of_dvd Q₀.exponent_pos (dvd_exponent_of_fieldElt hF hK))
      apply hnot
      rcases hd with ⟨n, hn, hdB, -⟩ | ⟨n, hn, hdD, -, -⟩ | ⟨n, hn, hdT, -, -⟩
      · rw [hdB]
        show Q₀.p = q ∧ (4 ≤ n ∨ (n = 3 ∧ 3 ≤ Q₀.exponent))
        exact ⟨hQ₀, by omega⟩
      · rw [hdD]
        show Q₀.p = q ∧ (5 ≤ n ∨ (n = 4 ∧ 3 ≤ Q₀.exponent))
        exact ⟨hQ₀, by omega⟩
      · rw [hdT]
        show Q₀.p = q ∧ (5 ≤ n ∨ (n = 4 ∧ 3 ≤ Q₀.exponent))
        exact ⟨hQ₀, by omega⟩
    have ht3 : T.card = 3 := by
      have h' : p ^ 4 ≤ p ^ (T.card + 1) := hBc ▸ h4
      have := (Nat.pow_le_pow_iff_right hp.one_lt).1 h'
      omega
    have hm8 : m ≤ 8 := by
      by_contra hm9
      apply hnot
      rcases hd with ⟨n, hn, hdB, hmn⟩ | ⟨n, hn, hdD, hmn, -⟩ | ⟨n, hn, hdT, hmn, -⟩
      · rw [hdB]
        show Q₀.p = q ∧ (4 ≤ n ∨ (n = 3 ∧ 3 ≤ Q₀.exponent))
        exact ⟨hQ₀, Or.inl (by omega)⟩
      · rw [hdD]
        show Q₀.p = q ∧ (5 ≤ n ∨ (n = 4 ∧ 3 ≤ Q₀.exponent))
        exact ⟨hQ₀, Or.inl (by omega)⟩
      · rw [hdT]
        show Q₀.p = q ∧ (5 ≤ n ∨ (n = 4 ∧ 3 ≤ Q₀.exponent))
        exact ⟨hQ₀, Or.inl (by omega)⟩
    obtain ⟨H₁, H₂, H₃, h12, h13, h23, hTeq⟩ := Finset.card_eq_three.1 ht3
    have h1 : H₁ ∈ T := by rw [hTeq]; simp
    have h2' : H₂ ∈ T := by rw [hTeq]; simp
    have h3 : H₃ ∈ T := by rw [hTeq]; simp
    have hsum3 := hsubsum T le_rfl
    rw [hTeq, Finset.sum_insert (by simp [h12, h13]), Finset.sum_pair h23] at hsum3
    have hplane : ∃ H ∈ T, finrank K ↥(weightSpace ρ H.1) = 2 := by
      by_contra hcon
      push Not at hcon
      have h4' : ∀ H ∈ T, 4 ≤ finrank K ↥(weightSpace ρ H.1) := fun H hH => by
        obtain ⟨k, hk⟩ := hev H
        have := hge2 H hH
        have := hcon H hH
        omega
      have := h4' H₁ h1
      have := h4' H₂ h2'
      have := h4' H₃ h3
      omega
    obtain ⟨Hq, hqT, hq2d⟩ := hplane
    have hqK := hdvdQ Hq hqT hq2d
    have hmax0 : IsMaxElem (polarBilin Q) ρ p ∅ := h𝒮0 ▸ hmaxE
    have hqN : p ∣ Fintype.card K - 1 ∨ p ∣ Fintype.card K + 1 := by
      rw [← Nat.card_eq_fintype_card]
      have h1K : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
      rcases hqK with h | h
      · left
        have e : ((Nat.card K - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) - 1 := by
          rw [Nat.cast_sub h1K, Nat.cast_one]
        rw [← e] at h
        exact_mod_cast h
      · right
        exact_mod_cast h
    have hpl : ∀ H ∈ T, finrank K ↥(weightSpace ρ H.1) = 2 := fun H hH =>
      finrank_weightSpace_eq_two (polarBilin Q) ρ hA hp hp2 hpK hρ
        (fun u v => by rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_comm]) h2 hQ.1
        hmax0 hqN H ((hT H).1 hH)
    have hIP := hinvol H₁ H₂ H₃ h1 h2' h3 h12 h13 h23
    rcases hd with ⟨n, hn, hdB, hmn⟩ | ⟨n, hn, -, hmn, hplusQ⟩ | ⟨n, hn, hdT, hmn, -⟩
    ·
      right
      have hn3 : n = 3 := by omega
      subst hn3
      unfold S267ConcBCDE
      exact Or.inr (Or.inr (Or.inl ⟨by rw [hBc, ht3], hBB.symm.trans hIP.1, hIP.2.1,
        center_pQuot_eq_bot hcore hZ, Q₀, hQ₀, Or.inl ⟨TauCeti.CFSGIndex.lie d, hdB, eS⟩,
        dvd_card_sq_sub_one hK hqK⟩))
    ·
      exfalso
      have hm8' : m = 8 := by omega
      exact not_isPlusType_of_three_planes Q hp hA hpK hQ h2 hp2 hAεβ hmax0 hT ht3 hpl hm8'
        hplusQ
    ·
      right
      have hn4 : n = 4 := by omega
      subst hn4
      unfold S267ConcBCDE
      exact Or.inr (Or.inr (Or.inl ⟨by rw [hBc, ht3], hBB.symm.trans hIP.1, hIP.2.1,
        center_pQuot_eq_bot hcore hZ, Q₀, hQ₀, Or.inr ⟨TauCeti.CFSGIndex.lie d, hdT, eS⟩,
        dvd_card_sq_sub_one hK hqK⟩))

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
