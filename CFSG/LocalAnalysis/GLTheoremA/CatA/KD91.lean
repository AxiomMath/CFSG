module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.I91
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.FieldActorFixed
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.G2Subgroup
public import CFSG.Assembly.InCatalogConverse
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor fixSubfield fieldActor_one fieldActor_mul
  ringEquiv_cube_apply_eq)
open CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3 (fixSubgroupFieldActorEquiv)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (exists_catEquiv_trialityD4)
open CFSG.HardMathSupport.Seitz.TrialityOdd.Inner (trialityFieldImageEquivG2)
open CFSG.Blueprint.Chevalley (TwistTag)


private theorem kd91_cube_roots_cyclic {G : Type} [Group G] [Finite G] [IsCyclic G] {σ x : G}
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hx : x ^ 3 = 1) : x = 1 ∨ x = σ ∨ x = σ ^ 2 := by
  classical
  haveI := Fintype.ofFinite G
  have hσ2 : σ ^ 2 ≠ 1 := by
    intro h
    apply hσ1
    have h4 : σ ^ 4 = σ := by rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hσ3, one_mul]
    have h4' : σ ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
    exact h4.symm.trans h4'
  have hss : σ ≠ σ ^ 2 := by
    intro h
    apply hσ1
    have h' : σ * σ = σ * 1 := by rw [mul_one, ← pow_two]; exact h.symm
    exact mul_left_cancel h'
  have hne : (1 : G) ≠ σ := fun h => hσ1 h.symm
  have hne' : (1 : G) ≠ σ ^ 2 := fun h => hσ2 h.symm
  have hcard : ({1, σ, σ ^ 2} : Finset G).card = 3 :=
    Finset.card_eq_three.2 ⟨1, σ, σ ^ 2, hne, hne', hss, rfl⟩
  have hle : (Finset.univ.filter fun a : G => a ^ 3 = 1).card ≤ 3 :=
    IsCyclic.card_pow_eq_one_le (by norm_num)
  have hsub : ({1, σ, σ ^ 2} : Finset G) ⊆ Finset.univ.filter fun a : G => a ^ 3 = 1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases ha with rfl | rfl | rfl
    · exact one_pow 3
    · exact hσ3
    · rw [← pow_mul, mul_comm, pow_mul, hσ3, one_pow]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hle)
  have hxS : x ∈ Finset.univ.filter fun a : G => a ^ 3 = 1 := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hx⟩
  rw [← heq] at hxS
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hxS

private theorem kd91_cube_eq_one {p f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (p ^ f)) : σ ^ 3 = 1 := by
  refine RingEquiv.ext fun c => ?_
  simpa [pow_succ] using ringEquiv_cube_apply_eq hK hσ c

private theorem kd91_frob_ne_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (p ^ f)) : σ ≠ 1 := by
  intro h1
  have hroot : ∀ c : K, c ^ (p ^ f) = c := fun c => by
    have := congrArg (fun τ : K ≃+* K => τ c) h1
    simpa [hσ] using this
  classical
  haveI := Fintype.ofFinite K
  have hQ : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
  have hdeg : (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial K).natDegree = p ^ f :=
    FiniteField.X_pow_card_sub_X_natDegree_eq K hQ
  have hne : (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial K) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ : Finset K).val ⊆
      (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial K).roots := by
    intro c _
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hroot c, sub_self]
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg, Finset.card_univ, ← Nat.card_eq_fintype_card, hK] at hle
  generalize p ^ f = x at hle hQ
  have h2 : 2 ≤ x := hQ
  nlinarith [Nat.mul_le_mul_left x h2, Nat.mul_le_mul_left (x * x) h2]

private theorem kd91_fieldActor_pow {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K) (n : ℕ) :
    fieldActor (t := TwistTag.D4) σ (δ ^ n) = fieldActor (t := TwistTag.D4) σ δ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, fieldActor_one]
  | succ n ih =>
    rw [pow_succ δ n, fieldActor_mul, ih, pow_succ (fieldActor (t := TwistTag.D4) σ δ) n]

private theorem kd91_fixSubgroup_inv {X : Type} [Group X] (α : MulAut X) :
    fixSubgroup α⁻¹ = fixSubgroup α := by
  ext x
  show α⁻¹ x = x ↔ α x = x
  constructor
  · intro h
    calc α x = α (α⁻¹ x) := by rw [h]
      _ = x := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  · intro h
    calc α⁻¹ x = α⁻¹ (α x) := by rw [h]
      _ = x := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

private noncomputable def kd91_fixSubgroupCongr {S C : Type} [Group S] [Group C] (e : S ≃* C)
    (γ : MulAut S) : ↥(fixSubgroup γ) ≃* ↥(fixSubgroup (MulAut.congr e γ)) := by
  have hmap : (fixSubgroup γ).map e.toMonoidHom = fixSubgroup (MulAut.congr e γ) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : γ x = x := hx
      show e (γ (e.symm (e x))) = e x
      rw [MulEquiv.symm_apply_apply, hx']
    · intro hy
      refine Subgroup.mem_map.2 ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      have h : e (γ (e.symm y)) = y := hy
      show γ (e.symm y) = e.symm y
      calc γ (e.symm y) = e.symm (e (γ (e.symm y))) := (e.symm_apply_apply _).symm
        _ = e.symm y := by rw [h]
  exact (Subgroup.equivMapOfInjective (fixSubgroup γ) e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hmap)

private theorem kd91_normal_form {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    (∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
        α = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ) ∧
    (∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      ∀ (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
        (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
        α = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ → Θ α = δ) ∧
    IsCyclic (K ≃+* K) := by
  by_cases h2 : p = 2
  · subst h2
    obtain ⟨-, hu, ⟨Θ, hΘ, -⟩, hcyc, -⟩ :=
      CFSG.LieType.Chevalley.even_triality_exact_automorphism_normal_form hf K hK σ hσ
    exact ⟨fun α => by
      obtain ⟨⟨g, δ⟩, h⟩ := (hu α).exists
      exact ⟨g, δ, h⟩, ⟨Θ, hΘ⟩, hcyc⟩
  · obtain ⟨-, hu, ⟨Θ, hΘ, -⟩, hcyc, -⟩ :=
      CFSG.LieType.Chevalley.odd_triality_exact_automorphism_normal_form hp h2 hf K hK σ hσ
    exact ⟨fun α => by
      obtain ⟨⟨g, δ⟩, h⟩ := (hu α).exists
      exact ⟨g, δ, h⟩, ⟨Θ, hΘ⟩, hcyc⟩

private theorem kd91_coset {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ3 : β ^ 3 = 1)
    (hβi : β ∉ innerAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      (δ = σ ∨ δ = σ ^ 2) ∧ MulAut.conj g * β = fieldActor (t := TwistTag.D4) σ δ := by
  obtain ⟨hdec, ⟨Θ, hΘ⟩, hcyc⟩ := kd91_normal_form hp hf K hK σ hσ
  haveI := hcyc
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (fun a b h => RingEquiv.ext fun x => congrFun h x)
  obtain ⟨g₀, δ₀, hβ⟩ := hdec β
  have h3 : δ₀ ^ 3 = 1 := by
    rw [← hΘ β g₀ δ₀ hβ, ← map_pow, hβ3, map_one]
  have hδ1 : δ₀ ≠ 1 := by
    intro h
    apply hβi
    exact MonoidHom.mem_range.2 ⟨g₀, by rw [hβ, h, fieldActor_one, mul_one]⟩
  rcases kd91_cube_roots_cyclic (kd91_cube_eq_one hK hσ) (kd91_frob_ne_one hp hf hK hσ) h3 with
    h | h | h
  · exact absurd h hδ1
  · exact ⟨g₀⁻¹, δ₀, Or.inl h, by rw [hβ, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]⟩
  · exact ⟨g₀⁻¹, δ₀, Or.inr h, by rw [hβ, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]⟩

private theorem kd91_fixSubgroup_G2 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (q.p ^ q.exponent) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent)) :
    Nonempty (↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) ≃*
      TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (fun a b h => RingEquiv.ext fun x => congrFun h x)
  have hq3 : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hσ3' : σ ^ 3 = 1 := kd91_cube_eq_one hK hσ
  have hσ1 : σ ≠ 1 := kd91_frob_ne_one q.prime_p q.exponent_pos hK hσ
  have hF : Nat.card (fixSubfield σ) = q.card := by
    have hK' : Nat.card K = q.p ^ (3 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
    have hord : orderOf σ = 3 := orderOf_eq_prime hσ3' hσ1
    obtain ⟨-, hc⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield q.prime_p
      (by have := q.exponent_pos; omega) hK' σ
    rw [hord, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)] at hc
    rw [TauCeti.PrimePower.card_def]
    exact hc
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    rw [ENat.card_eq_coe_natCard, hF]
    exact_mod_cast hq3
  have hZ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := CFSG.Blueprint.Chevalley.Tag.G2)
    (K := ↥(fixSubfield σ))
  obtain ⟨eQ⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv ↥(fixSubfield σ) hF
  have eAdj := ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eQ
  exact ⟨(fixSubgroupFieldActorEquiv K σ hσ3).trans
    ((trialityFieldImageEquivG2 σ hk3).trans eAdj)⟩

private theorem kd91_catalog_fix {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (hq2 : 2 < q.card) (hq3 : ¬ 3 ∣ q.card)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (q.p ^ q.exponent) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent))
    (δ : K ≃+* K) (hδ : δ = σ ∨ δ = σ ^ 2) :
    catalogIs ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ δ)) (onLie isG2Big) := by
  have hσ3' : σ ^ 3 = 1 := kd91_cube_eq_one hK hσ
  have hEq : fixSubgroup (fieldActor (t := TwistTag.D4) σ δ) =
      fixSubgroup (fieldActor (t := TwistTag.D4) σ σ) := by
    rcases hδ with rfl | rfl
    · rfl
    · have hinv : fieldActor (t := TwistTag.D4) σ (σ ^ 2) =
          (fieldActor (t := TwistTag.D4) σ σ)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← fieldActor_mul, show σ ^ 2 * σ = 1 by rw [← pow_succ]; exact hσ3', fieldActor_one]
      rw [hinv, kd91_fixSubgroup_inv]
  rw [hEq]
  obtain ⟨e⟩ := kd91_fixSubgroup_G2 hv hK hσ
  exact ⟨TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩, (show 2 < q.card ∧ ¬ 3 ∣ q.card from ⟨hq2, hq3⟩), ⟨e⟩⟩

private theorem kd91_clause_b {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq2 : 2 < q.card) (hq3 : ¬ 3 ∣ q.card)
    (eS : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    ∀ β : MulAut S, β ^ 3 = 1 → β ∉ innerAut S →
      ∃ g : S, (MulAut.conj g * β) ^ 3 = 1 ∧
        catalogIs ↥(fixSubgroup (MulAut.conj g * β)) (onLie isG2Big) := by
  intro β hβ3 hβi
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eC⟩⟩ := exists_catEquiv_trialityD4 q hv
  have hvG2 : (TauCeti.LieTypeIndex.G2 q).Valid :=
    (TauCeti.LieTypeIndex.valid_iff _).2
      ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 (show 3 ≤ q.card by omega),
        by simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]⟩
  have hK' : Nat.card K = (q.p ^ q.exponent) ^ 3 := hK
  let e : S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := eS.trans eC
  have hconj : ∀ y : S, MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
    intro y
    refine MulEquiv.ext fun z => ?_
    show e (y * e.symm z * y⁻¹) = e y * z * (e y)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hβ'3 : (MulAut.congr e β) ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hβ'i : MulAut.congr e β ∉ innerAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    intro h
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 h
    apply hβi
    refine MonoidHom.mem_range.2 ⟨e.symm x, ?_⟩
    apply (MulAut.congr e).injective
    rw [hconj, e.apply_symm_apply]
    exact hx
  obtain ⟨g, δ, hδ, hgδ⟩ := kd91_coset q.prime_p q.exponent_pos K hK' σ hσ (MulAut.congr e β) hβ'3 hβ'i
  have hkey : MulAut.congr e (MulAut.conj (e.symm g) * β) = fieldActor (t := TwistTag.D4) σ δ := by
    rw [map_mul, hconj, e.apply_symm_apply]
    exact hgδ
  refine ⟨e.symm g, ?_, ?_⟩
  · apply (MulAut.congr e).injective
    have hδ3 : δ ^ 3 = 1 := by
      rcases hδ with rfl | rfl
      · exact kd91_cube_eq_one hK' hσ
      · rw [← pow_mul, mul_comm, pow_mul, kd91_cube_eq_one hK' hσ, one_pow]
    rw [map_pow, hkey, map_one, ← kd91_fieldActor_pow, hδ3, fieldActor_one]
  · obtain ⟨i, hi, ⟨eF⟩⟩ := kd91_catalog_fix hvG2 hq2 hq3 hK' hσ δ hδ
    have hiso := kd91_fixSubgroupCongr e (MulAut.conj (e.symm g) * β)
    rw [hkey] at hiso
    exact ⟨i, hi, ⟨hiso.trans eF⟩⟩

private theorem kd91_td4_of_catalog {S : Type} [Group S] (h : catalogIs S (onLie isTrialityD4Big)) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      2 < q.card ∧ ¬ 3 ∣ q.card ∧
        Nonempty (S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex h
  cases d with
  | trialityD4 q =>
    obtain ⟨h1, h2⟩ := hP
    exact ⟨q, hv, h1, h2, ⟨e⟩⟩
  | _ => exact hP.elim

private theorem kd91_g2_of_catalog {T : Type} [Group T] (h : catalogIs T (onLie isG2Big)) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid),
      2 < q.card ∧ ¬ 3 ∣ q.card ∧
        Nonempty (T ≃* TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex h
  cases d with
  | G2 q =>
    obtain ⟨h1, h2⟩ := hP
    exact ⟨q, hv, h1, h2, ⟨e⟩⟩
  | _ => exact hP.elim

private theorem kd91_clause_a {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (eS : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    ∀ (E : Type) [Group E] [Finite E], CFSG.Open.IsQuasisimple E →
      IsPGroup 3 (Subgroup.center E) → Nonempty ((E ⧸ Subgroup.center E) ≃* S) →
        Subgroup.center E = ⊥ := by
  intro E _ _ hQ _ ⟨eQ⟩
  have hm : CFSG.Models.LieModel (E ⧸ Subgroup.center E) .trialityD4 0 q.p q.exponent :=
    CFSG.Models.lieModel_of_namesTag ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ (eQ.trans eS)
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hdvd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := 1) (d := 1) rfl rfl
    (by norm_num)
  have hc1 : Nat.card (Subgroup.center E) = 1 := Nat.dvd_one.1 (by simpa using hdvd)
  exact Subgroup.eq_bot_of_card_eq _ hc1

private theorem kd91_clause_c {T : Type} [Group T] [Finite T] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hq2 : 2 < q.card) (hq3 : ¬ 3 ∣ q.card)
    (eT : T ≃* TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) :
    IsSimpleGroup T ∧ (∃ a b : T, a * b ≠ b * a) ∧ 3 ∣ Nat.card T := by
  have hsimple : IsSimpleGroup T := (MulEquiv.isSimpleGroup_congr eT).2
    (CFSG.Assembly.lie_finite_simple ⟨.G2 q, hv⟩).2
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hq3' : 3 ≤ q.card := by omega
  have hq3'' : 3 ≤ q.p ^ q.exponent := by rw [← TauCeti.PrimePower.card_def]; exact hq3'
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv (GaloisField q.p q.exponent)
    (by rw [hK, TauCeti.PrimePower.card_def])
  have hL : CFSG.Blueprint.LieModel T .G2 0 q.p q.exponent :=
    Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags],
      ⟨⟨q.prime_p, q.exponent_pos, rfl, hq3''⟩, GaloisField q.p q.exponent, inferInstance,
        inferInstance, hK, ⟨eT.trans b.symm⟩⟩⟩)
  obtain ⟨-, hord, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput T .G2 0 q.p
    q.exponent (CFSG.Blueprint.LieModel.admissible hL) hL
  have hdiv : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .G2 0 (q.p ^ q.exponent) = 1 := rfl
  have hnum : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .G2 0 (q.p ^ q.exponent) =
      (q.p ^ q.exponent) ^ 6 * ((q.p ^ q.exponent) ^ 6 - 1) * ((q.p ^ q.exponent) ^ 2 - 1) := rfl
  rw [hdiv, mul_one, hnum, ← TauCeti.PrimePower.card_def] at hord
  have h3sq : 3 ∣ q.card ^ 2 - 1 := by
    have hmod : q.card % 3 = 1 ∨ q.card % 3 = 2 := by omega
    have hsq : q.card ^ 2 % 3 = 1 := by
      rcases hmod with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
    generalize q.card ^ 2 = M at hsq ⊢
    omega
  have h3 : 3 ∣ Nat.card T := by
    rw [hord]
    exact Dvd.dvd.mul_left h3sq _
  have hnab : ∃ a b : T, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    haveI : IsMulCommutative T := ⟨⟨fun a b => hcon a b⟩⟩
    have hprime : (Nat.card T).Prime := Group.is_simple_iff_prime_card.1 hsimple
    rw [hord] at hprime
    have h9 : 9 ≤ q.card ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq3' 2)
    have h729 : 729 ≤ q.card ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hq3' 6)
    rcases Nat.prime_mul_iff.1 hprime with ⟨-, h⟩ | ⟨-, h⟩
    · omega
    · have h1 := Nat.eq_one_of_mul_eq_one_right h
      omega
  exact ⟨hsimple, hnab, h3⟩

theorem kd91_holds : KD91 := by
  intro S _ _ hS
  obtain ⟨q, hv, hq2, hq3, ⟨eS⟩⟩ := kd91_td4_of_catalog hS
  refine ⟨kd91_clause_a hv eS, kd91_clause_b hv hq2 hq3 eS, fun T _ _ hT => ?_⟩
  obtain ⟨q', hv', hq2', hq3', ⟨eT⟩⟩ := kd91_g2_of_catalog hT
  exact kd91_clause_c hv' hq2' hq3' eT

theorem i91At_holds (G : Type) [Group G] [Finite G] : I91At G := i91At_of kd91_holds

end CFSG.LocalAnalysis.GLTheoremA

end
