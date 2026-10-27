module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsTwo
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE7

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Solomon.LocalBalance

set_option linter.unusedSectionVars false

section Transport

theorem map_centralizer_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) (t : A) :
    (Subgroup.centralizer ({t} : Set A)).map φ.toMonoidHom = Subgroup.centralizer {φ t} := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg φ h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    exact this
  · intro h
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h

theorem gLAPPrimeCoreOf_centralizer_eq_bot_iff {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    (t : A) : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({t} : Set A)) = ⊥ ↔
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({φ t} : Set B)) = ⊥ := by
  rw [← map_centralizer_mulEquiv φ t,
    gLAPPrimeCoreOf_map_of_injective 3 φ.toMonoidHom φ.injective]
  constructor
  · intro h
    rw [h, Subgroup.map_bot]
  · exact eq_bot_of_map_eq_bot φ.injective

theorem normal_of_relIndex_dvd_two {G : Type*} [Group G] {M W : Subgroup G} (hMW : M ≤ W)
    (hd : M.relIndex W ∣ 2) :
    (∀ u ∈ W, ∀ m ∈ M, u * m * u⁻¹ ∈ M) ∧ (∀ g ∈ W, g ^ 3 = 1 → g ∈ M) := by
  have h12 : (M.subgroupOf W).index = 1 ∨ (M.subgroupOf W).index = 2 :=
    (Nat.dvd_prime Nat.prime_two).1 hd
  rcases h12 with h1 | h2
  · have htop := Subgroup.index_eq_one.1 h1
    have hWM : W ≤ M := fun g hg => by
      have : (⟨g, hg⟩ : W) ∈ M.subgroupOf W := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this
    exact ⟨fun u hu m hm => hWM (mul_mem (mul_mem hu (hMW hm)) (inv_mem hu)),
      fun g hg _ => hWM hg⟩
  · have hN := Subgroup.normal_of_index_eq_two h2
    refine ⟨fun u hu m hm => ?_, fun g hg hg3 => ?_⟩
    · have := hN.conj_mem ⟨m, hMW hm⟩ (Subgroup.mem_subgroupOf.2 hm) ⟨u, hu⟩
      exact Subgroup.mem_subgroupOf.1 this
    · have hsq : g * g ∈ M := Subgroup.mem_subgroupOf.1
        (Subgroup.mul_self_mem_of_index_two h2 ⟨g, hg⟩)
      have : g = (g * g) * (g * g) := by
        calc g = g * g ^ 3 := by rw [hg3, mul_one]
          _ = (g * g) * (g * g) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [this]
      exact mul_mem hsq hsq

end Transport

section Model

variable {τ : Tag} {L : Type} [Field L] [CharP L 2]

theorem innerOneBalanceThree_of_model {X : Type*} [Group X] [Finite X]
    (hinj : Function.Injective (MulAut.conj : X →* MulAut X)) {W M : Subgroup (ModGL τ L)}
    (e : X ≃* M) (hMW : M ≤ W) (hnorm : ∀ u ∈ W, ∀ m ∈ M, u * m * u⁻¹ ∈ M) {ω : Lˣ}
    (hG : ∀ x, dV (τ := τ) ω x ∈ M)
    (hfus : ∀ s ∈ W, s ^ 3 = 1 → ∃ u ∈ W, ∃ x : Fin τ.rank → ZMod 3, u * s * u⁻¹ = dV ω x)
    (hbal : ∀ x : Fin τ.rank → ZMod 3, x ≠ 0 →
      GLAPPrimeCoreOf 3 (Subgroup.centralizer {dG hG x}) = ⊥)
    (hrig : ∀ t : X, t ^ 3 = 1 → t ≠ 1 → ∀ α : MulAut X,
      (∀ y ∈ Subgroup.centralizer {t}, α y = y) → α ∈ innerAut X) :
    InnerOneBalanceThree X := by
  refine innerOneBalanceThree_of_toral hinj {t | t ^ 3 = 1 ∧ t ≠ 1}
    (fun s hs3 hs1 => ⟨1, by simpa using ⟨hs3, hs1⟩⟩) ?_ (fun t ht => hrig t ht.1 ht.2)
  rintro t ⟨ht3, ht1⟩
  rw [gLAPPrimeCoreOf_centralizer_eq_bot_iff e t]
  have he3 : ((e t : M) : ModGL τ L) ^ 3 = 1 := by
    have h1 : (e t) ^ 3 = 1 := by rw [← map_pow, ht3, map_one]
    have := congrArg (fun m : M => (m : ModGL τ L)) h1
    simpa using this
  obtain ⟨u, huW, x, hux⟩ := hfus _ (hMW (e t).2) he3
  have hmap : M.map (MulAut.conj u).toMonoidHom = M := by
    refine le_antisymm ?_ fun m hm => ⟨u⁻¹ * m * u, ?_, ?_⟩
    · rintro _ ⟨m, hm, rfl⟩
      exact hnorm u huW m hm
    · have := hnorm u⁻¹ (inv_mem huW) m hm
      rwa [inv_inv] at this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  set φ : M ≃* M := ((MulAut.conj u).subgroupMap M).trans (MulEquiv.subgroupCongr hmap) with hφ
  rw [gLAPPrimeCoreOf_centralizer_eq_bot_iff φ (e t)]
  have hφt : φ (e t) = dG hG x := Subtype.ext hux
  rw [hφt]
  refine hbal x fun hx0 => ht1 ?_
  have h1 : φ (e t) = 1 := by
    rw [hφt]
    apply Subtype.ext
    rw [hx0]
    exact dV_zero ω
  have h2 : e t = 1 := by
    rw [← map_one φ] at h1
    exact φ.injective h1
  rw [← map_one e] at h2
  exact e.injective h2

end Model

section Two

variable {K : Type} [Field K] [Finite K]

theorem charP_two_of_card_two (hK : Nat.card K = 2) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have h : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK] at h
  exact (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h)

theorem eq_zero_or_eq_one_of_card_two (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
    have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.1 h1).1
    have h2 : Units.mk0 c hc = 1 := Subsingleton.elim _ _
    exact congrArg Units.val h2

theorem mem_innerAut_of_card_two
    (hK : Nat.card K = 2)
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) (α : MulAut (adjointGroup τ K)) :
    α ∈ innerAut (adjointGroup τ K) := by
  obtain ⟨hnf, Θ, hΘ, -, hker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form (f := 1) le_rfl K
      (by rw [hK]; norm_num) τ hτ
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hnf α
  simp only at hgσ
  have hσ : σ = RingEquiv.refl K := RingEquiv.ext fun c => by
    rcases eq_zero_or_eq_one_of_card_two hK c with rfl | rfl
    · rw [map_zero]; rfl
    · rw [map_one]; rfl
  have h1 : Θ α = σ := hΘ α g σ hgσ
  have h2 : α ∈ Θ.ker := by
    rw [MonoidHom.mem_ker, h1, hσ]
    rfl
  rw [hker] at h2
  exact h2

end Two

section Consumers

variable {K : Type} [Field K] [Finite K]

theorem innerOneBalanceThree_E8_two
    (hK : Nat.card K = 2) : InnerOneBalanceThree (adjointGroup Tag.E8 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card_two hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data Tag.E8 K e8Neg
  have hFr2 : Fr = iterateFrobenius (AlgebraicClosure K) 2 1 :=
    RingHom.ext fun c => by rw [hFr, hK, iterateFrobenius_two_one]
  subst hFr2
  have hMW := langModel_le_twModel Tag.E8 K (AlgebraicClosure K) hFr hg0C hg0
  have : Finite (twModel (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8Neg)
      (iterateFrobenius (AlgebraicClosure K) 2 1)) := finite_twModel hg0C hg0
  have hWM := le_langModel_E8_of_le_twModel K (AlgebraicClosure K) hFr hg0C hg0 (P :=
    twModel (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8Neg)
      (iterateFrobenius (AlgebraicClosure K) 2 1)) le_rfl
  have : Finite (langModel Tag.E8 K (AlgebraicClosure K) g0) :=
    finite_langModel Tag.E8 K (AlgebraicClosure K) g0
  obtain ⟨ω, hω, -⟩ := exists_orderOf_eq_of_dvd_add_one K (L := AlgebraicClosure K) (N := 3)
    (by rw [hK])
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hG : ∀ x, dV (τ := Tag.E8) ω x ∈ langModel Tag.E8 K (AlgebraicClosure K) g0 := fun x =>
    hWM (dV_mem_twModel rootDiagUnit_mem_torusGroup_E8 e8Neg_smul hω3 x)
  have hLang : ∀ a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) →
      ∀ c ∈ toralCentralizer Tag.E8 (AlgebraicClosure K) a,
        ∃ z ∈ toralCentralizer Tag.E8 (AlgebraicClosure K) a, z⁻¹ * frobTwistGL Tag.E8
          (AlgebraicClosure K) 2 1 (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K)
            e8Neg) z = c := fun a ha3 c hc =>
    toral_centralizer_Lang_E8_three 2 (AlgebraicClosure K) (by norm_num) a ha3 1 le_rfl
      (canonicalRep_mem_adjointGroup _ _ _) (s := 2) (by norm_num)
      (canonicalRep_conj_rootDiagUnit_sq e8Neg_smul ha3) c hc
  exact innerOneBalanceThree_of_model mulAut_conj_injective_adjointGroup
    (langModelEquiv Tag.E8 K (AlgebraicClosure K) g0) hMW
    (fun u hu m hm => hWM (mul_mem (mul_mem hu (hMW hm)) (inv_mem hu))) hG
    (fun s hs hs3 => exists_conj_dV_twModel (isAlgebraic_zmod_algebraicClosure_of_finite K 2)
      (monomialToralAt_three_of_block a2BlockToral_E8) e8Neg_smul hLang hω hs hs3)
    (fun x hx => gLAPPrimeCoreOf_centralizer_dV_two rootDiagUnit_mem_torusGroup_E8 e8Neg_smul
      hMW (fun g hg _ => hWM hg) hω hG Certificates.certificate13666.2.2.1 hx)
    (fun _ _ _ α _ => mem_innerAut_of_card_two hK (Or.inr rfl) α)

theorem innerOneBalanceThree_E7_two
    (hK : Nat.card K = 2) :
    InnerOneBalanceThree (adjointGroup Tag.E7 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card_two hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data Tag.E7 K e7Neg
  have hFr2 : Fr = iterateFrobenius (AlgebraicClosure K) 2 1 :=
    RingHom.ext fun c => by rw [hFr, hK, iterateFrobenius_two_one]
  subst hFr2
  set W := twModel (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) e7Neg)
    (iterateFrobenius (AlgebraicClosure K) 2 1) with hW
  set M := e7Model K (AlgebraicClosure K) g0 with hM
  have hMW : M ≤ W := e7Model_le_twModel K (AlgebraicClosure K) hFr hg0C hg0
  have : Finite W := finite_twModel hg0C hg0
  have : Finite M := finite_e7Model K (AlgebraicClosure K) g0
  have hd : M.relIndex W ∣ 2 := by
    set X := W.map (MulAut.conj g0).toMonoidHom with hX
    have : Finite X := Finite.of_surjective ((MulAut.conj g0).toMonoidHom.subgroupMap W)
      ((MulAut.conj g0).toMonoidHom.subgroupMap_surjective W)
    have hXF := map_conj_twModel hg0C hg0
    have hdesc := (finite_fixed_subgroup_rational_perfect 2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      (iterateFrobenius (AlgebraicClosure K) 2 1) hFr X (fun x hx => by
        rw [hX, hXF] at hx
        exact hx.1) (fun x hx => by
        rw [hX, hXF] at hx
        exact hx.2)).1
    have hcomp : (MulAut.conj g0).toMonoidHom.comp (MulAut.conj g0⁻¹).toMonoidHom =
        MonoidHom.id _ := by
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    have hMX : M.map (MulAut.conj g0).toMonoidHom =
        (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
      rw [hM, e7Model, Subgroup.map_map, hcomp, Subgroup.map_id]
    rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g0).toMonoidHom) _ _
      (MulAut.conj g0).injective, hMX]
    exact hdesc
  obtain ⟨hnorm, h3⟩ := normal_of_relIndex_dvd_two hMW hd
  obtain ⟨ω, hω, -⟩ := exists_orderOf_eq_of_dvd_add_one K (L := AlgebraicClosure K) (N := 3)
    (by rw [hK])
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hG : ∀ x, dV (τ := Tag.E7) ω x ∈ M := fun x =>
    h3 _ (dV_mem_twModel rootDiagUnit_mem_torusGroup_E7 e7Neg_smul hω3 x) (dV_pow_three hω3 x)
  have hLang : ∀ a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) →
      ∀ c ∈ toralCentralizer Tag.E7 (AlgebraicClosure K) a,
        ∃ z ∈ toralCentralizer Tag.E7 (AlgebraicClosure K) a, z⁻¹ * frobTwistGL Tag.E7
          (AlgebraicClosure K) 2 1 (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K)
            e7Neg) z = c := fun a ha3 c hc =>
    toral_centralizer_Lang_E7_three 2 (AlgebraicClosure K) (by norm_num) a ha3 1 le_rfl
      (canonicalRep_mem_adjointGroup _ _ _) (s := 2) (by norm_num)
      (canonicalRep_conj_rootDiagUnit_sq e7Neg_smul ha3) c hc
  exact innerOneBalanceThree_of_model mulAut_conj_injective_adjointGroup
    (e7ModelEquiv K (AlgebraicClosure K) g0) hMW hnorm hG
    (fun s hs hs3 => exists_conj_dV_twModel (isAlgebraic_zmod_algebraicClosure_of_finite K 2)
      (monomialToralAt_three_of_block a2BlockToral_E7) e7Neg_smul hLang hω hs hs3)
    (fun x hx => gLAPPrimeCoreOf_centralizer_dV_two rootDiagUnit_mem_torusGroup_E7 e7Neg_smul
      hMW h3 hω hG Certificates.certificate13666.2.1 hx)
    (fun _ _ _ α _ => mem_innerAut_of_card_two hK (Or.inl rfl) α)

end Consumers

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
