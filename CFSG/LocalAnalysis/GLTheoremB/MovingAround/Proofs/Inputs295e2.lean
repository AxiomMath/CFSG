module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs295e
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterIn
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsTwoE

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295e

section Generic

open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
  (isPSolvable_of_mulEquiv)

theorem pow_three_multiplicative {r : ℕ} (a : Multiplicative (Fin r → ZMod 3)) : a ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  have : (3 : ZMod 3) = 0 := rfl
  rw [Nat.cast_ofNat, this, zero_mul]

theorem card_multiplicative_three (r : ℕ) :
    Nat.card (Multiplicative (Fin r → ZMod 3)) = 3 ^ r := by
  rw [Nat.card_eq_fintype_card]
  simp

theorem le_pRank_centralizer_of_mem {X : Type} [Group X] [Finite X] {t : X} {E : Subgroup X}
    (htE : t ∈ E) (hE : CFSG.Open.IsElemAbelian 3 E) {k : ℕ} (hk : Nat.card E = 3 ^ k) :
    k ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({t} : Set X)) := by
  refine CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (fun y hy => ?_) hE hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (hE.1.is_comm.comm (⟨y, hy⟩ : E) ⟨t, htE⟩)

theorem exists_elemAbelian_mem_of_fusion {G X A : Type} [Group G] [Group X] [CommGroup A]
    {W M : Subgroup G} (e : X ≃* M) (hnorm : ∀ u ∈ W, ∀ m ∈ M, u * m * u⁻¹ ∈ M) (D : A →* G)
    (hD : Function.Injective D) (hDM : ∀ a, D a ∈ M) (hA3 : ∀ a : A, a ^ 3 = 1)
    (hfus : ∀ s ∈ M, s ^ 3 = 1 → ∃ u ∈ W, ∃ a : A, u * s * u⁻¹ = D a)
    (t : X) (ht3 : t ^ 3 = 1) :
    ∃ E : Subgroup X, t ∈ E ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = Nat.card A := by
  have hs3 : ((e t : M) : G) ^ 3 = 1 := by
    have h1 : (e t) ^ 3 = 1 := by rw [← map_pow, ht3, map_one]
    have := congrArg (fun m : M => (m : G)) h1
    simpa using this
  obtain ⟨u, huW, a, hua⟩ := hfus _ (e t).2 hs3
  have hmem : ∀ b, u⁻¹ * D b * u ∈ M := fun b => by
    have := hnorm u⁻¹ (inv_mem huW) (D b) (hDM b)
    rwa [inv_inv] at this
  let ψ₀ : A →* M := MonoidHom.mk' (fun b => ⟨u⁻¹ * D b * u, hmem b⟩) (fun b c => Subtype.ext (by
    simp only [map_mul, Subgroup.coe_mul]
    group))
  have hψ₀ : ∀ b, (ψ₀ b : G) = u⁻¹ * D b * u := fun b => rfl
  let ψ : A →* X := e.symm.toMonoidHom.comp ψ₀
  have hψ : Function.Injective ψ := by
    intro b c h
    apply hD
    have h1 : ψ₀ b = ψ₀ c := e.symm.injective h
    have h2 : u⁻¹ * D b * u = u⁻¹ * D c * u := by rw [← hψ₀, ← hψ₀, h1]
    simpa using h2
  have hψa : ψ a = t := by
    apply e.injective
    change e (e.symm (ψ₀ a)) = e t
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [hψ₀, ← hua]
    group
  refine ⟨ψ.range, ⟨a, hψa⟩, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, b, rfl⟩ ⟨_, c, rfl⟩
    apply Subtype.ext
    change ψ b * ψ c = ψ c * ψ b
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨b, rfl⟩
    rw [← map_pow, hA3, map_one]
  · exact Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm

theorem inner295At_of_toral {d : TauCeti.ValidLieTypeIndex} {k : ℕ} (hk : 4 ≤ k)
    (h : ∃ (X : Type) (_ : Group X), Nonempty ((TauCeti.CFSGIndex.lie d).Group ≃* X) ∧
      ∀ t : X, t ^ 3 = 1 →
        ∃ E : Subgroup X, t ∈ E ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k) :
    Inputs295c.Inner295At d := by
  obtain ⟨X, _, ⟨eX⟩, hX⟩ := h
  intro K _ _ _ _ ⟨e⟩ _ _ _ x hx
  set θ : K ≃* X := e.trans eX with hθ
  have hx3 : θ x ^ 3 = 1 := by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  obtain ⟨E, hxE, hE, hc⟩ := hX (θ x) hx3
  have hE' : CFSG.Open.IsElemAbelian 3 (E.comap θ.toMonoidHom) :=
    Inputs295.isElemAbelian_comap θ.injective hE
  have hc' : Nat.card (E.comap θ.toMonoidHom) = 3 ^ k := by
    rw [← hc]
    have hmap : (E.comap θ.toMonoidHom).map θ.toMonoidHom = E :=
      Subgroup.map_comap_eq_self_of_surjective θ.surjective E
    conv_rhs => rw [← hmap]
    exact (Nat.card_congr ((E.comap θ.toMonoidHom).equivMapOfInjective θ.toMonoidHom
      θ.injective).toEquiv)
  exact Or.inr (Or.inl (hk.trans (le_pRank_centralizer_of_mem (E := E.comap θ.toMonoidHom)
    hxE hE' hc')))

theorem outerExcl295_of_congr {S T : Type} [Group S] [Group T] [Finite S] [Finite T]
    (θ : S ≃* T) (α : MulAut S) (h : Inputs295c.OuterExcl295 (MulAut.congr θ α)) :
    Inputs295c.OuterExcl295 α := by
  rcases h with ⟨P, hP, hPp, hPc⟩ | hβ | hβ
  · refine Or.inl ⟨P.comap θ.toMonoidHom, ?_, hPp.comap_of_injective θ.toMonoidHom θ.injective,
      ?_⟩
    · intro g hg
      have : θ g ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.congr θ α) := hP hg
      rw [Inputs295c.fixSubgroup_congr] at this
      obtain ⟨g', hg', hgg⟩ := this
      rw [θ.injective hgg] at hg'
      exact hg'
    · have hmap : (P.comap θ.toMonoidHom).map θ.toMonoidHom = P :=
        Subgroup.map_comap_eq_self_of_surjective θ.surjective P
      rw [← hmap] at hPc
      rwa [Nat.card_congr ((P.comap θ.toMonoidHom).equivMapOfInjective θ.toMonoidHom
        θ.injective).toEquiv]
  · rw [Inputs295c.fixSubgroup_congr,
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_map_eq_of_injective (by norm_num)
        θ.toMonoidHom θ.injective] at hβ
    exact Or.inr (Or.inl hβ)
  · rw [Inputs295c.fixSubgroup_congr] at hβ
    refine Or.inr (Or.inr fun hs => hβ ?_)
    exact isPSolvable_of_mulEquiv ((CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
      α).equivMapOfInjective _ θ.injective) hs

end Generic

section Twisted

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3


variable {K : Type} [Field K] [Finite K]

theorem exists_elemAbelian_F4_two (hK : Nat.card K = 2)
    (t : adjointGroup Tag.F4 K)
    (ht3 : t ^ 3 = 1) :
    ∃ E : Subgroup ↥(adjointGroup Tag.F4 K), t ∈ E ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ Tag.F4.rank := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card_two hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data Tag.F4 K f4Neg
  have hFr2 : Fr = iterateFrobenius (AlgebraicClosure K) 2 1 :=
    RingHom.ext fun c => by rw [hFr, hK, iterateFrobenius_two_one]
  subst hFr2
  have htorL : ∀ a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit Tag.F4 a ∈ torusGroup Tag.F4 (AlgebraicClosure K) :=
    rootDiagUnit_mem_torusGroup_of_unimodular exists_mul_cartan_F4.choose_spec
  obtain ⟨ω, hω, -⟩ := exists_orderOf_eq_of_dvd_add_one K (L := AlgebraicClosure K) (N := 3)
    (by rw [hK])
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hLang : ∀ a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) →
      ∀ c ∈ toralCentralizer Tag.F4 (AlgebraicClosure K) a,
        ∃ z ∈ toralCentralizer Tag.F4 (AlgebraicClosure K) a, z⁻¹ * frobTwistGL Tag.F4
          (AlgebraicClosure K) 2 1 (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K)
            f4Neg) z = c := fun a ha3 c hc =>
    toral_centralizer_Lang_F4_three 2 (AlgebraicClosure K) (by norm_num) a ha3 1 le_rfl
      (canonicalRep_mem_adjointGroup _ _ _) (s := 2) (by norm_num)
      (canonicalRep_conj_rootDiagUnit_sq f4Neg_smul ha3) c hc
  obtain ⟨E, htE, hE, hc⟩ := exists_elemAbelian_mem_of_fusion
    (twModelEquivF4 K (AlgebraicClosure K) hFr hg0C hg0)
    (fun u hu m hm => mul_mem (mul_mem hu hm) (inv_mem hu)) (dVHom (τ := Tag.F4) hω3)
    (fun x y hxy => Multiplicative.toAdd.injective
      (dV_injective hω (hxy : dV ω x.toAdd = dV ω y.toAdd)))
    (fun x => dV_mem_twModel htorL f4Neg_smul hω3 x.toAdd) pow_three_multiplicative
    (fun s hs hs3 => by
      obtain ⟨u, hu, x, hux⟩ := exists_conj_dV_twModel
        (isAlgebraic_zmod_algebraicClosure_of_finite K 2)
        (monomialToralAt_three_of_block a2BlockToral_F4) f4Neg_smul hLang hω hs hs3
      exact ⟨u, hu, Multiplicative.ofAdd x, hux⟩) t ht3
  exact ⟨E, htE, hE, hc.trans (card_multiplicative_three _)⟩

theorem exists_elemAbelian_E8_two
    (hK : Nat.card K = 2)
    (t : adjointGroup Tag.E8 K) (ht3 : t ^ 3 = 1) :
    ∃ E : Subgroup ↥(adjointGroup Tag.E8 K), t ∈ E ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ Tag.E8.rank := by
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
  obtain ⟨ω, hω, -⟩ := exists_orderOf_eq_of_dvd_add_one K (L := AlgebraicClosure K) (N := 3)
    (by rw [hK])
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hLang : ∀ a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) →
      ∀ c ∈ toralCentralizer Tag.E8 (AlgebraicClosure K) a,
        ∃ z ∈ toralCentralizer Tag.E8 (AlgebraicClosure K) a, z⁻¹ * frobTwistGL Tag.E8
          (AlgebraicClosure K) 2 1 (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K)
            e8Neg) z = c := fun a ha3 c hc =>
    toral_centralizer_Lang_E8_three 2 (AlgebraicClosure K) (by norm_num) a ha3 1 le_rfl
      (canonicalRep_mem_adjointGroup _ _ _) (s := 2) (by norm_num)
      (canonicalRep_conj_rootDiagUnit_sq e8Neg_smul ha3) c hc
  obtain ⟨E, htE, hE, hc⟩ := exists_elemAbelian_mem_of_fusion
    (langModelEquiv Tag.E8 K (AlgebraicClosure K) g0)
    (W := twModel (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8Neg)
      (iterateFrobenius (AlgebraicClosure K) 2 1))
    (fun u hu m hm => hWM (mul_mem (mul_mem hu (hMW hm)) (inv_mem hu))) (dVHom (τ := Tag.E8) hω3)
    (fun x y hxy => Multiplicative.toAdd.injective
      (dV_injective hω (hxy : dV ω x.toAdd = dV ω y.toAdd)))
    (fun x => hWM (dV_mem_twModel rootDiagUnit_mem_torusGroup_E8 e8Neg_smul hω3 x.toAdd))
    pow_three_multiplicative
    (fun s hs hs3 => by
      obtain ⟨u, hu, x, hux⟩ := exists_conj_dV_twModel
        (isAlgebraic_zmod_algebraicClosure_of_finite K 2)
        (monomialToralAt_three_of_block a2BlockToral_E8) e8Neg_smul hLang hω (hMW hs) hs3
      exact ⟨u, hu, Multiplicative.ofAdd x, hux⟩) t ht3
  exact ⟨E, htE, hE, hc.trans (card_multiplicative_three _)⟩

theorem exists_elemAbelian_E7_two (hK : Nat.card K = 2)
    (t : adjointGroup Tag.E7 K)
    (ht3 : t ^ 3 = 1) :
    ∃ E : Subgroup ↥(adjointGroup Tag.E7 K), t ∈ E ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ Tag.E7.rank := by
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
  have hLang : ∀ a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) →
      ∀ c ∈ toralCentralizer Tag.E7 (AlgebraicClosure K) a,
        ∃ z ∈ toralCentralizer Tag.E7 (AlgebraicClosure K) a, z⁻¹ * frobTwistGL Tag.E7
          (AlgebraicClosure K) 2 1 (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K)
            e7Neg) z = c := fun a ha3 c hc =>
    toral_centralizer_Lang_E7_three 2 (AlgebraicClosure K) (by norm_num) a ha3 1 le_rfl
      (canonicalRep_mem_adjointGroup _ _ _) (s := 2) (by norm_num)
      (canonicalRep_conj_rootDiagUnit_sq e7Neg_smul ha3) c hc
  obtain ⟨E, htE, hE, hc⟩ := exists_elemAbelian_mem_of_fusion
    (e7ModelEquiv K (AlgebraicClosure K) g0) hnorm (dVHom (τ := Tag.E7) hω3)
    (fun x y hxy => Multiplicative.toAdd.injective
      (dV_injective hω (hxy : dV ω x.toAdd = dV ω y.toAdd)))
    (fun x => h3 _ (dV_mem_twModel rootDiagUnit_mem_torusGroup_E7 e7Neg_smul hω3 x.toAdd)
      (dV_pow_three hω3 x.toAdd))
    pow_three_multiplicative
    (fun s hs hs3 => by
      obtain ⟨u, hu, x, hux⟩ := exists_conj_dV_twModel
        (isAlgebraic_zmod_algebraicClosure_of_finite K 2)
        (monomialToralAt_three_of_block a2BlockToral_E7) e7Neg_smul hLang hω (hMW hs) hs3
      exact ⟨u, hu, Multiplicative.ofAdd x, hux⟩) t ht3
  exact ⟨E, htE, hE, hc.trans (card_multiplicative_three _)⟩

end Twisted

section E6Two

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.TableBExc.E6Three


variable {K : Type} [Field K] [Finite K]

theorem exists_elemAbelian_E6_two (hK : Nat.card K = 2) (t : adjointGroup Tag.E6 K)
    (ht3 : t ^ 3 = 1) :
    ∃ E : Subgroup ↥(adjointGroup Tag.E6 K), t ∈ E ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 4 := by
  have : CharP K 2 := CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.charP_two_of_card_two hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set B := (torusE6Two (K := K) h2).range with hBdef
  have hB : CFSG.Open.IsElemAbelian 3 B := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, b, rfl⟩ ⟨_, c, rfl⟩
      apply Subtype.ext
      change torusE6Two h2 b * torusE6Two h2 c = torusE6Two h2 c * torusE6Two h2 b
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨b, rfl⟩
      rw [← map_pow, pow_three_multiplicative, map_one]
  have hBc : Nat.card B = 3 ^ 4 :=
    (Nat.card_congr (MonoidHom.ofInjective (torusE6Two_injective (K := K) h2)).toEquiv.symm).trans
      (card_multiplicative_three 4)
  have hu : ∀ i, uE6Two (K := K) i ∈ B := fun i => ⟨.ofAdd (Pi.single i 1), by
    rw [torusE6Two_single, CFSG.RankThree.CentralCover.zmodPowHom_apply, ZMod.val_one, pow_one]⟩
  by_cases ht1 : t = 1
  · exact ⟨B, ht1 ▸ one_mem B, hB, hBc⟩
  obtain ⟨c, hc⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6.exists_conj_eq_rep_E6_two hK t ht3 ht1
  have hcB : c * t * c⁻¹ ∈ B := by
    rcases hc with h | h | h <;> rw [h]
    · exact hu 0
    · exact mul_mem (hu 0) (hu 3)
    · exact mul_mem (mul_mem (hu 0) (hu 2)) (hu 3)
  refine ⟨B.map (MulAut.conj c⁻¹).toMonoidHom, ⟨c * t * c⁻¹, hcB, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group⟩, CFSG.SectionRank.isElemAbelian_map hB _, ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hBc]

end E6Two

section TwE6Two

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3


variable {K : Type} [Field K] [Finite K]

theorem exists_elemAbelian_twE6_two (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    (t : twistedE6RootGroup K σ) (ht3 : t ^ 3 = 1) :
    ∃ E : Subgroup ↥(twistedE6RootGroup K σ), t ∈ E ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 5 := by
  have hchar : CharP K 2 := charP_two_of_card_four hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨g0, hg0C, hg0⟩ := exists_twE6Two_lang K
  have hcL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨ω₀, hω₀⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [card_units_four hK])
  set ω : (AlgebraicClosure K)ˣ := Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ω₀
    with hωdef
  have hω : orderOf ω = 3 := by
    rw [hωdef, orderOf_injective (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom)
      (Units.map_injective (algebraMap K (AlgebraicClosure K)).injective), hω₀]
  have hω3 : ω ^ 3 = 1 := pow_three_of_orderOf hω
  set e := twE6TwoEquiv hK σ hσ hg0C hg0 with he
  have hFin : Finite ↥⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :=
    Finite.of_equiv _ e.toEquiv
  let D : Multiplicative (Fin 5 → ZMod 3) →* ModGL Tag.E6 (AlgebraicClosure K) :=
    MonoidHom.mk' (fun y => dV ω (subLin e6InnerVec y.toAdd)) (fun y z => by
      rw [toAdd_mul, subLin_add, dV_add hω3])
  have hD : Function.Injective D := fun y z h => Multiplicative.toAdd.injective
    (subLin_e6InnerVec_injective (dV_injective hω h))
  obtain ⟨E, htE, hE, hc⟩ := exists_elemAbelian_mem_of_fusion e
    (W := twE6TwoModel (AlgebraicClosure K)) (fun u hu m hm => twE6Two_conj_mem_commutator hu hm)
    D hD (fun y => dV_subLin_mem hω3 (twE6Two_dV_e6InnerVec_mem_commutator hω3) y.toAdd)
    pow_three_multiplicative
    (fun s hs hs3 => by
      obtain ⟨m, hm, y, hmy⟩ := twE6TwoFusion_holds K hK σ hσ g0 hg0C hg0 ω hω s hs hs3
      exact ⟨m, hm, Multiplicative.ofAdd y, hmy⟩) t ht3
  exact ⟨E, htE, hE, hc.trans (card_multiplicative_three 5)⟩

end TwE6Two

section Inner


theorem inner295At_F4_two
    (q : TauCeti.PrimePower) (hq2 : q.card = 2) (hv : (TauCeti.LieTypeIndex.F4 q).Valid) :
    Inputs295c.Inner295At ⟨.F4 q, hv⟩ := by
  obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
  exact inner295At_of_toral (k := CFSG.Blueprint.Chevalley.Tag.F4.rank) (by decide)
    ⟨_, _, ⟨eK⟩, exists_elemAbelian_F4_two (hK.trans hq2)⟩

theorem inner295At_E6_two
    (q : TauCeti.PrimePower) (hq2 : q.card = 2) (hv : (TauCeti.LieTypeIndex.E6 q).Valid) :
    Inputs295c.Inner295At ⟨.E6 q, hv⟩ := by
  obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  exact inner295At_of_toral (k := 4) le_rfl ⟨_, _, ⟨eK⟩, exists_elemAbelian_E6_two (hK.trans hq2)⟩

theorem inner295At_E7_two
    (q : TauCeti.PrimePower) (hq2 : q.card = 2) (hv : (TauCeti.LieTypeIndex.E7 q).Valid) :
    Inputs295c.Inner295At ⟨.E7 q, hv⟩ := by
  obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
  exact inner295At_of_toral (k := CFSG.Blueprint.Chevalley.Tag.E7.rank) (by decide)
    ⟨_, _, ⟨eK⟩, exists_elemAbelian_E7_two (hK.trans hq2)⟩

theorem inner295At_E8_two
    (q : TauCeti.PrimePower) (hq2 : q.card = 2) (hv : (TauCeti.LieTypeIndex.E8 q).Valid) :
    Inputs295c.Inner295At ⟨.E8 q, hv⟩ := by
  obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
  exact inner295At_of_toral (k := CFSG.Blueprint.Chevalley.Tag.E8.rank) (by decide)
    ⟨_, _, ⟨eK⟩, exists_elemAbelian_E8_two (hK.trans hq2)⟩

theorem inner295At_twistedE6_two
    (q : TauCeti.PrimePower) (hq2 : q.card = 2) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) :
    Inputs295c.Inner295At ⟨.twistedE6 q, hv⟩ := by
  obtain ⟨hp, he⟩ := Inputs295d.p_eq_two_of_card_two hq2
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  have hK4 : Nat.card K = 4 := by rw [hK, hp, he]; norm_num
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK4]; norm_num)
  have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by rw [hσ c, hp, he, pow_one]
  exact inner295At_of_toral (k := 5) (by norm_num)
    ⟨_, _, ⟨eK⟩, exists_elemAbelian_twE6_two hK4 σ hσ2⟩

end Inner

section TwE6Outer

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
  (isPSolvable_of_mulEquiv)


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem mem_fixSubgroup_iff_twE6Two (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K)
      (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0)
    {δ : MulAut (twistedE6RootGroup K σ)} {ĝ : ModGL TwistTag.E6.tag K}
    (hĝδ : ∀ c : twistedE6RootGroup K σ,
      ((δ c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = ĝ * c * ĝ⁻¹)
    {m : ModGL Tag.E6 (AlgebraicClosure K)}
    (hm : m = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ĝ * g0)
    (c : twistedE6RootGroup K σ) :
    c ∈ fixSubgroup δ ↔
      twE6TwoEquiv hK σ hσ hg0C hg0 c ∈
        (Subgroup.centralizer ({m} : Set (ModGL Tag.E6 (AlgebraicClosure K)))).subgroupOf
          (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
            Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) := by
  set ι := algebraMap K (AlgebraicClosure K) with hι
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff, mem_fixSubgroup]
  have h2 : ((twE6TwoEquiv hK σ hσ hg0C hg0 c : ↥(⁅twE6TwoModel (AlgebraicClosure K),
      twE6TwoModel (AlgebraicClosure K)⁆ : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))) :
        ModGL Tag.E6 (AlgebraicClosure K)) =
      g0⁻¹ * baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * g0 :=
    coe_twE6TwoEquiv hK σ hσ hg0C hg0 c
  have h1 : δ c = c ↔ (c : ModGL TwistTag.E6.tag K) * ĝ = ĝ * c := by
    constructor
    · intro h
      have h3 : ((δ c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = c :=
        congrArg Subtype.val h
      rw [hĝδ] at h3
      calc (c : ModGL TwistTag.E6.tag K) * ĝ = (ĝ * c * ĝ⁻¹) * ĝ := by rw [h3]
        _ = ĝ * c := by group
    · intro h
      apply Subtype.ext
      rw [hĝδ, ← h]
      group
  rw [h1]
  show (c : ModGL TwistTag.E6.tag K) * ĝ = ĝ * c ↔
    ((twE6TwoEquiv hK σ hσ hg0C hg0 c : ↥(⁅twE6TwoModel (AlgebraicClosure K),
      twE6TwoModel (AlgebraicClosure K)⁆ : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))) :
        ModGL Tag.E6 (AlgebraicClosure K)) * m = m * ((twE6TwoEquiv hK σ hσ hg0C hg0 c :
          ↥(⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
            Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))) : ModGL Tag.E6 (AlgebraicClosure K))
  rw [h2, hm]
  constructor
  · intro hc
    have h3 : baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * baseChangeGL ι ĝ =
        baseChangeGL ι ĝ * baseChangeGL ι (c : ModGL TwistTag.E6.tag K) := by
      rw [← map_mul, ← map_mul, hc]
    exact (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterInAux.conj_commute_iff g0
      _ _).2 h3
  · intro hc
    have h3 := (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterInAux.conj_commute_iff
      g0 _ _).1 hc
    rw [← map_mul, ← map_mul] at h3
    exact baseChangeGL_injective ι h3

theorem five_le_pRank_fixSubgroup_of_toral (hK : Nat.card K = 4) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2) {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K)
      (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0)
    {δ : MulAut (twistedE6RootGroup K σ)} {ĝ : ModGL TwistTag.E6.tag K}
    (hĝδ : ∀ c : twistedE6RootGroup K σ,
      ((δ c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = ĝ * c * ĝ⁻¹)
    {m : ModGL Tag.E6 (AlgebraicClosure K)}
    (hm : m = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ĝ * g0)
    {ω : (AlgebraicClosure K)ˣ} (hω : orderOf ω = 3)
    {m' : ModGL Tag.E6 (AlgebraicClosure K)} (hm'M : m' ∈ twE6TwoModel (AlgebraicClosure K))
    {x : Fin Tag.E6.rank → ZMod 3} (hm' : m' * m * m'⁻¹ = dV ω x) :
    5 ≤ CFSG.Open.pRank 3 (fixSubgroup δ) := by
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hω3 : ω ^ 3 = 1 := pow_three_of_orderOf hω
  set e := twE6TwoEquiv hK σ hσ hg0C hg0 with he
  have hDΓ : ∀ y : Fin 5 → ZMod 3, dV ω (subLin e6InnerVec y) ∈
      (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
        Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) := fun y => by
    haveI : Finite ↥(⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
        Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) := Finite.of_equiv _ e.toEquiv
    exact dV_subLin_mem hω3 (twE6Two_dV_e6InnerVec_mem_commutator hω3) y
  have hmem : ∀ y : Fin 5 → ZMod 3, m'⁻¹ * dV ω (subLin e6InnerVec y) * m' ∈
      (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
        Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) := fun y => by
    have := twE6Two_conj_mem_commutator (inv_mem hm'M) (hDΓ y)
    rwa [inv_inv] at this
  let ψ₀ : Multiplicative (Fin 5 → ZMod 3) →*
      ↥(⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
        Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) :=
    MonoidHom.mk' (fun y => ⟨m'⁻¹ * dV ω (subLin e6InnerVec y.toAdd) * m', hmem _⟩)
      (fun y z => Subtype.ext (by
        simp only [toAdd_mul, subLin_add, dV_add hω3, Subgroup.coe_mul]
        group))
  have hψ₀ : ∀ y, (ψ₀ y : ModGL Tag.E6 (AlgebraicClosure K)) =
      m'⁻¹ * dV ω (subLin e6InnerVec y.toAdd) * m' := fun y => rfl
  let ψ : Multiplicative (Fin 5 → ZMod 3) →* twistedE6RootGroup K σ :=
    e.symm.toMonoidHom.comp ψ₀
  have hψ : Function.Injective ψ := by
    intro y z h
    have h1 : ψ₀ y = ψ₀ z := e.symm.injective h
    have h2 : m'⁻¹ * dV ω (subLin e6InnerVec y.toAdd) * m' =
        m'⁻¹ * dV ω (subLin e6InnerVec z.toAdd) * m' := by rw [← hψ₀, ← hψ₀, h1]
    have h3 : dV ω (subLin e6InnerVec y.toAdd) = dV ω (subLin e6InnerVec z.toAdd) := by
      simpa using h2
    exact Multiplicative.toAdd.injective (subLin_e6InnerVec_injective (dV_injective hω h3))
  refine CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) (fun a b => mul_comm a b)
    pow_three_multiplicative (card_multiplicative_three 5) ψ hψ ?_
  rintro _ ⟨y, rfl⟩
  rw [mem_fixSubgroup_iff_twE6Two hK σ hσ hg0C hg0 hĝδ hm, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_singleton_iff]
  have he' : ((e (ψ y) : ↥(⁅twE6TwoModel (AlgebraicClosure K),
      twE6TwoModel (AlgebraicClosure K)⁆ : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))) :
        ModGL Tag.E6 (AlgebraicClosure K)) = m'⁻¹ * dV ω (subLin e6InnerVec y.toAdd) * m' := by
    change ((e (e.symm (ψ₀ y)) : ↥(⁅twE6TwoModel (AlgebraicClosure K),
      twE6TwoModel (AlgebraicClosure K)⁆ : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))) :
        ModGL Tag.E6 (AlgebraicClosure K)) = _
    rw [MulEquiv.apply_symm_apply, hψ₀]
  have hmx : m = m'⁻¹ * dV ω x * m' := by rw [← hm']; group
  rw [he', hmx, CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterInAux.conj_commute_iff,
    ← dV_add hω3, ← dV_add hω3, add_comm]

end TwE6Outer

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 in
@[expose] def Input29_5'LieRest4 :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
    ∀ g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K),
      g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) →
      twistHom TwistTag.E6 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 →
    ∀ m ∈ twE6TwoModel (AlgebraicClosure K),
      m ∉ (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
        Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) → m ^ 3 = 1 →
    ∀ y ∈ adjointGroup Tag.E6 (AlgebraicClosure K), ∀ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
      (∀ i, a i ^ 3 = 1) → rootChar a e6Omega3 = 1 → m = y * rootDiagUnit Tag.E6 a * y⁻¹ →
      ¬ CFSG.HallHigman.IsPSolvable 3
        ↥((Subgroup.centralizer ({m} : Set (ModGL Tag.E6 (AlgebraicClosure K)))).subgroupOf
          (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
            Subgroup (ModGL Tag.E6 (AlgebraicClosure K))))

section Reduction


open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
  (isPSolvable_of_mulEquiv)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 in
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterInAux
  (cocycle_mem_toralRootGroup_of_nonInner exists_model_conj_dV) in
theorem outer295At_twistedE6_two (hexo : Input29_5'LieRest4) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hq2 : q.card = 2) :
    Inputs295c.Outer295At ⟨.twistedE6 q, hv⟩ := by
  classical
  intro S _ _ _ _ ⟨e⟩ _ _ _ α hα hout
  obtain ⟨hp, he⟩ := Inputs295d.p_eq_two_of_card_two hq2
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  have hK4 : Nat.card K = 4 := by rw [hK, hp, he]; norm_num
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK4]; norm_num)
  have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by rw [hσ c, hp, he, pow_one]
  have hchar : CharP K 2 := charP_two_of_card_four hK4
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  set θ : S ≃* twistedE6RootGroup K σ := e.trans eK with hθ
  refine outerExcl295_of_congr θ α ?_
  set δ := MulAut.congr θ α with hδdef
  have hδ3 : δ ^ 3 = 1 := Inputs295d.congr_pow_three_eq_one θ hα
  have hδout : δ ∉ twistedE6Inn K σ := Inputs295d.congr_not_mem_range_conj θ hout
  obtain ⟨ĝ, hĝ, hĝC, hĝ3, hĝδ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterInAux.exists_ghat hK4 σ hσ2 hδ3
      hδout
  obtain ⟨g0, hg0C, hg0⟩ := exists_twE6Two_lang K
  have hcL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  set ι := algebraMap K (AlgebraicClosure K) with hι
  set eΓ := twE6TwoEquiv hK4 σ hσ2 hg0C hg0 with heΓ
  set m : ModGL Tag.E6 (AlgebraicClosure K) := g0⁻¹ * baseChangeGL ι ĝ * g0 with hm
  have hmM : m ∈ twE6TwoModel (AlgebraicClosure K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterInAux.conj_ghat_mem_model hK4 σ
      hσ2 hg0C hg0 hĝ
  have hmΓ : m ∉ (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
      Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) := by
    intro hmΓ
    obtain ⟨c, hc⟩ := eΓ.surjective ⟨m, hmΓ⟩
    have h1 : ((eΓ c : ↥(⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
        Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))) : ModGL Tag.E6 (AlgebraicClosure K)) = m :=
      congrArg Subtype.val hc
    rw [coe_twE6TwoEquiv] at h1
    have h2 : baseChangeGL ι (c : ModGL TwistTag.E6.tag K) = baseChangeGL ι ĝ := by
      have := congrArg (fun y => g0 * y * g0⁻¹) h1
      simpa [hm, mul_assoc] using this
    exact hĝC (by
      have := baseChangeGL_injective ι h2
      rw [← this]
      exact c.2)
  have hm3 : m ^ 3 = 1 := by
    have h2 := conj_pow (a := g0⁻¹) (b := baseChangeGL ι ĝ) (i := 3)
    have h3 : (g0⁻¹ * baseChangeGL ι ĝ * g0) ^ 3 = g0⁻¹ * baseChangeGL ι ĝ ^ 3 * g0 := by
      simpa using h2
    have h4 : (g0⁻¹ * baseChangeGL ι ĝ * g0) ^ 3 = 1 := by
      rw [h3, ← map_pow, hĝ3, map_one]
      group
    exact h4
  obtain ⟨y, hyG, a, ha3, hsy⟩ := exists_conj_toral_E6_three hmM.1 hm3
  by_cases hnon : rootChar a e6Omega3 = 1
  ·
    have hns := hexo K hK4 σ hσ2 g0 hg0C hg0 m hmM hmΓ hm3 y hyG a ha3 hnon hsy
    refine Or.inr (Or.inr fun hs => hns ?_)
    have hmap : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δ).map eΓ.toMonoidHom =
        (Subgroup.centralizer ({m} : Set (ModGL Tag.E6 (AlgebraicClosure K)))).subgroupOf
          (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
            Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) := by
      ext z
      obtain ⟨c, rfl⟩ := eΓ.surjective z
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
      exact mem_fixSubgroup_iff_twE6Two hK4 σ hσ2 hg0C hg0 hĝδ hm c
    rw [← hmap]
    exact isPSolvable_of_mulEquiv
      ((CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δ).equivMapOfInjective _
        eΓ.injective) hs
  ·
    obtain ⟨ω₀, hω₀⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [card_units_four hK4])
    set ω : (AlgebraicClosure K)ˣ := Units.map ι.toMonoidHom ω₀ with hωdef
    have hω : orderOf ω = 3 := by
      rw [hωdef, orderOf_injective (Units.map ι.toMonoidHom) (Units.map_injective ι.injective),
        hω₀]
    have hprim : IsPrimitiveRoot (ω : AlgebraicClosure K) 3 :=
      IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hω)
    have hapow : ∀ i, ∃ n : ℕ, a i = ω ^ n := fun i => by
      obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (a i : AlgebraicClosure K))
        (by have := congrArg Units.val (ha3 i); simpa using this)
      exact ⟨n, Units.ext (by simpa using hn.symm)⟩
    choose mm hmm using hapow
    have hax : a = torV ω (fun i => (mm i : ZMod 3)) := by
      funext i
      rw [torV, ZMod.val_natCast, hmm i]
      have := pow_mod_orderOf ω (mm i)
      rw [hω] at this
      exact this.symm
    have hcoc := cocycle_mem_toralRootGroup_of_nonInner hmM hyG ha3 hsy hnon
    obtain ⟨m', hm'M, hm'⟩ := exists_model_conj_dV hyG hsy hcoc hax
    exact Or.inr (Or.inl ((by norm_num : 3 ≤ 5).trans
      (five_le_pRank_fixSubgroup_of_toral hK4 σ hσ2 hg0C hg0 hĝδ hm hω hm'M hm')))

theorem input29_5'LieRest3_of_rest4 (h : Input29_5'LieRest4) : Inputs295d.Input29_5'LieRest3 :=
  ⟨fun q hv hp3 hq2 => outer295At_D4 q hv hp3 hq2,
    fun q hv hq2 => outer295At_twistedE6_two h q hv hq2,
    fun _ hv hq2 => (at_twistedA_three_two hv hq2).2,
    fun q hq2 => ⟨inner295At_F4_two q hq2, inner295At_E6_two q hq2,
      inner295At_twistedE6_two q hq2, inner295At_E7_two q hq2, inner295At_E8_two q hq2⟩⟩

end Reduction

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295e
