module

public import CFSG.LieType.SeitzGeneration.HyperExExcV2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverE6RankTw
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTwistedE6
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6ModelCover

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge
  CFSG.Open CFSG.AGLEmbedding TauCeti CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KLAY
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.AGLEmbedding.KFactProofs.CoverE6

theorem card_fixSubfield_sq {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card (fixSubfield σ) = ℓ ^ f := by
  have hK2 : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨fr, hfr, hord, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ (by omega : 1 ≤ 2 * f) hK2
  have hσfr : σ = fr ^ f := RingEquiv.ext fun c => by
    rw [hσ, ringAut_pow_apply_of_frobenius hfr f c]
  have hσo : orderOf σ = 2 := by
    rw [hσfr, orderOf_pow_of_dvd (by omega) (by rw [hord]; exact Dvd.intro_left 2 rfl), hord,
      Nat.mul_div_cancel _ (by omega)]
  obtain ⟨-, hσcard⟩ := SteinbergBT.card_fixSubfield hℓ (by omega : 1 ≤ 2 * f) hK2 σ
  rw [hσo, Nat.mul_div_cancel_left _ (by norm_num)] at hσcard
  exact hσcard

section Four


theorem exists_four_sl2_twistedE6 {K k : Type} [Field K] [Field k] (ι : k →+* K)
    (σ : K →+* K) (hσ : ∀ c, σ (ι c) = ι c)
    (hcl : ⁅twistedFixedGroup TwistTag.E6 K σ, twistedFixedGroup TwistTag.E6 K σ⁆ =
      graphFixedRootGroup TwistTag.E6 K σ) :
    ∃ ψ : Fin 4 → SL2 k →* ↥(graphFixedRootGroup TwistTag.E6 K σ),
      (∀ i, Function.Injective (ψ i)) ∧ ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B) := by
  have hall : ∀ β ∈ (Finset.univ.image fourRoots : Finset (Fin TwistTag.E6.tag.rank → ℤ)),
      β ∈ fixedDegOneRoots := by decide +kernel
  have hmem : ∀ i, fourRoots i ∈ fixedDegOneRoots := fun i =>
    hall _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  choose w hwT hwβ using fun i => exists_tailWeyl_smul_single (hmem i)
  have hnΓ : ∀ i, canonicalRep (coxeterSystem TwistTag.E6.tag) K (w i) ∈
      twistedFixedGroup TwistTag.E6 K σ := fun i =>
    canonicalRep_mem_twistedFixedGroup TwistTag.E6 K σ (weylTwist_eq_of_mem_tailWeyl (hwT i))
  have ha : TwistTag.E6.perm (e6Idx 1) = e6Idx 1 := by decide
  let ψ : Fin 4 → Matrix.SpecialLinearGroup (Fin 2) k →* ModGL TwistTag.E6.tag K := fun i =>
    (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K (w i))).toMonoidHom.comp
      ((simpleRootSL2 TwistTag.E6.tag K (e6Idx 1)).comp (Matrix.SpecialLinearGroup.map ι))
  have hψ : ∀ i A, ψ i A = canonicalRep (coxeterSystem TwistTag.E6.tag) K (w i) *
      simpleRootSL2 TwistTag.E6.tag K (e6Idx 1) (Matrix.SpecialLinearGroup.map ι A) *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) K (w i))⁻¹ := fun i A => rfl
  have hψC : ∀ i A, ψ i A ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    intro i A
    have h0 := simpleRootSL2_map_mem ι σ hσ ha A
    rw [← hcl] at h0 ⊢
    rw [hψ]
    exact conj_mem_derived σ (hnΓ i) h0
  have hψQ : ∀ i A, ψ i A ∈ rootSubgroup TwistTag.E6.tag K (fourRoots i) ⊔
      rootSubgroup TwistTag.E6.tag K (-fourRoots i) := by
    intro i A
    have key := map_conj_canonicalRep_closure_xUnit_yUnit (τ := TwistTag.E6.tag) (K := K)
      (hwβ i)
    refine key.le (Subgroup.mem_map.2 ⟨simpleRootSL2 TwistTag.E6.tag K (e6Idx 1)
      (Matrix.SpecialLinearGroup.map ι A), ?_, (hψ i A).symm⟩)
    rw [← range_simpleRootSL2]
    exact MonoidHom.mem_range.2 ⟨_, rfl⟩
  have hinj : ∀ i, Function.Injective (ψ i) := by
    intro i A B hAB
    have hsimple : Function.Injective (simpleRootSL2 TwistTag.E6.tag K (e6Idx 1)) := by
      have := rootSL2_injective_of_field (τ := TwistTag.E6.tag) (K := K) (Pi.single (e6Idx 1) 1)
      rwa [rootSL2_single (τ := TwistTag.E6.tag) (K := K) (e6Idx 1)] at this
    exact map_injective_SL2 ι (hsimple ((MulAut.conj _).injective hAB))
  let ψ' : Fin 4 → SL2 k →* ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
    fun i => (ψ i).codRestrict _ (hψC i)
  have hψ' : ∀ i A, (ψ' i A).1 = ψ i A := fun i A => rfl
  refine ⟨ψ', fun i A B h => hinj i (by simpa only [hψ'] using congrArg Subtype.val h),
    fun i j hij A B => Subtype.ext ?_⟩
  exact (commute_of_mem_rootPair K hij (hψQ i A) (hψQ j B)).eq

end Four

section Cube


theorem exists_cube_cat_twistedE6 (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q.card ^ 2 - 1) :
    ∃ E : Subgroup (Cat ⟨.twistedE6 q, hv⟩), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      NormalizesRSub ⟨.twistedE6 q, hv⟩ E := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero _ q.prime_p.ne_zero))
  have hσ' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => hσ x
  have hcl := (finite_fixed_root_group_perfect TwistTag.E6 q.prime_p q.exponent_pos K hK
    σ.toRingHom hσ').2.2.1
  obtain ⟨ψ, hinj, hcomm⟩ := exists_four_sl2_twistedE6 (fixSubfield σ).subtype σ.toRingHom
    (fun c => c.2) hcl
  have hk : Nat.card (fixSubfield σ) = q.card := by
    rw [card_fixSubfield_sq q.prime_p q.exponent_pos hK σ hσ, PrimePower.card_def]
  have : Finite (fixSubfield σ) := Nat.finite_of_card_ne_zero (by
    rw [hk, PrimePower.card_def]
    exact pow_ne_zero _ q.prime_p.ne_zero)
  obtain ⟨E, hE, hc, hEc⟩ := exists_cube_of_four_sl2 hp hp2 (by rwa [hk]) ψ hinj hcomm
  let f : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →* Cat ⟨.twistedE6 q, hv⟩ :=
    e.symm.toMonoidHom
  refine ⟨E.map f, CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE f, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, hc]
  · have := Fintype.ofFinite K
    have hKc : CharP K q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2) (by
      rw [← Nat.card_eq_fintype_card, hK, pow_mul])
    have : CharP (fixSubfield σ) (LieTypeIndex.twistedE6 q).characteristic := by
      rw [LieTypeIndex.characteristic_twistedE6]
      exact ⟨fun x => by
        rw [← CharP.cast_eq_zero_iff K q.p x, ← map_natCast (fixSubfield σ).subtype x,
          map_eq_zero_iff _ Subtype.val_injective]⟩
    refine normalizesRSub_of_commute_sl2 (f.comp (ψ 3)) (e.symm.injective.comp (hinj 3)) ?_
    rintro _ ⟨x, hx, rfl⟩ A
    exact (hEc x hx A).map f

@[expose] def ExcCubeHighTw : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) (p : ℕ), p.Prime → p ≠ 2 → p ≠ q.p →
    ¬ P1ThreeLieList p ⟨.twistedE6 q, hv⟩ → ¬ p ∣ q.card ^ 2 - 1 →
    3 ≤ degCountTw (orderOf ((q.card : ℕ) : ZMod p)) →
    (∃ E₀ : Subgroup (Cat ⟨.twistedE6 q, hv⟩), IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 3) →
    ∃ E : Subgroup (Cat ⟨.twistedE6 q, hv⟩), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      (NormalizesRSub ⟨.twistedE6 q, hv⟩ E ∨ HyperGen p ⊤ E)

theorem excCubeFor_twistedE6_of_high (hH : ExcCubeHighTw) : ExcCubeFor IsTwistedE6Index := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hl ⟨q, rfl⟩ ⟨E₀, hE₀, hc₀⟩
  have hpq' : p ≠ q.p := by simpa using hpd
  by_cases hpq : p ∣ q.card ^ 2 - 1
  · obtain ⟨E, hE, hc, hR⟩ := exists_cube_cat_twistedE6 q hv hp hp2 hpq
    exact ⟨E, hE, hc, Or.inl hR⟩
  rcases (by omega : degCountTw (orderOf ((q.card : ℕ) : ZMod p)) ≤ 1 ∨
      degCountTw (orderOf ((q.card : ℕ) : ZMod p)) = 2 ∨
      3 ≤ degCountTw (orderOf ((q.card : ℕ) : ZMod p))) with h | h | h
  · exact (false_of_rankLE2_of_card hp (rankLE1_cat_twistedE6 q hv hp hpq' h).rankLE2 hE₀
      hc₀).elim
  · exact (false_of_rankLE2_of_card hp
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_cat_twistedE6 q hv hp h) hE₀ hc₀).elim
  · exact hH q hv p hp hp2 hpq' hl hpq h ⟨E₀, hE₀, hc₀⟩

end Cube

structure ExcCubeResidualsV3 : Prop where
  e6High : ExcCubeHigh .E6 LieTypeIndex.E6
  e7High : ExcCubeHigh .E7 LieTypeIndex.E7
  e8High : ExcCubeHigh .E8 LieTypeIndex.E8
  twE6High : ExcCubeHighTw


theorem ExcCubeResidualsV3.toV2 (h : ExcCubeResidualsV3) : ExcCubeResidualsV2 where
  e6High := h.e6High
  e7High := h.e7High
  e8High := h.e8High
  twistedE6 := excCubeFor_twistedE6_of_high h.twE6High

end CFSG.LieType.SeitzGeneration
