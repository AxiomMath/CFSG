module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverE6RankMain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover

public section

namespace CFSG.HardMathSupport.Lang.AlphaThree

section Orbits

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {t : TwistTag} {K : Type} [Field K]

theorem graphFixedRootGroup_le_of_orbitGroups
    (σ : K →+* K) (hσ : Function.Surjective σ) (G : Subgroup (ModGL t.tag K))
    (hOG : ∀ O ∈ t.diagramRootOrbits, ∀ u ∈ rootSpan t.tag K (O : Set (Fin t.tag.rank → ℤ)) ⊓
      twistedFixedGroup t K σ, u ∈ G) :
    graphFixedRootGroup t K σ ≤ G := by
  obtain ⟨k, O, hO, hrange⟩ := exists_ordering_posOrbits t
  have hposS : ∀ α ∈ {α | IsRoot t.tag α ∧ 0 < height α}, IsRoot t.tag α ∧ 0 < height α :=
    fun α hα => hα
  have hposρ : ∀ α ∈ {α | IsRoot t.tag α ∧ 0 < height α},
      permLattice t.perm α ∈ {α | IsRoot t.tag α ∧ 0 < height α} := fun α hα => by
    rw [← image_permLattice_posRoots t]
    exact ⟨α, hα, rfl⟩
  have hposcl : ∀ α ∈ {α | IsRoot t.tag α ∧ 0 < height α},
      ∀ β ∈ {α | IsRoot t.tag α ∧ 0 < height α}, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot t.tag (a • α + b • β) → a • α + b • β ∈ {α | IsRoot t.tag α ∧ 0 < height α} :=
    fun α hα β hβ a b ha hb hr => by
      refine ⟨hr, ?_⟩
      rw [height_nsmul_add_nsmul]
      have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith [hα.2, hβ.2]
  have hbij := bijOn_prod_graphFixed (K := K) hσ hposS hposρ hposcl O hO hrange
  have hOj : ∀ j, O j ∈ t.diagramRootOrbits := fun j => by
    have h : O j ∈ Set.range O := Set.mem_range_self j
    rw [hrange] at h
    exact h.1
  have hplus : graphFixedPosUnipotent t K σ ≤ G := fun g hg => by
    obtain ⟨u, -, rfl⟩ := hbij.surjOn hg
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    exact hOG _ (hOj j) _ (u j).2
  refine sup_le hplus fun g hg => ?_
  obtain ⟨w₀, hw₀, h₀⟩ := t.exists_reversesSigns_mem_relWeylTwist
  set n := canonicalRep (coxeterSystem t.tag) K w₀
  have hn : n ∈ twistedFixedGroup t K σ :=
    canonicalRep_mem_twistedFixedGroup t K σ ((mem_relWeylTwist t).1 hw₀)
  obtain ⟨hgU, hgΓ⟩ := Subgroup.mem_inf.1 hg
  have hmap := (canonical_weyl_root_transport t.tag K).1 w₀ {α | IsRoot t.tag α ∧ 0 < height α}
    fun α hα => hα.1
  rw [image_smul_posRoots_of_reversesSigns h₀] at hmap
  have hgU' : g ∈ rootSpan t.tag K {α | IsRoot t.tag α ∧ height α < 0} := hgU
  rw [← hmap] at hgU'
  obtain ⟨g', hg', rfl⟩ := hgU'
  have hg'Γ : g' ∈ twistedFixedGroup t K σ := by
    have e : g' = n⁻¹ * (MulAut.conj n).toMonoidHom g' * n := by simp [mul_assoc]
    rw [e]
    exact mul_mem (mul_mem (inv_mem hn) hgΓ) hn
  obtain ⟨u, -, rfl⟩ := hbij.surjOn (Subgroup.mem_inf.2 ⟨hg', hg'Γ⟩)
  rw [map_list_prod]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
  obtain ⟨α, hα, hαO⟩ := hOj j
  have hroots : ∀ β ∈ (O j : Set (Fin t.tag.rank → ℤ)), IsRoot t.tag β := fun β hβ => by
    rw [← hαO] at hβ
    exact t.isRoot_of_mem_diagramOrbit hα hβ
  have hconj := (canonical_weyl_root_transport t.tag K).1 w₀ _ hroots
  have hmem : (MulAut.conj n).toMonoidHom (u j : ModGL t.tag K) ∈
      rootSpan t.tag K ((fun β => w₀ • β) '' (O j : Set (Fin t.tag.rank → ℤ))) := by
    rw [← hconj]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.1 (u j).2).1
  refine hOG (t.diagramOrbit (w₀ • α)) ⟨_, IsRoot.smul hα w₀, rfl⟩ _
    (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
  · rw [t.diagramOrbit_smul hw₀, Finset.coe_image, hαO]
    exact hmem
  · exact mul_mem (mul_mem hn (Subgroup.mem_inf.1 (u j).2).2) (inv_mem hn)

end Orbits

namespace TwistedE6Gen

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLAY CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.AGLEmbedding.KFactProofs.CoverE6


theorem exists_inverter_data_twisted_mem {K k : Type} [Field K] [Field k] [Finite k] (ι : k →+* K)
    (σ : K →+* K) (hσ : ∀ c, σ (ι c) = ι c)
    (hcl : ⁅twistedFixedGroup TwistTag.E6 K σ, twistedFixedGroup TwistTag.E6 K σ⁆ =
      graphFixedRootGroup TwistTag.E6 K σ) (h3 : (3 : k) ≠ 0) :
    ∃ h w : Fin 4 → ↥(graphFixedRootGroup TwistTag.E6 K σ), (∀ i j, Commute (h i) (h j)) ∧
      (∀ i, orderOf (h i) = 3) ∧ (∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹) ∧
      (∀ i j, i ≠ j → w i * h j * (w i)⁻¹ = h j) ∧
      ∀ i, ((h i : ↥(graphFixedRootGroup TwistTag.E6 K σ)) : ModGL TwistTag.E6.tag K) ∈
        rootSubgroup TwistTag.E6.tag K (fourRoots i) ⊔
          rootSubgroup TwistTag.E6.tag K (-fourRoots i) := by
  obtain ⟨e, u, he1, he3, heu⟩ := exists_order_three_inverter k h3
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
  let ψ' : Fin 4 → Matrix.SpecialLinearGroup (Fin 2) k →* ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
    fun i => (ψ i).codRestrict _ (hψC i)
  have hψ' : ∀ i A, (ψ' i A).1 = ψ i A := fun i A => rfl
  have hinj' : ∀ i, Function.Injective (ψ' i) := fun i A B h =>
    hinj i (by simpa only [hψ'] using congrArg Subtype.val h)
  have hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ' i A) (ψ' j B) := fun i j hij A B =>
    Subtype.ext (commute_of_mem_rootPair K hij (hψQ i A) (hψQ j B)).eq
  refine ⟨fun i => ψ' i e, fun i => ψ' i u, fun i j => ?_, fun i => ?_, fun i => ?_,
    fun i j hij => ?_, fun i => hψQ i e⟩
  · by_cases hij : i = j
    · rw [hij]
    · exact hcomm i j hij e e
  · exact orderOf_eq_prime (by rw [← map_pow, he3, map_one])
      fun h => he1 (hinj' i (h.trans (map_one _).symm))
  · show ψ' i u * ψ' i e * (ψ' i u)⁻¹ = (ψ' i e)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, heu, map_inv]
  · rw [mul_inv_eq_iff_eq_mul]
    exact (hcomm i j hij u e).eq


theorem liftableNormalizerGen_graphFixed_of_gen {K k : Type} [Field K] [Field k] [Finite k]
    (ι : k →+* K) (σ : K →+* K) (hσ : ∀ c, σ (ι c) = ι c)
    (hcl : ⁅twistedFixedGroup TwistTag.E6 K σ, twistedFixedGroup TwistTag.E6 K σ⁆ =
      graphFixedRootGroup TwistTag.E6 K σ) (h3 : (3 : k) ≠ 0)
    (hgen : ∀ h : Fin 4 → ↥(graphFixedRootGroup TwistTag.E6 K σ),
      (∀ i, ((h i : ↥(graphFixedRootGroup TwistTag.E6 K σ)) : ModGL TwistTag.E6.tag K) ∈
        rootSubgroup TwistTag.E6.tag K (fourRoots i) ⊔
          rootSubgroup TwistTag.E6.tag K (-fourRoots i)) →
      Subgroup.closure (CFSG.AGLEmbedding.pairCentralizing h) = ⊤) :
    CFSG.AGLEmbedding.LiftableNormalizerGen ↥(graphFixedRootGroup TwistTag.E6 K σ) := by
  obtain ⟨h, w, hcomm, hord, hinv, hfix, hh⟩ := exists_inverter_data_twisted_mem ι σ hσ hcl h3
  refine CFSG.AGLEmbedding.liftableNormalizerGen_of_inverters h w hcomm hord hinv hfix ?_
  exact eq_top_iff.2 ((hgen h hh).symm.le.trans (Subgroup.closure_mono Set.subset_union_left))

end TwistedE6Gen

section Carrier

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem liftableNormalizerGen_twistedE6_of_graphFixed (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid)
    (hC : ∀ (K : Type) [Field K] [Finite K] (σ : K →+* K), Nat.card K = q.card ^ 2 →
      (∀ c, σ c = c ^ q.card) →
        CFSG.AGLEmbedding.LiftableNormalizerGen ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
    CFSG.AGLEmbedding.LiftableNormalizerGen
      (TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p (q.exponent * 2)) = q.card ^ 2 := by
    rw [GaloisField.card q.p (q.exponent * 2) (by have := q.exponent_pos; omega),
      TauCeti.PrimePower.card_def, pow_mul]
  have hσ : ∀ c : GaloisField q.p (q.exponent * 2),
      iterateFrobenius (GaloisField q.p (q.exponent * 2)) q.p q.exponent c = c ^ q.card :=
    fun c => by rw [iterateFrobenius_def, TauCeti.PrimePower.card_def]
  obtain ⟨br⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).twistedE6 q hv
    (GaloisField q.p (q.exponent * 2)) hcard
    (iterateFrobenius (GaloisField q.p (q.exponent * 2)) q.p q.exponent) hσ
  have hK : Nat.card (GaloisField q.p (q.exponent * 2)) =
      (q.p ^ q.exponent) ^ TwistTag.E6.order := by
    rw [hcard, TauCeti.PrimePower.card_def]
    rfl
  have hσ' : ∀ c : GaloisField q.p (q.exponent * 2),
      iterateFrobenius (GaloisField q.p (q.exponent * 2)) q.p q.exponent c =
        c ^ (q.p ^ q.exponent) := fun c => by rw [hσ, TauCeti.PrimePower.card_def]
  have hcl := (finite_fixed_root_group_perfect TwistTag.E6 q.prime_p q.exponent_pos
    (GaloisField q.p (q.exponent * 2)) hK _ hσ').2.2.1
  have hsurj : Function.Surjective
      (iterateFrobenius (GaloisField q.p (q.exponent * 2)) q.p q.exponent) :=
    Finite.surjective_of_injective (RingHom.injective _)
  have hZD : Subgroup.center ↥⁅twistedFixedGroup TwistTag.E6 (GaloisField q.p (q.exponent * 2))
      (iterateFrobenius (GaloisField q.p (q.exponent * 2)) q.p q.exponent),
      twistedFixedGroup TwistTag.E6 (GaloisField q.p (q.exponent * 2))
        (iterateFrobenius (GaloisField q.p (q.exponent * 2)) q.p q.exponent)⁆ = ⊥ := by
    rw [hcl]
    exact center_graphFixedRootGroup_eq_bot hsurj
  exact ((hC _ _ hcard hσ).of_mulEquiv ((MulEquiv.subgroupCongr hcl).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hZD).trans QuotientGroup.quotientBot).symm)).of_mulEquiv br

theorem liftableNormalizerGen_twistedE6_of_gen (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hq3 : 3 ∣ q.card + 1)
    (hgen : ∀ (K : Type) [Field K] [Finite K] (σ : K →+* K), Nat.card K = q.card ^ 2 →
      (∀ c, σ c = c ^ q.card) → ∀ h : Fin 4 → ↥(graphFixedRootGroup TwistTag.E6 K σ),
        (∀ i, ((h i : ↥(graphFixedRootGroup TwistTag.E6 K σ)) : ModGL TwistTag.E6.tag K) ∈
          rootSubgroup TwistTag.E6.tag K (CFSG.AGLEmbedding.KFactProofs.CoverE6.fourRoots i) ⊔
            rootSubgroup TwistTag.E6.tag K
              (-CFSG.AGLEmbedding.KFactProofs.CoverE6.fourRoots i)) →
        Subgroup.closure (CFSG.AGLEmbedding.pairCentralizing h) = ⊤) :
    CFSG.AGLEmbedding.LiftableNormalizerGen
      (TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) := by
  refine liftableNormalizerGen_twistedE6_of_graphFixed q hv fun K _ _ σ hK hσ => ?_
  have hp3 : q.p ≠ 3 := by
    intro h
    have h2 : 3 ∣ q.card := by
      rw [TauCeti.PrimePower.card_def, h]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    omega
  have hK' : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.E6.order := by
    rw [hK, TauCeti.PrimePower.card_def]
    rfl
  have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := fun c => by
    rw [hσ, TauCeti.PrimePower.card_def]
  have hcl := (finite_fixed_root_group_perfect TwistTag.E6 q.prime_p q.exponent_pos K hK' σ
    hσ').2.2.1
  have h3 : (3 : K) ≠ 0 :=
    CFSG.AGLEmbedding.KFactProofs.CoverThree.three_ne_zero_of_card q.prime_p
      (e := q.exponent * 2) (by have := q.exponent_pos; omega)
      (by rw [hK, TauCeti.PrimePower.card_def, ← pow_mul]) hp3
  let k := RingHom.eqLocusField σ (RingHom.id K)
  have h3k : (3 : ↥k) ≠ 0 := fun h =>
    h3 (by have := congrArg k.subtype h; rwa [map_ofNat, map_zero] at this)
  exact TwistedE6Gen.liftableNormalizerGen_graphFixed_of_gen k.subtype σ
    (fun c => RingHom.mem_eqLocusField.1 c.2) hcl h3k (hgen K σ hK hσ)

end Carrier

end CFSG.HardMathSupport.Lang.AlphaThree
