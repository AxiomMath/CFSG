module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverE6RankUntw
public import CFSG.LieType.Chevalley.E6GraphHighestRootData
public import CFSG.LieType.Chevalley.OddRootPairSL2
public import CFSG.RankThree.PartOne.KLAY.RootSL2

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLAY CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Chevalley.E6GraphHighestRoot

theorem conj_mem_derived {K : Type} [Field K] (σ : K →+* K) {n g : ModGL TwistTag.E6.tag K}
    (hn : n ∈ twistedFixedGroup TwistTag.E6 K σ)
    (hg : g ∈ ⁅twistedFixedGroup TwistTag.E6 K σ, twistedFixedGroup TwistTag.E6 K σ⁆) :
    n * g * n⁻¹ ∈ ⁅twistedFixedGroup TwistTag.E6 K σ, twistedFixedGroup TwistTag.E6 K σ⁆ := by
  have hmap : (twistedFixedGroup TwistTag.E6 K σ).map (MulAut.conj n).toMonoidHom =
      twistedFixedGroup TwistTag.E6 K σ := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.2 fun x hx => ?_) fun x hx => ?_
    · exact mul_mem (mul_mem hn hx) (inv_mem hn)
    · exact ⟨n⁻¹ * x * n, mul_mem (mul_mem (inv_mem hn) hx) hn, by simp [mul_assoc]⟩
  have := Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hg
  rwa [Subgroup.map_commutator, hmap] at this

theorem simpleRootSL2_map_mem {K k : Type} [Field K] [Field k] (ι : k →+* K) (σ : K →+* K)
    (hσ : ∀ c, σ (ι c) = ι c) {i : Fin TwistTag.E6.tag.rank} (hi : TwistTag.E6.perm i = i)
    (A : Matrix.SpecialLinearGroup (Fin 2) k) :
    simpleRootSL2 TwistTag.E6.tag K i (Matrix.SpecialLinearGroup.map ι A) ∈
      graphFixedRootGroup TwistTag.E6 K σ := by
  have hx : ∀ c : k, xUnit TwistTag.E6.tag K i (ι c) ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    intro c
    refine graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ ?_
    refine Subgroup.mem_inf.2 ⟨xUnit_mem_posUnipotent i _, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
    · exact xUnit_mem_adjointGroup i _
    · show twistHom TwistTag.E6 K σ _ = _
      rw [twistHom_xUnit, hi, hσ]
      rfl
  have hy : ∀ c : k, yUnit TwistTag.E6.tag K i (ι c) ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    intro c
    refine graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _ ?_
    refine Subgroup.mem_inf.2 ⟨yUnit_mem_negUnipotent i _, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
    · exact yUnit_mem_adjointGroup i _
    · show twistHom TwistTag.E6 K σ _ = _
      rw [twistHom_yUnit, hi, hσ]
      rfl
  have hle : Subgroup.closure (Set.range (sl2Upper k) ∪ Set.range (sl2Lower k)) ≤
      (graphFixedRootGroup TwistTag.E6 K σ).comap
        ((simpleRootSL2 TwistTag.E6.tag K i).comp (Matrix.SpecialLinearGroup.map ι)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply]
      change simpleRootSL2 TwistTag.E6.tag K i (Matrix.SpecialLinearGroup.map ι (uSL c)) ∈ _
      rw [map_uSL, simpleRootSL2_uSL]
      exact hx c
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply]
      change simpleRootSL2 TwistTag.E6.tag K i (Matrix.SpecialLinearGroup.map ι (vSL c)) ∈ _
      rw [map_vSL, simpleRootSL2_vSL]
      exact hy c
  have hA : A ∈ Subgroup.closure (Set.range (sl2Upper k) ∪ Set.range (sl2Lower k)) := by
    rw [sl2_closure_upper_lower]
    trivial
  exact hle hA

theorem weylTwist_eq_of_mem_tailWeyl {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ tailWeyl) :
    weylTwist TwistTag.E6 w = w := by
  have hgen : ∀ b, weylTwist TwistTag.E6 (tailGen b) = tailGen b := by
    intro b
    fin_cases b
    · have h := weylTwist_wordProd_eq (t := TwistTag.E6) (ω := [e6Idx 3]) (by decide)
      rw [CoxeterSystem.wordProd_singleton] at h
      exact h
    · have h := weylTwist_wordProd_eq (t := TwistTag.E6) (ω := [e6Idx 0, e6Idx 5]) (by decide)
      rw [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_singleton] at h
      exact h
    · have h := weylTwist_wordProd_eq (t := TwistTag.E6) (ω := [e6Idx 2, e6Idx 4]) (by decide)
      rw [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_singleton] at h
      exact h
  have hle : tailWeyl ≤ MonoidHom.eqLocus (weylTwist TwistTag.E6).toMonoidHom (MonoidHom.id _) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨b, rfl⟩
    exact hgen b
  exact hle hw

theorem exists_inverter_data_twisted {K k : Type} [Field K] [Field k] [Finite k] (ι : k →+* K)
    (σ : K →+* K) (hσ : ∀ c, σ (ι c) = ι c)
    (hcl : ⁅twistedFixedGroup TwistTag.E6 K σ, twistedFixedGroup TwistTag.E6 K σ⁆ =
      graphFixedRootGroup TwistTag.E6 K σ) (h3 : (3 : k) ≠ 0) :
    ∃ h w : Fin 4 → ↥(graphFixedRootGroup TwistTag.E6 K σ), (∀ i j, Commute (h i) (h j)) ∧
      (∀ i, orderOf (h i) = 3) ∧ (∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹) ∧
      (∀ i j, i ≠ j → w i * h j * (w i)⁻¹ = h j) := by
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
    fun i j hij => ?_⟩
  · by_cases hij : i = j
    · rw [hij]
    · exact hcomm i j hij e e
  · exact orderOf_eq_prime (by rw [← map_pow, he3, map_one])
      fun h => he1 (hinj' i (h.trans (map_one _).symm))
  · show ψ' i u * ψ' i e * (ψ' i u)⁻¹ = (ψ' i e)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, heu, map_inv]
  · rw [mul_inv_eq_iff_eq_mul]
    exact (hcomm i j hij u e).eq

end CFSG.AGLEmbedding.KFactProofs.CoverE6
