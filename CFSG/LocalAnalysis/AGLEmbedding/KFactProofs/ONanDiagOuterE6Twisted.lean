module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Torus
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem exists_compatDiag_torus_of_conj_mem
    {t : TwistTag} {K : Type} [Field K] {σ : K →+* K} (hσ : Function.Surjective σ)
    {h : graphFixedRootGroup t K σ}
    (hA : MulAut.conj h ∈ graphFixedUnipotentStabilizer t K σ) :
    ∃ u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ,
      MulAut.conj h = compatDiagAutHom t K σ u ∧
        (h : ModGL t.tag K) = rootDiagUnit t.tag (compatDiag t σ u) ∧
        (h : ModGL t.tag K) ∈ torusGroup t.tag K := by
  obtain ⟨hU, hV⟩ := hA
  have hNU := mem_normalizer_of_map_conj_subgroupOf
    (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ) hU
  have hNV := mem_normalizer_of_map_conj_subgroupOf
    (graphFixedNegUnipotent_le_graphFixedRootGroup t K σ) hV
  have hB : (h : ModGL t.tag K) ∈ graphFixedRootBorel t K σ := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ]
    exact Subgroup.mem_inf.2 ⟨h.2, hNU⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem t.tag).length
  have hn : canonicalRep (coxeterSystem t.tag) K w₀ ∈ graphFixedRootGroup t K σ :=
    canonicalRep_mem_graphFixedRootGroup (mem_relWeylTwist_of_forall_length_le hw₀)
  have hC : (graphFixedRootGroup t K σ).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
        graphFixedRootGroup t K σ :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)
  have e : graphFixedRootGroup t K σ ⊓
      Subgroup.normalizer (graphFixedNegUnipotent t K σ : Set (ModGL t.tag K)) =
        (graphFixedRootBorel t K σ).map
          (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ,
      Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective, hC, Subgroup.map_equiv_normalizer_eq,
      map_conj_graphFixedPosUnipotent hw₀]
  have hB' : (h : ModGL t.tag K) ∈ (graphFixedRootBorel t K σ).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom := by
    rw [← e]
    exact Subgroup.mem_inf.2 ⟨h.2, hNV⟩
  have hH : (h : ModGL t.tag K) ∈ graphFixedRootTorus t K σ := by
    rw [← graphFixedRootBorel_inf_map_conj hw₀]
    exact Subgroup.mem_inf.2 ⟨hB, hB'⟩
  have hT : (h : ModGL t.tag K) ∈ torusGroup t.tag K :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hH).1).1
  have hΓ : (h : ModGL t.tag K) ∈ twistedFixedGroup t K σ :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hH).1).2
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hF := ((mem_twistedFixedGroup_iff_twistHom t K σ).1 hΓ).2
  rw [hb, twistHom_rootDiagUnit_eq] at hF
  have hb' : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i) := by
    intro i
    have h1 := congrFun (rootDiagUnit_injective hF) (t.perm i)
    rw [Equiv.symm_apply_apply] at h1
    exact h1.symm
  obtain ⟨u, hu⟩ := exists_compatDiag_eq hb'
  refine ⟨u, MulEquiv.ext fun g => Subtype.ext ?_, by rw [hu, ← hb], hT⟩
  rw [coe_compatDiagAutHom, hu, ← hb]
  rfl

theorem compatDiag_npow {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ) (n : ℕ) :
    compatDiag t σ (u ^ n) = compatDiag t σ u ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, compatDiag_one]
  | succ n ih => rw [pow_succ, pow_succ, compatDiag_mul, ih]

@[expose] def e6OrbitPair {K : Type} [Field K] (x y : Kˣ) : Fin Tag.E6.rank → Kˣ :=
  ![x, 1, 1, 1, 1, y]

theorem e6OrbitPair_perm {K : Type} [Field K] (σ : K →+* K) (x : Kˣ)
    (hσσ : Units.map σ.toMonoidHom (Units.map σ.toMonoidHom x) = x) (i : Fin Tag.E6.rank) :
    e6OrbitPair x (Units.map σ.toMonoidHom x) (TwistTag.E6.perm i) =
      Units.map σ.toMonoidHom (e6OrbitPair x (Units.map σ.toMonoidHom x) i) := by
  have key : ∀ i : Fin 6, (![x, 1, 1, 1, 1, Units.map σ.toMonoidHom x] :
      Fin 6 → Kˣ) ((Equiv.swap 0 5 * Equiv.swap 2 4 : Equiv.Perm (Fin 6)) i) =
        Units.map σ.toMonoidHom ((![x, 1, 1, 1, 1, Units.map σ.toMonoidHom x] :
          Fin 6 → Kˣ) i) := by
    intro i
    fin_cases i <;> simp [Equiv.swap_apply_def]
    exact hσσ.symm
  exact key i

theorem e6Invariant_orbitPair {K : Type} [Field K] (x y : Kˣ) :
    e6Invariant K (e6OrbitPair x y) = x * y ^ 2 := by
  change ∏ l : Fin 6, (e6OrbitPair x y) l ^ e6Weight l = _
  rw [Fin.prod_univ_six]
  simp [e6OrbitPair, e6Weight]

theorem hasDiagOuterThree_graphFixedE6
    {K : Type} [Field K] [Finite K] {q : ℕ} (σ : K ≃+* K) (hK : Nat.card K = q ^ 2)
    (hσ : ∀ c, σ c = c ^ q) (h3 : 3 ∣ q + 1) :
    HasDiagOuterThree (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  have hcube : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    obtain ⟨j, hj⟩ : ∃ j, q = 3 * j + 2 := ⟨(q - 2) / 3, by omega⟩
    have h : q ^ 2 = 3 * (3 * j ^ 2 + 4 * j + 1) + 1 := by rw [hj]; ring
    rw [h, Nat.add_sub_cancel]
    exact Dvd.intro _ rfl
  obtain ⟨μ, hμ⟩ := exists_not_cube hcube
  have : Fintype K := Fintype.ofFinite K
  have hσμ : Units.map σ.toRingHom.toMonoidHom μ = μ ^ q := Units.ext (hσ _)
  have hσσ : Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom μ) = μ := by
    rw [hσμ, map_pow, hσμ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card]
    exact Units.ext (FiniteField.pow_card _)
  obtain ⟨u, hu⟩ := exists_compatDiag_eq (t := TwistTag.E6) (σ := σ.toRingHom)
    (b := e6OrbitPair μ (Units.map σ.toRingHom.toMonoidHom μ))
    (fun i => e6OrbitPair_perm σ.toRingHom μ hσσ i)
  refine ⟨compatDiagAutHom TwistTag.E6 K σ.toRingHom u, fun k hk => ?_⟩
  obtain ⟨g, hg⟩ := hk
  have hpow : compatDiagAutHom TwistTag.E6 K σ.toRingHom u ^ 2 ^ k =
      compatDiagAutHom TwistTag.E6 K σ.toRingHom (u ^ 2 ^ k) :=
    (map_pow (compatDiagAutHom TwistTag.E6 K σ.toRingHom) u (2 ^ k)).symm
  have hA : MulAut.conj g ∈ graphFixedUnipotentStabilizer TwistTag.E6 K σ.toRingHom := by
    rw [hg, hpow, ← normalActor_one_right σ]
    exact normalActor_mem σ _ 1
  obtain ⟨v, hv, hgv, hT⟩ := exists_compatDiag_torus_of_conj_mem σ.surjective hA
  have hvu : v = u ^ 2 ^ k := compatDiagAutHom_injective (hv.symm.trans (hg.trans hpow))
  obtain ⟨b, hb, z, hz⟩ := exists_cube_of_mem_torusGroup hT
  have hbv : b = compatDiag TwistTag.E6 σ.toRingHom v := rootDiagUnit_injective (hb.trans hgv)
  rw [hbv, hvu, compatDiag_npow, hu] at hz
  replace hz := hz.trans
    (map_pow (e6Invariant K) (e6OrbitPair μ (Units.map σ.toRingHom.toMonoidHom μ)) (2 ^ k))
  rw [e6Invariant_orbitPair, hσμ, ← pow_mul, ← pow_succ', ← pow_mul] at hz
  have h1 : Nat.Coprime (q * 2 + 1) 3 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega))
  obtain ⟨y, hy⟩ := isCube_of_pow_eq_cube
    (Nat.Coprime.mul_left h1 (Nat.Coprime.pow_left k (by norm_num))) hz.symm
  exact hμ y hy

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
