module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SteinbergLangFamily
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem graphTorus_zpow_sum {G : Type*} [CommGroup G] (a : G) {ι : Type*} (s : Finset ι)
    (f : ι → ℤ) : a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  refine Finset.induction_on s (by simp) fun x s hx ih => ?_
  rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]


section Torus

variable {τ : Tag} {L : Type} [Field L] {r : ℕ}

@[expose] def graphTorusChar (γ : Fin r → Fin τ.rank → ℤ) (u : Fin r → Lˣ) : Fin τ.rank → Lˣ :=
  fun i => ∏ j, u j ^ corootPair (γ j) (Pi.single i 1)

theorem graphTorusChar_mul (γ : Fin r → Fin τ.rank → ℤ) (u v : Fin r → Lˣ) :
    graphTorusChar γ (u * v) = graphTorusChar γ u * graphTorusChar γ v := by
  funext i
  simp only [graphTorusChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem graphTorusChar_one (γ : Fin r → Fin τ.rank → ℤ) :
    graphTorusChar γ (1 : Fin r → Lˣ) = 1 := by
  funext i
  simp [graphTorusChar]

@[expose] noncomputable def graphTorusHom (γ : Fin r → Fin τ.rank → ℤ) (G : Subgroup Lˣ)
    (z : ModGL τ L) : (Fin r → G) →* ModGL τ L where
  toFun u := z * rootDiagUnit τ (graphTorusChar γ fun j => (u j : Lˣ)) * z⁻¹
  map_one' := by
    have h : (fun j => ((1 : Fin r → G) j : Lˣ)) = 1 := by
      funext j
      rfl
    simp only [h, graphTorusChar_one, rootDiagUnit_one, mul_one, mul_inv_cancel]
  map_mul' u v := by
    have h : (fun j => ((u * v) j : Lˣ)) = (fun j => (u j : Lˣ)) * fun j => (v j : Lˣ) := by
      funext j
      rfl
    simp only [h, graphTorusChar_mul, rootDiagUnit_mul]
    group

theorem graphTorusHom_apply (γ : Fin r → Fin τ.rank → ℤ) (G : Subgroup Lˣ) (z : ModGL τ L)
    (u : Fin r → G) :
    graphTorusHom γ G z u = z * rootDiagUnit τ (graphTorusChar γ fun j => (u j : Lˣ)) * z⁻¹ :=
  rfl

theorem rootDiagUnit_graphTorusChar_mulSingle {γ : Fin r → Fin τ.rank → ℤ}
    (hγ : ∀ j, IsRoot τ (γ j)) (j : Fin r) (t : Lˣ) :
    rootDiagUnit τ (graphTorusChar γ (Pi.mulSingle j t)) = rootSL2 τ L (γ j) (HSL t) := by
  rw [rootSL2_HSL_eq (hγ j)]
  congr 1
  funext i
  simp only [graphTorusChar]
  rw [Finset.prod_eq_single j (fun k _ hk => by rw [Pi.mulSingle_eq_of_ne hk, one_zpow])
    (fun h => absurd (Finset.mem_univ j) h), Pi.mulSingle_eq_same]

theorem graphTorusHom_eq_prod {γ : Fin r → Fin τ.rank → ℤ} (hγ : ∀ j, IsRoot τ (γ j))
    (G : Subgroup Lˣ) (z : ModGL τ L) (u : Fin r → G) :
    graphTorusHom γ G z u = ((List.finRange r).map fun j =>
      z * rootSL2 τ L (γ j) (HSL (u j : Lˣ)) * z⁻¹).prod := by
  have hu : u = ((List.finRange r).map fun j => Pi.mulSingle j (u j)).prod := by
    rw [← Fin.prod_univ_def]
    exact (Finset.univ_prod_mulSingle u).symm
  conv_lhs => rw [hu]
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, graphTorusHom_apply]
  have h : (fun k => ((Pi.mulSingle j (u j) : Fin r → G) k : Lˣ)) =
      Pi.mulSingle j (u j : Lˣ) := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · rw [Pi.mulSingle_eq_of_ne hk, Pi.mulSingle_eq_of_ne hk]
      rfl
  rw [h, rootDiagUnit_graphTorusChar_mulSingle hγ]

theorem graphTorusHom_injective {γ : Fin r → Fin τ.rank → ℤ} {G : Subgroup Lˣ} (z : ModGL τ L)
    {n : ℕ} (hG : ∀ x ∈ G, x ^ n = 1) {A : Fin r → Fin τ.rank → ℤ} {D : ℤ}
    (hA : ∀ k j, ∑ i, A k i * corootPair (γ j) (Pi.single i 1) = if k = j then D else 0)
    (hD : Nat.Coprime D.natAbs n) : Function.Injective (graphTorusHom γ G z) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have h1 : rootDiagUnit τ (graphTorusChar γ fun j => (u j : Lˣ)) = 1 := by
    have h := congrArg (fun x => z⁻¹ * x * z) hu
    simpa [graphTorusHom_apply, mul_assoc] using h
  have h2 : graphTorusChar γ (fun j => (u j : Lˣ)) = 1 :=
    rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
  funext k
  apply Subtype.ext
  have h3 : ((u k : Lˣ)) ^ D = 1 := by
    have e1 : ∏ i, (graphTorusChar γ (fun j => (u j : Lˣ)) i) ^ (A k i) = 1 := by
      rw [h2]
      simp
    rw [← e1]
    simp only [graphTorusChar]
    rw [show (∏ i, (∏ j, (u j : Lˣ) ^ corootPair (γ j) (Pi.single i 1)) ^ A k i) =
        ∏ i, ∏ j, (u j : Lˣ) ^ (A k i * corootPair (γ j) (Pi.single i 1)) by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← zpow_mul, mul_comm], Finset.prod_comm]
    have e2 : ∀ j, ∏ i, (u j : Lˣ) ^ (A k i * corootPair (γ j) (Pi.single i 1)) =
        (u j : Lˣ) ^ (if k = j then D else 0) := fun j => by
      rw [← hA k j, graphTorus_zpow_sum]
    simp only [e2]
    rw [Finset.prod_eq_single k (fun j _ hj => by simp [Ne.symm hj])
      (fun h => absurd (Finset.mem_univ k) h)]
    simp
  have h4 : ((u k : Lˣ)) ^ n = 1 := hG _ (u k).2
  have h5 : ((u k : Lˣ)) ^ D.natAbs = 1 := by
    rcases Int.natAbs_eq D with hD' | hD'
    · rw [hD'] at h3
      exact_mod_cast h3
    · rw [hD', zpow_neg, inv_eq_one] at h3
      exact_mod_cast h3
  have h6 := (pow_gcd_eq_one (a := (u k : Lˣ))).2 ⟨h5, h4⟩
  rw [hD.gcd_eq_one, pow_one] at h6
  rw [h6]
  rfl

theorem rootChar_graphTorusChar {γ : Fin r → Fin τ.rank → ℤ} (hγ : ∀ j, IsRoot τ (γ j))
    (u : Fin r → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar (graphTorusChar γ u) v = ∏ j, u j ^ corootPair (γ j) v := by
  simp only [rootChar, graphTorusChar]
  rw [show (∏ i, (∏ j, u j ^ corootPair (γ j) (Pi.single i 1)) ^ v i) =
      ∏ i, ∏ j, u j ^ (v i * corootPair (γ j) (Pi.single i 1)) by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← zpow_mul, mul_comm], Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [corootPair_eq_sum (hγ j) v, graphTorus_zpow_sum]

end Torus

section Family

variable {τ : Tag} (K : Type) [Field K] [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
  (hFr : ∀ c, Fr c = c ^ Nat.card K) {w : WeylGroup τ}
  {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
  (hg0 : Units.map (entrywiseHom Fr) g0 =
    g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
  {p : ℕ} (S : LangSetup τ (AlgebraicClosure K) p)
  (hSD : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0)

include hSD in
theorem steinbergLang_exists_family_neg (hp : p.Prime)
    (hst : ∀ b : Fin τ.rank → (AlgebraicClosure K)ˣ, (∀ i, b i ^ p = 1) →
      rootCharStabilizerSubgroup b ≤ kernelReflectionGroup b)
    {w₀ : WeylGroup τ} (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    (h2 : Nat.card K % p = p - 1)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hE : rootDiagUnit τ a ∈ S.E)
    (i : KernelComponent (rootCharHom a)) :
    ∃ (z : ModGL τ (AlgebraicClosure K))
      (P : (Fin τ.rank → ℤ) → GL (Fin 2) (AlgebraicClosure K)),
      (∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ (AlgebraicClosure K),
        g ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) j) ↔
          z * g * z⁻¹ ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) j)) ∧
      (∀ γ ∈ componentRoots (rootCharHom a) i, ∀ A : SL2 K,
        S.D.step (z * rootSL2 τ (AlgebraicClosure K) γ (conjSL (P γ)
          (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A)) * z⁻¹) =
          z * rootSL2 τ (AlgebraicClosure K) γ (conjSL (P γ)
            (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A)) * z⁻¹) ∧
      (∀ γ ∈ componentRoots (rootCharHom a) i, ∀ ζ : (AlgebraicClosure K)ˣ,
        ζ ^ (Nat.card K + 1) = 1 →
          HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
            (conjSL (P γ))) := by
  classical
  have hq := steinbergLang_q_eq K hFr hg0C hg0 S hSD
  have hρ := steinbergLang_rho_eq K hFr hg0C hg0 S hSD
  obtain ⟨u, hu, hρu⟩ := steinbergLang_twist_neg S hρ hE hst hw₀ hp.one_lt.le
    (by rw [hq]; exact h2) i
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := f4Three_exists_untwist_neg S hw₀ hE i hu hρu
  have hσK : ∀ c, σ.toRingHom c = c ^ Nat.card K := fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ, hq]
  have hP : ∀ γ : Fin τ.rank → ℤ, ∃ P : GL (Fin 2) (AlgebraicClosure K),
      IsRoot τ γ →
        (∀ B : SL2 (AlgebraicClosure K),
          canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w₀ *
            Units.map (entrywiseHom σ.toRingHom) (rootSL2 τ (AlgebraicClosure K) γ B) *
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w₀)⁻¹ =
            rootSL2 τ (AlgebraicClosure K) γ B ↔
          B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
            (conjSL P)) ∧
        ∀ ζ : (AlgebraicClosure K)ˣ, ζ ^ (Nat.card K + 1) = 1 →
          HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
            (conjSL P) := by
    intro γ
    by_cases hγ : IsRoot τ γ
    · obtain ⟨P, hP1, hP2⟩ := exists_twisted_rootSL2 (K := K) hσK hγ (hw₀ γ)
      exact ⟨P, fun _ => ⟨hP1, hP2⟩⟩
    · exact ⟨1, fun h => absurd h hγ⟩
  choose P hP using hP
  refine ⟨z, P, hnorm, fun γ hγ A => ?_, fun γ hγ ζ hζ =>
    ((hP γ) (isRoot_of_mem_componentRoots hγ)).2 ζ hζ⟩
  have hγr := isRoot_of_mem_componentRoots hγ
  have hgS := steinbergLang_rootSL2_mem_component K i hγ
    (conjSL (P γ) (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A))
  rw [hz _ hgS]
  have hfix := (((hP γ) hγr).1
    (conjSL (P γ) (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A))).2
      ⟨_, ⟨A, rfl⟩, rfl⟩
  exact congrArg (fun x => z * x * z⁻¹) hfix

end Family

end CFSG.HardMathSupport.Timmesfeld.CrossChar
