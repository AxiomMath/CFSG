module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5TorusGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5SpinCoords
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidRank
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicRootCenter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen
open scoped Pointwise commutatorElement

section TorusCoords

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem rootChar_coordTuple {Δ : Finset (Fin τ.rank → ℤ)}
    (hΔ : ∀ β ∈ Δ, IsRoot τ β) (c : (Fin τ.rank → ℤ) → Lˣ) (γ : Fin τ.rank → ℤ) :
    rootChar (coordTuple Δ c) γ = ∏ β ∈ Δ, c β ^ corootPair β γ := by
  unfold rootChar
  simp only [coordTuple]
  rw [prod_zpow_prod_comm Δ Finset.univ c (fun β i => corootPair β (Pi.single i 1)) γ]
  refine Finset.prod_congr rfl fun β hβ => ?_
  rw [CFSG.StandardType.LayerCycRoot.corootPair_eq_sum_single (hΔ β hβ) γ]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem exists_pow_tuple_of_det_eq_four {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℤ} (hdet : A.det = 4) (d : ι → Lˣ) :
    ∃ c : ι → Lˣ, ∀ j, ∏ i, c i ^ A i j = d j := by
  classical
  have hroot : ∀ i : ι, ∃ f : Lˣ, (f : L) ^ 4 = (d i : L) := by
    intro i
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (d i : L) (by norm_num : 0 < 4)
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, zero_pow (by norm_num : 4 ≠ 0)] at hy
      exact (d i).ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, by simpa using hy⟩
  choose f hf using hroot
  refine ⟨fun i => ∏ k, f k ^ A.adjugate k i, fun j => ?_⟩
  have hcalc : ∏ i, (∏ k, f k ^ A.adjugate k i) ^ A i j =
      ∏ k, f k ^ (∑ i, A.adjugate k i * A i j) := by
    calc ∏ i, (∏ k, f k ^ A.adjugate k i) ^ A i j
        = ∏ i, ∏ k, (f k ^ A.adjugate k i) ^ A i j := by
          refine Finset.prod_congr rfl fun i _ =>
            (Finset.prod_zpow (fun k => f k ^ A.adjugate k i) Finset.univ (A i j)).symm
      _ = ∏ k, ∏ i, (f k ^ A.adjugate k i) ^ A i j := Finset.prod_comm
      _ = ∏ k, ∏ i, f k ^ (A.adjugate k i * A i j) := by
          refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun i _ => ?_
          rw [zpow_mul]
      _ = ∏ k, f k ^ (∑ i, A.adjugate k i * A i j) := by
          refine Finset.prod_congr rfl fun k _ => ?_
          rw [Finset.prod_zpow_eq_zpow_sum]
  rw [hcalc]
  have hsum : ∀ k, ∑ i, A.adjugate k i * A i j = 4 * (if k = j then 1 else 0) := by
    intro k
    have h1 := congrFun (congrFun (Matrix.adjugate_mul A) k) j
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, hdet, smul_eq_mul] at h1
    rw [h1]
  rw [Finset.prod_congr rfl fun k _ => by rw [hsum k]]
  rw [Finset.prod_eq_single j]
  · rw [if_pos rfl, mul_one]
    exact Units.ext (hf j)
  · intro k _ hk
    rw [if_neg hk, mul_zero, zpow_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem eq_one_of_pow_tuple_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℤ} (hdet : A.det = 4) {c : ι → Lˣ}
    (h : ∀ j, ∏ i, c i ^ A i j = 1) : c = 1 := by
  classical
  have hmain : ∀ j, (c j : L) ^ 4 = 1 := by
    intro j
    have h1 : ∏ k, (∏ i, c i ^ A i k) ^ A.adjugate k j = (c j : Lˣ) ^ A.det := by
      calc ∏ k, (∏ i, c i ^ A i k) ^ A.adjugate k j
          = ∏ k, ∏ i, c i ^ (A i k * A.adjugate k j) := by
            refine Finset.prod_congr rfl fun k _ => ?_
            rw [← Finset.prod_zpow]
            exact Finset.prod_congr rfl fun i _ => (zpow_mul _ _ _).symm
        _ = ∏ i, ∏ k, c i ^ (A i k * A.adjugate k j) := Finset.prod_comm
        _ = ∏ i, c i ^ (∑ k, A i k * A.adjugate k j) := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [Finset.prod_zpow_eq_zpow_sum]
        _ = ∏ i, c i ^ ((A * A.adjugate) i j) := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [Matrix.mul_apply]
        _ = ∏ i, c i ^ (A.det * (1 : Matrix ι ι ℤ) i j) := by
            rw [Matrix.mul_adjugate]
            simp
        _ = (c j : Lˣ) ^ A.det := by
            rw [Finset.prod_eq_single j]
            · rw [Matrix.one_apply_eq, mul_one]
            · intro i _ hi
              rw [Matrix.one_apply_ne hi, mul_zero, zpow_zero]
            · intro hj
              exact absurd (Finset.mem_univ j) hj
    have h2 : (c j : Lˣ) ^ A.det = 1 := by
      rw [← h1]
      exact Finset.prod_eq_one fun k _ => by rw [h k, one_zpow]
    rw [hdet] at h2
    exact congrArg Units.val h2
  funext j
  exact Units.ext (iterateFrobenius_inj L 2 2 (by simpa [iterateFrobenius_def] using hmain j))

end TorusCoords

section DatumCoords

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
  {M : Type} [CommGroup M]

theorem rootSL2_mem_rootSpan_of_mem {S : Set (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (h1 : β ∈ S) (h2 : -β ∈ S) (A : SL2 L) :
    rootSL2 τ L β A ∈ rootSpan τ L S := by
  have h : rootSL2 τ L β A ∈ (rootSL2 τ L β).range := ⟨A, rfl⟩
  rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ] at h
  exact sup_le (rootSubgroup_le_rootSpan h1) (rootSubgroup_le_rootSpan h2) h

theorem rootDiagUnit_coordTuple_mem_rootSpan {Δ : Finset (Fin τ.rank → ℤ)}
    {S : Set (Fin τ.rank → ℤ)}
    (hΔ : ∀ β ∈ Δ, IsRoot τ β) (c : (Fin τ.rank → ℤ) → Lˣ)
    (hsub : ∀ β ∈ Δ, β ∈ S) (hneg : ∀ β ∈ Δ, -β ∈ S) :
    rootDiagUnit τ (coordTuple Δ c) ∈ rootSpan τ L S := by
  classical
  induction Δ using Finset.induction with
  | empty =>
      have h : coordTuple (∅ : Finset (Fin τ.rank → ℤ)) c = 1 := by
        funext i
        simp [coordTuple]
      rw [h, rootDiagUnit_one]
      exact one_mem _
  | insert β s hβs ih =>
      have hcoord : coordTuple (insert β s) c =
          (fun i => c β ^ corootPair β (Pi.single i 1)) * coordTuple s c := by
        funext i
        simp [coordTuple, Finset.prod_insert hβs, Pi.mul_apply]
      have hβS : β ∈ S := hsub β (Finset.mem_insert_self β s)
      have hnegβS : -β ∈ S := hneg β (Finset.mem_insert_self β s)
      have hsub' : ∀ γ ∈ s, γ ∈ S := fun γ hγ => hsub γ (Finset.mem_insert_of_mem hγ)
      have hneg' : ∀ γ ∈ s, -γ ∈ S := fun γ hγ => hneg γ (Finset.mem_insert_of_mem hγ)
      rw [hcoord, rootDiagUnit_mul, ← rootSL2_HSL_eq (hΔ β (Finset.mem_insert_self β s))]
      exact mul_mem
        (rootSL2_mem_rootSpan_of_mem (hΔ β (Finset.mem_insert_self β s)) hβS hnegβS
          (HSL (c β)))
        (ih (fun γ hγ => hΔ γ (Finset.mem_insert_of_mem hγ)) hsub' hneg')

theorem exists_rootDiagUnit_coordTuple_of_mem_rootSpan_torus
    {S : Set (Fin τ.rank → ℤ)} {Δ : Finset (Fin τ.rank → ℤ)}
    (hΔroot : ∀ β ∈ Δ, IsRoot τ β)
    (hΔsub : ∀ β ∈ Δ, β ∈ S)
    (hdet : (Matrix.of fun β γ : Δ => corootPair (β : Fin τ.rank → ℤ) γ).det = 4)
    (hspan : ∀ γ ∈ S, ∃ cc : (Fin τ.rank → ℤ) → ℤ, γ = ∑ β ∈ Δ, cc β • β)
    (hSroot : ∀ γ ∈ S, IsRoot τ γ)
    (hneg : ∀ γ ∈ S, -γ ∈ S)
    (hcenter : Subgroup.center (rootSpan τ L S) = ⊥)
    {t : ModGL τ L} (ht : t ∈ rootSpan τ L S ⊓ torusGroup τ L) :
    ∃ c : (Fin τ.rank → ℤ) → Lˣ, t = rootDiagUnit τ (coordTuple Δ c) := by
  classical
  have htT : t ∈ torusGroup τ L := ht.2
  have htS : t ∈ rootSpan τ L S := ht.1
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htT
  rw [hl] at htS ⊢
  obtain ⟨c₀, hc₀⟩ := exists_pow_tuple_of_det_eq_four (L := L) hdet
    (fun β : Δ => rootChar l (β : Fin τ.rank → ℤ))
  let c : (Fin τ.rank → ℤ) → Lˣ := fun γ => if h : γ ∈ Δ then c₀ ⟨γ, h⟩ else 1
  have hc : ∀ β (hβ : β ∈ Δ), c β = c₀ ⟨β, hβ⟩ := by
    intro β hβ
    simp [c, hβ]
  have hrootc : ∀ β ∈ Δ, rootChar (coordTuple Δ c) β = rootChar l β := by
    intro β hβ
    rw [rootChar_coordTuple hΔroot c β]
    have h1 : (∏ γ ∈ Δ, c γ ^ corootPair γ β) =
        ∏ i : Δ, c₀ i ^ corootPair (i : Fin τ.rank → ℤ) β := by
      rw [← Finset.prod_coe_sort]
      exact Finset.prod_congr rfl fun i _ => by rw [hc i i.2]
    rw [h1]
    exact hc₀ ⟨β, hβ⟩
  have hchar : ∀ γ ∈ S, rootChar (coordTuple Δ c) γ = rootChar l γ := by
    intro γ hγ
    obtain ⟨cc, rfl⟩ := hspan γ hγ
    rw [CFSG.LieType.Chevalley.rootChar_sum, CFSG.LieType.Chevalley.rootChar_sum]
    exact Finset.prod_congr rfl fun β hβ => by
      rw [CFSG.LieType.Chevalley.rootChar_zsmul, CFSG.LieType.Chevalley.rootChar_zsmul, hrootc β hβ]
  have hcharz : ∀ γ ∈ S, rootChar (l * (coordTuple Δ c)⁻¹) γ = 1 := by
    intro γ hγ
    rw [CFSG.LieType.Chevalley.rootChar_mul_tuple, CFSG.LieType.Chevalley.rootChar_inv_apply,
      hchar γ hγ, mul_inv_cancel]
  let z : ModGL τ L := rootDiagUnit τ (l * (coordTuple Δ c)⁻¹)
  have hzS : z ∈ rootSpan τ L S := by
    rw [show z = rootDiagUnit τ (l * (coordTuple Δ c)⁻¹) from rfl, rootDiagUnit_mul,
      ← rootDiagUnit_inv]
    refine mul_mem htS (inv_mem ?_)
    refine rootDiagUnit_coordTuple_mem_rootSpan hΔroot c hΔsub (fun β hβ => hneg β (hΔsub β hβ))
  have hcent : (⟨z, hzS⟩ : ↥(rootSpan τ L S)) ∈ Subgroup.center (rootSpan τ L S) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have hx := rootSpan_le_centralizer (a := l * (coordTuple Δ c)⁻¹) (S := S)
      (fun γ hγ => ⟨hSroot γ hγ, hcharz γ hγ⟩) x.2
    exact (Subgroup.mem_centralizer_iff.1 hx z (by rfl)).symm
  have hz1 : z = 1 := by
    have h : (⟨z, hzS⟩ : ↥(rootSpan τ L S)) = 1 := by
      have hmem : (⟨z, hzS⟩ : ↥(rootSpan τ L S)) ∈ (⊥ : Subgroup ↥(rootSpan τ L S)) :=
        hcenter ▸ hcent
      exact Subgroup.mem_bot.1 hmem
    exact congrArg Subtype.val h
  refine ⟨c, ?_⟩
  have hz' : rootDiagUnit τ l * (rootDiagUnit τ (coordTuple Δ c))⁻¹ = 1 := by
    have h1 : rootDiagUnit τ (l * (coordTuple Δ c)⁻¹) = 1 := hz1
    rwa [rootDiagUnit_mul, ← rootDiagUnit_inv] at h1
  exact mul_inv_eq_one.mp hz'

theorem exists_rootDiagUnit_coordTuple_of_mem_torusJ
    (D : CFSG.RankThree.Lattice.GenFixedRootDatum τ 2 L M)
    (Δ : Finset (Fin τ.rank → ℤ))
    (hΔ : (Δ : Set (Fin τ.rank → ℤ)) = D.simpleRootsJ)
    (hΔroot : ∀ β ∈ Δ, IsRoot τ β)
    (hdet : (Matrix.of fun β γ : Δ => corootPair (β : Fin τ.rank → ℤ) γ).det = 4)
    (hspan : ∀ γ ∈ D.roots, ∃ cc : (Fin τ.rank → ℤ) → ℤ,
      γ = ∑ β ∈ Δ, cc β • β)
    (hcenter : Subgroup.center (rootSpan τ L D.roots) = ⊥)
    {t : ModGL τ L} (ht : t ∈ D.torusJ) :
    ∃ c : (Fin τ.rank → ℤ) → Lˣ, t = rootDiagUnit τ (coordTuple Δ c) := by
  refine exists_rootDiagUnit_coordTuple_of_mem_rootSpan_torus (S := D.roots)
    hΔroot ?_ hdet hspan (fun γ hγ => isRoot_of_mem_unionRoots hγ)
    (fun γ hγ => neg_mem_unionRoots (χ := D.χ) (J := D.J) hγ) hcenter ht
  intro β hβ
  have hβΔ : β ∈ D.simpleRootsJ := by rw [← hΔ]; exact hβ
  exact hβΔ.2

theorem coordTuple_injective_of_det_four
    (Δ : Finset (Fin τ.rank → ℤ))
    (hΔroot : ∀ β ∈ Δ, IsRoot τ β)
    (hdet : (Matrix.of fun β γ : Δ => corootPair (β : Fin τ.rank → ℤ) γ).det = 4)
    {c c' : (Fin τ.rank → ℤ) → Lˣ}
    (h : rootDiagUnit τ (coordTuple Δ c) = rootDiagUnit τ (coordTuple Δ c')) :
    ∀ β ∈ Δ, c β = c' β := by
  classical
  have htuple := CFSG.LieType.Chevalley.rootDiagUnit_injective h
  intro β hβ
  let A : Matrix Δ Δ ℤ := Matrix.of fun i j =>
    corootPair (i : Fin τ.rank → ℤ) (j : Fin τ.rank → ℤ)
  have hdetA : A.det = 4 := hdet
  have h1 : ∀ j : Δ, ∏ i : Δ, c (i : Fin τ.rank → ℤ) ^ A i j =
      ∏ i : Δ, c' (i : Fin τ.rank → ℤ) ^ A i j := by
    intro j
    have h1 := congrArg (fun t => rootChar t (j : Fin τ.rank → ℤ)) htuple
    rw [rootChar_coordTuple hΔroot c (j : Fin τ.rank → ℤ),
      rootChar_coordTuple hΔroot c' (j : Fin τ.rank → ℤ)] at h1
    have e1 : (∏ i : Δ, c (i : Fin τ.rank → ℤ) ^ A i j) =
        ∏ i ∈ Δ, c i ^ corootPair i (j : Fin τ.rank → ℤ) := by
      exact (Finset.prod_coe_sort (s := Δ)
        (f := fun i => c i ^ corootPair i (j : Fin τ.rank → ℤ)))
    have e2 : (∏ i : Δ, c' (i : Fin τ.rank → ℤ) ^ A i j) =
        ∏ i ∈ Δ, c' i ^ corootPair i (j : Fin τ.rank → ℤ) := by
      exact (Finset.prod_coe_sort (s := Δ)
        (f := fun i => c' i ^ corootPair i (j : Fin τ.rank → ℤ)))
    rw [e1, e2]
    exact h1
  have h2 : ∀ j : Δ, ∏ i : Δ, (c (i : Fin τ.rank → ℤ) / c' (i : Fin τ.rank → ℤ)) ^
      A i j = 1 := by
    intro j
    have e3 : (∏ i : Δ, (c (i : Fin τ.rank → ℤ) / c' (i : Fin τ.rank → ℤ)) ^ A i j) =
        ∏ i ∈ Δ, (c i / c' i) ^ corootPair i (j : Fin τ.rank → ℤ) := by
      exact (Finset.prod_coe_sort (s := Δ)
        (f := fun i => (c i / c' i) ^ corootPair i (j : Fin τ.rank → ℤ)))
    rw [e3]
    calc ∏ i ∈ Δ, (c i / c' i) ^ corootPair i (j : Fin τ.rank → ℤ)
        = ∏ i ∈ Δ, (c i ^ corootPair i (j : Fin τ.rank → ℤ) *
            (c' i ^ corootPair i (j : Fin τ.rank → ℤ))⁻¹) := by
          exact Finset.prod_congr rfl fun i _ => by
            rw [div_eq_mul_inv, mul_zpow, inv_zpow]
      _ = (∏ i ∈ Δ, c i ^ corootPair i (j : Fin τ.rank → ℤ)) *
          (∏ i ∈ Δ, c' i ^ corootPair i (j : Fin τ.rank → ℤ))⁻¹ := by
          rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
      _ = 1 := by
          have hj : (∏ i ∈ Δ, c i ^ corootPair i (j : Fin τ.rank → ℤ)) =
              ∏ i ∈ Δ, c' i ^ corootPair i (j : Fin τ.rank → ℤ) := by
            have h1 := congrArg (fun t => rootChar t (j : Fin τ.rank → ℤ)) htuple
            rw [rootChar_coordTuple hΔroot c (j : Fin τ.rank → ℤ),
              rootChar_coordTuple hΔroot c' (j : Fin τ.rank → ℤ)] at h1
            exact h1
          rw [hj, mul_inv_cancel]
  have h3 := eq_one_of_pow_tuple_eq_one (L := L) hdetA h2
  have h4 := congrFun h3 ⟨β, hβ⟩
  exact div_eq_one.mp h4

end DatumCoords

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
