module

public import CFSG.Quasithin.Background.SmithCurtisChevType
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.FixDim

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley

section BC

variable {K : Type*} [Field K] {k : Type*} [Field k] [Algebra K k] {G : Type*} [Group G]
  {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

@[expose] def bcMat (k : Type*) [Field k] [Algebra K k] (ρ : Representation K G (Idx → K)) (g : G) :
    Matrix Idx Idx k :=
  (LinearMap.toMatrix' (ρ g)).map (algebraMap K k)

@[expose] def bcRep (k : Type*) [Field k] [Algebra K k] (ρ : Representation K G (Idx → K)) :
    Representation k G (Idx → k) where
  toFun g := Matrix.toLin' (bcMat k ρ g)
  map_one' := by
    simp only [bcMat, map_one, LinearMap.toMatrix'_one]
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    simp only [bcMat, map_mul, LinearMap.toMatrix'_mul]
    rw [Matrix.map_mul, Matrix.toLin'_mul]
    rfl

@[expose] def bcv (k : Type*) [Field k] [Algebra K k] (v : Idx → K) : Idx → k :=
  fun i => algebraMap K k (v i)

theorem bcRep_apply (ρ : Representation K G (Idx → K)) (g : G) (v : Idx → k) :
    bcRep k ρ g v = (bcMat k ρ g).mulVec v := by
  simp [bcRep, Matrix.toLin'_apply]

theorem bcRep_bcv (ρ : Representation K G (Idx → K)) (g : G) (v : Idx → K) :
    bcRep k ρ g (bcv k v) = bcv k (ρ g v) := by
  rw [bcRep_apply]
  funext i
  have h := congrFun (LinearMap.toMatrix'_mulVec (ρ g) v) i
  simp only [bcv, bcMat, Matrix.mulVec, dotProduct, Matrix.map_apply] at h ⊢
  rw [← h, map_sum]
  simp only [map_mul]

theorem bcv_injective : Function.Injective (bcv (Idx := Idx) (K := K) k) := by
  intro a b h
  funext i
  exact (algebraMap K k).injective (congrFun h i)

theorem bcv_add (a b : Idx → K) : bcv k (a + b) = bcv k a + bcv k b := by
  funext i; simp [bcv]

theorem bcv_smul (c : K) (a : Idx → K) : bcv k (c • a) = algebraMap K k c • bcv k a := by
  funext i; simp [bcv]

theorem bcv_zero : bcv (Idx := Idx) (K := K) k 0 = 0 := by
  funext i; simp [bcv]

theorem bcv_single (i : Idx) : bcv (K := K) k (Pi.single i 1) = Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h; simp [bcv]
  · simp [bcv, Pi.single_apply, h]

theorem exists_smul_of_finrank_eq_one {V : Type*} [AddCommGroup V] [Module k V]
    (S : Submodule k V) (hS : Module.finrank k S = 1) {v : V} (hv : v ∈ S) (hv0 : v ≠ 0) {x : V}
    (hx : x ∈ S) : ∃ c : k, x = c • v := by
  have h := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : S) (fun h => hv0 (congrArg Subtype.val h))).1 hS
    ⟨x, hx⟩
  obtain ⟨c, hc⟩ := h
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem bcv_sum {ι : Type*} (s : Finset ι) (f : ι → Idx → K) :
    bcv k (∑ c ∈ s, f c) = ∑ c ∈ s, bcv k (f c) := by
  funext i
  simp [bcv, Finset.sum_apply, map_sum]

end BC

section Curtis


variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Type} [Field k] [Algebra K k]
  [CharP k 2] {Idx : Type} [Fintype Idx] [DecidableEq Idx] {τ : Tag}
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}

theorem isChevType_bcRep {ρ : Representation K (adjointGroup τ K) (Idx → K)} {y : Idx → K}
    {χ : adjointGroup τ K → K} {J : Finset (Fin τ.rank)} (ht : IsChevType τ K 2 hw ρ y χ J) :
    IsChevType τ K 2 hw (bcRep k ρ) (bcv k y) (fun g => algebraMap K k (χ g)) J := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨hfix, hy0, hH, hJ⟩ := ht
  refine ⟨fun u hu => ?_, fun h => hy0 (bcv_injective (k := k) (by rw [h, bcv_zero])),
    fun h hh => ?_, fun i => ?_⟩
  · rw [bcRep_bcv, hfix u hu]
  · rw [bcRep_bcv, hH h hh, bcv_smul]
  · have hT : (chevDatum τ K 2 hw).heckeT (bcRep k ρ) i (bcv k y) =
        bcv k ((chevDatum τ K 2 hw).heckeT ρ i y) := by
      rw [heckeT_chevDatum, heckeT_chevDatum, bcv_sum]
      exact Finset.sum_congr rfl fun c _ => bcRep_bcv _ _ _
    rw [hJ i, hT]
    refine and_congr ?_ ?_
    · constructor
      · intro hall t
        show algebraMap K k (χ (dC τ K i t)) = 1
        rw [hall t, map_one]
      · intro hall t
        apply (algebraMap K k).injective
        rw [map_one]
        exact hall t
    · constructor
      · intro h0
        rw [h0, bcv_zero]
      · intro h0
        exact bcv_injective (k := k) (by rw [h0, bcv_zero])

theorem isSimpleRep_bcRep {ρ : Representation K (adjointGroup τ K) (Idx → K)} (hρ : IsSimpleRep ρ)
    {y : Idx → K} {χ : adjointGroup τ K → K} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) : IsSimpleRep (bcRep k ρ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy0 := ht.2.1
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  haveI : Nonempty Idx := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hy0 (Subsingleton.elim _ _)
  haveI : Nontrivial (Idx → k) := inferInstance
  let D := chevDatum τ K 2 hw
  have hfixK : ∀ x ∈ D.fixU ρ, ∃ c : K, x = c • y := fun x hx => D.fixU_eq_smul hρ hμ hx
  let T : D.U → Matrix Idx Idx K := fun u => LinearMap.toMatrix' (ρ u)
  have hfixF : ∀ v : Idx → K, v ∈ fixF T ↔ v ∈ D.fixU ρ := by
    intro v
    rw [mem_fixF, CurtisDatum.mem_fixU]
    constructor
    · intro h u hu
      have := h ⟨u, hu⟩
      simpa [T, LinearMap.toMatrix'_mulVec] using this
    · intro h u
      simpa [T, LinearMap.toMatrix'_mulVec] using h u.1 u.2
  have h1 : Module.finrank K (fixF T) = 1 := by
    rw [finrank_eq_one_iff_of_nonzero' (⟨y, (hfixF y).2 ht.1⟩ : fixF T)
      (fun h => hy0 (congrArg Subtype.val h))]
    intro w
    obtain ⟨c, hc⟩ := hfixK w ((hfixF w).1 w.2)
    exact ⟨c, Subtype.ext hc.symm⟩
  have h2 : Module.finrank k (fixK (k := k) T) = 1 := by rw [finrank_fixK, h1]
  have hbcy : bcv k y ∈ fixK (k := k) T := by
    rw [mem_fixK]
    intro u
    have := ht.1 u.1 u.2
    have h3 := bcRep_bcv (k := k) ρ u.1 y
    rw [this, bcRep_apply] at h3
    exact h3
  have hbcy0 : bcv k y ≠ 0 := fun h => hy0 (bcv_injective (k := k) (by rw [h, bcv_zero]))
  have hgen : orbitSpan (bcRep k ρ) (bcv k y) = ⊤ := by
    have htop := orbitSpan_eq_top hρ hy0
    rw [eq_top_iff]
    intro w _
    have hmem : ∀ i, bcv k (Pi.single i (1 : K) : Idx → K) ∈ orbitSpan (bcRep k ρ) (bcv k y) := by
      intro i
      have hi : (Pi.single i (1 : K) : Idx → K) ∈ orbitSpan ρ y := by rw [htop]; trivial
      refine Submodule.span_induction
        (p := fun x _ => bcv k x ∈ orbitSpan (bcRep k ρ) (bcv k y)) ?_ ?_ ?_ ?_ hi
      · rintro _ ⟨g, rfl⟩
        rw [← bcRep_bcv]
        exact Submodule.subset_span ⟨g, rfl⟩
      · rw [bcv_zero]; exact zero_mem _
      · intro a b _ _ ha hb
        rw [bcv_add]; exact add_mem ha hb
      · intro c a _ ha
        rw [bcv_smul]; exact Submodule.smul_of_tower_mem _ _ ha
    have hw : w = ∑ i, w i • bcv k (Pi.single i (1 : K) : Idx → K) := by
      funext j
      simp [bcv_single, Finset.sum_apply, Pi.single_apply]
    rw [hw]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)
  refine D.isSimpleRep_of_fixU (p := 2) (bcRep k ρ) (y := bcv k y) (fun x hx => ?_) hgen
  have hx' : x ∈ fixK (k := k) T := by
    rw [mem_fixK]
    intro u
    have := hx u.1 u.2
    rw [bcRep_apply] at this
    exact this
  exact exists_smul_of_finrank_eq_one _ h2 hbcy hbcy0 hx'

end Curtis

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
