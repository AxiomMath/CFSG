module

public import CFSG.Quasithin.Background.SmithCurtisMain
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.Twist

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

open CFSG.Quasithin.SmithCurtis CoxeterSystem TensorProduct

variable {K : Type*} [Field K] (k : Type*) [Field k] [Algebra K k] {V : Type*} [AddCommGroup V]
  [Module K V] {G : Type*} [Group G]

@[expose] def bcRep (ρ : Representation K G V) : Representation k G (k ⊗[K] V) where
  toFun g := (ρ g).baseChange k
  map_one' := by
    rw [map_one]
    exact LinearMap.baseChange_one K V
  map_mul' g h := by
    rw [map_mul]
    exact LinearMap.baseChange_mul _ _

@[expose] def bcVec (v : V) : k ⊗[K] V := (1 : k) ⊗ₜ[K] v

variable {k}

theorem bcRep_bcVec (ρ : Representation K G V) (g : G) (v : V) :
    bcRep k ρ g (bcVec k v) = bcVec k (ρ g v) := rfl

theorem bcVec_injective : Function.Injective (bcVec (K := K) k (V := V)) := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K k)
    (LinearMap.ker_eq_bot.2 (algebraMap K k).injective)
  have key : ∀ v : V, (TensorProduct.lid K V) ((LinearMap.rTensor V π) (bcVec (K := K) k v)) = v := by
    intro v
    have h1 : π 1 = 1 := by simpa using LinearMap.congr_fun hπ 1
    simp [bcVec, TensorProduct.lid_tmul, h1]
  intro v w h
  have := congrArg (fun x => (TensorProduct.lid K V) ((LinearMap.rTensor V π) x)) h
  simpa [key] using this

theorem bcVec_smul (c : K) (v : V) :
    bcVec (K := K) k (c • v) = algebraMap K k c • bcVec (K := K) k v := by
  simp [bcVec, TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one, smul_tmul']

theorem bcVec_add (v w : V) : bcVec (K := K) k (v + w) = bcVec k v + bcVec k w := by
  simp [bcVec, TensorProduct.tmul_add]

theorem bcVec_ne_zero {v : V} (hv : v ≠ 0) : bcVec (K := K) k v ≠ 0 := by
  intro h
  exact hv (bcVec_injective (k := k) (by rw [h]; simp [bcVec]))

theorem bc_fix_line (ρ : Representation K G V) (T : Set G) (y : V)
    (hfix : ∀ x : V, (∀ u ∈ T, ρ u x = x) → ∃ c : K, x = c • y) (w : k ⊗[K] V)
    (hw : ∀ u ∈ T, bcRep k ρ u w = w) : ∃ l : k, w = l • bcVec k y := by
  classical
  let b := Module.Free.chooseBasis K k
  let e := TensorProduct.equivFinsuppOfBasisLeft (R := K) (N := V) b
  have hcomp : ∀ (f : V →ₗ[K] V) (x : k ⊗[K] V) (i), e (f.baseChange k x) i = f (e x i) := by
    intro f x i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      simp only [LinearMap.baseChange_tmul, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, e]
      exact (f.map_smul _ _).symm
    | add x y hx hy => simp [map_add, hx, hy]
  have hci : ∀ i, ∃ c : K, e w i = c • y := fun i => by
    refine hfix _ (fun u hu => ?_)
    have := congrArg (fun z => e z i) (hw u hu)
    simpa [bcRep, hcomp] using this
  choose c hc using hci
  refine ⟨∑ i ∈ (e w).support, c i • b i, ?_⟩
  have h1 : w = ∑ i ∈ (e w).support, b i ⊗ₜ[K] (e w i) := by
    have := e.symm_apply_apply w
    rw [show e.symm = (TensorProduct.equivFinsuppOfBasisLeft (R := K) (N := V) b).symm from rfl,
      TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum] at this
    exact this.symm
  conv_lhs => rw [h1]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc i]
  simp [bcVec, TensorProduct.tmul_smul, smul_tmul']

variable (k) in
theorem orbitSpan_bc (ρ : Representation K G V) (y : V) (h : orbitSpan ρ y = ⊤) :
    orbitSpan (bcRep k ρ) (bcVec k y) = ⊤ := by
  have h1 : ∀ v : V, bcVec k v ∈ orbitSpan (bcRep k ρ) (bcVec k y) := by
    intro v
    have hv : v ∈ orbitSpan ρ y := by rw [h]; trivial
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g, rfl⟩ := hv
      exact Submodule.subset_span ⟨g, rfl⟩
    | zero => simp [bcVec]
    | add a b _ _ ha hb => rw [bcVec_add]; exact add_mem ha hb
    | smul c a _ ha => rw [bcVec_smul]; exact Submodule.smul_mem _ _ ha
  refine (Submodule.eq_top_iff').2 fun w => ?_
  induction w using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a v =>
    have : a ⊗ₜ[K] v = a • bcVec k v := by simp [bcVec, smul_tmul']
    rw [this]
    exact Submodule.smul_mem _ a (h1 v)
  | add x y hx hy => exact add_mem hx hy

variable {B : Type*} {M : CoxeterMatrix B} {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ}
  (D : CurtisDatum G cs p)

theorem isSimpleRep_bc [Finite G] [Fact p.Prime] [CharP k p] (ρ : Representation K G V) (y : V)
    (hy : y ≠ 0) (hfix : ∀ x ∈ D.fixU ρ, ∃ c : K, x = c • y) (hgen : orbitSpan ρ y = ⊤) :
    IsSimpleRep (bcRep k ρ) := by
  have : Nontrivial (k ⊗[K] V) := ⟨⟨bcVec k y, 0, bcVec_ne_zero hy⟩⟩
  refine D.isSimpleRep_of_fixU (p := p) (bcRep k ρ) (y := bcVec k y) (fun x hx => ?_)
    (orbitSpan_bc k ρ y hgen)
  exact bc_fix_line ρ (D.U : Set G) y (fun z hz => hfix z hz) x ((D.mem_fixU _).1 hx)

theorem IsTypeGen.baseChange [Finite G] {ρ : Representation K G V} {y : V} {χ : G → K}
    {J : Finset B} {H' : Set G} {tor : B → Type*} {hh : ∀ s, tor s → G}
    (ht : IsTypeGen D ρ y χ J H' tor hh) :
    IsTypeGen D (bcRep k ρ) (bcVec k y) (fun g => algebraMap K k (χ g)) J H' tor hh := by
  obtain ⟨h1, h2, h3, h4⟩ := ht
  refine ⟨(D.mem_fixU _).2 fun u hu => ?_, bcVec_ne_zero h2, fun h hh' => ?_, fun s => ?_⟩
  · rw [bcRep_bcVec, (D.mem_fixU _).1 h1 u hu]
  · rw [bcRep_bcVec, h3 h hh', bcVec_smul]
  · rw [h4 s]
    refine and_congr ?_ ?_
    · exact forall_congr' fun u => (map_eq_one_iff (algebraMap K k)
        (algebraMap K k).injective).symm
    · have hT : D.heckeT (bcRep k ρ) s (bcVec k y) = bcVec k (D.heckeT ρ s y) := by
        have := Fintype.ofFinite (D.X s)
        rw [D.heckeT_apply, D.heckeT_apply]
        simp only [bcVec, tmul_sum]
        rfl
      rw [hT]
      constructor
      · intro h
        rw [h]; simp [bcVec]
      · intro h
        exact bcVec_injective (k := k) (by rw [h]; simp [bcVec])

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
