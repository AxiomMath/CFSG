module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInner
public import CFSG.LieType.SeitzGeneration.UnitaryNonabNonPth
public import CFSG.LieType.SeitzGeneration.UnitaryNonCube
public import CFSG.LieType.SeitzGeneration.UnitaryONExt
public import CFSG.LieType.SeitzGeneration.UnitaryNonabArith
public import CFSG.LieType.SeitzGeneration.UnitaryNonabPlane
public import CFSG.LieType.SeitzGeneration.UnitaryHeisTensorPair
public import CFSG.LieType.SeitzGeneration.ExcHigh.Leaves

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryAux

open Matrix CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.SeitzGeneration.Centers
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag

section Ext

variable {K : Type*} [Field K] {σ : K ≃+* K} {n m : ℕ}

theorem commute_ext_of_resMat (hσ : ∀ c, σ (σ c) = c) {x : Fin m → Fin n → K}
    (hx : ONExt.IsON σ x) {s : SUid σ n} (hs : ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d)
    (hs' : ∀ c, ∃ d, s⁻¹ • orthoEmb x c = orthoEmb x d) {g : SUid σ m}
    (hg : ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
        ONExt.resMat σ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ONExt.resMat σ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :
    s * ONExt.ext hσ hx g = ONExt.ext hσ hx g * s := by
  refine ext_smul σ fun v => ?_
  obtain ⟨c, u, hu, rfl⟩ := ONExt.exists_decomp hx v
  have hsu : ∀ i, herm σ (x i) (s • u) = 0 := by
    intro i
    obtain ⟨d, hd⟩ := hs' (Pi.single i 1)
    rw [ONExt.orthoEmb_single] at hd
    have h := herm_smul_smul σ s⁻¹ (x i) (s • u)
    rw [inv_smul_smul, hd] at h
    rw [← h]
    exact ONExt.herm_orthoEmb_of_orth x hu d
  have e1 : ONExt.ext hσ hx g • (orthoEmb x c + u) = orthoEmb x (g • c) + u := by
    rw [smul_add, ONExt.ext_smul_orthoEmb hσ hx, ONExt.ext_smul_of_orth hσ hx _ hu]
  have e2 : s • (orthoEmb x c + u) = orthoEmb x
      (ONExt.resMat σ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c) + s • u := by
    rw [smul_add, ONExt.orthoEmb_resMat_mulVec hx hs]
  rw [mul_smul, mul_smul, e1, e2, smul_add, smul_add, ← ONExt.orthoEmb_resMat_mulVec hx hs,
    ONExt.ext_smul_orthoEmb hσ hx, ONExt.ext_smul_of_orth hσ hx _ hsu]
  congr 2
  rw [smul_def, smul_def, mulVec_mulVec, mulVec_mulVec, hg]

theorem resMat_eq_smul_of_eigen {x : Fin m → Fin n → K} (hx : ONExt.IsON σ x)
    {s : SUid σ n} {lam : K} (hs : ∀ c, s • orthoEmb x c = lam • orthoEmb x c) :
    ONExt.resMat σ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = lam • 1 := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  apply ONExt.orthoEmb_injective hx
  rw [ONExt.orthoEmb_resMat_mulVec hx (fun c => ⟨lam • c, by rw [hs, map_smul]⟩), hs,
    Matrix.smul_mulVec, Matrix.one_mulVec, map_smul]

theorem resMat_smul_one {x : Fin m → Fin n → K} (hx : ONExt.IsON σ x) (c : K) :
    ONExt.resMat σ x (c • (1 : Matrix (Fin n) (Fin n) K)) = c • 1 := by
  rw [ONExt.resMat, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ONExt.coordMat_mul_colMat hx]

theorem resMat_mul_of {x : Fin m → Fin n → K} (hx : ONExt.IsON σ x) {s t : SUid σ n}
    (hs : ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d)
    (ht : ∀ c, ∃ d, t • orthoEmb x c = orthoEmb x d) :
    ONExt.resMat σ x (((s * t : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ONExt.resMat σ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ONExt.resMat σ x ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  ONExt.resMat_mul hx hs ht

@[expose] noncomputable def resGL {x : Fin m → Fin n → K} (hx : ONExt.IsON σ x) (s : SUid σ n)
    (hs : ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d)
    (hs' : ∀ c, ∃ d, s⁻¹ • orthoEmb x c = orthoEmb x d) : GL (Fin m) K where
  val := ONExt.resMat σ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  inv := ONExt.resMat σ x ((s⁻¹ : SUid σ n) : GL (Fin n) K)
  val_inv := by
    rw [← ONExt.resMat_mul hx hs hs', mul_inv_cancel, ONExt.resMat_one hx]
  inv_val := by
    rw [← ONExt.resMat_mul hx hs' hs, inv_mul_cancel, ONExt.resMat_one hx]

theorem coe_resGL {x : Fin m → Fin n → K} (hx : ONExt.IsON σ x) (s : SUid σ n)
    (hs : ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d)
    (hs' : ∀ c, ∃ d, s⁻¹ • orthoEmb x c = orthoEmb x d) :
    ((resGL hx s hs hs' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      ONExt.resMat σ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl

end Ext

section Hyper

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem mem_hyperClosure_of_comm (hp : p.Prime) {E : Subgroup G} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) {a b k : G} (haE : a ∈ E) (hbE : b ∈ E) (ha1 : a ≠ 1)
    (hb : b ∉ Subgroup.zpowers a) (hak : a * k = k * a) (hbk : b * k = k * b) :
    k ∈ hyperClosure p ⊤ E := by
  have hcent : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer {k} := by
    rw [Subgroup.closure_le]
    refine Set.insert_subset_iff.2 ⟨?_, Set.singleton_subset_iff.2 ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.2 hak
    · exact Subgroup.mem_centralizer_singleton_iff.2 hbk
  refine Subgroup.subset_closure ⟨Subgroup.mem_top _, Subgroup.closure ({a, b} : Set G),
    (Subgroup.closure_le E).2 (Set.insert_subset_iff.2 ⟨haE, Set.singleton_subset_iff.2 hbE⟩),
    relIndex_closure_pair_of_not_mem hp hE hcard haE hbE ha1 hb, fun z hz => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.1 (hcent hz)

end Hyper


section Block

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem mem_primeFormUnitary_of_herm (h : UnitaryFieldData ℓ f K) {m : ℕ} {g : GL (Fin m) K}
    (hg : ∀ u v, herm σ₀ ((g : Matrix (Fin m) (Fin m) K) *ᵥ u)
      ((g : Matrix (Fin m) (Fin m) K) *ᵥ v) = herm σ₀ u v) :
    g ∈ primeFormUnitary h (idGram K m) := by
  rw [← toLin_mem_sesqUnitaryGroup_iff, mem_sesqUnitaryGroup]
  intro u v
  rw [Nonsplit.idForm_eq_herm h, Nonsplit.idForm_eq_herm h]
  simpa [Matrix.toLin'_apply] using hg u v

theorem exists_orthoEmb_of_stable {σ : K ≃+* K} {m : ℕ} {x : Fin m → Fin n → K}
    {W : Submodule K (Fin n → K)} (hW : Submodule.span K (Set.range x) = W) {s : SUid σ n}
    (hs : ∀ v ∈ W, s • v ∈ W) (c : Fin m → K) : ∃ d, s • orthoEmb x c = orthoEmb x d := by
  have h1 : orthoEmb x c ∈ W := hW ▸ orthoEmb_mem_span x c
  have h2 := hs _ h1
  rw [← hW] at h2
  obtain ⟨d, hd⟩ := (mem_span_range_iff x _).1 h2
  exact ⟨d, hd.symm⟩

theorem allCenters_eigen (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) (hq2 : ℓ ^ f ≠ 2) {G : Type*} [Group G] [Finite G]
    (π : SUid σ₀ n →* G) {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    {x z y : SUid σ₀ n} (hxE : π x ∈ E) (hzE : π z ∈ E) (hyE : π y ∈ E) (hz1 : π z ≠ 1)
    (hxz : π x ∉ Subgroup.zpowers (π z)) (hyz : π y ∉ Subgroup.zpowers (π z))
    (hxy : x * y = y * x) (hxzc : x * z = z * x) (hyzc : y * z = z * y) {α μ ν : K}
    (hxp : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1)
    (hα : ¬ ∃ c : K, c ^ p = α) (hμ : μ ≠ 0)
    (hzp : ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (μ ^ p) • 1) (hν : ν ≠ 0)
    (hyp : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ν ^ p) • 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1) (j : Fin p) :
    AllCenters ((hyperClosure p ⊤ E).comap π)
      (Module.End.eigenspace (Matrix.toLin' ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (μ * ζ ^ (j : ℕ))) := by
  classical
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  set zm : Matrix (Fin n) (Fin n) K := ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hzm
  set xm : Matrix (Fin n) (Fin n) K := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hxm
  set ym : Matrix (Fin n) (Fin n) K := ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hym
  set V : Fin p → Submodule K (Fin n → K) :=
    fun i => Module.End.eigenspace (Matrix.toLin' zm) (μ * ζ ^ (i : ℕ)) with hV
  show AllCenters ((hyperClosure p ⊤ E).comap π) (V j)
  by_cases hU0 : V j = ⊥
  · intro v hv _
    rw [hU0, Submodule.mem_bot] at hv
    rw [hv]
    exact isCenter_zero
  have hmemV : ∀ i v, v ∈ V i ↔ zm *ᵥ v = (μ * ζ ^ (i : ℕ)) • v := fun i v => by
    rw [hV, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hzT3 : (Matrix.toLin' zm) ^ p = algebraMap K (Module.End K (Fin n → K)) (μ ^ p) := by
    have h2 := congrArg Matrix.toLinAlgEquiv' hzp
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hsup : ⨆ i, V i = ⊤ := NonPth.iSup_eigenspace_eq_top_p hp hpK hζ hμ hzT3
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exact absurd (Subsingleton.elim v₀ 0) hv₀0
    · exact h0
  have hzU : ∀ u w, herm σ₀ (zm *ᵥ u) (zm *ᵥ w) = herm σ₀ u w := fun u w =>
    herm_smul_smul σ₀ z u w
  have hμpN : h.bar (μ ^ p) * μ ^ p = 1 := by
    have hzpU : ∀ u w, herm σ₀ (zm ^ p *ᵥ u) (zm ^ p *ᵥ w) = herm σ₀ u w := by
      intro u w
      have := herm_smul_smul σ₀ (z ^ p) u w
      simpa [smul_def, Subgroup.coe_pow, Units.val_pow_eq_pow_val] using this
    have h1 := hzpU (Pi.single ⟨0, hn⟩ 1) (Pi.single ⟨0, hn⟩ 1)
    rw [hzp, Matrix.smul_mulVec, Matrix.one_mulVec, herm_smul_left, herm_smul_right,
      herm_single_left, map_one, one_mul, Pi.single_eq_same, mul_one] at h1
    rw [← hσb]
    simpa using h1
  have hμN : h.bar μ * μ = 1 :=
    bar_mul_eq_one_of_pow_eq h hp hp2 hpq hμ rfl (planeW_pow_card_succ h hμpN)
  have hlamN : ∀ k : ℕ, h.bar (μ * ζ ^ k) * (μ * ζ ^ k) = 1 := fun k => by
    rw [map_mul, map_pow]
    calc h.bar μ * h.bar ζ ^ k * (μ * ζ ^ k) = (h.bar μ * μ) * (h.bar ζ * ζ) ^ k := by ring
      _ = 1 := by rw [hμN, hζN, one_pow, one_mul]
  have hlam_ne : ∀ i i' : Fin p, i ≠ i' → h.bar (μ * ζ ^ (i : ℕ)) * (μ * ζ ^ (i' : ℕ)) ≠ 1 := by
    intro i i' hii he
    have key : μ * ζ ^ (i' : ℕ) = μ * ζ ^ (i : ℕ) := by
      linear_combination (-(μ * ζ ^ (i' : ℕ))) * hlamN i + (μ * ζ ^ (i : ℕ)) * he
    have h2 : ζ ^ (i' : ℕ) = ζ ^ (i : ℕ) := mul_left_cancel₀ hμ key
    exact hii (Fin.ext (hζ.pow_inj i'.2 i.2 h2).symm)
  set B := idForm h n with hBdef
  have hzB : ∀ u w, B (Matrix.toLin' zm u) (Matrix.toLin' zm w) = B u w := fun u w => by
    rw [hBdef, Nonsplit.idForm_eq_herm h, Nonsplit.idForm_eq_herm h, Matrix.toLin'_apply,
      Matrix.toLin'_apply]
    exact hzU u w
  have hV_orth : ∀ i i' : Fin p, i ≠ i' → ∀ u ∈ V i, ∀ v ∈ V i', B u v = 0 := by
    intro i i' hii u hu v hv
    exact NonCube.eigen_orthogonal hzB (hlam_ne i i' hii)
      (by rw [Matrix.toLin'_apply]; exact (hmemV i u).1 hu)
      (by rw [Matrix.toLin'_apply]; exact (hmemV i' v).1 hv)
  have hnd : (B.domRestrict₁₂ (V j) (V j)).SeparatingLeft :=
    NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n) V hV_orth hsup j
  have hcommM : ∀ a b : SUid σ₀ n, a * b = b * a →
      ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((b : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro a b hab
    have := congrArg (fun g : SUid σ₀ n => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hab
    simpa only [Subgroup.coe_mul, Units.val_mul] using this
  have hstab : ∀ s : SUid σ₀ n, s * z = z * s → ∀ v ∈ V j, s • v ∈ V j := by
    intro s hsz v hv
    rw [hmemV] at hv ⊢
    rw [smul_def, mulVec_mulVec, ← hcommM s z hsz, ← mulVec_mulVec, hv, mulVec_smul]
  have hinv : ∀ s : SUid σ₀ n, s * z = z * s → s⁻¹ * z = z * s⁻¹ := by
    intro s hsz
    exact (Commute.inv_left hsz).eq
  have hxT3 : (Matrix.toLin' xm) ^ p = algebraMap K (Module.End K (Fin n → K)) α := by
    have h2 := congrArg Matrix.toLinAlgEquiv' hxp
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hdim : p ≤ Module.finrank K (V j) :=
    NonPth.p_le_finrank_of_stable hp hxT3 hα (fun s hs => by
      rw [Matrix.toLin'_apply]; exact hstab x hxzc s hs) hU0
  have hON : HasONBasis σ₀ (V j) := by
    refine Nonsplit.hasONBasis_of_separatingLeft h (V j) hnd ?_
    rcases Nat.lt_or_ge p 4 with hp4 | hp4
    · obtain ⟨s, hs0, hs1⟩ := Nonsplit.exists_norm_ne_one h hq2
      exact Or.inr ⟨by have := hp.two_le; omega, s, hs0, by rw [hσb]; exact hs1⟩
    · exact Or.inl (by omega)
  obtain ⟨m, xs, hxs, hspan, -⟩ := hON
  have hxsON : ONExt.IsON σ₀ xs := hxs
  have hsU : ∀ s : SUid σ₀ n, s * z = z * s → ∀ c, ∃ d, s • orthoEmb xs c = orthoEmb xs d :=
    fun s hsz => exists_orthoEmb_of_stable hspan (hstab s hsz)
  have hsU' : ∀ s : SUid σ₀ n, s * z = z * s → ∀ c, ∃ d, s⁻¹ • orthoEmb xs c = orthoEmb xs d :=
    fun s hsz => exists_orthoEmb_of_stable hspan (hstab s⁻¹ (hinv s hsz))
  have hzlam : ∀ c, z • orthoEmb xs c = (μ * ζ ^ (j : ℕ)) • orthoEmb xs c := by
    intro c
    have h1 : orthoEmb xs c ∈ V j := hspan ▸ orthoEmb_mem_span xs c
    exact (hmemV j _).1 h1
  have hzres : ONExt.resMat σ₀ xs zm = (μ * ζ ^ (j : ℕ)) • 1 :=
    resMat_eq_smul_of_eigen hxsON hzlam
  have hzz : z * z = z * z := rfl
  set H := (hyperClosure p ⊤ E).comap π with hH
  set ε := ONExt.ext hσ.invol hxsON with hε
  set HU := H.comap ε with hHU
  have hcentU : ∀ s : SUid σ₀ n, s * z = z * s → π s ∈ E → π s ∉ Subgroup.zpowers (π z) →
      HeisTensor.Cent HU (ONExt.resMat σ₀ xs ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    intro s hsz hsE hs g hg
    have h1 : s * ε g = ε g * s :=
      commute_ext_of_resMat hσ.invol hxsON (hsU s hsz) (hsU' s hsz) hg
    have h2 : z * ε g = ε g * z := by
      refine commute_ext_of_resMat hσ.invol hxsON (hsU z hzz) (hsU' z hzz) ?_
      rw [hzres, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
    show π (ε g) ∈ hyperClosure p ⊤ E
    refine mem_hyperClosure_of_comm hp hE hcard hzE hsE hz1 hs ?_ ?_
    · rw [← map_mul, ← map_mul, h2]
    · rw [← map_mul, ← map_mul, h1]
  have hXmem : ∀ s : SUid σ₀ n, ∀ (hs : ∀ c, ∃ d, s • orthoEmb xs c = orthoEmb xs d)
      (hs' : ∀ c, ∃ d, s⁻¹ • orthoEmb xs c = orthoEmb xs d),
      resGL hxsON s hs hs' ∈ primeFormUnitary h (idGram K m) := by
    intro s hs hs'
    refine mem_primeFormUnitary_of_herm h fun u v => ?_
    rw [coe_resGL]
    exact ONExt.herm_resMat hxsON hs u v
  have hpowres : ∀ s : SUid σ₀ n, ∀ (hs : ∀ c, ∃ d, s • orthoEmb xs c = orthoEmb xs d) {β : K},
      ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1 →
      (ONExt.resMat σ₀ xs ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ p = β • 1 := by
    intro s hs β hβ
    rw [← ONExt.resMat_pow hxsON hs p]
    have : (((s ^ p : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = β • 1 := by
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hβ]
    rw [this, resMat_smul_one hxsON]
  set X := resGL hxsON x (hsU x hxzc) (hsU' x hxzc) with hX
  set Y := resGL hxsON y (hsU y hyzc) (hsU' y hyzc) with hY
  have hXG : X ∈ primeFormUnitary h (idGram K m) := hXmem x _ _
  have hYG : Y ∈ primeFormUnitary h (idGram K m) := hXmem y _ _
  have hXp : ((X ^ p : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = α • 1 := by
    rw [Units.val_pow_eq_pow_val, hX, coe_resGL]
    exact hpowres x (hsU x hxzc) hxp
  have hYp : ((Y ^ p : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = (ν ^ p) • 1 := by
    rw [Units.val_pow_eq_pow_val, hY, coe_resGL]
    exact hpowres y (hsU y hyzc) hyp
  have hXY : X * Y = Y * X := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hX, hY, coe_resGL, coe_resGL,
      ← resMat_mul_of hxsON (hsU x hxzc) (hsU y hyzc),
      ← resMat_mul_of hxsON (hsU y hyzc) (hsU x hxzc), hxy]
  have hCX : HeisTensor.Cent HU ((X : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) :=
    hcentU x hxzc hxE hxz
  have hCY : HeisTensor.Cent HU ((Y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) :=
    hcentU y hyzc hyE hyz
  have htop : HU = ⊤ := by
    by_cases hYs : ∃ c : K, ((Y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = c • 1
    · obtain ⟨c, hc⟩ := hYs
      rw [eq_top_iff]
      intro g _
      apply hCY g
      rw [hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
    push Not at hYs
    have hνpN : h.bar (ν ^ p) * ν ^ p = 1 := bar_mul_eq_one_of_scalar_pow h
      (by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · exfalso
          subst h0
          exact hYs 0 (Subsingleton.elim _ _)
        · exact h0) hYG hYp
    have hνN : h.bar ν * ν = 1 :=
      bar_mul_eq_one_of_pow_eq h hp hp2 hpq hν rfl (planeW_pow_card_succ h hνpN)
    rcases Nat.lt_or_ge p 5 with hp5 | hp5
    ·
      have hp3 : p = 3 := by
        have := hp.two_le
        interval_cases p
        · exact absurd rfl hp2
        · rfl
        · exact absurd hp (by decide)
      subst hp3
      exact NonCube.eq_top_of_noncube_pair h hq2 hXG hYG hXY hXp hα hYp hν hνN
        hζ.pow_eq_one (hζ.ne_one (by norm_num)) hζN hYs hCX hCY
    ·
      have hν'N : h.bar ν⁻¹ * ν⁻¹ = 1 := by
        rw [map_inv₀, ← mul_inv, hνN, inv_one]
      set Y' : GL (Fin m) K :=
        Matrix.GeneralLinearGroup.scalar (Fin m) (Units.mk0 ν⁻¹ (inv_ne_zero hν)) * Y with hY'
      have hY'M : ((Y' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
          ν⁻¹ • ((Y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
        rw [hY', Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          Units.val_mk0, ← Matrix.smul_eq_diagonal_mul]
      have hY'G : Y' ∈ primeFormUnitary h (idGram K m) :=
        Subgroup.mul_mem _ (planeW_scalar_mem h (inv_ne_zero hν) hν'N) hYG
      have hY'p : ((Y' ^ p : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 := by
        rw [Units.val_pow_eq_pow_val, hY'M, smul_pow, ← Units.val_pow_eq_pow_val, hYp,
          smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hν), one_smul]
      have hXY' : X * Y' = Y' * X := by
        apply Units.ext
        show ((X : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) * ((Y' : GL (Fin m) K) :
            Matrix (Fin m) (Fin m) K) = ((Y' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
              ((X : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)
        rw [hY'M, Matrix.mul_smul, Matrix.smul_mul]
        congr 1
        rw [← Units.val_mul, ← Units.val_mul, hXY]
      have hY'1 : ∀ c : K, ((Y' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ≠ c • 1 := by
        intro c hc
        apply hYs (ν * c)
        rw [hY'M] at hc
        calc ((Y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)
            = ν • (ν⁻¹ • ((Y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) := by
              rw [smul_smul, mul_inv_cancel₀ hν, one_smul]
          _ = (ν * c) • 1 := by rw [hc, smul_smul]
      have hCY' : HeisTensor.Cent HU ((Y' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
        rw [hY'M]
        exact HeisTensor.Cent.smul hCY (inv_ne_zero hν)
      exact NonPth.eq_top_of_nonpth_pair h hp hp5 hpq hXG hY'G hXY' hXp hα hY'p hY'1 hCX hCY'
  have hall : ∀ g, ε g ∈ H := fun g => by
    have : g ∈ HU := by rw [htop]; exact Subgroup.mem_top g
    exact this
  rw [← hspan]
  exact ONExt.allCenters_of_forall_ext_mem hσ.invol hxsON hall

end Block


section Lines

theorem pth_power_of_pow_coprime {K : Type} [Field K] {p : ℕ} (hp : p.Prime) {β s : K}
    (hβ : β ≠ 0) {b : ℕ} (hb : ¬ p ∣ b) (hs : β ^ b = s ^ p) : ∃ t : K, t ^ p = β := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hb).symm hp.one_lt
  obtain ⟨k, hk⟩ : ∃ k : ℕ, b * m = p * k + 1 :=
    ⟨b * m / p, by have h1 := Nat.div_add_mod (b * m) p; rw [hm] at h1; exact h1.symm⟩
  have hpow : β ^ (b * m) = (s ^ m) ^ p := by
    rw [pow_mul, hs, ← pow_mul, ← pow_mul, mul_comm]
  have hpow2 : β ^ (b * m) = (β ^ k) ^ p * β := by
    rw [hk, pow_succ, pow_mul']
  have key : (β ^ k) ^ p * β = (s ^ m) ^ p := hpow2.symm.trans hpow
  have hne : (β ^ k) ^ p ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hβ)
  refine ⟨s ^ m * (β ^ k)⁻¹, ?_⟩
  rw [mul_pow, inv_pow, ← key, mul_comm ((β ^ k) ^ p) β, mul_assoc, mul_inv_cancel₀ hne,
    mul_one]

theorem mem_of_pow_mem {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {S : Subgroup G} {e : G}
    (he : e ^ p = 1) {b : ℕ} (hb : ¬ p ∣ b) (h : e ^ b ∈ S) : e ∈ S := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hb).symm hp.one_lt
  have key : e = (e ^ b) ^ m := by
    rw [← pow_mul, ← Nat.mod_add_div (b * m) p, hm, pow_add, pow_one, pow_mul, he, one_pow,
      mul_one]
  rw [key]
  exact S.pow_mem h m

theorem exists_not_mem_of_card {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E S : Subgroup G} (hcard : Nat.card E = p ^ 3) {k : ℕ} (hk : k < 3)
    (hS : Nat.card S = p ^ k) : ∃ e ∈ E, e ∉ S := by
  by_contra hcon
  push Not at hcon
  have hle : E ≤ S := hcon
  have h1 := Subgroup.card_le_of_le hle
  rw [hcard, hS] at h1
  have := Nat.pow_lt_pow_right hp.one_lt hk
  omega

theorem dvd_of_pow_mul_pow_eq_one {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {u w : G}
    (hu : u ^ p = 1) (hw : w ^ p = 1) (hu1 : u ≠ 1) (hwu : w ∉ Subgroup.zpowers u) {a b : ℕ}
    (hab : u ^ a * w ^ b = 1) : p ∣ a ∧ p ∣ b := by
  have hfp : Fact p.Prime := ⟨hp⟩
  by_cases hb : p ∣ b
  · obtain ⟨t, rfl⟩ := hb
    rw [pow_mul, hw, one_pow, mul_one] at hab
    refine ⟨?_, dvd_mul_right p t⟩
    rw [← orderOf_eq_prime hu hu1]
    exact orderOf_dvd_of_pow_eq_one hab
  · exfalso
    apply hwu
    refine mem_of_pow_mem hp hw hb ?_
    have : w ^ b = (u ^ a)⁻¹ := eq_inv_of_mul_eq_one_right hab
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers u a)

end Lines

section Joint

theorem eigenspace_le_iSup_inf {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {A B : Module.End K V} (hAB : A * B = B * A) {ν : K} (hν : ν ≠ 0)
    (hB : B ^ p = algebraMap K (Module.End K V) (ν ^ p)) (a : K) :
    A.eigenspace a ≤ ⨆ j : Fin p, A.eigenspace a ⊓ B.eigenspace (ν * ζ ^ (j : ℕ)) := by
  set W := A.eigenspace a with hW
  have hBW : ∀ v ∈ W, B v ∈ W := by
    intro v hv
    rw [hW, Module.End.mem_eigenspace_iff] at hv ⊢
    have := congrArg (fun T : Module.End K V => T v) hAB
    simp only [Module.End.mul_apply] at this
    rw [this, hv, map_smul]
  have hB' : (B.restrict hBW) ^ p = algebraMap K (Module.End K W) (ν ^ p) := by
    rw [Module.End.pow_restrict]
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    rw [LinearMap.restrict_coe_apply, hB]
    simp [Algebra.algebraMap_eq_smul_one]
  have hsupB := NonPth.iSup_eigenspace_eq_top_p hp hpK hζ hν hB'
  calc W = (⊤ : Submodule K W).map W.subtype := (Submodule.map_subtype_top W).symm
    _ = ⨆ j : Fin p, (Module.End.eigenspace (B.restrict hBW) (ν * ζ ^ (j : ℕ))).map
        W.subtype := by
        rw [← hsupB, Submodule.map_iSup]
    _ ≤ ⨆ j : Fin p, W ⊓ B.eigenspace (ν * ζ ^ (j : ℕ)) := by
        refine iSup_mono fun j => le_inf ?_ (Module.End.eigenspace_restrict_le_eigenspace B hBW _)
        rintro _ ⟨w, -, rfl⟩
        exact w.2

theorem finrank_iSup_le_sum {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type*} [Fintype ι] (W : ι → Submodule K V) :
    Module.finrank K (⨆ i, W i : Submodule K V) ≤ ∑ i, Module.finrank K (W i) := by
  classical
  have key : ∀ s : Finset ι, Module.finrank K (⨆ i ∈ s, W i : Submodule K V) ≤
      ∑ i ∈ s, Module.finrank K (W i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.iSup_insert, Finset.sum_insert hi]
      exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (by omega)
  have := key Finset.univ
  have e : (⨆ i ∈ (Finset.univ : Finset ι), W i : Submodule K V) = ⨆ i, W i := by
    simp only [Finset.mem_univ, iSup_pos]
  rwa [e] at this

theorem iSup_inf_eigenspace_eq_top {K : Type} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {A B : Module.End K V} (hAB : A * B = B * A) {ν₁ ν₂ : K} (hν₁ : ν₁ ≠ 0) (hν₂ : ν₂ ≠ 0)
    (hA : A ^ p = algebraMap K (Module.End K V) (ν₁ ^ p))
    (hB : B ^ p = algebraMap K (Module.End K V) (ν₂ ^ p)) :
    ⨆ ij : Fin p × Fin p, A.eigenspace (ν₁ * ζ ^ (ij.1 : ℕ)) ⊓
      B.eigenspace (ν₂ * ζ ^ (ij.2 : ℕ)) = ⊤ := by
  have hsupA := NonPth.iSup_eigenspace_eq_top_p hp hpK hζ hν₁ hA
  rw [eq_top_iff, ← hsupA, iSup_prod]
  refine iSup_le fun i => ?_
  set W := A.eigenspace (ν₁ * ζ ^ (i : ℕ)) with hW
  have hBW : ∀ v ∈ W, B v ∈ W := by
    intro v hv
    rw [hW, Module.End.mem_eigenspace_iff] at hv ⊢
    have := congrArg (fun T : Module.End K V => T v) hAB
    simp only [Module.End.mul_apply] at this
    rw [this, hv, map_smul]
  have hB' : (B.restrict hBW) ^ p = algebraMap K (Module.End K W) (ν₂ ^ p) := by
    rw [Module.End.pow_restrict]
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    rw [LinearMap.restrict_coe_apply, hB]
    simp [Algebra.algebraMap_eq_smul_one]
  have hsupB := NonPth.iSup_eigenspace_eq_top_p hp hpK hζ hν₂ hB'
  calc W = (⊤ : Submodule K W).map W.subtype := (Submodule.map_subtype_top W).symm
    _ = ⨆ j : Fin p, (Module.End.eigenspace (B.restrict hBW) (ν₂ * ζ ^ (j : ℕ))).map
        W.subtype := by
        rw [← hsupB, Submodule.map_iSup]
    _ ≤ ⨆ j : Fin p, W ⊓ B.eigenspace (ν₂ * ζ ^ (j : ℕ)) := by
        refine iSup_mono fun j => le_inf ?_ (Module.End.eigenspace_restrict_le_eigenspace B hBW _)
        rintro _ ⟨w, -, rfl⟩
        exact w.2
    _ ≤ _ := le_iSup_of_le i (iSup_mono fun j => le_rfl)

end Joint


section Choice

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem scalar_ne_zero_of_matPow {m : ℕ} (hm : 0 < m) {g : GL (Fin m) K} {k : ℕ} {β : K}
    (hg : ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ^ k = β • 1) : β ≠ 0 := by
  rintro rfl
  have h1 : (((g ^ k : GL (Fin m) K) * (g ^ k)⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      1 := by
    rw [mul_inv_cancel, Units.val_one]
  rw [Units.val_mul, Units.val_pow_eq_pow_val, hg, zero_smul, Matrix.zero_mul] at h1
  have := congrFun (congrFun h1 ⟨0, hm⟩) ⟨0, hm⟩
  simp at this

theorem coe_pow_mul_pow (x s : SUid σ₀ n) (a b : ℕ) :
    (((x ^ a * s ^ b : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ a *
        ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ b := by
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val]

theorem coe_comm {x s : SUid σ₀ n} (hxs : x * s = s * x) :
    ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((s : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have := congrArg (fun g : SUid σ₀ n => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hxs
  simpa only [Subgroup.coe_mul, Units.val_mul] using this

theorem pow_word_of_comm {x s : SUid σ₀ n} (hxs : x * s = s * x) {α β : K}
    (hxp : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1)
    (hsp : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1) (a b : ℕ) :
    (((x ^ a * s ^ b : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p =
      (α ^ a * β ^ b) • 1 := by
  have hc : Commute ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := coe_comm hxs
  rw [coe_pow_mul_pow, (hc.pow_pow a b).mul_pow, ← pow_mul, ← pow_mul, mul_comm a p,
    mul_comm b p, pow_mul, pow_mul, hxp, hsp, smul_pow, smul_pow, one_pow, one_pow,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]

theorem exists_pth_word (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hn : 0 < n) {G : Type*}
    [Group G] (π : SUid σ₀ n →* G)
    (hker : ∀ g ∈ π.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    {E : Subgroup G} (hE : IsElemAbelian p E) {x s : SUid σ₀ n} (hxs : x * s = s * x) {α : K}
    (hα0 : α ≠ 0) (hxp : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1)
    (hα : ¬ ∃ c : K, c ^ p = α) (hsE : π s ∈ E) :
    ∃ a b : ℕ, ¬ p ∣ b ∧ ∃ ν : K, ν ≠ 0 ∧
      (((x ^ a * s ^ b : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p =
        (ν ^ p) • 1 := by
  have hsp : π (s ^ p) = 1 := by rw [map_pow]; exact hE.2 _ hsE
  obtain ⟨β, hβ⟩ := hker (s ^ p) hsp
  have hβ' : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1 := by
    rw [← hβ, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hβ0 : β ≠ 0 := scalar_ne_zero_of_matPow hn hβ'
  obtain ⟨a, b, hab, ν, hν⟩ := exists_pth_power_word hp hpK hα0 hβ0
  have hb : ¬ p ∣ b := by
    rintro ⟨t, rfl⟩
    have hpa : ¬ p ∣ a := fun hpa => hab ⟨hpa, dvd_mul_right p t⟩
    apply hα
    refine pth_power_of_pow_coprime hp hα0 hpa (s := ν * (β ^ t)⁻¹) ?_
    rw [mul_pow, inv_pow, ← pow_mul, hν, mul_comm t p, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hβ0), mul_one]
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hν
    exact mul_ne_zero (pow_ne_zero _ hα0) (pow_ne_zero _ hβ0) hν.symm
  exact ⟨a, b, hb, ν, hν0, by rw [pow_word_of_comm hxs hxp hβ' a b, ← hν]⟩

theorem exists_pth_lines (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hn : 0 < n) {G : Type*}
    [Group G] [Finite G] (π : SUid σ₀ n →* G) (hπ : Function.Surjective π)
    (hker : ∀ g ∈ π.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hcomm : ∀ a b : SUid σ₀ n, π a ∈ E → π b ∈ E → a * b = b * a)
    {x : SUid σ₀ n} (hxE : π x ∈ E) (hx1 : π x ≠ 1) {α : K} (hα0 : α ≠ 0)
    (hxp : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1)
    (hα : ¬ ∃ c : K, c ^ p = α) :
    ∃ y₁ y₂ : SUid σ₀ n, π y₁ ∈ E ∧ π y₂ ∈ E ∧ π y₁ ≠ 1 ∧ π y₂ ∉ Subgroup.zpowers (π y₁) ∧
      π x ∉ Subgroup.closure ({π y₁, π y₂} : Set G) ∧ ∃ ν₁ ν₂ : K, ν₁ ≠ 0 ∧ ν₂ ≠ 0 ∧
        ((y₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ν₁ ^ p) • 1 ∧
        ((y₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ν₂ ^ p) • 1 := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hexp : ∀ e ∈ E, e ^ p = 1 := hE.2
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hox : orderOf (π x) = p := orderOf_eq_prime (hexp _ hxE) hx1
  obtain ⟨e₁, he₁E, he₁⟩ := exists_not_mem_of_card hp (S := Subgroup.zpowers (π x)) hcard
    (k := 1) (by norm_num) (by rw [Nat.card_zpowers, hox, pow_one])
  obtain ⟨s₁, rfl⟩ := hπ e₁
  obtain ⟨a₁, b₁, hb₁, ν₁, hν₁, hy₁⟩ :=
    exists_pth_word hp hpK hn π hker hE (hcomm x s₁ hxE he₁E) hα0 hxp hα he₁E
  set y₁ := x ^ a₁ * s₁ ^ b₁ with hy₁def
  have hy₁E : π y₁ ∈ E := by
    rw [hy₁def, map_mul, map_pow, map_pow]
    exact E.mul_mem (E.pow_mem hxE _) (E.pow_mem he₁E _)
  have hy₁x : π y₁ ∉ Subgroup.zpowers (π x) := by
    intro hmem
    apply he₁
    refine mem_of_pow_mem hp (hexp _ he₁E) hb₁ ?_
    have : (π s₁) ^ b₁ = ((π x) ^ a₁)⁻¹ * π y₁ := by
      rw [hy₁def, map_mul, map_pow, map_pow, inv_mul_cancel_left]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ _)) hmem
  have hy₁1 : π y₁ ≠ 1 := fun h1 => hy₁x (h1 ▸ Subgroup.one_mem _)
  have hc2 : Nat.card (Subgroup.closure ({π x, π y₁} : Set G)) = p ^ 2 :=
    card_closure_pair_of_not_mem hp hE hxE hy₁E hx1 hy₁x
  obtain ⟨e₂, he₂E, he₂⟩ := exists_not_mem_of_card hp hcard (k := 2) (by norm_num) hc2
  obtain ⟨s₂, rfl⟩ := hπ e₂
  obtain ⟨a₂, b₂, hb₂, ν₂, hν₂, hy₂⟩ :=
    exists_pth_word hp hpK hn π hker hE (hcomm x s₂ hxE he₂E) hα0 hxp hα he₂E
  set y₂ := x ^ a₂ * s₂ ^ b₂ with hy₂def
  have hy₂E : π y₂ ∈ E := by
    rw [hy₂def, map_mul, map_pow, map_pow]
    exact E.mul_mem (E.pow_mem hxE _) (E.pow_mem he₂E _)
  have hxcl : π x ∈ Subgroup.closure ({π x, π y₁} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hy₁cl : π y₁ ∈ Subgroup.closure ({π x, π y₁} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hy₂cl : π y₂ ∉ Subgroup.closure ({π x, π y₁} : Set G) := by
    intro hmem
    apply he₂
    refine mem_of_pow_mem hp (hexp _ he₂E) hb₂ ?_
    have : (π s₂) ^ b₂ = ((π x) ^ a₂)⁻¹ * π y₂ := by
      rw [hy₂def, map_mul, map_pow, map_pow, inv_mul_cancel_left]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hxcl _)) hmem
  have hy₂y₁ : π y₂ ∉ Subgroup.zpowers (π y₁) := fun hmem =>
    hy₂cl (Subgroup.zpowers_le.2 hy₁cl hmem)
  refine ⟨y₁, y₂, hy₁E, hy₂E, hy₁1, hy₂y₁, ?_, ν₁, ν₂, hν₁, hν₂, hy₁, hy₂⟩
  intro hxmem
  have hc2' : Nat.card (Subgroup.closure ({π y₁, π y₂} : Set G)) = p ^ 2 :=
    card_closure_pair_of_not_mem hp hE hy₁E hy₂E hy₁1 hy₂y₁
  have hle : Subgroup.closure ({π x, π y₁} : Set G) ≤ Subgroup.closure ({π y₁, π y₂} : Set G) :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hxmem, Set.singleton_subset_iff.2
      (Subgroup.subset_closure (Set.mem_insert _ _))⟩)
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hc2, hc2'])
  exact hy₂cl (heq ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

end Choice


section Norms

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem dvd_card_sub_one_of_unitary (h : UnitaryFieldData ℓ f K) (hpq : p ∣ ℓ ^ f + 1) :
    p ∣ Nat.card K - 1 := by
  rw [UnitaryFieldData.card_eq_sq h]
  obtain ⟨m, hm⟩ : ∃ m, ℓ ^ f = m + 1 :=
    ⟨ℓ ^ f - 1, by have := pow_pos h.prime.pos f; omega⟩
  rw [hm] at hpq ⊢
  have hsq : (m + 1) ^ 2 - 1 = (m + 1 + 1) * m := Nat.sub_eq_of_eq_add (by ring)
  rw [hsq]
  exact Dvd.dvd.mul_right hpq m

theorem bar_mul_eq_one_of_SUid_pow (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) (hn : 0 < n) {s : SUid σ₀ n} {ν : K} (hν : ν ≠ 0)
    (hsp : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ν ^ p) • 1) :
    h.bar ν * ν = 1 := by
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have hνpN : h.bar (ν ^ p) * ν ^ p = 1 := by
    have h1 := herm_smul_smul σ₀ (s ^ p) (Pi.single ⟨0, hn⟩ 1) (Pi.single ⟨0, hn⟩ 1)
    rw [smul_def, Subgroup.coe_pow, Units.val_pow_eq_pow_val, hsp, Matrix.smul_mulVec,
      Matrix.one_mulVec, herm_smul_left, herm_smul_right, herm_single_left, map_one, one_mul,
      Pi.single_eq_same, mul_one] at h1
    rw [← hσb]
    simpa using h1
  exact bar_mul_eq_one_of_pow_eq h hp hp2 hpq hν rfl (planeW_pow_card_succ h hνpN)

theorem bar_mul_ne_one (h : UnitaryFieldData ℓ f K) {ν ζ : K} (hν : ν ≠ 0)
    (hνN : h.bar ν * ν = 1) (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1) {i i' : Fin p}
    (hii : i ≠ i') : σ₀ (ν * ζ ^ (i : ℕ)) * (ν * ζ ^ (i' : ℕ)) ≠ 1 := by
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  rw [hσb]
  have hlamN : ∀ k : ℕ, h.bar (ν * ζ ^ k) * (ν * ζ ^ k) = 1 := fun k => by
    rw [map_mul, map_pow]
    calc h.bar ν * h.bar ζ ^ k * (ν * ζ ^ k) = (h.bar ν * ν) * (h.bar ζ * ζ) ^ k := by ring
      _ = 1 := by rw [hνN, hζN, one_pow, one_mul]
  intro he
  have key : ν * ζ ^ (i' : ℕ) = ν * ζ ^ (i : ℕ) := by
    linear_combination (-(ν * ζ ^ (i' : ℕ))) * hlamN i + (ν * ζ ^ (i : ℕ)) * he
  have h2 : ζ ^ (i' : ℕ) = ζ ^ (i : ℕ) := mul_left_cancel₀ hν key
  exact hii (Fin.ext (hζ.pow_inj i'.2 i.2 h2).symm)

theorem herm_eq_zero_of_eigen {σ : K ≃+* K} {s : SUid σ n} {u v : Fin n → K} {l₁ l₂ : K}
    (hu : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u = l₁ • u)
    (hv : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = l₂ • v)
    (hl : σ l₁ * l₂ ≠ 1) : herm σ u v = 0 := by
  have h1 := herm_smul_smul σ s u v
  rw [smul_def, smul_def, hu, hv, herm_smul_left, herm_smul_right] at h1
  have h2 : (σ l₁ * l₂ - 1) * herm σ u v = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (sub_eq_zero.1 h3) hl
  · exact h3

theorem pow_eq_pow_mod {ζ : K} (hζ : IsPrimitiveRoot ζ p) (N : ℕ) : ζ ^ N = ζ ^ (N % p) := by
  conv_lhs => rw [← Nat.mod_add_div N p, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

end Norms

section CaseB

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem hyperGen_of_nonpth (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) (hq2 : ℓ ^ f ≠ 2) (hn : 0 < n) {G : Type*} [Group G] [Finite G]
    (π : SUid σ₀ n →* G) (hπ : Function.Surjective π)
    (hker : ∀ g ∈ π.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    (hker' : ∀ g : SUid σ₀ n, (∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) →
      π g = 1)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hcomm : ∀ a b : SUid σ₀ n, π a ∈ E → π b ∈ E → a * b = b * a)
    {x : SUid σ₀ n} (hxE : π x ∈ E) {α : K}
    (hxp : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1)
    (hα : ¬ ∃ c : K, c ^ p = α) :
    HyperGen p (⊤ : Subgroup G) E := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have hpK1 : p ∣ Nat.card K - 1 := dvd_card_sub_one_of_unitary h hpq
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hα ⟨0, zero_pow hp.ne_zero⟩
  have hx1 : π x ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := hker x h1
    apply hα
    refine ⟨c, ?_⟩
    rw [hc, smul_pow, one_pow] at hxp
    have := congrFun (congrFun hxp ⟨0, hn⟩) ⟨0, hn⟩
    simpa using this
  obtain ⟨ζ, hζ, hζN⟩ := NonPth.exists_primitive_prime_root_bar h hp hpq
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  obtain ⟨y₁, y₂, hy₁E, hy₂E, hy₁1, hy₂y₁, hxcl, ν₁, ν₂, hν₁, hν₂, hy₁p, hy₂p⟩ :=
    exists_pth_lines hp hpK1 hn π hπ hker hE hcard hcomm hxE hx1 hα0 hxp hα
  have hexp : ∀ e ∈ E, e ^ p = 1 := hE.2
  have hxy₁ : x * y₁ = y₁ * x := hcomm x y₁ hxE hy₁E
  have hxy₂ : x * y₂ = y₂ * x := hcomm x y₂ hxE hy₂E
  have hy₁y₂ : y₁ * y₂ = y₂ * y₁ := hcomm y₁ y₂ hy₁E hy₂E
  have hν₁N := bar_mul_eq_one_of_SUid_pow h hp hp2 hpq hn hν₁ hy₁p
  have hν₂N := bar_mul_eq_one_of_SUid_pow h hp hp2 hpq hn hν₂ hy₂p
  have hy₁cl : π y₁ ∈ Subgroup.closure ({π y₁, π y₂} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hy₂cl : π y₂ ∈ Subgroup.closure ({π y₁, π y₂} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hc2 : Nat.card (Subgroup.closure ({π y₁, π y₂} : Set G)) = p ^ 2 :=
    card_closure_pair_of_not_mem hp hE hy₁E hy₂E hy₁1 hy₂y₁
  set H := (hyperClosure p ⊤ E).comap π with hH
  set xm : Matrix (Fin n) (Fin n) K := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hxm
  set y₁m : Matrix (Fin n) (Fin n) K := ((y₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hy₁m
  set y₂m : Matrix (Fin n) (Fin n) K := ((y₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hy₂m
  have hpowT : ∀ (M : Matrix (Fin n) (Fin n) K) (c : K), M ^ p = c • 1 →
      (Matrix.toLin' M) ^ p = algebraMap K (Module.End K (Fin n → K)) c := by
    intro M c hM
    have h2 := congrArg Matrix.toLinAlgEquiv' hM
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  set W : Fin p × Fin p → Submodule K (Fin n → K) := fun ij =>
    Module.End.eigenspace (Matrix.toLin' y₁m) (ν₁ * ζ ^ (ij.1 : ℕ)) ⊓
      Module.End.eigenspace (Matrix.toLin' y₂m) (ν₂ * ζ ^ (ij.2 : ℕ)) with hW
  have hWtop : ⨆ ij, W ij = ⊤ := by
    refine iSup_inf_eigenspace_eq_top hp hpK hζ ?_ hν₁ hν₂ (hpowT _ _ hy₁p) (hpowT _ _ hy₂p)
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, Module.End.mul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, mulVec_mulVec, coe_comm hy₁y₂]
  have hmemW : ∀ ij v, v ∈ W ij ↔ y₁m *ᵥ v = (ν₁ * ζ ^ (ij.1 : ℕ)) • v ∧
      y₂m *ᵥ v = (ν₂ * ζ ^ (ij.2 : ℕ)) • v := by
    intro ij v
    rw [hW, Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff,
      Matrix.toLin'_apply, Matrix.toLin'_apply]
  have hW_orth : ∀ ij ij' : Fin p × Fin p, ij ≠ ij' → ∀ u ∈ W ij, ∀ v ∈ W ij',
      herm σ₀ u v = 0 := by
    intro ij ij' hne u hu v hv
    rw [hmemW] at hu hv
    by_cases h1 : ij.1 = ij'.1
    · have h2 : ij.2 ≠ ij'.2 := fun h2 => hne (Prod.ext h1 h2)
      exact herm_eq_zero_of_eigen hu.2 hv.2 (bar_mul_ne_one h hν₂ hν₂N hζ hζN h2)
    · exact herm_eq_zero_of_eigen hu.1 hv.1 (bar_mul_ne_one h hν₁ hν₁N hζ hζN h1)
  have hWsep : ∀ ij, ((idForm h n).domRestrict₁₂ (W ij) (W ij)).SeparatingLeft :=
    NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n) W
      (fun ij ij' hne u hu v hv => by
        rw [Nonsplit.idForm_eq_herm h]; exact hW_orth ij ij' hne u hu v hv) hWtop
  have hWx : ∀ ij, ∀ v ∈ W ij, Matrix.toLin' xm v ∈ W ij := by
    intro ij v hv
    rw [Matrix.toLin'_apply]
    rw [hmemW] at hv ⊢
    constructor
    · rw [mulVec_mulVec, ← coe_comm hxy₁, ← mulVec_mulVec, hv.1, mulVec_smul]
    · rw [mulVec_mulVec, ← coe_comm hxy₂, ← mulVec_mulVec, hv.2, mulVec_smul]
  have hWdim : ∀ ij, W ij ≠ ⊥ → p ≤ Module.finrank K (W ij) := fun ij hne =>
    NonPth.p_le_finrank_of_stable hp (hpowT _ _ hxp) hα (hWx ij) hne
  have hWON : ∀ ij, W ij ≠ ⊥ → HasONBasis σ₀ (W ij) := by
    intro ij hne
    refine Nonsplit.hasONBasis_of_separatingLeft h (W ij) (hWsep ij) ?_
    have hd := hWdim ij hne
    rcases Nat.lt_or_ge p 4 with hp4 | hp4
    · obtain ⟨s, hs0, hs1⟩ := Nonsplit.exists_norm_ne_one h hq2
      exact Or.inr ⟨by have := hp.two_le; omega, s, hs0, by rw [hσb]; exact hs1⟩
    · exact Or.inl (by omega)
  have hcl_le : ∀ a b : ℕ, Subgroup.zpowers (π (y₁ ^ a * y₂ ^ b)) ≤
      Subgroup.closure ({π y₁, π y₂} : Set G) := by
    intro a b
    rw [Subgroup.zpowers_le, map_mul, map_pow, map_pow]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hy₁cl _) (Subgroup.pow_mem _ hy₂cl _)
  have hword : ∀ a b : ℕ, ¬ (p ∣ a ∧ p ∣ b) → ∀ k : Fin p,
      AllCenters H (Module.End.eigenspace (Matrix.toLin' (((y₁ ^ a * y₂ ^ b : SUid σ₀ n) :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ((ν₁ ^ a * ν₂ ^ b) * ζ ^ (k : ℕ))) := by
    intro a b hab k
    set z := y₁ ^ a * y₂ ^ b with hz
    have hzE : π z ∈ E := by
      rw [hz, map_mul, map_pow, map_pow]
      exact E.mul_mem (E.pow_mem hy₁E _) (E.pow_mem hy₂E _)
    have hz1 : π z ≠ 1 := by
      intro h1
      rw [hz, map_mul, map_pow, map_pow] at h1
      exact hab (dvd_of_pow_mul_pow_eq_one hp (hexp _ hy₁E) (hexp _ hy₂E) hy₁1 hy₂y₁ h1)
    have hxz : π x ∉ Subgroup.zpowers (π z) := fun hm => hxcl (hcl_le a b hm)
    have hcz : ∀ t : SUid σ₀ n, t * y₁ = y₁ * t → t * y₂ = y₂ * t → t * z = z * t := by
      intro t h1 h2
      rw [hz]
      exact ((Commute.pow_right h1 a).mul_right (Commute.pow_right h2 b)).eq
    have hzp : (((z : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p =
        ((ν₁ ^ a * ν₂ ^ b) ^ p) • 1 := by
      rw [hz, pow_word_of_comm hy₁y₂ hy₁p hy₂p a b, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul,
        ← pow_mul, mul_comm p a, mul_comm p b]
    have hμ : ν₁ ^ a * ν₂ ^ b ≠ 0 := mul_ne_zero (pow_ne_zero _ hν₁) (pow_ne_zero _ hν₂)
    by_cases hy₁z : π y₁ ∈ Subgroup.zpowers (π z)
    · have hy₂z : π y₂ ∉ Subgroup.zpowers (π z) := by
        intro hy₂z
        have hle : Subgroup.closure ({π y₁, π y₂} : Set G) ≤ Subgroup.zpowers (π z) :=
          (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hy₁z,
            Set.singleton_subset_iff.2 hy₂z⟩)
        have h1 := Subgroup.card_le_of_le hle
        rw [hc2, Nat.card_zpowers, orderOf_eq_prime (hexp _ hzE) hz1] at h1
        have := Nat.pow_lt_pow_right hp.one_lt (by norm_num : 1 < 2)
        rw [pow_one] at this
        omega
      exact allCenters_eigen h hp hp2 hpq hq2 π hE hcard hxE hzE hy₂E hz1 hxz hy₂z hxy₂
        (hcz x hxy₁ hxy₂) (hcz y₂ hy₁y₂.symm rfl) hxp hα hμ hzp hν₂ hy₂p hζ hζN k
    · exact allCenters_eigen h hp hp2 hpq hq2 π hE hcard hxE hzE hy₁E hz1 hxz hy₁z hxy₁
        (hcz x hxy₁ hxy₂) (hcz y₁ rfl hy₁y₂) hxp hα hμ hzp hν₁ hy₁p hζ hζN k
  have hAll : ∀ ij, AllCenters H (W ij) := by
    intro ij v hv hvi
    have hp1 : ¬ p ∣ 1 := fun hd => hp.one_lt.ne' (Nat.dvd_one.1 hd)
    have h1 := hword 1 0 (fun hd => hp1 hd.1) ij.1
    simp only [pow_one, pow_zero, mul_one] at h1
    refine h1 v ?_ hvi
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact ((hmemW ij v).1 hv).1
  have hmix : ∀ ij ij' : Fin p × Fin p, ij ≠ ij' → W ij ≠ ⊥ → W ij' ≠ ⊥ →
      ∃ w₁ ∈ W ij, ∃ w₂ ∈ W ij', w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ IsCenter H (w₁ + w₂) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hne h0 h0'
    set a : ℕ := (((j' : ℕ) : ZMod p) - ((j : ℕ) : ZMod p)).val with ha
    set b : ℕ := (((i : ℕ) : ZMod p) - ((i' : ℕ) : ZMod p)).val with hb
    have haZ : (a : ZMod p) = ((j' : ℕ) : ZMod p) - ((j : ℕ) : ZMod p) := ZMod.natCast_zmod_val _
    have hbZ : (b : ZMod p) = ((i : ℕ) : ZMod p) - ((i' : ℕ) : ZMod p) := ZMod.natCast_zmod_val _
    have hfin : ∀ u v : Fin p, ((u : ℕ) : ZMod p) = ((v : ℕ) : ZMod p) → u = v := by
      intro u v huv
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt u.2, Nat.mod_eq_of_lt v.2] at huv
      exact Fin.ext huv
    have hab : ¬ (p ∣ a ∧ p ∣ b) := by
      rintro ⟨hpa, hpb⟩
      apply hne
      have h1 : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff a p).2 hpa
      have h2 : (b : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff b p).2 hpb
      rw [haZ, sub_eq_zero] at h1
      rw [hbZ, sub_eq_zero] at h2
      rw [hfin _ _ h1, hfin _ _ h2]
    set k : Fin p := ⟨(a * i + b * j) % p, Nat.mod_lt _ hp.pos⟩ with hk
    have hcong : (a * i' + b * j') % p = (a * i + b * j) % p := by
      rw [← ZMod.natCast_eq_natCast_iff']
      push_cast
      rw [haZ, hbZ]
      ring
    set z := y₁ ^ a * y₂ ^ b with hz
    have hzv : ∀ (i₀ j₀ : Fin p) (v : Fin n → K), v ∈ W (i₀, j₀) →
        (((z : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
          ((ν₁ ^ a * ν₂ ^ b) * ζ ^ ((a * i₀ + b * j₀) % p)) • v := by
      intro i₀ j₀ v hv
      rw [hmemW] at hv
      have hpow : ∀ (M : Matrix (Fin n) (Fin n) K) (c : K) (t : ℕ), M *ᵥ v = c • v →
          (M ^ t) *ᵥ v = c ^ t • v := by
        intro M c t hMv
        induction t with
        | zero => simp
        | succ t ih =>
          rw [pow_succ, ← mulVec_mulVec, hMv, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
      rw [hz, coe_pow_mul_pow, ← mulVec_mulVec, hpow _ _ b hv.2, mulVec_smul, hpow _ _ a hv.1,
        smul_smul, ← pow_eq_pow_mod hζ]
      congr 1
      simp only [mul_pow, ← pow_mul]
      rw [pow_add]
      ring
    have hUc := hword a b hab k
    obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    obtain ⟨w₁, hw₁, hw₁i, hw₁0⟩ := Nonsplit.exists_isotropic_pairing hσ (hWON _ h0) hu₀ hu₀0
    obtain ⟨u₀', hu₀', hu₀0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0'
    obtain ⟨w₂, hw₂, hw₂i, hw₂0⟩ := Nonsplit.exists_isotropic_pairing hσ (hWON _ h0') hu₀' hu₀0'
    have hw₁ne : w₁ ≠ 0 := by rintro rfl; exact hw₁0 (herm_zero_right σ₀ _)
    have hw₂ne : w₂ ≠ 0 := by rintro rfl; exact hw₂0 (herm_zero_right σ₀ _)
    refine ⟨w₁, hw₁, w₂, hw₂, hw₁ne, hw₂ne, hUc _ ?_ ?_⟩
    · rw [Module.End.mem_eigenspace_iff, map_add, Matrix.toLin'_apply, Matrix.toLin'_apply,
        hzv i j w₁ hw₁, hzv i' j' w₂ hw₂, hcong, smul_add]
    · have h12 := hW_orth (i, j) (i', j') hne w₁ hw₁ w₂ hw₂
      have h21 := hW_orth (i', j') (i, j) (Ne.symm hne) w₂ hw₂ w₁ hw₁
      simp only [herm_add_left, herm_add_right, hw₁i, hw₂i, h12, h21, add_zero]
  have hpair : ∃ ij ij' : Fin p × Fin p, ij ≠ ij' ∧ W ij ≠ ⊥ ∧ W ij' ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨ij₀, hij₀⟩ : ∃ ij₀, ∀ ij, ij ≠ ij₀ → W ij = ⊥ := by
      by_cases hex : ∃ ij₀, W ij₀ ≠ ⊥
      · obtain ⟨ij₀, hij₀⟩ := hex
        exact ⟨ij₀, fun ij hij => hcon ij₀ ij (Ne.symm hij) hij₀⟩
      · push Not at hex
        exact ⟨(⟨0, hp.pos⟩, ⟨0, hp.pos⟩), fun ij _ => hex ij⟩
    have hall : ∀ v, y₁m *ᵥ v = (ν₁ * ζ ^ (ij₀.1 : ℕ)) • v := by
      intro v
      have hv : v ∈ ⨆ ij, W ij := by rw [hWtop]; exact Submodule.mem_top
      have hle : (⨆ ij, W ij) ≤ W ij₀ := iSup_le fun ij => by
        by_cases hij : ij = ij₀
        · rw [hij]
        · rw [hij₀ ij hij]; exact bot_le
      exact ((hmemW ij₀ v).1 (hle hv)).1
    apply hy₁1
    refine hker' y₁ ⟨ν₁ * ζ ^ (ij₀.1 : ℕ), ?_⟩
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [hall, Matrix.smul_mulVec, Matrix.one_mulVec]
  obtain ⟨ij₀, ij₁, hne₀₁, h₀, h₁⟩ := hpair
  have hn4 : 4 ≤ n := by
    have hd₀ := hWdim ij₀ h₀
    have hd₁ := hWdim ij₁ h₁
    have hdisj : Disjoint (W ij₀) (W ij₁) := by
      rw [Submodule.disjoint_def]
      intro v hv0 hv1
      have hvv : herm σ₀ v v = 0 := hW_orth ij₀ ij₁ hne₀₁ v hv0 v hv1
      have hsep := hWsep ij₀
      have : (⟨v, hv0⟩ : W ij₀) = 0 := by
        apply hsep
        rintro ⟨w, hw⟩
        simp only [LinearMap.domRestrict₁₂_apply]
        rw [Nonsplit.idForm_eq_herm h]
        exact hW_orth ij₁ ij₀ (Ne.symm hne₀₁) v hv1 w hw
      exact congrArg Subtype.val this
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq (W ij₀) (W ij₁)
    rw [hdisj.eq_bot, finrank_bot] at h3
    have h4 := Submodule.finrank_le (W ij₀ ⊔ W ij₁)
    rw [Module.finrank_fin_fun] at h4
    have := hp.two_le
    omega
  let ι := {ij : Fin p × Fin p // W ij ≠ ⊥}
  have : Nonempty ι := ⟨⟨ij₀, h₀⟩⟩
  have hHtop : H = ⊤ := by
    refine Centers.eq_top_of_blocks hσ hn4 (fun i : ι => W i.1) (fun i => hWON i.1 i.2)
      (fun i i' hii u hu v hv => hW_orth i.1 i'.1 (fun h' => hii (Subtype.ext h')) u hu v hv)
      (fun i => hAll i.1)
      (fun i i' hii => hmix i.1 i'.1 (fun h' => hii (Subtype.ext h')) i.2 i'.2) ?_
    rw [eq_top_iff, ← hWtop]
    refine iSup_le fun ij => ?_
    by_cases hij : W ij = ⊥
    · rw [hij]; exact bot_le
    · exact le_iSup_of_le (⟨ij, hij⟩ : ι) le_rfl
  intro k _
  obtain ⟨g, rfl⟩ := hπ k
  have hg : g ∈ H := by rw [hHtop]; exact Subgroup.mem_top g
  exact hg

end CaseB


section ToolsC

variable {K : Type*} [Field K] {σ : K ≃+* K} {n m : ℕ}

theorem resMat_mulVec_of_eq {x : Fin m → Fin n → K} (hx : ONExt.IsON σ x)
    {M : Matrix (Fin n) (Fin n) K} {c d : Fin m → K} (hd : M *ᵥ orthoEmb x c = orthoEmb x d) :
    ONExt.resMat σ x M *ᵥ c = d := by
  rw [ONExt.resMat, ← mulVec_mulVec, ← mulVec_mulVec, ONExt.colMat_mulVec, hd,
    ONExt.coordMat_mulVec, ONExt.coord_orthoEmb hx]

theorem mulVec_orthoEmb_eq {x : Fin m → Fin n → K} (hx : ONExt.IsON σ x)
    {M : Matrix (Fin n) (Fin n) K} (hM : ∀ c, ∃ d, M *ᵥ orthoEmb x c = orthoEmb x d)
    (c : Fin m → K) : M *ᵥ orthoEmb x c = orthoEmb x (ONExt.resMat σ x M *ᵥ c) := by
  obtain ⟨d, hd⟩ := hM c
  rw [resMat_mulVec_of_eq hx hd, hd]

theorem commute_extMat_of_GL (hσ : ∀ c, σ (σ c) = c) {x : Fin m → Fin n → K}
    (hx : ONExt.IsON σ x) {M : GL (Fin n) K}
    (hMu : ∀ u v, herm σ ((M : Matrix (Fin n) (Fin n) K) *ᵥ u)
      ((M : Matrix (Fin n) (Fin n) K) *ᵥ v) = herm σ u v)
    (hM : ∀ c, ∃ d, (M : Matrix (Fin n) (Fin n) K) *ᵥ orthoEmb x c = orthoEmb x d)
    (hM' : ∀ c, ∃ d, ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ orthoEmb x c =
      orthoEmb x d)
    {g : Matrix (Fin m) (Fin m) K}
    (hg : g * ONExt.resMat σ x (M : Matrix (Fin n) (Fin n) K) =
      ONExt.resMat σ x (M : Matrix (Fin n) (Fin n) K) * g) :
    (M : Matrix (Fin n) (Fin n) K) * ONExt.extMat σ x g =
      ONExt.extMat σ x g * (M : Matrix (Fin n) (Fin n) K) := by
  have hMM : ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (M : Matrix (Fin n) (Fin n) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have horth : ∀ u : Fin n → K, (∀ i, herm σ (x i) u = 0) →
      ∀ i, herm σ (x i) ((M : Matrix (Fin n) (Fin n) K) *ᵥ u) = 0 := by
    intro u hu i
    obtain ⟨d, hd⟩ := hM' (Pi.single i 1)
    rw [ONExt.orthoEmb_single] at hd
    have h := hMu (((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x i) u
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h
    rw [h, hd]
    exact ONExt.herm_orthoEmb_of_orth x hu d
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  obtain ⟨c, u, hu, hv⟩ := ONExt.exists_decomp hx (Pi.single i 1)
  rw [hv, ONExt.extMat_mulVec hx g c hu, mulVec_add, mulVec_add, mulVec_orthoEmb_eq hx hM,
    mulVec_orthoEmb_eq hx hM, ONExt.extMat_mulVec hx g _ (horth u hu), mulVec_mulVec,
    mulVec_mulVec, hg]

theorem exists_siegel (hσ : ∀ c, σ (σ c) = c) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → Fin n → K) (hu : ∀ k l, herm σ (u k) (u l) = 0) {c : K} (hc : c + σ c = 0) :
    ∃ S : SUid σ n, ∀ v, S • v = v + ∑ k, (c * herm σ (u k) v) • u k := by
  have hstep : ∀ s : Finset ι, ∃ S : SUid σ n,
      ∀ v, S • v = v + ∑ k ∈ s, (c * herm σ (u k) v) • u k := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, fun v => by simp⟩
    | insert i s hi ih =>
      obtain ⟨S, hS⟩ := ih
      refine ⟨tv hσ (hu i i) hc * S, fun v => ?_⟩
      have h0 : herm σ (u i) (∑ k ∈ s, (c * herm σ (u k) v) • u k) = 0 := by
        have := map_sum (hermL σ (u i)) (fun k => (c * herm σ (u k) v) • u k) s
        simp only [hermL_apply, herm_smul_right, hu, mul_zero, Finset.sum_const_zero] at this
        exact this
      rw [mul_smul, hS v, tv_smul, Finset.sum_insert hi, herm_add_right, h0, add_zero]
      abel
  exact hstep Finset.univ

theorem eq_top_of_normal_of_nonscalar {K : Type} [Field K] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m) (h3 : m = 3 → ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1)
    {N : Subgroup (SUid σ m)} (hN : ∀ g ∈ N, ∀ s : SUid σ m, s * g * s⁻¹ ∈ N)
    {g : SUid σ m} (hgN : g ∈ N)
    (hg : ∀ c : K, ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ≠ c • 1) : N = ⊤ := by
  classical
  haveI hsimple := isSimpleGroup_statedProj_SUid hσ hm h3
  have hperf := isPerfect_SUid hσ hm h3
  set Z := (StatedScalars (Fin m) K).subgroupOf (SUid σ m) with hZ
  set φ : SUid σ m →* StatedProj (SUid σ m) := QuotientGroup.mk' Z with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective Z
  have hNn : N.Normal := ⟨fun g hg s => hN g hg s⟩
  have hmapn : (N.map φ).Normal := Subgroup.Normal.map hNn φ hφs
  have hZc : ∀ z ∈ Z, ∀ y : SUid σ m, z * y = y * z := by
    intro z hz y
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hz
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map φ) with hbot | htop
  · exfalso
    have h1 : φ g = 1 := by
      have : φ g ∈ N.map φ := ⟨g, hgN, rfl⟩
      rw [hbot] at this
      exact this
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 h1
    apply hg (c : K)
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  · have hdec : ∀ y : SUid σ m, ∃ a ∈ N, ∃ z ∈ Z, y = a * z := by
      intro y
      have : φ y ∈ N.map φ := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨a, ha, hay⟩ := this
      refine ⟨a, ha, a⁻¹ * y, ?_, by group⟩
      rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_mul, map_inv]
      rw [← hφ, hay, inv_mul_cancel]
    rw [eq_top_iff, ← hperf.commutator_eq_top, commutator_def, Subgroup.commutator_le]
    intro y _ y' _
    obtain ⟨a, ha, z, hz, rfl⟩ := hdec y
    obtain ⟨a', ha', z', hz', rfl⟩ := hdec y'
    have e : a * z * (a' * z') * (a * z)⁻¹ * (a' * z')⁻¹ = a * a' * a⁻¹ * a'⁻¹ := by
      have e1 : z * (a' * z') = (a' * z') * z := hZc z hz _
      have e2 : z' * a⁻¹ = a⁻¹ * z' := hZc z' hz' _
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
      calc a * z * (a' * z') * (z⁻¹ * a⁻¹) * (z'⁻¹ * a'⁻¹)
          = a * (z * (a' * z')) * (z⁻¹ * a⁻¹) * (z'⁻¹ * a'⁻¹) := by group
        _ = a * ((a' * z') * z) * (z⁻¹ * a⁻¹) * (z'⁻¹ * a'⁻¹) := by rw [e1]
        _ = a * a' * (z' * a⁻¹) * (z'⁻¹ * a'⁻¹) := by group
        _ = a * a' * (a⁻¹ * z') * (z'⁻¹ * a'⁻¹) := by rw [e2]
        _ = a * a' * a⁻¹ * a'⁻¹ := by group
    rw [commutatorElement_def, e]
    exact N.mul_mem (N.mul_mem (N.mul_mem ha ha') (N.inv_mem ha)) (N.inv_mem ha')

theorem tv_inv (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : herm σ a a = 0) {c : K}
    (hc : c + σ c = 0) (hc' : -c + σ (-c) = 0) : (tv hσ ha hc)⁻¹ = tv hσ ha hc' := by
  rw [inv_eq_iff_mul_eq_one, tv_mul_tv hσ ha hc hc' (by rw [add_neg_cancel, map_zero, add_zero])]
  have h0 : (0 : K) + σ 0 = 0 := by rw [map_zero, add_zero]
  rw [← tv_zero hσ ha h0]
  congr 1
  ring

theorem conj_mem_of_tv (hσ : IsUnitaryInvolution σ) (hm : 2 ≤ m)
    (h3 : m = 3 → ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1) {N : Subgroup (SUid σ m)}
    (htv : ∀ (a : Fin m → K) (ha : herm σ a a = 0) (c : K) (hc : c + σ c = 0),
      ∀ g ∈ N, tv hσ.invol ha hc * g * (tv hσ.invol ha hc)⁻¹ ∈ N) :
    ∀ g ∈ N, ∀ s : SUid σ m, s * g * s⁻¹ ∈ N := by
  have key : ∀ s : SUid σ m, s ∈ T σ m →
      ∀ g ∈ N, s * g * s⁻¹ ∈ N ∧ s⁻¹ * g * s ∈ N := by
    intro s hs
    induction hs using Subgroup.closure_induction with
    | mem t ht =>
      obtain ⟨a, c, ha, hc, h⟩ := ht
      have hc' : -c + σ (-c) = 0 := by rw [map_neg]; linear_combination -hc
      have ht' : t = tv hσ.invol ha hc := ext_smul σ fun v => by rw [h, tv_smul]
      intro g hg
      refine ⟨by rw [ht']; exact htv a ha c hc g hg, ?_⟩
      have := htv a ha (-c) hc' g hg
      rw [← tv_inv hσ.invol ha hc hc', inv_inv] at this
      rw [ht']
      exact this
    | one => intro g hg; simpa using hg
    | mul x y _ _ ihx ihy =>
      intro g hg
      refine ⟨?_, ?_⟩
      · have := (ihx _ (ihy g hg).1).1
        simpa only [_root_.mul_inv_rev, mul_assoc] using this
      · have := (ihy _ (ihx g hg).2).2
        simpa only [_root_.mul_inv_rev, mul_assoc] using this
    | inv x _ ihx =>
      intro g hg
      refine ⟨?_, ?_⟩
      · simpa only [inv_inv] using (ihx g hg).2
      · simpa only [inv_inv] using (ihx g hg).1
  intro g hg s
  exact (key s (by rw [T_eq_top hσ hm h3]; exact Subgroup.mem_top s) g hg).1

theorem siegel_comm_of_eigen {ι : Type*} [Fintype ι] {S B : SUid σ n} {u : ι → Fin n → K}
    {c : K} (hS : ∀ v, S • v = v + ∑ k, (c * herm σ (u k) v) • u k) {lam : ι → K}
    (hB : ∀ k, B • u k = lam k • u k) (hl : ∀ k, σ (lam k) * lam k = 1) : B * S = S * B := by
  refine ext_smul σ fun v => ?_
  rw [mul_smul, mul_smul, hS, hS, smul_add, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have hl0 : lam k ≠ 0 := by
    rintro h0
    have := hl k
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have hσl : σ (lam k)⁻¹ = lam k := by
    rw [map_inv₀]
    exact inv_eq_of_mul_eq_one_right (hl k)
  have hBu : u k = B • ((lam k)⁻¹ • u k) := by
    rw [smul_comm, hB, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  have h1 : herm σ (u k) (B • v) = lam k * herm σ (u k) v := by
    conv_lhs => rw [hBu]
    rw [herm_smul_smul, herm_smul_left, hσl]
  rw [smul_comm, hB, h1, smul_smul]
  congr 1
  ring

theorem exists_siegel_orbit (hσ : ∀ c, σ (σ c) = c) {p : ℕ} [NeZero p] {X : SUid σ n} {β : K}
    (hXp : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1) (hβ : σ β * β = 1)
    {w : Fin n → K} (horth : ∀ k l : Fin p, herm σ ((X ^ (k : ℕ)) • w) ((X ^ (l : ℕ)) • w) = 0)
    {c : K} (hc : c + σ c = 0) :
    ∃ S : SUid σ n, (∀ v, S • v = v + ∑ k : Fin p,
      (c * herm σ ((X ^ (k : ℕ)) • w) v) • ((X ^ (k : ℕ)) • w)) ∧ X * S = S * X := by
  obtain ⟨S, hS⟩ := exists_siegel hσ (fun k : Fin p => (X ^ (k : ℕ)) • w) horth hc
  refine ⟨S, hS, ext_smul σ fun v => ?_⟩
  rw [mul_smul, mul_smul, hS, hS, smul_add, Finset.smul_sum]
  congr 1
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := NeZero.pos p; omega⟩
  rw [← Equiv.sum_comp (finRotate (q + 1)) (fun k : Fin (q + 1) =>
    (c * herm σ ((X ^ (k : ℕ)) • w) (X • v)) • ((X ^ (k : ℕ)) • w))]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hXpw : (X ^ (q + 1)) • w = β • w := by
    rw [smul_def, Subgroup.coe_pow, Units.val_pow_eq_pow_val, hXp, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  by_cases hk : k = Fin.last q
  · subst hk
    rw [finRotate_last, Fin.val_zero, pow_zero, one_smul, Fin.val_last, smul_comm X,
      ← mul_smul X (X ^ q) w, ← pow_succ', hXpw, smul_smul]
    have h1 : herm σ ((X ^ q) • w) v = σ β * herm σ w (X • v) := by
      rw [← herm_smul_smul σ X, ← mul_smul, ← pow_succ', hXpw, herm_smul_left]
    rw [h1]
    congr 1
    linear_combination (c * herm σ w (X • v)) * hβ
  · rw [coe_finRotate_of_ne_last hk, pow_succ', mul_smul X (X ^ (k : ℕ)) w, herm_smul_smul]
    exact smul_comm X _ _

@[expose] noncomputable def diagTwo (σ : K ≃+* K) {d : K} (hd : σ d * d = 1) : SUid σ 2 :=
  mkSU σ (Matrix.diagonal ![d, d⁻¹])
    (by
      have hd0 : d ≠ 0 := by rintro rfl; rw [mul_zero] at hd; exact zero_ne_one hd
      rw [Matrix.det_diagonal, Fin.prod_univ_two]
      simp [hd0])
    (by
      have hd0 : d ≠ 0 := by rintro rfl; rw [mul_zero] at hd; exact zero_ne_one hd
      have hd' : σ d⁻¹ * d⁻¹ = 1 := by
        rw [map_inv₀, ← mul_inv, hd, inv_one]
      intro u v
      simp only [herm_def, Fin.sum_univ_two, Matrix.mulVec_diagonal, map_mul]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      linear_combination (σ (u 0) * v 0) * hd + (σ (u 1) * v 1) * hd')

theorem diagTwo_smul_single (σ : K ≃+* K) {d : K} (hd : σ d * d = 1) :
    diagTwo σ hd • (Pi.single 0 1 : Fin 2 → K) = d • Pi.single 0 1 ∧
      diagTwo σ hd • (Pi.single 1 1 : Fin 2 → K) = d⁻¹ • Pi.single 1 1 := by
  constructor <;>
  · rw [diagTwo, mkSU_smul]
    funext i
    rw [Matrix.mulVec_diagonal]
    fin_cases i <;> simp

theorem exists_nonscalar_comm (hσ : IsUnitaryInvolution σ) {xs : Fin m → Fin n → K}
    (hxs : ONExt.IsON σ xs) {s : SUid σ n} (hsU : ∀ c, ∃ d, s • orthoEmb xs c = orthoEmb xs d)
    (hsU' : ∀ c, ∃ d, s⁻¹ • orthoEmb xs c = orthoEmb xs d) {e₁ e₂ : Fin m → K}
    (h11 : herm σ e₁ e₁ = 1) (h22 : herm σ e₂ e₂ = 1) (h12 : herm σ e₁ e₂ = 0)
    {l₁ l₂ : K} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0) (hs₁ : s • orthoEmb xs e₁ = l₁ • orthoEmb xs e₁)
    (hs₂ : s • orthoEmb xs e₂ = l₂ • orthoEmb xs e₂) {d : K} (hd : σ d * d = 1)
    (hdd : d ≠ d⁻¹) :
    ∃ g : SUid σ m, (∀ c : K, ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ≠ c • 1) ∧
      s * ONExt.ext hσ.invol hxs g = ONExt.ext hσ.invol hxs g * s := by
  classical
  have hσi := hσ.invol
  set y : Fin 2 → Fin m → K := ![e₁, e₂] with hy
  have h21 : herm σ e₂ e₁ = 0 := herm_eq_zero_comm σ hσi h12
  have hyON : ONExt.IsON σ y := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hy, h11, h22, h12, h21]
  set g : SUid σ m := ONExt.ext hσi hyON (diagTwo σ hd) with hg
  have hy0 : orthoEmb y (Pi.single 0 1) = e₁ := by rw [ONExt.orthoEmb_single]; rfl
  have hy1 : orthoEmb y (Pi.single 1 1) = e₂ := by rw [ONExt.orthoEmb_single]; rfl
  have hge₁ : g • e₁ = d • e₁ := by
    rw [← hy0, hg, ONExt.ext_smul_orthoEmb, (diagTwo_smul_single σ hd).1, map_smul]
  have hge₂ : g • e₂ = d⁻¹ • e₂ := by
    rw [← hy1, hg, ONExt.ext_smul_orthoEmb, (diagTwo_smul_single σ hd).2, map_smul]
  refine ⟨g, fun c hc => ?_, ?_⟩
  ·
    have he₁ : e₁ ≠ 0 := by rintro rfl; rw [herm_zero_left] at h11; exact zero_ne_one h11
    have he₂ : e₂ ≠ 0 := by rintro rfl; rw [herm_zero_left] at h22; exact zero_ne_one h22
    have h1 : c • e₁ = d • e₁ := by
      rw [← hge₁, smul_def, hc, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 : c • e₂ = d⁻¹ • e₂ := by
      rw [← hge₂, smul_def, hc, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hcd : c = d := by
      have h3 : (c - d) • e₁ = 0 := by rw [sub_smul, h1, sub_self]
      rcases smul_eq_zero.1 h3 with h4 | h4
      · exact sub_eq_zero.1 h4
      · exact absurd h4 he₁
    have hcd' : c = d⁻¹ := by
      have h3 : (c - d⁻¹) • e₂ = 0 := by rw [sub_smul, h2, sub_self]
      rcases smul_eq_zero.1 h3 with h4 | h4
      · exact sub_eq_zero.1 h4
      · exact absurd h4 he₂
    exact hdd (hcd.symm.trans hcd')
  ·
    refine commute_ext_of_resMat hσi hxs hsU hsU' ?_
    set M : GL (Fin m) K := resGL hxs s hsU hsU' with hM
    have hMe : ∀ (e : Fin m → K) (l : K), s • orthoEmb xs e = l • orthoEmb xs e →
        (M : Matrix (Fin m) (Fin m) K) *ᵥ e = l • e := by
      intro e l he
      rw [hM, coe_resGL]
      exact resMat_mulVec_of_eq hxs (by rw [← smul_def, he, ← map_smul])
    have hMe₁ := hMe e₁ l₁ hs₁
    have hMe₂ := hMe e₂ l₂ hs₂
    have hsinv : ∀ (e : Fin m → K) (l : K), l ≠ 0 → s • orthoEmb xs e = l • orthoEmb xs e →
        s⁻¹ • orthoEmb xs e = l⁻¹ • orthoEmb xs e := by
      intro e l hl he
      rw [inv_smul_eq_iff, smul_comm, he, smul_smul, inv_mul_cancel₀ hl, one_smul]
    have hMinv : ∀ (e : Fin m → K) (l : K), l ≠ 0 → s • orthoEmb xs e = l • orthoEmb xs e →
        ((M⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ e = l⁻¹ • e := by
      intro e l hl he
      show ONExt.resMat σ xs (((s⁻¹ : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e =
        l⁻¹ • e
      exact resMat_mulVec_of_eq hxs (by rw [← smul_def, hsinv e l hl he, ← map_smul])
    have hspan : ∀ (N : Matrix (Fin m) (Fin m) K) (a b : K), N *ᵥ e₁ = a • e₁ →
        N *ᵥ e₂ = b • e₂ → ∀ c, ∃ c', N *ᵥ orthoEmb y c = orthoEmb y c' := by
      intro N a b ha hb c
      refine ⟨![a * c 0, b * c 1], ?_⟩
      simp only [Centers.orthoEmb_apply, Fin.sum_univ_two, hy, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, mulVec_add, mulVec_smul, ha, hb, smul_smul]
      ring_nf
    have hres : ONExt.resMat σ y (M : Matrix (Fin m) (Fin m) K) =
        Matrix.diagonal ![l₁, l₂] := by
      refine Matrix.ext_of_mulVec_single fun j => ?_
      have hj : (M : Matrix (Fin m) (Fin m) K) *ᵥ orthoEmb y (Pi.single j 1) =
          orthoEmb y (![l₁, l₂] j • Pi.single j 1) := by
        rw [ONExt.orthoEmb_single, map_smul, ONExt.orthoEmb_single]
        fin_cases j
        · simpa [hy] using hMe₁
        · simpa [hy] using hMe₂
      rw [resMat_mulVec_of_eq hyON hj]
      funext i
      rw [Matrix.mulVec_diagonal]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    have hcomm := commute_extMat_of_GL hσi hyON (M := M)
      (fun u v => by rw [hM, coe_resGL]; exact ONExt.herm_resMat hxs hsU u v)
      (hspan _ l₁ l₂ hMe₁ hMe₂)
      (hspan _ l₁⁻¹ l₂⁻¹ (hMinv e₁ l₁ hl₁ hs₁) (hMinv e₂ l₂ hl₂ hs₂))
      (g := ((diagTwo σ hd : SUid σ 2) : GL (Fin 2) K)) (by
        rw [hres]
        show Matrix.diagonal ![d, d⁻¹] * Matrix.diagonal ![l₁, l₂] =
          Matrix.diagonal ![l₁, l₂] * Matrix.diagonal ![d, d⁻¹]
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        exact mul_comm _ _)
    rw [hM, coe_resGL] at hcomm
    exact hcomm.symm

end ToolsC

section BlockC

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem exists_unit_of_separatingLeft (h : UnitaryFieldData ℓ f K) {W : Submodule K (Fin n → K)}
    (hW : W ≠ ⊥) (hnd : ((idForm h n).domRestrict₁₂ W W).SeparatingLeft) :
    ∃ e ∈ W, herm σ₀ e e = 1 := by
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  by_cases hall : ∀ w ∈ W, herm σ₀ w w = 0
  · exfalso
    apply hW
    rw [eq_bot_iff]
    intro w hw
    have h0 : (⟨w, hw⟩ : W) = 0 := hnd ⟨w, hw⟩ fun w' => by
      simp only [LinearMap.domRestrict₁₂_apply]
      rw [Nonsplit.idForm_eq_herm h]
      exact herm_eq_zero_of_forall_isotropic hσ hall hw w'.2
    rw [Submodule.mem_bot]
    simpa using congrArg Subtype.val h0
  push Not at hall
  obtain ⟨w, hw, hww⟩ := hall
  have hfix : σ₀ (herm σ₀ w w)⁻¹ = (herm σ₀ w w)⁻¹ := by
    rw [map_inv₀, herm_self_fixed σ₀ hσ.invol]
  obtain ⟨s, hs⟩ := hσ.exists_norm hfix
  refine ⟨s • w, W.smul_mem s hw, ?_⟩
  rw [herm_smul_left, herm_smul_right, ← mul_assoc, hs, inv_mul_cancel₀ hww]

theorem bar_mul_eq_one_of_SUid_scalar (h : UnitaryFieldData ℓ f K) (hn : 0 < n)
    {s : SUid σ₀ n} {k : ℕ} {β : K}
    (hsk : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ k = β • 1) : h.bar β * β = 1 := by
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have h1 := herm_smul_smul σ₀ (s ^ k) (Pi.single ⟨0, hn⟩ 1) (Pi.single ⟨0, hn⟩ 1)
  rw [smul_def, Subgroup.coe_pow, Units.val_pow_eq_pow_val, hsk, Matrix.smul_mulVec,
    Matrix.one_mulVec, herm_smul_left, herm_smul_right, herm_single_left, map_one, one_mul,
    Pi.single_eq_same, mul_one] at h1
  rw [← hσb]
  simpa using h1

theorem mulVec_pow_smul_of_qcomm {X B : SUid σ₀ n} {ζ : K}
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) {μ : K} :
    ∀ (k a : ℕ) (v : Fin n → K),
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = (μ * ζ ^ a) • v →
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ((X ^ k) • v) =
        (μ * ζ ^ (a + k)) • ((X ^ k) • v) := by
  intro k
  induction k with
  | zero => intro a v hv; simpa using hv
  | succ k ih =>
    intro a v hv
    rw [pow_succ', mul_smul, smul_def σ₀ X, mulVec_mulVec, hBX, Matrix.smul_mulVec,
      ← mulVec_mulVec, ih a v hv, mulVec_smul, smul_smul]
    congr 1
    ring

theorem eq_smul_of_eigen_le {X B r : SUid σ₀ n} {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : (p : K) ≠ 0) (hrX : r * X = X * r)
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {μ : K} (hμ : μ ≠ 0)
    (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (μ ^ p) • 1) (hp : p.Prime)
    (l : Fin p) {lam : K}
    (hle : Module.End.eigenspace (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (μ * ζ ^ (l : ℕ)) ≤
      Module.End.eigenspace (Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) lam) :
    ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = lam • 1 := by
  have hmemE : ∀ (M : Matrix (Fin n) (Fin n) K) (a : K) (v : Fin n → K),
      v ∈ Module.End.eigenspace (Matrix.toLin' M) a ↔ M *ᵥ v = a • v := fun M a v => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hBT : (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ p =
      algebraMap K (Module.End K (Fin n → K)) (μ ^ p) := by
    have h2 := congrArg Matrix.toLinAlgEquiv' hBp
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hsup := NonPth.iSup_eigenspace_eq_top_p hp hpK hζ hμ hBT
  have hVle : ∀ i : Fin p,
      Module.End.eigenspace (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (μ * ζ ^ (i : ℕ)) ≤
      Module.End.eigenspace (Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        lam := by
    intro i v hv
    rw [hmemE] at hv ⊢
    set k := (l : ℕ) + p - i with hk
    have hXkv := mulVec_pow_smul_of_qcomm hBX k i v hv
    have hik : (i : ℕ) + k = l + p := by have := i.2; omega
    rw [hik, pow_add, hζ.pow_eq_one, mul_one] at hXkv
    have h1 := (hmemE _ _ _).1 (hle ((hmemE _ _ _).2 hXkv))
    have h2 : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ((X ^ k) • v) =
        (X ^ k) • (((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
      rw [smul_def, smul_def, mulVec_mulVec, mulVec_mulVec, coe_comm (Commute.pow_right hrX k).eq]
    rw [h2, ← smul_comm] at h1
    exact smul_left_cancel _ h1
  refine Matrix.ext_of_mulVec_single fun i => ?_
  have hv : (Pi.single i 1 : Fin n → K) ∈ (⊤ : Submodule K (Fin n → K)) := Submodule.mem_top
  rw [← hsup] at hv
  rw [(hmemE _ _ _).1 ((iSup_le hVle) hv), Matrix.smul_mulVec, Matrix.one_mulVec]

theorem exists_two_eigen {X B r : SUid σ₀ n} {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : (p : K) ≠ 0) (hp : p.Prime) (hrX : r * X = X * r) (hrB : r * B = B * r)
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {μ ρ : K} (hμ : μ ≠ 0)
    (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (μ ^ p) • 1) (hρ : ρ ≠ 0)
    (hrp : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ρ ^ p) • 1)
    (hrs : ∀ c : K, ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1) (l : Fin p)
    (hU0 : Module.End.eigenspace (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (μ * ζ ^ (l : ℕ)) ≠ ⊥) :
    ∃ c₁ c₂ : Fin p, c₁ ≠ c₂ ∧
      Module.End.eigenspace (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
          (μ * ζ ^ (l : ℕ)) ⊓
        Module.End.eigenspace (Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
          (ρ * ζ ^ (c₁ : ℕ)) ≠ ⊥ ∧
      Module.End.eigenspace (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
          (μ * ζ ^ (l : ℕ)) ⊓
        Module.End.eigenspace (Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
          (ρ * ζ ^ (c₂ : ℕ)) ≠ ⊥ := by
  classical
  set U := Module.End.eigenspace (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (μ * ζ ^ (l : ℕ)) with hU
  have hrT : (Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ p =
      algebraMap K (Module.End K (Fin n → K)) (ρ ^ p) := by
    have h2 := congrArg Matrix.toLinAlgEquiv' hrp
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hBr_lin : Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, Module.End.mul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, mulVec_mulVec, coe_comm hrB]
  have hdecU := eigenspace_le_iSup_inf hp hpK hζ hBr_lin hρ hrT (μ * ζ ^ (l : ℕ))
  by_contra hcon
  push Not at hcon
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Fin p, U ≤ Module.End.eigenspace
      (Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (ρ * ζ ^ (c₀ : ℕ)) := by
    by_cases hex : ∃ c₀ : Fin p, U ⊓ Module.End.eigenspace
        (Matrix.toLin' ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (ρ * ζ ^ (c₀ : ℕ)) ≠ ⊥
    · obtain ⟨c₀, hne⟩ := hex
      refine ⟨c₀, hdecU.trans (iSup_le fun c => ?_)⟩
      by_cases hc : c = c₀
      · rw [hc]
        exact inf_le_right
      · rw [hcon c₀ c (Ne.symm hc) hne]
        exact bot_le
    · push Not at hex
      exfalso
      apply hU0
      rw [eq_bot_iff]
      refine hdecU.trans (iSup_le fun c => ?_)
      rw [hex c]
  exact hrs _ (eq_smul_of_eigen_le hζ hpK hrX hBX hμ hBp hp l hc₀)

theorem finrank_eigen_le {X B : SUid σ₀ n} {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) (μ : K) (a b : Fin p) :
    Module.finrank K (Module.End.eigenspace
        (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (μ * ζ ^ (a : ℕ))) ≤
      Module.finrank K (Module.End.eigenspace
        (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (μ * ζ ^ (b : ℕ))) := by
  have hmemE : ∀ (M : Matrix (Fin n) (Fin n) K) (c : K) (v : Fin n → K),
      v ∈ Module.End.eigenspace (Matrix.toLin' M) c ↔ M *ᵥ v = c • v := fun M c v => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  set k := (b : ℕ) + p - a with hk
  have hmaps : ∀ v ∈ Module.End.eigenspace
      (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (μ * ζ ^ (a : ℕ)),
      Matrix.toLin' (((X ^ k : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v ∈
        Module.End.eigenspace (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
          (μ * ζ ^ (b : ℕ)) := by
    intro v hv
    rw [hmemE] at hv ⊢
    rw [Matrix.toLin'_apply, ← smul_def]
    have h1 := mulVec_pow_smul_of_qcomm hBX k a v hv
    have hak : (a : ℕ) + k = b + p := by have := a.2; omega
    rwa [hak, pow_add, hζ.pow_eq_one, mul_one] at h1
  refine LinearMap.finrank_le_finrank_of_injective
    (f := (Matrix.toLin' (((X ^ k : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).restrict
      hmaps) ?_
  intro v w hvw
  apply Subtype.ext
  have := congrArg Subtype.val hvw
  simp only [LinearMap.restrict_coe_apply, Matrix.toLin'_apply] at this
  rw [← smul_def, ← smul_def] at this
  exact smul_left_cancel _ this

theorem allCenters_eigen_nonab (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) (hq2 : ℓ ^ f ≠ 2) {G : Type*} [Group G] [Finite G]
    (π : SUid σ₀ n →* G)
    (hker' : ∀ g : SUid σ₀ n, (∃ c : K,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) → π g = 1)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    {X B r : SUid σ₀ n} (hXE : π X ∈ E) (hBE : π B ∈ E) (hrE : π r ∈ E) (hr1 : π r ≠ 1)
    (hB1 : π B ≠ 1) (hBr : π B ∉ Subgroup.zpowers (π r)) (hXB : π X ∉ Subgroup.zpowers (π B))
    (hrX : r * X = X * r) (hrB : r * B = B * r)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1)
    (hBX : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {β μ ρ : K} (hXp : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1)
    (hμ : μ ≠ 0) (hBp : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (μ ^ p) • 1)
    (hρ : ρ ≠ 0) (hrp : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ρ ^ p) • 1)
    (l : Fin p)
    (hdim : 3 ≤ Module.finrank K (Module.End.eigenspace
      (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (μ * ζ ^ (l : ℕ)))) :
    AllCenters ((hyperClosure p ⊤ E).comap π) (Module.End.eigenspace
      (Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (μ * ζ ^ (l : ℕ))) := by
  classical
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσi := hσ.invol
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set Bm : Matrix (Fin n) (Fin n) K := ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hBm
  set Xm : Matrix (Fin n) (Fin n) K := ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hXm
  set rm : Matrix (Fin n) (Fin n) K := ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hrm
  set U := Module.End.eigenspace (Matrix.toLin' Bm) (μ * ζ ^ (l : ℕ)) with hU
  have hU0 : U ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hdim
    omega
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exact absurd (Subsingleton.elim v₀ 0) hv₀0
    · exact h0
  have hμN := bar_mul_eq_one_of_SUid_pow h hp hp2 hpq hn hμ hBp
  have hρN := bar_mul_eq_one_of_SUid_pow h hp hp2 hpq hn hρ hrp
  have hβN := bar_mul_eq_one_of_SUid_scalar h hn hXp
  have hpowT : ∀ (M : Matrix (Fin n) (Fin n) K) (c : K), M ^ p = c • 1 →
      (Matrix.toLin' M) ^ p = algebraMap K (Module.End K (Fin n → K)) c := by
    intro M c hM
    have h2 := congrArg Matrix.toLinAlgEquiv' hM
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hmemE : ∀ (M : Matrix (Fin n) (Fin n) K) (a : K) (v : Fin n → K),
      v ∈ Module.End.eigenspace (Matrix.toLin' M) a ↔ M *ᵥ v = a • v := fun M a v => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hlamN : ∀ (c : K), h.bar c * c = 1 → ∀ k : ℕ, h.bar (c * ζ ^ k) * (c * ζ ^ k) = 1 := by
    intro c hc k
    rw [map_mul, map_pow]
    calc h.bar c * h.bar ζ ^ k * (c * ζ ^ k) = (h.bar c * c) * (h.bar ζ * ζ) ^ k := by ring
      _ = 1 := by rw [hc, hζN, one_pow, one_mul]
  have horthE : ∀ (s : SUid σ₀ n) (c : K), c ≠ 0 → h.bar c * c = 1 → ∀ a b : ℕ, a % p ≠ b % p →
      ∀ u v, ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u = (c * ζ ^ a) • u →
        ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = (c * ζ ^ b) • v →
        herm σ₀ u v = 0 := by
    intro s c hc0 hcN a b hab u v hu hv
    rw [pow_eq_pow_mod hζ a] at hu
    rw [pow_eq_pow_mod hζ b] at hv
    exact herm_eq_zero_of_eigen hu hv (bar_mul_ne_one h hc0 hcN hζ hζN
      (i := ⟨a % p, Nat.mod_lt _ hp.pos⟩) (i' := ⟨b % p, Nat.mod_lt _ hp.pos⟩)
      (fun he => hab (congrArg Fin.val he)))
  have hmodne : ∀ a b : ℕ, a < p → b < p → a ≠ b → a % p ≠ b % p := by
    intro a b ha hb hab
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have hshiftk : ∀ (k a : ℕ) (v : Fin n → K), Bm *ᵥ v = (μ * ζ ^ a) • v →
      Bm *ᵥ ((X ^ k) • v) = (μ * ζ ^ (a + k)) • ((X ^ k) • v) :=
    mulVec_pow_smul_of_qcomm hBX
  have hsup : ⨆ i : Fin p, Module.End.eigenspace (Matrix.toLin' Bm) (μ * ζ ^ (i : ℕ)) = ⊤ :=
    NonPth.iSup_eigenspace_eq_top_p hp hpK hζ hμ (hpowT _ _ hBp)
  have hnd : ((idForm h n).domRestrict₁₂ U U).SeparatingLeft := by
    refine NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n)
      (fun i : Fin p => Module.End.eigenspace (Matrix.toLin' Bm) (μ * ζ ^ (i : ℕ)))
      (fun i i' hii u hu v hv => ?_) hsup l
    rw [Nonsplit.idForm_eq_herm h]
    exact horthE B μ hμ hμN i i' (hmodne _ _ i.2 i'.2 (fun he => hii (Fin.ext he))) u v
      ((hmemE _ _ u).1 hu) ((hmemE _ _ v).1 hv)
  have hON : HasONBasis σ₀ U := by
    refine Nonsplit.hasONBasis_of_separatingLeft h U hnd ?_
    obtain ⟨s, hs0, hs1⟩ := Nonsplit.exists_norm_ne_one h hq2
    exact Or.inr ⟨hdim, s, hs0, by rw [hσb]; exact hs1⟩
  obtain ⟨m, xs, hxs, hspan, hm⟩ := hON
  have hxsON : ONExt.IsON σ₀ xs := hxs
  have hm3 : 3 ≤ m := by rcases hm with h4 | ⟨h3, -⟩ <;> omega
  have h3m : m = 3 → ∃ s : K, s ≠ 0 ∧ σ₀ s * s ≠ 1 := fun _ => by
    obtain ⟨s, hs0, hs1⟩ := Nonsplit.exists_norm_ne_one h hq2
    exact ⟨s, hs0, by rw [hσb]; exact hs1⟩
  have hstab : ∀ t : SUid σ₀ n, t * B = B * t → ∀ v ∈ U, t • v ∈ U := by
    intro t ht v hv
    rw [hU, hmemE] at hv ⊢
    rw [smul_def, mulVec_mulVec, ← coe_comm ht, ← mulVec_mulVec, hv, mulVec_smul]
  have hsU : ∀ t : SUid σ₀ n, t * B = B * t → ∀ c, ∃ d, t • orthoEmb xs c = orthoEmb xs d :=
    fun t ht => exists_orthoEmb_of_stable hspan (hstab t ht)
  have hsU' : ∀ t : SUid σ₀ n, t * B = B * t → ∀ c, ∃ d, t⁻¹ • orthoEmb xs c = orthoEmb xs d :=
    fun t ht => exists_orthoEmb_of_stable hspan (hstab t⁻¹ (Commute.inv_left ht).eq)
  have hBlam : ∀ c, B • orthoEmb xs c = (μ * ζ ^ (l : ℕ)) • orthoEmb xs c := fun c => by
    have hc : orthoEmb xs c ∈ U := hspan ▸ orthoEmb_mem_span xs c
    exact (hmemE _ _ _).1 hc
  have hBres : ONExt.resMat σ₀ xs Bm = (μ * ζ ^ (l : ℕ)) • 1 :=
    resMat_eq_smul_of_eigen hxsON hBlam
  have hBB : B * B = B * B := rfl
  set H := (hyperClosure p ⊤ E).comap π with hH
  set ε := ONExt.ext hσi hxsON with hε
  set HU := H.comap ε with hHU
  have hnorm : ∀ g ∈ HU, ∀ t : SUid σ₀ m, t * g * t⁻¹ ∈ HU := by
    refine conj_mem_of_tv hσ (by omega) h3m ?_
    intro a ha c hc g hg
    set w := orthoEmb xs a with hw
    have hwU : w ∈ U := hspan ▸ orthoEmb_mem_span xs a
    have hwB : Bm *ᵥ w = (μ * ζ ^ (l : ℕ)) • w := (hmemE _ _ w).1 hwU
    have hXkB : ∀ k : ℕ, Bm *ᵥ ((X ^ k) • w) = (μ * ζ ^ ((l : ℕ) + k)) • ((X ^ k) • w) :=
      fun k => hshiftk k _ w hwB
    have horthS : ∀ k k' : Fin p, herm σ₀ ((X ^ (k : ℕ)) • w) ((X ^ (k' : ℕ)) • w) = 0 := by
      intro k k'
      by_cases hkk : k = k'
      · subst hkk
        rw [herm_smul_smul, hw, herm_orthoEmb hxs, ha]
      · refine horthE B μ hμ hμN ((l : ℕ) + k) ((l : ℕ) + k') ?_ _ _ (hXkB k) (hXkB k')
        intro he
        apply hkk
        have h1 := Nat.ModEq.add_left_cancel' (l : ℕ) he
        exact Fin.ext (by rwa [Nat.ModEq, Nat.mod_eq_of_lt k.2, Nat.mod_eq_of_lt k'.2] at h1)
    obtain ⟨S, hS, hXS⟩ :=
      exists_siegel_orbit hσi (p := p) hXp (by rw [hσb]; exact hβN) horthS hc
    have hBS : B * S = S * B := siegel_comm_of_eigen hS
      (lam := fun k : Fin p => μ * ζ ^ ((l : ℕ) + k)) (fun k => by rw [smul_def]; exact hXkB k)
      (fun k => by rw [hσb]; exact hlamN μ hμN _)
    have hSH : S ∈ H := mem_hyperClosure_of_comm hp hE hcard hBE hXE hB1 hXB
      (by rw [← map_mul, ← map_mul, hBS]) (by rw [← map_mul, ← map_mul, hXS])
    have hSU : ∀ c', S • orthoEmb xs c' = ε (tv hσi ha hc) • orthoEmb xs c' := by
      intro c'
      have hc'U : orthoEmb xs c' ∈ U := hspan ▸ orthoEmb_mem_span xs c'
      rw [hS, ONExt.ext_tv_smul hσi hxsON ha hc, ← hw]
      congr 1
      rw [Finset.sum_eq_single (0 : Fin p)]
      · simp
      · intro k _ hk0
        have h0 : herm σ₀ ((X ^ (k : ℕ)) • w) (orthoEmb xs c') = 0 := by
          refine horthE B μ hμ hμN ((l : ℕ) + k) l ?_ _ _ (hXkB k) ((hmemE _ _ _).1 hc'U)
          intro he
          apply hk0
          have h1 : (l : ℕ) + k ≡ (l : ℕ) + 0 [MOD p] := by rw [add_zero]; exact he
          have h2 := Nat.ModEq.add_left_cancel' (l : ℕ) h1
          exact Fin.ext (by rwa [Nat.ModEq, Nat.mod_eq_of_lt k.2, Nat.zero_mod] at h2)
        rw [h0, mul_zero, zero_smul]
      · intro h0
        exact absurd (Finset.mem_univ _) h0
    set T := (ε (tv hσi ha hc))⁻¹ * S with hT
    have hTU : ∀ c', T • orthoEmb xs c' = orthoEmb xs c' := by
      intro c'
      rw [hT, mul_smul, hSU, inv_smul_smul]
    have hTU' : ∀ c', T⁻¹ • orthoEmb xs c' = orthoEmb xs c' := by
      intro c'
      rw [inv_smul_eq_iff, hTU]
    have hTres : ONExt.resMat σ₀ xs ((T : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [resMat_eq_smul_of_eigen hxsON (lam := 1) (fun c' => by rw [hTU, one_smul]), one_smul]
    have hTg : T * ε g = ε g * T :=
      commute_ext_of_resMat hσi hxsON (fun c' => ⟨c', hTU c'⟩) (fun c' => ⟨c', hTU' c'⟩)
        (by rw [hTres, Matrix.mul_one, Matrix.one_mul])
    have hS' : S = ε (tv hσi ha hc) * T := by rw [hT, mul_inv_cancel_left]
    have hconj : T * ε g * T⁻¹ = ε g := by rw [hTg, mul_inv_cancel_right]
    have key : ε (tv hσi ha hc * g * (tv hσi ha hc)⁻¹) = S * ε g * S⁻¹ := by
      calc ε (tv hσi ha hc * g * (tv hσi ha hc)⁻¹)
          = ε (tv hσi ha hc) * ε g * (ε (tv hσi ha hc))⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = ε (tv hσi ha hc) * (T * ε g * T⁻¹) * (ε (tv hσi ha hc))⁻¹ := by rw [hconj]
        _ = (ε (tv hσi ha hc) * T) * ε g * (ε (tv hσi ha hc) * T)⁻¹ := by group
        _ = S * ε g * S⁻¹ := by rw [← hS']
    show ε (tv hσi ha hc * g * (tv hσi ha hc)⁻¹) ∈ H
    rw [key]
    exact H.mul_mem (H.mul_mem hSH hg) (H.inv_mem hSH)
  have hBr_lin : Matrix.toLin' Bm * Matrix.toLin' rm = Matrix.toLin' rm * Matrix.toLin' Bm := by
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, Module.End.mul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, mulVec_mulVec, coe_comm hrB]
  obtain ⟨c₁, c₂, hc12, hJ₁, hJ₂⟩ := exists_two_eigen hζ hpK hp hrX hrB hBX hμ hBp hρ hrp
    (fun c hc => hr1 (hker' r ⟨c, hc⟩)) l hU0
  set J : Fin p × Fin p → Submodule K (Fin n → K) := fun ij =>
    Module.End.eigenspace (Matrix.toLin' Bm) (μ * ζ ^ (ij.1 : ℕ)) ⊓
      Module.End.eigenspace (Matrix.toLin' rm) (ρ * ζ ^ (ij.2 : ℕ)) with hJ
  have hJtop : ⨆ ij, J ij = ⊤ :=
    iSup_inf_eigenspace_eq_top hp hpK hζ hBr_lin hμ hρ (hpowT _ _ hBp) (hpowT _ _ hrp)
  have hJorth : ∀ ij ij' : Fin p × Fin p, ij ≠ ij' → ∀ u ∈ J ij, ∀ v ∈ J ij',
      herm σ₀ u v = 0 := by
    intro ij ij' hne u hu v hv
    by_cases h1 : ij.1 = ij'.1
    · have h2 : ij.2 ≠ ij'.2 := fun h2 => hne (Prod.ext h1 h2)
      exact horthE r ρ hρ hρN ij.2 ij'.2 (hmodne _ _ ij.2.2 ij'.2.2 (fun he => h2 (Fin.ext he)))
        u v ((hmemE _ _ u).1 hu.2) ((hmemE _ _ v).1 hv.2)
    · exact horthE B μ hμ hμN ij.1 ij'.1 (hmodne _ _ ij.1.2 ij'.1.2 (fun he => h1 (Fin.ext he)))
        u v ((hmemE _ _ u).1 hu.1) ((hmemE _ _ v).1 hv.1)
  have hJsep : ∀ ij, ((idForm h n).domRestrict₁₂ (J ij) (J ij)).SeparatingLeft :=
    NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n) J
      (fun ij ij' hne u hu v hv => by
        rw [Nonsplit.idForm_eq_herm h]; exact hJorth ij ij' hne u hu v hv) hJtop
  obtain ⟨e₁, he₁J, he₁⟩ := exists_unit_of_separatingLeft h hJ₁ (hJsep (l, c₁))
  obtain ⟨e₂, he₂J, he₂⟩ := exists_unit_of_separatingLeft h hJ₂ (hJsep (l, c₂))
  have he₁₂ : herm σ₀ e₁ e₂ = 0 := hJorth (l, c₁) (l, c₂) (fun he => hc12 (congrArg Prod.snd he))
    e₁ he₁J e₂ he₂J
  obtain ⟨d₁, hd₁⟩ := (mem_span_range_iff xs e₁).1 (hspan ▸ he₁J.1)
  obtain ⟨d₂, hd₂⟩ := (mem_span_range_iff xs e₂).1 (hspan ▸ he₂J.1)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζζ : ζ ≠ ζ⁻¹ := by
    intro he
    have h1 : ζ ^ 2 = 1 := by
      rw [sq]
      calc ζ * ζ = ζ * ζ⁻¹ := by rw [← he]
        _ = 1 := mul_inv_cancel₀ hζ0
    have := Nat.le_of_dvd (by norm_num) (hζ.dvd_of_pow_eq_one 2 h1)
    have := hp.two_le
    omega
  have hρζ : ∀ c : ℕ, ρ * ζ ^ c ≠ 0 := fun c => mul_ne_zero hρ (pow_ne_zero _ hζ0)
  obtain ⟨g₀, hg₀s, hg₀r⟩ := exists_nonscalar_comm hσ hxsON (hsU r hrB) (hsU' r hrB)
    (by rw [← herm_orthoEmb hxs, hd₁, he₁]) (by rw [← herm_orthoEmb hxs, hd₂, he₂])
    (by rw [← herm_orthoEmb hxs, hd₁, hd₂, he₁₂]) (hρζ c₁) (hρζ c₂)
    (by rw [hd₁, smul_def]; exact (hmemE _ _ _).1 he₁J.2)
    (by rw [hd₂, smul_def]; exact (hmemE _ _ _).1 he₂J.2) (d := ζ) (by rw [hσb]; exact hζN) hζζ
  have hg₀B : B * ε g₀ = ε g₀ * B :=
    commute_ext_of_resMat hσi hxsON (hsU B hBB) (hsU' B hBB)
      (by rw [hBres, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul])
  have hg₀HU : g₀ ∈ HU := by
    show π (ε g₀) ∈ hyperClosure p ⊤ E
    exact mem_hyperClosure_of_comm hp hE hcard hrE hBE hr1 hBr
      (by rw [← map_mul, ← map_mul, hg₀r]) (by rw [← map_mul, ← map_mul, hg₀B])
  have htop : HU = ⊤ := eq_top_of_normal_of_nonscalar hσ hm3 h3m hnorm hg₀HU hg₀s
  rw [← hspan]
  exact ONExt.allCenters_of_forall_ext_mem hσi hxsON fun g => by
    have : g ∈ HU := by rw [htop]; exact Subgroup.mem_top g
    exact this

theorem pow_mulVec_of_eigen {M : Matrix (Fin n) (Fin n) K} {c : K} {v : Fin n → K}
    (hv : M *ᵥ v = c • v) (t : ℕ) : (M ^ t) *ᵥ v = c ^ t • v := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← mulVec_mulVec, hv, mulVec_smul, ih, smul_smul, pow_succ,
      mul_comm]

theorem hyperGen_of_nonab_pth (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) (hq2 : ℓ ^ f ≠ 2) (hn : 2 * p < n) {G : Type*} [Group G] [Finite G]
    (π : SUid σ₀ n →* G) (hπ : Function.Surjective π)
    (hker' : ∀ g : SUid σ₀ n, (∃ c : K,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) → π g = 1)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    {X Y r : SUid σ₀ n} (hXE : π X ∈ E) (hYE : π Y ∈ E) (hrE : π r ∈ E) (hr1 : π r ≠ 1)
    (hYr : π Y ∉ Subgroup.zpowers (π r))
    (hXcl : π X ∉ Subgroup.closure ({π r, π Y} : Set G))
    (hrX : r * X = X * r) (hrY : r * Y = Y * r)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hζN : h.bar ζ * ζ = 1)
    (hYX : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {β ν ρ : K} (hXp : ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1)
    (hν : ν ≠ 0) (hYp : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ν ^ p) • 1)
    (hρ : ρ ≠ 0) (hrp : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ρ ^ p) • 1) :
    HyperGen p (⊤ : Subgroup G) E := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσi := hσ.invol
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hn0 : 0 < n := by omega
  have hexp : ∀ e ∈ E, e ^ p = 1 := hE.2
  have hrs : ∀ c : K, ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1 :=
    fun c hc => hr1 (hker' r ⟨c, hc⟩)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  set Xm : Matrix (Fin n) (Fin n) K := ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hXm
  set Ym : Matrix (Fin n) (Fin n) K := ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hYm
  set rm : Matrix (Fin n) (Fin n) K := ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hrm
  have hmemE : ∀ (M : Matrix (Fin n) (Fin n) K) (a : K) (v : Fin n → K),
      v ∈ Module.End.eigenspace (Matrix.toLin' M) a ↔ M *ᵥ v = a • v := fun M a v => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hpowT : ∀ (M : Matrix (Fin n) (Fin n) K) (c : K), M ^ p = c • 1 →
      (Matrix.toLin' M) ^ p = algebraMap K (Module.End K (Fin n → K)) c := by
    intro M c hM
    have h2 := congrArg Matrix.toLinAlgEquiv' hM
    rw [map_pow, map_smul, map_one] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
  have hνN := bar_mul_eq_one_of_SUid_pow h hp hp2 hpq hn0 hν hYp
  have hρN := bar_mul_eq_one_of_SUid_pow h hp hp2 hpq hn0 hρ hrp
  have hrcl : π r ∈ Subgroup.closure ({π r, π Y} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hYcl : π Y ∈ Subgroup.closure ({π r, π Y} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hYr' : Y * r = r * Y := hrY.symm
  have hBm : ∀ t : ℕ, (((Y * r ^ t : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Ym * rm ^ t := fun t => by
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val, hYm,
      hrm]
  have hBE : ∀ t : ℕ, π (Y * r ^ t) ∈ E := fun t => by
    rw [map_mul, map_pow]
    exact E.mul_mem hYE (E.pow_mem hrE t)
  have hBX : ∀ t : ℕ, (((Y * r ^ t : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Xm =
      ζ • (Xm * (((Y * r ^ t : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    intro t
    have hc : Commute rm Xm := coe_comm hrX
    rw [hBm, Matrix.mul_assoc, (hc.pow_left t).eq, ← Matrix.mul_assoc, hYX, Matrix.smul_mul,
      Matrix.mul_assoc]
  have hrB : ∀ t : ℕ, r * (Y * r ^ t) = (Y * r ^ t) * r := fun t => by
    rw [← mul_assoc, hrY, mul_assoc, mul_assoc, (Commute.self_pow r t).eq]
  have hBp : ∀ t : ℕ, (((Y * r ^ t : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p =
      ((ν * ρ ^ t) ^ p) • 1 := by
    intro t
    have := pow_word_of_comm hYr' hYp hrp 1 t
    rw [pow_one] at this
    rw [this]
    congr 1
    rw [pow_one, mul_pow, ← pow_mul, ← pow_mul, mul_comm t p]
  have hμ : ∀ t : ℕ, ν * ρ ^ t ≠ 0 := fun t => mul_ne_zero hν (pow_ne_zero _ hρ)
  have hBr : ∀ t : ℕ, π (Y * r ^ t) ∉ Subgroup.zpowers (π r) := by
    intro t hmem
    apply hYr
    have : π Y = π (Y * r ^ t) * ((π r) ^ t)⁻¹ := by
      rw [map_mul, map_pow, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ _))
  have hB1 : ∀ t : ℕ, π (Y * r ^ t) ≠ 1 := fun t h1 => hBr t (h1 ▸ Subgroup.one_mem _)
  have hXB : ∀ t : ℕ, π X ∉ Subgroup.zpowers (π (Y * r ^ t)) := by
    intro t hmem
    apply hXcl
    refine (Subgroup.zpowers_le.2 ?_) hmem
    rw [map_mul, map_pow]
    exact Subgroup.mul_mem _ hYcl (Subgroup.pow_mem _ hrcl t)
  have hdim : ∀ (t : ℕ) (l : Fin p), 3 ≤ Module.finrank K (Module.End.eigenspace
      (Matrix.toLin' (((Y * r ^ t : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        ((ν * ρ ^ t) * ζ ^ (l : ℕ))) := by
    intro t l
    by_contra hlt
    push Not at hlt
    have hsup := NonPth.iSup_eigenspace_eq_top_p hp hpK hζ (hμ t) (hpowT _ _ (hBp t))
    have h1 := finrank_iSup_le_sum (K := K) (fun l' : Fin p => Module.End.eigenspace
      (Matrix.toLin' (((Y * r ^ t : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        ((ν * ρ ^ t) * ζ ^ (l' : ℕ)))
    rw [hsup, finrank_top, Module.finrank_fin_fun] at h1
    have h2 : ∀ l' : Fin p, Module.finrank K (Module.End.eigenspace
        (Matrix.toLin' (((Y * r ^ t : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
          ((ν * ρ ^ t) * ζ ^ (l' : ℕ))) ≤ 2 := fun l' =>
      (finrank_eigen_le hζ (hBX t) _ l' l).trans (by omega)
    have h3 := Finset.sum_le_sum (s := Finset.univ) fun l' _ => h2 l'
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
    omega
  set H := (hyperClosure p ⊤ E).comap π with hH
  have hAll : ∀ (t : ℕ) (l : Fin p), AllCenters H (Module.End.eigenspace
      (Matrix.toLin' (((Y * r ^ t : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        ((ν * ρ ^ t) * ζ ^ (l : ℕ))) := fun t l =>
    allCenters_eigen_nonab h hp hp2 hpq hq2 π hker' hE hcard hXE (hBE t) hrE hr1 (hB1 t) (hBr t)
      (hXB t) hrX (hrB t) hζ hζN (hBX t) hXp (hμ t) (hBp t) hρ hrp l (hdim t l)
  have hY0 : (((Y * r ^ 0 : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Ym := by
    rw [hBm, pow_zero, Matrix.mul_one]
  set W : Fin p → Submodule K (Fin n → K) :=
    fun l => Module.End.eigenspace (Matrix.toLin' Ym) (ν * ζ ^ (l : ℕ)) with hW
  have hWeq : ∀ l : Fin p, W l = Module.End.eigenspace
      (Matrix.toLin' (((Y * r ^ 0 : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        ((ν * ρ ^ 0) * ζ ^ (l : ℕ)) := fun l => by
    rw [hY0, pow_zero, mul_one]
  have hWtop : ⨆ l, W l = ⊤ := NonPth.iSup_eigenspace_eq_top_p hp hpK hζ hν (hpowT _ _ hYp)
  have horthE : ∀ (s : SUid σ₀ n) (c : K), c ≠ 0 → h.bar c * c = 1 → ∀ a b : Fin p, a ≠ b →
      ∀ u v, ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u = (c * ζ ^ (a : ℕ)) • u →
        ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = (c * ζ ^ (b : ℕ)) • v →
        herm σ₀ u v = 0 := fun s c hc0 hcN a b hab u v hu hv =>
    herm_eq_zero_of_eigen hu hv (bar_mul_ne_one h hc0 hcN hζ hζN hab)
  have hWorth : ∀ l l' : Fin p, l ≠ l' → ∀ u ∈ W l, ∀ v ∈ W l', herm σ₀ u v = 0 :=
    fun l l' hll u hu v hv => horthE Y ν hν hνN l l' hll u v ((hmemE _ _ u).1 hu)
      ((hmemE _ _ v).1 hv)
  have hWsep : ∀ l, ((idForm h n).domRestrict₁₂ (W l) (W l)).SeparatingLeft :=
    NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n) W
      (fun l l' hne u hu v hv => by
        rw [Nonsplit.idForm_eq_herm h]; exact hWorth l l' hne u hu v hv) hWtop
  have hWON : ∀ l, HasONBasis σ₀ (W l) := by
    intro l
    refine Nonsplit.hasONBasis_of_separatingLeft h (W l) (hWsep l) ?_
    obtain ⟨s, hs0, hs1⟩ := Nonsplit.exists_norm_ne_one h hq2
    exact Or.inr ⟨by rw [hWeq]; exact hdim 0 l, s, hs0, by rw [hσb]; exact hs1⟩
  have hWAll : ∀ l, AllCenters H (W l) := fun l => by rw [hWeq]; exact hAll 0 l
  have hW0 : ∀ l, W l ≠ ⊥ := by
    intro l h0
    have := hdim 0 l
    rw [← hWeq, h0, finrank_bot] at this
    omega
  have hYr_lin : Matrix.toLin' Ym * Matrix.toLin' rm = Matrix.toLin' rm * Matrix.toLin' Ym := by
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, Module.End.mul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, mulVec_mulVec, coe_comm hrY]
  set J : Fin p × Fin p → Submodule K (Fin n → K) := fun ij =>
    W ij.1 ⊓ Module.End.eigenspace (Matrix.toLin' rm) (ρ * ζ ^ (ij.2 : ℕ)) with hJ
  have hJtop : ⨆ ij, J ij = ⊤ :=
    iSup_inf_eigenspace_eq_top hp hpK hζ hYr_lin hν hρ (hpowT _ _ hYp) (hpowT _ _ hrp)
  have hJorth : ∀ ij ij' : Fin p × Fin p, ij ≠ ij' → ∀ u ∈ J ij, ∀ v ∈ J ij',
      herm σ₀ u v = 0 := by
    intro ij ij' hne u hu v hv
    by_cases h1 : ij.1 = ij'.1
    · have h2 : ij.2 ≠ ij'.2 := fun h2 => hne (Prod.ext h1 h2)
      exact horthE r ρ hρ hρN ij.2 ij'.2 h2 u v ((hmemE _ _ u).1 hu.2) ((hmemE _ _ v).1 hv.2)
    · exact hWorth ij.1 ij'.1 h1 u hu.1 v hv.1
  have hJsep : ∀ ij, ((idForm h n).domRestrict₁₂ (J ij) (J ij)).SeparatingLeft :=
    NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n) J
      (fun ij ij' hne u hu v hv => by
        rw [Nonsplit.idForm_eq_herm h]; exact hJorth ij ij' hne u hu v hv) hJtop
  have hJshift : ∀ (l l' c : Fin p), J (l, c) ≠ ⊥ → J (l', c) ≠ ⊥ := by
    intro l l' c hne h0
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    set k := (l' : ℕ) + p - l with hk
    have h1 := mulVec_pow_smul_of_qcomm hYX k l v ((hmemE _ _ v).1 hv.1)
    have hlk : (l : ℕ) + k = l' + p := by have := l.2; omega
    rw [hlk, pow_add, hζ.pow_eq_one, mul_one] at h1
    have h2 : rm *ᵥ ((X ^ k) • v) = (ρ * ζ ^ (c : ℕ)) • ((X ^ k) • v) := by
      rw [smul_def, mulVec_mulVec, coe_comm (Commute.pow_right hrX k).eq, ← mulVec_mulVec,
        (hmemE _ _ v).1 hv.2, mulVec_smul]
    have hmem : (X ^ k) • v ∈ J (l', c) := ⟨(hmemE _ _ _).2 h1, (hmemE _ _ _).2 h2⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hv0 (by simpa using congrArg (fun w => (X ^ k)⁻¹ • w) hmem)
  have hmix : ∀ l l' : Fin p, l ≠ l' →
      ∃ w₁ ∈ W l, ∃ w₂ ∈ W l', w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ IsCenter H (w₁ + w₂) := by
    intro l l' hll
    obtain ⟨c₁, c₂, hc12, hJ₁, hJ₂⟩ :=
      exists_two_eigen hζ hpK hp hrX hrY hYX hν hYp hρ hrp hrs l (hW0 l)
    have hJ₂' : J (l', c₂) ≠ ⊥ := hJshift l l' c₂ hJ₂
    obtain ⟨e₁, he₁J, he₁⟩ := exists_unit_of_separatingLeft h hJ₁ (hJsep (l, c₁))
    obtain ⟨e₂, he₂J, he₂⟩ := exists_unit_of_separatingLeft h hJ₂' (hJsep (l', c₂))
    obtain ⟨u, hu⟩ := hσ.exists_norm_neg_one
    have hcz : ((c₁ : ℕ) : ZMod p) - ((c₂ : ℕ) : ZMod p) ≠ 0 := by
      intro h0
      apply hc12
      rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt c₁.2,
        Nat.mod_eq_of_lt c₂.2] at h0
      exact Fin.ext h0
    set t : ℕ := ((((l' : ℕ) : ZMod p) - ((l : ℕ) : ZMod p)) *
      (((c₁ : ℕ) : ZMod p) - ((c₂ : ℕ) : ZMod p))⁻¹).val with ht
    have htZ : (t : ZMod p) = (((l' : ℕ) : ZMod p) - ((l : ℕ) : ZMod p)) *
        (((c₁ : ℕ) : ZMod p) - ((c₂ : ℕ) : ZMod p))⁻¹ := ZMod.natCast_zmod_val _
    have hcong : ((l : ℕ) + c₁ * t) % p = ((l' : ℕ) + c₂ * t) % p := by
      rw [← ZMod.natCast_eq_natCast_iff']
      push_cast
      have key : ((c₁ : ℕ) : ZMod p) * t - ((c₂ : ℕ) : ZMod p) * t =
          ((l' : ℕ) : ZMod p) - ((l : ℕ) : ZMod p) := by
        rw [← sub_mul, htZ, mul_comm, mul_assoc, inv_mul_cancel₀ hcz, mul_one]
      linear_combination key
    set kk : Fin p := ⟨((l : ℕ) + c₁ * t) % p, Nat.mod_lt _ hp.pos⟩ with hkk
    have hBv : ∀ (a c : Fin p) (v : Fin n → K), v ∈ J (a, c) →
        (((Y * r ^ t : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
          ((ν * ρ ^ t) * ζ ^ (((a : ℕ) + c * t) % p)) • v := by
      intro a c v hv
      rw [hBm, ← mulVec_mulVec, pow_mulVec_of_eigen ((hmemE _ _ v).1 hv.2), mulVec_smul,
        (hmemE _ _ v).1 hv.1, smul_smul, ← pow_eq_pow_mod hζ]
      congr 1
      rw [pow_add, mul_pow, ← pow_mul]
      ring
    have he₁B := hBv l c₁ e₁ he₁J
    have he₂B := hBv l' c₂ e₂ he₂J
    rw [← hcong] at he₂B
    have hw₂ : u • e₂ ∈ W l' := (W l').smul_mem u he₂J.1
    have he₁0 : e₁ ≠ 0 := by rintro rfl; rw [herm_zero_left] at he₁; exact zero_ne_one he₁
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at hu
      exact (neg_ne_zero.mpr one_ne_zero) hu.symm
    have he₂0 : u • e₂ ≠ 0 := by
      rintro h0
      rcases smul_eq_zero.1 h0 with h1 | h1
      · exact hu0 h1
      · rw [h1, herm_zero_left] at he₂; exact zero_ne_one he₂
    refine ⟨e₁, he₁J.1, u • e₂, hw₂, he₁0, he₂0, hAll t kk _ ?_ ?_⟩
    · rw [hmemE, mulVec_add, mulVec_smul, he₁B, he₂B, smul_add, smul_comm u]
    · have h12 := hWorth l l' hll e₁ he₁J.1 (u • e₂) hw₂
      have h21 := hWorth l' l (Ne.symm hll) (u • e₂) hw₂ e₁ he₁J.1
      rw [herm_add_left, herm_add_right, herm_add_right, h12, h21, he₁, herm_smul_left,
        herm_smul_right, he₂, mul_one, hu]
      ring
  have hn4 : 4 ≤ n := by have := hp.two_le; omega
  have : Nonempty (Fin p) := ⟨⟨0, hp.pos⟩⟩
  have hHtop : H = ⊤ :=
    Centers.eq_top_of_blocks hσ hn4 W hWON hWorth hWAll hmix hWtop
  intro k _
  obtain ⟨g, rfl⟩ := hπ k
  have hg : g ∈ H := by rw [hHtop]; exact Subgroup.mem_top g
  exact hg

end BlockC

section ChoiceC

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem closure_triple_eq {G : Type*} [Group G] [Finite G] (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) {x y z : G} (hxE : x ∈ E) (hyE : y ∈ E)
    (hzE : z ∈ E) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x)
    (hz : z ∉ Subgroup.closure ({x, y} : Set G)) :
    Subgroup.closure ({x, y, z} : Set G) = E := by
  have hS2 : Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 2 :=
    card_closure_pair_of_not_mem hp hE hxE hyE hx1 hyx
  have hle23 : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.closure ({x, y, z} : Set G) :=
    Subgroup.closure_mono (by intro w hw; rcases hw with rfl | rfl <;> simp)
  have hle3E : Subgroup.closure ({x, y, z} : Set G) ≤ E :=
    (Subgroup.closure_le E).2 (by
      intro w hw
      rcases hw with rfl | rfl | rfl
      exacts [hxE, hyE, hzE])
  have hd1 := Subgroup.card_dvd_of_le hle23
  have hd2 := Subgroup.card_dvd_of_le hle3E
  rw [hS2] at hd1
  rw [hcard] at hd2
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hp).1 hd2
  have hk2 : 2 ≤ k := by
    rw [hk] at hd1
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hd1
  have hk3' : k = 3 := by
    by_contra hne
    have hk2' : k = 2 := by omega
    rw [hk2'] at hk
    have heq := Subgroup.eq_of_le_of_card_ge hle23 (by rw [hk, hS2])
    exact hz (heq ▸ Subgroup.subset_closure (by simp))
  rw [hk3'] at hk
  exact Subgroup.eq_of_le_of_card_ge hle3E (by rw [hk, hcard])

theorem exists_comm_scalar (hn : 0 < n) {G : Type*} [Group G] (π : SUid σ₀ n →* G)
    (hker : ∀ g ∈ π.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    {E : Subgroup G} (hE : IsElemAbelian p E) {a b : SUid σ₀ n} (ha : π a ∈ E)
    (hb : π b ∈ E) :
    ∃ c : K, ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • (((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∧ c ^ p = 1 := by
  have hcommE : π b * π a = π a * π b :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨π b, hb⟩ ⟨π a, ha⟩)
  have h1 : π (b * a * b⁻¹ * a⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcommE]
    group
  obtain ⟨c, hc⟩ := hker _ h1
  have hrel : ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • (((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    have e : b * a = (b * a * b⁻¹ * a⁻¹) * (a * b) := by group
    have := congrArg (fun g : SUid σ₀ n => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) e
    simp only [Subgroup.coe_mul, Units.val_mul] at this
    rw [this]
    have hc' : ((((b * a * b⁻¹ * a⁻¹ : SUid σ₀ n) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) = c • 1 := hc
    simp only [Subgroup.coe_mul, Units.val_mul] at hc'
    rw [hc', Matrix.smul_mul, Matrix.one_mul]
  refine ⟨c, hrel, ?_⟩
  have hap : π (a ^ p) = 1 := by rw [map_pow]; exact hE.2 _ ha
  obtain ⟨α, hα⟩ := hker _ hap
  have hα' : (((a : GL (Fin n) K) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1 := by
    rw [← hα, Subgroup.coe_pow]
  have hα0 : α ≠ 0 := scalar_ne_zero_of_matPow hn (by rw [← Units.val_pow_eq_pow_val]; exact hα')
  exact pow_eq_one_of_smul_comm_p hn hα0 hα' hrel

theorem comm_of_scalar {σ : K ≃+* K} {z : SUid σ n} {c : K}
    (hz : ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) (s : SUid σ n) :
    z * s = s * z := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hz, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem eq_mul_scalar {G : Type*} [Group G] (π : SUid σ₀ n →* G)
    (hker : ∀ g ∈ π.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    {s w : SUid σ₀ n} (hsw : π w = π s) :
    ∃ z : SUid σ₀ n, (∃ c : K, ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) ∧
      s = w * z :=
  ⟨w⁻¹ * s, hker _ (by rw [MonoidHom.mem_ker, map_mul, map_inv, hsw, inv_mul_cancel]),
    by rw [mul_inv_cancel_left]⟩

theorem exists_radical (hp : p.Prime) (hn : 0 < n) {G : Type*} [Group G] [Finite G]
    (π : SUid σ₀ n →* G) (hπ : Function.Surjective π)
    (hker : ∀ g ∈ π.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    {a b : SUid σ₀ n} (ha : π a ∈ E) (hb : π b ∈ E) (hab : a * b ≠ b * a) :
    π a ≠ 1 ∧ π b ∉ Subgroup.zpowers (π a) ∧
    ∃ r : SUid σ₀ n, π r ∈ E ∧ π r ∉ Subgroup.closure ({π a, π b} : Set G) ∧
      r * a = a * r ∧ r * b = b * r ∧ ∀ s : SUid σ₀ n, π s ∈ E → r * s = s * r := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have ha1 : π a ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := hker a h1
    exact hab (comm_of_scalar hc b)
  have hba : π b ∉ Subgroup.zpowers (π a) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    obtain ⟨z, hz, hbz⟩ := eq_mul_scalar π hker (s := b) (w := a ^ k) (by rw [map_zpow, hk])
    apply hab
    obtain ⟨c, hc⟩ := hz
    have hza : z * a = a * z := comm_of_scalar hc a
    rw [hbz]
    calc a * (a ^ k * z) = a ^ (1 + k) * z := by rw [← mul_assoc, ← _root_.zpow_one_add]
      _ = a ^ (k + 1) * z := by rw [add_comm]
      _ = a ^ k * a * z := by rw [_root_.zpow_add_one]
      _ = a ^ k * z * a := by rw [mul_assoc, ← hza, ← mul_assoc]
  obtain ⟨c, hcba, hcp⟩ := exists_comm_scalar hn π hker hE ha hb
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hab
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hcba, one_smul]
  have hζc : IsPrimitiveRoot c p := by
    rw [← orderOf_eq_prime hcp hc1]
    exact IsPrimitiveRoot.orderOf c
  have hc0 : c ≠ 0 := hζc.ne_zero hp.ne_zero
  have hc2 : Nat.card (Subgroup.closure ({π a, π b} : Set G)) = p ^ 2 :=
    card_closure_pair_of_not_mem hp hE ha hb ha1 hba
  obtain ⟨e₀, he₀E, he₀⟩ := exists_not_mem_of_card hp hcard (k := 2) (by norm_num) hc2
  obtain ⟨e, rfl⟩ := hπ e₀
  obtain ⟨d₁, hd₁, hd₁p⟩ := exists_comm_scalar hn π hker hE he₀E ha
  obtain ⟨d₂, hd₂, hd₂p⟩ := exists_comm_scalar hn π hker hE he₀E hb
  obtain ⟨s₁, hs₁, hcs₁⟩ := hζc.eq_pow_of_pow_eq_one hd₁p
  obtain ⟨s₂, hs₂, hcs₂⟩ := hζc.eq_pow_of_pow_eq_one hd₂p
  set am : Matrix (Fin n) (Fin n) K := ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with ham
  set bm : Matrix (Fin n) (Fin n) K := ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hbm
  set em : Matrix (Fin n) (Fin n) K := ((e : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hem
  set i := p - s₂ with hi
  set j := s₁ with hj
  set r := e * a ^ i * b ^ j with hr
  have hrm : ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = em * am ^ i * bm ^ j := by
    simp only [hr, Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val,
      hem, ham, hbm]
  have hbaj : bm ^ j * am = c ^ j • (am * bm ^ j) := qcommMat_pow_left hcba j
  have hbai : bm * am ^ i = c ^ i • (am ^ i * bm) := by
    have := qcommMat_pow_pow hcba i 1
    simpa only [pow_one, mul_one] using this
  have hra : r * a = a * r := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hrm]
    calc em * am ^ i * bm ^ j * am = em * am ^ i * (bm ^ j * am) := by
          simp only [Matrix.mul_assoc]
      _ = c ^ j • (em * (am ^ i * am) * bm ^ j) := by
          rw [hbaj, Matrix.mul_smul]
          simp only [Matrix.mul_assoc]
      _ = c ^ j • (em * am * am ^ i * bm ^ j) := by
          rw [← pow_succ, pow_succ']
          simp only [Matrix.mul_assoc]
      _ = (d₁ • (em * am)) * am ^ i * bm ^ j := by
          rw [hcs₁, Matrix.smul_mul, Matrix.smul_mul]
      _ = am * (em * am ^ i * bm ^ j) := by
          rw [← hd₁]
          simp only [Matrix.mul_assoc]
  have hrb : r * b = b * r := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hrm]
    have hci : d₂ * c ^ i = 1 := by
      rw [← hcs₂, hi, ← pow_add, Nat.add_sub_cancel' hs₂.le, hcp]
    symm
    calc bm * (em * am ^ i * bm ^ j) = (bm * em) * am ^ i * bm ^ j := by
          simp only [Matrix.mul_assoc]
      _ = d₂ • (em * (bm * am ^ i) * bm ^ j) := by
          rw [hd₂, Matrix.smul_mul, Matrix.smul_mul]
          simp only [Matrix.mul_assoc]
      _ = (d₂ * c ^ i) • (em * am ^ i * (bm * bm ^ j)) := by
          rw [hbai, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
          simp only [Matrix.mul_assoc]
      _ = em * am ^ i * bm ^ j * bm := by
          rw [hci, one_smul, ← pow_succ', pow_succ]
          simp only [Matrix.mul_assoc]
  have hacl : π a ∈ Subgroup.closure ({π a, π b} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hbcl : π b ∈ Subgroup.closure ({π a, π b} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hrE : π r ∈ E := by
    rw [hr, map_mul, map_mul, map_pow, map_pow]
    exact E.mul_mem (E.mul_mem he₀E (E.pow_mem ha _)) (E.pow_mem hb _)
  have hrcl : π r ∉ Subgroup.closure ({π a, π b} : Set G) := by
    intro hmem
    apply he₀
    have : π e = π r * ((π a) ^ i * (π b) ^ j)⁻¹ := by
      rw [hr, map_mul, map_mul, map_pow, map_pow]
      group
    rw [this]
    exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ hacl _) (Subgroup.pow_mem _ hbcl _)))
  refine ⟨ha1, hba, r, hrE, hrcl, hra, hrb, fun s hs => ?_⟩
  have hcl3 := closure_triple_eq hp hE hcard ha hb hrE ha1 hba hrcl
  have hsmem : π s ∈ (Subgroup.closure ({a, b, r} : Set (SUid σ₀ n))).map π := by
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
      hcl3]
    exact hs
  obtain ⟨w, hw, hws⟩ := hsmem
  have hwr : Subgroup.closure ({a, b, r} : Set (SUid σ₀ n)) ≤ Subgroup.centralizer {r} := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hx with rfl | rfl | rfl
    · exact hra.symm
    · exact hrb.symm
    · rfl
  have hrw : r * w = w * r := (Subgroup.mem_centralizer_singleton_iff.1 (hwr hw)).symm
  obtain ⟨z, ⟨cz, hcz⟩, rfl⟩ := eq_mul_scalar π hker hws
  rw [← mul_assoc, hrw, mul_assoc, ← comm_of_scalar hcz r, mul_assoc]

theorem exists_heis_pair (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) (hn : 0 < n) {G : Type*} [Group G] [Finite G] (π : SUid σ₀ n →* G)
    (hker : ∀ g ∈ π.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    {a b r : SUid σ₀ n} (ha : π a ∈ E) (hb : π b ∈ E) (hab : a * b ≠ b * a) (ha1 : π a ≠ 1)
    (hba : π b ∉ Subgroup.zpowers (π a)) (hrE : π r ∈ E)
    (hrcl : π r ∉ Subgroup.closure ({π a, π b} : Set G)) (hra : r * a = a * r)
    (hrb : r * b = b * r) :
    ∃ (X Y : SUid σ₀ n) (ζ ν : K), π X ∈ E ∧ π Y ∈ E ∧ π Y ∉ Subgroup.zpowers (π r) ∧
      π X ∉ Subgroup.closure ({π r, π Y} : Set G) ∧ r * X = X * r ∧ r * Y = Y * r ∧
      IsPrimitiveRoot ζ p ∧ h.bar ζ * ζ = 1 ∧
      ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∧
      ν ≠ 0 ∧ ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ν ^ p) • 1 := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hexp : ∀ e ∈ E, e ^ p = 1 := hE.2
  obtain ⟨c, hcba, hcp⟩ := exists_comm_scalar hn π hker hE ha hb
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hab
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hcba, one_smul]
  have hζc : IsPrimitiveRoot c p := by
    rw [← orderOf_eq_prime hcp hc1]
    exact IsPrimitiveRoot.orderOf c
  have hc0 : c ≠ 0 := hζc.ne_zero hp.ne_zero
  set am : Matrix (Fin n) (Fin n) K := ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with ham
  set bm : Matrix (Fin n) (Fin n) K := ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hbm
  have hap : π (a ^ p) = 1 := by rw [map_pow]; exact hexp _ ha
  have hbp : π (b ^ p) = 1 := by rw [map_pow]; exact hexp _ hb
  obtain ⟨α, hα⟩ := hker _ hap
  obtain ⟨β, hβ⟩ := hker _ hbp
  have hα' : am ^ p = α • 1 := by rw [← hα, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hβ' : bm ^ p = β • 1 := by rw [← hβ, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hα0 : α ≠ 0 := scalar_ne_zero_of_matPow hn hα'
  have hβ0 : β ≠ 0 := scalar_ne_zero_of_matPow hn hβ'
  obtain ⟨i, j, hij, ν, hν⟩ :=
    exists_pth_power_word hp (dvd_card_sub_one_of_unitary h hpq) hα0 hβ0
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hν
    exact mul_ne_zero (pow_ne_zero _ hα0) (pow_ne_zero _ hβ0) hν.symm
  set Y := a ^ i * b ^ j with hY
  have hYm : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = am ^ i * bm ^ j := by
    simp only [hY, Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val,
      ham, hbm]
  have hYp : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = (ν ^ p) • 1 := by
    rw [hYm, pow_word_p hp hp2 hα' hβ' hcba hcp i j, hν]
  have hYE : π Y ∈ E := by
    rw [hY, map_mul, map_pow, map_pow]
    exact E.mul_mem (E.pow_mem ha _) (E.pow_mem hb _)
  have hrY : r * Y = Y * r := ((Commute.pow_right hra i).mul_right (Commute.pow_right hrb j)).eq
  have hacl : π a ∈ Subgroup.closure ({π a, π b} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hbcl : π b ∈ Subgroup.closure ({π a, π b} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hYcl : π Y ∈ Subgroup.closure ({π a, π b} : Set G) := by
    rw [hY, map_mul, map_pow, map_pow]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hacl _) (Subgroup.pow_mem _ hbcl _)
  have hY1 : π Y ≠ 1 := by
    intro h1
    rw [hY, map_mul, map_pow, map_pow] at h1
    exact hij (dvd_of_pow_mul_pow_eq_one hp (hexp _ ha) (hexp _ hb) ha1 hba h1)
  have hr1 : π r ≠ 1 := fun h1 => hrcl (h1 ▸ Subgroup.one_mem _)
  have hYr : π Y ∉ Subgroup.zpowers (π r) := by
    intro hmem
    apply hrcl
    have hle : Subgroup.zpowers (π Y) ≤ Subgroup.zpowers (π r) := Subgroup.zpowers_le.2 hmem
    have heq := Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (hexp _ hrE) hr1,
        orderOf_eq_prime (hexp _ hYE) hY1])
    have : π r ∈ Subgroup.zpowers (π Y) := heq ▸ Subgroup.mem_zpowers (π r)
    exact Subgroup.zpowers_le.2 hYcl this
  obtain ⟨X, ζ, hXab, hζ, hYX⟩ : ∃ (X : SUid σ₀ n) (ζ : K), (X = a ∨ X = b) ∧
      IsPrimitiveRoot ζ p ∧
      ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ζ • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    by_cases hj : p ∣ j
    · have hi : ¬ p ∣ i := fun hi => hij ⟨hi, hj⟩
      refine ⟨b, (c ^ i)⁻¹, Or.inr rfl,
        (hζc.pow_of_coprime i (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hi))).inv,
        ?_⟩
      rw [hYm]
      exact planeW_comm_caseII hcba hc0 i j
    · refine ⟨a, c ^ j, Or.inl rfl,
        hζc.pow_of_coprime j (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hj)), ?_⟩
      rw [hYm]
      exact planeW_comm_caseI hcba i j
  have hXE : π X ∈ E := by rcases hXab with rfl | rfl <;> assumption
  have hXcl' : π X ∈ Subgroup.closure ({π a, π b} : Set G) := by
    rcases hXab with rfl | rfl <;> assumption
  have hrX : r * X = X * r := by rcases hXab with rfl | rfl <;> assumption
  have hζN : h.bar ζ * ζ = 1 := by
    rw [h.bar_apply, ← pow_succ]
    obtain ⟨k, hk⟩ := hpq
    rw [hk, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨X, Y, ζ, ν, hXE, hYE, hYr, ?_, hrX, hrY, hζ, hζN, hYX, hν0, hYp⟩
  have hXY : π X ∉ Subgroup.zpowers (π Y) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    obtain ⟨z, ⟨cz, hcz⟩, hXz⟩ := eq_mul_scalar π hker (s := X) (w := Y ^ k) (by rw [map_zpow, hk])
    have hcomm : X * Y = Y * X := by
      rw [hXz, mul_assoc, comm_of_scalar hcz Y, ← mul_assoc, ← (Commute.self_zpow Y k).eq,
        mul_assoc]
    have hM := coe_comm hcomm
    rw [← hM] at hYX
    have h1 : (1 - ζ) • (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 0 := by
      rw [sub_smul, one_smul, ← hYX, sub_self]
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact hζ.ne_one hp.one_lt (sub_eq_zero.1 h2).symm
    · have h3 : (((X * Y : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 0 := by
        simp only [Subgroup.coe_mul, Units.val_mul]
        exact h2
      have h4 := ((mem_SUid_iff σ₀).1 (X * Y).2).1
      haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      rw [h3, Matrix.det_zero] at h4
      exact zero_ne_one h4
  intro hmem
  have hcXY : Nat.card (Subgroup.closure ({π Y, π X} : Set G)) = p ^ 2 :=
    card_closure_pair_of_not_mem hp hE hYE hXE hY1 hXY
  have hcab : Nat.card (Subgroup.closure ({π a, π b} : Set G)) = p ^ 2 :=
    card_closure_pair_of_not_mem hp hE ha hb ha1 hba
  have hcrY : Nat.card (Subgroup.closure ({π r, π Y} : Set G)) = p ^ 2 :=
    card_closure_pair_of_not_mem hp hE hrE hYE hr1 (fun hm => hYr hm)
  have hle1 : Subgroup.closure ({π Y, π X} : Set G) ≤ Subgroup.closure ({π a, π b} : Set G) :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hYcl, Set.singleton_subset_iff.2 hXcl'⟩)
  have hle2 : Subgroup.closure ({π Y, π X} : Set G) ≤ Subgroup.closure ({π r, π Y} : Set G) :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2
      ⟨Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), Set.singleton_subset_iff.2 hmem⟩)
  have heq1 := Subgroup.eq_of_le_of_card_ge hle1 (by rw [hcXY, hcab])
  have heq2 := Subgroup.eq_of_le_of_card_ge hle2 (by rw [hcXY, hcrY])
  apply hrcl
  rw [← heq1, heq2]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

end ChoiceC

section Model

open TauCeti

theorem exists_model {m : ℕ} {q : PrimePower} (hv : (LieTypeIndex.twistedA m q).Valid) :
    ∃ (ℓ f : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : Fact ℓ.Prime) (_ : CharP K ℓ)
      (h : UnitaryFieldData ℓ f K) (π : unitarySU ℓ f K (m + 1) →* Cat ⟨.twistedA m q, hv⟩),
      ℓ ^ f = q.card ∧ Function.Surjective π ∧
      (∀ g ∈ π.ker, ∃ c : K,
        ((g : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = c • 1) ∧
      (∀ g : unitarySU ℓ f K (m + 1), (∃ c : K,
        ((g : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = c • 1) →
        π g = 1) := by
  set ℓ := ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ with hℓ
  set f := ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ with hf
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f
    (ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have hfact : Fact ℓ.Prime := ⟨hU.prime⟩
  have hfin : Finite (GaloisField ℓ (2 * f)) := hU.finite
  have hchar : CharP (GaloisField ℓ (2 * f)) ℓ := hU.charP
  have hqc : ℓ ^ f = q.card := card_twistedA m q hv
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv
  let π₀ : unitarySU ℓ f (GaloisField ℓ (2 * f)) (m + 1) →*
      StatedProj (StatedSU (m + 1) (ℓ ^ f) (GaloisField ℓ (2 * f))) :=
    QuotientGroup.mk' ((StatedScalars (Fin (m + 1)) (GaloisField ℓ (2 * f))).subgroupOf
      (StatedSU (m + 1) (ℓ ^ f) (GaloisField ℓ (2 * f))))
  refine ⟨ℓ, f, GaloisField ℓ (2 * f), inferInstance, hfin, hfact, hchar, hU,
    e.symm.toMonoidHom.comp π₀, hqc, e.symm.surjective.comp (QuotientGroup.mk'_surjective _),
    fun g hg => ?_, fun g ⟨c, hc⟩ => ?_⟩
  · rw [MonoidHom.mem_ker] at hg
    have h1 : π₀ g = 1 := by
      have : e.symm (π₀ g) = e.symm 1 := by rw [map_one]; exact hg
      exact e.symm.injective this
    have h2 := (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 h2
    refine ⟨(c : GaloisField ℓ (2 * f)), ?_⟩
    have : ((g : GL (Fin (m + 1)) (GaloisField ℓ (2 * f))) : Matrix (Fin (m + 1)) (Fin (m + 1))
        (GaloisField ℓ (2 * f))) = (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c :
          GL (Fin (m + 1)) (GaloisField ℓ (2 * f))) := congrArg Units.val hc.symm
    rw [this, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  · have hc0 : c ≠ 0 := by
      rintro rfl
      have hdet := ((mem_unitarySU_iff hU).1 g.2).1
      haveI : Nonempty (Fin (m + 1)) := ⟨0⟩
      rw [hc, zero_smul, Matrix.det_zero] at hdet
      exact zero_ne_one hdet
    show e.symm (π₀ g) = 1
    rw [MulEquiv.map_eq_one_iff]
    show (QuotientGroup.mk' _ g : StatedProj (StatedSU (m + 1) (ℓ ^ f) (GaloisField ℓ (2 * f)))) =
      1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, hc, Units.val_mk0, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]

end Model

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryAux

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryAux

@[expose] def UNonabRestLift (d : TauCeti.ValidLieTypeIndex) (p : ℕ) (E₀ : Subgroup (Cat d)) :
    Prop :=
  ∃ (ℓ f n : ℕ) (K : Type) (_ : Field K)
    (_ : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f K)
    (π : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (n + 1) →* Cat d),
    Function.Surjective π ∧
    (∀ g ∈ π.ker, ∃ c : K,
      ((g : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = c • 1) ∧
    p ∣ ℓ ^ f + 1 ∧ ℓ ^ f ≠ 2 ∧
    (∃ x y : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (n + 1), π x ∈ E₀ ∧ π y ∈ E₀ ∧
      x * y ≠ y * x) ∧
    (n + 1 ≤ 2 * p ∨ ∃ r : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (n + 1),
      π r ∈ E₀ ∧ π r ≠ 1 ∧
      (∀ s : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (n + 1), π s ∈ E₀ →
        r * s = s * r) ∧
      ¬ ∃ c : K, ((r : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) ^ p = c ^ p • 1)

@[expose] def SeitzGoodInnerUnitaryNonabRest : Prop :=
  SeitzHyperLie fun d p E₀ => UToralRestPrime d p ∧ ¬ UReducible d p E₀ ∧ SeitzGoodIndex p d.1 ∧
    UNonabRestLift d p E₀

theorem seitzGoodInnerUnitaryNonDiag_of_nonabRest (hC : SeitzGoodInnerUnitaryNonabRest) :
    SeitzGoodInnerUnitaryNonDiag := by
  classical
  rintro ⟨d, hv⟩ p hp hp2 hpd hlist E₀ hE hcard ⟨⟨m, q, hd, hpq, hq⟩, hred, hgood, hdiag⟩
  simp only at hd
  subst hd
  have hq2 : q.card ≠ 2 := by
    intro hq2
    have hp3 : p = 3 := by
      rw [hq2] at hpq
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpq
    subst hp3
    rcases hgood with hng | hsix
    · exact hng (SeitzHyperGoodInAux.exc_of_twistedA_card_two hv hq2)
    · rcases hsix with h1 | h1 | h1
      · exact h1
      · exact h1
      · obtain ⟨⟨h2, h3⟩, -⟩ := h1
        rw [TauCeti.PrimePower.card_def, h2, h3] at hq2
        norm_num at hq2
  obtain ⟨ℓ, f, K, _, _, _, _, h, π, hqc, hπ, hker, hker'⟩ := exists_model hv
  have hpq' : p ∣ ℓ ^ f + 1 := by rw [hqc]; exact hpq
  have hq2' : ℓ ^ f ≠ 2 := by rw [hqc]; exact hq2
  let ε : CFSG.LieType.Universal.Unitary.SUid (CFSG.LieType.BorelTits.unitaryInvolution K ℓ f)
      (m + 1) ≃* CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (m + 1) :=
    MulEquiv.subgroupCongr (suid_unitaryInvolution_eq h (m + 1))
  let πS := π.comp ε.toMonoidHom
  have hπS : Function.Surjective πS := hπ.comp ε.surjective
  have hkerS : ∀ g ∈ πS.ker, ∃ c : K,
      ((g : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = c • 1 :=
    fun g hg => hker (ε g) hg
  have hkerS' : ∀ g : CFSG.LieType.Universal.Unitary.SUid
      (CFSG.LieType.BorelTits.unitaryInvolution K ℓ f) (m + 1), (∃ c : K,
        ((g : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = c • 1) →
      πS g = 1 :=
    fun g hg => hker' (ε g) hg
  have hπSε : ∀ x : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (m + 1),
      πS (ε.symm x) = π x := fun x => by
    show π (ε (ε.symm x)) = π x
    rw [MulEquiv.apply_symm_apply]
  haveI : Finite (Cat ⟨.twistedA m q, hv⟩) := Finite.of_surjective πS hπS
  by_cases hab : ∀ x y : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (m + 1), π x ∈ E₀ →
      π y ∈ E₀ → x * y = y * x
  ·
    have hpow : ¬ ∀ x : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K (m + 1), π x ∈ E₀ →
        x ^ (ℓ ^ f + 1) = 1 :=
      fun hpow => hdiag ⟨ℓ, f, m, K, inferInstance, h, π, hπ, hker, hpq', hq2', hab, hpow⟩
    push Not at hpow
    obtain ⟨x, hxE, hx⟩ := hpow
    have hcommS : ∀ a b : CFSG.LieType.Universal.Unitary.SUid
        (CFSG.LieType.BorelTits.unitaryInvolution K ℓ f) (m + 1), πS a ∈ E₀ → πS b ∈ E₀ →
        a * b = b * a := fun a b ha hb =>
      ε.injective (by rw [map_mul, map_mul]; exact hab _ _ ha hb)
    set x' := ε.symm x with hx'
    have hx'E : πS x' ∈ E₀ := by rw [hx', hπSε]; exact hxE
    have hxp1 : πS (x' ^ p) = 1 := by rw [map_pow]; exact hE.2 _ hx'E
    obtain ⟨α, hα⟩ := hkerS (x' ^ p) hxp1
    have hxp : ((x' : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) ^ p =
        α • 1 := by
      rw [← hα, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    have hxx' : ((x : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
        ((x' : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := rfl
    have hα' : ¬ ∃ c : K, c ^ p = α := by
      rintro ⟨c, rfl⟩
      apply hx
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact scalar_ne_zero_of_matPow (Nat.succ_pos m) hxp (zero_pow hp.ne_zero)
      have hcN := bar_mul_eq_one_of_SUid_pow h hp hp2 hpq' (Nat.succ_pos m) hc0 hxp
      obtain ⟨t, ht⟩ := hpq'
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hxx', ht, pow_mul, hxp, smul_pow, one_pow,
        ← pow_mul, ← ht, planeW_pow_card_succ h hcN, one_smul]
      rfl
    exact hyperGen_of_nonpth h hp hp2 hpq' hq2' (Nat.succ_pos m) πS hπS hkerS hkerS' hE hcard
      hcommS hx'E hxp hα'
  ·
    push Not at hab
    obtain ⟨x, y, hxE, hyE, hxy⟩ := hab
    set a := ε.symm x with ha
    set b := ε.symm y with hb
    have haE : πS a ∈ E₀ := by rw [ha, hπSε]; exact hxE
    have hbE : πS b ∈ E₀ := by rw [hb, hπSε]; exact hyE
    have hab' : a * b ≠ b * a := by
      intro he
      apply hxy
      have := congrArg ε he
      rwa [map_mul, map_mul, ha, hb, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        at this
    obtain ⟨ha1, hba, r, hrE, hrcl, hra, hrb, hrc⟩ :=
      exists_radical hp (Nat.succ_pos m) πS hπS hkerS hE hcard haE hbE hab'
    have hr1 : πS r ≠ 1 := fun h1 => hrcl (h1 ▸ Subgroup.one_mem _)
    by_cases hcase : (∃ ρ : K, ρ ≠ 0 ∧
        ((r : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) ^ p = (ρ ^ p) • 1) ∧
        2 * p < m + 1
    ·
      obtain ⟨⟨ρ, hρ, hrp⟩, hn⟩ := hcase
      obtain ⟨X, Y, ζ, ν, hXE, hYE, hYr, hXcl, hrX, hrY, hζ, hζN, hYX, hν, hYp⟩ :=
        exists_heis_pair h hp hp2 hpq' (Nat.succ_pos m) πS hkerS hE hcard haE hbE hab' ha1 hba
          hrE hrcl hra hrb
      have hXp1 : πS (X ^ p) = 1 := by rw [map_pow]; exact hE.2 _ hXE
      obtain ⟨β, hβ⟩ := hkerS (X ^ p) hXp1
      have hXp : ((X : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) ^ p =
          β • 1 := by
        rw [← hβ, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
      exact hyperGen_of_nonab_pth h hp hp2 hpq' hq2' hn πS hπS hkerS' hE hcard hXE hYE hrE hr1
        hYr hXcl hrX hrY hζ hζN hYX hXp hν hYp hρ hrp
    ·
      refine hC ⟨.twistedA m q, hv⟩ p hp hp2 hpd hlist E₀ hE hcard
        ⟨⟨m, q, rfl, hpq, hq⟩, hred, hgood, ℓ, f, m, K, inferInstance, h, π, hπ, hker, hpq',
          hq2', ⟨x, y, hxE, hyE, hxy⟩, ?_⟩
      by_cases hn : 2 * p < m + 1
      · right
        refine ⟨ε r, hrE, hr1, fun s hs => ?_, ?_⟩
        · have := hrc (ε.symm s) (by rw [hπSε]; exact hs)
          have h2 := congrArg ε this
          rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
        · rintro ⟨c, hc⟩
          apply hcase
          refine ⟨⟨c, fun hc0 => ?_, hc⟩, hn⟩
          rw [hc0, zero_pow hp.ne_zero] at hc
          exact scalar_ne_zero_of_matPow (Nat.succ_pos m) hc rfl
      · left
        omega

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
