module

public import CFSG.ClassicalInvolution.Phan.PhanDn.KleinWedge
public import CFSG.RankThree.PartOne.K159.Klein
public import CFSG.LieType.BorelTits.Families
public import CFSG.ClassicalInvolution.Phan.PhanDn.Perp
public import CFSG.ClassicalInvolution.Phan.PhanDn.FlipFrame

public section

namespace CFSG.ClassicalInvolution.PhanDn

open Matrix Module CFSG.RankThree.PartOne.K159 CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K}

private noncomputable def orthSubtype :
    TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K) →*
      Module.End K (Fin 3 ⊕ Fin 3 → K) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (Subgroup.subtype (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)))

omit [CharP K 2] in
private theorem orthSubtype_isometry
    (h : TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)) :
    ∀ v, (quadPlusForm 3 K).Q (orthSubtype h v) = (quadPlusForm 3 K).Q v := by
  intro v
  simp only [quadPlusForm_Q]
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp h.2 v

noncomputable def kleinDickson :
    TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K) →* Multiplicative (ZMod 2) :=
  (quadPlusForm 3 K).dicksonHom orthSubtype orthSubtype_isometry (isLagrangian_stdLag 3 K)

omit [CharP K 2] in
theorem kleinDickson_eq_one_iff
    (L : TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)) :
    kleinDickson L = 1 ↔
      Even (3 - finrank K ↥((stdLag 3 K).map
        ((L : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)).toLinearMap) ⊓
          stdLag 3 K)) := by
  rw [kleinDickson, QuadForm.dicksonHom_apply, ofAdd_eq_one, dicksonInvariant,
    inf_comm, ZMod.natCast_eq_zero_iff_even, finrank_stdLag]
  rfl

private noncomputable def rhoOrth :
    SpecialLinearGroup (Fin 4) K →*
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K) :=
  (Klein.rho : SpecialLinearGroup (Fin 4) K →* _).codRestrict _ Klein.rho_mem

theorem kleinDickson_rho (g : SpecialLinearGroup (Fin 4) K) :
    kleinDickson ⟨Klein.rho g, Klein.rho_mem g⟩ = 1 := by
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 4) K) :=
    (Klein.sl4_isSimpleGroup_and_perfect (K := K)).2
  let f : SpecialLinearGroup (Fin 4) K →* Multiplicative (ZMod 2) :=
    kleinDickson.comp rhoOrth
  have hf : ∀ x, f x = 1 := by
    intro x
    have hx : x ∈ commutator (SpecialLinearGroup (Fin 4) K) := by
      rw [hperf.commutator_eq_top]
      exact Subgroup.mem_top x
    exact Abelianization.commutator_subset_ker f hx
  exact hf g

private def swapZero : Equiv.Perm (Fin 3 ⊕ Fin 3) :=
  Equiv.swap (Sum.inl 0) (Sum.inr 0)

private noncomputable def swapZeroLin :
    (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K) :=
  LinearEquiv.funCongrLeft K K swapZero

omit [CharP K 2] in
private theorem quadPlus_swapZero (v : Fin 3 ⊕ Fin 3 → K) :
    quadPlus 3 K (swapZeroLin v) = quadPlus 3 K v := by
  rw [quadPlus_apply, quadPlus_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [swapZeroLin, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    swapZero]
  norm_num [Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_def]
  ring

omit [CharP K 2] in
private theorem mem_stdLag_iff (v : Fin 3 ⊕ Fin 3 → K) :
    v ∈ stdLag 3 K ↔ v (Sum.inr 0) = 0 ∧ v (Sum.inr 1) = 0 ∧ v (Sum.inr 2) = 0 := by
  rw [stdLag, LinearMap.mem_ker]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simpa using And.intro h0 (And.intro h1 h2)
  · rintro ⟨h0, h1, h2⟩
    funext i
    fin_cases i <;> simp [h0, h1, h2]

omit [CharP K 2] in
private theorem stdLag_map_swapZero_inf :
    (stdLag 3 K).map swapZeroLin.toLinearMap ⊓ stdLag 3 K =
      Submodule.span K ({stdE (K := K) 1, stdE (K := K) 2} :
        Set (Fin 3 ⊕ Fin 3 → K)) := by
  ext v
  rw [Submodule.mem_inf, Submodule.mem_map_equiv]
  constructor
  · rintro ⟨hmap, hstd⟩
    rw [mem_stdLag_iff] at hmap hstd
    obtain ⟨h0, h1, h2⟩ := hmap
    obtain ⟨g0, g1, g2⟩ := hstd
    have hv0 : v (Sum.inl 0) = 0 := by
      simpa [swapZeroLin, LinearEquiv.funCongrLeft_symm, swapZero] using h0
    rw [Submodule.mem_span_pair]
    refine ⟨v (Sum.inl 1), v (Sum.inl 2), ?_⟩
    funext x
    rcases x with i | i <;> fin_cases i <;> simp [stdE, g0, g1, g2, hv0]
  · intro hv
    rw [Submodule.mem_span_pair] at hv
    obtain ⟨a, b, rfl⟩ := hv
    constructor
    · rw [mem_stdLag_iff]
      simp [swapZeroLin, LinearEquiv.funCongrLeft_symm, swapZero, stdE,
        Equiv.swap_apply_of_ne_of_ne]
    · rw [mem_stdLag_iff]
      simp [stdE]

omit [CharP K 2] in
private theorem finrank_span_stdE_one_two :
    finrank K (Submodule.span K
      ({stdE (K := K) 1, stdE (K := K) 2} : Set (Fin 3 ⊕ Fin 3 → K))) = 2 := by
  have hli : LinearIndependent K (![stdE (K := K) 1, stdE (K := K) 2] :
      Fin 2 → (Fin 3 ⊕ Fin 3 → K)) := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrFun hab (Sum.inl 1)
    have h2 := congrFun hab (Sum.inl 2)
    simp [stdE] at h1 h2
    exact ⟨h1, h2⟩
  have hset : ({stdE (K := K) 1, stdE (K := K) 2} : Set (Fin 3 ⊕ Fin 3 → K)) =
      Set.range ![stdE (K := K) 1, stdE (K := K) 2] := by
    ext x
    simp [or_comm]
  rw [hset, finrank_span_eq_card hli]
  simp

omit [CharP K 2] in
private theorem kleinDickson_swapZero_ne_one :
    kleinDickson (K := K) ⟨swapZeroLin (K := K), by
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro v
      exact quadPlus_swapZero v⟩ ≠ 1 := by
  intro h
  have hEven := (kleinDickson_eq_one_iff _).mp h
  rw [stdLag_map_swapZero_inf, finrank_span_stdE_one_two] at hEven
  norm_num at hEven

theorem exists_rho_eq [Finite K]
    (L : TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K))
    (hL : kleinDickson L = 1) :
    ∃ g, Klein.rho g = (L : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) := by
  classical
  let R : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)) :=
    (rhoOrth (K := K)).range
  have hRinj : Function.Injective (rhoOrth (K := K)) := by
    intro a b h
    exact Klein.rho_injective (congrArg Subtype.val h)
  have hRle : R ≤ (kleinDickson (K := K)).ker := by
    rintro _ ⟨g, rfl⟩
    exact kleinDickson_rho g
  have hRcard : Nat.card R = Nat.card (SpecialLinearGroup (Fin 4) K) := by
    let e : SpecialLinearGroup (Fin 4) K ≃* R := MonoidHom.ofInjective hRinj
    exact (Nat.card_congr e.toEquiv).symm
  have hidx : R.index = 2 := by
    have h1 := Subgroup.card_mul_index R
    rw [hRcard, Klein.card_orthogonalGroup_quadPlus_three] at h1
    rw [mul_comm (2 : ℕ) (Nat.card (SpecialLinearGroup (Fin 4) K))] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hcoatom : IsCoatom R :=
    Subgroup.isCoatom_of_index_prime (by rw [hidx]; norm_num)
  have hker_ne_top : (kleinDickson (K := K)).ker ≠ ⊤ := by
    intro htop
    let Ls : TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K) :=
      ⟨swapZeroLin (K := K), by
        rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
        intro v
        exact quadPlus_swapZero v⟩
    have hmem : Ls ∈ (kleinDickson (K := K)).ker := by
      rw [htop]
      exact Subgroup.mem_top Ls
    exact kleinDickson_swapZero_ne_one (MonoidHom.mem_ker.mp hmem)
  have hker_eq : (kleinDickson (K := K)).ker = R := by
    by_contra hne
    have hlt : R < (kleinDickson (K := K)).ker := lt_of_le_of_ne hRle (Ne.symm hne)
    exact hker_ne_top ((hcoatom.lt_iff).mp hlt)
  have hLker : L ∈ (kleinDickson (K := K)).ker := hL
  rw [hker_eq] at hLker
  have hLker' : L ∈ (rhoOrth (K := K)).range := by simpa [R] using hLker
  obtain ⟨g, hg⟩ := hLker'
  exact ⟨g, congrArg Subtype.val hg⟩

omit [CharP K 2] in
private theorem det_map_coe (g : SpecialLinearGroup (Fin 4) K) :
    ((g : Matrix (Fin 4) (Fin 4) K).map σ).det = 1 := by
  change ((g : Matrix (Fin 4) (Fin 4) K).map (σ : K →+* K)).det = 1
  rw [← RingHom.mapMatrix_apply (σ : K →+* K) (g : Matrix (Fin 4) (Fin 4) K)]
  rw [← RingHom.map_det (σ : K →+* K) (g : Matrix (Fin 4) (Fin 4) K), g.2, map_one]

omit [CharP K 2] in
private theorem det_inverseTranspose_map (g : SpecialLinearGroup (Fin 4) K) :
    ((((g : Matrix (Fin 4) (Fin 4) K).map σ)⁻¹)ᵀ).det = 1 := by
  rw [Matrix.det_transpose, Matrix.det_nonsing_inv, det_map_coe (σ := σ) g,
    Ring.inverse_one]

private theorem conjTr_mul_self_of_rho_comm (hσ : ∀ x, σ (σ x) = x)
    (g : SpecialLinearGroup (Fin 4) K)
    (h : ∀ w, Klein.rho g (dFlip σ w) = dFlip σ (Klein.rho g w)) :
    conjTr σ (g : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K) = 1 := by
  let g' : SpecialLinearGroup (Fin 4) K :=
    ⟨(((g : Matrix (Fin 4) (Fin 4) K).map σ)⁻¹)ᵀ,
      det_inverseTranspose_map (σ := σ) g⟩
  have hstep : ∀ w, dFlip σ (Klein.rho g w) = Klein.rho g' (dFlip σ w) := by
    intro w
    have hc := dFlip_cong (σ := σ) (Matrix.SpecialLinearGroup.toGL g) w
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hc
    rw [Klein.rho_apply, hc, g.2, map_one, one_smul, Klein.rho_apply]
  have hrho : Klein.rho g = Klein.rho g' := by
    ext v
    rw [show v = dFlip σ (dFlip σ v) from (dFlip_dFlip hσ v).symm]
    rw [h (dFlip σ v), hstep (dFlip σ v)]
  have hg : g = g' := Klein.rho_injective hrho
  have hmat : (g : Matrix (Fin 4) (Fin 4) K) =
      (((g : Matrix (Fin 4) (Fin 4) K).map σ)⁻¹)ᵀ := by
    simpa [g'] using congrArg
      (fun x : SpecialLinearGroup (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K)) hg
  have hT : (g : Matrix (Fin 4) (Fin 4) K).transpose =
      (((g : Matrix (Fin 4) (Fin 4) K).map σ)⁻¹) := by
    simpa using congrArg Matrix.transpose hmat
  have hdet : ((g : Matrix (Fin 4) (Fin 4) K).map σ).det = 1 :=
    det_map_coe (σ := σ) g
  have hright : (g : Matrix (Fin 4) (Fin 4) K).transpose *
      ((g : Matrix (Fin 4) (Fin 4) K).map σ) = 1 := by
    rw [hT]
    exact Matrix.nonsing_inv_mul _ (by rw [hdet]; exact isUnit_one)
  have htrans := congrArg Matrix.transpose hright
  simpa [conjTr, Matrix.transpose_mul, Matrix.transpose_transpose] using htrans

theorem exists_SUid_of_rho_comm (hσ : ∀ x, σ (σ x) = x)
    (g : SpecialLinearGroup (Fin 4) K)
    (h : ∀ w, Klein.rho g (dFlip σ w) = dFlip σ (Klein.rho g w)) :
    ∃ u : SUid σ 4, ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = g := by
  have hconj := conjTr_mul_self_of_rho_comm (σ := σ) hσ g h
  have hiso : ∀ x y, herm σ ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ x)
      ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ y) = herm σ x y := by
    intro x y
    rw [herm_mulVec, hconj, Matrix.one_mulVec]
  let u : SUid σ 4 := mkSU σ (g : Matrix (Fin 4) (Fin 4) K) g.2 hiso
  exact ⟨u, rfl⟩

end CFSG.ClassicalInvolution.PhanDn

end
