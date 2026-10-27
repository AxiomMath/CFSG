module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6CompsAux
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealEigen
import CFSG.HardMathSupport.Dickson.Bal207.CompShape

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

namespace U6Heis

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Dickson.I271
open scoped commutatorElement

open Polynomial CFSG.HardMathSupport.Dickson.Sec6.I1431
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryScalar CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.RankThree.PartOne.KCUnitaryExact CFSG.RankThree.PartOne.KCUnitaryBlock
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks
open Matrix

section ON3

variable {K0 : Type} [Field K0]

theorem exists_on_triple (h : UnitaryFieldData 2 3 K0) (A : primeFormUnitary h (idGram K0 6))
    (hA3 : (A : GL (Fin 6) K0) ^ 3 = 1) {d : K0}
    (hd : 3 ≤ eigMult (A : GL (Fin 6) K0) d) :
    ∃ b₁ b₂ b₃ : Fin 6 → K0, IsONPair h b₁ b₂ ∧ IsONPair h b₁ b₃ ∧
      LinearIndependent K0 ![b₁, b₂, b₃] ∧ U6Comps.xlin h A b₁ = d • b₁ ∧
      U6Comps.xlin h A b₂ = d • b₂ ∧ U6Comps.xlin h A b₃ = d • b₃ := by
  classical
  obtain ⟨κ, hκ3, hκ1⟩ := u6r_exists_primitive_cube_root h
  have hζ : IsPrimitiveRoot κ 3 := by
    have := IsPrimitiveRoot.orderOf κ
    rwa [orderOf_eq_prime hκ3 hκ1] at this
  have hx3 : U6Comps.xlin h A ^ 3 = 1 := by
    have : ((t6psub_toLin A : LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) :
        Module.End K0 (Fin 6 → K0)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, t6psub_toLin, ← map_pow, hA3, map_one, Units.val_one]
    exact this
  obtain ⟨b, μ, hbμ, hb⟩ :=
    CFSG.RankThree.PartOne.KCUnitaryPlane.exists_orthonormal_common_eigenbasis h hζ
      (by norm_num) (idForm_isSymm (h := h) (n := 6)) (idForm_separatingLeft (h := h) (n := 6))
      (fun _ : Unit => U6Comps.xlin h A) (fun _ _ => Commute.refl _) (fun _ => hx3)
      (fun _ v w => (mem_sesqUnitaryGroup.mp (toLinU_mem A)) v w)
  have hrepr : ∀ w : Fin 6 → K0, ∀ j, b.repr (U6Comps.xlin h A w) j = μ () j * b.repr w j := by
    intro w j
    have h1 : U6Comps.xlin h A w = ∑ i, (b.repr w i * μ () i) • b i := by
      conv_lhs => rw [← b.sum_repr w]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hbμ (), smul_smul]
    rw [h1, b.repr_sum_self, mul_comm]
  set S : Finset (Fin (Module.finrank K0 (Fin 6 → K0))) :=
    Finset.univ.filter fun j => μ () j = d with hS
  have hspan : (U6Comps.xlin h A).eigenspace d ≤
      Submodule.span K0 (Set.range fun j : S => b j) := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [← b.sum_repr v]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j ∈ S
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    · have hμj : μ () j ≠ d := by
        intro hμ; exact hj (by simp [hS, hμ])
      have h2 := hrepr v j
      rw [hv, map_smul, Finsupp.smul_apply, smul_eq_mul] at h2
      have h3 : b.repr v j = 0 := by
        have : (d - μ () j) * b.repr v j = 0 := by rw [sub_mul, h2, sub_self]
        exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hμj))
      rw [h3, zero_smul]
      exact Submodule.zero_mem _
  have hcard : 3 ≤ S.card := by
    have h1 := Submodule.finrank_mono hspan
    have h2 := finrank_range_le_card (R := K0) (fun j : S => b j)
    have h3 : eigMult (A : GL (Fin 6) K0) d =
        Module.finrank K0 ((U6Comps.xlin h A).eigenspace d) := by
      rw [U6Comps.eigMult_eq_finrank, U6Comps.primaryComponent_X_sub_C_eq_eigenspace]
    rw [Fintype.card_coe, Set.finrank] at h2
    omega
  obtain ⟨j₁, j₂, j₃, hj₁, hj₂, hj₃, h12, h13, h23⟩ :=
    (Finset.two_lt_card_iff (s := S)).1 (by omega)
  have hon : IsOrthonormalFamily h (fun j => (b j : Fin 6 → K0)) := fun i j => hb i j
  have hev : ∀ j ∈ S, U6Comps.xlin h A (b j) = d • b j := by
    intro j hj
    have : μ () j = d := by simpa [hS] using hj
    rw [hbμ (), this]
  exact ⟨b j₁, b j₂, b j₃, hon.pair h12, hon.pair h13, hon.linearIndependent_triple h12 h13 h23,
    hev j₁ hj₁, hev j₂ hj₂, hev j₃ hj₃⟩

end ON3

section BlockFix

variable {K0 : Type} [Field K0]

@[expose] noncomputable def blockSU (h : UnitaryFieldData 2 3 K0)
    (A : primeFormUnitary h (idGram K0 6)) (d : K0) : Subgroup (gramSU h (idGram K0 6)) :=
  (specialBlock (idForm h 6) (t6psub_toLin A) (X - C d)).comap (toLinSU h 6)

theorem torusUnitary_mem_specialBlock (h : UnitaryFieldData 2 3 K0)
    (A : primeFormUnitary h (idGram K0 6))
    (H : UnitaryPrimaryData h.bar (idForm h 6) (toLinU h 6 A)) {μ : K0}
    (hμ : h.bar μ * μ = 1)
    (ha : (X - C μ : K0[X]) ∈ primaryFactors ((toLinU h 6 A :
      LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) : Module.End K0 (Fin 6 → K0)))
    {b₁ b₂ : Fin 6 → K0} (hb : IsONPair h b₁ b₂)
    (hx₁ : ((toLinU h 6 A : LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) :
      Module.End K0 (Fin 6 → K0)) b₁ = μ • b₁)
    (hx₂ : ((toLinU h 6 A : LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) :
      Module.End K0 (Fin 6 → K0)) b₂ = μ • b₂) (c : K0ˣ) (hc : h.norm (c : K0) = 1) :
    toLinU h 6 (torusUnitary h hb c hc) ∈ specialBlock (idForm h 6) (toLinU h 6 A) (X - C μ) := by
  set T := torusUnitary h hb c hc with hT
  have hTmat : (((T : primeFormUnitary h (idGram K0 6)) : GL (Fin 6) K0) :
      Matrix (Fin 6) (Fin 6) K0) = torusMat h b₁ b₂ c := rfl
  have hgapply : ∀ v, ((toLinU h 6 T : LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) :
      Module.End K0 (Fin 6 → K0)) v = torusMat h b₁ b₂ c *ᵥ v := fun v => by
    rw [toLinU_apply_eq, hTmat]
  have hxiso := toLinU_mem A
  refine mem_specialBlock_of_degree_one H hμ ha (toLinU_mem T) ?_ ?_ ?_
  · show (_ : Module.End K0 (Fin 6 → K0)) * _ = _ * _
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hgapply, hgapply, torusMat_mulVec,
      torusMat_mulVec, map_add, map_add, map_smul, map_smul, hx₁, hx₂,
      idForm_apply_of_eigen h hxiso hμ hx₁, idForm_apply_of_eigen h hxiso hμ hx₂]
    module
  · intro v hv
    have h1 : idForm h 6 b₁ v = 0 := hv b₁ (by simp [mem_primaryComponent, hx₁])
    have h2 : idForm h 6 b₂ v = 0 := hv b₂ (by simp [mem_primaryComponent, hx₂])
    rw [hgapply, torusMat_mulVec, h1, h2]
    simp
  · have : ((toLinU h 6 T : LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) :
        Module.End K0 (Fin 6 → K0)) = Matrix.toLin' (torusMat h b₁ b₂ c) :=
      LinearMap.ext fun v => by rw [hgapply, Matrix.toLin'_apply]
    rw [this, LinearMap.det_toLin']
    exact det_torusMat h hb c.ne_zero

theorem isPerfect_blockSU_map (h : UnitaryFieldData 2 3 K0) (A : primeFormUnitary h (idGram K0 6))
    (hA3 : (A : GL (Fin 6) K0) ^ 3 = 1) {d : K0} (hd : 2 ≤ eigMult (A : GL (Fin 6) K0) d) :
    Group.IsPerfect ↥((blockSU h A d).map (gramSUToUnitary h (idGram K0 6))) := by
  haveI := h.finite
  haveI : Finite (GL (Fin 6) K0) :=
    Finite.of_injective (fun g : GL (Fin 6) K0 => (g : Matrix (Fin 6) (Fin 6) K0))
      Units.val_injective
  obtain ⟨hd3, i, hi⟩ := U6Comps.exists_goodIdx h A hA3 hd
  have H := primaryData_toLin' h A.2 Nat.prime_three (by norm_num : 3 ≠ 2) (c := 1)
    (by rw [hA3, map_one])
  have hB : blockSU h A d = t6psub_block A i := by
    unfold blockSU t6psub_block
    rw [hi]
    rfl
  have hperf : ⁅blockSU h A d, blockSU h A d⁆ = blockSU h A d := by
    rw [hB]
    exact Subgroup.isPerfect_iff.1 (t6psub_isQuasisimple_block A H i).1
  rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, hperf]

theorem torusUnitary_mem_blockSU_map (h : UnitaryFieldData 2 3 K0)
    (A : primeFormUnitary h (idGram K0 6)) (hA3 : (A : GL (Fin 6) K0) ^ 3 = 1) {d : K0}
    (hd3 : d ^ 3 = 1) {b b' : Fin 6 → K0} (hb : IsONPair h b b')
    (hx : U6Comps.xlin h A b = d • b) (hx' : U6Comps.xlin h A b' = d • b') (c : K0ˣ)
    (hc : h.norm (c : K0) = 1) :
    torusUnitary h hb c hc ∈ (blockSU h A d).map (gramSUToUnitary h (idGram K0 6)) := by
  have H := primaryData_toLin' h A.2 Nat.prime_three (by norm_num : 3 ≠ 2) (c := 1)
    (by rw [hA3, map_one])
  have hdd : h.bar d * d = 1 :=
    CFSG.RankThree.PartOne.KCUnitaryPlane.bar_eq_inv_of_pow_eq_one h (by norm_num) hd3
  have hmem : (X - C d : K0[X]) ∈ primaryFactors ((toLinU h 6 A :
      LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) : Module.End K0 (Fin 6 → K0)) :=
    u6r_mem_primaryFactors A ((u6r_mem_primaryComponent_iff A d b).2 hx) hb.ne_zero_left
  have hT := torusUnitary_mem_specialBlock h A H hdd hmem hb hx hx' c hc
  have hdet := det_torusUnitary h hb c hc
  refine ⟨⟨((torusUnitary h hb c hc : primeFormUnitary h (idGram K0 6)) : GL (Fin 6) K0),
    (torusUnitary h hb c hc).2, hdet⟩, Subgroup.mem_comap.2 hT, rfl⟩

theorem fieldFactor_eq_one_of_fixes_block (h : UnitaryFieldData 2 3 K0)
    (A : primeFormUnitary h (idGram K0 6)) (hA3 : (A : GL (Fin 6) K0) ^ 3 = 1) {d : K0}
    (hd : 3 ≤ eigMult (A : GL (Fin 6) K0) d) (ψ : MulAut (primeFormP h (idGram K0 6)))
    (hψ : ∀ t ∈ U6Comps.blockImage h A d, ψ t = t) :
    primeFormFieldFactor h (isPrimeFormGram_idGram (K := K0) (n := 6)) (by norm_num)
      (by norm_num) ψ = 1 := by
  obtain ⟨⟨M, τ⟩, rfl⟩ := primeFormPsi_surjective h
    (isPrimeFormGram_idGram (K := K0) (n := 6)) (by norm_num) (by norm_num) ψ
  rw [primeFormFieldFactor_psi]
  show τ = 1
  obtain ⟨hd3, -⟩ := U6Comps.exists_goodIdx h A hA3 (d := d) (by omega)
  obtain ⟨b₁, b₂, b₃, h12, h13, hind, e₁, e₂, e₃⟩ := exists_on_triple h A hA3 hd
  have hperf := isPerfect_blockSU_map h A hA3 (d := d) (by omega)
  have hβ : ∀ g ∈ (blockSU h A d).map (gramSUToUnitary h (idGram K0 6)),
      primeFormPsi h (isPrimeFormGram_idGram (K := K0) (n := 6)) ⟨M, τ⟩ *
        primeFormConjHom h (idGram K0 6) g = primeFormConjHom h (idGram K0 6) g *
        primeFormPsi h (isPrimeFormGram_idGram (K := K0) (n := 6)) ⟨M, τ⟩ := by
    rintro g ⟨s, hs, rfl⟩
    have hs' : ((s : gramSU h (idGram K0 6)) : primeFormP h (idGram K0 6)) ∈
        U6Comps.blockImage h A d := ⟨s, hs, rfl⟩
    have hfix := hψ _ hs'
    rw [show primeFormConjHom h (idGram K0 6) (gramSUToUnitary h (idGram K0 6) s) =
      MulAut.conj ((s : gramSU h (idGram K0 6)) : primeFormP h (idGram K0 6)) from
        primeFormConjHom_eq_conj h (idGram K0 6) s]
    refine MulEquiv.ext fun z => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfix]
  have hcomm := matrix_comm_of_perfect (by norm_num) (by norm_num) hperf M τ hβ
  refine tau_eq_one_of_torus h (M : GL (Fin 6) K0).isUnit h12 h13 hind ?_ ?_
  · intro c hc
    exact hcomm _ (torusUnitary_mem_blockSU_map h A hA3 hd3 h12 e₁ e₂ c hc)
  · intro c hc
    exact hcomm _ (torusUnitary_mem_blockSU_map h A hA3 hd3 h13 e₁ e₃ c hc)

theorem comm_conj_of_fixes (h : UnitaryFieldData 2 3 K0) (A : primeFormUnitary h (idGram K0 6))
    (d : K0) (ψ : MulAut (primeFormP h (idGram K0 6)))
    (hψ : ∀ t ∈ U6Comps.blockImage h A d, ψ t = t) :
    ∀ g ∈ (blockSU h A d).map (gramSUToUnitary h (idGram K0 6)),
      ψ * primeFormConjHom h (idGram K0 6) g = primeFormConjHom h (idGram K0 6) g * ψ := by
  rintro g ⟨s, hs, rfl⟩
  have hs' : ((s : gramSU h (idGram K0 6)) : primeFormP h (idGram K0 6)) ∈
      U6Comps.blockImage h A d := ⟨s, hs, rfl⟩
  have hfix := hψ _ hs'
  rw [show primeFormConjHom h (idGram K0 6) (gramSUToUnitary h (idGram K0 6) s) =
    MulAut.conj ((s : gramSU h (idGram K0 6)) : primeFormP h (idGram K0 6)) from
      primeFormConjHom_eq_conj h (idGram K0 6) s]
  refine MulEquiv.ext fun z => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfix]

theorem scalar_of_conj_fixes_block (h : UnitaryFieldData 2 3 K0)
    (A : primeFormUnitary h (idGram K0 6)) (hA3 : (A : GL (Fin 6) K0) ^ 3 = 1) {d : K0}
    (hd : 2 ≤ eigMult (A : GL (Fin 6) K0) d) (M : primeFormUnitary h (idGram K0 6))
    (hMA : M * A = A * M)
    (hfix : ∀ t ∈ U6Comps.blockImage h A d, primeFormConjHom h (idGram K0 6) M t = t) :
    ∃ c : K0, ∀ v : Fin 6 → K0, U6Comps.xlin h A v = d • v →
      ((M : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) *ᵥ v = c • v := by
  haveI := h.finite
  haveI : Finite (GL (Fin 6) K0) :=
    Finite.of_injective (fun g : GL (Fin 6) K0 => (g : Matrix (Fin 6) (Fin 6) K0))
      Units.val_injective
  obtain ⟨hd3, i, hi⟩ := U6Comps.exists_goodIdx h A hA3 hd
  have H := primaryData_toLin' h A.2 Nat.prime_three (by norm_num : 3 ≠ 2) (c := 1)
    (by rw [hA3, map_one])
  have hperf := isPerfect_blockSU_map h A hA3 hd
  have hψ : primeFormPsi h (isPrimeFormGram_idGram (K := K0) (n := 6)) ⟨M, 1⟩ =
      primeFormConjHom h (idGram K0 6) M := by
    rw [primeFormPsi_apply, map_one, mul_one]
  have hβ := comm_conj_of_fixes h A d (primeFormConjHom h (idGram K0 6) M) hfix
  have hcomm := matrix_comm_of_perfect (by norm_num) (by norm_num) hperf M 1
    (by rw [hψ]; exact hβ)
  have hcomm1 : ∀ g ∈ (blockSU h A d).map (gramSUToUnitary h (idGram K0 6)),
      M * g = g * M := by
    intro g hg
    have := hcomm g hg
    rw [show (⇑(1 : K0 ≃+* K0) : K0 → K0) = id from rfl, Matrix.map_id] at this
    exact Subtype.ext (Units.ext this)
  have hmem : (X - C d : K0[X]) ∈ primaryFactors ((t6psub_toLin A :
      LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) : Module.End K0 (Fin 6 → K0)) := hi ▸ i.1.2
  have hia : i.1 = ⟨X - C d, hmem⟩ := Subtype.ext hi
  have hgood : IsGoodBlock h (t6psub_toLin A) ⟨X - C d, hmem⟩ := hia ▸ i.2
  have hY : toLinU h 6 M ∈ unitaryCentralizer (idForm h 6) (t6psub_toLin A) :=
    mem_unitaryCentralizer.mpr ⟨toLinU_mem M, (commute_toLinU hMA).units_val⟩
  have hblock : ∀ g ∈ specialBlock (idForm h 6) (t6psub_toLin A) (X - C d),
      Commute (toLinU h 6 M) g := by
    intro g hg
    have hrange : specialBlock (idForm h 6) (t6psub_toLin A) (X - C d) ≤
        (toLinSU h 6).range := by
      have := t6psub_specialBlock_le_range A H i
      rwa [hi] at this
    obtain ⟨s, hsg⟩ := hrange hg
    have hs : s ∈ blockSU h A d := by
      show toLinSU h 6 s ∈ specialBlock (idForm h 6) (t6psub_toLin A) (X - C d)
      rw [hsg]
      exact hg
    have e1 : toLinU h 6 (gramSUToUnitary h (idGram K0 6) s) = g := hsg
    rw [← e1]
    exact commute_toLinU (hcomm1 _ ⟨s, hs, rfl⟩)
  obtain ⟨c', hc'⟩ := (commute_specialBlock_iff_scalar H (by norm_num : 2 ≤ 2 ^ 3)
    ⟨X - C d, hmem⟩ hgood hY).1 hblock
  obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective c'
  refine ⟨r.eval d, fun v hv => ?_⟩
  have hvmem : v ∈ primaryComponent ((t6psub_toLin A :
      LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) : Module.End K0 (Fin 6 → K0)) (X - C d) :=
    mem_primaryComponent_X_sub_C.mpr hv
  have h1 := hc' ⟨v, hvmem⟩
  rw [coe_mk_smul_primaryComponent] at h1
  by_cases hv0 : v = 0
  · simp [hv0]
  have heig : Module.End.HasEigenvector ((t6psub_toLin A :
      LinearMap.GeneralLinearGroup K0 (Fin 6 → K0)) : Module.End K0 (Fin 6 → K0)) d v :=
    ⟨Module.End.mem_eigenspace_iff.mpr hv, hv0⟩
  have h2 := Module.End.aeval_apply_of_hasEigenvector heig (p := r)
  rw [← toLinU_apply_eq]
  exact h1.trans h2

end BlockFix

section ModelChange

open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.U
  OuterFourInAux CFSG.Open.StatedSUFieldChange

variable {K0 : Type} [Field K0]

theorem coe_glEntry' {n : ℕ} (σ : K0 ≃+* K0) (g : GL (Fin n) K0) :
    ((glEntry σ g : GL (Fin n) K0) : Matrix (Fin n) (Fin n) K0) =
      (g : Matrix (Fin n) (Fin n) K0).map σ := by
  simp [glEntry, RingHom.mapMatrix_apply]

theorem exists_conj_uFieldAut {S : Type} [Group S] {φ : MulAut S} (hφ : FieldAutU 6 S φ)
    (h : UnitaryFieldData 2 3 K0) (e : S ≃* StatedProj (StatedSU 6 (2 ^ 3) K0)) :
    ∃ (σ : K0 ≃+* K0) (δ : MulAut (StatedProj (StatedSU 6 (2 ^ 3) K0))), σ ≠ 1 ∧
      δ * MulAut.congr e φ * δ⁻¹ = uFieldAut h (by norm_num) σ := by
  classical
  obtain ⟨K', fK', hfin', e', σ', γ', hcard', hσ'1, -, hent⟩ := hφ
  haveI := h.finite
  haveI : Fintype K' := Fintype.ofFinite K'
  haveI : Fintype K0 := Fintype.ofFinite K0
  have hKK : Fintype.card K' = Fintype.card K0 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard', h.card_eq_sq]
  let eK : K' ≃+* K0 := FiniteField.ringEquivOfCardEq hKK
  let ιS := statedProjSUEquiv eK 6 (2 ^ 3)
  let σ : K0 ≃+* K0 := eK.symm.trans (σ'.trans eK)
  have hσ : ∀ x, σ (eK x) = eK (σ' x) := fun x => by simp [σ]
  let ϖ : MulAut (StatedProj (StatedSU 6 (2 ^ 3) K0)) := e.symm.trans (e'.trans ιS)
  have hA : MulAut.congr ιS (MulAut.congr e' φ) = ϖ * MulAut.congr e φ * ϖ⁻¹ := by
    refine MulEquiv.ext fun z => ?_
    simp [ϖ, MulAut.congr_apply, MulAut.mul_apply]
  have hB : IsEntrywiseProj (StatedSU 6 (2 ^ 3) K0) σ
      (MulAut.congr ιS (γ' * MulAut.congr e' φ * γ'⁻¹)) := by
    intro g
    obtain ⟨g₀, rfl⟩ := (statedSUEquiv eK 6 (2 ^ 3)).surjective g
    obtain ⟨g₀', hg₀', hψ⟩ := hent g₀
    refine ⟨statedSUEquiv eK 6 (2 ^ 3) g₀', ?_, ?_⟩
    · rw [statedSUEquiv_coe, statedSUEquiv_coe, hg₀']
      apply Units.ext
      rw [glEquiv_coe, coe_glEntry', coe_glEntry', glEquiv_coe]
      ext i j
      simp [Matrix.map_apply, hσ]
    · have hmk : ιS (QuotientGroup.mk g₀) = QuotientGroup.mk (statedSUEquiv eK 6 (2 ^ 3) g₀) :=
        QuotientGroup.congr_mk _ _ _ _ g₀
      have hmk' : ιS (QuotientGroup.mk g₀') = QuotientGroup.mk (statedSUEquiv eK 6 (2 ^ 3) g₀') :=
        QuotientGroup.congr_mk _ _ _ _ g₀'
      rw [← hmk, ← hmk']
      show ιS ((γ' * MulAut.congr e' φ * γ'⁻¹) (ιS.symm (ιS (QuotientGroup.mk g₀)))) =
        ιS (QuotientGroup.mk g₀')
      rw [MulEquiv.symm_apply_apply, hψ]
  have hC : MulAut.congr ιS (γ' * MulAut.congr e' φ * γ'⁻¹) = uFieldAut h (by norm_num) σ :=
    U6Bridge.isEntrywiseProj_unique _ σ hB (U6Bridge.isEntrywiseProj_uFieldAut h (by norm_num) σ)
  refine ⟨σ, MulAut.congr ιS γ' * ϖ, ?_, ?_⟩
  · intro hσ1
    apply hσ'1
    refine RingEquiv.ext fun x => ?_
    have := hσ x
    rw [hσ1] at this
    exact eK.injective this.symm
  · rw [← hC, map_mul, map_mul, map_inv, hA]
    group

end ModelChange

section Heis

open Matrix

variable {K0 : Type} [Field K0]

theorem scalar_mulVec (c : K0ˣ) (v : Fin 6 → K0) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 6) c : GL (Fin 6) K0) :
      Matrix (Fin 6) (Fin 6) K0) *ᵥ v = (c : K0) • v := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

theorem mul_mulVec (a b : GL (Fin 6) K0) (v : Fin 6 → K0) :
    ((a * b : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) *ᵥ v =
      (a : Matrix (Fin 6) (Fin 6) K0) *ᵥ ((b : Matrix (Fin 6) (Fin 6) K0) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem three_dvd_of_heis_scalar {κ : K0ˣ} (hκ3 : κ ^ 3 = 1) (hκ1 : κ ≠ 1)
    {g₁ g₂ A : GL (Fin 6) K0}
    (hcomm : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) κ)
    (h₁A : g₁ * A = A * g₁) (h₂A : g₂ * A = A * g₂) {d : K0} {v : Fin 6 → K0} (hv0 : v ≠ 0)
    (hv : (A : Matrix (Fin 6) (Fin 6) K0) *ᵥ v = d • v) (j k : ℤ) (c : K0)
    (hG : ∀ w : Fin 6 → K0, (A : Matrix (Fin 6) (Fin 6) K0) *ᵥ w = d • w →
      ((g₁ ^ j * g₂ ^ k : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) *ᵥ w = c • w) :
    (3 : ℤ) ∣ j ∧ (3 : ℤ) ∣ k := by
  set ks : GL (Fin 6) K0 := Matrix.GeneralLinearGroup.scalar (Fin 6) κ with hks
  have hk1 : ∀ x : GL (Fin 6) K0, Commute ks x := fun x => (commute_scalar κ x).symm
  have ha : g₁ * g₂ * g₁⁻¹ = ks * g₂ := by
    have := congrArg (· * g₂) hcomm
    simpa [mul_assoc] using this
  have hg12 : g₁ * g₂ = ks * g₂ * g₁ := by
    rw [← ha]; group
  have hb : g₂ * g₁ * g₂⁻¹ = ks⁻¹ * g₁ := by
    have h1 : g₂ * g₁ = ks⁻¹ * (g₁ * g₂) := by rw [hg12]; group
    rw [h1]; group
  set G : GL (Fin 6) K0 := g₁ ^ j * g₂ ^ k with hGdef
  have hR1 : g₁ * G * g₁⁻¹ = ks ^ k * G := by
    have e2 : g₁ * g₂ ^ k * g₁⁻¹ = (g₁ * g₂ * g₁⁻¹) ^ k := by
      have := map_zpow (MulAut.conj g₁) g₂ k
      simpa [MulAut.conj_apply] using this
    calc g₁ * G * g₁⁻¹ = (g₁ * g₁ ^ j) * g₂ ^ k * g₁⁻¹ := by rw [hGdef]; group
      _ = (g₁ ^ j * g₁) * g₂ ^ k * g₁⁻¹ := by rw [(Commute.self_zpow g₁ j).eq]
      _ = g₁ ^ j * (g₁ * g₂ ^ k * g₁⁻¹) := by group
      _ = g₁ ^ j * ((ks * g₂) ^ k) := by rw [e2, ha]
      _ = g₁ ^ j * (ks ^ k * g₂ ^ k) := by rw [(hk1 g₂).mul_zpow k]
      _ = ks ^ k * G := by
        have hc : Commute (ks ^ k) (g₁ ^ j) := (hk1 (g₁ ^ j)).zpow_left k
        rw [hGdef, ← mul_assoc, ← mul_assoc, ← hc.eq]
  have hR2 : g₂ * G * g₂⁻¹ = (ks⁻¹) ^ j * G := by
    have e2 : g₂ * g₁ ^ j * g₂⁻¹ = (g₂ * g₁ * g₂⁻¹) ^ j := by
      have := map_zpow (MulAut.conj g₂) g₁ j
      simpa [MulAut.conj_apply] using this
    have hc : Commute ((ks⁻¹) ^ j) g₁ := ((hk1 g₁).inv_left).zpow_left j
    calc g₂ * G * g₂⁻¹ = (g₂ * g₁ ^ j * g₂⁻¹) * (g₂ * g₂ ^ k * g₂⁻¹) := by rw [hGdef]; group
      _ = (g₂ * g₁ ^ j * g₂⁻¹) * g₂ ^ k := by
        congr 1
        rw [(Commute.self_zpow g₂ k).eq]; group
      _ = ((ks⁻¹ * g₁) ^ j) * g₂ ^ k := by rw [e2, hb]
      _ = (ks⁻¹) ^ j * G := by rw [(hk1 g₁).inv_left.mul_zpow j, hGdef, mul_assoc]
  have hGinv : ∀ w : Fin 6 → K0, ((G : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) *ᵥ w = 0 →
      w = 0 := by
    intro w hw
    have := congrArg (fun z => ((G⁻¹ : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) *ᵥ z) hw
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this
  have hc0 : c ≠ 0 := by
    intro hc
    have := hG v hv
    rw [hc, zero_smul] at this
    exact hv0 (hGinv v this)
  have hcvne : c • v ≠ 0 := fun h0 => hv0 ((smul_eq_zero.1 h0).resolve_left hc0)
  have key : ∀ (g : GL (Fin 6) K0) (e : K0ˣ), g * A = A * g →
      g * G * g⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) e * G → e = 1 := by
    intro g e hgA hgG
    have hgA' : A * g⁻¹ = g⁻¹ * A := by
      have := congrArg (fun z => g⁻¹ * z * g⁻¹) hgA
      simpa [mul_assoc] using this
    have hu : (A : Matrix (Fin 6) (Fin 6) K0) *ᵥ
        (((g⁻¹ : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) *ᵥ v) =
        d • (((g⁻¹ : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) *ᵥ v) := by
      rw [← mul_mulVec (A : GL (Fin 6) K0) (g⁻¹) v, hgA', mul_mulVec, hv, Matrix.mulVec_smul]
    have h1 := hG _ hu
    have h2 : ((g * G * g⁻¹ : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) *ᵥ v = c • v := by
      rw [mul_mulVec, mul_mulVec, h1, Matrix.mulVec_smul, ← mul_mulVec, mul_inv_cancel]
      simp
    have h3 : ((Matrix.GeneralLinearGroup.scalar (Fin 6) e * G : GL (Fin 6) K0) :
        Matrix (Fin 6) (Fin 6) K0) *ᵥ v = (e : K0) • (c • v) := by
      rw [mul_mulVec, hG v hv, scalar_mulVec]
    rw [hgG, h3] at h2
    have h4 : ((e : K0) - 1) • (c • v) = 0 := by rw [sub_smul, h2, one_smul, sub_self]
    have h5 := (smul_eq_zero.1 h4).resolve_right hcvne
    exact Units.ext (sub_eq_zero.1 h5)
  have hk : κ ^ k = 1 := by
    refine key g₁ (κ ^ k) h₁A ?_
    rw [hR1, hks, map_zpow]
  have hj : (κ⁻¹) ^ j = 1 := by
    refine key g₂ ((κ⁻¹) ^ j) h₂A ?_
    rw [hR2, hks, map_zpow, map_inv]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf κ = 3 := orderOf_eq_prime hκ3 hκ1
  have hj' : κ ^ j = 1 := by
    rw [_root_.inv_zpow, inv_eq_one] at hj
    exact hj
  refine ⟨?_, ?_⟩
  · have := (orderOf_dvd_iff_zpow_eq_one (G := K0ˣ)).2 hj'
    rwa [hord] at this
  · have := (orderOf_dvd_iff_zpow_eq_one (G := K0ˣ)).2 hk
    rwa [hord] at this

end Heis

section Rank

variable {X : Type} [Group X]

theorem autImageRankThree_of_card_ge [Finite X] {B J : Subgroup X}
    (hBel : CFSG.Open.IsElemAbelian 3 B) (h27 : 27 ≤ Nat.card (autImage B J)) :
    KSF4SU3.AutImageRankThree B J := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAel : CFSG.Open.IsElemAbelian 3 (autImage B J) := by
    have h1 : CFSG.Open.IsElemAbelian 3 (B ⊓ Subgroup.normalizer (J : Set X)) :=
      CFSG.Open.IsElemAbelian.mono hBel inf_le_left
    exact (h1.subgroupOf (Subgroup.normalizer (J : Set X))).map (actHom J)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hAel.isPGroup
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h27' : 3 ^ 3 ∣ Nat.card ↥(autImage B J) := by
    rw [hn]
    exact pow_dvd_pow 3 hn3
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(autImage B J)) 3 h27'
  refine ⟨K₀.map (autImage B J).subtype, Subgroup.map_subtype_le _,
    hAel.mono (Subgroup.map_subtype_le _), ?_⟩
  rw [Subgroup.card_map_of_injective (autImage B J).subtype_injective, hK₀]
  norm_num

end Rank

section Fix

variable {X : Type} [Group X]

theorem congr_actHom_fixes_image {K J : Subgroup X} (hJK : J ≤ K) {w : X}
    (hwN : w ∈ Subgroup.normalizer (K : Set X)) (hwC : w ∈ Subgroup.centralizer (J : Set X))
    {G : Type} [Group G] (ε : (↥K ⧸ Subgroup.center ↥K) ≃* G) :
    ∀ t ∈ ((J.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))).map
      (ε : (↥K ⧸ Subgroup.center ↥K) →* G), MulAut.congr ε (actHom K ⟨w, hwN⟩) t = t := by
  rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
  have hjw : (j : X) * w = w * (j : X) :=
    Subgroup.mem_centralizer_iff.1 hwC (j : X) (Subgroup.mem_subgroupOf.1 hj)
  have e1 : K.normalizerMonoidHom ⟨w, hwN⟩ j = j := by
    apply Subtype.ext
    rw [coe_normalizerMonoidHom]
    calc w * (j : X) * w⁻¹ = (j : X) * w * w⁻¹ := by rw [← hjw]
      _ = (j : X) := by group
  show ε ((actHom K ⟨w, hwN⟩) (ε.symm (ε (QuotientGroup.mk j)))) = ε (QuotientGroup.mk j)
  rw [MulEquiv.symm_apply_apply, actHom_mk, e1]

end Fix

section Factor

variable {K0 : Type} [Field K0]

@[expose] noncomputable def fieldFactor (h : UnitaryFieldData 2 3 K0) :
    MulAut (primeFormP h (idGram K0 6)) →* (K0 ≃+* K0) :=
  primeFormFieldFactor h (isPrimeFormGram_idGram (K := K0) (n := 6)) (by norm_num) (by norm_num)

theorem fieldFactor_conj (h : UnitaryFieldData 2 3 K0) (A : primeFormUnitary h (idGram K0 6)) :
    fieldFactor h (primeFormConjHom h (idGram K0 6) A) = 1 := by
  have := primeFormFieldFactor_apply h (isPrimeFormGram_idGram (K := K0) (n := 6))
    (by norm_num) (by norm_num) A 1
  rwa [map_one, mul_one] at this

theorem fieldFactor_field (h : UnitaryFieldData 2 3 K0) (σ : K0 ≃+* K0) :
    fieldFactor h (primeFormFieldHom h (isPrimeFormGram_idGram (K := K0) (n := 6)) σ) = σ := by
  have := primeFormFieldFactor_apply h (isPrimeFormGram_idGram (K := K0) (n := 6))
    (by norm_num) (by norm_num) 1 σ
  rwa [map_one, one_mul] at this

theorem fieldFactor_eq_of_conj (h : UnitaryFieldData 2 3 K0)
    {ψ δ : MulAut (primeFormP h (idGram K0 6))} {σ : K0 ≃+* K0}
    (hδ : δ * ψ * δ⁻¹ = primeFormFieldHom h (isPrimeFormGram_idGram (K := K0) (n := 6)) σ) :
    fieldFactor h ψ = σ := by
  have h1 := congrArg (fieldFactor h) hδ
  rw [map_mul, map_mul, map_inv, fieldFactor_field] at h1
  rw [← h1]
  have hc : Commute (fieldFactor h δ) (fieldFactor h ψ) := ringAut_commute h _ _
  rw [hc.eq]
  group

end Factor

section Key

variable {K0 : Type} [Field K0] {X : Type} [Group X]

theorem key_lemma {K J B : Subgroup X} (hJK : J ≤ K) (hperf : ⁅J, J⁆ = J)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hBel : CFSG.Open.IsElemAbelian 3 B)
    {x b₁ b₂ : X} (hx : x ∈ B) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (h : UnitaryFieldData 2 3 K0)
    (ε : (↥K ⧸ Subgroup.center ↥K) ≃* primeFormP h (idGram K0 6))
    (A : primeFormUnitary h (idGram K0 6)) (hA3 : (A : GL (Fin 6) K0) ^ 3 = 1) {d : K0}
    (hd : 3 ≤ eigMult (A : GL (Fin 6) K0) d)
    (hL : ((J.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))).map
      (ε : (↥K ⧸ Subgroup.center ↥K) →* primeFormP h (idGram K0 6)) = U6Comps.blockImage h A d)
    {σ : K0 ≃+* K0} (hσ1 : σ ≠ 1) (hσ3 : σ ^ 3 = 1)
    (hψx : fieldFactor h (MulAut.congr ε (actHom K ⟨x, hBN hx⟩)) = σ)
    {M₁ M₂ : primeFormUnitary h (idGram K0 6)}
    (hM₁ : MulAut.congr ε (actHom K ⟨b₁, hBN hb₁⟩) = primeFormConjHom h (idGram K0 6) M₁)
    (hM₂ : MulAut.congr ε (actHom K ⟨b₂, hBN hb₂⟩) = primeFormConjHom h (idGram K0 6) M₂)
    (hM₁A : M₁ * A = A * M₁) (hM₂A : M₂ * A = A * M₂) {κ : K0ˣ} (hκ3 : κ ^ 3 = 1) (hκ1 : κ ≠ 1)
    (hcomm : (M₁ : GL (Fin 6) K0) * M₂ * (M₁ : GL (Fin 6) K0)⁻¹ * (M₂ : GL (Fin 6) K0)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) κ)
    (i j k : ℤ) (hwJ : x ^ i * b₁ ^ j * b₂ ^ k ∈ Subgroup.normalizer (J : Set X))
    (hw : actHom J ⟨x ^ i * b₁ ^ j * b₂ ^ k, hwJ⟩ = 1) :
    (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j ∧ (3 : ℤ) ∣ k := by
  have hwB : x ^ i * b₁ ^ j * b₂ ^ k ∈ B :=
    B.mul_mem (B.mul_mem (B.zpow_mem hx i) (B.zpow_mem hb₁ j)) (B.zpow_mem hb₂ k)
  have hwN := hBN hwB
  have hwC : x ^ i * b₁ ^ j * b₂ ^ k ∈ Subgroup.centralizer (J : Set X) :=
    KSF4SU3.mem_centralizer_of_actHom_eq_one hperf hwJ hw
  have hfixL := congr_actHom_fixes_image hJK hwN hwC ε
  rw [hL] at hfixL
  have hψw : MulAut.congr ε (actHom K ⟨x ^ i * b₁ ^ j * b₂ ^ k, hwN⟩) =
      MulAut.congr ε (actHom K ⟨x, hBN hx⟩) ^ i * MulAut.congr ε (actHom K ⟨b₁, hBN hb₁⟩) ^ j *
        MulAut.congr ε (actHom K ⟨b₂, hBN hb₂⟩) ^ k := by
    have : (⟨x ^ i * b₁ ^ j * b₂ ^ k, hwN⟩ : ↥(Subgroup.normalizer (K : Set X))) =
        ⟨x, hBN hx⟩ ^ i * ⟨b₁, hBN hb₁⟩ ^ j * ⟨b₂, hBN hb₂⟩ ^ k := rfl
    rw [this]
    simp only [map_mul, map_zpow]
  have hF1 := fieldFactor_eq_one_of_fixes_block h A hA3 hd _ hfixL
  have hσi : σ ^ i = 1 := by
    have h2 := hF1
    change fieldFactor h _ = 1 at h2
    rw [hψw] at h2
    simp only [map_mul, map_zpow, hψx, hM₁, hM₂, fieldFactor_conj, _root_.one_zpow, mul_one] at h2
    exact h2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have h3i : (3 : ℤ) ∣ i := by
    have := (orderOf_dvd_iff_zpow_eq_one (G := K0 ≃+* K0)).2 hσi
    rwa [hord] at this
  refine ⟨h3i, ?_⟩
  have hxi : x ^ i = 1 := by
    obtain ⟨m, rfl⟩ := h3i
    have hx3 : x ^ (3 : ℤ) = 1 := by
      have := hBel.2 x hx
      rw [zpow_ofNat]
      exact this
    rw [_root_.zpow_mul, hx3, _root_.one_zpow]
  have hψxi : MulAut.congr ε (actHom K ⟨x, hBN hx⟩) ^ i = 1 := by
    rw [← map_zpow, ← map_zpow]
    have : (⟨x, hBN hx⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ i = 1 := Subtype.ext hxi
    rw [this, map_one, map_one]
  set M : primeFormUnitary h (idGram K0 6) := M₁ ^ j * M₂ ^ k with hMdef
  have hψM : MulAut.congr ε (actHom K ⟨x ^ i * b₁ ^ j * b₂ ^ k, hwN⟩) =
      primeFormConjHom h (idGram K0 6) M := by
    rw [hψw, hψxi, one_mul, hM₁, hM₂, hMdef]
    simp only [map_mul, map_zpow]
  have hfixM : ∀ t ∈ U6Comps.blockImage h A d, primeFormConjHom h (idGram K0 6) M t = t := by
    intro t ht
    rw [← hψM]
    exact hfixL t ht
  have hMA : M * A = A * M :=
    ((Commute.zpow_left (show Commute M₁ A from hM₁A) j).mul_left
      (Commute.zpow_left (show Commute M₂ A from hM₂A) k)).eq
  obtain ⟨c, hc⟩ := scalar_of_conj_fixes_block h A hA3 (by omega) M hMA hfixM
  have hpos : 0 < Module.finrank K0
      (primaryComponent (U6Comps.xlin h A) (Polynomial.X - Polynomial.C d)) := by
    rw [← U6Comps.eigMult_eq_finrank]
    omega
  obtain ⟨⟨v, hvmem⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hv : U6Comps.xlin h A v = d • v := mem_primaryComponent_X_sub_C.1 hvmem
  have hcoe : ((M : GL (Fin 6) K0) : GL (Fin 6) K0) =
      (M₁ : GL (Fin 6) K0) ^ j * (M₂ : GL (Fin 6) K0) ^ k := by
    rw [hMdef, Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow]
  have hcomm_GL : ∀ N : primeFormUnitary h (idGram K0 6), N * A = A * N →
      (N : GL (Fin 6) K0) * (A : GL (Fin 6) K0) = (A : GL (Fin 6) K0) * (N : GL (Fin 6) K0) :=
    fun N hN => by simpa using congrArg (fun z : primeFormUnitary h (idGram K0 6) =>
      (z : GL (Fin 6) K0)) hN
  have := three_dvd_of_heis_scalar hκ3 hκ1 hcomm (hcomm_GL M₁ hM₁A) (hcomm_GL M₂ hM₂A)
    (d := d) (v := v) (fun h0 => hv0 (Subtype.ext h0)) hv j k c (fun w hw => by
      rw [← hcoe]
      exact hc w hw)
  exact this

end Key

section Scalars

variable {K0 : Type} [Field K0]

theorem cube_eq_one_of_scalar_mem (h : UnitaryFieldData 2 3 K0) {s : GL (Fin 6) K0}
    (hs : s ∈ gramSU h (idGram K0 6)) {μ : K0ˣ}
    (hμ : s = Matrix.GeneralLinearGroup.scalar (Fin 6) μ) : μ ^ 3 = 1 := by
  have hn1 : 1 ≤ 6 := by norm_num
  have hcU : Matrix.GeneralLinearGroup.scalar (Fin 6) μ ∈
      primeFormUnitary h ((1 : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) := by
    rw [← hμ]; exact hs.1
  have hN : h.norm (μ : K0) = 1 := norm_eq_one_of_scalar_mem_primeFormUnitary h hn1 1 hcU
  have h9 : (μ : K0) ^ 9 = 1 := by
    have := h.norm_eq_pow (μ : K0)
    rw [hN] at this
    norm_num at this
    exact this.symm
  have h6 : (μ : K0) ^ 6 = 1 := by
    have e1 : ((Matrix.GeneralLinearGroup.scalar (Fin 6) μ : GL (Fin 6) K0) :
        Matrix (Fin 6) (Fin 6) K0).det = (μ : K0) ^ 6 := by
      simp [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const]
    have e2 : ((s : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0).det = 1 := hs.2
    rw [hμ] at e2
    rw [← e1]
    exact e2
  have h3 : (μ : K0) ^ 3 = 1 := by
    have : (μ : K0) ^ 3 * (μ : K0) ^ 6 = (μ : K0) ^ 6 := by
      rw [← pow_add]; simpa using h9.trans h6.symm
    have h6' : (μ : K0) ^ 6 ≠ 0 := pow_ne_zero 6 μ.ne_zero
    exact mul_right_cancel₀ h6' (this.trans (by rw [one_mul]))
  exact Units.ext (by simpa using h3)

theorem commute_of_scalar_mul {g A : GL (Fin 6) K0} (ν : K0ˣ)
    (hg : g * (Matrix.GeneralLinearGroup.scalar (Fin 6) ν * A) =
      (Matrix.GeneralLinearGroup.scalar (Fin 6) ν * A) * g) : g * A = A * g := by
  have hc := commute_scalar ν g
  have h1 : Matrix.GeneralLinearGroup.scalar (Fin 6) ν * (g * A) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) ν * (A * g) := by
    calc Matrix.GeneralLinearGroup.scalar (Fin 6) ν * (g * A)
        = (Matrix.GeneralLinearGroup.scalar (Fin 6) ν * g) * A := by rw [mul_assoc]
      _ = (g * Matrix.GeneralLinearGroup.scalar (Fin 6) ν) * A := by rw [hc.eq.symm]
      _ = g * (Matrix.GeneralLinearGroup.scalar (Fin 6) ν * A) := by rw [mul_assoc]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 6) ν * A) * g := hg
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) ν * (A * g) := by rw [mul_assoc]
  exact mul_left_cancel h1

end Scalars

end U6Heis

section Main

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Dickson.I271 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.U
  CFSG.RankThree.PartOne.KCUnitaryModel OuterFourInAux U6Heis
open scoped commutatorElement

variable {K0 : Type} [Field K0]

theorem u6_heis_rank_three [Fintype K0] {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hBel : CFSG.Open.IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (h : UnitaryFieldData 2 3 K0)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* StatedProj (StatedSU 6 (2 ^ 3) K0)) {x y b₁ b₂ : X}
    (hx : x ∈ B) (hFx : FieldAutU 6 (↥K ⧸ Subgroup.center ↥K) (actHom K ⟨x, hBN hx⟩))
    {g₁ g₂ g₃ : StatedSU 6 (2 ^ 3) K0} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hy : y ∈ B)
    (h₁ : ActsAs K e b₁ g₁) (h₂ : ActsAs K e b₂ g₂) (h₃ : ActsAs K e y g₃)
    (hH : HeisData (g₁ : GL (Fin 6) K0) g₂ g₃) {J : Subgroup X}
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J)
    (hBJ : B ≤ Subgroup.normalizer (J : Set X)) :
    KSF4SU3.AutImageRankThree B J := by
  classical
  have hJK : J ≤ K := fun z hz => (Subgroup.mem_inf.1 (hJ.1 hz)).1
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hy3 : y ^ 3 = 1 := hBel.2 y hy
  set ε := e.trans (uTransport h (by norm_num : 1 ≤ 6)) with hεdef
  obtain ⟨hyN, A, ν, hA3, hgA, hεy⟩ := U6Comps.exists_model_of_actsAs h e h₃ hy3
  obtain ⟨hb₁N, hψ₁⟩ := U6Comps.congr_actHom_eq h e h₁
  obtain ⟨hb₂N, hψ₂⟩ := U6Comps.congr_actHom_eq h e h₂
  obtain ⟨⟨κ, hκ1, hκcomm⟩, hg13, hg23, hdivg⟩ := hH
  have hdivA : ∀ d : K0, 3 ∣ eigMult (A : GL (Fin 6) K0) d := by
    intro d
    have := hdivg (ν * d)
    rw [hgA, U6Comps.eigMult_scalar_mul, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_mul] at this
    exact this
  have hlayerA := LieSemisimple.perfectInLayer_primeFormP h (by norm_num) (by norm_num)
    Nat.prime_three (by norm_num) (by norm_num) (primeFormConjHom h (idGram K0 6) A)
    (U6Comps.conj_pow_three h A hA3)
  have hlayer : PerfectInLayer (actHom K ⟨y, hyN⟩) :=
    LieSemisimple.perfectInLayer_of_congr ε _ (by rw [hεy]; exact hlayerA)
  have hc := U6Comps.isComponentOf_image hyN hlayer hJ
  have hL : CFSG.Open.IsComponentOf
      (((J.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))).map
        (ε : (↥K ⧸ Subgroup.center ↥K) →* primeFormP h (idGram K0 6)))
      (fixSubgroup (primeFormConjHom h (idGram K0 6) A)) := by
    rw [← hεy, CFSG.HardMathSupport.Dickson.Bal207.fixSubgroup_mulAutCongr]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map ε hc
  obtain ⟨d, hd2, hLd⟩ := U6Comps.comp_eq_blockImage h A hA3 hL
  have hd3 : 3 ≤ eigMult (A : GL (Fin 6) K0) d := by
    have := hdivA d
    omega
  obtain ⟨σ, δ, hσ1, hδ⟩ := exists_conj_uFieldAut hFx h e
  have hψx : fieldFactor h (MulAut.congr ε (actHom K ⟨x, hBN hx⟩)) = σ := by
    refine fieldFactor_eq_of_conj h
      (δ := MulAut.congr (uTransport h (by norm_num : 1 ≤ 6)) δ) ?_
    have h1 := congrArg (MulAut.congr (uTransport h (by norm_num : 1 ≤ 6))) hδ
    rw [map_mul, map_mul, map_inv] at h1
    have h2 : MulAut.congr (uTransport h (by norm_num : 1 ≤ 6)) (uFieldAut h (by norm_num) σ) =
        primeFormFieldHom h (isPrimeFormGram_idGram (K := K0) (n := 6)) σ :=
      MulEquiv.apply_symm_apply (MulAut.congr (uTransport h (by norm_num : 1 ≤ 6))) _
    have h3 : MulAut.congr ε (actHom K ⟨x, hBN hx⟩) =
        MulAut.congr (uTransport h (by norm_num : 1 ≤ 6))
          (MulAut.congr e (actHom K ⟨x, hBN hx⟩)) := MulEquiv.ext fun _ => rfl
    rw [h3, ← h2]
    exact h1
  have hσ3 : σ ^ 3 = 1 := by
    have hx3 : (actHom K ⟨x, hBN hx⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hBN hx⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 :=
        Subtype.ext (hBel.2 x hx)
      rw [this, map_one]
    rw [← hψx, ← map_pow, ← map_pow, hx3, map_one, map_one]
  have hg1G : (g₁ : GL (Fin 6) K0) ∈ gramSU h (idGram K0 6) := by
    rw [← statedSU_eq_gramSU h]; exact g₁.2
  have hg2G : (g₂ : GL (Fin 6) K0) ∈ gramSU h (idGram K0 6) := by
    rw [← statedSU_eq_gramSU h]; exact g₂.2
  have hκ3 : κ ^ 3 = 1 :=
    cube_eq_one_of_scalar_mem h
      (mul_mem (mul_mem (mul_mem hg1G hg2G) (inv_mem hg1G)) (inv_mem hg2G)) hκcomm
  have hM₁A : (⟨(g₁ : GL (Fin 6) K0), statedSU_le_uU h g₁.2⟩ : primeFormUnitary h (idGram K0 6)) *
      A = A * ⟨(g₁ : GL (Fin 6) K0), statedSU_le_uU h g₁.2⟩ := by
    rw [hgA] at hg13
    exact Subtype.ext (commute_of_scalar_mul ν hg13)
  have hM₂A : (⟨(g₂ : GL (Fin 6) K0), statedSU_le_uU h g₂.2⟩ : primeFormUnitary h (idGram K0 6)) *
      A = A * ⟨(g₂ : GL (Fin 6) K0), statedSU_le_uU h g₂.2⟩ := by
    rw [hgA] at hg23
    exact Subtype.ext (commute_of_scalar_mul ν hg23)
  have key : ∀ i j k : ℤ, ∀ hwJ : x ^ i * b₁ ^ j * b₂ ^ k ∈ Subgroup.normalizer (J : Set X),
      actHom J ⟨x ^ i * b₁ ^ j * b₂ ^ k, hwJ⟩ = 1 →
        (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j ∧ (3 : ℤ) ∣ k := fun i j k hwJ hw =>
    key_lemma hJK hperf hBN hBel hx hb₁ hb₂ h ε A hA3 hd3 hLd hσ1 hσ3 hψx hψ₁ hψ₂ hM₁A hM₂A
      hκ3 hκ1 hκcomm i j k hwJ hw
  haveI : IsMulCommutative ↥B := hBel.1
  let φ : ↥B →* MulAut (↥J ⧸ Subgroup.center ↥J) :=
    (actHom J).comp (Subgroup.inclusion hBJ)
  let wB : ℤ → ℤ → ℤ → ↥B := fun i j k => ⟨x, hx⟩ ^ i * ⟨b₁, hb₁⟩ ^ j * ⟨b₂, hb₂⟩ ^ k
  have hkey' : ∀ i j k : ℤ, φ (wB i j k) = 1 →
      (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j ∧ (3 : ℤ) ∣ k := by
    intro i j k hφ1
    have hcoe : ((wB i j k : ↥B) : X) = x ^ i * b₁ ^ j * b₂ ^ k := by
      simp [wB]
    have hwJ : x ^ i * b₁ ^ j * b₂ ^ k ∈ Subgroup.normalizer (J : Set X) :=
      hcoe ▸ hBJ (wB i j k).2
    refine key i j k hwJ ?_
    have : actHom J ⟨x ^ i * b₁ ^ j * b₂ ^ k, hwJ⟩ = φ (wB i j k) := by
      show _ = actHom J ⟨((wB i j k : ↥B) : X), hBJ (wB i j k).2⟩
      congr 1
    rw [this]
    exact hφ1
  open scoped IsMulCommutative in
  have hinj : Function.Injective
      (fun p : Fin 3 × Fin 3 × Fin 3 => φ (wB (p.1 : ℕ) (p.2.1 : ℕ) (p.2.2 : ℕ))) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ hp
    have hq : wB ((a : ℕ) - (a' : ℕ)) ((b : ℕ) - (b' : ℕ)) ((c : ℕ) - (c' : ℕ)) =
        wB (a : ℕ) (b : ℕ) (c : ℕ) * (wB (a' : ℕ) (b' : ℕ) (c' : ℕ))⁻¹ := by
      simp only [wB, zpow_sub, mul_inv]
      ac_rfl
    have h1 : φ (wB ((a : ℕ) - (a' : ℕ)) ((b : ℕ) - (b' : ℕ)) ((c : ℕ) - (c' : ℕ))) = 1 := by
      rw [hq, map_mul, map_inv]
      have hp' : φ (wB (a : ℕ) (b : ℕ) (c : ℕ)) = φ (wB (a' : ℕ) (b' : ℕ) (c' : ℕ)) := hp
      rw [hp', mul_inv_cancel]
    obtain ⟨h3a, h3b, h3c⟩ := hkey' _ _ _ h1
    have ha := a.2
    have ha' := a'.2
    have hb := b.2
    have hb' := b'.2
    have hc := c.2
    have hc' := c'.2
    have e1 : (a : ℕ) = a' := by omega
    have e2 : (b : ℕ) = b' := by omega
    have e3 : (c : ℕ) = c' := by omega
    rw [Fin.ext e1, Fin.ext e2, Fin.ext e3]
  have hrange : ∀ p : Fin 3 × Fin 3 × Fin 3,
      φ (wB (p.1 : ℕ) (p.2.1 : ℕ) (p.2.2 : ℕ)) ∈ autImage B J := fun p =>
    mem_autImage.2 ⟨((wB (p.1 : ℕ) (p.2.1 : ℕ) (p.2.2 : ℕ) : ↥B) : X),
      hBJ (wB (p.1 : ℕ) (p.2.1 : ℕ) (p.2.2 : ℕ)).2, (wB (p.1 : ℕ) (p.2.1 : ℕ) (p.2.2 : ℕ)).2, rfl⟩
  let f : Fin 3 × Fin 3 × Fin 3 → ↥(autImage B J) := fun p =>
    ⟨φ (wB (p.1 : ℕ) (p.2.1 : ℕ) (p.2.2 : ℕ)), hrange p⟩
  have hfinj : Function.Injective f := fun p q hpq => hinj (congrArg Subtype.val hpq)
  have h27 : 27 ≤ Nat.card ↥(autImage B J) := by
    have := Nat.card_le_card_of_injective f hfinj
    simpa [Nat.card_eq_fintype_card] using this
  exact autImageRankThree_of_card_ge hBel h27

end Main

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
