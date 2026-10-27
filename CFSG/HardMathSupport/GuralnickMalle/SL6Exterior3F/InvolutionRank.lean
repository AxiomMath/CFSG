module

public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3F
public import CFSG.HardMathSupport.GuralnickMalle.InvolutionRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bInvol

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module
open CFSG.Open
open CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.QuasithinUnique.Setup.X7 (permMat)
open CFSG.QuasithinUnique.Setup.X7b (rank_permMat_sub_one rank_conj_eq exists_perm_conj)

variable {K : Type} [Field K]

theorem natRank_eq_rank (a : GL (Fin 6) K) :
    natRank a = ((a : Matrix (Fin 6) (Fin 6) K) - 1).rank := by
  rw [natRank]
  have h : Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K) - 1) =
      Matrix.toLin' (a : Matrix (Fin 6) (Fin 6) K) - 1 := by
    rw [map_sub, Matrix.toLin'_one]
    rfl
  rw [← h]
  exact (Matrix.rank_eq_finrank_range_toLin ((a : Matrix (Fin 6) (Fin 6) K) - 1)
    (Pi.basisFun K (Fin 6)) (Pi.basisFun K (Fin 6))).symm

noncomputable def imageSubsetEquiv {n k : ℕ} (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Set.powersetCard (Fin n) k) where
  toFun := permImage τ
  invFun := permImage τ.symm
  left_inv I := by
    apply Subtype.ext
    change (I.val.image τ).image τ.symm = I.val
    simp [Finset.image_image]
  right_inv I := by
    apply Subtype.ext
    change (I.val.image τ.symm).image τ = I.val
    simp [Finset.image_image]

noncomputable def imageSubsetHom (n k : ℕ) :
    Equiv.Perm (Fin n) →* Equiv.Perm (Set.powersetCard (Fin n) k) where
  toFun := imageSubsetEquiv
  map_one' := by
    refine Equiv.ext (fun I => ?_)
    apply Subtype.ext
    simp [imageSubsetEquiv, permImage]
  map_mul' σ τ := by
    refine Equiv.ext (fun I => ?_)
    apply Subtype.ext
    simp [imageSubsetEquiv, permImage, Equiv.Perm.mul_apply, Finset.image_image]

theorem card_fixed_imageSubset_eq_filter (σ : Equiv.Perm (Fin 6)) :
    Fintype.card {s : Set.powersetCard (Fin 6) 3 // imageSubsetEquiv σ s = s} =
    ((Finset.powersetCard 3 (Finset.univ : Finset (Fin 6))).filter
      (fun s => s.image σ = s)).card := by
  classical
  let S := Finset.powersetCard 3 (Finset.univ : Finset (Fin 6))
  let efix : {s : Set.powersetCard (Fin 6) 3 // imageSubsetEquiv σ s = s} ≃
      {s : Finset (Fin 6) // s.card = 3 ∧ s.image σ = s} :=
    { toFun := fun t =>
        ⟨t.1.val, t.1.prop, by
          have h := congrArg Subtype.val t.2
          simpa [imageSubsetEquiv, permImage] using h⟩
      invFun := fun t =>
        ⟨⟨t.1, t.2.1⟩, by
          apply Subtype.ext
          simpa [imageSubsetEquiv, permImage] using t.2.2⟩
      left_inv := fun t => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun t => by apply Subtype.ext; rfl }
  calc Fintype.card {s : Set.powersetCard (Fin 6) 3 // imageSubsetEquiv σ s = s}
      = Fintype.card {s : Finset (Fin 6) // s.card = 3 ∧ s.image σ = s} :=
        Fintype.card_congr efix
    _ = (S.filter (fun s => s.image σ = s)).card := by
        apply Fintype.card_of_subtype
        intro s
        simp [S, Finset.mem_powersetCard]

theorem card_fixed_conj (g σ : Equiv.Perm (Fin 6)) :
    Fintype.card {x : Fin 6 // (g * σ * g⁻¹) x = x} =
    Fintype.card {x : Fin 6 // σ x = x} := by
  refine Fintype.card_congr (Equiv.subtypeEquiv g⁻¹ ?_)
  intro x
  rw [show (g * σ * g⁻¹) x = g (σ (g⁻¹ x)) by simp [Equiv.Perm.mul_apply],
    Equiv.apply_eq_iff_eq_symm_apply]
  simp

theorem card_fixed_imageSubset_conj (g σ : Equiv.Perm (Fin 6)) :
    Fintype.card {s : Set.powersetCard (Fin 6) 3 //
      imageSubsetEquiv (g * σ * g⁻¹) s = s} =
    Fintype.card {s : Set.powersetCard (Fin 6) 3 // imageSubsetEquiv σ s = s} := by
  have hmul : imageSubsetEquiv (k := 3) (g * σ * g⁻¹) =
      imageSubsetEquiv (k := 3) g * imageSubsetEquiv (k := 3) σ *
        (imageSubsetEquiv (k := 3) g)⁻¹ := by
    refine Equiv.ext (fun s => ?_)
    apply Subtype.ext
    change (s.val.image (g * σ * g⁻¹)) = ((s.val.image g.symm).image σ).image g
    simp [Finset.image_image, Function.comp_assoc]
  rw [hmul]
  refine Fintype.card_congr (Equiv.subtypeEquiv (imageSubsetEquiv (k := 3) g)⁻¹ ?_)
  intro s
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv]
  constructor
  · intro h
    have h' := congrArg (Equiv.symm (imageSubsetEquiv (k := 3) g)) h
    simpa using h'
  · intro h
    have h' := congrArg (imageSubsetEquiv (k := 3) g) h
    simpa using h'

theorem card_stable_subsets_le_two_mul_card_fixed (σ : Equiv.Perm (Fin 6))
    (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) :
    Fintype.card {s : Set.powersetCard (Fin 6) 3 // imageSubsetEquiv σ s = s} ≤
      2 * Fintype.card {x : Fin 6 // σ x = x} := by
  classical
  have hpow : σ ^ 2 = 1 := by rw [pow_two]; exact hσ
  set t : ℕ := σ.cycleType.card with ht
  have hcycle : σ.cycleType = Multiset.replicate t 2 := by
    rw [ht]
    simpa using (Equiv.Perm.cycleType_of_pow_prime_eq_one (σ := σ) (p := 2) hpow)
  have htpos : 0 < t := by
    rw [ht]
    exact (Equiv.Perm.card_cycleType_pos (σ := σ)).2 hσ1
  have hsum : σ.support.card = 2 * t := by
    rw [← Equiv.Perm.sum_cycleType, hcycle, Multiset.sum_replicate]
    simp [Nat.mul_comm]
  have ht3 : t ≤ 3 := by
    have hle : σ.support.card ≤ 6 := by simpa using Finset.card_le_univ σ.support
    omega
  interval_cases t
  · have hnorm : (Equiv.swap (0 : Fin 6) 1).cycleType = Multiset.replicate 1 2 := by
      rw [Multiset.replicate_one]
      exact Equiv.Perm.isSwap_iff_cycleType.mp
        (Equiv.Perm.swap_isSwap_iff.mpr (by decide : (0 : Fin 6) ≠ 1))
    have hconj : IsConj (Equiv.swap (0 : Fin 6) 1) σ :=
      Equiv.Perm.isConj_iff_cycleType_eq.2 (by rw [hcycle, hnorm])
    obtain ⟨g, hg⟩ := isConj_iff.1 hconj
    rw [← hg]
    rw [card_fixed_imageSubset_conj, card_fixed_conj, card_fixed_imageSubset_eq_filter]
    decide
  · have hnorm : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (2 : Fin 6) 3).cycleType =
        Multiset.replicate 2 2 := by
      have h := Equiv.Perm.cycleType_swap_mul_swap_of_nodup (α := Fin 6)
        (x := 0) (y := 1) (z := 2) (t := 3) (by decide)
      simpa using h
    have hconj : IsConj (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (2 : Fin 6) 3) σ :=
      Equiv.Perm.isConj_iff_cycleType_eq.2 (by rw [hcycle, hnorm])
    obtain ⟨g, hg⟩ := isConj_iff.1 hconj
    rw [← hg]
    rw [card_fixed_imageSubset_conj, card_fixed_conj, card_fixed_imageSubset_eq_filter]
    decide
  · have hnorm : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (2 : Fin 6) 3 *
        Equiv.swap (4 : Fin 6) 5).cycleType = Multiset.replicate 3 2 := by
      have hd : Equiv.Perm.Disjoint (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (2 : Fin 6) 3)
          (Equiv.swap (4 : Fin 6) 5) :=
        Equiv.Perm.Disjoint.mul_left
          (Equiv.Perm.disjoint_swap_swap (x := 0) (y := 1) (z := 4) (t := 5) (by decide))
          (Equiv.Perm.disjoint_swap_swap (x := 2) (y := 3) (z := 4) (t := 5) (by decide))
      rw [Equiv.Perm.Disjoint.cycleType_mul hd]
      rw [show (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (2 : Fin 6) 3).cycleType =
          Multiset.replicate 2 2 from by
        have h := Equiv.Perm.cycleType_swap_mul_swap_of_nodup (α := Fin 6)
          (x := 0) (y := 1) (z := 2) (t := 3) (by decide)
        simpa using h]
      rw [show (Equiv.swap (4 : Fin 6) 5).cycleType = Multiset.replicate 1 2 from by
        rw [Multiset.replicate_one]
        exact Equiv.Perm.isSwap_iff_cycleType.mp
          (Equiv.Perm.swap_isSwap_iff.mpr (by decide : (4 : Fin 6) ≠ 5))]
      rw [← Multiset.replicate_add]
    have hconj : IsConj (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (2 : Fin 6) 3 *
        Equiv.swap (4 : Fin 6) 5) σ :=
      Equiv.Perm.isConj_iff_cycleType_eq.2 (by rw [hcycle, hnorm])
    obtain ⟨g, hg⟩ := isConj_iff.1 hconj
    rw [← hg]
    rw [card_fixed_imageSubset_conj, card_fixed_conj, card_fixed_imageSubset_eq_filter]
    decide

theorem finrank_fixSubGen_closure_add_two_mul_natRank_le (K : Type) [Field K] [Finite K]
    [CharP K 2] (a : GL (Fin 6) K) (ha : a * a = 1) (ha1 : a ≠ 1) :
    Module.finrank K (fixSubGen (glExterior3Rep K) (Subgroup.closure {a})) + 2 * natRank a ≤ 16 := by
  classical
  let z : Matrix (Fin 6) (Fin 6) K := (a : Matrix (Fin 6) (Fin 6) K)
  have hz : z * z = 1 := by
    simpa [z] using congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) ha
  obtain ⟨σ, P, Q, hσ, hPQ, hQP, hzP⟩ := exists_perm_conj (k := K) (κ := Fin 6) hz
  have hz_eq : z = P * permMat K σ * Q := by
    calc z = z * 1 := (mul_one z).symm
      _ = z * (P * Q) := by rw [hPQ]
      _ = (z * P) * Q := by rw [mul_assoc]
      _ = (P * permMat K σ) * Q := by rw [hzP]
  have hperm_one : permMat K (1 : Equiv.Perm (Fin 6)) = 1 := by
    ext y x
    simp [CFSG.QuasithinUnique.Setup.X7.permMat, Matrix.one_apply, eq_comm]
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply ha1
    apply Units.ext
    show (a : Matrix (Fin 6) (Fin 6) K) = 1
    calc (a : Matrix (Fin 6) (Fin 6) K) = z := rfl
      _ = P * permMat K σ * Q := hz_eq
      _ = P * 1 * Q := by rw [h1, hperm_one]
      _ = 1 := by rw [Matrix.mul_one, hPQ]
  set F1 : ℕ := Fintype.card {i : Fin 6 // σ i = i} with hF1
  set F3 : ℕ := Fintype.card {s : Set.powersetCard (Fin 6) 3 //
    imageSubsetEquiv σ s = s} with hF3
  set r3 : ℕ := (permMat K (imageSubsetEquiv (k := 3) σ) - 1).rank with hr3
  have hσ₃ : imageSubsetEquiv (k := 3) σ * imageSubsetEquiv (k := 3) σ = 1 := by
    have h := map_mul (imageSubsetHom 6 3) σ σ
    rw [hσ, map_one] at h
    exact h.symm
  have hnat_eq : 2 * natRank a + F1 = 6 := by
    rw [hF1]
    have hnat : natRank a = (z - 1).rank := by
      rw [natRank_eq_rank]
    have hrank1 : (z - 1).rank = (permMat K σ - 1).rank := by
      have hQzP : Q * z * P = permMat K σ := by
        rw [Matrix.mul_assoc, hzP, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
      have hconj : Q * (z - 1) * P = permMat K σ - 1 := by
        have h1 : Q * (z - 1) * P = Q * z * P - Q * P := by
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
        rw [h1, hQzP, hQP]
      calc (z - 1).rank = (Q * (z - 1) * P).rank :=
            (rank_conj_eq (M := z - 1) (P := Q) (Q := P) hPQ).symm
        _ = (permMat K σ - 1).rank := by rw [hconj]
    have hfix : (permMat K σ - 1).rank * 2 +
        Fintype.card {i : Fin 6 // σ i = i} = 6 := by
      simpa using rank_permMat_sub_one (k := K) σ hσ
    rw [hnat, hrank1]
    omega
  have hF3rank : r3 * 2 + F3 = 20 := by
    rw [hr3, hF3]
    have h := rank_permMat_sub_one (k := K) (imageSubsetEquiv σ) hσ₃
    have hcard : Fintype.card (Set.powersetCard (Fin 6) 3) = 20 := by
      rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
      simp
      decide
    simpa [hcard] using h
  have hfinite : F3 ≤ 2 * F1 := by
    rw [hF3, hF1]
    exact card_stable_subsets_le_two_mul_card_fixed σ hσ hσ1
  let B : Basis (Set.powersetCard (Fin 6) 3) K (⋀[K]^3 (Fin 6 → K)) :=
    (Pi.basisFun K (Fin 6)).exteriorPower 3
  have hmat_minor : ∀ M : Matrix (Fin 6) (Fin 6) K,
      LinearMap.toMatrix B B (exteriorPower.map 3 (Matrix.toLin' M)) = minor M := by
    intro M
    ext s t
    rw [LinearMap.toMatrix_apply]
    exact repr_exteriorPower_map_eq_minor M s t
  let Mz : Matrix (Set.powersetCard (Fin 6) 3) (Set.powersetCard (Fin 6) 3) K := minor z
  have hmat_z : LinearMap.toMatrix B B ((glExterior3Rep K) a) = Mz := by
    rw [glExterior3Rep_apply, glNaturalRep_eq_toLin]
    simpa [Mz, z] using hmat_minor z
  have hmat_f : LinearMap.toMatrix B B ((glExterior3Rep K) a - 1) = Mz - 1 := by
    have hsub : LinearMap.toMatrix B B ((glExterior3Rep K) a - 1) =
        LinearMap.toMatrix B B ((glExterior3Rep K) a) -
          LinearMap.toMatrix B B (1 : Module.End K (⋀[K]^3 (Fin 6 → K))) :=
      map_sub (LinearMap.toMatrix B B) ((glExterior3Rep K) a) 1
    rw [hsub, hmat_z, LinearMap.toMatrix_one]
  have hperm_basis : ∀ i : Fin 6,
      Matrix.toLin' (permMat K σ) (Pi.basisFun K (Fin 6) i) =
        Pi.basisFun K (Fin 6) (σ i) := by
    intro i
    rw [Pi.basisFun_apply, Matrix.toLin'_apply]
    ext y
    simp [CFSG.QuasithinUnique.Setup.X7.permMat, Matrix.mulVec, dotProduct, Pi.single_apply,
      eq_comm]
  have hmat_perm : LinearMap.toMatrix B B
      (exteriorPower.map 3 (Matrix.toLin' (permMat K σ))) =
        permMat K (imageSubsetEquiv (k := 3) σ) := by
    ext s t
    rw [LinearMap.toMatrix_apply]
    change B.repr (exteriorPower.map 3 (Matrix.toLin' (permMat K σ)) (B t)) s =
      permMat K (imageSubsetEquiv (k := 3) σ) s t
    rw [exteriorPower_map_basis_perm (K := K) (b := Pi.basisFun K (Fin 6)) (Matrix.toLin' (permMat K σ)) σ hperm_basis t,
      Basis.repr_self]
    simp [CFSG.QuasithinUnique.Setup.X7.permMat, imageSubsetEquiv, permImage, eq_comm,
      Finsupp.single_apply]
  let eP : (Fin 6 → K) ≃ₗ[K] (Fin 6 → K) :=
    { toFun := Matrix.toLin' P
      invFun := Matrix.toLin' Q
      left_inv := fun v => by
        rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hQP, Matrix.toLin'_one]
        rfl
      right_inv := fun v => by
        rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hPQ, Matrix.toLin'_one]
        rfl
      map_add' := (Matrix.toLin' P).map_add
      map_smul' := (Matrix.toLin' P).map_smul }
  let e3P : (⋀[K]^3 (Fin 6 → K)) ≃ₗ[K] (⋀[K]^3 (Fin 6 → K)) :=
    { toFun := exteriorPower.map 3 eP.toLinearMap
      invFun := exteriorPower.map 3 eP.symm.toLinearMap
      left_inv := fun v => by
        rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, eP.symm_comp,
          exteriorPower.map_id]
        rfl
      right_inv := fun v => by
        rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, eP.comp_symm,
          exteriorPower.map_id]
        rfl
      map_add' := (exteriorPower.map 3 eP.toLinearMap).map_add
      map_smul' := (exteriorPower.map 3 eP.toLinearMap).map_smul }
  have hz_decomp : (glExterior3Rep K) a =
      e3P.conj (exteriorPower.map 3 (Matrix.toLin' (permMat K σ))) := by
    rw [glExterior3Rep_apply, glNaturalRep_eq_toLin]
    change exteriorPower.map 3 (Matrix.toLin' z) =
      e3P.conj (exteriorPower.map 3 (Matrix.toLin' (permMat K σ)))
    rw [hz_eq, Matrix.toLin'_mul, Matrix.toLin'_mul, exteriorPower.map_comp,
      exteriorPower.map_comp, LinearEquiv.conj_apply]
    rw [LinearMap.comp_assoc]
    rfl
  have hconj_rank : Module.finrank K (LinearMap.range ((glExterior3Rep K) a - 1)) =
      Module.finrank K (LinearMap.range
        (exteriorPower.map 3 (Matrix.toLin' (permMat K σ)) - 1)) := by
    rw [hz_decomp]
    exact finrank_range_sub_one_eq_of_intertwines e3P _ _
      (fun x => by simp [LinearEquiv.conj_apply_apply])
  have hmat_perm_f : LinearMap.toMatrix B B
      (exteriorPower.map 3 (Matrix.toLin' (permMat K σ)) - 1) =
        permMat K (imageSubsetEquiv (k := 3) σ) - 1 := by
    have hsub : LinearMap.toMatrix B B
        (exteriorPower.map 3 (Matrix.toLin' (permMat K σ)) - 1) =
        LinearMap.toMatrix B B (exteriorPower.map 3 (Matrix.toLin' (permMat K σ))) -
          LinearMap.toMatrix B B (1 : Module.End K (⋀[K]^3 (Fin 6 → K))) :=
      map_sub (LinearMap.toMatrix B B) _ 1
    rw [hsub, hmat_perm, LinearMap.toMatrix_one]
  have hrank_perm : Module.finrank K (LinearMap.range
      (exteriorPower.map 3 (Matrix.toLin' (permMat K σ)) - 1)) = r3 := by
    rw [hr3]
    have h := Matrix.rank_eq_finrank_range_toLin
      (LinearMap.toMatrix B B (exteriorPower.map 3 (Matrix.toLin' (permMat K σ)) - 1)) B B
    rw [Matrix.toLin_toMatrix] at h
    rw [← h, hmat_perm_f]
  have hrank_range : Module.finrank K (LinearMap.range ((glExterior3Rep K) a - 1)) = r3 := by
    rw [hconj_rank, hrank_perm]
  have hdimV : Module.finrank K (⋀[K]^3 (Fin 6 → K)) = 20 := by
    rw [exteriorPower.finrank_eq]
    simp
    decide
  have hrn := LinearMap.finrank_range_add_finrank_ker ((glExterior3Rep K) a - 1)
  rw [hdimV, hrank_range] at hrn
  have hdimfix : Module.finrank K (fixSubGen (glExterior3Rep K) (Subgroup.closure {a})) +
      r3 = 20 := by
    rw [fixSubGen_closure_singleton]
    omega
  omega

end CFSG.HardMathSupport.GuralnickMalle
