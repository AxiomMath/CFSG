module

public import CFSG.ClassicalInvolution.Phan.PhanDn.PanelStab

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits
open CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.Phan.PhanE
open CFSG.Monster.B.Geometry
open QuadraticMap

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f)) {m : ℕ}

variable {M : CoxeterMatrix (Fin (m + 1))}
  {S : PhanFamilyE K 2 f M ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}

theorem parab_singleton (i : Fin (m + 1)) :
    S.parab {i} = S.torus ⊔ (S.ι i).range := by
  rw [PhanFamilyE.parab, iSup_singleton]

theorem conjTau_conjTau
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
    conjTau E (conjTau E g) = g := by
  have hτ : tauAt E (Fin.last m) * tauAt E (Fin.last m) = 1 :=
    tauAt_mul_self E (Fin.last m)
  have hτ' : (tauAt E (Fin.last m))⁻¹ = tauAt E (Fin.last m) :=
    inv_eq_of_mul_eq_one_right hτ
  refine Subtype.ext ?_
  rw [coe_conjTau, coe_conjTau, hτ']
  calc tauAt E (Fin.last m) * (tauAt E (Fin.last m) *
        (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) * tauAt E (Fin.last m)) *
        tauAt E (Fin.last m)
      = (tauAt E (Fin.last m) * tauAt E (Fin.last m)) *
          (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
          (tauAt E (Fin.last m) * tauAt E (Fin.last m)) := by group
    _ = g := by rw [hτ]; simp

theorem torus_le_panelStab (hm : 3 ≤ m) (hS : IsStdDFamily E hm S) (i : Fin (m + 1)) :
    S.torus ≤ panelStab E i := by
  intro g hg
  rw [hS.torus_eq] at hg
  rw [mem_panelStab]
  have hstab : g • stdDChamber (unitaryInvolution K 2 f) (m + 1) =
      stdDChamber (unitaryInvolution K 2 f) (m + 1) := by
    rw [smul_stdDChamber_eq_iff (n := m + 1)]
    exact hg
  intro j _
  have h := congrArg (fun c : DChamber (unitaryInvolution K 2 f) (m + 1) => c.elt j) hstab
  rw [elt_smul] at h
  exact h

@[expose] def coordSpan (n : ℕ) (I J : Set (Fin n)) :
    Submodule K (Fin n ⊕ Fin n → K) :=
  Submodule.span K (stdE (K := K) (n := n) '' I ∪ stdF (K := K) (n := n) '' J)

omit [Finite K] [CharP K 2] in
theorem coordSpan_mono {n : ℕ} {I I' J J' : Set (Fin n)} (hI : I ⊆ I') (hJ : J ⊆ J') :
    coordSpan (K := K) n I J ≤ coordSpan (K := K) n I' J' := by
  refine Submodule.span_mono ?_
  rintro v (hv | hv)
  · exact Or.inl (Set.image_mono hI hv)
  · exact Or.inr (Set.image_mono hJ hv)

theorem stdDChamber_elt_last_eq_coordSpan :
    (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt (Fin.last m) =
      coordSpan (K := K) (m + 1) Set.univ ∅ := by
  rw [stdDChamber_elt_last, stdDChamber_sub_eq_span,
    show {i : Fin (m + 1) | (i : ℕ) < m + 1} = Set.univ by
      ext i
      exact ⟨fun _ => Set.mem_univ i, fun _ => i.isLt⟩,
    Set.image_univ]
  simp only [coordSpan, Set.image_univ, Set.image_empty, Set.union_empty]

theorem stdDChamber_elt_eq_sub_coordSpan {j : Fin (m + 1)} (hj : j ≠ Fin.last m)
    (hj' : (j : ℕ) + 1 ≠ m) :
    (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt j =
      coordSpan (K := K) (m + 1) {i : Fin (m + 1) | (i : ℕ) < (j : ℕ) + 1} ∅ := by
  rw [stdDChamber_elt_eq_sub hj hj', stdDChamber_sub_eq_span]
  simp only [coordSpan, Set.image_empty, Set.union_empty]

theorem stdDChamber_elt_eq_alt_coordSpan {j : Fin (m + 1)} (hj : j ≠ Fin.last m)
    (hj' : (j : ℕ) + 1 = m) :
    (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt j =
      coordSpan (K := K) (m + 1) {i : Fin (m + 1) | (i : ℕ) < m} {Fin.last m} := by
  rw [stdDChamber_elt_eq_alt hj hj', stdDChamber_alt_eq, stdDChamber_sub_eq_span]
  simp only [coordSpan, Submodule.span_union, Set.image_singleton]

theorem map_coordSpan_le_of_bc {n : ℕ} (g : (Fin n → K) ≃ₗ[F] (Fin n → K))
    {I J : Set (Fin n)}
    (hI : ∀ i ∈ I, bc E n g (stdE (K := K) (n := n) i) ∈ coordSpan (K := K) n I J)
    (hJ : ∀ j ∈ J, bc E n g (stdF (K := K) (n := n) j) ∈ coordSpan (K := K) n I J) :
    (coordSpan (K := K) n I J).map
        (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))) ≤ coordSpan (K := K) n I J := by
  rw [bcLin_eq_coe_bc]
  simp only [coordSpan]
  rw [Submodule.map_span, Submodule.span_le]
  rintro v ⟨u, hu, rfl⟩
  rcases hu with hu | hu
  · obtain ⟨i, hi, rfl⟩ := hu
    exact hI i hi
  · obtain ⟨j, hj, rfl⟩ := hu
    exact hJ j hj

theorem map_coordSpan_eq_of_bc {n : ℕ} (g : (Fin n → K) ≃ₗ[F] (Fin n → K))
    {I J : Set (Fin n)}
    (hI : ∀ i ∈ I, bc E n g (stdE (K := K) (n := n) i) ∈ coordSpan (K := K) n I J)
    (hJ : ∀ j ∈ J, bc E n g (stdF (K := K) (n := n) j) ∈ coordSpan (K := K) n I J) :
    (coordSpan (K := K) n I J).map
        (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))) = coordSpan (K := K) n I J := by
  refine Submodule.eq_of_le_of_finrank_eq (map_coordSpan_le_of_bc E g hI hJ) ?_
  rw [bcLin_eq_coe_bc]
  exact LinearEquiv.finrank_map_eq (bc E n g) _

theorem bc_suEndN_stdE {n : ℕ} (B : SUid (unitaryInvolution K 2 f) n) (i : Fin n) :
    bc E n (suEndN (F := F) (unitaryInvolution K 2 f) n B) (stdE (K := K) (n := n) i) =
      ∑ a : Fin n, ((((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a i)) •
        stdE (K := K) (n := n) a := by
  have h := bc_suEndN E n B (stdE (K := K) (n := n) i)
  ext p
  cases p with
  | inl a =>
    rw [h.1 a, Finset.sum_apply, Finset.sum_eq_single a]
    · have hvec : (fun j : Fin n => stdE (K := K) (n := n) i (Sum.inl j)) =
          Pi.single i 1 := by
        funext j
        simp only [stdE, Pi.single_apply, Sum.inl.injEq]
      rw [hvec, Matrix.mulVec_single_one]
      simp [stdE]
    · intro b _ hb
      simp [stdE, hb]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  | inr a =>
    rw [h.2 a]
    have hvec : (fun j : Fin n => stdE (K := K) (n := n) i (Sum.inr j)) = 0 := by
      funext j
      simp [stdE]
    rw [hvec, Matrix.mulVec_zero]
    simp [stdE]

theorem bc_suEndN_stdF {n : ℕ} (B : SUid (unitaryInvolution K 2 f) n) (i : Fin n) :
    bc E n (suEndN (F := F) (unitaryInvolution K 2 f) n B) (stdF (K := K) (n := n) i) =
      ∑ a : Fin n, (unitaryInvolution K 2 f)
          ((((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a i)) •
        stdF (K := K) (n := n) a := by
  have h := bc_suEndN E n B (stdF (K := K) (n := n) i)
  ext p
  cases p with
  | inl a =>
    rw [h.1 a]
    have hvec : (fun j : Fin n => stdF (K := K) (n := n) i (Sum.inl j)) = 0 := by
      funext j
      simp [stdF]
    rw [hvec, Matrix.mulVec_zero]
    simp [stdF]
  | inr a =>
    rw [h.2 a, Finset.sum_apply, Finset.sum_eq_single a]
    · have hvec : (fun j : Fin n => stdF (K := K) (n := n) i (Sum.inr j)) =
          Pi.single i 1 := by
        funext j
        simp only [stdF, Pi.single_apply, Sum.inr.injEq]
      rw [hvec, Matrix.mulVec_single_one]
      simp [stdF]
    · intro b _ hb
      simp [stdF, hb]
    · intro ha
      exact absurd (Finset.mem_univ a) ha

theorem bc_suEndN_blockEmb_stdE_of_not_mem {m a len : ℕ}
    (h : a + len ≤ m + 1) (A : Su K 2 f len) {i : Fin (m + 1)}
    (hi : ¬ (a ≤ i.val ∧ i.val < a + len)) :
    bc E (m + 1) (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1)
        (blockEmb K 2 f (m + 1) len a h A)) (stdE (K := K) (n := m + 1) i) =
      stdE (K := K) (n := m + 1) i := by
  rw [bc_suEndN_stdE]
  rw [Finset.sum_eq_single i]
  · rw [coe_coe_blockEmb, blockMat_apply_of_not_mem_left _ hi, Matrix.one_apply_eq, one_smul]
  · intro b _ hbi
    rw [coe_coe_blockEmb, blockMat_apply_of_not_mem_right _ b hi, Matrix.one_apply_ne hbi,
      zero_smul]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

theorem bc_suEndN_blockEmb_stdF_of_not_mem {m a len : ℕ}
    (h : a + len ≤ m + 1) (A : Su K 2 f len) {i : Fin (m + 1)}
    (hi : ¬ (a ≤ i.val ∧ i.val < a + len)) :
    bc E (m + 1) (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1)
        (blockEmb K 2 f (m + 1) len a h A)) (stdF (K := K) (n := m + 1) i) =
      stdF (K := K) (n := m + 1) i := by
  rw [bc_suEndN_stdF]
  rw [Finset.sum_eq_single i]
  · rw [coe_coe_blockEmb, blockMat_apply_of_not_mem_left _ hi, Matrix.one_apply_eq]
    simp
  · intro b _ hbi
    rw [coe_coe_blockEmb, blockMat_apply_of_not_mem_right _ b hi, Matrix.one_apply_ne hbi,
      map_zero, zero_smul]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

private theorem bc_suEndN_blockEmb_stdE_mem_coordSpan {m a len : ℕ}
    (h : a + len ≤ m + 1) (A : Su K 2 f len) {I J : Set (Fin (m + 1))}
    (hsub : ∀ b : Fin (m + 1), a ≤ b.val → b.val < a + len → b ∈ I)
    {i : Fin (m + 1)} (hi : i ∈ I) :
    bc E (m + 1) (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1)
        (blockEmb K 2 f (m + 1) len a h A)) (stdE (K := K) (n := m + 1) i) ∈
      coordSpan (K := K) (m + 1) I J := by
  by_cases hiW : a ≤ i.val ∧ i.val < a + len
  · rw [bc_suEndN_stdE]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hbW : a ≤ b.val ∧ b.val < a + len
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span (Or.inl ⟨b, hsub b hbW.1 hbW.2, rfl⟩))
    · have hz : ((((blockEmb K 2 f (m + 1) len a h A : Su K 2 f (m + 1)) :
            GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) b i = 0 := by
        rw [coe_coe_blockEmb, blockMat_apply_of_not_mem_left _ hbW]
        have hbi : b ≠ i := by
          intro h'
          exact hbW (h' ▸ hiW)
        rw [Matrix.one_apply_ne hbi]
      rw [hz, zero_smul]
      exact Submodule.zero_mem _
  · rw [bc_suEndN_blockEmb_stdE_of_not_mem E h A hiW]
    exact Submodule.subset_span (Or.inl ⟨i, hi, rfl⟩)

private theorem bc_suEndN_blockEmb_stdF_mem_coordSpan {m a len : ℕ}
    (h : a + len ≤ m + 1) (A : Su K 2 f len) {I J : Set (Fin (m + 1))}
    (hsub : ∀ b : Fin (m + 1), a ≤ b.val → b.val < a + len → b ∈ J)
    {i : Fin (m + 1)} (hi : i ∈ J) :
    bc E (m + 1) (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1)
        (blockEmb K 2 f (m + 1) len a h A)) (stdF (K := K) (n := m + 1) i) ∈
      coordSpan (K := K) (m + 1) I J := by
  by_cases hiW : a ≤ i.val ∧ i.val < a + len
  · rw [bc_suEndN_stdF]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hbW : a ≤ b.val ∧ b.val < a + len
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span (Or.inr ⟨b, hsub b hbW.1 hbW.2, rfl⟩))
    · have hz : ((((blockEmb K 2 f (m + 1) len a h A : Su K 2 f (m + 1)) :
            GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) b i = 0 := by
        rw [coe_coe_blockEmb, blockMat_apply_of_not_mem_left _ hbW]
        have hbi : b ≠ i := by
          intro h'
          exact hbW (h' ▸ hiW)
        rw [Matrix.one_apply_ne hbi]
      rw [hz, map_zero, zero_smul]
      exact Submodule.zero_mem _
  · rw [bc_suEndN_blockEmb_stdF_of_not_mem E h A hiW]
    exact Submodule.subset_span (Or.inr ⟨i, hi, rfl⟩)

theorem map_coordSpan_eq_of_blockEmb {m a len : ℕ}
    (h : a + len ≤ m + 1) (A : Su K 2 f len) {I J : Set (Fin (m + 1))}
    (hI : (∀ i : Fin (m + 1), a ≤ i.val → i.val < a + len → i ∈ I) ∨
      (∀ i ∈ I, ¬ (a ≤ i.val ∧ i.val < a + len)))
    (hJ : (∀ j : Fin (m + 1), a ≤ j.val → j.val < a + len → j ∈ J) ∨
      (∀ j ∈ J, ¬ (a ≤ j.val ∧ j.val < a + len))) :
    (coordSpan (K := K) (m + 1) I J).map
        (bcLin E (m + 1) (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1)
          (blockEmb K 2 f (m + 1) len a h A) :
          (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
      coordSpan (K := K) (m + 1) I J := by
  refine map_coordSpan_eq_of_bc (K := K) E _ (fun i hi => ?_) (fun j hj => ?_)
  · rcases hI with hsub | hdisj
    · exact bc_suEndN_blockEmb_stdE_mem_coordSpan E h A hsub hi
    · rw [bc_suEndN_blockEmb_stdE_of_not_mem E h A (hdisj i hi)]
      exact Submodule.subset_span (Or.inl ⟨i, hi, rfl⟩)
  · rcases hJ with hsub | hdisj
    · exact bc_suEndN_blockEmb_stdF_mem_coordSpan E h A hsub hj
    · rw [bc_suEndN_blockEmb_stdF_of_not_mem E h A (hdisj j hj)]
      exact Submodule.subset_span (Or.inr ⟨j, hj, rfl⟩)


private theorem bc_apply_mul {n : ℕ} (u v : (Fin n → K) ≃ₗ[F] (Fin n → K))
    (w : Fin n ⊕ Fin n → K) :
    bc E n (u * v) w = bc E n u (bc E n v w) := by
  rw [map_mul]
  rfl

private theorem bcLin_conjTau_comp
    (x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
    (bcLin E (m + 1) ((conjTau E x :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))).comp
      (bcLin E (m + 1) (tauAt E (Fin.last m) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
    (bcLin E (m + 1) (tauAt E (Fin.last m) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))).comp
      (bcLin E (m + 1) ((x :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) := by
  have hτ : (tauAt E (Fin.last m))⁻¹ = tauAt E (Fin.last m) :=
    inv_eq_of_mul_eq_one_right (tauAt_mul_self E (Fin.last m))
  have hgrp : ((conjTau E x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) * tauAt E (Fin.last m) =
      tauAt E (Fin.last m) * (x :
        (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) := by
    rw [coe_conjTau, hτ]
    calc (tauAt E (Fin.last m) * (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
          tauAt E (Fin.last m)) * tauAt E (Fin.last m)
        = (tauAt E (Fin.last m) *
            (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))) *
            (tauAt E (Fin.last m) * tauAt E (Fin.last m)) := by group
      _ = tauAt E (Fin.last m) *
            (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) := by
            rw [tauAt_mul_self E (Fin.last m), mul_one]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, bcLin_eq_coe_bc]
  calc bc E (m + 1) ((conjTau E x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
        (bc E (m + 1) (tauAt E (Fin.last m)) v)
      = bc E (m + 1) (((conjTau E x :
            ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
            (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
          tauAt E (Fin.last m)) v :=
        (bc_apply_mul (E := E) (n := m + 1) _ _ _).symm
    _ = bc E (m + 1) (tauAt E (Fin.last m) * (x :
          (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))) v := by rw [hgrp]
    _ = bc E (m + 1) (tauAt E (Fin.last m))
          (bc E (m + 1) (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) v) :=
        bc_apply_mul (E := E) (n := m + 1) _ _ _

private theorem conj_tau_diagHom_exists
    (t : Fin (m + 1) → normOne (unitaryInvolution K 2 f)) :
    ∃ t' : Fin (m + 1) → normOne (unitaryInvolution K 2 f),
      tauAt E (Fin.last m) * diagHom F (unitaryInvolution K 2 f) (m + 1) t *
          (tauAt E (Fin.last m))⁻¹ =
        diagHom F (unitaryInvolution K 2 f) (m + 1) t' := by
  let u : Kˣ := (t (Fin.last m) : Kˣ)
  let u' : Kˣ := Units.map ((unitaryInvolution K 2 f) : K →* K) u
  have hu' : u' ∈ normOne (unitaryInvolution K 2 f) := by
    rw [CFSG.LieType.Steinberg.mem_normOne]
    change unitaryInvolution K 2 f (unitaryInvolution K 2 f ((u : K))) *
      unitaryInvolution K 2 f ((u : K)) = 1
    rw [E.isUnitary.invol]
    have hu : ((t (Fin.last m) : normOne (unitaryInvolution K 2 f)) : Kˣ) ∈
        normOne (unitaryInvolution K 2 f) := (t (Fin.last m)).2
    rw [CFSG.LieType.Steinberg.mem_normOne] at hu
    simpa [u, mul_comm] using hu
  refine ⟨Function.update t (Fin.last m) ⟨u', hu'⟩, ?_⟩
  have hτ : (tauAt E (Fin.last m))⁻¹ = tauAt E (Fin.last m) :=
    inv_eq_of_mul_eq_one_right (tauAt_mul_self E (Fin.last m))
  apply LinearEquiv.ext
  intro a
  rw [hτ]
  funext i
  by_cases hi : i = Fin.last m
  · subst hi
    simp only [LinearEquiv.mul_apply, tauAt_apply, if_true, diagHom_apply,
      Function.update_self]
    rw [map_mul, E.isUnitary.invol]
    simp [u', u, Units.coe_map]
  · simp [tauAt_apply, diagHom_apply, Function.update, hi]

theorem range_ι_castSucc_le_panelStab (hm : 3 ≤ m) (hS : IsStdDFamily E hm S) (k : Fin m) :
    (S.ι k.castSucc).range ≤ panelStab E k.castSucc := by
  rintro g ⟨A, rfl⟩
  rw [mem_panelStab]
  intro j hj
  have hcoe : ((S.ι k.castSucc A :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) =
      (stdChainIota (F := F) (f := f) m k A :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) :=
    congrArg (fun e : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K) =>
      (e : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) (hS.ι_castSucc k A)
  rw [hcoe]
  have hstd : (stdChainIota (F := F) (f := f) m k A :
      (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) =
      (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1)
        (blockEmb K 2 f (m + 1) 2 k.val (by omega) A) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) := rfl
  by_cases hjlast : j = Fin.last m
  · subst hjlast
    rw [stdDChamber_elt_last_eq_coordSpan, hstd]
    exact map_coordSpan_eq_of_blockEmb (K := K) E (a := k.val) (len := 2) (by omega) A
      (Or.inl (fun _ _ _ => Set.mem_univ _)) (Or.inr (fun j' hj' => by simp at hj'))
  · by_cases hjalt : (j : ℕ) + 1 = m
    · have hjval : (j : ℕ) = m - 1 := by
        have := j.isLt
        omega
      have hkne : (k : ℕ) ≠ m - 1 := by
        intro h
        apply hj
        apply Fin.ext
        show (j : ℕ) = (k.castSucc : Fin (m + 1))
        rw [Fin.val_castSucc, hjval, h]
      rw [stdDChamber_elt_eq_alt_coordSpan hjlast hjalt, hstd]
      refine map_coordSpan_eq_of_blockEmb (K := K) E (a := k.val) (len := 2) (by omega) A ?_ ?_
      · left
        intro i hi₁ hi₂
        simp only [Set.mem_setOf_eq]
        have := k.isLt
        omega
      · right
        intro j' hj' hiW
        simp only [Set.mem_singleton_iff] at hj'
        subst hj'
        simp only [Fin.val_last] at hiW
        omega
    · rw [stdDChamber_elt_eq_sub_coordSpan hjlast hjalt, hstd]
      have hne : j.val ≠ k.val := fun h => hj (Fin.ext (by simpa using h))
      refine map_coordSpan_eq_of_blockEmb (K := K) E (a := k.val) (len := 2) (by omega) A ?_
        (Or.inr (fun j' hj' => by simp at hj'))
      by_cases hkj : k.val < j.val + 1
      · left
        intro i hi₁ hi₂
        simp only [Set.mem_setOf_eq]
        omega
      · right
        intro i hi hiW
        simp only [Set.mem_setOf_eq] at hi
        omega

theorem map_conjTau_panelStab (hm : 3 ≤ m) :
    (panelStab E ⟨m - 1, by omega⟩).map (conjTau E).toMonoidHom =
      panelStab E (Fin.last m) := by
  let a : Fin (m + 1) := ⟨m - 1, by omega⟩
  let s : Equiv.Perm (Fin (m + 1)) := Equiv.swap a (Fin.last m)
  change (panelStab E a).map (conjTau E).toMonoidHom = panelStab E (Fin.last m)
  have hs_invol : ∀ j : Fin (m + 1), s (s j) = j := by
    intro j
    change Equiv.swap a (Fin.last m) (Equiv.swap a (Fin.last m) j) = j
    by_cases h1 : j = a
    · subst h1
      rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
    · by_cases h2 : j = Fin.last m
      · subst h2
        rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2,
          Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hs_a : s a = Fin.last m := by
    change Equiv.swap a (Fin.last m) a = Fin.last m
    exact Equiv.swap_apply_left _ _
  have hs_last : s (Fin.last m) = a := by
    change Equiv.swap a (Fin.last m) (Fin.last m) = a
    exact Equiv.swap_apply_right _ _
  have hs_ne_a : ∀ j, s j ≠ a ↔ j ≠ Fin.last m := by
    intro j
    constructor
    · intro h hlast
      exact h (by rw [hlast, hs_last])
    · intro hlast hsa
      have := congrArg s hsa
      rw [hs_invol j, hs_a] at this
      exact hlast this
  have hs_ne_last : ∀ j, s j ≠ Fin.last m ↔ j ≠ a := by
    intro j
    constructor
    · intro h ha
      exact h (by rw [ha, hs_a])
    · intro ha hslast
      have := congrArg s hslast
      rw [hs_invol j, hs_last] at this
      exact ha this
  have hinj : Function.Injective (bcLin E (m + 1) (tauAt E (Fin.last m) :
      (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) := by
    intro u v huv
    rw [bcLin_eq_coe_bc] at huv
    exact (bc E (m + 1) (tauAt E (Fin.last m))).injective huv
  have fix_imp : ∀ (x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
      (j : Fin (m + 1)),
      ((stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt (s j)).map
          (bcLin E (m + 1) (x : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt (s j) →
      ((stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt j).map
          (bcLin E (m + 1) ((conjTau E x :
            ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
            (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt j := by
    intro x j hjx
    have hmap : ((stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt j).map
        (bcLin E (m + 1) (tauAt E (Fin.last m) :
          (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt (s j) := by
      simpa [s, a] using map_bc_tauAt_elt (f := f) E hm j
    have hcomp := bcLin_conjTau_comp (F := F) (f := f) E (conjTau E x)
    rw [conjTau_conjTau] at hcomp
    apply Submodule.map_injective_of_injective hinj
    rw [← Submodule.map_comp, ← hcomp, Submodule.map_comp, hmap, hjx]
  have key : ∀ x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))),
      x ∈ panelStab E a ↔ conjTau E x ∈ panelStab E (Fin.last m) := by
    intro x
    rw [mem_panelStab, mem_panelStab]
    constructor
    · intro h j hj
      exact fix_imp x j (h (s j) ((hs_ne_a j).mpr hj))
    · intro h j hj
      have hy := fix_imp (conjTau E x) j (h (s j) ((hs_ne_last j).mpr hj))
      rwa [conjTau_conjTau] at hy
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (key y).mp hy
  · intro hx
    refine ⟨conjTau E x, (key (conjTau E x)).mpr ?_, conjTau_conjTau E x⟩
    rwa [conjTau_conjTau]

theorem map_conjTau_torus (hm : 3 ≤ m) (hS : IsStdDFamily E hm S) :
    S.torus.map (conjTau E).toMonoidHom = S.torus := by
  rw [hS.torus_eq]
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    change ((y : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      diagTorusV F (unitaryInvolution K 2 f) (m + 1) at hy
    change ((conjTau E y : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      diagTorusV F (unitaryInvolution K 2 f) (m + 1)
    rw [coe_conjTau]
    obtain ⟨t, ht⟩ := hy
    rw [← ht]
    obtain ⟨t', ht'⟩ := conj_tau_diagHom_exists (F := F) (f := f) E t
    exact ⟨t', ht'.symm⟩
  · intro x hx
    change ((x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      diagTorusV F (unitaryInvolution K 2 f) (m + 1) at hx
    obtain ⟨t, ht⟩ := hx
    obtain ⟨t', ht'⟩ := conj_tau_diagHom_exists (F := F) (f := f) E t
    refine ⟨conjTau E x, ?_, conjTau_conjTau E x⟩
    change ((conjTau E x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      diagTorusV F (unitaryInvolution K 2 f) (m + 1)
    rw [coe_conjTau, ← ht]
    exact ⟨t', ht'.symm⟩

theorem map_conjTau_range_ι (hm : 3 ≤ m) (hS : IsStdDFamily E hm S) :
    (S.ι ⟨m - 1, by omega⟩).range.map (conjTau E).toMonoidHom =
      (S.ι (Fin.last m)).range := by
  have hidx : (⟨m - 1, by omega⟩ : Fin (m + 1)) =
      ((⟨m - 1, by omega⟩ : Fin m).castSucc : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  have hgen : ∀ A : Su K 2 f 2,
      conjTau E (S.ι ⟨m - 1, by omega⟩ A) = S.ι (Fin.last m) A := by
    intro A
    apply Subtype.ext
    rw [coe_conjTau]
    rw [show ((S.ι ⟨m - 1, by omega⟩ A :
          ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
          (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
        stdChainIota (F := F) (f := f) m (⟨m - 1, by omega⟩ : Fin m) A from by
      rw [hidx]
      exact hS.ι_castSucc (⟨m - 1, by omega⟩ : Fin m) A]
    rw [hS.ι_last A]
    rfl
  apply le_antisymm
  · rintro x ⟨y, hy, hxy⟩
    obtain ⟨A, rfl⟩ := hy
    refine ⟨A, ?_⟩
    rw [← hxy]
    exact (hgen A).symm
  · rintro x ⟨A, rfl⟩
    exact ⟨S.ι ⟨m - 1, by omega⟩ A, ⟨A, rfl⟩, hgen A⟩

theorem map_conjTau_parab (hm : 3 ≤ m) (hS : IsStdDFamily E hm S) :
    (S.parab {⟨m - 1, by omega⟩}).map (conjTau E).toMonoidHom =
      S.parab {Fin.last m} := by
  rw [parab_singleton (E := E) (i := ⟨m - 1, by omega⟩),
    parab_singleton (E := E) (i := Fin.last m), Subgroup.map_sup,
    map_conjTau_torus E hm hS, map_conjTau_range_ι E hm hS]

theorem parab_le_panelStab (hm : 3 ≤ m) (hS : IsStdDFamily E hm S) (i : Fin (m + 1)) :
    S.parab {i} ≤ panelStab E i := by
  by_cases hi : i = Fin.last m
  · subst hi
    have hchain : S.parab {⟨m - 1, by omega⟩} ≤ panelStab E ⟨m - 1, by omega⟩ := by
      rw [parab_singleton (E := E) (i := ⟨m - 1, by omega⟩)]
      refine sup_le (torus_le_panelStab E hm hS _) ?_
      have hidx : (⟨m - 1, by omega⟩ : Fin (m + 1)) =
          ((⟨m - 1, by omega⟩ : Fin m).castSucc : Fin (m + 1)) := by
        apply Fin.ext
        rfl
      rw [hidx]
      exact range_ι_castSucc_le_panelStab E hm hS (⟨m - 1, by omega⟩ : Fin m)
    rw [← map_conjTau_parab E hm hS, ← map_conjTau_panelStab E hm]
    exact Subgroup.map_mono hchain
  · have hival : i.val < m := by
      have h1 := i.isLt
      have hne : i.val ≠ m := fun h' => hi (Fin.ext (by simpa using h'))
      omega
    rw [parab_singleton (E := E) i]
    have hidx : i = ((⟨i.val, hival⟩ : Fin m).castSucc : Fin (m + 1)) := by
      apply Fin.ext
      rfl
    rw [hidx]
    exact sup_le (torus_le_panelStab E hm hS _)
      (range_ι_castSucc_le_panelStab E hm hS ⟨i.val, hival⟩)

end CFSG.ClassicalInvolution.PhanDn

end
