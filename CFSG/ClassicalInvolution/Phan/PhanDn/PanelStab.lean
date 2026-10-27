module

public import CFSG.ClassicalInvolution.Phan.PhanDn.Chambers
public import CFSG.ClassicalInvolution.Phan.PhanDn.StdFamilyTorus
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipFrame
import all CFSG.ClassicalInvolution.Phan.PhanDn.BaseChange

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


noncomputable def subStab (W : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)) :
    Subgroup ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) where
  carrier := {g | W.map (bcLin E (m + 1) (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) = W}
  one_mem' := by
    change (W.map (bcLin E (m + 1)
      ((1 : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)))) = W
    rw [show ((1 : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) = LinearMap.id from rfl,
      bcLin_id, Submodule.map_id]
  mul_mem' {g h} hg hh := by
    change W.map (bcLin E (m + 1)
      ((g * h : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) = W
    rw [show ((g * h : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) =
      ((g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)).comp
        (h : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) from rfl,
      bcLin_comp, Submodule.map_comp]
    rw [hh, hg]
  inv_mem' {g} hg := by
    have hgg : ((g⁻¹ * g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) = LinearMap.id := by
      have h1 : ((g⁻¹ * g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
          (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) =
          ((1 : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
            (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) :=
        congrArg (fun e : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) =>
          (e : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) (inv_mul_cancel g)
      exact h1
    have hmul : ((g⁻¹ * g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) =
        ((g⁻¹ : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
          (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)).comp
          (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) := rfl
    have hcomp : bcLin E (m + 1)
        (((g⁻¹ : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
            (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)).comp
          (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        (bcLin E (m + 1) ((g⁻¹ :
            ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
            (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))).comp
          (bcLin E (m + 1) (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) :=
      bcLin_comp E (m + 1) _ _
    change W.map (bcLin E (m + 1)
      ((g⁻¹ : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) = W
    calc W.map (bcLin E (m + 1) ((g⁻¹ :
          ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
          (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)))
        = (W.map (bcLin E (m + 1) (g : (Fin (m + 1) → K) →ₗ[F]
            (Fin (m + 1) → K)))).map (bcLin E (m + 1) ((g⁻¹ :
            ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
            (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) := by rw [hg]
      _ = W.map ((bcLin E (m + 1) ((g⁻¹ :
            ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
            (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))).comp
            (bcLin E (m + 1) (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)))) := by
          rw [Submodule.map_comp]
      _ = W.map (bcLin E (m + 1) (((g⁻¹ :
            ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
            (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)).comp
          (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)))) := by
          rw [hcomp]
      _ = W.map (bcLin E (m + 1)
          (((g⁻¹ * g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
            (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)))) := by
          rw [hmul]
      _ = W := by rw [hgg, bcLin_id, Submodule.map_id]

noncomputable def panelStab (i : Fin (m + 1)) :
    Subgroup ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :=
  ⨅ (j : Fin (m + 1)) (_ : j ≠ i),
    subStab E ((stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt j)

theorem mem_panelStab {i : Fin (m + 1)}
    {g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))} :
    g ∈ panelStab E i ↔ ∀ j, j ≠ i →
      ((stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt j).map (bcLin E (m + 1)
        (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
        (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt j := by
  simp only [panelStab, Subgroup.mem_iInf, subStab]
  rfl

theorem adj_smul_stdDChamber_iff_mem_panelStab (i : Fin (m + 1))
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
    (dChamberSystem (unitaryInvolution K 2 f) m).adj i
        (g • stdDChamber (unitaryInvolution K 2 f) (m + 1))
        (stdDChamber (unitaryInvolution K 2 f) (m + 1)) ↔ g ∈ panelStab E i := by
  rw [dChamberSystem_adj_iff]
  constructor
  · intro h
    rw [mem_panelStab]
    intro j hj
    have h1 := h j hj
    rw [elt_smul] at h1
    exact h1
  · intro h j hj
    rw [mem_panelStab] at h
    rw [elt_smul]
    exact h j hj


omit [Finite K] [CharP K 2] in
private theorem finset_sup_span_singleton {ι M : Type*} [AddCommGroup M] [Module K M]
    (s : Finset ι) (v : ι → M) :
    s.sup (fun i => K ∙ v i) = Submodule.span K (v '' (s : Set ι)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sup_insert, ih, ← Submodule.span_union]
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff, Finset.coe_insert,
      Set.mem_insert_iff]
    constructor
    · rintro (rfl | ⟨y, hy, rfl⟩)
      · exact ⟨a, Or.inl rfl, rfl⟩
      · exact ⟨y, Or.inr hy, rfl⟩
    · rintro ⟨y, rfl | hy, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨y, hy, rfl⟩

theorem stdFrame_sub_eq_span (n j : ℕ) :
    (FlipFrame.stdFrame (unitaryInvolution K 2 f) n).sub j =
      Submodule.span K (stdE (K := K) (n := n) '' {i : Fin n | (i : ℕ) < j}) := by
  rw [FlipFrame.sub, FlipFrame.spanAt]
  change (Finset.univ.filter fun l : Fin n => (l : ℕ) < j).sup
    (fun i => K ∙ stdE (K := K) (n := n) i) = _
  rw [finset_sup_span_singleton]
  congr 1
  ext v
  simp

theorem stdDChamber_sub_eq_span (j : ℕ) :
    (stdDChamber (unitaryInvolution K 2 f) (m + 1)).sub j =
      Submodule.span K (stdE (K := K) (n := m + 1) '' {i : Fin (m + 1) | (i : ℕ) < j}) :=
  stdFrame_sub_eq_span (f := f) (m + 1) j

theorem stdDChamber_alt_eq :
    (stdDChamber (unitaryInvolution K 2 f) (m + 1)).alt =
      (stdDChamber (unitaryInvolution K 2 f) (m + 1)).sub m ⊔
        K ∙ stdF (K := K) (n := m + 1) (Fin.last m) := by
  change (FlipFrame.stdFrame (unitaryInvolution K 2 f) (m + 1)).alt =
    (stdDChamber (unitaryInvolution K 2 f) (m + 1)).sub m ⊔ _
  rw [FlipFrame.alt]
  congr 1
  change dFlipSub (unitaryInvolution K 2 f)
    (K ∙ stdE (K := K) (n := m + 1) (Fin.last m)) = K ∙ stdF (K := K) (n := m + 1) (Fin.last m)
  rw [dFlipSub_span_singleton, show dFlip (unitaryInvolution K 2 f)
      (stdE (K := K) (n := m + 1) (Fin.last m)) =
      stdF (K := K) (n := m + 1) (Fin.last m) from by
    funext i
    cases i with
    | inl j =>
      by_cases hj : j = Fin.last m
      · subst hj
        simp [dFlip, stdE, stdF]
      · simp [dFlip, stdE, stdF]
    | inr j =>
      by_cases hj : j = Fin.last m
      · subst hj
        simp [dFlip, stdE, stdF]
      · simp [dFlip, stdE, stdF, hj]]

theorem stdDChamber_elt_last :
    (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt (Fin.last m) =
      (stdDChamber (unitaryInvolution K 2 f) (m + 1)).sub (m + 1) := by
  rw [FlipFrame.elt]
  simp

theorem stdDChamber_elt_eq_sub {i : Fin (m + 1)} (hi : i ≠ Fin.last m)
    (hi' : (i : ℕ) + 1 ≠ m) :
    (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt i =
      (stdDChamber (unitaryInvolution K 2 f) (m + 1)).sub ((i : ℕ) + 1) := by
  rw [FlipFrame.elt]
  simp [hi, hi']

theorem stdDChamber_elt_eq_alt {i : Fin (m + 1)} (hi : i ≠ Fin.last m)
    (hi' : (i : ℕ) + 1 = m) :
    (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt i =
      (stdDChamber (unitaryInvolution K 2 f) (m + 1)).alt := by
  rw [FlipFrame.elt]
  simp [hi, hi']

omit [Finite K] [CharP K 2] in
theorem swapAt_stdE_of_ne {i : Fin (m + 1)} (hi : i ≠ Fin.last m) :
    swapAt (m + 1) (Fin.last m) (stdE (K := K) (n := m + 1) i) =
      stdE (K := K) (n := m + 1) i := by
  ext p
  cases p with
  | inl j =>
    simp only [swapAt_inl]
    split_ifs with hj
    · have hij : i ≠ j := fun h => hi (h.trans hj)
      have hji : j ≠ i := Ne.symm hij
      simp [stdE, Pi.single_eq_of_ne, hji]
    · by_cases hij : i = j
      · subst hij; simp
      · have hji : j ≠ i := Ne.symm hij
        simp [stdE, hji]
  | inr j =>
    simp only [swapAt_inr]
    split_ifs with hj
    · have hij : i ≠ j := fun h => hi (h.trans hj)
      have hji : j ≠ i := Ne.symm hij
      simp [stdE, Pi.single_eq_of_ne, hji]
    · simp [stdE]

omit [Finite K] [CharP K 2] in
theorem swapAt_stdE_last :
    swapAt (m + 1) (Fin.last m) (stdE (K := K) (n := m + 1) (Fin.last m)) =
      stdF (K := K) (n := m + 1) (Fin.last m) := by
  ext p
  cases p with
  | inl j =>
    simp only [swapAt_inl]
    by_cases hj : j = Fin.last m
    · subst hj
      simp [stdE, stdF]
    · have hji : j ≠ Fin.last m := hj
      simp [stdF, Pi.single_eq_of_ne, hj]
  | inr j =>
    simp only [swapAt_inr]
    by_cases hj : j = Fin.last m
    · subst hj
      simp [stdE, stdF]
    · simp [stdE, stdF, Pi.single_eq_of_ne, hj]

omit [Finite K] [CharP K 2] in
theorem swapAt_stdF_of_ne {i : Fin (m + 1)} (hi : i ≠ Fin.last m) :
    swapAt (m + 1) (Fin.last m) (stdF (K := K) (n := m + 1) i) =
      stdF (K := K) (n := m + 1) i := by
  ext p
  cases p with
  | inl j =>
    simp only [swapAt_inl]
    split_ifs with hj
    · subst hj
      simp [stdF, Pi.single_eq_of_ne, hi]
    · rfl
  | inr j =>
    simp only [swapAt_inr]
    split_ifs with hj
    · subst hj
      simp [stdF, Pi.single_eq_of_ne, hi]
    · rfl

omit [Finite K] [CharP K 2] in
theorem swapAt_stdF_last :
    swapAt (m + 1) (Fin.last m) (stdF (K := K) (n := m + 1) (Fin.last m)) =
      stdE (K := K) (n := m + 1) (Fin.last m) := by
  ext p
  cases p with
  | inl j =>
    simp only [swapAt_inl]
    by_cases hj : j = Fin.last m
    · subst hj
      simp [stdE, stdF]
    · simp [stdE, stdF, Pi.single_eq_of_ne, hj]
  | inr j =>
    simp only [swapAt_inr]
    by_cases hj : j = Fin.last m
    · subst hj
      simp [stdE, stdF]
    · have hji : j ≠ Fin.last m := hj
      simp [stdF, Pi.single_eq_of_ne, hj]

omit [Finite K] [CharP K 2] in
private theorem map_span_eq_of_forall {V : Type*} [AddCommGroup V] [Module K V]
    {S : Set V} {L : V →ₗ[K] V} (h : ∀ v ∈ S, L v = v) :
    (Submodule.span K S).map L = Submodule.span K S := by
  have hfix : ∀ u ∈ Submodule.span K S, L u = u := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul a x _ hx => rw [map_smul, hx]
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [hfix u hu]
    exact hu
  · intro hv
    exact ⟨v, hv, hfix v hv⟩

theorem stdDChamber_sub_map_swapAt {j : ℕ} (hj : j ≤ m) :
    ((stdDChamber (unitaryInvolution K 2 f) (m + 1)).sub j).map
        (swapAt (m + 1) (Fin.last m)) =
      (stdDChamber (unitaryInvolution K 2 f) (m + 1)).sub j := by
  rw [stdDChamber_sub_eq_span]
  refine map_span_eq_of_forall ?_
  rintro v ⟨i, hi, rfl⟩
  refine swapAt_stdE_of_ne ?_
  intro hlast
  have hval : (i : ℕ) = m := by simpa using congrArg Fin.val hlast
  have hi' : (i : ℕ) < j := hi
  rw [hval] at hi'
  omega

theorem stdDChamber_sub_succ_eq {j : ℕ} (hj : j ≤ m) :
    (stdDChamber (unitaryInvolution K 2 f) (m + 1)).sub (j + 1) =
      (stdDChamber (unitaryInvolution K 2 f) (m + 1)).sub j ⊔
        K ∙ stdE (K := K) (n := m + 1) ⟨j, by omega⟩ := by
  rw [stdDChamber_sub_eq_span, stdDChamber_sub_eq_span, ← Submodule.span_union]
  congr 1
  ext v
  simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases hij : (i : ℕ) < j
    · exact Or.inl ⟨i, hij, rfl⟩
    · right
      have hval : (i : ℕ) = j := by omega
      exact congrArg (stdE (K := K) (n := m + 1))
        (Fin.ext hval : i = ⟨j, by omega⟩)
  · rintro (⟨i, hi, rfl⟩ | rfl)
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨⟨j, by omega⟩, by simp, rfl⟩

theorem stdDChamber_alt_map_swapAt :
    ((stdDChamber (unitaryInvolution K 2 f) (m + 1)).alt).map
        (swapAt (m + 1) (Fin.last m)) =
      (stdDChamber (unitaryInvolution K 2 f) (m + 1)).sub (m + 1) := by
  rw [stdDChamber_alt_eq, Submodule.map_sup, stdDChamber_sub_map_swapAt le_rfl,
    Submodule.map_span, Set.image_singleton, swapAt_stdF_last]
  have h : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
  rw [← h, ← stdDChamber_sub_succ_eq le_rfl]

theorem stdDChamber_sub_last_map_swapAt :
    ((stdDChamber (unitaryInvolution K 2 f) (m + 1)).sub (m + 1)).map
        (swapAt (m + 1) (Fin.last m)) =
      (stdDChamber (unitaryInvolution K 2 f) (m + 1)).alt := by
  rw [stdDChamber_sub_succ_eq le_rfl, Submodule.map_sup,
    stdDChamber_sub_map_swapAt le_rfl, Submodule.map_span, Set.image_singleton]
  have h : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
  rw [h, swapAt_stdE_last, ← stdDChamber_alt_eq]

theorem map_bc_tauAt_elt (hm : 3 ≤ m) (j : Fin (m + 1)) :
    ((stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt j).map
        (bcLin E (m + 1) (tauAt E (Fin.last m) :
          (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
      (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt
        (Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 1)) (Fin.last m) j) := by
  have ha_last : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  have ha_succ : ((⟨m - 1, by omega⟩ : Fin (m + 1)) : ℕ) + 1 = m := by
    simp only []
    omega
  rw [bcLin_tauAt]
  by_cases hjlast : j = Fin.last m
  · subst hjlast
    rw [stdDChamber_elt_last, stdDChamber_sub_last_map_swapAt,
      Equiv.swap_apply_right]
    exact (stdDChamber_elt_eq_alt ha_last ha_succ).symm
  · by_cases hja : j = (⟨m - 1, by omega⟩ : Fin (m + 1))
    · subst hja
      rw [stdDChamber_elt_eq_alt ha_last ha_succ,
        stdDChamber_alt_map_swapAt, Equiv.swap_apply_left,
        stdDChamber_elt_last]
    · have hj' : (j : ℕ) + 1 ≠ m := by
        intro h
        apply hja
        ext
        have := j.isLt
        simp only []
        omega
      have hjlt : (j : ℕ) ≤ m - 1 := by
        have hne : (j : ℕ) ≠ m := fun h => hjlast (Fin.ext (by simpa using h))
        have := j.isLt
        omega
      rw [stdDChamber_elt_eq_sub hjlast hj',
        stdDChamber_sub_map_swapAt (by omega),
        Equiv.swap_apply_of_ne_of_ne]
      · exact (stdDChamber_elt_eq_sub hjlast hj').symm
      · intro h
        exact hja h
      · exact hjlast

theorem stdDChamber_elt_last_eq_stdLag :
    (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt (Fin.last m) =
      stdLag (m + 1) K := by
  rw [stdDChamber_elt_last, stdDChamber_sub_eq_span]
  rw [show {i : Fin (m + 1) | (i : ℕ) < m + 1} = Set.univ by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact i.isLt]
  rw [Set.image_univ]
  exact (stdLag_eq_span_stdE (m + 1)).symm

theorem isKLinear_of_mem_panelStab (i : Fin (m + 1)) (hi : i ≠ Fin.last m)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
    (hg : g ∈ panelStab E i) :
    ∀ (a : K) x, (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (a • x) =
      a • (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) x := by
  rw [mem_panelStab] at hg
  have hlast : ((stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt (Fin.last m)).map
      (bcLin E (m + 1) (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) =
      (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt (Fin.last m) :=
    hg (Fin.last m) (Ne.symm hi)
  rw [stdDChamber_elt_last_eq_stdLag] at hlast
  exact (map_stdLag_bcLin_le_iff E (m + 1)
    (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))).mp (le_of_eq hlast)

theorem suEndN_mem_orthDerived (hn : 4 ≤ m + 1)
    (s : SUid (unitaryInvolution K 2 f) (m + 1)) :
    suEndN (F := F) (unitaryInvolution K 2 f) (m + 1) s ∈
      CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)) := by
  rw [← rulingGroup_eq_orthDerived E hn]
  refine mem_rulingGroup_of_map_stdLag E (m + 1)
    (suEndN_mem_orthogonalGroup E (m + 1) s) ?_
  have hle : (stdLag (m + 1) K).map
      (bcLin E (m + 1) (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1) s :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) ≤ stdLag (m + 1) K := by
    rw [stdLag_eq_span_stdE, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro v ⟨i, ⟨k, rfl⟩, rfl⟩
    have h := bcLin_stdLag_of_isKLinear E (m + 1)
      (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1) s :
        (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) (fun a x => by
      change suEndN (F := F) (unitaryInvolution K 2 f) (m + 1) s (a • x) =
        a • suEndN (F := F) (unitaryInvolution K 2 f) (m + 1) s x
      rw [suEndN_apply, suEndN_apply]
      rw [CFSG.ClassicalGroups.Unitary.smul_def, CFSG.ClassicalGroups.Unitary.smul_def]
      exact Matrix.mulVec_smul _ _ _)
      (Pi.single k (1 : K))
    rw [stdLag_eq_span_stdE] at h
    simpa [stdE] using h
  have hfin : Module.finrank K
      ↥((stdLag (m + 1) K).map
        (bcLin E (m + 1) (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1) s :
          (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)))) =
      Module.finrank K ↥(stdLag (m + 1) K) := by
    rw [bcLin_eq_coe_bc]
    exact LinearEquiv.finrank_map_eq
      (bc E (m + 1) (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1) s))
      (stdLag (m + 1) K)
  exact Submodule.eq_of_le_of_finrank_eq hle hfin

noncomputable def suEndNΩ (hn : 4 ≤ m + 1) :
    SUid (unitaryInvolution K 2 f) (m + 1) →*
      ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) where
  toFun s := ⟨suEndN (F := F) (unitaryInvolution K 2 f) (m + 1) s,
    suEndN_mem_orthDerived E hn s⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' s t := Subtype.ext (map_mul _ s t)

structure IsStdDFamily {M : CoxeterMatrix (Fin (m + 1))} (hm : 3 ≤ m)
    (S : PhanFamilyE K 2 f M
      ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) : Prop where
  ι_castSucc : ∀ (k : Fin m) (A : Su K 2 f 2),
    ((S.ι k.castSucc A :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      stdChainIota (F := F) (f := f) m k A
  ι_last : ∀ A : Su K 2 f 2,
    ((S.ι (Fin.last m) A :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) = stdForkIota E m hm A
  torus_eq : S.torus = (diagTorusV F (unitaryInvolution K 2 f) (m + 1)).subgroupOf
    (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))

theorem isStdDFamily_stdFamilyΩ (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    IsStdDFamily E hm (stdFamilyΩ E m hm hK hq) where
  ι_castSucc k A := by
    have h := DFunLike.congr_fun
      (coe_stdFamilyΩ_ι (E := E) m hm hK hq (Fin.castSucc k)) A
    exact h.trans (DFunLike.congr_fun (stdFamilyV_ι_castSucc (E := E) m hm k) A)
  ι_last A := by
    have h := DFunLike.congr_fun
      (coe_stdFamilyΩ_ι (E := E) m hm hK hq (Fin.last m)) A
    exact h.trans (DFunLike.congr_fun (stdFamilyV_ι_last (E := E) m hm) A)
  torus_eq := by
    have hmap : ((stdFamilyΩ E m hm hK hq).torus).map
        (Subgroup.subtype
          (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) =
        (stdFamilyV E m hm).torus := by
      rw [PhanFamilyE.torus, PhanFamilyE.torus, Subgroup.map_iSup]
      refine iSup_congr fun i => ?_
      rw [show (((stdFamilyΩ E m hm hK hq).nodeTor i).range.map
            (Subgroup.subtype
              (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))) =
          ((Subgroup.subtype
              (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))).comp
            ((stdFamilyΩ E m hm hK hq).nodeTor i)).range from
        (MonoidHom.range_comp _ _).symm]
      congr 1
    apply Subgroup.map_injective
      (f := (Subgroup.subtype
        (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))))
      (Subgroup.subtype_injective _)
    rw [hmap, torus_stdFamilyV E m hm hK,
      Subgroup.map_subgroupOf_eq_of_le
        (diagTorusV_le_orthDerived E (by omega : 4 ≤ m + 1))]

noncomputable def conjTau :
    ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) ≃*
      ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) := by
  classical
  let τ : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K) := tauAt E (Fin.last m)
  let O := TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))
  have hτO : τ ∈ O := tauAt_mem_orthogonalGroup E (Fin.last m)
  have hOmap : O.map (MulAut.conj τ).toMonoidHom = O := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      change τ * h * τ⁻¹ ∈ O
      exact O.mul_mem (O.mul_mem hτO hh) (O.inv_mem hτO)
    · intro hg
      refine ⟨τ⁻¹ * g * τ, ?_, ?_⟩
      · exact O.mul_mem (O.mul_mem (O.inv_mem hτO) hg) hτO
      · change τ * (τ⁻¹ * g * τ) * τ⁻¹ = g
        group
  have hmap : (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))).map
      (MulAut.conj τ).toMonoidHom =
      CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)) := by
    rw [CFSG.RankThree.Classical2.orthDerived, Subgroup.map_commutator, hOmap]
  exact (Subgroup.equivMapOfInjective
      (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))
      (MulAut.conj τ).toMonoidHom (MulAut.conj τ).injective).trans
    (MulEquiv.subgroupCongr hmap)

theorem coe_conjTau (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
    ((conjTau E g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      tauAt E (Fin.last m) * (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
        (tauAt E (Fin.last m))⁻¹ := by
  rfl

end CFSG.ClassicalInvolution.PhanDn

end
