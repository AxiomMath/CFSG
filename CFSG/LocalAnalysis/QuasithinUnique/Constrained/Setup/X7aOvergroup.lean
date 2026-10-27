module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBorelOvergroups
public import CFSG.LinearAlgebra.LinearGroups.Generation

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Linear

variable {K : Type*} [Field K] {n : ℕ}

theorem reduced_word_extraction_unitriangular (A : Subgroup (SpecialLinearGroup (Fin n) K))
    (hU : unitriangular n K ≤ A) :
    ∀ (l : List ℕ) (w : Equiv.Perm (Fin n)) (z : SpecialLinearGroup (Fin n) K), z ∈ A →
      IsMonomial (z : Matrix (Fin n) (Fin n) K) w → IsReducedWord w l →
        ∀ i ∈ l, ∀ (hi : 1 ≤ i) (hin : i < n), reflection n K i hi hin ∈ A := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _ i hi; exact absurd hi List.not_mem_nil
  | cons i l ih =>
    intro w z hzA hzm hred
    obtain ⟨hi, hin, hdesc, hred'⟩ := (symmetric_group_descents w).2.2 i l hred
    set x : Fin n := ⟨i - 1, by omega⟩ with hx
    set y : Fin n := ⟨i, hin⟩ with hy
    have hxy : x < y := by rw [Fin.lt_def]; simp [hx, hy]; omega
    have hri : reflection n K i hi hin ∈ A := by
      rw [(monomial_root_transport (K := K) (n := n)).2.2 i hi hin]
      obtain ⟨c, hc⟩ := hzm
      set a := w⁻¹ y
      set b := w⁻¹ x
      have hab : a < b := hdesc
      have hwa : w a = y := perm_apply_inv w y
      have hwb : w b = x := perm_apply_inv w x
      have hlow : SpecialLinearGroup.transvection (i := y) (j := x) hxy.ne' 1 ∈ A := by
        have h1 := mul_mem (mul_mem hzA (hU (transvection_mem_unitriangular hab
          ((c b : K) * (c a : K)⁻¹)))) (inv_mem hzA)
        rw [monomial_conj_transvection (M := z) hc hab.ne] at h1
        convert h1 using 1
        apply Subtype.ext
        simp only [SpecialLinearGroup.transvection_coe, hwa, hwb]
        congr 1
        field_simp [(c a).ne_zero, (c b).ne_zero]
      exact mul_mem (mul_mem (hU (transvection_mem_unitriangular hxy (-1))) hlow)
        (hU (transvection_mem_unitriangular hxy (-1)))
    have hmono : IsMonomial (((reflection n K i hi hin)⁻¹ * z : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) (adjSwap n i * w) := by
      rw [SpecialLinearGroup.coe_mul, ← adjSwap_inv]
      exact (IsMonomial.inv (isMonomial_reflection (K := K) i hi hin)).mul hzm
    intro j hj hj1 hjn
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hri
    · exact ih _ _ (mul_mem (inv_mem hri) hzA) hmono hred' j hj hj1 hjn

theorem isMonomial_of_isDiag {d : SpecialLinearGroup (Fin n) K}
    (hd : Matrix.IsDiag (d : Matrix (Fin n) (Fin n) K)) :
    IsMonomial (d : Matrix (Fin n) (Fin n) K) 1 := by
  have hne : ∀ i, (d : Matrix (Fin n) (Fin n) K) i i ≠ 0 := by
    intro i h
    have hdet : (d : Matrix (Fin n) (Fin n) K).det = 1 := d.2
    have h1 : (d : Matrix (Fin n) (Fin n) K).det = ∏ j, (d : Matrix (Fin n) (Fin n) K) j j := by
      conv_lhs => rw [← hd.diagonal_diag]
      exact det_diagonal
    rw [h1, Finset.prod_eq_zero (f := fun j => (d : Matrix (Fin n) (Fin n) K) j j)
      (Finset.mem_univ i) h] at hdet
    exact zero_ne_one hdet
  refine ⟨fun j => Units.mk0 _ (hne j), fun j => ?_⟩
  ext a
  simp only [mulVec_single_one, col_apply, Equiv.Perm.one_apply, Units.val_mk0, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul]
  by_cases h : a = j
  · subst h; simp
  · have := hd h
    simp [h, this]

theorem exists_unitriangular_mul_diagonal {b : SpecialLinearGroup (Fin n) K}
    (hb : b ∈ upperTriangular n K) :
    ∃ u ∈ unitriangular n K, ∃ d : SpecialLinearGroup (Fin n) K,
      Matrix.IsDiag (d : Matrix (Fin n) (Fin n) K) ∧ b = u * d := by
  have hb' : (b : Matrix (Fin n) (Fin n) K).IsUpperTriangular := fun _ _ h => hb _ _ h
  have hdet : (diagonal (fun i => (b : Matrix (Fin n) (Fin n) K) i i)).det = 1 := by
    rw [det_diagonal, ← det_of_isUpperTriangular hb']
    exact b.2
  set d : SpecialLinearGroup (Fin n) K := ⟨_, hdet⟩ with hd
  have hdcoe : (d : Matrix (Fin n) (Fin n) K) =
      diagonal (fun i => (b : Matrix (Fin n) (Fin n) K) i i) := rfl
  have hdB : d ∈ upperTriangular n K := fun i j hij => by
    rw [hdcoe, diagonal_apply_ne _ (ne_of_gt hij)]
  have hd' : (d : Matrix (Fin n) (Fin n) K).IsUpperTriangular := fun _ _ h => hdB _ _ h
  refine ⟨b * d⁻¹, ⟨(upperTriangular n K).mul_mem hb ((upperTriangular n K).inv_mem hdB), fun i => ?_⟩,
    d, ?_, (inv_mul_cancel_right b d).symm⟩
  · have h1 := coe_inv_apply_self_of_isUpperTriangular hd' i
    rw [SpecialLinearGroup.coe_mul, mul_apply_self_of_isUpperTriangular hb'
      (coe_inv_isUpperTriangular hd') i]
    rw [hdcoe, diagonal_apply_eq] at h1
    exact h1
  · rw [hdcoe]
    exact isDiag_diagonal _

theorem le_flagStabilizer_borelOvergroupCuts (M : Subgroup (SpecialLinearGroup (Fin n) K))
    (hU : unitriangular n K ≤ M) : M ≤ flagStabilizer n K (borelOvergroupCuts M) := by
  classical
  set I := borelOvergroupCuts M with hIdef
  have hmem := (subflag_stabilizer_generation (K := K) (n := n) I).2.2
  intro g hg
  obtain ⟨w, hw⟩ := (triangular_bruhat (K := K) (n := n)).1 g
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.mp hw
  obtain ⟨u₁, hu₁, d₁, hd₁, rfl⟩ := exists_unitriangular_mul_diagonal hb₁
  obtain ⟨u', hu', d', hd', hb₂'⟩ :=
    exists_unitriangular_mul_diagonal ((upperTriangular n K).inv_mem hb₂)
  have hb₂eq : b₂ = d'⁻¹ * u'⁻¹ := by
    rw [← _root_.mul_inv_rev, ← hb₂', inv_inv]
  set z : SpecialLinearGroup (Fin n) K := d₁ * signedPermutation n K w * d'⁻¹ with hz
  have hzM : z ∈ M := by
    have h1 : z = u₁⁻¹ * (u₁ * d₁ * signedPermutation n K w * b₂) * u' := by
      rw [hb₂eq, hz]; group
    rw [h1]
    exact mul_mem (mul_mem (inv_mem (hU hu₁)) hg) (hU hu')
  have hzmono : IsMonomial (z : Matrix (Fin n) (Fin n) K) w := by
    have h1 := (((isMonomial_of_isDiag hd₁).mul (isMonomial_signedPermMatrix (K := K) w)).mul
      (isMonomial_of_isDiag hd').inv)
    rw [hz, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_signedPermutation]
    simpa using h1
  obtain ⟨l, hl⟩ := exists_isReducedWord w
  have hletters := reduced_word_extraction_unitriangular M hU l w z hzM hzmono hl
  set ρ := (l.map (reflElt n K)).prod with hρ
  have hρmem : ρ ∈ flagStabilizer n K I := by
    rw [hρ]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hj1, hjn⟩ := hl.1 j hj
    rw [reflElt_of_lt hj1 hjn]
    refine (hmem j hj1 hjn).mpr fun hjI => ?_
    obtain ⟨_, _, hnot⟩ := hjI
    exact hnot (hletters j hj hj1 hjn)
  have hρmono := isMonomial_prod_reflElt (K := K) (n := n) l
  rw [hl.2.1] at hρmono
  obtain ⟨D, hD, hzD⟩ := IsMonomial.exists_diagonal (M := z) (M' := ρ) hzmono hρmono
  have hBI := upperTriangular_le_flagStabilizer (K := K) (n := n) I
  have hUI : ∀ u ∈ unitriangular n K, u ∈ flagStabilizer n K I := fun u hu =>
    hBI (unitriangular_le_upperTriangular n K hu)
  have hgz : u₁ * d₁ * signedPermutation n K w * b₂ = u₁ * z * u'⁻¹ := by
    rw [hb₂eq, hz]; group
  rw [hgz, hzD]
  exact mul_mem (mul_mem (hUI _ hu₁) (mul_mem hρmem (hBI hD))) ((flagStabilizer n K I).inv_mem
    (hUI _ hu'))

theorem eq_top_of_borelOvergroupCuts_eq_empty (M : Subgroup (SpecialLinearGroup (Fin n) K))
    (hU : unitriangular n K ≤ M) (h : borelOvergroupCuts M = ∅) : M = ⊤ := by
  classical
  have hr : ∀ (i : ℕ) (hi : 1 ≤ i) (hin : i < n), reflection n K i hi hin ∈ M := by
    intro i hi hin
    by_contra hnot
    have : i ∈ borelOvergroupCuts M := ⟨hi, hin, hnot⟩
    rw [h] at this
    exact this
  have hperm : ∀ w : Equiv.Perm (Fin n), ∃ z ∈ M, IsMonomial (z : Matrix (Fin n) (Fin n) K) w := by
    intro w
    obtain ⟨l, hl⟩ := exists_isReducedWord w
    refine ⟨(l.map (reflElt n K)).prod, ?_, ?_⟩
    · refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      obtain ⟨hj1, hjn⟩ := hl.1 j hj
      rw [reflElt_of_lt hj1 hjn]
      exact hr j hj1 hjn
    · have := isMonomial_prod_reflElt (K := K) (n := n) l
      rwa [hl.2.1] at this
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := n) (K := K),
    Subgroup.closure_le]
  rintro _ ⟨a, b, hab, t, rfl⟩
  rcases lt_or_gt_of_ne hab with h | h
  · exact hU (transvection_mem_unitriangular h t)
  · obtain ⟨z, hzM, c, hc⟩ := hperm (Equiv.swap b a)
    have hwb : (Equiv.swap b a) b = a := Equiv.swap_apply_left b a
    have hwa : (Equiv.swap b a) a = b := Equiv.swap_apply_right b a
    have h1 := mul_mem (mul_mem hzM (hU (transvection_mem_unitriangular h
      ((c a : K) * (c b : K)⁻¹ * t)))) (inv_mem hzM)
    rw [monomial_conj_transvection (M := z) hc h.ne] at h1
    change SpecialLinearGroup.transvection hab t ∈ M
    convert h1 using 1
    apply Subtype.ext
    simp only [SpecialLinearGroup.transvection_coe, hwa, hwb]
    congr 2
    field_simp [(c a).ne_zero, (c b).ne_zero]

theorem linear_unitriangular_overgroup_subflag_containment :
    (∀ M : Subgroup (SpecialLinearGroup (Fin n) K), unitriangular n K ≤ M →
      M ≤ flagStabilizer n K (borelOvergroupCuts M) ∧ (borelOvergroupCuts M = ∅ ↔ M = ⊤)) ∧
    ∀ A : Subgroup (projectiveSL n K), A ≠ ⊤ → projUnitriangular n K ≤ A →
      ∃ i : ℕ, 1 ≤ i ∧ i < n ∧ A ≤ projStabilizer (flagSpace n K i) := by
  classical
  refine ⟨fun M hU => ⟨le_flagStabilizer_borelOvergroupCuts M hU,
    ⟨eq_top_of_borelOvergroupCuts_eq_empty M hU, fun hM => ?_⟩⟩, fun A hA hU => ?_⟩
  · refine Set.eq_empty_of_forall_notMem fun i hi => ?_
    obtain ⟨hi1, hin, hnot⟩ := hi
    exact hnot (hM ▸ Subgroup.mem_top _)
  · set M := A.comap (proj n K) with hM
    have hUM : unitriangular n K ≤ M := fun u hu =>
      hU (Subgroup.mem_map_of_mem _ hu)
    have hMtop : M ≠ ⊤ := by
      intro hMt
      apply hA
      rw [eq_top_iff]
      intro p _
      obtain ⟨g, rfl⟩ := proj_surjective n K p
      have : g ∈ M := hMt ▸ Subgroup.mem_top g
      exact this
    have hne : borelOvergroupCuts M ≠ ∅ := fun he => hMtop (eq_top_of_borelOvergroupCuts_eq_empty M hUM he)
    obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨hi1, hin, hrnot⟩ := hi
    refine ⟨i, hi1, hin, fun p hp => ?_⟩
    obtain ⟨g, rfl⟩ := proj_surjective n K p
    have hgM : g ∈ M := hp
    have hgQ := le_flagStabilizer_borelOvergroupCuts M hUM hgM
    exact ⟨g, mem_flagStabilizer.mp hgQ i ⟨hi1, hin, hrnot⟩, rfl⟩

end Linear

end CFSG.QuasithinUnique.Setup.X7a
