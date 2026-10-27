module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6GInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KNoSLReduce

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

namespace EvenSL

theorem isSLThreeFour_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSLThreeFour Y) : IsSLThreeFour X := by
  obtain ⟨K, hF, hfin, hK, ⟨e'⟩⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨e.trans e'⟩⟩

theorem isLThreeFour_quot_center_of_isSLThreeFour {X : Type} [Group X] (h : IsSLThreeFour X) :
    IsLThreeFour (X ⧸ Subgroup.center X) := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  have e₁ : X ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
  exact ⟨F, inferInstance, inferInstance, hcard,
      ⟨(QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F)⟩⟩

theorem eq_bot_of_normal_isPGroup_two {X : Type} [Group X] [Finite X] (h : IsSLThreeFour X)
    (O : Subgroup X) [O.Normal] (hO : IsPGroup 2 O) : O = ⊥ := by
  have hL := isLThreeFour_quot_center_of_isSLThreeFour h
  obtain ⟨hs, -⟩ := isSimpleGroup_of_isLThreeFour hL
  have hc := card_lThreeFour hL
  have hO' : IsPGroup 2 (O.map (QuotientGroup.mk' (Subgroup.center X))) := hO.map _
  have hn : (O.map (QuotientGroup.mk' (Subgroup.center X))).Normal :=
    Subgroup.Normal.map ‹O.Normal› (QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective _)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hn with hb | ht
  · have hle : O ≤ Subgroup.center X := by
      intro x hx
      have : QuotientGroup.mk' (Subgroup.center X) x ∈
          O.map (QuotientGroup.mk' (Subgroup.center X)) := Subgroup.mem_map_of_mem _ hx
      rw [hb, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).1 this
    have h3 := card_center_slThreeFour h
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := hO ⟨x, hx⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hx3 : x ^ 3 = 1 := by
      have := pow_card_eq_one' (G := Subgroup.center X) (x := ⟨x, hle hx⟩)
      rw [h3] at this
      simpa using congrArg Subtype.val this
    have hg : Nat.gcd 3 (2 ^ k) = 1 :=
      Nat.Coprime.pow_right k (by norm_num)
    have := pow_gcd_eq_one.2 ⟨hx3, hk'⟩
    rwa [hg, pow_one] at this
  · exfalso
    rw [ht] at hO'
    obtain ⟨n, hn⟩ := hO'.exists_card_eq
    rw [Subgroup.card_top, hc] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

section Tri

variable {K : Type} [Field K]

@[expose] def tMat (a b c : K) : Matrix (Fin 3) (Fin 3) K := !![1, a, c; 0, 1, b; 0, 0, 1]

theorem tMat_mul (a b c a' b' c' : K) :
    tMat a b c * tMat a' b' c' = tMat (a + a') (b + b') (c + c' + a * b') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem tMat_zero : tMat (0 : K) 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMat]

@[expose] def tGL (a b c : K) : GL (Fin 3) K :=
  ⟨tMat a b c, tMat (-a) (-b) (a * b - c),
    by rw [tMat_mul]; convert tMat_zero (K := K) using 2 <;> ring,
    by rw [tMat_mul]; convert tMat_zero (K := K) using 2 <;> ring⟩

theorem tGL_mul (a b c a' b' c' : K) :
    tGL a b c * tGL a' b' c' = tGL (a + a') (b + b') (c + c' + a * b') :=
  Units.ext (tMat_mul a b c a' b' c')

theorem tGL_zero : tGL (0 : K) 0 0 = 1 := Units.ext tMat_zero

theorem tGL_mem (a b c : K) : tGL a b c ∈ CFSG.Open.StatedSL 3 K := by
  apply Subgroup.subset_closure
  show (tMat a b c).det = 1
  simp [tMat, Matrix.det_fin_three]

@[expose] def uniTri (K : Type) [Field K] : Subgroup (GL (Fin 3) K) where
  carrier := {g | ∃ a b c : K, g = tGL a b c}
  one_mem' := ⟨0, 0, 0, tGL_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨_, _, _, tGL_mul a b c a' b' c'⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    refine ⟨-a, -b, a * b - c, ?_⟩
    apply inv_eq_of_mul_eq_one_left
    rw [tGL_mul]
    convert tGL_zero (K := K) using 2 <;> ring

theorem pow_four_eq_one_of_mem_uniTri (h2 : (2 : K) = 0) {g : GL (Fin 3) K}
    (hg : g ∈ uniTri K) : g ^ 4 = 1 := by
  obtain ⟨a, b, c, rfl⟩ := hg
  have h22 : ∀ z : K, z + z = 0 := fun z => by rw [← two_mul, h2, zero_mul]
  have hsq : tGL a b c ^ 2 = tGL 0 0 (a * b) := by
    rw [pow_two, tGL_mul]
    congr 1
    · exact h22 a
    · exact h22 b
    · have : c + c = 0 := h22 c
      linear_combination this
  have : tGL a b c ^ 4 = (tGL a b c ^ 2) ^ 2 := by rw [← pow_mul]
  rw [this, hsq, pow_two, tGL_mul]
  convert tGL_zero (K := K) using 2
  · simp
  · simp
  · have := h22 (a * b)
    linear_combination this

theorem tGL_noncomm : tGL (1 : K) 0 0 * tGL 0 1 0 ≠ tGL 0 1 0 * tGL 1 0 0 := by
  rw [tGL_mul, tGL_mul]
  intro h
  have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 2) h
  simp [tGL, tMat] at this

end Tri

theorem exists_nonabelian_isPGroup_two {X : Type} [Group X] (h : IsSLThreeFour X) :
    ∃ A : Subgroup X, IsPGroup 2 A ∧ ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := h
  have h2 := NoSLReduce.two_eq_zero_of_card_four hK
  let A0 : Subgroup ↥(CFSG.Open.StatedSL 3 K) := (uniTri K).subgroupOf _
  refine ⟨A0.comap e.toMonoidHom, ?_, ?_⟩
  · intro g
    refine ⟨2, ?_⟩
    have hg : ((e g.1 : ↥(CFSG.Open.StatedSL 3 K)) : GL (Fin 3) K) ^ 4 = 1 :=
      pow_four_eq_one_of_mem_uniTri h2 g.2
    have hg4 : g.1 ^ 4 = 1 := by
      apply e.injective
      rw [map_pow, map_one]
      exact Subtype.ext (by simpa using hg)
    have h4 : g ^ 4 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hg4)
    simpa using h4
  · refine ⟨e.symm ⟨tGL 1 0 0, tGL_mem _ _ _⟩, ?_, e.symm ⟨tGL 0 1 0, tGL_mem _ _ _⟩, ?_, ?_⟩
    · show e (e.symm _) ∈ A0
      rw [MulEquiv.apply_symm_apply]
      exact ⟨1, 0, 0, rfl⟩
    · show e (e.symm _) ∈ A0
      rw [MulEquiv.apply_symm_apply]
      exact ⟨0, 1, 0, rfl⟩
    · intro hc
      have := congrArg e hc
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
      apply tGL_noncomm (K := K)
      exact congrArg Subtype.val this

end EvenSL

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
