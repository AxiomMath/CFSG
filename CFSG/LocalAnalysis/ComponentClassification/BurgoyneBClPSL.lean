module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieLBlocks
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieL2

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Cl

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.Burgoyne.PSL (coordBlock slCentralizer mem_slCentralizer signGL
  coe_signGL coordBlock_le_slCentralizer normalizes_coordBlock exists_split_normal_form
  exists_quad_normal_form even_of_sq_eq_nonsquare quadMat quadGL blockSLE blockRep
  blockRep_commute_quadMat exists_blockRep_of_commute blockRep_injective QuadExt
  range_blockSLE_le)
open CFSG.ComponentClassification.CatLeafProof.EndOddLin
open scoped MatrixGroups commutatorElement

variable {n : ℕ} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem fixOf_slConjugation (A : GL (Fin n) K) :
    fixOf (slConjugation n K A).toMonoidHom = slCentralizer A := by
  ext g
  rw [mem_slCentralizer]
  change (slConjugation n K A g = g) ↔ _
  have hAA : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAA' : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  constructor
  · intro h
    have h1 := congrArg (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) h
    simp only [coe_slConjugation] at h1
    calc (g : Matrix (Fin n) (Fin n) K) * A =
        (A : Matrix (Fin n) (Fin n) K) * g * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          A := by rw [h1]
      _ = A * g := by rw [Matrix.mul_assoc, hAA, Matrix.mul_one]
  · intro h
    apply Subtype.ext
    change ((slConjugation n K A g : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = g
    rw [coe_slConjugation, ← h, Matrix.mul_assoc, hAA', Matrix.mul_one]

omit [Finite K] in
theorem conjAut_lift (A : GL (Fin n) K) (g : SpecialLinearGroup (Fin n) K) :
    conjAut n K A (g : projectiveSL n K) =
      ((slConjugation n K A).toMonoidHom g : projectiveSL n K) :=
  conjAut_proj A g

theorem noL2At_conj_signGL (hK : ringChar K ≠ 2) {J : Finset (Fin n)} {a b : Fin n}
    (ha : a ∈ J) (hb : b ∉ J) : NoL2At (conjAut n K (signGL K J)) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hZ := scalars_le_center n K
  have hw := conjAut_lift (n := n) (K := K) (signGL K J)
  have hfix := fixOf_slConjugation (n := n) (K := K) (signGL K J)
  have hle : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) →
      coordBlock K I ≤ fixOf (slConjugation n K (signGL K J)).toMonoidHom := fun hI => by
    rw [hfix]
    exact coordBlock_le_slCentralizer h2 hI
  have hn : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) →
      ∀ B ∈ fixOf (slConjugation n K (signGL K J)).toMonoidHom, ∀ m ∈ coordBlock K I,
        B * m * B⁻¹ ∈ coordBlock K I := fun hI B hB m hm => by
    rw [hfix] at hB
    exact normalizes_coordBlock h2 hI B hB m hm
  have haJ : a ∉ Jᶜ := by simpa using ha
  refine noL2At_of_blocks (map_fix_le_autFixed hZ hw (hle (Or.inl rfl)))
    (map_fix_le_autFixed hZ hw (hle (Or.inr rfl))) (isSubnormal_map_of_fix hZ hw
      (hle (Or.inl rfl)) (hn (Or.inl rfl))) (isSubnormal_map_of_fix hZ hw (hle (Or.inr rfl))
      (hn (Or.inr rfl))) (fun L hL hp => ?_) (quatBlock_coordBlock hK hb)
    (quatBlock_coordBlock hK haJ)
  refine (le_map_commutator_fix_of_perfect hZ hw hL hp).trans ?_
  rw [hfix, ← Subgroup.map_sup]
  exact map_mono (C.commutator_slCentralizer_le h2 J)

variable {l : K} {m : ℕ}

theorem commutator_quadCentralizer_le (hl : ¬ IsSquare l) (hm : 2 ≤ m) :
    ⁅slCentralizer (quadGL l m hl), slCentralizer (quadGL l m hl)⁆ ≤ (blockSLE hl hm).range := by
  have hcent : ∀ {g : SpecialLinearGroup (Fin (m * 2)) K},
      g ∈ slCentralizer (quadGL l m hl) ↔
        (g : Matrix (Fin (m * 2)) (Fin (m * 2)) K) * quadMat l m = quadMat l m * g := by
    intro g
    rw [mem_slCentralizer]
    rfl
  rw [commutator_le]
  intro g hg h hh
  have hY : ∀ {u : SpecialLinearGroup (Fin (m * 2)) K}, u ∈ slCentralizer (quadGL l m hl) →
      ∃ Y : Matrix (Fin m) (Fin m) (QuadExt l),
        blockRep l m Y = (u : Matrix (Fin (m * 2)) (Fin (m * 2)) K) :=
    fun hu => exists_blockRep_of_commute (hcent.1 hu)
  obtain ⟨Y₁, hY₁⟩ := hY hg
  obtain ⟨Y₂, hY₂⟩ := hY hh
  obtain ⟨Y₃, hY₃⟩ := hY (inv_mem hg)
  obtain ⟨Y₄, hY₄⟩ := hY (inv_mem hh)
  have hinv : ∀ {u : SpecialLinearGroup (Fin (m * 2)) K} {Y Y' : Matrix (Fin m) (Fin m)
      (QuadExt l)}, blockRep l m Y = (u : Matrix _ _ K) →
      blockRep l m Y' = ((u⁻¹ : SpecialLinearGroup (Fin (m * 2)) K) : Matrix _ _ K) →
      Y * Y' = 1 := by
    intro u Y Y' hYu hY'u
    apply blockRep_injective hl
    rw [map_mul, hYu, hY'u, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, map_one]
  have h13 := hinv hY₁ hY₃
  have h24 := hinv hY₂ hY₄
  have hdet : (Y₁ * Y₂ * Y₃ * Y₄).det = 1 := by
    have e1 : Y₁.det * Y₃.det = 1 := by rw [← det_mul, h13, det_one]
    have e2 : Y₂.det * Y₄.det = 1 := by rw [← det_mul, h24, det_one]
    rw [det_mul, det_mul, det_mul]
    calc _ = (Y₁.det * Y₃.det) * (Y₂.det * Y₄.det) := by ring
      _ = 1 := by rw [e1, e2, mul_one]
  refine ⟨⟨_, hdet⟩, Subtype.ext ?_⟩
  change blockRep l m (Y₁ * Y₂ * Y₃ * Y₄) =
    ((⁅g, h⁆ : SpecialLinearGroup (Fin (m * 2)) K) : Matrix (Fin (m * 2)) (Fin (m * 2)) K)
  rw [commutatorElement_def, map_mul, map_mul, map_mul, hY₁, hY₂, hY₃, hY₄]
  rfl

theorem noL2At_conj_quad (hK : ringChar K ≠ 2) (hl : ¬ IsSquare l) (hm3 : 3 ≤ m) :
    NoL2At (conjAut (m * 2) K (quadGL l m hl)) := by
  have hm : 2 ≤ m := by omega
  have hZ := scalars_le_center (m * 2) K
  have hw := conjAut_lift (n := m * 2) (K := K) (quadGL l m hl)
  have hfix := fixOf_slConjugation (n := m * 2) (K := K) (quadGL l m hl)
  have hF : (blockSLE hl hm).range ≤
      fixOf (slConjugation (m * 2) K (quadGL l m hl)).toMonoidHom := by
    rw [hfix]
    exact range_blockSLE_le hl hm
  refine noL2At_of_layer (map_fix_le_autFixed hZ hw hF) (fun L hL hp => ?_)
    (quatBlock_blockSLE hK hl hm hm3)
  refine (le_map_commutator_fix_of_perfect hZ hw hL hp).trans ?_
  rw [hfix]
  exact map_mono (commutator_quadCentralizer_le hl hm)

theorem noL2At_conjAut (hK : ringChar K ≠ 2) (hn : 6 ≤ n) {A : GL (Fin n) K}
    (hA : orderOf (conjAut n K A) = 2) : NoL2At (conjAut n K A) := by
  have hsc : ∀ (c : Kˣ) (Z : GL (Fin n) K), Commute (GeneralLinearGroup.scalar (Fin n) c) Z :=
    fun c Z => by
      ext i j
      simp [GeneralLinearGroup.scalar, mul_comm]
  have hA2 : conjAut n K (A * A) * fieldAut n K 1 = 1 := by
    rw [map_one, mul_one, map_mul, ← pow_two, ← hA, pow_orderOf_eq_one]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by omega) _ 1 hA2
  have hns : ∀ c : Kˣ, A ≠ GeneralLinearGroup.scalar (Fin n) c := by
    intro c' hc'
    rw [hc', conjAut_scalar, orderOf_one] at hA
    exact absurd hA (by norm_num)
  by_cases hsq : IsSquare (c : K)
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact c.ne_zero (by rw [hr, mul_zero])
    set μ := Units.mk0 r hr0
    have hAμ : A * A = GeneralLinearGroup.scalar (Fin n) (μ * μ) := by
      rw [← hc]
      congr 1
      exact Units.ext hr
    obtain ⟨H, J, a, b, ha, hb, hH⟩ := exists_split_normal_form hK hAμ hns
    refine NoL2At.of_conj (conjAut n K H) ?_
    have e : conjAut n K H * conjAut n K A * (conjAut n K H)⁻¹ = conjAut n K (signGL K J) := by
      rw [← map_inv, ← map_mul, ← map_mul, hH, map_mul, conjAut_scalar, one_mul]
    rw [e]
    exact noL2At_conj_signGL hK ha hb
  · have hev := even_of_sq_eq_nonsquare hc.symm hsq
    obtain ⟨m, rfl⟩ : ∃ m, n = m * 2 := ⟨n / 2, by obtain ⟨k, hk⟩ := hev; omega⟩
    have hm3 : 3 ≤ m := by omega
    have hAm : (A : Matrix (Fin (m * 2)) (Fin (m * 2)) K) * A = (c : K) • 1 := by
      have := congrArg Units.val hc
      rw [Units.val_mul] at this
      rw [← this]
      ext i j
      simp [GeneralLinearGroup.scalar, Matrix.smul_apply, one_apply, diagonal_apply]
    obtain ⟨H, hH⟩ := exists_quad_normal_form hsq hAm
    have hHGL : H * A * H⁻¹ = quadGL (c : K) m hsq := Units.ext hH
    refine NoL2At.of_conj (conjAut (m * 2) K H) ?_
    have e : conjAut (m * 2) K H * conjAut (m * 2) K A * (conjAut (m * 2) K H)⁻¹ =
        conjAut (m * 2) K (quadGL (c : K) m hsq) := by
      rw [← map_inv, ← map_mul, ← map_mul, hHGL]
    rw [e]
    exact noL2At_conj_quad hK hsq hm3

end CFSG.ComponentClassification.Burgoyne.Cl
