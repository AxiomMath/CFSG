module

public import CFSG.ClassicalInvolution.Q3.TL4MF163L3Y
public import CFSG.ClassicalInvolution.Q3.TL4ExitDichA
public import CFSG.ClassicalInvolution.Q3.TL4MF163L3C
public import CFSG.ClassicalInvolution.Q3.TL4MF163L3G
public import CFSG.ClassicalInvolution.Q3.TL4MF163L3X

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF163.L3

open CFSG CFSG.Open CFSG.ClassicalInvolution Matrix QuaternionGroup
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3
open CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] [Finite K]

theorem concl163Syl_of_psl3 {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R}
    {z : X}
    (hm : EdgelessMember3 R S z) [IsSimpleGroup ↥(genFittingFStar X)] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    (e : ↥(genFittingFStar X) ≃* projectiveSL 3 K) : Concl163Syl R S z := by
  set N := genFittingFStar X with hNdef
  have hNn : N.Normal := genFittingFStar_normal X
  have hD := hm.datum
  have hoddK : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card K := by omega
  have h2 : (2 : K) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero K hoddK
  have hnab : ∃ a b : N, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_noncomm (K := K)
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hC : Subgroup.centralizer (N : Set X) = ⊥ := centralizer_genFittingFStar_eq_bot hnab
  have hZP : Subgroup.center (projectiveSL 3 K) = ⊥ := center_eq_bot_of_equiv hnab e
  obtain ⟨ιq, hιq, hιqS, hιqz⟩ := exists_quat_of_member_syl hm
  have hιqK : ∀ q, ιq q ∈ tightCore R := fun q => sylow_le_tightCore S (hιqS q)
  have hιqR : ∀ q, ιq q ∈ R := fun q => tightCore_le R (hιqK q)
  have hq4 : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
  have hzN : z ∈ N := by
    have hq : (a 1 : QuaternionGroup 2) * xa 0 * (a 1)⁻¹ * (xa 0)⁻¹ = a 2 := by decide
    have hz' : z = ιq (a 1) * ιq (xa 0) * (ιq (a 1))⁻¹ * (ιq (xa 0))⁻¹ := by
      rw [← hιqz, ← hq, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hD' : MulAut.congr e (MulAut.conjNormal z) ∈ linearAutGroup 3 K := by
      rw [hz', map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv,
        map_inv]
      exact commutator_mem_linearAutGroup le_rfl _ _
    have hz2 : MulAut.congr e (MulAut.conjNormal z) ^ 2 ^ 1 = 1 := by
      rw [pow_one, ← map_pow, ← map_pow, ← hD.order, pow_orderOf_eq_one, map_one, map_one]
    exact mem_of_congr_mem_inner hC e (mem_inner_of_pow hD' hz2)
  obtain ⟨Q, π, hrange, hk, hπ1, hπ⟩ := exists_frame hoddK e hzN hD.order
  let e' : ↥N ≃* projectiveSL 3 K := e.trans (conjAut 3 K Q)⁻¹
  have hπN : ∀ A, π A ∈ N := fun A => by rw [hπ A]; exact (e.symm _).2
  have he'π : ∀ A, e' ⟨π A, hπN A⟩ = proj 3 K (blkP 1 (A : GL (Fin 2) K)) := fun A => by
    have h1 : (⟨π A, hπN A⟩ : N) = e.symm (proj 3 K (blkP Q A)) := Subtype.ext (hπ A)
    show (conjAut 3 K Q)⁻¹ (e ⟨π A, hπN A⟩) = _
    rw [h1, MulEquiv.apply_symm_apply, conjAut_inv_proj_blkP]
  let ι : X →* MulAut (projectiveSL 3 K) :=
    (MulAut.congr e').toMonoidHom.comp (MulAut.conjNormal (H := N))
  have hιapp : ∀ x, ι x = MulAut.congr e' (MulAut.conjNormal x) := fun x => rfl
  have hιπ : ∀ A, ι (π A) = MulAut.conj (proj 3 K (blkP 1 (A : GL (Fin 2) K))) := fun A => by
    rw [hιapp, congr_conjNormal_of_mem e' (hπN A), he'π]
  have hRJ := TA3.TightDatum.le_centralizer_of_gl2 hD hrange hk hoddK h4 slPartTopEquiv
  have hfix : ∀ r ∈ R, ∀ B : SL(2, K), ι r (proj 3 K ((blkP 1).comp SpecialLinearGroup.toGL B)) =
      proj 3 K ((blkP 1).comp SpecialLinearGroup.toGL B) := by
    intro r hr B
    let A : (⊤ : Subgroup (GL (Fin 2) K)) := ⟨SpecialLinearGroup.toGL B, Subgroup.mem_top _⟩
    have hAJ : π A ∈ (slPart (⊤ : Subgroup (GL (Fin 2) K))).map π :=
      ⟨A, mem_slPart.mpr (SpecialLinearGroup.coeToGL_det B), rfl⟩
    have hcomm : π A * r = r * π A := Subgroup.mem_centralizer_iff.mp (hRJ hr) _ hAJ
    show ι r (proj 3 K (blkP 1 (A : GL (Fin 2) K))) = proj 3 K (blkP 1 (A : GL (Fin 2) K))
    rw [← he'π A, hιapp]
    rw [show MulAut.congr e' (MulAut.conjNormal r) (e' ⟨π A, hπN A⟩) =
      e' (MulAut.conjNormal r ⟨π A, hπN A⟩) by simp [MulAut.congr_apply]]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← hcomm, mul_inv_cancel_right]
  have hs : ∃ q : QuaternionGroup 2, ¬ q ^ 2 ^ 1 = 1 ∧ ιq q ∈ N := by
    have hE : ∃ q : QuaternionGroup 2, ¬ q ^ 2 ^ 1 = 1 ∧ ι (ιq q) ∈ semilinearAutGroup 3 K := by
      by_cases ha : ι (ιq (a 1)) ∈ semilinearAutGroup 3 K
      · exact ⟨a 1, by decide, ha⟩
      by_cases hb : ι (ιq (xa 0)) ∈ semilinearAutGroup 3 K
      · exact ⟨xa 0, by decide, hb⟩
      refine ⟨a 1 * xa 0, by decide, ?_⟩
      rw [map_mul ιq, map_mul ι]
      exact mul_mem_semilinearAutGroup ha hb
    obtain ⟨q, hq2, hqE⟩ := hE
    have hqD := mem_linearAutGroup_of_fix h4 ((blkP 1).comp SpecialLinearGroup.toGL)
      (trace_blkP 1) hqE (hfix _ (hιqR q))
    have hq4' : ι (ιq q) ^ 2 ^ 2 = 1 := by
      rw [← map_pow, ← map_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, hq4, map_one, map_one]
    exact ⟨q, hq2, mem_of_congr_mem_inner hC e' (mem_inner_of_pow hqD hq4')⟩
  obtain ⟨q, hq2, hqN⟩ := hs
  have hqq : q * q = a 2 := by
    have hQ : ∀ q : QuaternionGroup 2, ¬ q ^ 2 ^ 1 = 1 → q * q = a 2 := by decide
    exact hQ q hq2
  obtain ⟨A, hA, l₀, hl₀⟩ :=
    exists_scalar_of_mem hD hrange hk slCentScalar_top hoddK h4 slPartTopEquiv (hιqR q) hqN
  have hAA : π (A * A) = π ⟨-1, Subgroup.mem_top _⟩ := by
    rw [map_mul, hA, hπ1, ← map_mul, hqq, hιqz]
  obtain ⟨ω, hω3, hω⟩ := hk (A * A * (⟨-1, Subgroup.mem_top _⟩)⁻¹)
    (by rw [map_mul, hAA, map_inv, mul_inv_cancel])
  have hl₀2 : (l₀ : K) * l₀ = -(ω : K) := by
    have e1 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hω
    simp [hl₀, GeneralLinearGroup.coe_scalar] at e1
    linear_combination -e1
  set l : Kˣ := l₀ * ω with hldef
  have hω3' : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hl : (l : K) * l = -1 := by
    rw [hldef, Units.val_mul]
    linear_combination (ω : K) ^ 2 * hl₀2 - hω3'
  have he's : e' ⟨ιq q, hqN⟩ = proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l)) := by
    have h1 : (⟨ιq q, hqN⟩ : N) = ⟨π A, hπN A⟩ := Subtype.ext hA.symm
    have hA' : (A : GL (Fin 2) K) = GeneralLinearGroup.scalar (Fin 2) l₀ := hl₀
    rw [h1, he'π, hA', hldef, map_mul, map_mul, map_mul, proj_blkP_scalar_cube hω3, mul_one]
  obtain ⟨q', hq'N, -⟩ := exists_quat_not_mem hD hrange hk slCentScalar_top hoddK h4
    slPartTopEquiv ιq hιq hιqR (hιqz ▸ hzN)
  have hσK : ιq q' ∈ tightCore R := hιqK q'
  have hσ4 : ι (ιq q') ^ 2 ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, hq4, map_one, map_one]
  obtain ⟨Aσ, τσ, εσ, hεσ, hσform⟩ :=
    (automorphism_generation (K := K) (n := 3) le_rfl).2 (ι (ιq q'))
  have hε1 : εσ = 1 := by
    interval_cases εσ
    · exfalso
      rw [pow_zero, mul_one] at hσform
      have hE : ι (ιq q') ∈ semilinearAutGroup 3 K :=
        mem_semilinearAutGroup_iff.mpr ⟨Aσ, τσ, hσform⟩
      have hDσ := mem_linearAutGroup_of_fix h4 _ (trace_blkP 1) hE (hfix _ (hιqR q'))
      exact hq'N (mem_of_congr_mem_inner hC e' (mem_inner_of_pow hDσ hσ4))
    · rfl
  subst hε1
  rw [pow_one] at hσform
  obtain ⟨hτσ, μ, hμ⟩ := graph_of_fix h4 h2 (fun B => by
    have := hfix _ (hιqR q') B
    rw [hσform] at this
    exact this)
  subst hτσ
  have hσ0 : ι (ιq q') = conjAut 3 K (sigMat μ) * dualAut 3 K := by
    rw [hσform, map_one, mul_one, hμ]
  have hZK : ∀ μ' : Kˣ,
      π ⟨GeneralLinearGroup.scalar (Fin 2) μ', Subgroup.mem_top _⟩ ∈ tightCore R := by
    intro μ'
    have hdet0 : (!![(μ' : K), 0; 0, 1] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
      simp [Matrix.det_fin_two_of]
    let A' : (⊤ : Subgroup (GL (Fin 2) K)) :=
      ⟨GeneralLinearGroup.mkOfDetNeZero !![(μ' : K), 0; 0, 1] hdet0, Subgroup.mem_top _⟩
    have hA'C : π A' ∈ Subgroup.centralizer ({z} : Set X) := by
      have : π A' ∈ π.range := ⟨A', rfl⟩
      rw [hrange] at this
      exact this.2
    have hcK := commutator_mem_tightCore hD hA'C hσK
    have hdetA' : GeneralLinearGroup.det (A' : GL (Fin 2) K) = μ' := Units.ext (by
      rw [GeneralLinearGroup.val_det_apply]
      simp [A', Matrix.det_fin_two_of])
    have h1 : ι ⁅π A', ιq q'⁆ =
        ι (π ⟨GeneralLinearGroup.scalar (Fin 2) μ', Subgroup.mem_top _⟩) := by
      rw [map_commutatorElement, hιπ, hσ0, commutator_conj, sig_dual_blkP, hιπ, ← map_inv,
        ← map_mul, ← map_inv, ← map_mul, hdetA']
      congr 3
      rw [_root_.mul_inv_rev, ← map_inv, inv_inv, ← mul_assoc, ← scalar_mul_comm, mul_assoc,
        mul_inv_cancel, mul_one]
    rw [← congr_conjNormal_injective hC e' h1]
    exact hcK
  have hτ : ∀ τ : K ≃+* K, τ * τ = 1 → τ = 1 := by
    intro τ hτ2
    by_contra hτ1
    obtain ⟨μ', hμ'⟩ := exists_orderOf_eight hp hp2 hf hK hτ2 hτ1
    set r := π ⟨GeneralLinearGroup.scalar (Fin 2) μ', Subgroup.mem_top _⟩ with hrdef
    have hrR : r ∈ R := tightCore_le R (hZK μ')
    have hμ8 : μ' ^ 8 = 1 := hμ' ▸ pow_orderOf_eq_one μ'
    have hr8 : r ^ 2 ^ 3 = 1 := by
      rw [hrdef, ← map_pow, show (2 : ℕ) ^ 3 = 8 by norm_num]
      have : (⟨GeneralLinearGroup.scalar (Fin 2) μ', Subgroup.mem_top _⟩ :
          (⊤ : Subgroup (GL (Fin 2) K))) ^ 8 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow, hμ8, map_one]; rfl)
      rw [this, map_one]
    obtain ⟨g, -, hgS⟩ := TA3.TightDatum.exists_conj_mem_of_pow S hrR hr8
    obtain ⟨eQ⟩ := hm.cls.1
    obtain ⟨y, hy, hyr⟩ := hgS
    have hy4 : y ^ 4 = 1 := by
      have : (⟨y, hy⟩ : (S : Subgroup R)) ^ 4 = 1 := by
        apply eQ.injective
        rw [map_pow, hq4, map_one]
      simpa using congrArg Subtype.val this
    have hr4 : r ^ 4 = 1 := by
      have h1 : (g * r * g⁻¹) ^ 4 = 1 := by
        rw [← hyr, Subgroup.coe_subtype, ← Subgroup.coe_pow, hy4, Subgroup.coe_one]
      rw [conj_pow, mul_inv_eq_one, mul_eq_left] at h1
      exact h1
    have hr4' : π ⟨GeneralLinearGroup.scalar (Fin 2) (μ' ^ 4), Subgroup.mem_top _⟩ = 1 := by
      rw [← hr4, hrdef, ← map_pow]
      congr 1
      exact Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow])
    obtain ⟨ω', hω'3, hω'⟩ := hk _ hr4'
    have hμω : μ' ^ 4 = ω' := scalar_injective hω'
    have h12 : μ' ^ 12 = 1 := by rw [show 12 = 4 * 3 by rfl, pow_mul, hμω, hω'3]
    have := orderOf_dvd_of_pow_eq_one h12
    rw [hμ'] at this
    norm_num at this
  refine concl163Syl_of_aut hC e' fun b hb2 hbK => ?_
  have hbc : b (proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l))) =
      proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l)) := by
    rw [← he's]
    apply apply_eq_of_comm_conj hZP
    rw [← congr_conjNormal_of_mem e' hqN]
    exact hbK _ (hιqS q)
  have hbσ := hbK _ (hιqS q')
  rw [← hιapp, hσ0] at hbσ
  rcases eq_of_inv_aut h2 hτ hl μ hb2 hbc hbσ with h | h
  · exact Or.inl h
  · right
    rw [h, congr_conjNormal_of_mem e' hzN]
    have hz : (⟨z, hzN⟩ : N) = ⟨π ⟨-1, Subgroup.mem_top _⟩, hπN _⟩ := Subtype.ext hπ1.symm
    rw [hz, he'π, ← conjAut_toGL, toGL_blkP, one_mul, inv_one, mul_one]

theorem concl163_of_psl3 {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {z : X}
    (hm : EdgelessMember3 R S z) [IsSimpleGroup ↥(genFittingFStar X)] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    (e : ↥(genFittingFStar X) ≃* projectiveSL 3 K) : Concl163 R z :=
  Concl163Syl.concl163 (concl163Syl_of_psl3 hm hp hp2 hf hK h5 e)

end CFSG.ClassicalInvolution.Q3.TL4.MF163.L3
