module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddSLCore
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddTemplate

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.ChevTwo CFSG.LieType.ChevTwo.OppCl

theorem mem_statedScalars_of_natRep {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) (x : H) (h : ∃ c : K, ∀ v, natRep H x v = c • v) :
    x ∈ (StatedScalars ι K).subgroupOf H := by
  obtain ⟨c, hc⟩ := h
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : x = 1 := Subtype.ext (Units.ext (Matrix.ext fun i => (IsEmpty.false i).elim))
    rw [this]
    exact one_mem _
  have hM : ((x : GL ι K) : Matrix ι ι K) = Matrix.scalar ι c := by
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    have := hc v
    rw [natRep_apply] at this
    rw [this]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hc0 : c ≠ 0 := by
    intro h0
    have hdet : (((x : GL ι K) : Matrix ι ι K)).det ≠ 0 := by
      have := (x : GL ι K).isUnit.map Matrix.detMonoidHom
      exact this.ne_zero
    rw [hM, h0] at hdet
    apply hdet
    simp
  refine Subgroup.mem_subgroupOf.2 ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  rw [hM]
  rfl

section SLQ

variable (n : ℕ) {F : Type} [Field F] [Finite F]

theorem exists_statedSL_of_sq_zero_q (q : ℕ) [Fact q.Prime] [CharP F q]
    (g : (Fin n → F) →ₗ[F] (Fin n → F)) (hg : ∀ v, g (g v) = 0) :
    ∃ y : StatedSL n F, ∀ v, natRep (StatedSL n F) y v = v + g v := by
  set M : Matrix (Fin n) (Fin n) F := LinearMap.toMatrix' (LinearMap.id + g) with hM
  have hMv : ∀ v, Matrix.mulVec M v = v + g v := by
    intro v
    rw [hM, LinearMap.toMatrix'_mulVec]
    simp
  set G : Matrix (Fin n) (Fin n) F := LinearMap.toMatrix' g with hG
  have hGv : ∀ v, Matrix.mulVec G v = g v := by
    intro v
    rw [hG, LinearMap.toMatrix'_mulVec]
  have hGG : G * G = 0 := by
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    rw [← Matrix.mulVec_mulVec, hGv, hGv, hg, Matrix.zero_mulVec]
  have hnil : IsNilpotent G := ⟨2, by rw [pow_two]; exact hGG⟩
  have hMG : M = 1 + G := by
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    rw [hMv, Matrix.add_mulVec, Matrix.one_mulVec, hGv]
  have hdet : M.det = 1 := by
    rw [hMG]
    exact det_one_add_of_isNilpotent q hnil
  have hdet0 : M.det ≠ 0 := by rw [hdet]; exact one_ne_zero
  refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet0, Subgroup.subset_closure ?_⟩, fun v => ?_⟩
  · show (Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet0 : Matrix (Fin n) (Fin n) F).det = 1
    simpa using hdet
  · rw [natRep_apply]
    exact hMv v

theorem exists_transvection_mem_flagKernel_q (q : ℕ) [Fact q.Prime] [CharP F q]
    (Q : Subgroup (StatedSL n F)) (w : Fin n → F)
    (hw : w ∈ fixFlag (natRep (StatedSL n F)) Q 1) (φ : (Fin n → F) →ₗ[F] F)
    (hφ : ∀ x ∈ fixFlag (natRep (StatedSL n F)) Q 1, φ x = 0) :
    ∃ y ∈ flagKernel (natRep (StatedSL n F)) (fixFlag (natRep (StatedSL n F)) Q),
      ∀ v, natRep (StatedSL n F) y v = v + φ v • w := by
  set ρ := natRep (StatedSL n F) with hρ
  set g : (Fin n → F) →ₗ[F] (Fin n → F) := φ.smulRight w with hg
  have hgv : ∀ v, g v = φ v • w := fun v => rfl
  have hg2 : ∀ v, g (g v) = 0 := by
    intro v
    rw [hgv, hgv, map_smul, hφ w hw, smul_zero, zero_smul]
  obtain ⟨y, hy⟩ := exists_statedSL_of_sq_zero_q n q g hg2
  have hy' : ∀ v, ρ y v = v + φ v • w := fun v => by rw [hy, hgv]
  have hyinv : ∀ v, ρ y⁻¹ v = v - φ v • w := by
    intro v
    have h1 : ρ y (v - φ v • w) = v := by
      rw [hy', map_sub, map_smul, hφ w hw, smul_zero, sub_zero]
      abel
    have h2 := congrArg (ρ y⁻¹) h1
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2
    exact h2.symm
  refine ⟨y, ⟨?_, ?_⟩, hy'⟩
  · intro k v hv
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [fixFlag_zero, Submodule.mem_bot] at hv
      rw [hv, map_zero, map_zero]
      exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    · have hwk : w ∈ fixFlag ρ Q k := fixFlag_mono ρ Q hk hw
      rw [hy', hyinv]
      exact ⟨add_mem hv (Submodule.smul_mem _ _ hwk), sub_mem hv (Submodule.smul_mem _ _ hwk)⟩
  · intro k v hv
    rw [hy', add_sub_cancel_left]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hφ v hv, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (fixFlag_mono ρ Q hk hw)

theorem rigidInner_SL {q : ℕ} [Fact q.Prime] [CharP F q] (Q : Subgroup (StatedSL n F))
    (hQ : IsPGroup q Q)
    (hK : flagKernel (natRep (StatedSL n F)) (fixFlag (natRep (StatedSL n F)) Q) ≠ ⊥)
    (x : StatedSL n F) (hx : Nat.Coprime (orderOf x) q)
    (hcomm : ∀ k ∈ flagKernel (natRep (StatedSL n F)) (fixFlag (natRep (StatedSL n F)) Q),
      x * k = k * x) :
    ∃ c : F, ∀ v, natRep (StatedSL n F) x v = c • v := by
  set ρ := natRep (StatedSL n F) with hρ
  have hinj : Function.Injective ρ := natRep_injective _
  obtain ⟨x1, hx1k, hx11⟩ : ∃ x1 ∈ flagKernel ρ (fixFlag ρ Q), x1 ≠ 1 :=
    (Subgroup.bot_or_exists_ne_one _).resolve_left hK
  have hVnt : Nontrivial (Fin n → F) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hx11 (hinj (LinearMap.ext fun v => Subsingleton.elim _ _))
  have hW0 : fixFlag ρ Q 1 ≠ ⊥ := by
    obtain ⟨v, hv0, hv⟩ := exists_fixed_ne_zero ρ q Q hQ
    intro hbot
    apply hv0
    have : v ∈ fixFlag ρ Q 1 := fun g hg => by rw [hv g hg, sub_self]; exact Submodule.zero_mem _
    rw [hbot, Submodule.mem_bot] at this
    exact this
  have hWtop : fixFlag ρ Q 1 ≠ ⊤ := by
    intro htop
    apply hx11
    apply hinj
    apply LinearMap.ext
    intro v
    have h1 := hx1k.2 0 v (by rw [htop]; trivial)
    rw [fixFlag_zero, Submodule.mem_bot, sub_eq_zero] at h1
    rw [h1, map_one]
    rfl
  let r : Equiv.Perm (Fin n → F) :=
    { toFun := ρ x
      invFun := ρ x⁻¹
      left_inv := fun v => by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      right_inv := fun v => by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] }
  have hrv : ∀ v, r v = ρ x v := fun v => rfl
  have hr : r ∈ semilinGroup F (Fin n → F) :=
    ⟨fun u v => by rw [hrv, hrv, hrv]; exact map_add (ρ x) u v, RingEquiv.refl F,
      fun c v => by rw [hrv, hrv]; exact map_smul (ρ x) c v⟩
  have hpow : ∀ k : ℕ, ∀ v, (r ^ k) v = (ρ x ^ k) v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ', Equiv.Perm.mul_apply, ih, hrv, pow_succ', Module.End.mul_apply]
  have hrm : r ^ orderOf x = 1 := by
    refine Equiv.ext fun v => ?_
    rw [hpow, ← map_pow, pow_orderOf_eq_one, map_one]
    rfl
  have hcommV : ∀ (w : Fin n → F) (φ : (Fin n → F) →ₗ[F] F),
      w ∈ fixFlag ρ Q 1 → (∀ y ∈ fixFlag ρ Q 1, φ y = 0) →
        ∀ v, r (v + φ v • w) = r v + φ (r v) • w := by
    intro w φ hw hφ v
    obtain ⟨y, hy, hyv⟩ := exists_transvection_mem_flagKernel_q n q Q w hw φ hφ
    have := congrArg (fun z : StatedSL n F => ρ z v) (hcomm y hy)
    simp only [map_mul, Module.End.mul_apply] at this
    rw [hyv v, hyv (ρ x v)] at this
    rw [hrv, hrv]
    exact this
  obtain ⟨c, hc⟩ := rigidSLCoreQ q F (Fin n → F) (fixFlag ρ Q 1) hW0 hWtop r hr (orderOf x) hx hrm
    hcommV
  exact ⟨c, fun v => by rw [← hrv]; exact hc v⟩

theorem radRigidInner_PSL {q : ℕ} [Fact q.Prime] [CharP F q] :
    RadRigidInner q (StatedProj (StatedSL n F)) := by
  have : Finite (StatedSL n F) := inferInstance
  exact radRigidInner_of_rigid (H := StatedSL n F)
    ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) (statedProj_kernel_central _)
    (statedProj_kernel_coprime q _) (natRep (StatedSL n F)) (natRep_injective _)
    (fun Q => fixFlag (natRep (StatedSL n F)) Q) (fun Q _ => fixFlag_zero _ Q)
    (fun Q hQ => exists_fixFlag_eq_top (natRep (StatedSL n F)) q Q hQ)
    (fun Q _ => normalizer_le_flagStab_fixFlag _ Q) (fun Q _ => le_flagKernel_fixFlag _ Q)
    (fun x hx => mem_statedScalars_of_natRep _ x hx)
    (fun Q hQ hK x hx hcomm => rigidInner_SL n Q hQ hK x hx hcomm)

end SLQ

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
