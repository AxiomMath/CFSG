module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Template
import CFSG.LieType.ChevTwo.OppCl.SL
import CFSG.LieType.ChevTwo.OppCl.Toolkit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.ChevTwo CFSG.LieType.ChevTwo.OppCl

@[expose] def RigidSLCore : Prop :=
  ∀ (F : Type) [Field F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (W : Submodule F V), W ≠ ⊥ → W ≠ ⊤ → ∀ (r : Equiv.Perm V), r ∈ semilinGroup F V →
      ∀ m : ℕ, Odd m → r ^ m = 1 →
        (∀ (w : V) (φ : V →ₗ[F] F), w ∈ W → (∀ x ∈ W, φ x = 0) →
          ∀ v, r (v + φ v • w) = r v + φ (r v) • w) →
        ∃ c : F, ∀ v, r v = c • v

section SL

variable (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_transvection_mem_flagKernel (Q : Subgroup (StatedSL n F)) (w : Fin n → F)
    (hw : w ∈ fixFlag (natRep (StatedSL n F)) Q 1) (φ : (Fin n → F) →ₗ[F] F)
    (hφ : ∀ x ∈ fixFlag (natRep (StatedSL n F)) Q 1, φ x = 0) :
    ∃ y ∈ flagKernel (natRep (StatedSL n F)) (fixFlag (natRep (StatedSL n F)) Q),
      ∀ v, natRep (StatedSL n F) y v = v + φ v • w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := natRep (StatedSL n F) with hρ
  set g : (Fin n → F) →ₗ[F] (Fin n → F) := φ.smulRight w with hg
  have hgv : ∀ v, g v = φ v • w := fun v => rfl
  have hg2 : ∀ v, g (g v) = 0 := by
    intro v
    rw [hgv, hgv, map_smul, hφ w hw, smul_zero, zero_smul]
  obtain ⟨y, hy⟩ := exists_statedSL_of_sq_zero n F g hg2
  have hy' : ∀ v, ρ y v = v + φ v • w := fun v => by rw [hy, hgv]
  have hyw : ρ y w = w := by rw [hy', hφ w hw, zero_smul, add_zero]
  have hyy : ∀ v, ρ y (ρ y v) = v := by
    intro v
    have h2 : ∀ u : Fin n → F, u + u = 0 := fun u => by
      funext i
      simp [CharTwo.add_self_eq_zero]
    calc ρ y (ρ y v) = ρ y (v + φ v • w) := congrArg (ρ y) (hy' v)
      _ = ρ y v + φ v • ρ y w := by rw [map_add, map_smul]
      _ = (v + φ v • w) + φ v • w := by rw [hy' v, hyw]
      _ = v := by rw [add_assoc, h2, add_zero]
  have hyinv : ρ y⁻¹ = ρ y := by
    have h1 : ρ y * ρ y = 1 := LinearMap.ext fun v => hyy v
    calc ρ y⁻¹ = (ρ y * ρ y) * ρ y⁻¹ := by rw [h1, one_mul]
      _ = ρ y * ρ (y * y⁻¹) := by rw [mul_assoc, ← map_mul]
      _ = ρ y := by rw [mul_inv_cancel, map_one, mul_one]
  refine ⟨y, ⟨?_, ?_⟩, hy'⟩
  · intro k v hv
    have hmem : ∀ u ∈ fixFlag ρ Q k, ρ y u ∈ fixFlag ρ Q k := by
      intro u hu
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [fixFlag_zero, Submodule.mem_bot] at hu
        rw [hu, map_zero]
        exact Submodule.zero_mem _
      · rw [hy']
        exact add_mem hu (Submodule.smul_mem _ _ (fixFlag_mono ρ Q hk hw))
    exact ⟨hmem v hv, by rw [hyinv]; exact hmem v hv⟩
  · intro k v hv
    rw [hy', add_sub_cancel_left]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hφ v hv, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (fixFlag_mono ρ Q hk hw)

theorem rigidProp_SL (core : RigidSLCore) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    RigidProp (fun _ => True) (natRep (StatedSL n F))
      (fun Q => fixFlag (natRep (StatedSL n F)) Q) p := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Rh hRhs _ hRhp _ Q hQ2 hK hcomm r hr
  set ρ := natRep (StatedSL n F) with hρ
  have hinj : Function.Injective ρ := natRep_injective _
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ flagKernel ρ (fixFlag ρ Q), x ≠ 1 :=
    (Subgroup.bot_or_exists_ne_one _).resolve_left hK
  have hVnt : Nontrivial (Fin n → F) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hx1 (hinj (LinearMap.ext fun v => Subsingleton.elim _ _))
  have hW0 : fixFlag ρ Q 1 ≠ ⊥ := by
    obtain ⟨v, hv0, hv⟩ := exists_fixed_ne_zero ρ 2 Q hQ2
    intro hbot
    apply hv0
    have : v ∈ fixFlag ρ Q 1 := fun g hg => by rw [hv g hg, sub_self]; exact Submodule.zero_mem _
    rw [hbot, Submodule.mem_bot] at this
    exact this
  have hWtop : fixFlag ρ Q 1 ≠ ⊤ := by
    intro htop
    apply hx1
    apply hinj
    apply LinearMap.ext
    intro v
    have h1 := hx.2 0 v (by rw [htop]; trivial)
    rw [fixFlag_zero, Submodule.mem_bot, sub_eq_zero] at h1
    rw [h1, map_one]
    rfl
  obtain ⟨k, hk⟩ := hRhp ⟨r, hr⟩
  have hrk : r ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine core F (Fin n → F) (fixFlag ρ Q 1) hW0 hWtop r (hRhs hr) (p ^ k)
    ((hp.odd_of_ne_two hp2).pow) hrk ?_
  intro w φ hw hφ v
  obtain ⟨y, hy, hyv⟩ := exists_transvection_mem_flagKernel n Q w hw φ hφ
  have := hcomm y hy r hr v
  rw [hyv, hyv] at this
  exact this

theorem radRigid_PSL (core : RigidSLCore) (hn : 3 ≤ n) :
    RadRigid 2 (StatedProj (StatedSL n F)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (StatedSL n F) := inferInstance
  refine radRigid_of_rigid (H := StatedSL n F)
    ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) (statedProj_kernel_central _)
    (statedProj_kernel_coprime 2 _) (fun _ => True) (natRep (StatedSL n F)) (natRep_injective _)
    (fun Q => fixFlag (natRep (StatedSL n F)) Q) (fun Q _ => fixFlag_zero _ Q)
    (fun Q hQ => exists_fixFlag_eq_top (natRep (StatedSL n F)) 2 Q hQ)
    (fun Q _ => normalizer_le_flagStab_fixFlag _ Q) (fun Q _ => le_flagKernel_fixFlag _ Q) ?_
    (fun p hp hp2 => rigidProp_SL n core p hp hp2)
  intro p hp hp2 R hR
  haveI : Fact p.Prime := ⟨hp⟩
  exact autLift_of_induced (fun _ => True) trivial (fun _ _ _ _ => trivial) (fun _ _ => trivial)
    p R hR (induced_PSL n F hn p hp2 R hR)

end SL

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
