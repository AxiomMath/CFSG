module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreA
public import CFSG.HardMathSupport.Timmesfeld.DefChar.Families

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.DefChar

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem mul_conj_mul_inv_apply (σ : MulAut G) (g : G) :
    σ * MulAut.conj g * σ⁻¹ = MulAut.conj (σ g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem apply_eq_of_mem_gLAPPrimeCoreOf (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    {H : Subgroup (MulAut G)} (hH : innerAut G ≤ H) {y g : MulAut G}
    (hg : g ∈ GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({y} : Set (MulAut G))))
    (T : Subgroup G) (hTy : ∀ t ∈ T, y t = t) (hTg : ∀ t ∈ T, g t ∈ T)
    (hO : ∀ R : Subgroup G, R ≤ T → (∀ t ∈ T, ∀ r ∈ R, t * r * t⁻¹ ∈ R) →
      (∀ r ∈ R, Nat.Coprime 3 (orderOf r)) → R = ⊥) :
    ∀ t ∈ T, g t = t := by
  set X := H ⊓ Subgroup.centralizer ({y} : Set (MulAut G)) with hX
  set N := GLAPPrimeCoreOf 3 X with hN
  have hcX : ∀ t ∈ T, (MulAut.conj t : MulAut G) ∈ X := by
    intro t ht
    refine Subgroup.mem_inf.2 ⟨hH ⟨t, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := mul_conj_mul_inv_apply y t
    rw [hTy t ht] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  set R : Subgroup G := T ⊓ N.comap (MulAut.conj : G →* MulAut G) with hR
  have hR1 : R = ⊥ := by
    refine hO R inf_le_left (fun t ht r hr => ?_) (fun r hr => ?_)
    · obtain ⟨hrT, hrN⟩ := Subgroup.mem_inf.1 hr
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht hrT) (inv_mem ht), ?_⟩
      rw [Subgroup.mem_comap] at hrN ⊢
      have := conj_mem_gLAPPrimeCoreOf hrN (hcX t ht)
      simpa [map_mul, map_inv] using this
    · obtain ⟨-, hrN⟩ := Subgroup.mem_inf.1 hr
      rw [Subgroup.mem_comap] at hrN
      have := CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_coprime_of_mem_GLAPPrimeCoreOf
        Nat.prime_three hrN
      rwa [orderOf_injective (MulAut.conj : G →* MulAut G) hinj r, Nat.coprime_comm] at this
  intro t ht
  have hr : t * (g t)⁻¹ ∈ R := by
    refine Subgroup.mem_inf.2 ⟨mul_mem ht (inv_mem (hTg t ht)), ?_⟩
    rw [Subgroup.mem_comap]
    have h1 := conj_mem_gLAPPrimeCoreOf hg (hcX t ht)
    have h2 := mul_mem h1 (inv_mem hg)
    have e : (MulAut.conj t : MulAut G) * g * (MulAut.conj t)⁻¹ * g⁻¹ =
        MulAut.conj (t * (g t)⁻¹) := by
      rw [map_mul, map_inv, ← mul_conj_mul_inv_apply g t]
      group
    rw [e] at h2
    exact h2
  rw [hR1, Subgroup.mem_bot] at hr
  exact (mul_inv_eq_one.1 hr).symm

end CFSG.HardMathSupport.Solomon.Coordinator
