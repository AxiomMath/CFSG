module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Simp

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem conj_mul_conj_inv {S : Type} [Group S] (a : MulAut S) (s : S) :
    a * MulAut.conj s * a⁻¹ = MulAut.conj (a s) := by
  ext y
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem l34g_conj_injective {S : Type} [Group S] (h : center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro z
    have := congrArg (fun φ : MulAut S => φ z) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc z * g = g * z * g⁻¹ * g := by rw [this]
      _ = g * z := by group
  rw [h, Subgroup.mem_bot] at hc
  exact hc

theorem l34g_inn_normal (S : Type) [Group S] :
    ((MulAut.conj : S →* MulAut S).range).Normal := by
  refine ⟨fun x hx φ => ?_⟩
  obtain ⟨g, rfl⟩ := hx
  refine ⟨φ g, ?_⟩
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply, MulAut.inv_apply]

theorem l34g_inn_centralizer {S : Type} [Group S] (h : center S = ⊥) :
    centralizer (((MulAut.conj : S →* MulAut S).range : Subgroup (MulAut S)) : Set (MulAut S)) =
      ⊥ := by
  have hinj := l34g_conj_injective h
  rw [eq_bot_iff]
  intro φ hφ
  rw [Subgroup.mem_centralizer_iff] at hφ
  rw [Subgroup.mem_bot]
  ext x
  have hcomm : MulAut.conj x * φ = φ * MulAut.conj x := hφ (MulAut.conj x) ⟨x, rfl⟩
  have h5 : MulAut.conj (φ x) = MulAut.conj x := by
    rw [← conj_mul_conj_inv φ x, ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  simpa using hinj h5

theorem l34g_inn_simpleFStar {S : Type} [Group S] [Finite S] (h : SimpleFStarQuotient S) :
    SimpleFStarQuotient ↥((MulAut.conj : S →* MulAut S).range) := by
  have hc : center S = ⊥ := (l34g_simple_of_simpleFStar h).2
  exact l34g_simpleFStar_of_mulEquiv (MonoidHom.ofInjective (l34g_conj_injective hc)) h

theorem l34g_inn_commute_iff {S : Type} [Group S] (h : center S = ⊥) (a : MulAut S) (s : S) :
    MulAut.conj s * a = a * MulAut.conj s ↔ a s = s := by
  have hinj := l34g_conj_injective h
  constructor
  · intro hc
    apply hinj
    rw [← conj_mul_conj_inv a s, ← hc, mul_assoc, mul_inv_cancel, mul_one]
  · intro hs
    have h1 : a * MulAut.conj s * a⁻¹ = MulAut.conj s := by
      rw [conj_mul_conj_inv, hs]
    have h2 : a * MulAut.conj s = MulAut.conj s * a := by
      have := congrArg (fun x : MulAut S => x * a) h1
      simpa [mul_assoc] using this
    exact h2.symm

end CFSG.OddStandard.SmallF3.Omega
