module

public import CFSG.GH74.GLS.Stage4.T2NumGtSL2Lift

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG.GH74.GLS

theorem l64_rank_double {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F] (hF : IVK.L2Field F)
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) F) {z : K} (hz : e z = Rest.T2.negOne F)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ρ : Representation (ZMod p) K V) (hρz : ∀ v, ρ z v = -v)
    {y : K} (hy1 : y ≠ 1) (hyodd : Odd (orderOf y))
    (E : Submodule (ZMod p) V) (hE : ∀ v ∈ E, ρ y v = v) :
    2 * Module.finrank (ZMod p) E ≤ Module.finrank (ZMod p) V := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have hey1 : e y ≠ 1 := fun h => hy1 (e.injective (by rw [h, map_one]))
  have heyodd : Odd (orderOf (e y)) := by rw [MulEquiv.orderOf_eq]; exact hyodd
  obtain ⟨g, hg⟩ := sl2_exists_conj_neg_mem hF hey1 heyodd
  set b : K := e.symm g with hb
  have hzM : z ∈ Subgroup.closure ({y, b * y * b⁻¹} : Set K) := by
    have hmap : (Subgroup.closure ({y, b * y * b⁻¹} : Set K)).map e.toMonoidHom =
        Subgroup.closure ({e y, g * e y * g⁻¹} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
      rw [MonoidHom.map_closure, Set.image_pair]
      congr 2
      simp [hb]
    have h1 : e z ∈ (Subgroup.closure ({y, b * y * b⁻¹} : Set K)).map e.toMonoidHom := by
      rw [hmap, hz]; exact hg
    exact (Subgroup.mem_map_iff_mem e.injective).1 h1
  have hbb : ∀ v, ρ b (ρ b⁻¹ v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hbb' : ∀ v, ρ b⁻¹ (ρ b v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hinj : Function.Injective (ρ b) := fun v w h => by
    have := congrArg (ρ b⁻¹) h
    rwa [hbb', hbb'] at this
  let E' : Submodule (ZMod p) V := E.map (ρ b)
  have hdisj : Disjoint E E' := by
    rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨w, hw, hwv⟩ := hv'
    let S : Subgroup K :=
      { carrier := {k | ρ k v = v}
        mul_mem' := fun {a c} ha hc => by
          have ha' : ρ a v = v := ha
          have hc' : ρ c v = v := hc
          show ρ (a * c) v = v
          rw [map_mul, Module.End.mul_apply, hc', ha']
        one_mem' := by
          show ρ 1 v = v
          simp
        inv_mem' := fun {a} ha => by
          have ha' : ρ a v = v := ha
          show ρ a⁻¹ v = v
          calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
            _ = v := by rw [← Module.End.mul_apply, ← map_mul]; simp }
    have hyS : y ∈ S := hE v hv
    have hbyS : b * y * b⁻¹ ∈ S := by
      show ρ (b * y * b⁻¹) v = v
      calc ρ (b * y * b⁻¹) v = ρ b (ρ y (ρ b⁻¹ v)) := by
            simp only [map_mul, Module.End.mul_apply]
        _ = ρ b (ρ y w) := by rw [← hwv, hbb']
        _ = ρ b w := by rw [hE w hw]
        _ = v := hwv
    have hle : Subgroup.closure ({y, b * y * b⁻¹} : Set K) ≤ S := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hyS
      · exact hbyS
    have hzS : ρ z v = v := hle hzM
    have hneg := hρz v
    rw [hzS] at hneg
    have h3 : (2 : ZMod p) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hneg]
      exact neg_add_cancel _
    exact (smul_eq_zero.1 h3).resolve_left h2
  have hfin : Module.finrank (ZMod p) E' = Module.finrank (ZMod p) E :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (ρ b) hinj E)).symm
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq E E'
  have hinf : E ⊓ E' = ⊥ := disjoint_iff.1 hdisj
  rw [hinf, finrank_bot, add_zero] at hsup
  have hle := Submodule.finrank_le (E ⊔ E')
  omega

end CFSG.GH74.GLS.Stage4.Rest
