module

public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

section Norm

variable {V : Type*} [CommGroup V]

theorem pow_odd_eq_self (hV : ∀ v : V, v ^ 2 = 1) (c : V) {k : ℕ} (hk : Odd k) : c ^ k = c := by
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul, hV c, one_pow, one_mul]

@[expose] def normK (K : Subgroup (MulAut V)) [Fintype ↥K] : V →* V where
  toFun v := ∏ k : ↥K, (k : MulAut V) v
  map_one' := by simp
  map_mul' v w := by simp [Finset.prod_mul_distrib]

variable (K : Subgroup (MulAut V)) [Fintype ↥K]

theorem normK_apply (v : V) : normK K v = ∏ k : ↥K, (k : MulAut V) v := rfl

theorem normK_apply_mem {g : MulAut V} (hg : g ∈ K) (v : V) : normK K (g v) = normK K v := by
  rw [normK_apply, normK_apply]
  refine Fintype.prod_equiv (Equiv.mulRight (⟨g, hg⟩ : ↥K)) _ _ fun k => ?_
  simp

theorem apply_normK {g : MulAut V} (hg : g ∈ K) (v : V) : g (normK K v) = normK K v := by
  rw [normK_apply, map_prod]
  refine Fintype.prod_equiv (Equiv.mulLeft (⟨g, hg⟩ : ↥K)) _ _ fun k => ?_
  simp

theorem normK_mem_fixV (v : V) : normK K v ∈ fixV K := fun _ hg => apply_normK K hg v

theorem normK_of_mem_fixV {c : V} (hc : c ∈ fixV K) : normK K c = c ^ Fintype.card ↥K := by
  rw [normK_apply]
  have : ∀ k : ↥K, (k : MulAut V) c = c := fun k => hc k k.2
  simp [this]

theorem normK_of_mem_fixV' (hodd : Odd (Fintype.card ↥K)) (hV : ∀ v : V, v ^ 2 = 1) {c : V}
    (hc : c ∈ fixV K) : normK K c = c := by
  rw [normK_of_mem_fixV K hc, pow_odd_eq_self hV _ hodd]

theorem normK_normK (hodd : Odd (Fintype.card ↥K)) (hV : ∀ v : V, v ^ 2 = 1) (v : V) :
    normK K (normK K v) = normK K v :=
  normK_of_mem_fixV' K hodd hV (normK_mem_fixV K v)

theorem normK_div_mem_ker (hodd : Odd (Fintype.card ↥K)) (hV : ∀ v : V, v ^ 2 = 1) (v : V) :
    normK K (v * (normK K v)⁻¹) = 1 := by
  rw [map_mul, map_inv, normK_normK K hodd hV, mul_inv_cancel]

theorem normK_ker_inf_fixV (hodd : Odd (Fintype.card ↥K)) (hV : ∀ v : V, v ^ 2 = 1) :
    (normK K).ker ⊓ fixV K = ⊥ := by
  rw [eq_bot_iff]
  rintro c ⟨hc1, hc2⟩
  rw [Subgroup.mem_bot]
  have := normK_of_mem_fixV' K hodd hV hc2
  rw [MonoidHom.mem_ker.mp hc1] at this
  exact this.symm

theorem normK_ker_sup_fixV (hodd : Odd (Fintype.card ↥K)) (hV : ∀ v : V, v ^ 2 = 1) :
    (normK K).ker ⊔ fixV K = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have h1 : v * (normK K v)⁻¹ ∈ (normK K).ker := normK_div_mem_ker K hodd hV v
  have := Subgroup.mul_mem_sup h1 (normK_mem_fixV K v)
  rwa [inv_mul_cancel_right] at this

theorem eq_prod_of_mem_ker_normK (hodd : Odd (Fintype.card ↥K)) (hV : ∀ v : V, v ^ 2 = 1) {w : V}
    (hw : w ∈ (normK K).ker) : w = ∏ k : ↥K, ((k : MulAut V) w * w⁻¹)⁻¹ := by
  have h1 : ∏ k : ↥K, ((k : MulAut V) w * w⁻¹)⁻¹ = (normK K w)⁻¹ * w ^ Fintype.card ↥K := by
    rw [Finset.prod_inv_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      inv_pow, normK_apply]
    simp [mul_comm]
  rw [h1, MonoidHom.mem_ker.mp hw, pow_odd_eq_self hV _ hodd, inv_one, one_mul]

end Norm

end CFSG.CGT.PushingUpLit.CGT6
