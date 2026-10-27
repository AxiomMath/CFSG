module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult

section Aux

variable {J : Type*} [Group J]

def centralCoprimeSubgroup (Z : Subgroup J) (hZ : Z ≤ Subgroup.center J) (p : ℕ) :
    Subgroup J where
  carrier := {g | g ∈ Z ∧ ∃ m : ℕ, Nat.Coprime m p ∧ g ^ m = 1}
  one_mem' := ⟨one_mem Z, 1, Nat.coprime_one_left p, one_pow 1⟩
  mul_mem' := by
    rintro a b ⟨ha, m, hm, ham⟩ ⟨hb, n, hn, hbn⟩
    have hcomm : Commute a b := Subgroup.mem_center_iff.mp (hZ hb) a
    refine ⟨mul_mem ha hb, m * n, Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩, ?_⟩
    rw [hcomm.mul_pow, pow_mul, ham, one_pow, one_mul, mul_comm m n, pow_mul, hbn, one_pow]
  inv_mem' := by
    rintro a ⟨ha, m, hm, ham⟩
    exact ⟨inv_mem ha, m, hm, by rw [inv_pow, ham, inv_one]⟩

end Aux

theorem exists_pgroup_central_ext {J T : Type} [Group J] [Finite J] [Group T] (π : J →* T)
    (hπ : Function.Surjective π) (hJ : Group.IsPerfect J) (hz : π.ker ≤ Subgroup.center J)
    (hne : π.ker ≠ ⊥) :
    ∃ (p : ℕ) (_ : p.Prime) (J₁ : Type) (_ : Group J₁) (_ : Finite J₁) (π₁ : J₁ →* T),
      Function.Surjective π₁ ∧ Group.IsPerfect J₁ ∧ π₁.ker ≤ Subgroup.center J₁ ∧
        IsPGroup p π₁.ker ∧ π₁.ker ≠ ⊥ := by
  classical
  obtain ⟨p, hp, hpd⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card π.ker :=
    Nat.exists_prime_and_dvd fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) p hpd
  let W : Subgroup J := centralCoprimeSubgroup π.ker hz p
  have hWn : W.Normal := Subgroup.normal_of_le_center fun g hg => hz hg.1
  have hWker : W ≤ π.ker := fun g hg => hg.1
  let π₁ : J ⧸ W →* T := QuotientGroup.lift W π hWker
  have hπ₁ : ∀ g : J, π₁ (g : J ⧸ W) = π g := fun g => rfl
  refine ⟨p, hp, J ⧸ W, inferInstance, inferInstance, π₁, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨g, rfl⟩ := hπ t
    exact ⟨(g : J ⧸ W), hπ₁ g⟩
  · have := hJ
    infer_instance
  · intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg : g ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hπ₁]
      exact hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.mp (hz hg)) h]
  · intro x
    obtain ⟨x, hx⟩ := x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg : g ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hπ₁]
      exact hx
    obtain ⟨e, b, hb, hgb⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
    refine ⟨e, Subtype.ext ?_⟩
    show (g : J ⧸ W) ^ p ^ e = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine ⟨Subgroup.pow_mem _ hg _, b, ((Nat.Prime.coprime_iff_not_dvd hp).mpr hb).symm, ?_⟩
    rw [← pow_mul, ← hgb, pow_orderOf_eq_one]
  · intro hbot
    have hz0' : orderOf (z0 : J) = p := by rwa [Subgroup.orderOf_coe]
    have hmem : ((z0 : J) : J ⧸ W) ∈ π₁.ker := by
      rw [MonoidHom.mem_ker, hπ₁]
      exact z0.2
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    obtain ⟨_, m, hm, hzm⟩ := hmem
    have hpm : p ∣ m := hz0' ▸ orderOf_dvd_of_pow_eq_one hzm
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hm hpm dvd_rfl)

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult
