module

public import CFSG.Holt.Fixed
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Holt

open MulAction
open scoped commutatorElement

section ExponentTwo

variable {G : Type*} [Group G]

theorem exists_monoidHom_ker_eq_of_index_eq_two {H : Subgroup G} (hH : H.index = 2) :
    ∃ χ : G →* Multiplicative (ZMod 2), χ.ker = H := by
  classical
  refine ⟨{ toFun := fun g => if g ∈ H then 1 else Multiplicative.ofAdd 1
            map_one' := by simp
            map_mul' := fun a b => ?_ }, ?_⟩
  · simp only [Subgroup.mul_mem_iff_of_index_two hH]
    by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [ha, hb]
    decide
  · ext g
    simp only [MonoidHom.mem_ker, MonoidHom.coe_mk, OneHom.coe_mk]
    by_cases hg : g ∈ H <;> simp [hg]

theorem monoidHom_eq_one_of_isSimpleGroup [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {A : Type*} [CommGroup A] (ψ : G →* A) : ψ = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact absurd ((ψ.ker_eq_bot_iff.mp h) (by rw [map_mul, map_mul, mul_comm])) hab
  · exact MonoidHom.ext fun x => ψ.mem_ker.mp (h ▸ Subgroup.mem_top x)

theorem index_ne_two_of_forall_monoidHom_eq_one
    (h : ∀ χ : G →* Multiplicative (ZMod 2), χ = 1) (N : Subgroup G) : N.index ≠ 2 := by
  intro hN
  obtain ⟨χ, hχ⟩ := exists_monoidHom_ker_eq_of_index_eq_two hN
  have htop : N = ⊤ := by
    rw [← hχ, eq_top_iff]
    intro g _
    rw [MonoidHom.mem_ker, h χ]
    rfl
  rw [htop, Subgroup.index_top] at hN
  exact absurd hN (by norm_num)

theorem subgroup_index_ne_two_of_isSimpleGroup [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (N : Subgroup G) : N.index ≠ 2 :=
  index_ne_two_of_forall_monoidHom_eq_one (monoidHom_eq_one_of_isSimpleGroup hnonab) N

end ExponentTwo

end CFSG.Holt
