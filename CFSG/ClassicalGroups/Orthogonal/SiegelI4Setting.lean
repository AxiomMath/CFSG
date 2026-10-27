module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4Defs
public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1CaseII
public import CFSG.ClassicalGroups.Alternating.RT1SpFaithful
public import CFSG.ClassicalGroups.Alternating.I4SpPlaneConj

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem i4Setting_of (hq : 4 ≤ Nat.card K) (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    (h6 : 6 ≤ finrank K N) (Qf : QuadraticForm K V)
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (ρ : Gsp BN →* (V ≃ₗ[K] V)) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    {a₀ c₀ : N} (hac₀ : BN a₀ c₀ = 0) (hli₀ : LinearIndependent K ![a₀, c₀])
    (hsieg : finrank K (movedSpace (ρ (lineElt hBN a₀ c₀))) = 2 ∧
      ∀ w ∈ movedSpace (ρ (lineElt hBN a₀ c₀)), Qf w = 0)
    (hC : ∀ v : V, (∀ g, ρ g v = v) → v = 0) (hV : commutatorSpace ρ.range = ⊤) :
    I4Setting hBN Qf ρ := by
  have hS : IsLongRootElement Qf (ρ (lineElt hBN a₀ c₀)) :=
    (isLongRootElement_iff hnd).2 ⟨hρQ _, hsieg.1, hsieg.2⟩
  have hne : ρ (lineElt hBN a₀ c₀) ≠ 1 := by
    intro h
    have h2 := hsieg.1
    rw [h, movedSpace_one_eq_bot, finrank_bot] at h2
    exact absurd h2 (by norm_num)
  have hinj : Function.Injective ρ := by
    haveI := isSimpleGroup_Gsp hq hBN hBNnd (by omega)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with hker | hker
    · exact (MonoidHom.ker_eq_bot_iff ρ).mp hker
    · exact absurd (MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top (lineElt hBN a₀ c₀))) hne
  refine ⟨hq, hBNnd, h6, hnd, hρQ, ?_, hC, hV, hinj⟩
  intro a c hac hli
  obtain ⟨g, hg⟩ := exists_conj_lineElt_eq hBN hBNnd hac₀ hac hli₀ hli
  have e : ρ (lineElt hBN a c) = ρ g * ρ (lineElt hBN a₀ c₀) * (ρ g)⁻¹ := by
    rw [← hg, map_mul, map_mul, map_inv]
  rw [e]
  exact IsLongRootElement.conj (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hρQ g)) hS

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
