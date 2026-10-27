module

public import CFSG.LieType.Steinberg.CentralExt.Model
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.LieType.Steinberg

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ClassicalGroups.Symplectic

theorem card_statedScalars_subgroupOf_statedSp_le_two (n : ℕ) (K : Type) [Field K] :
    Nat.card ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)) ≤ 2 := by
  refine card_le_two_of_forall_scalar
    (φ := (StatedSp n K).subtype.comp (Subgroup.subtype _))
    (Subtype.val_injective.comp Subtype.val_injective) fun g => ?_
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 g.2
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, one_pow 2, Subsingleton.elim _ _⟩
  have hmat : (((g : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Matrix.scalar (Fin n ⊕ Fin n) (c : K) := by
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
  have hsp : ((g : StatedSp n K) : GL (Fin n ⊕ Fin n) K) ∈ TauCeti.GLSymplectic (Fin n) K := by
    rw [← statedSp_eq_GLSymplectic]
    exact (g : StatedSp n K).2
  rw [TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup, hmat,
    scalar_mem_symplecticGroup_iff hn] at hsp
  exact ⟨c, hsp, hmat⟩

theorem odd_symplectic_perfect_central_two_part_order_at_most_two {p f n : ℕ} (hp2 : p ≠ 2)
    {P Q : Type} [Group P] [Group Q] [Finite P] (hQ : LieModel Q .PSp n p f) {η : P →* Q}
    (hη : Function.Surjective η) (hP : Group.IsPerfect P) (hC : η.ker ≤ Subgroup.center P)
    (C₂ : Sylow 2 η.ker) : IsCyclic C₂ ∧ Nat.card C₂ ≤ 2 := by
  have := hP
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ :=
    statedClassicalModel_of_lieModel (by decide) hQ
  have hk : ringChar K ≠ 2 := ringChar_ne_two_of_card_eq_pow hp hp2 hK
  let β : StatedSp n K →* Q := e.symm.toMonoidHom.comp (QuotientGroup.mk' _)
  have hβ : Function.Surjective β := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : β.ker = (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) :=
    ker_comp_mk' _ e.symm
  obtain ⟨hdvd, -⟩ := sylow_two_of_isPerfect (β := β)
    (fun E _ _ π hπ hcen h2 => (odd_symplectic_central_two_extension_splitting hk n hπ hcen
      h2).imp fun _ h => h.1) hβ hη hC C₂
  have hZ : Nat.card β.ker ≤ 2 := hker ▸ card_statedScalars_subgroupOf_statedSp_le_two n K
  have hcard : Nat.card C₂ ≤ 2 := (Nat.le_of_dvd Nat.card_pos hdvd).trans hZ
  exact ⟨isCyclic_of_card_le_two hcard, hcard⟩

end CFSG.LieType.Steinberg
