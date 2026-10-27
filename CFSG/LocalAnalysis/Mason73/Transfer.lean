module

public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.Mason73.Rank

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem not_mem_commutator_of_not_conj_into {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤) {Q : Subgroup (L4Model n)} (hQ : Q.index = 2)
    {l : L4Model n} (hl : orderOf l = 2) (hQl : ∀ x : G, x⁻¹ * ι l * x ∉ Q.map ι) :
    ι l ∉ commutator G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hP2, hPidx⟩ := isSylowOf_iff.1 hS
  have hQidx : (Q.map ι).relIndex ι.range = 2 := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hι,
      Subgroup.relIndex_top_right, hQ]
  have hQP : Q.map ι ≤ ι.range := by
    rintro _ ⟨q, -, rfl⟩
    exact ⟨q, rfl⟩
  obtain ⟨N, -, hNn, hsq, hlN⟩ := CFSG.Quasithin.thompson_transfer_exists_normal_subgroup
    le_top hP2 hPidx hQP hQidx (Subgroup.mem_top _) (by rw [orderOf_injective ι hι, hl])
    (fun x _ => hQl x)
  haveI : N.Normal := ⟨fun x hx g => Subgroup.mem_subgroupOf.1
    (hNn.conj_mem ⟨x, Subgroup.mem_top x⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨g, Subgroup.mem_top g⟩)⟩
  have hcomm : IsMulCommutative (G ⧸ N) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have hE : ∀ x ∈ (⊤ : Subgroup (G ⧸ N)), x * x = 1 := by
      intro x _
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← pow_two]
      exact hsq g (Subgroup.mem_top g)
    exact mul_comm_of_mul_self hE (Subgroup.mem_top a) (Subgroup.mem_top b)
  exact fun hlc => hlN ((Subgroup.Normal.quotient_commutative_iff_commutator_le.1 hcomm) hlc)

end CFSG.LocalAnalysis.Mason73
