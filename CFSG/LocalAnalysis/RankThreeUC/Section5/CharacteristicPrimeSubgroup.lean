module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ActorCyclicity

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.CharacteristicPrimeSubgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_characteristic {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {r : ℕ} (hr : r ∈ piOf B) :
    ∃ A : Subgroup G, A ≤ B ∧ Nat.card A = r ∧
      ∀ φ : B ≃* B, (A.subgroupOf B).map φ.toMonoidHom = A.subgroupOf B := by
  haveI : IsCyclic B := actor_isCyclic h
  simp only [piOf, Set.mem_setOf_eq] at hr
  obtain ⟨hrp, hrd⟩ := hr
  haveI : Fact r.Prime := ⟨hrp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hrd
  refine ⟨(Subgroup.zpowers x).map B.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩; exact y.2
  · rw [Subgroup.card_map_of_injective B.subtype_injective, Nat.card_zpowers, hx]
  · intro φ
    have hsub : ((Subgroup.zpowers x).map B.subtype).subgroupOf B = Subgroup.zpowers x := by
      exact Subgroup.comap_map_eq_self_of_injective B.subtype_injective _
    rw [hsub]
    apply IsCyclic.subgroup_eq_iff_card_eq.mpr
    rw [Subgroup.card_map_of_injective φ.injective]

end CFSG.LocalAnalysis.RankThreeUC.Section5.CharacteristicPrimeSubgroup
