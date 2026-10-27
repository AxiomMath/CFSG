module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13CI8

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  {c : I13Ctx L z t T₀ E Q x β B S α} {π : MulAut ↥E →* Equiv.Perm (Fin 5)}
  {Rs : Subgroup G}

namespace IsRs

variable (hR : c.IsRs Rs) (hπ : EPi E π)
  (hI : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔
    π a ∈ alternatingGroup (Fin 5) ∧ π b = π a)
  (hfix : ∀ φ : MulAut ↥E, BInv E π φ → Nat.card {e : ↥E // φ e = e} = 4)

include hR hπ hI hfix

theorem not_two_dvd_index_caseI : ¬ 2 ∣ Rs.index := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hR.pgroup.exists_le_sylow
  have hEq : Rs = (P : Subgroup G) := by
    by_contra hne
    have hlt : Rs < (P : Subgroup G) := lt_of_le_of_ne hP hne
    have : Group.IsNilpotent (↥(P : Subgroup G)) := P.isPGroup'.isNilpotent
    have hproper : Rs.subgroupOf (P : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hne
      refine le_antisymm hP (fun x hx => ?_)
      have : (⟨x, hx⟩ : ↥(P : Subgroup G)) ∈ Rs.subgroupOf (P : Subgroup G) := htop ▸ mem_top _
      exact this
    obtain ⟨n, hnN, hn⟩ := IsConcreteLE.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (G := ↥(P : Subgroup G)) _ hproper)
    have hnG : ((n : ↥(P : Subgroup G)) : G) ∉ Rs := hn
    have hnP : (n : G) ∈ (P : Subgroup G) := n.2
    have hnorm : ∀ r : G, r ∈ Rs ↔ (n : G) * r * (n : G)⁻¹ ∈ Rs := by
      intro r
      constructor
      · intro hr
        have := (Subgroup.mem_normalizer_iff.1 hnN ⟨r, hP hr⟩).1 (by exact hr)
        exact this
      · intro hr
        have hrP : (n : G) * r * (n : G)⁻¹ ∈ (P : Subgroup G) := hP hr
        have hrP' : r ∈ (P : Subgroup G) := by
          have := mul_mem (mul_mem (inv_mem hnP) hrP) hnP
          simpa [mul_assoc] using this
        have := (Subgroup.mem_normalizer_iff.1 hnN ⟨r, hrP'⟩).2 (by exact hr)
        exact this
    have hQn := hR.normalizes_Qs hπ hI hfix hnorm
    have hnNc : (n : G) ∈ c.Nc := c.mem_Nc.2 (fun q => hQn q)
    have hT2 : IsPGroup 2 (Rs ⊔ zpowers (n : G) : Subgroup G) :=
      P.isPGroup'.to_le (sup_le hP (zpowers_le.2 hnP))
    have hTN : (Rs ⊔ zpowers (n : G) : Subgroup G) ≤ c.Nc :=
      sup_le hR.le_Nc (zpowers_le.2 hnNc)
    have := hR.max _ hT2 hTN le_sup_left
    apply hnG
    rw [← this]
    exact mem_sup_right (mem_zpowers _)
  rw [hEq]
  exact P.not_dvd_index

end IsRs

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
