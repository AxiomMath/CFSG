module

public import CFSG.GH74.Generic.S1.Front
public import CFSG.GH74.Generic.S3.LeavesR
public import CFSG.GH74.Constrained
public import CFSG.GH74.Generic.S45.PartA
public import CFSG.LocalAnalysis.ComponentClassification.LocalB

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint Subgroup

theorem onlyInvX_of_centralizer_eq {G : Type} [Group G] [Finite G] {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)}
    (h : centralizer (K : Set (CentralizerBar x)) = Subgroup.zpowers (xbar x)) : S3.OnlyInvX x K := by
  intro u hu hu2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : orderOf (xbar x) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact xbar_mul_self hx) (xbar_ne_one hx)
  have hu' : u ∈ Subgroup.zpowers (xbar x) := h ▸ hu
  rcases (CFSG.ComponentClassification.LocalB.mem_zpowers_iff_of_involution (xbar x) u hx2).1 hu' with
    h1 | h1
  · rw [h1, orderOf_one] at hu2
    omega
  · exact h1

theorem S1.S1Front.onlyInvX {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)}
    (h : S1.S1Front G x K) (hx : orderOf x = 2) : S3.OnlyInvX x K :=
  onlyInvX_of_centralizer_eq hx h.cent_eq

theorem S45.onlyInvX {G : Type} [Group G] [Finite G] (hKf : S45.B_S45_KFacts) (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hKc : IsComponent K) (hj : S45.IsJ1OrRee ↥K)
    (hnot : xbar x ∉ K) : S3.OnlyInvX x K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : S45.KData (CentralizerBar x) K (xbar x) :=
    { gen4 := gen4_centralizerBar hgen x
      oddcore := pPrimeCore_quotient_pPrimeCore_eq_bot _ 2
      central := fun g => xbar_comm x g
      sq := xbar_mul_self hx
      ne := xbar_ne_one hx
      comp := hKc
      notin := hnot
      facts := hKf ↥K hj }
  exact onlyInvX_of_centralizer_eq hx (hd.centralizer_eq_zpowers (S45.card_D_eq_two hs hn hx hd))

end CFSG.GH74.Generic
