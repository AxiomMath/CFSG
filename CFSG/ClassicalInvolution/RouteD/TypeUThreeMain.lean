module

public import CFSG.ClassicalInvolution.RouteD.TypeUThreeKer
public import CFSG.ClassicalInvolution.RouteD.TypeUThreePartner
public import CFSG.ClassicalInvolution.RouteD.TypeUThreeMiddle

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.RouteD.Gaps

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem exists_chain_typeU_three (hMFZ : FundNoncentral p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeU p f 3 Ω z) (hP1 : LocalOddCentral Ω {z}) :
    ∃ U : Fin (3 + 2) → Subgroup G, (∀ i, U i ∈ Ω) ∧
      (∀ i j : Fin (3 + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j)) ∧
      ∀ i j : Fin (3 + 2), (j : ℕ) = i + 1 →
        ∃ W : Subgroup G,
          UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (U i) (U j) := by
  obtain ⟨d⟩ := LocalShapeU.nonempty_dict hp2 (by omega) hΩ hK hz hshape
  let c : UCtx p f 3 Ω K z :=
    { hm := by omega, hp2 := hp2, hq := hq, hΩ := hΩ, hex := hex, hK := hK, hz := hz, hP1 := hP1,
      d := d,
      hlift := Or.inr (ShapeUDict.kerInvolutionFree_three hp2 hq hΩ hex hK hsingle hz hP1 d) }
  obtain ⟨nd⟩ := c.nonempty_nodes
  obtain ⟨β, hβΩ, ⟨t, hβcl⟩, hnK, hW1, hnβ0, ⟨W2, hW2⟩, hlast⟩ := c.exists_partner_three nd hsingle
  obtain ⟨N, hN, hNK, hβN, ⟨W3, hW3⟩, ⟨W4, hW4⟩⟩ :=
    c.exists_middle_three nd hMFZ hshape hsingle hβΩ hβcl hnK hW1 hnβ0 hlast
  obtain ⟨W1, hW1⟩ := hW1
  refine ⟨![K, β, nd.j 0, N, nd.j 2], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hK
    · exact hβΩ
    · exact (nd.mem 0 (by omega)).1
    · exact hN.1
    · exact (nd.mem 2 (by omega)).1
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; exact absurd hij (by decide)) | skip
    · exact nd.commK 0 (by omega)
    · exact typeU_commutes_K_of_ne c.hp2 c.hq c.hm hΩ hex hK hz hP1 c.d hN hNK
    · exact nd.commK 2 (by omega)
    · exact hβN
    · exact hlast
    · exact nd.far 0 (by omega) 2 (by omega) (by omega)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; exact absurd hij (by decide)) | skip
    · exact ⟨W1, hW1⟩
    · exact ⟨W2, hW2⟩
    · exact ⟨W3, hW3⟩
    · exact ⟨W4, hW4⟩

theorem routeD_typeU_three (hMFZ : FundNoncentral p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeU p f 3 Ω z)
    (hP1 : LocalOddCentral Ω {z}) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSU ∧ D.rank i = 3 + 3 := by
  obtain ⟨U, hUΩ, hcomm, hpair⟩ :=
    exists_chain_typeU_three hMFZ hp2 hq hΩ hex hK hsingle hz hshape hP1
  exact routeD_typeU_of_chain hp2 hq (by omega) hΩ hex hK hsingle hconn hz hshape hP1 U hUΩ hcomm
    hpair

end CFSG.ClassicalInvolution.RouteD
