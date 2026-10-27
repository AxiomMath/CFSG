module

public import CFSG.ClassicalInvolution.RouteD.SmallAKer
public import CFSG.ClassicalInvolution.RouteD.SmallAMiddle
public import CFSG.ClassicalInvolution.RouteD.SmallAPartner
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Final
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Standard

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD.Gaps
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem exists_chain_three (hMFZ : FundNoncentral p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeA p f 3 Ω z) (hP1 : LocalOddCentral Ω {z}) :
    ∃ U : Fin (3 + 2) → Subgroup G, (∀ i, U i ∈ Ω) ∧
      (∀ i j : Fin (3 + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j)) ∧
      ∀ i j : Fin (3 + 2), (j : ℕ) = i + 1 →
        ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (U i) (U j) := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have hF : OddCoverSL3 (GaloisField p f) :=
    CFSG.ClassicalInvolution.ModelFacts.OddCover.noCover_odd_sl3.{0} (GaloisField.card p f hf) hq
  obtain ⟨d⟩ := LocalShapeA.nonempty_dict (by omega) hΩ hK hz hshape
  let c : ACtx p f 3 Ω K z :=
    { hm := by omega, hp2 := hp2, hq := hq, hΩ := hΩ, hex := hex, hK := hK, hz := hz, hP1 := hP1,
      d := d, hF := hF,
      hlift := Or.inr (ShapeADict.kerInvolutionFree_three hp2 hq hΩ hex hK hsingle hz hP1 d) }
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
    · exact commutes_K_of_ne c.hm c.hodd hΩ hex hK hz hP1 c.d hN hNK
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

theorem routeD_typeA_three (hMFZ : FundNoncentral p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeA p f 3 Ω z)
    (hP1 : LocalOddCentral Ω {z}) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSL ∧ D.rank i = 3 + 3 := by
  obtain ⟨U, hUΩ, hcomm, hpair⟩ :=
    exists_chain_three hMFZ hp2 hq hΩ hex hK hsingle hz hshape hP1
  exact routeD_typeA_of_chain hp2 hq (by omega) hΩ hK hsingle hconn hz hshape hP1 U hUΩ hcomm hpair

theorem exists_chain_four (hMFZ : FundNoncentral p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeA p f 4 Ω z) (hP1 : LocalOddCentral Ω {z}) :
    ∃ U : Fin (4 + 2) → Subgroup G, (∀ i, U i ∈ Ω) ∧
      (∀ i j : Fin (4 + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j)) ∧
      ∀ i j : Fin (4 + 2), (j : ℕ) = i + 1 →
        ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (U i) (U j) := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have hF : OddCoverSL3 (GaloisField p f) :=
    CFSG.ClassicalInvolution.ModelFacts.OddCover.noCover_odd_sl3.{0} (GaloisField.card p f hf) hq
  obtain ⟨d⟩ := LocalShapeA.nonempty_dict (by omega) hΩ hK hz hshape
  let c : ACtx p f 4 Ω K z :=
    { hm := by omega, hp2 := hp2, hq := hq, hΩ := hΩ, hex := hex, hK := hK, hz := hz, hP1 := hP1,
      d := d, hF := hF, hlift := Or.inl (by omega) }
  obtain ⟨nd⟩ := c.nonempty_nodes
  obtain ⟨β, hβΩ, ⟨t, hβcl⟩, hnK, ⟨W1, hW1⟩, hnβ0, ⟨W2, hW2⟩, hlast, hmid⟩ :=
    c.exists_partner nd (by omega) hsingle
  have hm1 : Commutes β (nd.j 1) := hmid 1 le_rfl (by omega)
  have hsecond : Commutes β (nd.j 2) :=
    Gaps.ACtx.end_relation_four c nd hMFZ hshape hsingle hβΩ hβcl hnK ⟨W1, hW1⟩ hnβ0 hm1 hlast
  refine ⟨![K, β, nd.j 0, nd.j 1, nd.j 2, nd.j 3], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hK
    · exact hβΩ
    · exact (nd.mem 0 (by omega)).1
    · exact (nd.mem 1 (by omega)).1
    · exact (nd.mem 2 (by omega)).1
    · exact (nd.mem 3 (by omega)).1
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; exact absurd hij (by decide)) | skip
    · exact nd.commK 0 (by omega)
    · exact nd.commK 1 (by omega)
    · exact nd.commK 2 (by omega)
    · exact nd.commK 3 (by omega)
    · exact hm1
    · exact hsecond
    · exact hlast
    · exact nd.far 0 (by omega) 2 (by omega) (by omega)
    · exact nd.far 0 (by omega) 3 (by omega) (by omega)
    · exact nd.far 1 (by omega) 3 (by omega) (by omega)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; exact absurd hij (by decide)) | skip
    · exact ⟨W1, hW1⟩
    · exact ⟨W2, hW2⟩
    · exact nd.pair 0 (by omega)
    · exact nd.pair 1 (by omega)
    · exact nd.pair 2 (by omega)

theorem routeD_typeA_four (hMFZ : FundNoncentral p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeA p f 4 Ω z)
    (hP1 : LocalOddCentral Ω {z}) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSL ∧ D.rank i = 4 + 3 := by
  obtain ⟨U, hUΩ, hcomm, hpair⟩ :=
    exists_chain_four hMFZ hp2 hq hΩ hex hK hsingle hz hshape hP1
  exact routeD_typeA_of_chain hp2 hq (by omega) hΩ hK hsingle hconn hz hshape hP1 U hUΩ hcomm hpair

end CFSG.ClassicalInvolution.RouteD
