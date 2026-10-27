module

public import CFSG.ClassicalInvolution.RouteD.TypeENodes
public import CFSG.ClassicalInvolution.RouteD.TypeERecognition
public import CFSG.ClassicalInvolution.RouteD.TypeEFive

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv InClass IsClassicalMember LocalOddCentral ExactMembers
  centralizingMembers LieSystemData)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def PartnerAt (p f : ℕ) [Fact p.Prime] {r : ℕ} (Ω : Set (Subgroup G))
    (j : Fin r → Subgroup G) (k : Fin r) : Prop :=
  ∃ β ∈ Ω, (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (j k)) ∧
    ∀ a, a ≠ k → Commutes β (j a)

section Residual

variable (p f) (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G)

@[expose] def PartnerPatternE6 : Prop :=
  ∀ j : Fin 5 → Subgroup G, NodeSystem p f (fun a b : Fin 5 => b.val = a.val + 1) Ω K z j →
    PartnerAt p f Ω j 2

@[expose] def PartnerPatternE7 : Prop :=
  ∀ j : Fin 6 → Subgroup G, NodeSystem p f (edgeD 6) Ω K z j →
    PartnerAt p f Ω j 4 ∨ PartnerAt p f Ω j 5

@[expose] def PartnerPatternE8 : Prop :=
  ∀ j : Fin 7 → Subgroup G, NodeSystem p f (edgeE 7) Ω K z j → PartnerAt p f Ω j 6

end Residual

section ChainE6

variable {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem chainE6_of_partner {j : Fin 5 → Subgroup G}
    (hj : NodeSystem p f (fun a b : Fin 5 => b.val = a.val + 1) Ω K z j)
    (hβ : PartnerAt p f Ω j 2) :
    ∃ U : Fin 6 → Subgroup G, (∀ i, U i ∈ Ω) ∧
      (∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i → Commutes (U i) (U j)) ∧
      (∀ i j : Fin 6, edgeE 6 i j →
        ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) := by
  obtain ⟨β, hβΩ, ⟨W₀, hW₀⟩, hβc⟩ := hβ
  have hD : ∀ a b : Fin 5, a ≠ b → ¬ b.val = a.val + 1 → ¬ a.val = b.val + 1 →
      Commutes (j a) (j b) := hj.comm
  refine ⟨![j 0, β, j 1, j 2, j 3, j 4], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    all_goals first | exact hβΩ | exact (hj.mem _).1
  · intro i k hik h1 h2
    have b0 := hβc 0 (by decide)
    have b1 := hβc 1 (by decide)
    have b3 := hβc 3 (by decide)
    have b4 := hβc 4 (by decide)
    fin_cases i <;> fin_cases k <;> simp [edgeE] at hik h1 h2 ⊢
    all_goals first
      | exact b0 | exact b0.symm | exact b1 | exact b1.symm | exact b3 | exact b3.symm
      | exact b4 | exact b4.symm
      | exact hD _ _ (by decide) (by decide) (by decide)
  · intro i k hik
    fin_cases i <;> fin_cases k <;> simp [edgeE] at hik ⊢
    all_goals first
      | exact ⟨W₀, hW₀⟩
      | exact hj.pair _ _ (by decide)

end ChainE6

section ChainE7

variable {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem chainE7_of_partner {j : Fin 6 → Subgroup G}
    (hj : NodeSystem p f (edgeD 6) Ω K z j) (hβ : PartnerAt p f Ω j 4) :
    ∃ U : Fin 7 → Subgroup G, (∀ i, U i ∈ Ω) ∧
      (∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i → Commutes (U i) (U j)) ∧
      (∀ i j : Fin 7, edgeE 7 i j →
        ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) := by
  obtain ⟨β, hβΩ, ⟨W₀, hW₀⟩, hβc⟩ := hβ
  have hD : ∀ a b : Fin 6, a ≠ b → ¬ edgeD 6 a b → ¬ edgeD 6 b a → Commutes (j a) (j b) :=
    hj.comm
  have hP : ∀ a b : Fin 6, edgeD 6 a b →
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (j b) (j a) :=
    fun a b h => by
      obtain ⟨W, hW⟩ := hj.pair a b h
      exact ⟨W, hW.symm⟩
  refine ⟨![β, j 5, j 4, j 3, j 2, j 1, j 0], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hβΩ
    all_goals exact (hj.mem _).1
  · intro i k hik h1 h2
    have b0 := hβc 0 (by decide)
    have b1 := hβc 1 (by decide)
    have b2 := hβc 2 (by decide)
    have b3 := hβc 3 (by decide)
    have b5 := hβc 5 (by decide)
    fin_cases i <;> fin_cases k <;> simp [edgeE] at hik h1 h2 ⊢
    all_goals first
      | exact b0 | exact b0.symm | exact b1 | exact b1.symm | exact b2 | exact b2.symm
      | exact b3 | exact b3.symm | exact b5 | exact b5.symm
      | exact hD _ _ (by decide) (by decide) (by decide)
  · intro i k hik
    fin_cases i <;> fin_cases k <;> simp [edgeE] at hik ⊢
    all_goals first
      | exact ⟨W₀, hW₀⟩
      | exact hP _ _ (by decide)

end ChainE7

section ChainE8

variable {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem chainE8_of_partner {j : Fin 7 → Subgroup G}
    (hj : NodeSystem p f (edgeE 7) Ω K z j) (hβ : PartnerAt p f Ω j 6) :
    ∃ U : Fin 8 → Subgroup G, (∀ i, U i ∈ Ω) ∧
      (∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i → Commutes (U i) (U j)) ∧
      (∀ i j : Fin 8, edgeE 8 i j →
        ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) := by
  obtain ⟨β, hβΩ, ⟨W₀, hW₀⟩, hβc⟩ := hβ
  have hD : ∀ a b : Fin 7, a ≠ b → ¬ edgeE 7 a b → ¬ edgeE 7 b a → Commutes (j a) (j b) :=
    hj.comm
  refine ⟨![j 0, j 1, j 2, j 3, j 4, j 5, j 6, β], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    all_goals first | exact hβΩ | exact (hj.mem _).1
  · intro i k hik h1 h2
    have b0 := hβc 0 (by decide)
    have b1 := hβc 1 (by decide)
    have b2 := hβc 2 (by decide)
    have b3 := hβc 3 (by decide)
    have b4 := hβc 4 (by decide)
    have b5 := hβc 5 (by decide)
    fin_cases i <;> fin_cases k <;> simp [edgeE] at hik h1 h2 ⊢
    all_goals first
      | exact b0 | exact b0.symm | exact b1 | exact b1.symm | exact b2 | exact b2.symm
      | exact b3 | exact b3.symm | exact b4 | exact b4.symm | exact b5 | exact b5.symm
      | exact hD _ _ (by decide) (by decide) (by decide)
  · intro i k hik
    fin_cases i <;> fin_cases k <;> simp [edgeE] at hik ⊢
    all_goals first
      | exact hj.pair _ _ (by decide)
      | exact ⟨W₀, hW₀.symm⟩

end ChainE8


section Relabel

variable {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem NodeSystem.comp_equiv {r : ℕ} {adj : Fin r → Fin r → Prop} {j : Fin r → Subgroup G}
    (hj : NodeSystem p f adj Ω K z j) (σ : Equiv.Perm (Fin r))
    (hσ : ∀ a b, adj (σ a) (σ b) ↔ adj a b) :
    NodeSystem p f adj Ω K z (j ∘ σ) where
  mem a := hj.mem (σ a)
  ne_K a := hj.ne_K (σ a)
  commK a := hj.commK (σ a)
  comm a b hab h1 h2 := hj.comm (σ a) (σ b) (fun e => hab (σ.injective e))
    (fun h => h1 ((hσ a b).mp h)) (fun h => h2 ((hσ b a).mp h))
  pair a b h := hj.pair (σ a) (σ b) ((hσ a b).mpr h)

theorem PartnerAt.comp_equiv {r : ℕ} {j : Fin r → Subgroup G} {k : Fin r}
    (σ : Equiv.Perm (Fin r)) (h : PartnerAt p f Ω j (σ k)) : PartnerAt p f Ω (j ∘ σ) k := by
  obtain ⟨β, hβ, hW, hc⟩ := h
  exact ⟨β, hβ, hW, fun a ha => hc (σ a) (fun e => ha (σ.injective e))⟩

theorem edgeD6_swap : ∀ a b : Fin 6, edgeD 6 (Equiv.swap (4 : Fin 6) 5 a) (Equiv.swap 4 5 b) ↔
    edgeD 6 a b := by
  decide

end Relabel

section Main

variable [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem routeD_typeE6 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 1 .PSL 6 Ω z)
    (hP1 : LocalOddCentral Ω {z}) (hpartner : PartnerPatternE6 p f Ω K z) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E6 ∧ D.rank i = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hadmY : StatedLieAdmissible .PSL 6 p f :=
    ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, by norm_num, by simp, by simp⟩
  have hsc : FundamentalSingleClass .PSL (modelUniv .PSL 6 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .PSL 6 p f hp trivial hadmY (by decide) (by decide)
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT (by decide) hsc hΩ hK hz hshape
  let c : ETCtx p f .PSL 6 Ω K z :=
    { hp2 := hp2, hq := hq, hΩ := hΩ, hex := hex, hK := hK, hz := hz, hP1 := hP1, d := d,
      hF := oddCoverSL3_of_five_le hq, hY := yData_A5 hadmY (by omega) }
  obtain ⟨j, hj⟩ := c.exists_nodeSystem_A5 hadmY
  obtain ⟨U, hUΩ, hcomm, hpair⟩ := chainE6_of_partner hj (hpartner j hj)
  exact routeD_typeE6_of_chain hp2 hq hΩ hK hsingle hconn hz hshape hP1 U hUΩ hcomm hpair

theorem routeD_typeE7 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 1 .POmegaPlus 6 Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (hpartner : PartnerPatternE7 p f Ω K z) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E7 ∧ D.rank i = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hadmY : StatedLieAdmissible .POmegaPlus 6 p f :=
    ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, by norm_num⟩
  have hsc : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaPlus 6 p f hp trivial hadmY (by decide) (by decide)
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT (by decide) hsc hΩ hK hz hshape
  let c : ETCtx p f .POmegaPlus 6 Ω K z :=
    { hp2 := hp2, hq := hq, hΩ := hΩ, hex := hex, hK := hK, hz := hz, hP1 := hP1, d := d,
      hF := oddCoverSL3_of_five_le hq, hY := yData_D6 hadmY (by omega) }
  obtain ⟨j, hj⟩ := c.exists_nodeSystem_D6 hadmY
  rcases hpartner j hj with h4 | h5
  · obtain ⟨U, hUΩ, hcomm, hpair⟩ := chainE7_of_partner hj h4
    exact routeD_typeE7_of_chain hp2 hq hΩ hK hsingle hconn hz hshape hP1 U hUΩ hcomm hpair
  · have hj' := hj.comp_equiv (Equiv.swap (4 : Fin 6) 5) edgeD6_swap
    have h5' : PartnerAt p f Ω (j ∘ Equiv.swap (4 : Fin 6) 5) 4 :=
      PartnerAt.comp_equiv (Equiv.swap (4 : Fin 6) 5) (by rwa [Equiv.swap_apply_left])
    obtain ⟨U, hUΩ, hcomm, hpair⟩ := chainE7_of_partner hj' h5'
    exact routeD_typeE7_of_chain hp2 hq hΩ hK hsingle hconn hz hshape hP1 U hUΩ hcomm hpair

theorem routeD_typeE8 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 1 .E7 0 Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (hpartner : PartnerPatternE8 p f Ω K z) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E8 ∧ D.rank i = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hadmY : StatedLieAdmissible .E7 0 p f := ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, rfl⟩
  have hsc : FundamentalSingleClass .E7 (modelUniv .E7 0 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .E7 0 p f hp trivial hadmY (by decide) (by decide)
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT (by decide) hsc hΩ hK hz hshape
  let c : ETCtx p f .E7 0 Ω K z :=
    { hp2 := hp2, hq := hq, hΩ := hΩ, hex := hex, hK := hK, hz := hz, hP1 := hP1, d := d,
      hF := oddCoverSL3_of_five_le hq, hY := yData_E7 hadmY (by omega) }
  obtain ⟨j, hj⟩ := c.exists_nodeSystem_E7 hadmY
  obtain ⟨U, hUΩ, hcomm, hpair⟩ := chainE8_of_partner hj (hpartner j hj)
  exact routeD_typeE8_of_chain hp2 hq hΩ hK hsingle hconn hz hshape hP1 U hUΩ hcomm hpair


def AdaptedPartnerE (c : ACtx p f 5 Ω K z) : Prop :=
  ∀ nd : Nodes c, ∃ β, IsPartnerE c nd β ∧
    ∀ wβ : G, IsClassicalMember p f β wβ → Commute wβ (nd.w 3)

theorem routeD_typeA_five (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hconn : DeltaConnected Ω) (hz : IsClassicalMember p f K z) (hshape : LocalShapeA p f 5 Ω z)
    (hP1 : LocalOddCentral Ω {z}) (hadapt : ∀ c : ACtx p f 5 Ω K z, AdaptedPartnerE c) :
    (∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSL ∧ D.rank i = 8) ∨
    (∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E6 ∧ D.rank i = 0) := by
  obtain ⟨d⟩ := LocalShapeA.nonempty_dict (by norm_num) hΩ hK hz hshape
  let c : ACtx p f 5 Ω K z :=
    { hm := by norm_num, hp2 := hp2, hq := hq, hΩ := hΩ, hex := hex, hK := hK, hz := hz,
      hP1 := hP1, d := d, hF := oddCoverSL3_of_five_le hq, hlift := Or.inl (by norm_num) }
  obtain ⟨nd⟩ := c.nonempty_nodes
  obtain ⟨β, hβ, hadp⟩ := hadapt c nd
  obtain ⟨wβ, hwβ⟩ := hβ.cl
  rcases c.commutes_or_stdpair_end nd hsingle hβ hwβ (hadp wβ hwβ) with h3 | h3
  · left
    obtain ⟨U, hUΩ, hcomm, hpair⟩ := c.chain_A7 nd hβ h3
    exact routeD_typeA_of_chain hp2 hq (by norm_num) hΩ hK hsingle hconn hz hshape hP1 U hUΩ hcomm
      hpair
  · right
    obtain ⟨U, hUΩ, hcomm, hpair⟩ := c.chain_E6 nd hβ h3
    exact routeD_typeE6_of_chain hp2 hq hΩ hK hsingle hconn hz hshape.toT hP1 U hUΩ hcomm hpair

def EndDichotomyE (c : ACtx p f 5 Ω K z) : Prop :=
  ∀ nd : Nodes c, ∀ β₁ β₂ : Subgroup G, IsPartnerE c nd β₁ → IsMidPartnerE c nd β₂ →
    Commutes β₁ (nd.j 3) ∨ Commutes β₂ (nd.j 1)

theorem routeD_typeA_five_dich (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hconn : DeltaConnected Ω) (hz : IsClassicalMember p f K z) (hshape : LocalShapeA p f 5 Ω z)
    (hP1 : LocalOddCentral Ω {z}) (hdich : ∀ c : ACtx p f 5 Ω K z, EndDichotomyE c) :
    (∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSL ∧ D.rank i = 8) ∨
    (∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E6 ∧ D.rank i = 0) := by
  obtain ⟨d⟩ := LocalShapeA.nonempty_dict (by norm_num) hΩ hK hz hshape
  let c : ACtx p f 5 Ω K z :=
    { hm := by norm_num, hp2 := hp2, hq := hq, hΩ := hΩ, hex := hex, hK := hK, hz := hz,
      hP1 := hP1, d := d, hF := oddCoverSL3_of_five_le hq, hlift := Or.inl (by norm_num) }
  obtain ⟨nd⟩ := c.nonempty_nodes
  obtain ⟨β₁, hβ₁⟩ := c.exists_partnerE nd hsingle
  obtain ⟨β₂, hβ₂⟩ := c.exists_partnerMidE nd hsingle
  rcases hdich c nd β₁ β₂ hβ₁ hβ₂ with h3 | h1
  · left
    obtain ⟨U, hUΩ, hcomm, hpair⟩ := c.chain_A7 nd hβ₁ h3
    exact routeD_typeA_of_chain hp2 hq (by norm_num) hΩ hK hsingle hconn hz hshape hP1 U hUΩ hcomm
      hpair
  · right
    have hj : NodeSystem p f (fun a b : Fin 5 => b.val = a.val + 1) Ω K z (fun a : Fin 5 => nd.j a) := by
      refine ⟨fun a => nd.mem a a.isLt, fun a => nd.ne_K a a.isLt, fun a => nd.commK a a.isLt,
        fun a b hab h1 h2 => ?_, fun a b h => ?_⟩
      · have : a.val + 2 ≤ b.val ∨ b.val + 2 ≤ a.val := by
          have := Fin.val_ne_of_ne hab
          omega
        rcases this with h | h
        · exact nd.far a a.isLt b b.isLt h
        · exact (nd.far b b.isLt a a.isLt h).symm
      · have ha : a.val + 1 < 5 := by have := b.isLt; omega
        have := nd.pair a ha
        rwa [show a.val + 1 = b.val from h.symm] at this
    have hP : PartnerAt p f Ω (fun a : Fin 5 => nd.j a) 2 := by
      refine ⟨β₂, hβ₂.mem, hβ₂.p2, fun a ha => ?_⟩
      have h0 := hβ₂.zero
      have h3 := hβ₂.three
      have h4 := hβ₂.four
      fin_cases a <;> simp at ha ⊢
      all_goals first | exact h0 | exact h1 | exact h3 | exact h4
    obtain ⟨U, hUΩ, hcomm, hpair⟩ := chainE6_of_partner hj hP
    exact routeD_typeE6_of_chain hp2 hq hΩ hK hsingle hconn hz hshape.toT hP1 U hUΩ hcomm hpair

end Main

end CFSG.ClassicalInvolution.RouteD
