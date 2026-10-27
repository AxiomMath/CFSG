module

public import CFSG.ClassicalInvolution.RouteD.TypeUChain
public import CFSG.Timmesfeld.RankTwo.LevisExceptional

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.Timmesfeld
open scoped MatrixGroups

theorem typeU_standardPair_symm {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] {X : Type} [Group X] {W U V : Subgroup X}
    (h : UnitaryBlockStandardPair K p f W U V) : UnitaryBlockStandardPair K p f W V U := by
  obtain ⟨θ, c, h1, h2, h3⟩ := h
  exact ⟨θ, c, h1, h2, h3.symm⟩

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

structure IsPartnerU (c : UCtx p f 5 Ω K z) (nd : UNodes c) (β : Subgroup G) : Prop where
  mem : β ∈ Ω
  cl : ∃ wβ : G, IsClassicalMember p f β wβ
  nK : ¬ Commutes K β
  pK : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W K β
  n0 : ¬ Commutes β (nd.j 0)
  p0 : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W β (nd.j 0)
  last : Commutes β (nd.j 4)
  mid : ∀ a, 1 ≤ a → a ≤ 2 → Commutes β (nd.j a)

theorem UCtx.exists_partnerU (c : UCtx p f 5 Ω K z) (nd : UNodes c)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) : ∃ β, IsPartnerU c nd β := by
  obtain ⟨β, hβ, hcl, hnK, hpK, hn0, hp0, hlast, hmid⟩ :=
    c.exists_partner nd (by norm_num) hsingle
  exact ⟨β, ⟨hβ, hcl, hnK, hpK, hn0, hp0, hlast, hmid⟩⟩

theorem UCtx.commutes_or_stdpair_end (c : UCtx p f 5 Ω K z) (nd : UNodes c)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G} (hβ : IsPartnerU c nd β)
    {wβ : G} (hwβ : IsClassicalMember p f β wβ) (hcomm : Commute wβ (nd.w 3)) :
    Commutes β (nd.j 3) ∨ ∃ W : Subgroup G,
      UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W β (nd.j 3) := by
  obtain ⟨g, hg⟩ := hsingle (nd.j 1) (nd.mem 1 (by norm_num)).1
  have hβZ : Commutes β (nd.j 1) := hβ.mid 1 le_rfl (by norm_num)
  have hβne : β ≠ nd.j 1 := by
    intro h
    exact hβ.nK (h ▸ nd.commK 1 (by norm_num))
  have h3Z : Commutes (nd.j 3) (nd.j 1) :=
    (nd.far 1 (by norm_num) 3 (by norm_num) (by norm_num)).symm
  have h3ne : nd.j 3 ≠ nd.j 1 := nd.inj 3 (by norm_num) 1 (by norm_num) (by norm_num)
  obtain ⟨hβm, hβne', Rb, ib, hRb, hβR, hyb, hib⟩ :=
    c.exists_rootData_conj hg hβ.mem hβZ hβne hwβ
  obtain ⟨h3m, h3ne', R3, i3, hR3, h3R, hy3, hi3⟩ :=
    c.exists_rootData_conj hg (nd.mem 3 (by norm_num)).1 h3Z h3ne (nd.isCl 3 (by norm_num))
  have hne : conjSub g⁻¹ β ≠ conjSub g⁻¹ (nd.j 3) := by
    intro h
    have h' : β = nd.j 3 := conjSub_injective g⁻¹ h
    have h4 : Commutes (nd.j 3) (nd.j 4) := h' ▸ hβ.last
    exact nd.adj 3 (by norm_num) h4
  have hclβ : IsClassicalMember p f (conjSub g⁻¹ β) (g⁻¹ * wβ * g) := by
    have := IsClassicalMember.conj hwβ g⁻¹
    rwa [inv_inv] at this
  have hcl3 : IsClassicalMember p f (conjSub g⁻¹ (nd.j 3)) (g⁻¹ * nd.w 3 * g) := by
    have := IsClassicalMember.conj (nd.isCl 3 (by norm_num)) g⁻¹
    rwa [inv_inv] at this
  have hc : g⁻¹ * wβ * g * (g⁻¹ * nd.w 3 * g) = g⁻¹ * nd.w 3 * g * (g⁻¹ * wβ * g) := by
    calc g⁻¹ * wβ * g * (g⁻¹ * nd.w 3 * g) = g⁻¹ * (wβ * nd.w 3) * g := by group
      _ = g⁻¹ * (nd.w 3 * wβ) * g := by rw [hcomm.eq]
      _ = g⁻¹ * nd.w 3 * g * (g⁻¹ * wβ * g) := by group
  rcases c.rel_dichotomy hβm h3m hβne' h3ne' hne hclβ hcl3 hc with h | ⟨W, hW⟩
  · left
    exact (commutes_conjSub_iff g⁻¹).mp h
  · right
    refine ⟨conjSub g W, ?_⟩
    have := typeU_standardPair_conjSub hW g
    rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this

omit [Finite G] in
theorem UCtx.chain_U7 (c : UCtx p f 5 Ω K z) (nd : UNodes c) {β : Subgroup G}
    (hβ : IsPartnerU c nd β) (h3 : Commutes β (nd.j 3)) :
    ∃ U : Fin 7 → Subgroup G, (∀ i, U i ∈ Ω) ∧
      (∀ i j : Fin 7, (i : ℕ) + 1 < j → Commutes (U i) (U j)) ∧
      (∀ i j : Fin 7, (j : ℕ) = i + 1 →
        ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (U i) (U j)) := by
  refine ⟨![K, β, nd.j 0, nd.j 1, nd.j 2, nd.j 3, nd.j 4], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact c.hK
    · exact hβ.mem
    all_goals exact (nd.mem _ (by norm_num)).1
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact nd.commK 0 (by norm_num)
    · exact nd.commK 1 (by norm_num)
    · exact nd.commK 2 (by norm_num)
    · exact nd.commK 3 (by norm_num)
    · exact nd.commK 4 (by norm_num)
    · exact hβ.mid 1 le_rfl (by norm_num)
    · exact hβ.mid 2 (by norm_num) le_rfl
    · exact h3
    · exact hβ.last
    · exact nd.far 0 (by norm_num) 2 (by norm_num) (by norm_num)
    · exact nd.far 0 (by norm_num) 3 (by norm_num) (by norm_num)
    · exact nd.far 0 (by norm_num) 4 (by norm_num) (by norm_num)
    · exact nd.far 1 (by norm_num) 3 (by norm_num) (by norm_num)
    · exact nd.far 1 (by norm_num) 4 (by norm_num) (by norm_num)
    · exact nd.far 2 (by norm_num) 4 (by norm_num) (by norm_num)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact hβ.pK
    · exact hβ.p0
    · exact nd.pair 0 (by norm_num)
    · exact nd.pair 1 (by norm_num)
    · exact nd.pair 2 (by norm_num)
    · exact nd.pair 3 (by norm_num)

omit [Finite G] in
theorem UCtx.chain_E6 (c : UCtx p f 5 Ω K z) (nd : UNodes c) {β : Subgroup G}
    (hβ : IsPartnerU c nd β)
    (h3 : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W β (nd.j 3)) :
    ∃ U : Fin 6 → Subgroup G, (∀ i, U i ∈ Ω) ∧
      (∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i → Commutes (U i) (U j)) ∧
      (∀ i j : Fin 6, edgeE 6 i j →
        ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (U i) (U j)) := by
  refine ⟨![nd.j 1, K, nd.j 0, β, nd.j 3, nd.j 4], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact (nd.mem 1 (by norm_num)).1
    · exact c.hK
    · exact (nd.mem 0 (by norm_num)).1
    · exact hβ.mem
    all_goals exact (nd.mem _ (by norm_num)).1
  · intro i j hij h1 h2
    have e0 := nd.commK 0 (by norm_num)
    have e1 := nd.commK 1 (by norm_num)
    have e3 := nd.commK 3 (by norm_num)
    have e4 := nd.commK 4 (by norm_num)
    have b1 := hβ.mid 1 le_rfl (by norm_num)
    have b4 := hβ.last
    have f13 := nd.far 1 (by norm_num) 3 (by norm_num) (by norm_num)
    have f14 := nd.far 1 (by norm_num) 4 (by norm_num) (by norm_num)
    have f03 := nd.far 0 (by norm_num) 3 (by norm_num) (by norm_num)
    have f04 := nd.far 0 (by norm_num) 4 (by norm_num) (by norm_num)
    fin_cases i <;> fin_cases j <;> simp [edgeE] at hij h1 h2 ⊢
    all_goals first
      | exact e0 | exact e0.symm | exact e1 | exact e1.symm | exact e3 | exact e3.symm
      | exact e4 | exact e4.symm | exact b1 | exact b1.symm | exact b4 | exact b4.symm
      | exact f13 | exact f13.symm | exact f14 | exact f14.symm | exact f03 | exact f03.symm
      | exact f04 | exact f04.symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [edgeE] at hij ⊢
    all_goals first
      | (obtain ⟨W, hW⟩ := nd.pair 0 (by norm_num); exact ⟨W, typeU_standardPair_symm hW⟩)
      | exact hβ.pK
      | (obtain ⟨W, hW⟩ := hβ.p0; exact ⟨W, typeU_standardPair_symm hW⟩)
      | exact h3
      | exact nd.pair 3 (by norm_num)

theorem UCtx.five_alternative (c : UCtx p f 5 Ω K z) (nd : UNodes c)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hshape : LocalShapeU p f 5 Ω z) {β : Subgroup G} (hβ : IsPartnerU c nd β) {wβ : G}
    (hwβ : IsClassicalMember p f β wβ) (hcomm : Commute wβ (nd.w 3)) :
    (∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSU ∧ D.rank i = 8) ∨
      ∃ U : Fin 6 → Subgroup G, (∀ i, U i ∈ Ω) ∧
        (∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i → Commutes (U i) (U j)) ∧
        (∀ i j : Fin 6, edgeE 6 i j → ∃ W : Subgroup G,
          UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (U i) (U j)) := by
  rcases c.commutes_or_stdpair_end nd hsingle hβ hwβ hcomm with h3 | h3
  · exact Or.inl (c.lieSystem_of_partner nd (by norm_num) hsingle hconn hshape hβ.mem hβ.pK hβ.p0
      hβ.mid hβ.last h3)
  · exact Or.inr (c.chain_E6 nd hβ h3)

end CFSG.ClassicalInvolution.RouteD
