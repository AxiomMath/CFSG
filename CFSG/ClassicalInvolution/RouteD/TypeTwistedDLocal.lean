module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinPartner
public import CFSG.ClassicalInvolution.RouteD.TypeENodes
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDModel
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairTwisted

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv InClass IsClassicalMember LocalOddCentral ExactMembers
  centralizingMembers)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

theorem mf4_minus {m : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .POmegaMinus m p f) :
    ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus m p f Fact.out).D,
      ∃ R' ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus m p f Fact.out).D,
        ∃ W, LinearBlockStandardPair (GaloisField p f) W R R' := by
  refine exists_partner_fund _ (by decide) (by decide) fun γ hγ => ?_
  obtain ⟨δ, hδ, -, hW⟩ := ModelFacts.exists_standardPair_partner_POmegaMinus (p := p) (f := f) m
    hp2 hadm hγ
  exact ⟨δ, hδ, hW⟩

theorem yData_minus {m : ℕ} (hm : 4 ≤ m) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaMinus m p f) (hq : 4 ≤ p ^ f) :
    YData p f .POmegaMinus m := by
  obtain ⟨hf, hK⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  have hp : p.Prime := Fact.out
  have hsc : FundamentalSingleClass .POmegaMinus (modelUniv .POmegaMinus m p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaMinus m p f hp trivial hadm (by decide) (by decide)
  have hq' : 4 ≤ Nat.card (GaloisField p f) := hK ▸ hq
  have hirr := minusCoeffs_irr p f
  have hk0 : (⟨0, by omega⟩ : Fin (m - 1)).val + 1 < m - 1 := by simp only; omega
  have hR₀ := rankOne_mem_fund_minus hirr hk0
  obtain ⟨W₁, hW₁⟩ := CFSG.ClassicalInvolution.WeakCT.linearBlockStandardPair_minusDatum hirr
    (ModelFacts.two_ne_zero_galoisField f hp2) hm
    (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) rfl (by simp only; omega)
  refine ⟨by decide, hsc, perfectK_of_admissible hp trivial hadm, ?_, ?_, mf4_minus hp2 hadm⟩
  · exact perfect_of_mem_fundamental hsc hR₀ (rankOne_minusDatum_perfect hirr hq' hk0)
  · exact central_of_stdPair hsc hR₀ hW₁

theorem nonempty_fund_minus {m : ℕ} (hm : 4 ≤ m) :
    (fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus m p f Fact.out).D).Nonempty :=
  ⟨_, rankOne_mem_fund_minus (minusCoeffs_irr p f) (k := (⟨0, by omega⟩ : Fin (m - 1)))
    (by simp only; omega)⟩

namespace TCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

omit [Finite G] in
theorem exists_nodes_minus [Finite G] {m : ℕ} (hm : 4 ≤ m) (hp2 : p ≠ 2)
    (c : TCtx p f .POmegaMinus m Ω K z) :
    ∃ j : Fin (m - 2) → Subgroup G, (∀ a, j a ∈ centralizingMembers Ω {z} ∧ j a ≠ K ∧
        ¬ locImg Ω z (j a) ≤ c.d.Q₁) ∧
      (∀ a b : Fin (m - 2), a.val + 1 < b.val → Commutes (j a) (j b)) ∧
      (∀ a b : Fin (m - 2), a.val + 1 = b.val → ∃ W : Subgroup G,
        LinearBlockStandardPair (GaloisField p f) W (j a) (j b)) ∧
      (∀ a, Commutes K (j a)) ∧
      (∀ a : Fin (m - 2), locImg Ω z (j a) =
        (rankOne (minusDatum m (minusCoeffs_irr p f)).rootGroup
          (⟨a.val, by have := a.2; omega⟩ : Fin (m - 1))).map c.d.ψ) := by
  have hirr := minusCoeffs_irr p f
  let nd : Fin (m - 2) → Fin (m - 1) := fun a => ⟨a.val, by have := a.2; omega⟩
  have hlong : ∀ a : Fin (m - 2), (nd a).val + 1 < m - 1 := fun a => by
    have := a.2
    simp only [nd]
    omega
  obtain ⟨j, hj, hjc, hjp, hjK⟩ := c.exists_nodes
    (fun a : Fin (m - 2) => rankOne (minusDatum m hirr).rootGroup (nd a))
    (fun a => rankOne_mem_fund_minus hirr (hlong a))
    (fun a b => a.val + 1 = b.val)
    (fun a b hab h1 h2 => by
      rcases lt_or_gt_of_ne (fun h => hab (Fin.ext h) : a.val ≠ b.val) with hlt | hgt
      · exact fun x hx y hy => CFSG.ClassicalInvolution.WeakCT.commute_rankOne_minusDatum hirr
          (nd a) (nd b) (by simp only [nd]; omega) x hx y hy
      · exact fun x hx y hy => (CFSG.ClassicalInvolution.WeakCT.commute_rankOne_minusDatum hirr
          (nd b) (nd a) (by simp only [nd]; omega) y hy x hx).symm)
    (fun a b hab => CFSG.ClassicalInvolution.WeakCT.linearBlockStandardPair_minusDatum hirr
      (ModelFacts.two_ne_zero_galoisField f hp2) hm (i := nd a) (j := nd b) hab (hlong b))
  refine ⟨j, fun a => ⟨(hj a).1, (hj a).2.1, (hj a).2.2.1⟩, fun a b hab => ?_, hjp, hjK,
    fun a => (hj a).2.2.2⟩
  exact hjc a b (Fin.ne_of_val_ne (by omega)) (by show ¬ (a.val + 1 = b.val); omega)
    (by show ¬ (b.val + 1 = a.val); omega)

theorem exists_partner_minus {m : ℕ} (hm : 4 ≤ m) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaMinus m p f) (c : TCtx p f .POmegaMinus m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaMinus m Ω z) :
    ∃ β ∈ Ω, (∃ t : G, IsClassicalMember p f β t) ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) ∧ HasFixedMember Ω K β z :=
  c.exists_partner hsingle hshape (nonempty_fund_minus hm) (mf4_minus hp2 hadm)

end TCtx

theorem TCtx.nonempty_minus {G : Type} [Group G] [Finite G] {m : ℕ} (hm : 4 ≤ m) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral Ω {z}) (hshape : LocalShapeT p f 2 .POmegaMinus m Ω z) :
    Nonempty (TCtx p f .POmegaMinus m Ω K z) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaMinus m p f := ⟨Fact.out, hf, by show 4 ≤ m; omega⟩
  have hY := yData_minus hm hp2 hadm (by omega : 4 ≤ p ^ f)
  obtain ⟨d⟩ := hshape.nonempty_dictT2 hY.ne_d4 hY.sc hΩ hK hz
  obtain ⟨d', hQ⟩ := exists_dictT2_of_member hY hK hz d
  exact ⟨{
    hp2 := hp2
    hq := hq
    hΩ := hΩ
    hex := hex
    hK := hK
    hz := hz
    hP1 := hP1
    d := d'
    hQ₀ := hQ
    hY := hY }⟩

end CFSG.ClassicalInvolution.RouteD
