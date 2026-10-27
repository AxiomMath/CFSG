module

public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Model
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairModels
public import CFSG.ClassicalInvolution.Balance.QNineShape
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.LieType.Steinberg.TwistedE6

section TwistedE6

variable {p : ℕ} [hp : Fact p.Prime]

theorem standardPair_twistedE6_nodes {f : ℕ} (hadm : StatedLieAdmissible .twistedE6 0 p f) :
    ModelFacts.IsPartner (modelUniv .twistedE6 0 p f hp.out).D.isFiniteType
      (Pi.single (nf 0 : Fin (modelUniv .twistedE6 0 p f hp.out).D.rank) 1)
      (Pi.single (nf 1 : Fin (modelUniv .twistedE6 0 p f hp.out).D.rank) 1) ∧
    ∃ W, LinearBlockStandardPair (GaloisField p f) W
      (CFSG.LieType.CurtisTits.rankOne (modelUniv .twistedE6 0 p f hp.out).D.rootGroup (nf 0))
      (CFSG.LieType.CurtisTits.rankOne (modelUniv .twistedE6 0 p f hp.out).D.rootGroup (nf 1)) := by
  have hf : 1 ≤ f := hadm.2.1
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  obtain ⟨eF⟩ := nonempty_ringEquiv_fixedField_frobQ p f hf hF
  refine ⟨ModelFacts.isPartner_single_single _ ?_ ?_, ?_⟩
  · show Blueprint.Chevalley.Tag.cartan .F4 (nf 0) (nf 1) = -1
    decide
  · show Blueprint.Chevalley.Tag.cartan .F4 (nf 1) (nf 0) = -1
    decide
  · obtain ⟨W, hW⟩ := linearBlockStandardPair_twistedE6_long
      (CFSG.LieType.Steinberg.Exceptional.frobQ p f)
    exact ⟨W, hW.of_ringEquiv eF.symm⟩

theorem exists_standardPair_partner_twistedE6 {f : ℕ} (hadm : StatedLieAdmissible .twistedE6 0 p f)
    {γ : Fin (modelUniv .twistedE6 0 p f hp.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv .twistedE6 0 p f hp.out).D γ) :
    ∃ δ : Fin (modelUniv .twistedE6 0 p f hp.out).D.rank → ℤ,
      IsLongestRoot (modelUniv .twistedE6 0 p f hp.out).D δ ∧
      ModelFacts.IsPartner (modelUniv .twistedE6 0 p f hp.out).D.isFiniteType γ δ ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W
        ((modelUniv .twistedE6 0 p f hp.out).D.rootGroup γ ⊔
          (modelUniv .twistedE6 0 p f hp.out).D.rootGroup (-γ))
        ((modelUniv .twistedE6 0 p f hp.out).D.rootGroup δ ⊔
          (modelUniv .twistedE6 0 p f hp.out).D.rootGroup (-δ)) := by
  obtain ⟨hp01, hpair⟩ := standardPair_twistedE6_nodes hadm
  exact ModelFacts.exists_standardPair_partner_of_nodes
    (ModelFacts.hasBruhatDatum .twistedE6 0 p f hp.out trivial hadm)
    (ModelFacts.cartanOK .twistedE6 0 p f hp.out trivial hadm)
    (ModelFacts.isLongestRoot_single .twistedE6 0 p f hp.out trivial hadm (nf 0)
      (by show 0 < 2; decide))
    (ModelFacts.isLongestRoot_single .twistedE6 0 p f hp.out trivial hadm (nf 1)
      (by show 1 < 2; decide)) hp01 hpair hγ

theorem fundamental_leviBlockImage_of_twistedE6 {t : StatedLieTag} {n e : ℕ}
    (hadm : StatedLieAdmissible t n p e) (ht : t = .twistedE6) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, LeviBlockImage p e R := by
  subst ht
  obtain rfl : n = 0 := hadm.2.2
  intro R hR
  obtain ⟨g, γ, hγ, rfl⟩ := hR
  have hlong : IsLongestRoot (modelUniv .twistedE6 0 p e hp.out).D γ := by
    refine hγ.resolve_right ?_
    rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> cases h1
  obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_twistedE6 hadm hlong
  exact Or.inl ⟨_, _, ModelFacts.linearBlockStandardPair_map_conj hW g⟩

end TwistedE6

section Component

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_member_leviBlockImage_of_twistedE6 (hq : 5 ≤ p ^ f)
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (i : Fin D.card)
    (ht : D.tag i = .twistedE6) :
    ∃ L ∈ centralizingMembers Ω {x}, LeviBlockImage p f (locImg Ω x L) := by
  have hexp : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h
      cases h
  exact exists_member_leviBlockImage_of_model hq D i hexp
    (fundamental_leviBlockImage_of_twistedE6 (D.admissible i) ht)

end Component

end CFSG.ClassicalInvolution.Balance
