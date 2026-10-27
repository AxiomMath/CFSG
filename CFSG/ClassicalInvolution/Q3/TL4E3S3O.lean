module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3ODefs
public import CFSG.ClassicalInvolution.Q3.TL4E3S3

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.Blueprint
open scoped commutatorElement

namespace E3S3O

variable {G : Type} [Group G]

theorem conjInvariant_conjClass (K : Subgroup G) : ConjInvariant (CoreAssembly.conjClass K) := by
  rintro n _ ⟨g, rfl⟩
  exact ⟨n * g, conjSub_mul n g K⟩

noncomputable abbrev actW [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {x y : G}
    (hcl : ConjInvariant Ω) (hy : y ∈ Subgroup.centralizer ({x} : Set G))
    (hW : (secOrb Ω K x).map (secAct hcl hy).toMonoidHom = secOrb Ω K x) :
    MulAut ↥(secOrb Ω K x) :=
  ((secAct hcl hy).subgroupMap (secOrb Ω K x)).trans (MulEquiv.subgroupCongr hW)

theorem lieModel_congr {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {t : Assembly.LowTwoRank.StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU) {m p f : ℕ} (h : LieModel A t m p f) : LieModel B t m p f := by
  rcases ht with rfl | rfl <;> rcases h with ⟨ht, hadm, K, hK, hKf, hc, ⟨e'⟩⟩ | h | h | h
  all_goals first
    | exact Or.inl ⟨ht, hadm, K, hK, hKf, hc, ⟨e.symm.trans e'⟩⟩
    | (rcases h with ⟨-, ht, -⟩; simp [chevalleyExceptionalTags, reeTitsTags] at ht)

end E3S3O

section Cit3


@[expose] def TightE3S3OConfig (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u),
      TightEdgeless (secR R u) → (∀ W ∈ WSet (E3.secΩ R u), MuIsoS3 (E3.secΩ R u) W) →
        ¬ TightInO2 (E3.secT htu ht) → Concl163 (secR R u) (E3.secT htu ht) →
      ∀ L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R),
        L ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
          L ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
            (∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J,
              ⁅u * t, y⁆ ∈ oddCoreOf
                (E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J)) →
      ∀ (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (S' : Sylow 2 Y) (R' T W : Subgroup Y),
        tightCore Rd = J → TightStd8R 3 n Rd Sd u (tightCore R) S' R' T W t →
          ∃ (Φ : Set (Subgroup
              ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (u * t))))
            (K K' : Subgroup
              ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (u * t)))
            (k k' : ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (u * t)))
            (σ : MulAut
              ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (u * t))),
            TwinSigma3 Φ K K' k k' σ ∧
              (SecTwinOmega (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (u * t) →
                ∃ (N : Subgroup
                    ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (u * t)))
                  (_ : N.Normal), N = Subgroup.zpowers (k * k') ∧
                    CentOmega3 (↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)
                      (u * t)) ⧸ N)) ∧
              ((LieModel ↥(sigmaFixGen K σ) .PSU 3 3 1 ∨
                  LieModel ↥(sigmaFixGen K σ) .PSL 3 3 1) →
                LieModel (E3.OrbQ (CoreAssembly.conjClass (tightCore R)) J (tightCore R))
                    .PSL 3 3 1 ∨
                  LieModel (E3.OrbQ (CoreAssembly.conjClass (tightCore R)) J (tightCore R))
                    .PSU 3 3 1)

theorem tightE3S3Orth_of_config {n : ℕ} (hOm : Model1524Twin3Om) (hE4 : Model1524Twin3E4)
    (hC : TightE3S3OConfig n) : TightE3S3Orth n := by
  intro Y _ _ R S t J u hF htu ht hedge hμ hO2 h163 L hLπ hLs hLn hc Rd Sd S' R' T W hcore hs hω
  obtain ⟨Φ, K, K', k, k', σ, hcfg, hN, htr⟩ :=
    hC Y R S t J u hF htu ht hedge hμ hO2 h163 L hLπ hLs hLn hc Rd Sd S' R' T W hcore hs
  apply htr
  rcases hω with h4 | hom
  · exact hE4 _ Φ K K' k k' σ hcfg h4
  · exact hOm _ Φ K K' k k' σ hcfg (hN hom)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
