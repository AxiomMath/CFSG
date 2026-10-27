module

public import CFSG.ClassicalInvolution.Q3.TL3C2
public import CFSG.ClassicalInvolution.Q3.Q3CLKey
public import CFSG.ClassicalInvolution.Q3.TL3C4

public section

namespace CFSG.ClassicalInvolution.Q3.TC

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def nbrAdj (Ω : Set (Subgroup G)) (K J : Subgroup G) : Prop :=
  K ∈ Ω ∧ J ∈ omegaNbr Ω K

@[expose] def SepHyp (Ω : Set (Subgroup G)) : Prop :=
  ∀ {K J J' : Subgroup G}, nbrAdj Ω K J → nbrAdj Ω K J' → J' ∉ orbOf (nbrAdj Ω) K J →
    nbrAdj Ω J J'

theorem mem_omegaNbr_iff (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J) {K J : Subgroup G} :
    J ∈ omegaNbr Ω K ↔ J ∈ Ω ∧ J ≠ K ∧ J ≤ Subgroup.normalizer (K : Set G) := by
  constructor
  · rintro ⟨hJ, hne, R, hR, hRJ, hRN⟩
    refine ⟨hJ, hne, ?_⟩
    have hRs : IsSylow2In R J := Q3CL.Sec7.isSylow2In_of_mem_RSet_of_le hΩ hR hJ hRJ
    have hRJ' : R = J := (hRs.2.2 J le_rfl (h2 J hJ) hRJ).symm
    exact hRJ' ▸ hRN
  · rintro ⟨hJ, hne, hJN⟩
    exact ⟨hJ, hne, J, mem_RSet_of_isPGroup hJ (h2 J hJ), le_rfl, hJN⟩

theorem orbitGraph (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (hsep : SepHyp Ω) :
    OrbitGraph (nbrAdj Ω) where
  symm := fun {K J} h => ⟨h.2.1, Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ h.1 h.2.1 h.2⟩
  irrefl := fun K h => h.2.2.1 rfl
  conj := fun {K J} g h =>
    ⟨hΩ.conjInvariant g K h.1, Asc77.omegaNbr_conj hΩ.conjInvariant h.2 g⟩
  fix := fun {K J} h j hj => by
    have hJN := ((mem_omegaNbr_iff hΩ h2).mp h.2).2.2
    exact conjSub_eq_of_mem_normalizer (hJN hj)
  sep := fun hKJ hKJ' h => hsep hKJ hKJ' h

theorem graphFam (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (hsep : SepHyp Ω)
    {K : Subgroup G} (htr : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (hgen : (⨆ J ∈ Ω, J) = ⊤) (hconn : Disconnected.DConnected Ω) :
    GraphFam Ω (nbrAdj Ω) where
  graph := orbitGraph hΩ h2 hsep
  mem := fun {K J} h => h.1
  conjMem := fun K hK g => hΩ.conjInvariant g K hK
  trans := by
    intro L hL M hM
    obtain ⟨a, rfl⟩ := htr L hL
    obtain ⟨b, rfl⟩ := htr M hM
    refine ⟨b * a⁻¹, by rw [hgen]; exact Subgroup.mem_top _, ?_⟩
    rw [conjSub_mul, conjSub_inv_conjSub]
  conn := by
    intro L hL M hM
    have key : ∀ b, Relation.ReflTransGen (fun M N : Subgroup G =>
        N ∈ Ω ∧ Disconnected.dAdj Ω M N) L b → b ∈ Ω ∧ Relation.ReflTransGen (nbrAdj Ω) L b := by
      intro b hb
      induction hb with
      | refl => exact ⟨hL, Relation.ReflTransGen.refl⟩
      | tail _ hbc ih =>
        rename_i b c
        obtain ⟨hbΩ, hpath⟩ := ih
        obtain ⟨hcΩ, hadj⟩ := hbc
        refine ⟨hcΩ, hpath.tail ⟨hbΩ, ?_⟩⟩
        rcases hadj with h | h
        · exact h
        · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hcΩ hbΩ h
    exact (key M (hconn L hL M hM)).2

end CFSG.ClassicalInvolution.Q3.TC
