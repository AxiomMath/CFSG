module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Tags
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieExc

public section

namespace CFSG.Quasithin.LieOver

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

private theorem lo1_two_le_of_g2 {n f : ℕ} (hadm : StatedLieAdmissible .G2 n 2 f) : 2 ≤ f := by
  have h3 : 3 ≤ 2 ^ f := hadm.2.2.2
  by_contra hc
  have hlt : f < 2 := by omega
  interval_cases f <;> norm_num at h3

theorem asLieTwoAt_g2 :
    AsLieTwoAt .G2 := by
  intro n f X _ _ _ hadm hmod
  have h : ChevalleyExceptionalModel X .G2 2 f :=
    hmod.chevalleyExceptionalModel (by decide)
  unfold SylowProps
  refine ⟨?_, CFSG.QuasithinUnique.Bridge.g2_sylowAutTrivial X f (lo1_two_le_of_g2 hadm) h⟩
  intro T Y hT hTY hY
  exact (CFSG.QuasithinUnique.B113Lie.g2_sylowFacts h hT).2.1 Y hTY hY

theorem asLieTwoAt_trialityD4 :
    AsLieTwoAt .trialityD4 := by
  intro n f X _ _ _ hadm hmod
  have hf : 1 ≤ f := hadm.2.1
  have h : ChevalleyExceptionalModel X .trialityD4 2 f :=
    hmod.chevalleyExceptionalModel (by decide)
  have hsyl : ∀ T : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ →
      CFSG.QuasithinUnique.B113Lie.SylowFacts X T :=
    fun _ hT => CFSG.QuasithinUnique.B113Lie.d4_sylowFacts hf h hT
  unfold SylowProps
  exact ⟨CFSG.QuasithinUnique.B113Lie.overgroups_of_forall_sylowFacts hsyl,
    CFSG.QuasithinUnique.B113Lie.oddAut_of_forall_sylowFacts hsyl⟩

theorem asLieTwoAt_twistedF4 :
    AsLieTwoAt .twistedF4 := by
  intro n f X _ _ _ hadm hmod
  obtain ⟨-, -, hn, -, hodd, hf⟩ := hadm
  subst hn
  have hR : ReeTitsModel X .twistedF4 2 f := by
    rcases hmod with h | h | h | h
    · exact absurd h.1 (by decide)
    · exact absurd h.2.1 (by decide)
    · exact h.2.2
    · exact absurd h.2.1 (by decide)
  have hF : ∀ T : Subgroup X, IsSylowTwoOf T ⊤ →
      CFSG.QuasithinUnique.B113Lie.SylowFacts X T :=
    fun T hT => CFSG.QuasithinUnique.B113Lie.f4_sylowFacts hodd hf hR hT
  exact And.intro (CFSG.QuasithinUnique.B113Lie.overgroups_of_forall_sylowFacts hF)
    (CFSG.QuasithinUnique.B113Lie.oddAut_of_forall_sylowFacts hF)

theorem asLieTwoAt_tits :
    AsLieTwoAt .Tits := by
  intro n f X _ _ _ hadm hmod
  obtain ⟨-, -, hn, -, hf⟩ := hadm
  subst hn
  subst hf
  have hR : ReeTitsModel X .Tits 2 1 := by
    rcases hmod with h | h | h | h
    · exact absurd h.1 (by decide)
    · exact absurd h.2.1 (by decide)
    · exact h.2.2
    · exact absurd h.2.1 (by decide)
  have hF : ∀ T : Subgroup X, IsSylowTwoOf T ⊤ →
      CFSG.QuasithinUnique.B113Lie.SylowFacts X T :=
    fun T hT => CFSG.QuasithinUnique.B113Lie.tits_sylowFacts hR hT
  exact And.intro (CFSG.QuasithinUnique.B113Lie.overgroups_of_forall_sylowFacts hF)
    (CFSG.QuasithinUnique.B113Lie.oddAut_of_forall_sylowFacts hF)

end CFSG.Quasithin.LieOver
