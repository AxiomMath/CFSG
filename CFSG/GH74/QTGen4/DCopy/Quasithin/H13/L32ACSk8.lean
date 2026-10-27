module

public import CFSG.Quasithin.H13.L32ACSk8
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk7

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14_7_32_L2_red_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, ¬ T ≤ Subgroup.normalizer (K : Set G) →
      ((∃ n : ℕ, IsPSL 2 2 n (cStar K)) ∨ IsAlt 5 (cStar K)) → L2Red G T L V K

@[expose] def Lemma14_7_32_L2_mod_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V K : Subgroup G), L2Red G T L V K → L2CaseOne G T L V

@[expose] def Lemma14_7_32_L2_loc_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V K : Subgroup G), L2Red G T L V K →
    L2CaseOne G T L V → False

theorem lemma14_7_32_L2_of_F4 (h1 : Lemma14_7_32_L2_red_F4) (h2 : Lemma14_7_32_L2_mod_F4)
    (h3 : Lemma14_7_32_L2_loc_F4) : Lemma14_7_32_L2_F4 := by
  intro G _ _ T L V H S K hK hT
  have key : ((∃ n : ℕ, IsPSL 2 2 n (cStar K)) ∨ IsAlt 5 (cStar K)) → False := fun h => by
    have hred := h1 G T L V H S K hK hT h
    exact h3 G T L V K hred (h2 G T L V K hred)
  exact ⟨fun n hn => key (Or.inl ⟨n, hn⟩), fun h => key (Or.inr h)⟩

end CFSG.Quasithin.H13.L32A.C
