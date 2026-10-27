module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk11

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14_7_42_S5S3_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ (l1 T L V ⊔ T) →
      ∀ n : ℕ, 1 < n → A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)) →
        ¬ l1 T L V ≤ K →
        ∃ ρ : ↥H →* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3), Function.Surjective ρ ∧
          ρ.ker = CFSG.Open.pCore 2 ↥H

theorem lemma14_7_42_s5s3_of_F4 (h : Lemma14_7_42_F4) : Lemma14_7_42_S5S3_F4 :=
  fun G _ _ T L V H S K hK hHeq n hn hLie hl1K => by
    obtain ⟨ρ, hρs, hρk, -⟩ := h G T L V H S K hK hHeq n hn hLie hl1K
    exact ⟨ρ, hρs, hρk⟩

end CFSG.Quasithin.H13.L32A.C
