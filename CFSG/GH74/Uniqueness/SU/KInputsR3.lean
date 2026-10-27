module

public import CFSG.GH74.Uniqueness.SU.KInputs2
public import CFSG.GH74.Uniqueness.SU.SU5Main

public section

namespace CFSG.GH74.Uniqueness.SU.K

open Subgroup CFSG.Blueprint

@[expose] def KI1r3 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SU0.GHGroup H → pPrimeCore 2 H = ⊥ →
    Open.twoRank H = 3 → center H = ⊥ →
    ∀ (T : Sylow 2 H) (x : H), x ∈ (T : Subgroup H) → orderOf x = 2 →
      Open.pRank 2 (centralizer ({x} : Set H)) = 2 →
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel ↥(generalizedFitting H) .PSL 2 p f ∧
          IsPGL2 ↥(generalizedFitting H ⊔ zpowers x) p f

theorem ki1r3_of_ki1 (hKI1 : KI1) : KI1r3 := by
  intro H _ _ hGH hO hrank hcenter T x hxT hx2 hrk2
  have hJ4 : SU5.IsJ2Type ↥(T : Subgroup H) → False := by
    intro hJ
    obtain ⟨T', x', hemb⟩ := SU5.exists_config_of_isJ2Type hJ
    have h4 := hemb.pRank
    have h1 := SU1.pRank_mono (p := 2) (by norm_num) (le_top : (T : Subgroup H) ≤ ⊤)
    unfold Open.twoRank at hrank
    omega
  rcases hKI1 H hGH hO hrank.ge hcenter T x hxT hx2 hrk2 with ⟨_, hJ⟩ | hB | ⟨_, hJ⟩
  · exact (hJ4 hJ.1).elim
  · exact hB
  · exact (hJ4 hJ.1).elim

@[expose] def KI5b : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) → center K ≠ ⊥ →
    Nonempty ((K ⧸ center K) ≃* CFSG.Theory.Comparator.SzModel 1) →
      (∀ (P : Sylow 2 K), ∀ g ∈ (P : Subgroup K), g ^ 2 ∈ center K → g ^ 2 = 1) ∧
      (∀ (P : Sylow 2 K), ∀ g ∈ (P : Subgroup K), ∀ h ∈ (P : Subgroup K),
        g ^ 2 ∈ center K → h ^ 2 ∈ center K → g * h = h * g)

theorem ki5b_of_ki5 (h : KI5) : KI5b := by
  intro K _ _ hq hZp hZne he
  obtain ⟨-, -, -, -, h5, h6⟩ := h K hq hZp hZne he
  exact ⟨h5, h6⟩

@[expose] def KI7b9 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsTwoAlt X 9 → 4 ≤ Open.twoRank X

theorem ki7b9_of_ki7b (h : KI7b) : KI7b9 := by
  intro X _ _ hX
  have h9 := h 9 (by norm_num) X hX
  omega

end CFSG.GH74.Uniqueness.SU.K
