module

public import CFSG.ClassicalInvolution.Q3.Q3YAbs
public import CFSG.ClassicalInvolution.Q3.Generation
public import CFSG.ClassicalInvolution.Uniform.U3M11

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank

section Members

variable {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem LieSystemData3.commute_or_same (D : LieSystemData3 ι X Φ)
    {L L' : Subgroup X} (hL : L ∈ Φ) (hL' : L' ∈ Φ) :
    (∀ a ∈ L, ∀ b ∈ L', a * b = b * a) ∨
      ∃ i, ∃ R ∈ (D.kind i).fund, ∃ R' ∈ (D.kind i).fund,
        L = R.map (D.hom i) ∧ L' = R'.map (D.hom i) := by
  obtain ⟨i, R, hR, rfl⟩ := D.fundamental L hL
  obtain ⟨j, R', hR', rfl⟩ := D.fundamental L' hL'
  by_cases hij : i = j
  · subst hij
    exact Or.inr ⟨i, R, hR, R', hR', rfl, rfl⟩
  · refine Or.inl ?_
    rintro _ ⟨r, -, rfl⟩ _ ⟨r', -, rfl⟩
    exact D.commute i j hij r r'

theorem LieSystemData3.exists_conj_of_not_commute (D : LieSystemData3 ι X Φ)
    (hD : SingleClassComponents3 D) {L L' : Subgroup X} (hL : L ∈ Φ) (hL' : L' ∈ Φ)
    (hnc : ¬ ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) : ∃ g : X, L' = conjSub g L := by
  rcases D.commute_or_same hL hL' with h | ⟨i, R, hR, R', hR', rfl, rfl⟩
  · exact absurd h hnc
  · obtain ⟨g, hg⟩ := hD i R hR R' hR'
    refine ⟨D.hom i g, ?_⟩
    rw [hg]
    exact (conjSub_map _ _ _).symm

end Members

namespace Q3Y

section Exclusion

theorem false_of_comp_model_G2D4 {c : CompData} {X : Type} [Group X] (hom : c.G →* X)
    (hker : hom.ker ≤ Subgroup.center c.G) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (ht : t = .G2 ∨ t = .trialityD4) (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hc : c = CompData.model t n)
    (heven : Even (Nat.card c.G)) {z : X} (hz1 : z ≠ 1) (hzc : ∀ x : X, x * z = z * x)
    (hF : ∀ F : Subgroup X, IsElemAbelian 2 F → Nat.card F = 4 → z ∈ F) : False := by
  subst hc
  have hcen : Subgroup.center (CompData.model t n).G = ⊥ := by
    rcases ht with rfl | rfl
    · exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    · exact exc3_center_trialityD4 n Nat.prime_three
  have hfin : Finite (CompData.model t n).G :=
    ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three hfund hadm
  have hq : CFSG.Open.IsQuasisimple (CompData.model t n).G :=
    ModelFacts.isQuasisimple_modelUniv t n 3 1 Nat.prime_three hfund hadm
  exact false_of_central_component hom hker hcen (isSimpleGroup_of_center_eq_bot hq hcen)
    (exists_noncomm_of_isQuasisimple hq) heven hz1 hzc hF

end Exclusion

end Q3Y

section Single

variable {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem LieSystemData3.singleClassComponents3_of_central (D : LieSystemData3 ι X Φ)
    {z : X} (hz1 : z ≠ 1) (hzc : ∀ x : X, x * z = z * x)
    (hF : ∀ F : Subgroup X, IsElemAbelian 2 F → Nat.card F = 4 → z ∈ F) :
    SingleClassComponents3 D := by
  intro i
  have heven : Even (Nat.card (D.kind i).G) := by
    obtain ⟨R, -, hRΦ⟩ := D.meets i
    have h24 := D.card_eq _ hRΦ
    have h1 : Nat.card (R.map (D.hom i)) ∣ Nat.card R := Subgroup.card_map_dvd R (D.hom i)
    have h2 : Nat.card R ∣ Nat.card (D.kind i).G := Subgroup.card_subgroup_dvd_card R
    have h3 : 24 ∣ Nat.card (D.kind i).G := h24 ▸ h1.trans h2
    exact even_iff_two_dvd.mpr (dvd_trans (by norm_num) h3)
  rcases D.valid i with ⟨t, n, hfund, hadm, hc⟩ | hc | hc
  · by_cases ht : t = .G2 ∨ t = .trialityD4
    · exact (Q3Y.false_of_comp_model_G2D4 (D.hom i) (D.ker_le_center i) ht hfund hadm hc heven hz1
        hzc hF).elim
    · push Not at ht
      rw [hc]
      exact ModelFacts.fundamentalSingleClass t n 3 1 Nat.prime_three hfund hadm ht.1 ht.2
  · rw [hc]
    intro R hR R' hR'
    rw [Set.mem_singleton_iff.mp hR, Set.mem_singleton_iff.mp hR']
    exact ⟨1, by simp⟩
  · rw [hc]
    exact Uniform.m11_singleClass

end Single

end CFSG.ClassicalInvolution.Q3
