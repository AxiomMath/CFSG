module

public import CFSG.ClassicalInvolution.Uniform.UThm2
public import CFSG.ClassicalInvolution.Uniform.U3G2
public import CFSG.ClassicalInvolution.Uniform.U3M11
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Model
public import CFSG.ClassicalInvolution.Uniform.UExact

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups

section SingleClass

variable {M G : Type} [Group M] [Group G]

theorem exists_conj_map_of_conj (ψ : M →* G) {R S : Subgroup M} {g : M} (hg : S = conjSub g R) :
    ∃ g' : G, conjSub g' (R.map ψ) = S.map ψ := by
  refine ⟨ψ g, ?_⟩
  rw [hg]
  exact (map_conj_eq_conjSub_map ψ g R).symm

theorem false_of_singleClass (ψ : M →* G) {fund : Set (Subgroup M)}
    (hsc : ∀ R ∈ fund, ∀ R' ∈ fund, ∃ g : M, R' = conjSub g R) {R S : Subgroup M} (hR : R ∈ fund)
    (hS : S ∈ fund) (hnc : ¬ ∃ g : G, conjSub g (R.map ψ) = S.map ψ) : False := by
  obtain ⟨g, hg⟩ := hsc R hR S hS
  exact hnc (exists_conj_map_of_conj ψ hg)

end SingleClass

section Model

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem false_of_modelPair (hp2 : p ≠ 2) (hΩ : HypOmegaModU (.sl2 p f) Ω) (hex : ExactMembers Ω)
    (hA : ∀ K ∈ Ω, AEmpty Ω K) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m e : ℕ}
    (ht : Generic.IsFundTag t) (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t m p e)
    (ψ : (compModel p e t m).G →* G) (hker : ψ.ker ≤ Subgroup.center (compModel p e t m).G)
    {R S : Subgroup (compModel p e t m).G} (hR : R ∈ (compModel p e t m).fund)
    (hS : S ∈ (compModel p e t m).fund) (hK : R.map ψ ∈ Ω) (hJ : S.map ψ ∈ Ω)
    (hnc : ¬ ∃ g : G, conjSub g (R.map ψ) = S.map ψ) : False := by
  by_cases hG2 : t = .G2
  · have hinj := RouteD.G2D4.injective_of_ker_le_center hp2 (Or.inl hG2) m hadm.2.1 ψ hker
    exact false_of_pair_of_conjInvolutions hΩ hex hA ψ hinj
      (fun z z' hz hz' hz1 hz1' => g2_model_involutions_conj hG2 hp2 hadm hz hz' hz1 hz1') hK hJ
      hnc
  by_cases hD4 : t = .trialityD4
  · have hinj := RouteD.G2D4.injective_of_ker_le_center hp2 (Or.inr hD4) m hadm.2.1 ψ hker
    have hcR : Nat.card R = Nat.card SL(2, GaloisField p f) := by
      rw [← natCard_map_of_injOn ψ (fun x _ h => hinj (by rw [h, map_one]))]
      exact natCard_memberU hΩ hex hK
    have hcS : Nat.card S = Nat.card SL(2, GaloisField p f) := by
      rw [← natCard_map_of_injOn ψ (fun x _ h => hinj (by rw [h, map_one]))]
      exact natCard_memberU hΩ hex hJ
    by_cases hconj : ∃ g, S = R.map (MulAut.conj g).toMonoidHom
    · obtain ⟨g, hg⟩ := hconj
      exact hnc (exists_conj_map_of_conj ψ hg)
    · exact d4OrdersDiffer p t m e hD4 hadm R hR S hS hconj (hcR.trans hcS.symm)
  · exact false_of_singleClass ψ (fun R hR R' hR' =>
      fundamentalSingleClass t m p e Fact.out (isFundTag_modelFacts ht) hadm hG2 hD4 R hR R' hR')
      hR hS hnc

end Model

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem thm4BelowU_of_citBelowT {n : ℕ} (hn : CITBelowT (.sl2 p f) n) : Thm4BelowU p f n := by
  intro hp2 _ G _ _ hG Ω hΩ hO hA K hK J hJ hnc
  obtain ⟨D⟩ := exists_omegaLieU hn hΩ ⟨K, hK⟩ hO hG
  have hex := D.exactMembers hΩ
  obtain ⟨i, R, hR, hKR⟩ := D.fundamental K hK
  obtain ⟨j, S, hS, hJS⟩ := D.fundamental J hJ
  by_cases hij : i = j
  swap
  · intro a ha b hb
    rw [hKR] at ha
    rw [hJS] at hb
    obtain ⟨x, -, rfl⟩ := ha
    obtain ⟨y, -, rfl⟩ := hb
    exact D.commute i j hij x y
  subst hij
  exfalso
  rcases D.valid i with ⟨t, m, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
  · obtain ⟨R', hR', hRR⟩ := exists_map_castHom hc (D.hom i) hR
    obtain ⟨S', hS', hSS⟩ := exists_map_castHom hc (D.hom i) hS
    have hker := castHom_ker_le_center hc (D.hom i) (D.ker_le_center i)
    refine false_of_modelPair hp2 hΩ hex hA ht hadm (castHom hc (D.hom i)) hker hR' hS' ?_ ?_ ?_
    · rw [hRR, ← hKR]
      exact hK
    · rw [hSS, ← hJS]
      exact hJ
    · rw [hRR, hSS, ← hKR, ← hJS]
      exact hnc
  ·
    obtain ⟨R', hR', hRR⟩ := exists_map_castHom hc (D.hom i) hR
    obtain ⟨S', hS', hSS⟩ := exists_map_castHom hc (D.hom i) hS
    refine false_of_singleClass (castHom hc (D.hom i)) (fun R₁ h₁ R₂ h₂ => ⟨1, ?_⟩) hR' hS' ?_
    · rw [Set.mem_singleton_iff.mp h₁, Set.mem_singleton_iff.mp h₂, conjSub_one]
    · rw [hRR, hSS, ← hKR, ← hJS]
      exact hnc
  ·
    obtain ⟨R', hR', hRR⟩ := exists_map_castHom hc (D.hom i) hR
    obtain ⟨S', hS', hSS⟩ := exists_map_castHom hc (D.hom i) hS
    refine false_of_singleClass (castHom hc (D.hom i)) (fun R₁ h₁ R₂ h₂ => ?_) hR' hS' ?_
    · exact m11_singleClass R₁ h₁ R₂ h₂
    · rw [hRR, hSS, ← hKR, ← hJS]
      exact hnc

theorem ihInterfaceU_proved : IHInterfaceU p f :=
  fun _ hn => ⟨thm4BelowU_of_citBelowT hn, thm2BelowU_of_citBelowT hn⟩

theorem ihInterfaceU_three : IHInterfaceU 3 1 :=
  ihInterfaceU_proved (p := 3) (f := 1)

end Main

end CFSG.ClassicalInvolution.Uniform
