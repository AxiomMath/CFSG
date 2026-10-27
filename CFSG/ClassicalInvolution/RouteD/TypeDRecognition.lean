module

public import CFSG.ClassicalInvolution.RouteD.TypeDModel
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalReduce

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.Generic (Commutes conjSub)

section Recognition

open CFSG.ClassicalInvolution.Generic (fundamentalSubgroups FundamentalSingleClass InClass LocalOddCentral)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair weakCT_spinPlus)

variable {p f : ℕ} [hp : Fact p.Prime] {G : Type} [Group G]

theorem exists_psi_of_chain_plus {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n p f)
    (hq : 4 ≤ p ^ f) (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin n, edgeD n i j →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) :
    ∃ ψ : spinGroup (quadPlus n (GaloisField p f)) →* G, ψ.ker ≤ Subgroup.center _ ∧
      ∀ k : Fin n, (rankOne (plusDatum n (GaloisField p f) (by have := hadm.2.2; omega)).rootGroup k).map ψ =
        U k := by
  have hf : f ≠ 0 := by have := hadm.2.1; omega
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hn3 : 3 ≤ n := by have := hadm.2.2; omega
  set Gs := ⨆ i, U i with hGs
  have hUle : ∀ i, U i ≤ Gs := fun i => le_iSup U i
  obtain ⟨Ψ, -, hker, -, -, -, hnodes⟩ := weakCT_spinPlus hadm hn3 hF (hF ▸ hq)
    (X := ↥Gs) (fun i => (U i).subgroupOf Gs) (CFSG.ClassicalInvolution.Generic.iSup_subgroupOf_self U)
    (fun i j hij h1 h2 a ha b hb => Subtype.ext (hcomm i j hij h1 h2 a.1
      (Subgroup.mem_subgroupOf.mp ha) b.1 (Subgroup.mem_subgroupOf.mp hb)))
    (fun i j hij => by
      obtain ⟨W, hW⟩ := hpair i j hij
      exact ⟨W.subgroupOf Gs, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_subgroupOf
        ((linearBlockStandardPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
  refine ⟨Gs.subtype.comp Ψ, ?_, fun k => ?_⟩
  · intro x hx
    have : Ψ x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · rw [← Subgroup.map_map, hnodes k, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hUle k)]

end Recognition

section Main

open CFSG.ClassicalInvolution.Generic (fundamentalSubgroups FundamentalSingleClass InClass LocalOddCentral
  LieSystemData IsClassicalMember modelUniv)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [hp : Fact p.Prime] {G : Type} [Group G]

theorem modelUniv_POmegaPlus_eq {n : ℕ} (hn : 3 ≤ n) :
    modelUniv .POmegaPlus n p f hp.out =
      ⟨spinGroup (quadPlus n (GaloisField p f)), plusDatum n (GaloisField p f) hn⟩ := by
  simp only [modelUniv, lieUniversal, hn, ↓reduceDIte]

theorem routeD_typeD_of_chain [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 6 ≤ n)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K₀ z) (hshape : LocalShapeT p f 2 .POmegaPlus (n - 2) Ω z)
    (hP1 : LocalOddCentral Ω {z}) (U : Fin n → Subgroup G) (hUΩ : ∀ k, U k ∈ Ω)
    (hcomm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin n, edgeD n i j →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaPlus ∧ D.rank i = n := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hn3 : 3 ≤ n := by omega
  have hn3' : 3 ≤ n - 2 := by omega
  have hadm : StatedLieAdmissible .POmegaPlus n p f := ⟨hp.out, hf, by show 4 ≤ n; omega⟩
  have hadmY : StatedLieAdmissible .POmegaPlus (n - 2) p f :=
    ⟨hp.out, hf, by show 4 ≤ n - 2; omega⟩
  have hfund : CFSG.ClassicalInvolution.Generic.IsFundTag .POmegaPlus := trivial
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaPlus := trivial
  have e1 := modelUniv_POmegaPlus_eq (p := p) (f := f) hn3
  have e2 := modelUniv_POmegaPlus_eq (p := p) (f := f) hn3'
  have hscT : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus n p f hp.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass _ _ p _ _ hfundM hadm (by decide)
      (by decide)
  have hscY : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus (n - 2) p f hp.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass _ _ p _ _ hfundM hadmY (by decide)
      (by decide)
  have hscT' : FundamentalSingleClass .POmegaPlus (plusDatum n (GaloisField p f) hn3) := by
    revert hscT; rw [e1]; exact id
  have hscY' : FundamentalSingleClass .POmegaPlus (plusDatum (n - 2) (GaloisField p f) hn3') := by
    revert hscY; rw [e2]; exact id
  have hfinY : Finite (modelUniv .POmegaPlus (n - 2) p f hp.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 hp.out hfundM hadmY
  have hM : Nonempty (ExtModel p f .POmegaPlus n .POmegaPlus (n - 2) 2) := by
    show Nonempty (ExtModelU .POmegaPlus .POmegaPlus (modelUniv .POmegaPlus n p f hp.out)
      (modelUniv .POmegaPlus (n - 2) p f hp.out) 2)
    rw [e1, e2]
    exact nonempty_extModelU_plus hn hscT' hscY' hadmY (by omega)
  obtain ⟨M⟩ := hM
  obtain ⟨ψ0, hker0, hψ0⟩ := exists_psi_of_chain_plus hadm (by omega) U hcomm hpair
  have hΩψ0 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) hn3),
      R.map ψ0 ∈ Ω := by
    intro R hR
    obtain ⟨g, hg⟩ := hscT' (rankOne (plusDatum n (GaloisField p f) hn3).rootGroup (zeroD (n := n) (by omega)))
      (rankOne_mem_fundamentalSubgroups_plusDatum hn3 _) R hR
    rw [hg, ← CFSG.ClassicalInvolution.Generic.conjSub_map, hψ0]
    exact hΩ.conjInvariant _ _ (hUΩ _)
  have hψ : ∃ ψ : (modelUniv .POmegaPlus n p f hp.out).K →* G,
      ψ.ker ≤ Subgroup.center (modelUniv .POmegaPlus n p f hp.out).K ∧
      ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p f hp.out).D,
        R.map ψ ∈ Ω := by
    rw [e1]
    exact ⟨ψ0, hker0, hΩψ0⟩
  obtain ⟨ψ, hker, hΩψ⟩ := hψ
  exact routeD_core (by norm_num) hfund hadm hscT (by decide) hfinY M hΩ hK₀ hsingle hconn hz hshape
    hP1 ψ hker hΩψ

end Main

end CFSG.ClassicalInvolution.RouteD
