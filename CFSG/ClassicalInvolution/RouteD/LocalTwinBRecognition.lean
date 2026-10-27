module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinBModel
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalReduce

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Generic (Commutes conjSub)

section Recognition

open CFSG.ClassicalInvolution.Generic (fundamentalSubgroups FundamentalSingleClass InClass
  LocalOddCentral LieSystemData IsClassicalMember modelUniv)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair weakCT_spinOdd)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair
  symplecticBlockStandardPair_subgroupOf symplecticBlockStandardPair_le_sup)

variable {p f : ℕ} [hp : Fact p.Prime] {G : Type} [Group G]

theorem exists_psi_of_chain_odd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n p f)
    (hq : 4 ≤ p ^ f) (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 2 = n → j.val + 1 = n →
      ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (U i) (U j)) :
    ∃ ψ : spinGroup (quadOdd n (GaloisField p f)) →* G, ψ.ker ≤ Subgroup.center _ ∧
      ∀ k : Fin n, (rankOne (oddDatum n (GaloisField p f)).rootGroup k).map ψ = U k := by
  have hf : f ≠ 0 := by have := hadm.2.1; omega
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  set Gs := ⨆ i, U i with hGs
  have hUle : ∀ i, U i ≤ Gs := fun i => le_iSup U i
  obtain ⟨Ψ, -, hker, -, -, -, hnodes⟩ := weakCT_spinOdd hadm hF (hF ▸ hq)
    (X := ↥Gs) (fun i => (U i).subgroupOf Gs)
    (CFSG.ClassicalInvolution.Generic.iSup_subgroupOf_self U)
    (fun i j hij a ha b hb => Subtype.ext (hcomm i j hij a.1
      (Subgroup.mem_subgroupOf.mp ha) b.1 (Subgroup.mem_subgroupOf.mp hb)))
    (fun i j hij hj => by
      obtain ⟨W, hW⟩ := hpair i j hij hj
      exact ⟨W.subgroupOf Gs, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_subgroupOf
        ((linearBlockStandardPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
    (fun i j hi hj => by
      obtain ⟨W, hW⟩ := hsp i j hi hj
      exact ⟨W.subgroupOf Gs, symplecticBlockStandardPair_subgroupOf
        ((symplecticBlockStandardPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
  refine ⟨Gs.subtype.comp Ψ, ?_, fun k => ?_⟩
  · intro x hx
    have : Ψ x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · rw [← Subgroup.map_map, hnodes k, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hUle k)]

theorem routeD_typeB_of_chain [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 5 ≤ n)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K₀ z) (hshape : LocalShapeT p f 2 .POmegaOdd (n - 2) Ω z)
    (hP1 : LocalOddCentral Ω {z}) (U : Fin n → Subgroup G)
    (hUΩ : ∀ k : Fin n, k.val + 1 < n → U k ∈ Ω)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 2 = n → j.val + 1 = n →
      ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (U i) (U j)) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaOdd ∧ D.rank i = n := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hn3 : 3 ≤ n := by omega
  have hn3' : 3 ≤ n - 2 := by omega
  have h2 : (2 : GaloisField p f) ≠ 0 := two_ne_zero_galoisField hp2
  have hadm : StatedLieAdmissible .POmegaOdd n p f := ⟨hp.out, hf, hn3, hp2⟩
  have hadmY : StatedLieAdmissible .POmegaOdd (n - 2) p f := ⟨hp.out, hf, hn3', hp2⟩
  have hfund : CFSG.ClassicalInvolution.Generic.IsFundTag .POmegaOdd := trivial
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaOdd := trivial
  have hscT : FundamentalSingleClass .POmegaOdd (modelUniv .POmegaOdd n p f hp.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass _ _ p _ _ hfundM hadm (by decide)
      (by decide)
  have hscY : FundamentalSingleClass .POmegaOdd (modelUniv .POmegaOdd (n - 2) p f hp.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass _ _ p _ _ hfundM hadmY (by decide)
      (by decide)
  have hfinY : Finite (modelUniv .POmegaOdd (n - 2) p f hp.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 hp.out hfundM hadmY
  have hM : Nonempty (ExtModel p f .POmegaOdd n .POmegaOdd (n - 2) 2) :=
    nonempty_extModelU_odd hn h2 hscT hscY hadmY (by omega)
  obtain ⟨M⟩ := hM
  obtain ⟨ψ, hker, hψ⟩ := exists_psi_of_chain_odd hadm (by omega) U hcomm hpair hsp
  have hscT' : FundamentalSingleClass .POmegaOdd (oddDatum n (GaloisField p f)) := hscT
  have hΩψ : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p f)),
      R.map ψ ∈ Ω := by
    intro R hR
    obtain ⟨g, hg⟩ := hscT' (rankOne (oddDatum n (GaloisField p f)).rootGroup
      (zeroB (n := n) (by omega)))
      (rankOne_mem_fundamentalSubgroups_oddDatum hn3 (by simp only [zeroB_val]; omega)) R hR
    rw [hg, ← CFSG.ClassicalInvolution.Generic.conjSub_map, hψ]
    exact hΩ.conjInvariant _ _ (hUΩ _ (by simp only [zeroB_val]; omega))
  exact routeD_core (by norm_num) hfund hadm hscT (by decide) hfinY M hΩ hK₀ hsingle hconn hz
    hshape hP1 ψ hker hΩψ

end Recognition

end CFSG.ClassicalInvolution.RouteD
