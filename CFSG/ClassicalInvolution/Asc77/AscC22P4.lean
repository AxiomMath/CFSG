module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.ClassicalInvolution.Asc77.AscT7Z1
public import CFSG.ClassicalInvolution.Asc77.AscT7Z6

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped commutatorElement MatrixGroups

namespace C22P

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


theorem nonempty_pslLayer_of_layerOrth {c : G}
    (hOc : classicalInvolutionOddCore ↥(exactLayer Ω c) = ⊥) (hL : LayerOrthType p f Ω c 6 true) :
    Nonempty (T7Z.PSLLayer p f (exactFamily Ω c)) := by
  obtain ⟨t', n', ht', D, hcard, i, hit, hir⟩ := T7Z.exists_omegaLie_of_layerOrth hOc hL
  have htn : t' = .PSL ∧ n' = 4 := by
    rcases ht' with h | h | h | h | h | h <;> simp_all
  have hie : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · exact absurd (hit.symm.trans h) (by rw [htn.1]; decide)
  exact T7Z.nonempty_pslLayer_of_omegaLie D hcard i (hit.trans htn.1) (hir.trans htn.2) hie

theorem pair_of_member' (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Φ : Set (Subgroup G)}
    (P : T7Z.PSLLayer p f Φ) {K K' L : Subgroup G}
    {RK RK' RL : Subgroup (modelUniv .PSL 4 p f Fact.out).K}
    (hRK : RK ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f Fact.out).D)
    (hRL : RL ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f Fact.out).D)
    (hKR : K = RK.map P.ψ) (hKR' : K' = RK'.map P.ψ) (hLR : L = RL.map P.ψ)
    (eK : Nonempty (↥K ≃* SL(2, GaloisField p f)))
    (eL : Nonempty (↥L ≃* SL(2, GaloisField p f))) {z t e a b : G}
    (hzK : IsUniqueInvolution K z) (htL : IsUniqueInvolution L t) (ha : a ∈ K) (hb : b ∈ K')
    (haa : a * a = z) (hcomm : Commutes K K') (he : e ∈ omegaGen Φ)
    (hec : ∀ y ∈ omegaGen Φ, e * y = y * e) (htab : t = a * b * e) (hne : K ≠ L)
    (hnc : ¬ Commutes K L) :
    (∃ W, LinearBlockStandardPair (GaloisField p f) W RK RL) ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W K L := by
  have have_perf := T7Z.PSLLayer.perfect_U (p := p) (f := f)
  have := T7Z.PSLLayer.finite_U (p := p) (f := f) hp2 hq
  have hU : (⊤ : Subgroup (modelUniv .PSL 4 p f Fact.out).K) ≤
      ⁅(⊤ : Subgroup (modelUniv .PSL 4 p f Fact.out).K),
        (⊤ : Subgroup (modelUniv .PSL 4 p f Fact.out).K)⁆ :=
    (Subgroup.commutator_eq_self (H := (⊤ : Subgroup (modelUniv .PSL 4 p f Fact.out).K))).ge
  have hR₁ : RK ≤ ⁅RK, RK⁆ :=
    RouteD.Gaps.fundPerfect_modelUniv hp2 (by trivial) (T7Z.admissible_psl4 hq)
      (by omega) RK hRK
  have hi₁ := P.injOn_fund hp2 hq hRK hKR eK
  have hi₃ := P.injOn_fund hp2 hq hRL hLR eL
  have hcomm' : Commutes (RK.map P.ψ) (RK'.map P.ψ) := by
    rw [← hKR, ← hKR']
    exact hcomm
  obtain ⟨c₁, hc₁, c₂, hc₂, ho₁, ho₂, -, -, hcc⟩ := T7Z.exists_commuting_lifts P.ψ P.ker_le hU hR₁
    hi₁ hi₃ (hKR ▸ ha) (hKR' ▸ hb) hcomm' (P.range_eq ▸ he)
    (fun y hy => hec y (P.range_eq ▸ hy)) haa hzK.sq hzK.ne_one (hLR ▸ htL.mem) htab htL.sq
    htL.ne_one
  have hne' : RK.map P.ψ ≠ RL.map P.ψ := by
    rw [← hKR, ← hLR]
    exact hne
  have hnc' : ¬ Commutes (RK.map P.ψ) (RL.map P.ψ) := by
    rw [← hKR, ← hLR]
    exact hnc
  obtain ⟨h1, h2⟩ := T7Z.psl_pair_of_lifts hp2 hq (T7Z.admissible_psl4 hq) P.ψ P.ker_le hRK hRL hc₁
    hc₂ ho₁ ho₂ hcc hne' hnc'
  exact ⟨h1, by rw [← hKR, ← hLR] at h2; exact h2⟩

theorem nonempty_equiv_sl2_of_exact {K : Subgroup G} (hst : AscStand p f Ω K)
    (hex : ExactMembers Ω) : ∀ L ∈ Ω, Nonempty (↥L ≃* SL(2, GaloisField p f)) := by
  intro L hL
  obtain ⟨zL, hzL⟩ := hst.hyp.classical L hL
  exact hzL.nonempty_equiv_sl2 (hex L hL)

end C22P

end CFSG.ClassicalInvolution.Asc77
