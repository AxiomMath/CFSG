module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.ClassicalInvolution.Asc77.AscT7Z6
public import CFSG.ClassicalInvolution.Asc77.WP3Layer
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd

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

section Abstract

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}


theorem nonempty_pslLayer_of_lieSystemData (D : LieSystemData p f X Φ) (hcard : D.card = 1)
    (i : Fin D.card) (hit : D.tag i = .PSL) (hir : D.rank i = 4) (hie : D.exp i = f)
    (hgen : omegaGen Φ = ⊤) : Nonempty (T7Z.PSLLayer p f Φ) := by
  have hsub : Subsingleton (Fin D.card) := by
    rw [hcard]
    infer_instance
  have key : ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e : ℕ)
      (ψ : (modelUniv t k p e Fact.out).K →* X),
      t = .PSL → k = 4 → e = f → ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K →
      ψ.range = omegaGen Φ →
      (∀ L ∈ Φ, ∃ R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D, L = R.map ψ) →
      Nonempty (T7Z.PSLLayer p f Φ) := by
    rintro t k e ψ rfl rfl rfl hker hr hf
    exact ⟨⟨ψ, hker, hr, hf⟩⟩
  refine key _ _ _ (D.hom i) hit hir hie (D.ker_le_center i) ?_ ?_
  · have h1 : ⨆ j, (D.hom j).range = (D.hom i).range :=
      le_antisymm (iSup_le fun j => by rw [Subsingleton.elim j i])
        (le_iSup (fun j => (D.hom j).range) i)
    rw [← h1, D.generate, hgen]
  · intro L hL
    obtain ⟨j, R, hR, hLR⟩ := D.fundamental L hL
    obtain rfl : j = i := Subsingleton.elim j i
    exact ⟨R, hR, hLR⟩

theorem PSLLayer.injOn_fund' (hq : 5 ≤ p ^ f) (P : T7Z.PSLLayer p f Φ)
    {R : Subgroup (modelUniv .PSL 4 p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f Fact.out).D) :
    ∀ x ∈ R, P.ψ x = 1 → x = 1 := fun x hx hψ =>
  fund_noncentral_modelUniv (p := p) (e := f) (t := .PSL) (n := 4) (by trivial)
    (T7Z.admissible_psl4 hq) (by rintro ⟨-, h⟩; omega) R hR x hx
    (P.ker_le (MonoidHom.mem_ker.mpr hψ))

theorem PSLLayer.oddCoreOf_fund (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (P : T7Z.PSLLayer p f Φ)
    {L : Subgroup X} {R : Subgroup (modelUniv .PSL 4 p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f Fact.out).D)
    (hLR : L = R.map P.ψ) : oddCoreOf L = ⊥ := by
  have have_fin := T7Z.PSLLayer.finite_U (p := p) (f := f) hp2 hq
  obtain ⟨eR⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSL)
    (n := 4) (by trivial) (T7Z.admissible_psl4 hq) (by decide) (by decide) hR
  have hinj : Function.Injective (P.ψ.comp R.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (PSLLayer.injOn_fund' hq P hR x.1 x.2 hx)
  obtain ⟨eL⟩ := Balance.nonempty_equiv_of_map_eq R.subtype P.ψ hinj
    (K := L) (by rw [hLR, Subgroup.range_subtype])
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f
    (by rintro rfl; simp at hq)
  have h2F : (2 : GaloisField p f) ≠ 0 := by
    intro h
    have : (2 : ℕ) = 0 ∨ p = 2 := by
      have := (CharP.cast_eq_zero_iff (GaloisField p f) p 2).mp (by exact_mod_cast h)
      exact Or.inr ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
    rcases this with h' | h'
    · omega
    · exact hp2 h'
  have h4F : 4 ≤ Nat.card (GaloisField p f) := by omega
  have hO1 := ModelFacts.LinearAut.oddCore_sl2_eq_bot h2F h4F
  have hO2 : classicalInvolutionOddCore ↥L = ⊥ := by
    have e : (classicalInvolutionOddCore ↥L).map (eL.trans eR).toMonoidHom =
        classicalInvolutionOddCore SL(2, GaloisField p f) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant (eL.trans eR)
    rw [hO1] at e
    exact (Subgroup.map_eq_bot_iff_of_injective _ (eL.trans eR).injective).mp e
  unfold oddCoreOf
  rw [hO2, Subgroup.map_bot]

theorem commutes_of_twins_bot (hΦ : HypOmegaMod p f Φ) {M₁ M₂ : Subgroup X} {z : X}
    (hM₁ : M₁ ∈ Φ) (hM₂ : M₂ ∈ Φ) (hne : M₁ ≠ M₂) (hz₁ : IsUniqueInvolution M₁ z)
    (hz₂ : IsUniqueInvolution M₂ z) (hO : oddCoreOf M₁ = ⊥) : Commutes M₁ M₂ := by
  have h := hΦ.comm_le_oddCore_of_twin hM₁ hM₂ hne hz₁ hz₂
  rw [hO, bot_inf_eq, le_bot_iff] at h
  intro x hx y hy
  have : ⁅x, y⁆ ∈ ⁅M₁, M₂⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [h, Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this

theorem pair_of_member_ne (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (P : T7Z.PSLLayer p f Φ)
    {K K' L : Subgroup X}
    {RK RK' RL : Subgroup (modelUniv .PSL 4 p f Fact.out).K}
    (hRK : RK ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f Fact.out).D)
    (hRL : RL ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f Fact.out).D)
    (hKR : K = RK.map P.ψ) (hKR' : K' = RK'.map P.ψ) (hLR : L = RL.map P.ψ) {z t e a b : X}
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
  have hi₁ := PSLLayer.injOn_fund' hq P hRK
  have hi₃ := PSLLayer.injOn_fund' hq P hRL
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

theorem sup_eq_of_chain (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (P : T7Z.PSLLayer p f Φ)
    {K K' L L' : Subgroup X}
    {RK RK' RL RL' : Subgroup (modelUniv .PSL 4 p f Fact.out).K}
    (hRK : RK ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f Fact.out).D)
    (hRL : RL ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f Fact.out).D)
    (hRL' : RL' ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f Fact.out).D)
    (hKR : K = RK.map P.ψ) (hKR' : K' = RK'.map P.ψ) (hLR : L = RL.map P.ψ)
    (hL'R : L' = RL'.map P.ψ) {z t e a b : X} (hzK : IsUniqueInvolution K z)
    (htL : IsUniqueInvolution L t) (htL' : IsUniqueInvolution L' t) (ha : a ∈ K) (hb : b ∈ K')
    (haa : a * a = z) (hcomm : Commutes K K') (hcomm' : Commutes L L')
    (he : e ∈ omegaGen Φ) (hec : ∀ y ∈ omegaGen Φ, e * y = y * e) (htab : t = a * b * e)
    (hne : K ≠ L) (hnc : ¬ Commutes K L) (hne' : K ≠ L') (hnc' : ¬ Commutes K L') :
    L' ⊔ K ⊔ L = omegaGen Φ := by
  obtain ⟨h1, -⟩ := pair_of_member_ne hp2 hq P hRK hRL hKR hKR' hLR hzK htL ha hb haa hcomm he hec
    htab hne hnc
  obtain ⟨⟨W₁, hW₁⟩, -⟩ := pair_of_member_ne hp2 hq P hRK hRL' hKR hKR' hL'R hzK htL' ha hb haa
    hcomm he hec htab hne' hnc'
  exact T7Z.PSLLayer.sup_eq_omegaGen hp2 hq P hRL' hKR hLR hL'R
    ⟨W₁, linearBlockStandardPair_symm hW₁⟩ h1 hcomm'

end Abstract

end C22P

end CFSG.ClassicalInvolution.Asc77
