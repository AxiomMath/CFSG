module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryActionRankAlternatives
import CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantElemAbelianFixed
import CFSG.LocalAnalysis.RankThreeUC.Section5.InvolutionMovedBlocks
import CFSG.LocalAnalysis.RankThreeUC.Section5.NotIsPrimePowTwoPowSubOne
import CFSG.LocalAnalysis.RankThreeUC.Section5.TwoPowLeCardDelta
import CFSG.LocalAnalysis.UniquenessCase.UC22P22vb
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CommRankDef
public import CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary.FaithfulPImageVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.PNoncentralizingInvolutionDisplacement

open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.Section5
  CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantAbelianCentralizedByBstar
  CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialSstarNormalizerEqCenter
open scoped commutatorElement

theorem commute_commutator_of {H : Type*} [Group H] {z a b c : H} (hza : z * a * z⁻¹ = c * a)
    (hzb : z * b = b * z) (hcb : c * b = b * c) (hcc : c * (a * b * a⁻¹ * b⁻¹) = (a * b * a⁻¹ * b⁻¹) * c) :
    z * (a * b * a⁻¹ * b⁻¹) = (a * b * a⁻¹ * b⁻¹) * z := by
  have hzb' : z * b * z⁻¹ = b := by rw [hzb]; group
  have hcb' : c⁻¹ * b⁻¹ = b⁻¹ * c⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hcb]
  have hconj : z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ = a * b * a⁻¹ * b⁻¹ := by
    calc z * (a * b * a⁻¹ * b⁻¹) * z⁻¹
        = (z * a * z⁻¹) * (z * b * z⁻¹) * (z * a * z⁻¹)⁻¹ * (z * b * z⁻¹)⁻¹ := by group
      _ = c * a * b * a⁻¹ * (c⁻¹ * b⁻¹) := by rw [hza, hzb']; group
      _ = c * a * b * a⁻¹ * (b⁻¹ * c⁻¹) := by rw [hcb']
      _ = c * (a * b * a⁻¹ * b⁻¹) * c⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := by rw [hcc]; group
  calc z * (a * b * a⁻¹ * b⁻¹) = z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ * z := by group
    _ = (a * b * a⁻¹ * b⁻¹) * z := by rw [hconj]

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem mem_normalizer_twoCoreCommutator (hS : Setting G p P T B) {t : G} (ht : t ∈ T) :
    t ∈ Subgroup.normalizer ((twoCoreCommutator T B : Subgroup G) : Set G) := by
  obtain ⟨s, hs, n, hn, rfl⟩ := (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22vb_five_six T B hS.twoGroup
    hS.abelian hS.oddOrder hS.prod_comm.symm).2 t ht
  obtain ⟨hnT, hnB⟩ := Subgroup.mem_inf.mp hn
  have hnS : n ∈ Subgroup.normalizer ((twoCoreCommutator T B : Subgroup G) : Set G) :=
    NotIsPrimePowTwoPowSubOne.mem_normalizer_commutator_of
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (B ⊔ T) (Subgroup.mem_sup_right hnT)) hnB
  have hsS : s ∈ twoCoreCommutator T B := hs
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer hsS) hnS

theorem mul_comm_of_mem (hc : BinaryActionRankCounterexample G p P T B e ρ) {a b : G} (ha : a ∈ P)
    (hb : b ∈ P) : a * b = b * a :=
  congrArg Subtype.val ((isElemAbelian_of_binary_rank_counterexample hc).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem apply_mem_fixedSubmodule (hc : BinaryActionRankCounterexample G p P T B e ρ) {E : Subgroup G}
    (hEP : E ≤ P) {x : G} (hx : x ∈ P) {u : V} (hu : u ∈ fixedSubmodule ρ E) : ρ x u ∈ fixedSubmodule ρ E := by
  rw [QuadraticSetConjugationTransport.mem_fixedSubmodule_iff] at hu ⊢
  intro d hd
  have h1 : ρ d (ρ x u) = ρ x (ρ d u) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm_of_mem hc (hEP hd) hx]
  rw [h1, hu d hd]

theorem eq_zero_of_apply_eq (hc : BinaryActionRankCounterexample G p P T B e ρ) {E : Subgroup G}
    (hE : E ∈ Delta p P ρ) {x : G} (hxP : x ∈ P) (hxE : x ∉ E) {u : V} (hu : u ∈ fixedSubmodule ρ E)
    (hxu : ρ x u = u) : u = 0 := by
  obtain ⟨hEP, hidx, -⟩ := hE
  have hEK : E ≤ E ⊔ Subgroup.zpowers x := le_sup_left
  have hKP : E ⊔ Subgroup.zpowers x ≤ P := sup_le hEP ((Subgroup.zpowers_le).mpr hxP)
  have hmul := Subgroup.relIndex_mul_relIndex E (E ⊔ Subgroup.zpowers x) P hEK hKP
  rw [hidx] at hmul
  have hEK1 : E.relIndex (E ⊔ Subgroup.zpowers x) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro h
    exact hxE (h (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  have hKP1 : (E ⊔ Subgroup.zpowers x).relIndex P = 1 := by
    have hp := hc.oddPrimeClassTwoAction.setting.prime
    rw [← hmul] at hp
    rcases Nat.prime_mul_iff.mp hp with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact absurd h hEK1
  have hPK : P ≤ E ⊔ Subgroup.zpowers x := Subgroup.relIndex_eq_one.mp hKP1
  let Stab : Subgroup G :=
    { carrier := {g | ρ g u = u}
      mul_mem' := fun {a b} (ha : ρ a u = u) (hb : ρ b u = u) => by
        show ρ (a * b) u = u
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by
        show ρ 1 u = u
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {a} (ha : ρ a u = u) => by
        show ρ a⁻¹ u = u
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hES : E ≤ Stab := fun d hd => (QuadraticSetConjugationTransport.mem_fixedSubmodule_iff ρ E u).mp hu d hd
  have hxS : Subgroup.zpowers x ≤ Stab := (Subgroup.zpowers_le).mpr hxu
  have huP : u ∈ fixedSubmodule ρ P :=
    (QuadraticSetConjugationTransport.mem_fixedSubmodule_iff ρ P u).mpr fun y hy => sup_le hES hxS (hPK hy)
  rw [InvariantElemAbelianFixed.fixedSubmodule_eq_bot hc, Submodule.mem_bot] at huP
  exact huP

theorem exists_linearIndependent_pair (hc : BinaryActionRankCounterexample G p P T B e ρ) {E : Subgroup G}
    (hE : E ∈ Delta p P ρ) :
    ∃ f : Fin 2 → V, LinearIndependent (ZMod 2) f ∧ ∀ j, f j ∈ fixedSubmodule ρ E := by
  obtain ⟨hEP, hidx, hne⟩ := hE
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hPE : ¬ P ≤ E := fun h => by
    rw [Subgroup.relIndex_eq_one.mpr h] at hidx
    exact hc.oddPrimeClassTwoAction.setting.prime.one_lt.ne hidx
  obtain ⟨x, hxP, hxE⟩ := SetLike.not_le_iff_exists.mp hPE
  have hxu : ρ x u ∈ fixedSubmodule ρ E := apply_mem_fixedSubmodule hc hEP hxP hu
  have hxu0 : ρ x u ≠ 0 := by
    intro h
    apply hu0
    have h1 : ρ x⁻¹ (ρ x u) = u := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1, h, map_zero]
  have hxu1 : ρ x u ≠ u := fun h => hu0 (eq_zero_of_apply_eq hc ⟨hEP, hidx, hne⟩ hxP hxE hu h)
  refine ⟨![u, ρ x u], (LinearIndependent.pair_iff' hu0).mpr fun a ha => ?_, Fin.forall_fin_two.mpr ⟨hu, hxu⟩⟩
  rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) a with rfl | rfl
  · rw [zero_smul] at ha
    exact hxu0 ha.symm
  · rw [one_smul] at ha
    exact hxu1 ha.symm

theorem exists_apply_ne_of_inverts (hc : BinaryActionRankCounterexample G p P T B e ρ) {E : Subgroup G}
    (hE : E ∈ Delta p P ρ) {t : G} (ht : ∀ x ∈ P, t * x * t⁻¹ = x⁻¹) :
    ∃ u ∈ fixedSubmodule ρ E, ρ t u ≠ u := by
  have hS := hc.oddPrimeClassTwoAction.setting
  obtain ⟨hEP, hidx, hne⟩ := hE
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hPE : ¬ P ≤ E := fun h => by
    rw [Subgroup.relIndex_eq_one.mpr h] at hidx
    exact hS.prime.one_lt.ne hidx
  obtain ⟨x, hxP, hxE⟩ := SetLike.not_le_iff_exists.mp hPE
  by_contra hall
  push Not at hall
  have hmul : ∀ (a b : G) (w : V), ρ (a * b) w = ρ a (ρ b w) := fun a b w => by rw [map_mul]; rfl
  have hxu : ρ x u ∈ fixedSubmodule ρ E := apply_mem_fixedSubmodule hc hEP hxP hu
  have htx : t * x = x⁻¹ * t := by
    calc t * x = (t * x * t⁻¹) * t := by group
      _ = x⁻¹ * t := by rw [ht x hxP]
  have h1 : ρ x u = ρ x⁻¹ u := by
    calc ρ x u = ρ t (ρ x u) := (hall _ hxu).symm
      _ = ρ (t * x) u := (hmul t x u).symm
      _ = ρ (x⁻¹ * t) u := by rw [htx]
      _ = ρ x⁻¹ (ρ t u) := hmul _ _ _
      _ = ρ x⁻¹ u := by rw [hall u hu]
  have h2 : ρ (x * x) u = u := by
    rw [hmul, h1, ← hmul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hx2E : x * x ∉ E := by
    intro h
    obtain ⟨k, hk⟩ := hS.odd
    have hxp : x ^ p = 1 := (isElemAbelian_of_binary_rank_counterexample hc).2 x hxP
    have hxk : x = (x * x) ^ (k + 1) := by
      rw [← pow_two, ← pow_mul]
      calc x = x ^ p * x := by rw [hxp, one_mul]
        _ = x ^ (p + 1) := (pow_succ x p).symm
        _ = x ^ (2 * (k + 1)) := by congr 1; omega
    have h3 := E.pow_mem h (k + 1)
    rw [← hxk] at h3
    exact hxE h3
  exact hu0 (eq_zero_of_apply_eq hc ⟨hEP, hidx, hne⟩ (P.mul_mem hxP hxP) hx2E hu h2)

end CFSG.LocalAnalysis.RankThreeUC.Section5.PNoncentralizingInvolutionDisplacement

namespace CFSG.LocalAnalysis.RankThreeUC.Section5

open CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantAbelianCentralizedByBstar
  CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialSstarNormalizerEqCenter
  CFSG.LocalAnalysis.RankThreeUC.Section5.PNoncentralizingInvolutionDisplacement
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem lt_commRank_of_not_mem_centralizer (hc : BinaryActionRankCounterexample G p P T B e ρ) {t : G}
    (ht : orderOf t = 2) (htT : t ∈ T) (htP : t ∉ Subgroup.centralizer (P : Set G)) :
    e + 1 < commRank ρ t := by
  classical
  have hS := hc.oddPrimeClassTwoAction.setting
  have hF := hc.faithfulBinaryIrreducibleAction
  have hP : P.Normal := hF.normal
  haveI : FiniteDimensional (ZMod 2) V :=
    CFSG.LinearAlgebra.CoprimeActions.IrreducibleFiniteGroupFiniteDimensional.finiteDimensional_of_irreducible
      ρ hF.irreducible
  haveI : Fintype ↥(Delta p P ρ) := Fintype.ofFinite _
  have h520 := cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc
  set D₀ : Subgroup G := ⁅B, P⁆ with hD₀
  set act := DeltaConjugationAction.act (p := p) hP ρ with hact
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hdec := isInternal_hyperplane_fixedSubmodule_of_binary_rank_counterexample hc
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hdec
  obtain ⟨hind, -⟩ := hdec
  have hΔ := lt_card_Delta hc
  have hΔ2 := InvolutionMovedBlocks.two_mul_succ_lt hc.oddPrimeClassTwoAction.two_lt
    (two_pow_le_card_Delta hc).1 (two_pow_le_card_Delta hc).2
  have hσσ : ∀ E, act t (act t E) = E := fun E => by
    rw [← Equiv.Perm.mul_apply, ← map_mul, htt, map_one, Equiv.Perm.one_apply]
  have hτ : ∀ E : ↥(Delta p P ρ), ∀ v ∈ fixedSubmodule ρ (E : Subgroup G),
      ρ t v ∈ fixedSubmodule ρ ((act t E : ↥(Delta p P ρ)) : Subgroup G) := fun E v hv => by
    rw [hact, ← DeltaConjugationAction.fixed_map hP ρ t E]
    exact Submodule.mem_map_of_mem hv
  have hfixall : ∀ g : G, act g = 1 → ∀ E ∈ Delta p P ρ, g ∈ Subgroup.normalizer (E : Set G) := by
    intro g hg E hE
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : act g ⟨E, hE⟩ = ⟨E, hE⟩ := by rw [hg, Equiv.Perm.one_apply]
    have h2 := congrArg Subtype.val h1
    rw [hact, DeltaConjugationAction.apply_eq] at h2
    exact h2
  have hact1 : ∀ g : G, (∀ E ∈ Delta p P ρ, E.map (MulAut.conj g).toMonoidHom = E) → act g = 1 := by
    intro g hg
    refine Equiv.ext fun E => Subtype.ext ?_
    rw [hact, DeltaConjugationAction.apply_eq, Equiv.Perm.one_apply]
    exact hg E.1 E.2
  have htS : t ∈ Subgroup.normalizer ((twoCoreCommutator T B : Subgroup G) : Set G) :=
    mem_normalizer_twoCoreCommutator hS htT
  by_cases hσ : act t = 1
  ·
    obtain ⟨s, hs, n, hn, hsn⟩ := (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22vb_five_six T B hS.twoGroup
      hS.abelian hS.oddOrder hS.prod_comm.symm).2 t htT
    have hsS : s ∈ twoCoreCommutator T B := hs
    obtain ⟨hnT, hnB⟩ := Subgroup.mem_inf.mp hn
    have hnD : n ∈ Subgroup.normalizer (D₀ : Set G) :=
      NotIsPrimePowTwoPowSubOne.mem_normalizer_commutator_of hnB (hS.normT hnT)
    have hsD : s ∈ Subgroup.normalizer (D₀ : Set G) := by
      have h1 : s = t * n⁻¹ := by rw [hsn, mul_inv_cancel_right]
      rw [h1]
      exact Subgroup.mul_mem _ (hfixall t hσ D₀ h520.1) (Subgroup.inv_mem _ hnD)
    have hs1 : act s = 1 := hact1 s (map_conj_eq_of_mem_normalizer_commutator hc s hsS hsD)
    have hn1 : act n = 1 := by
      have h1 : act n = (act s)⁻¹ * act t := by rw [hsn, map_mul, inv_mul_cancel_left]
      rw [h1, hs1, hσ, inv_one, one_mul]
    obtain ⟨F, hF, hFD⟩ : ∃ F ∈ Delta p P ρ, F ≠ D₀ := by
      haveI : Nontrivial ↥(Delta p P ρ) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨F, hF⟩ := exists_ne (⟨D₀, h520.1⟩ : ↥(Delta p P ρ))
      exact ⟨F.1, F.2, fun h => hF (Subtype.ext h)⟩
    have hnB' : ∀ b ∈ B, n * b = b * n := by
      intro b hb
      have hcB : n * b * n⁻¹ * b⁻¹ ∈ B :=
        B.mul_mem ((Subgroup.mem_normalizer_iff.mp hnB b).mp hb) (B.inv_mem hb)
      have hc1 : act (n * b * n⁻¹ * b⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hn1]
        group
      by_contra hne
      have hne' : n * b * n⁻¹ * b⁻¹ ≠ 1 := fun h => by
        apply hne
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
        exact h
      exact h520.2.2.2.1 _ hcB hne' F hF hFD (hfixall _ hc1 F hF)
    obtain ⟨-, hZ⟩ := isSpecialPGroup_Sstar_and_center_eq_centralizer hc
    have hZB : ∀ g ∈ twoCoreCommutator T B, g ∈ Subgroup.normalizer (D₀ : Set G) →
        conjOnP P hP g ∈ Subgroup.centralizer (Bstar P B : Set (MulAut ↥P)) := by
      intro g hg hgD
      have h1 := conjOnP_mem_center_of_mem_normalizer hc hg hgD
      rw [hZ] at h1
      exact (Subgroup.mem_inf.mp h1).2
    have hnBs : conjOnP P hP n ∈ Subgroup.centralizer (Bstar P B : Set (MulAut ↥P)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro β hβ
      obtain ⟨b, hb, rfl⟩ := (mem_Bstar_iff hP).mp hβ
      rw [← map_mul, ← map_mul, hnB' b hb]
    have hzB : conjOnP P hP t ∈ Subgroup.centralizer (Bstar P B : Set (MulAut ↥P)) := by
      rw [hsn, map_mul]
      exact Subgroup.mul_mem _ (hZB s hsS hsD) hnBs
    have hmem : ∀ s' ∈ twoCoreCommutator T B, t * s' * t⁻¹ * s'⁻¹ ∈ twoCoreCommutator T B :=
      fun s' hs' => Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp htS s').mp hs') (Subgroup.inv_mem _ hs')
    have hD : ∀ s' : G, t * s' * t⁻¹ * s'⁻¹ ∈ Subgroup.normalizer (D₀ : Set G) := by
      intro s'
      refine hfixall _ ?_ D₀ h520.1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hσ]
      group
    obtain ⟨-, -, -, hSB⟩ :=
      CoprimeStarSubgroupStructure.«structure» hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction
    have hle : Sstar P T B ≤ Subgroup.centralizer ({conjOnP P hP t} : Set (MulAut ↥P)) := by
      rw [← hSB, Subgroup.commutator_le]
      intro a ha b hb
      have hab : a * b * a⁻¹ * b⁻¹ ∈ Sstar P T B := by
        have h := Subgroup.commutator_mem_commutator ha hb
        rw [hSB, commutatorElement_def] at h
        exact h
      obtain ⟨s', hs', rfl⟩ := (mem_Sstar_iff hP).mp ha
      have hcZ := conjOnP_mem_center_of_mem_normalizer hc (hmem s' hs') (hD s')
      have hcB := hZB _ (hmem s' hs') (hD s')
      rw [Subgroup.mem_centralizer_singleton_iff, commutatorElement_def]
      refine (commute_commutator_of (c := conjOnP P hP (t * s' * t⁻¹ * s'⁻¹)) ?_
        (Subgroup.mem_centralizer_iff.mp hzB b hb).symm (Subgroup.mem_centralizer_iff.mp hcB b hb).symm
        (mul_comm_of_mem_center hcZ hab)).symm
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      group
    have hzS : ∀ ψ ∈ Sstar P T B, conjOnP P hP t * ψ = ψ * conjOnP P hP t := fun ψ hψ =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hle hψ)).symm
    have hz2 : ∀ y : ↥P, conjOnP P hP t (conjOnP P hP t y) = y := fun y => by
      rw [← MulAut.mul_apply, ← map_mul, htt, map_one, MulAut.one_apply]
    have hz1 : conjOnP P hP t ≠ 1 := by
      intro h
      apply htP
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun ψ : MulAut ↥P => ((ψ ⟨x, hx⟩ : ↥P) : G)) h
      simp only [conjOnP_apply, MulAut.one_apply] at h1
      calc x * t = (t * x * t⁻¹) * t := by rw [h1]
        _ = t * x := by group
    have hinv := inverts_of_commute hc hzS hzB hz2 hz1
    have hinvG : ∀ x ∈ P, t * x * t⁻¹ = x⁻¹ := fun x hx => by
      have h1 := congrArg Subtype.val (hinv ⟨x, hx⟩)
      rw [conjOnP_apply] at h1
      exact h1
    have htact : ∀ E : ↥(Delta p P ρ), ∃ u ∈ fixedSubmodule ρ (E : Subgroup G), ρ t u ≠ u :=
      fun E => exists_apply_ne_of_inverts hc E.2 hinvG
    choose u hu hu' using htact
    have hy_mem : ∀ E : ↥(Delta p P ρ), (ρ t - 1) (u E) ∈ fixedSubmodule ρ (E : Subgroup G) := by
      intro E
      have h1 := hτ E (u E) (hu E)
      rw [hσ, Equiv.Perm.one_apply] at h1
      simpa using Submodule.sub_mem _ h1 (hu E)
    have hy_ne : ∀ E : ↥(Delta p P ρ), (ρ t - 1) (u E) ≠ 0 := fun E h =>
      hu' E (by simpa [sub_eq_zero] using h)
    have hli : LinearIndependent (ZMod 2) (fun E : ↥(Delta p P ρ) => (ρ t - 1) (u E)) :=
      hind.linearIndependent _ hy_mem hy_ne
    have hli' : LinearIndependent (ZMod 2)
        (fun E : ↥(Delta p P ρ) => (⟨(ρ t - 1) (u E), LinearMap.mem_range_self _ _⟩ :
          ↥(LinearMap.range (ρ t - 1)))) :=
      LinearIndependent.of_comp (LinearMap.range (ρ t - 1)).subtype hli
    calc e + 1 < Nat.card ↥(Delta p P ρ) := hΔ
      _ = Fintype.card ↥(Delta p P ρ) := Nat.card_eq_fintype_card
      _ ≤ commRank ρ t := hli'.fintype_card_le_finrank
  ·
    set A : Subgroup (Equiv.Perm ↥(Delta p P ρ)) := (twoCoreCommutator T B).map act with hA
    have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
      rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
      have hss : s * s' * s⁻¹ * s'⁻¹ ∈ twoCoreCommutator T B :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hs hs') (Subgroup.inv_mem _ hs))
          (Subgroup.inv_mem _ hs')
      have h1 := hact1 _ (map_conj_eq_of_mem_normalizer_commutator hc _ hss
        (commutator_mem_normalizer_and_mul_self_mem_normalizer hc s hs s' hs').1)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc act s * act s' = act s * act s' * (act s)⁻¹ * (act s')⁻¹ * (act s' * act s) := by group
        _ = act s' * act s := by rw [h1, one_mul]
    have htrans : ∀ x y : ↥(Delta p P ρ), ∃ a ∈ A, a x = y := by
      intro x y
      obtain ⟨s, hs, hxy⟩ := h520.2.2.2.2.1 x.1 x.2 y.1 y.2
      refine ⟨act s, ⟨s, hs, rfl⟩, Subtype.ext ?_⟩
      rw [hact, DeltaConjugationAction.apply_eq]
      exact hxy.symm
    have hσA : ∀ a ∈ A, act t * a * (act t)⁻¹ ∈ A := by
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨t * s * t⁻¹, (Subgroup.mem_normalizer_iff.mp htS s).mp hs, ?_⟩
      rw [map_mul, map_mul, map_inv]
    have hfix := InvolutionMovedBlocks.two_mul_card_fixed_le hAab htrans hσA hσ
    have hpair : ∀ E : ↥(Delta p P ρ), ∃ f : Fin 2 → V, LinearIndependent (ZMod 2) f ∧
        ∀ j, f j ∈ fixedSubmodule ρ (E : Subgroup G) := fun E => exists_linearIndependent_pair hc E.2
    choose f hf hfW using hpair
    have hmoved := InvolutionMovedBlocks.card_moved_le_finrank_range hind (ρ t) (act t) hσσ hτ f
      (fun E _ => hf E) (fun E _ => hfW E)
    have hsplit : (Finset.univ.filter fun E : ↥(Delta p P ρ) => act t E = E).card +
        (Finset.univ.filter fun E : ↥(Delta p P ρ) => act t E ≠ E).card = Fintype.card ↥(Delta p P ρ) :=
      Finset.card_filter_add_card_filter_not _
    have hcard : Nat.card ↥(Delta p P ρ) = Fintype.card ↥(Delta p P ρ) := Nat.card_eq_fintype_card
    show e + 1 < Module.finrank (ZMod 2) ↥(LinearMap.range (ρ t - 1))
    omega

theorem lt_commRank_of_not_mem_centralizer_of_orderOf_eq_two (hc : BinaryActionRankCounterexample G p P T B e ρ)
    {t : G} (ht : orderOf t = 2) (htP : t ∉ Subgroup.centralizer (P : Set G)) : e + 1 < commRank ρ t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := hc.faithfulBinaryIrreducibleAction.normal
  obtain ⟨T₀, hT₀⟩ := NotIsPrimePowTwoPowSubOne.exists_sylow_coe hc.faithfulBinaryIrreducibleAction.sylow
  have h2 : IsPGroup 2 (Subgroup.zpowers t) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨Q, hQ⟩ := h2.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G T₀ Q
  have htQ : t ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers t)
  rw [← hx, NotIsPrimePowTwoPowSubOne.mem_smul_sylow_iff, hT₀] at htQ
  have hord : orderOf (x⁻¹ * t * x) = 2 := by
    have h := (MulAut.conj x⁻¹).orderOf_eq t
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, ht]
  have hnot : x⁻¹ * t * x ∉ Subgroup.centralizer (P : Set G) := by
    intro h
    apply htP
    have hCn : (Subgroup.centralizer (P : Set G)).Normal := by
      haveI := hP
      exact Subgroup.normal_centralizer
    have h' := hCn.conj_mem _ h x
    rwa [show x * (x⁻¹ * t * x) * x⁻¹ = t by group] at h'
  have h1 := lt_commRank_of_not_mem_centralizer hc hord htQ hnot
  have h3 := commRank_conj ρ x⁻¹ t
  rw [inv_inv] at h3
  rwa [h3] at h1

end CFSG.LocalAnalysis.RankThreeUC.Section5
