module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowDataB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverBasic
public import CFSG.Certificates.Kernel.Th.Spec.DceHyp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1TwoB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCLocal

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block


@[expose] def G24FixedNonsolvable : Prop :=
  ∀ (K : Type) [Group K], Nonempty (K ≃* ↥twoBD) → ∀ α : MulAut K, α ≠ 1 → α * α = 1 →
    ¬ Group.IsSolvable ↥(fixSubgroup α)

@[expose] def Co1AutCentralizerA4 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H), OddCover .Co1 L →
    Co1Pair H L K u → Group.IsSolvable ↥(autCentralizer L K) ∧ ElemBound 4 ↥(autCentralizer L K)

theorem outTwoCovers_co1 (hmult : OddMultTrivial .Co1) : OutTwoCovers [.Co1] := by
  intro s hs H _ M hM
  rcases List.mem_singleton.1 hs with rfl
  have := hM.finite (by decide)
  intro α _
  exact Or.inl (TwoCo1.HypOne.allInner_of_isSporadic
    (isSporadic_of_center_eq_bot (hmult ↥M hM.1 hM.2.1 hM.2.2) hM.2.2) α)

theorem co1_perfect_unique {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hL : IsSporadic ↥L .Co1) (hQ : Co1Pair H L K u) {K'' : Subgroup H} (hK''L : K'' ≤ L)
    (hK''u : ∀ k ∈ K'', k * u = u * k) (hperf : Group.IsPerfect ↥K'')
    (hcard : Nat.card ↥K'' = Nat.card ↥K) : K'' = K := by
  obtain ⟨f⟩ := co1_equiv_GA hL
  have hu2 : orderOf (⟨u, hQ.1⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk, hQ.2.1]
  have hKLc : K.subgroupOf L ≤ Subgroup.centralizer ({(⟨u, hQ.1⟩ : ↥L)} : Set ↥L) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (hQ.2.2.2.1 k (Subgroup.mem_subgroupOf.1 hk))
  have hcardK : Nat.card (K.subgroupOf L) = 251596800 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ.2.2.1).toEquiv]
    exact hQ.2.2.2.2.2
  have hdvd : 251596800 ∣ Nat.card (Subgroup.centralizer ({(⟨u, hQ.1⟩ : ↥L)} : Set ↥L)) := by
    have := Subgroup.card_dvd_of_le hKLc
    rwa [hcardK] at this
  have hs2 : orderOf (f ⟨u, hQ.1⟩) = 2 := by rw [MulEquiv.orderOf_eq, hu2]
  have hdvd' : 251596800 ∣ Nat.card (Subgroup.centralizer ({f ⟨u, hQ.1⟩} : Set GA)) := by
    rw [← card_centralizer_eq_of_mulEquiv_sub GA f]
    exact hdvd
  obtain ⟨ζ⟩ := exists_centralizer_mulEquiv GA f ⟨u, hQ.1⟩ a₁ (co1_isConj_a₁ hs2 hdvd')
  have hq := Quot2Data.comp_equiv_sub C₁ co1_quot2Data ζ
  have hperfK' : Group.IsPerfect ((K.subgroupOf L).subgroupOf (Subgroup.centralizer
      ({(⟨u, hQ.1⟩ : ↥L)} : Set ↥L))) :=
    isPerfect_subgroupOf_of_le hKLc (isPerfect_subgroupOf_of_le hQ.2.2.1 hQ.2.2.2.2.1)
  have hcardK' : Nat.card ((K.subgroupOf L).subgroupOf (Subgroup.centralizer
      ({(⟨u, hQ.1⟩ : ↥L)} : Set ↥L))) = Nat.card twoBD := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKLc).toEquiv, hcardK, card_twoBD]
  have hK''L' : K''.subgroupOf L ≤ Subgroup.centralizer ({(⟨u, hQ.1⟩ : ↥L)} : Set ↥L) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (hK''u k (Subgroup.mem_subgroupOf.1 hk))
  have hperf'' : Group.IsPerfect (K''.subgroupOf L) := isPerfect_subgroupOf_of_le hK''L hperf
  have hcard'' : Nat.card (K''.subgroupOf L) = Nat.card (K.subgroupOf L) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK''L).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ.2.2.1).toEquiv, hcard]
  have hcard2 : Nat.card ((K''.subgroupOf L).subgroupOf (Subgroup.centralizer
      ({(⟨u, hQ.1⟩ : ↥L)} : Set ↥L))) = Nat.card twoBD := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK''L').toEquiv, hcard'', hcardK,
      card_twoBD]
  have heq := hq.eq_of_perfect hperfK' hcardK' (isPerfect_subgroupOf_of_le hK''L' hperf'')
    hcard2
  rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hK''L', inf_eq_left.2 hKLc] at heq
  have heq2 : K''.subgroupOf L = K.subgroupOf L := heq
  rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hK''L, inf_eq_left.2 hQ.2.2.1] at heq2
  exact heq2

theorem involutionFixesNotLam_of_nonsolvable {K : Type} [Group K] {b : ℕ}
    (h : ∀ α : MulAut K, α ≠ 1 → α * α = 1 → ¬ Group.IsSolvable ↥(fixSubgroup α)) :
    InvolutionFixesNotLam K b := fun α h1 h2 =>
  ⟨fun hL => h α h1 h2 (by
      have := hL.1
      exact Group.isSolvable_of_isSolvable_injective (inl_injective' ↥(fixSubgroup α)
        (Multiplicative (ZMod 2)))),
    fun _ hL => h α h1 h2 hL.1⟩

theorem lemma36eDataQ_co1 (hmult : OddMultTrivial .Co1) (hsol : Co1AutCentralizerA4)
    (hfix : G24FixedNonsolvable) : Lemma36eDataQ .Co1 Co1Pair 2 4 where
  m_le := le_rfl
  data H _ _ L K u hcov hQ := by
    have hP : Co1Pair H L K u := hQ
    have hL : IsSporadic ↥L .Co1 := hcov.isSporadic_of_mult hmult
    obtain ⟨huL, hu2, hKL, hKu, hperf, hcard⟩ := hQ
    have hloc := solomonLocal_co1 hL hP
    have hKC : K ≤ L ⊓ centralizer ({u} : Set H) := fun k hk =>
      ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
    obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨu⟩ := co1_model hL hP
    obtain ⟨M⟩ := co1_outModel
    obtain ⟨eK⟩ := M.equiv_D huL hKL hKu Ψ hΨ hΨL hΨu hperf (hcard.trans card_twoBD.symm)
    refine ⟨hu2, huL, hKC, ?_, ?_, (hsol H L K u hcov hP).1, hloc.autCentralizer_two,
      (hsol H L K u hcov hP).2, ?_, ?_, Or.inr ?_⟩
    · rw [Subgroup.characteristic_iff_map_le]
      set C : Subgroup H := L ⊓ centralizer ({u} : Set H) with hC
      intro φ
      have hperfC : Group.IsPerfect (K.subgroupOf C) := isPerfect_subgroupOf_of_le hKC hperf
      have hcardC : Nat.card (K.subgroupOf C) = Nat.card K :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv
      set K₂ : Subgroup H := ((K.subgroupOf C).map φ.toMonoidHom).map C.subtype with hK₂
      have hK₂L : K₂ ≤ L := fun x hx => by
        obtain ⟨z, -, rfl⟩ := hx
        exact z.2.1
      have hK₂u : ∀ k ∈ K₂, k * u = u * k := fun k hk => by
        obtain ⟨z, -, rfl⟩ := hk
        exact mem_centralizer_singleton_iff.1 z.2.2
      have hK₂perf : Group.IsPerfect ↥K₂ := by
        have := hperfC
        have h1 : Group.IsPerfect ((K.subgroupOf C).map φ.toMonoidHom) := Group.IsPerfect.map _
        have := h1
        exact Group.IsPerfect.map _
      have hK₂card : Nat.card ↥K₂ = Nat.card ↥K := by
        rw [hK₂, Subgroup.card_map_of_injective C.subtype_injective,
          Subgroup.card_map_of_injective φ.injective, hcardC]
      have hK₂K : K₂ = K := co1_perfect_unique hL ⟨huL, hu2, hKL, hKu, hperf, hcard⟩ hK₂L hK₂u
        hK₂perf hK₂card
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hmem : ((φ.toMonoidHom y : C) : H) ∈ K₂ := ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rw [hK₂K] at hmem
      exact hmem
    · have hqK : CFSG.Open.IsQuasisimple ↥K :=
        isQuasisimple_of_mulEquiv' eK.symm
          (isQuasisimple_of_simple isSimpleGroup_twoBD ⟨xD, yD, xD_yD_ne⟩)
      exact ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1).2 hqK
    · intro α _
      exact TwoCo1.HypOne.allInner_of_isSporadic hL α
    · exact involutionFixesNotLam_of_nonsolvable fun α h1 h2 => hfix ↥K ⟨eK⟩ α h1 h2
    · obtain ⟨e⟩ := hL
      exact PerfectInvolutions.subgroup e (perfectInvolutions_native a₁_mem_commutator) u huL hu2

end CFSG.EvenSporadicStandard.Induction
