module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp6Orb
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieSp6

open Polynomial CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {K : Type} [Field K]

theorem proj_injective_of_card_two [Finite K] (hK : Nat.card K = 2) :
    Function.Injective (proj 3 K) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  unfold proj
  rw [QuotientGroup.ker_mk', CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK (Fin 3 ⊕ Fin 3),
    Subgroup.bot_subgroupOf]

theorem exists_noncomm_of_simple_not_prime {S : Type} [Group S] [IsSimpleGroup S]
    (hc : ¬ (Nat.card S).Prime) : ∃ a b : S, a * b ≠ b * a := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  letI : CommGroup S := { ‹Group S› with mul_comm := fun a b => h a b }
  exact hc ((CommGroup.is_simple_iff_prime_card (α := S)).1 ‹IsSimpleGroup S›)

theorem card_alternating_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  rfl

theorem glaPPrimeCore_eq_bot_of_simple_dvd {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    {p : ℕ} (hp : p.Prime) (hpT : p ∣ Nat.card T) : GLAPPrimeCore p T = ⊥ := by
  refine le_bot_iff.1 (sSup_le ?_)
  rintro N ⟨hN, hcop⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · rw [h]
  · exfalso
    rw [h, Subgroup.card_top] at hcop
    have hg := Nat.Coprime.gcd_eq_one hcop
    rw [Nat.gcd_eq_left hpT] at hg
    exact hp.ne_one hg

theorem components_A6 [Finite K] (hK : Nat.card K = 2) {x : StatedSp 3 K} (hx : x ^ 3 = 1)
    (hx1 : x ≠ 1) (blocks : SpPrimaryBlocks 2 1 3 x (proj 3 K x))
    {J : Subgroup (StatedProj (StatedSp 3 K))}
    (hJ : GLAPComponent 3 (fixSubgroup (MulAut.conj (proj 3 K x))) J) :
    Nonempty (PSimple 3 J ≃* alternatingGroup (Fin 6)) := by
  classical
  haveI : Finite ↥(reciprocalOrbits (spEnd x)) :=
    ((Finset.finite_toSet (primaryFactors (spEnd x))).image _).to_subtype
  let A : ↥(reciprocalOrbits (spEnd x)) → Subgroup (StatedSp 3 K) :=
    fun O => spSupported x (O : Set K[X])
  have hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b := fun i j hij a ha b hb =>
    blocks.directProduct.1 i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb
  have hjoin : ⨆ i, A i = Subgroup.centralizer ({x} : Set (StatedSp 3 K)) :=
    blocks.directProduct.2.2
  have htame : ∀ i, CFSG.IsQuasisimple ↥⁅A i, A i⁆ ∨ Group.IsSolvable ↥(A i) := fun i =>
    (orbit_tame hK hx hx1 blocks i).elim (fun h => Or.inl h.1) Or.inr
  have hker : (proj 3 K).ker ≤ Subgroup.center (StatedSp 3 K) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 (proj_injective_of_card_two hK)]
    exact bot_le
  have hπ : Function.Surjective (proj 3 K) := QuotientGroup.mk'_surjective _
  have hPIL := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_of_orbit_family
    (proj 3 K) hπ hker x A hc hjoin htame
  have hcomp := components_conj_of_orbit_family (proj 3 K) hπ hker x A hc hjoin htame
  have hperf : ⁅J, J⁆ = J := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.glaPComponent_perfect hJ
  have hlayer := hPIL J hJ.1 hperf
  obtain ⟨hcomJ, -⟩ := glaPComponent_isComponent_of_le_layer hJ hlayer
  obtain ⟨i, hq, hJeq⟩ := hcomp J hcomJ
  rcases orbit_tame hK hx hx1 blocks i with ⟨-, h4, hO⟩ | hsol
  swap
  · exact (not_solvable_of_quasisimple hq (commutator_solvable_of_solvable hsol)).elim
  have hAi : A i = spFixedFactor x := by
    show spSupported x (i : Set K[X]) = spSupported x {X - 1}
    rw [hO]
  rw [hAi] at hJeq
  obtain ⟨⟨e6⟩, -⟩ := spFixed_four_two_alt hK blocks h4
  have hinj := proj_injective_of_card_two hK
  let eJ : ↥J ≃* alternatingGroup (Fin 6) :=
    (MulEquiv.subgroupCongr hJeq).trans ((Subgroup.equivMapOfInjective _ _ hinj).symm.trans e6)
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hbot : GLAPPrimeCore 3 (alternatingGroup (Fin 6)) = ⊥ :=
    glaPPrimeCore_eq_bot_of_simple_dvd Nat.prime_three
      (by rw [card_alternating_six]; norm_num)
  have hna : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a :=
    exists_noncomm_of_simple_not_prime (by rw [card_alternating_six]; norm_num)
  exact pSimple_equiv_of_surjective_simple Nat.prime_three hJ hna hbot eJ.toMonoidHom
    eJ.surjective

theorem kLevel_three_alternating_six_le : kLevel 3 (alternatingGroup (Fin 6)) ≤ 1 := by
  have hch : IsChevSimple 3 (alternatingGroup (Fin 6)) :=
    Or.inr ⟨.alternating 6 (by norm_num), by simp [ambiguousChev], ⟨MulEquiv.refl _⟩⟩
  unfold kLevel
  rw [if_pos hch]

theorem kLevel_le_one_of_component [Finite K] (hK : Nat.card K = 2) {x : StatedSp 3 K}
    (hx : x ^ 3 = 1) (hx1 : x ≠ 1) (blocks : SpPrimaryBlocks 2 1 3 x (proj 3 K x))
    {J : Subgroup (StatedProj (StatedSp 3 K))}
    (hJ : GLAPComponent 3 (fixSubgroup (MulAut.conj (proj 3 K x))) J) :
    kLevel 3 (PSimple 3 J) ≤ 1 := by
  obtain ⟨e⟩ := components_A6 hK hx hx1 blocks hJ
  rw [kLevel_congr 3 e]
  exact kLevel_three_alternating_six_le

end CFSG.LocalAnalysis.GLTheoremA.LevelLieSp6

end
