module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510ii
public import CFSG.HardMathSupport.Solomon.Proving.L34Cover
public import CFSG.RankThree.PartTwo.KFacts.L34Models
public import CFSG.CGT.Timmesfeld75.MultPrime

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.GLTheoremB CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem heis_of_card_sl {k : Type} [Field k] (hk : Nat.card k = 4)
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k)} (hZP : scalars 3 k ≤ P)
    (hP : Nat.card P = 27) :
    (∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x) ∧ ∀ x ∈ P, x ^ 3 = 1 := by
  have hfin : Finite k := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
  have hker : (proj 3 k).ker ≤ P := by rw [ker_proj]; exact hZP
  set E := P.map (proj 3 k) with hE
  have hcomap : E.comap (proj 3 k) = P := Subgroup.comap_map_eq_self hker
  have hSL : Nat.card (scalars 3 k) * Nat.card (projectiveSL 3 k) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) k) := by
    have := Subgroup.card_ker_mul_card_of_surjective (proj_surjective 3 k)
    rwa [ker_proj] at this
  have h3 := CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine.card_scalars hk (k := k)
  have h1 := Subgroup.card_mul_index P
  have h2 := Subgroup.card_mul_index E
  have hi : (E.comap (proj 3 k)).index = E.index :=
    Subgroup.index_comap_of_surjective E (proj_surjective 3 k)
  rw [← hcomap, hi] at h1
  have hidx : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hE9 : Nat.card E = 9 := by
    rw [hcomap, hP] at h1
    rw [h3] at hSL
    have : 27 * E.index = 3 * (Nat.card E * E.index) := by rw [h2, hSL]; exact h1
    have : 9 * E.index = Nat.card E * E.index := by omega
    exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidx) this).symm
  obtain ⟨⟨-, -, -, hZc⟩, hc27, hexp⟩ := isHeisThree_comap_proj hk hE9
  constructor
  · by_contra hall
    push Not at hall
    have hcomm : ∀ g : ↥(E.comap (proj 3 k)), g ∈ Subgroup.center ↥(E.comap (proj 3 k)) := by
      intro g
      rw [Subgroup.mem_center_iff]
      intro h
      have hg : (g : Matrix.SpecialLinearGroup (Fin 3) k) ∈ P :=
        Eq.mp (congrArg ((g : Matrix.SpecialLinearGroup (Fin 3) k) ∈ ·) hcomap) g.2
      have hh : (h : Matrix.SpecialLinearGroup (Fin 3) k) ∈ P :=
        Eq.mp (congrArg ((h : Matrix.SpecialLinearGroup (Fin 3) k) ∈ ·) hcomap) h.2
      have := hall _ hh _ hg
      exact Subtype.ext this
    have htop : Subgroup.center ↥(E.comap (proj 3 k)) = ⊤ := eq_top_iff.2 fun g _ => hcomm g
    rw [htop, Subgroup.card_top, hc27] at hZc
    omega
  · intro x hx
    have hx' : x ∈ E.comap (proj 3 k) := by rw [hcomap]; exact hx
    have h1 := Monoid.pow_exponent_eq_one (⟨x, hx'⟩ : ↥(E.comap (proj 3 k)))
    rw [hexp] at h1
    exact congrArg Subtype.val h1

theorem card_of_isLThreeFour {Y : Type} [Group Y] (h : IsLThreeFour Y) : Nat.card Y = 20160 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact (Nat.card_congr (CFSG.CGT.Timmesfeld75.projectiveSLMulEquivStatedProj 3 K).toEquiv).symm.trans
    (card_projectiveSL hK)

theorem inputSL34Sylow_holds :
    LocalBalance.Lemma510iiNs.InputSL34Sylow := by
  intro Y _ _ hq hZ3 hZ1 hL P hP hZP hcard
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpc : CFSG.pCore 3 Y = Subgroup.center Y :=
    le_antisymm (Proving.pCore_three_le_center_of_quasisimple hq)
      (le_sSup ⟨inferInstance, hZ3⟩)
  have hL' : IsLThreeFour (Y ⧸ CFSG.pCore 3 Y) :=
    UniquenessMaximal.IsLThreeFour.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hpc.symm) hL
  rcases Proving.inputL34Cover_holds Y hq hL' with h | h
  · exfalso
    have h1 := card_of_isLThreeFour h
    have h2 := card_of_isLThreeFour hL
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)
    rw [h1, h2] at h3
    have : Nat.card (Subgroup.center Y) = 1 := by omega
    exact hZ1 (Subgroup.eq_bot_of_card_eq _ this)
  · obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
    have hKf : Finite K := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hK
    let e : Y ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
      φ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
    have hcen : Nat.card (Subgroup.center Y) = 3 := by
      rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv,
        ← scalars_eq_center 3 K]
      exact CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine.card_scalars hK
    have hP27 : Nat.card (P.map e.toMonoidHom) = 27 := by
      rw [Subgroup.card_map_of_injective e.injective, hcard, hcen]
    have hsc : scalars 3 K ≤ P.map e.toMonoidHom := by
      rw [scalars_eq_center 3 K, ← Subgroup.map_center_eq e]
      exact Subgroup.map_mono hZP
    obtain ⟨⟨x, hx, y, hy, hxy⟩, hexp⟩ := heis_of_card_sl hK hsc hP27
    refine ⟨?_, fun z hz => ?_⟩
    · obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨x', hx', y', hy', fun h => hxy (by simp only [MulEquiv.coe_toMonoidHom, ← map_mul, h])⟩
    · have := hexp (e z) ⟨z, hz, rfl⟩
      exact e.injective (by simpa using this)

end CFSG.HardMathSupport.Solomon.Coordinator
