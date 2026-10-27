module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR1Local
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimKProofTriple
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR1Gen
public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Local

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native.ONTriple Subgroup CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

theorem gfr1_map_centralizer {Y Y' : Type*} [Group Y] [Group Y'] (ψ : Y ≃* Y') (g : Y)
    (K : Subgroup Y')
    (h : Subgroup.centralizer ({ψ g} : Set Y') = Subgroup.zpowers (ψ g) ⊔ K) :
    Subgroup.centralizer ({g} : Set Y) =
      Subgroup.zpowers g ⊔ K.map ψ.symm.toMonoidHom := by
  have hcent : Subgroup.centralizer ({g} : Set Y) =
      (Subgroup.centralizer ({ψ g} : Set Y')).map ψ.symm.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul, ψ.injective.eq_iff]
  rw [hcent, h, Subgroup.map_sup, MonoidHom.map_zpowers]
  simp

section

set_option linter.unusedSectionVars false


theorem gfr1_quasi_of_cases {X : Type} [Group X] (h : IsHatON X ∨ IsHatSix X) :
    CFSG.Open.IsQuasisimple X ∧ IsPGroup 3 (Subgroup.center X) ∧ 3 ∣ Nat.card X := by
  have hcard : Nat.card (Subgroup.center X) = 3 := by
    rcases h with h | h
    · exact h.2.1
    · exact h.2.1
  refine ⟨?_, IsPGroup.of_card (n := 1) (by rw [hcard, pow_one]), ?_⟩
  · rcases h with ⟨hperf, -, ⟨iso⟩⟩ | ⟨hperf, -, ⟨iso⟩⟩
    · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
      have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
          (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
      have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
        CFSG.Sporadic.ON.isSimpleGroup_ON
      exact ⟨hperf, (iso.trans b'.symm).isSimpleGroup⟩
    · have := on25_alt6_simple
      exact ⟨hperf, iso.isSimpleGroup⟩
  · rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _


theorem gfr1_centralizer_decomp {Y : Type} [Group Y] [Finite Y] (hY : IsHatON Y)
    (ψ : Y ≃* GM) {g : Y} (hg3 : g ^ 3 = 1) :
    ∃ K : Subgroup Y, Subgroup.centralizer ({g} : Set Y) = Subgroup.zpowers g ⊔ K ∧
      Subgroup.center Y ≤ K ∧ (IsHatON ↥K ∨ IsHatSix ↥K) := by
  by_cases hgc : g ∈ Subgroup.center Y
  · refine ⟨⊤, ?_, le_top, Or.inl (gfr1_isHatON_of_equiv Subgroup.topEquiv.symm hY)⟩
    rw [sup_top_eq]
    refine top_unique fun x _ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.1 hgc x)
  · have hgz : ψ g ∉ zpowers zG := fun h =>
      hgc ((CFSG.RankThree.PartTwo.Sec13.ON134.mem_center_iff_model ψ).2 h)
    have ha3 : (ψ g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
    obtain ⟨n, hC, -⟩ := gfr1_exists_conj ha3 hgz
    refine ⟨(K0G.map (MulAut.conj n).toMonoidHom).map ψ.symm.toMonoidHom,
      gfr1_map_centralizer ψ g _ hC, ?_, Or.inr ?_⟩
    · intro x hx
      have hx' := (CFSG.RankThree.PartTwo.Sec13.ON134.mem_center_iff_model ψ).1 hx
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
      exact (Subgroup.zpowers_le.2 (on25_z_mem_K n)) hx'
    · exact gfr1_isHatSix_of_equiv
        ((on25_KEquiv n).trans
          ((Subgroup.equivMapOfInjective _ ψ.symm.toMonoidHom ψ.symm.injective)))
        gfr1_K0_isHatSix

theorem gapFinalLayerON_holds : GapFinalLayerON := by
  intro Y _ _ hY α hα
  obtain ⟨hperf, hZ, ⟨iso⟩⟩ := hY
  have hY : IsHatON Y := ⟨hperf, hZ, ⟨iso⟩⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
  have hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover Y CFSG.Blueprint.NativeSporadic.ON :=
    ⟨hZ, ⟨iso.trans b'.symm⟩⟩
  obtain ⟨ψ⟩ := CFSG.RankThree.PartTwo.Sec13.ON134.nonempty_equiv_model ⟨hperf⟩ hT
  have hfix := fun z (hz : z ∈ Subgroup.center Y) =>
    CFSG.RankThree.PartTwo.Sec10.Step1012ClaimKProof.fix_center_of_pow_three hZ hα hz
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec13.ON134.aut_inner ψ α hfix
  have hαg : α = MulAut.conj g := by
    ext x
    rw [hg x]
    rfl
  have hg3 : g ^ 3 = 1 := by
    have h1 : MulAut.conj (g ^ 3) = 1 := by rw [map_pow, ← hαg, hα]
    have h2 : g ^ 3 ∈ Subgroup.center Y :=
      CFSG.RankThree.PartTwo.Sec10.Step1012ClaimKProof.conj_eq_one_iff.1 h1
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : (g ^ 3) ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := Subgroup.center Y) (x := ⟨g ^ 3, h2⟩)
      rw [hZ] at h
      exact congrArg Subtype.val h
    refine CFSG.RankThree.PartTwo.Sec13.ON134.pow_three_eq_one ψ (k := 2) ?_
    rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul]
    exact h3
  have hfixSub : Lemma510Ns.fixSub α = Subgroup.centralizer ({g} : Set Y) := by
    ext x
    rw [Lemma510Ns.mem_fixSub, Subgroup.mem_centralizer_singleton_iff, hαg, MulAut.conj_apply]
    constructor
    · intro h
      calc x * g = g * x * g⁻¹ * g := by rw [h]
        _ = g * x := by group
    · intro h
      rw [← h]
      group
  obtain ⟨K, hC, hZK, hKtype⟩ := gfr1_centralizer_decomp hY ψ hg3
  obtain ⟨hq, hZp, h3⟩ := gfr1_quasi_of_cases hKtype
  obtain ⟨hcomp, huniq⟩ := gfr1_components hC hq hZp h3
  rw [hfixSub]
  refine ⟨⟨K, hcomp⟩, fun J hJ => ?_⟩
  rw [huniq J hJ]
  refine ⟨hZK, ?_⟩
  rcases hKtype with h | h
  · exact Or.inl (gfr1_isHatON_of_equiv (gfr1_barOf_equiv hq hZp h3).symm h)
  · exact Or.inr (gfr1_isHatSix_of_equiv (gfr1_barOf_equiv hq hZp h3).symm h)

end

end CFSG.HardMathSupport.Solomon.Coordinator
