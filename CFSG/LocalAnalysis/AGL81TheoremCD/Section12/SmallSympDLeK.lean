module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.SmallSympDLeKLinear
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.SmallSympDLeKSymplectic
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneReduce
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.SignalizerFunctorTheorem.Quadratic.Toolkit
import CFSG.GroupTheory.PSubgroupLeOfPrimeNotDvdIndex
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGSmallRep
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.SmallSympDLeK

open Module Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
open CFSG.SignalizerFunctorTheorem.Quadratic

variable {W : Type} [AddCommGroup W] [Module (ZMod 3) W] [Module.Finite (ZMod 3) W]

theorem exists_invariant_subspace_of_threeGroup {d : ℕ} (hd : d.Prime)
    {N D : Subgroup (Module.End (ZMod 3) W)ˣ}
    (hN : oPPrimeHull 3 N = N) (hN0 : N ≠ ⊥) (hD : IsPGroup d D)
    (hDN : D ≤ normalizer (N : Set (Module.End (ZMod 3) W)ˣ))
    (hdN : ¬ d ∣ Nat.card N) :
    ∃ U : Submodule (ZMod 3) W, U ≠ ⊥ ∧ U ≠ ⊤ ∧
      ∀ g ∈ D, ∀ u ∈ U, (g : Module.End (ZMod 3) W) u ∈ U := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite W := Module.finite_of_finite (ZMod 3)
  have : Finite (Module.End (ZMod 3) W)ˣ :=
    Finite.of_injective (fun x : (Module.End (ZMod 3) W)ˣ => (x : W → W))
      (fun x y h => Units.ext (LinearMap.ext (congrFun h)))
  have h3N : 3 ∣ Nat.card N := dvd_card_of_oPPrimeHull_of_ne_bot hN hN0
  obtain ⟨P, hDP, hP0⟩ := CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
    d 3 hd Nat.prime_three D N hD hDN ((hd.coprime_iff_not_dvd).mpr hdN) h3N
  let R : Subgroup (Module.End (ZMod 3) W)ˣ := (P : Subgroup N).map N.subtype
  have hR : IsPGroup 3 R := P.isPGroup'.map N.subtype
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) W
  let R' : Subgroup (W ≃ₗ[ZMod 3] W) := R.map e.toMonoidHom
  have hR' : IsPGroup 3 R' := hR.map e.toMonoidHom
  have hR'0 : R' ≠ ⊥ := by
    intro h
    exact hP0 ((Subgroup.map_eq_bot_iff_of_injective R e.injective).mp h)
  have hDnorm : ∀ g ∈ D, e g ∈ normalizer (R' : Set (W ≃ₗ[ZMod 3] W)) := by
    intro g hg
    rw [← Subgroup.map_equiv_normalizer_eq R e]
    exact mem_map_of_mem e.toMonoidHom (hDP hg)
  have hW : Nontrivial W := by
    by_contra h
    have : Subsingleton W := not_nontrivial_iff_subsingleton.mp h
    apply hR'0
    rw [eq_bot_iff]
    intro g _
    rw [mem_bot]
    ext w
    exact Subsingleton.elim _ _
  have : Nontrivial W := hW
  obtain ⟨v, -, hv0, hvR⟩ := exists_fixed_of_isPGroup hR'
    (show (⊤ : Submodule (ZMod 3) W) ≠ ⊥ from top_ne_bot)
    (fun _ _ _ _ => trivial)
  refine ⟨fixSub R', ?_, ?_, ?_⟩
  · intro h
    have hv : v ∈ fixSub R' := hvR
    rw [h, Submodule.mem_bot] at hv
    exact hv0 hv
  · exact fun h => hR'0 ((fixSub_eq_top_iff R').mp h)
  · intro g hg u hu
    exact map_mem_fixSub_of_mem_normalizer R' (hDnorm g hg) hu

private theorem le_of_not_sq_dvd {X : Type} [Group X] [Finite X] {N D : Subgroup X}
    (hN : N.Normal) {d : ℕ} (hd : d.Prime) (hsq : ¬ d ^ 2 ∣ Nat.card X)
    (hdN : d ∣ Nat.card N) (hD : IsPGroup d D) : D ≤ N := by
  have hidx : ¬ d ∣ N.index := by
    intro h
    exact hsq (by
      rw [← N.card_mul_index, pow_two]
      exact Nat.mul_dvd_mul hdN h)
  exact CFSG.pSubgroup_le_of_not_dvd_index hd hN hidx hD

theorem le_normal_of_small_rep {X : Type} [Group X] [Finite X]
    (φ : X →* (Module.End (ZMod 3) W)ˣ) {N : Subgroup X} (hNn : N.Normal)
    (hN : oPPrimeHull 3 N = N) (hN0 : N.map φ ≠ ⊥)
    (hW : finrank (ZMod 3) W ≤ 4)
    (hcase : finrank (ZMod 3) W ≤ 3 ∨
      (∀ D : Subgroup (Module.End (ZMod 3) W)ˣ, ∀ d : ℕ, d.Prime → 5 ≤ d →
        IsPGroup d D → D ≤ φ.range → Nat.card D ∣ 51840))
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) {D : Subgroup X} (hD : IsPGroup d D) :
    D.map φ ≤ N.map φ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact d.Prime := ⟨hd⟩
  have : N.Normal := hNn
  have : Finite W := Module.finite_of_finite (ZMod 3)
  have : Finite (Module.End (ZMod 3) W)ˣ :=
    Finite.of_injective (fun x : (Module.End (ZMod 3) W)ˣ => (x : W → W))
      (fun x y h => Units.ext (LinearMap.ext (congrFun h)))
  let f : X →* φ.range := φ.rangeRestrict
  let N' : Subgroup φ.range := N.map f
  let D' : Subgroup φ.range := D.map f
  have hN'n : N'.Normal := hNn.map f φ.rangeRestrict_surjective
  have hmapN : N'.map φ.range.subtype = N.map φ := by
    rw [Subgroup.map_map]
    rfl
  have hmapD : D'.map φ.range.subtype = D.map φ := by
    rw [Subgroup.map_map]
    rfl
  have hsq : ¬ d ^ 2 ∣ Nat.card φ.range := by
    intro h
    exact not_sq_dvd_card_endUnits_of_five_le hd hd5 hW
      (h.trans φ.range.card_subgroup_dvd_card)
  have hD' : IsPGroup d D' := hD.map f
  by_cases hdN : d ∣ Nat.card N'
  · have hle : D' ≤ N' := le_of_not_sq_dvd hN'n hd hsq hdN hD'
    rw [← hmapD, ← hmapN]
    exact Subgroup.map_mono hle
  · have hNd : ¬ d ∣ Nat.card (N.map φ) := by
      rw [← hmapN, Subgroup.card_map_of_injective φ.range.subtype_injective]
      exact hdN
    have hDN : D.map φ ≤ normalizer (N.map φ : Set (Module.End (ZMod 3) W)ˣ) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [← hmapN]
      have hyN : f y ∈ normalizer (N' : Set φ.range) := by
        have : N'.Normal := hN'n
        rw [normalizer_eq_top N']
        exact mem_top _
      have hle := Subgroup.le_normalizer_map (H := N') φ.range.subtype
      exact hle (mem_map_of_mem φ.range.subtype hyN)
    obtain ⟨U, hU0, hUt, hDU⟩ := exists_invariant_subspace_of_threeGroup hd
      (oPPrimeHull_map_eq φ hN) hN0 (hD.map φ) hDN hNd
    have hD0 : D.map φ = ⊥ := by
      by_contra hD0
      have hdvd : d ∣ Nat.card (D.map φ) := (hD.map φ).card_eq_or_dvd.resolve_left fun h =>
        hD0 (Subgroup.card_eq_one.mp h)
      rcases hcase with h3 | hSp
      · have hdiv : Nat.card (D.map φ) ∣ 11232 :=
          (D.map φ).card_subgroup_dvd_card.trans (by
            rw [Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) W).toEquiv]
            exact CFSG.OddStandard.SmallF3.Omega.fg_card_linearEquiv_dvd h3)
        have hd13 : d = 13 := by
          have hdiv := hdvd.trans hdiv
          rw [show (11232 : ℕ) = 2 ^ 5 * 3 ^ 3 * 13 by norm_num] at hdiv
          rcases hd.dvd_mul.mp hdiv with h | h
          · rcases hd.dvd_mul.mp h with h | h
            · have := (Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp (hd.dvd_of_dvd_pow h)
              omega
            · have := (Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp (hd.dvd_of_dvd_pow h)
              omega
          · exact (Nat.prime_dvd_prime_iff_eq hd (by norm_num)).mp h
        subst d
        exact hD0 (eq_bot_of_thirteenGroup_of_invariant_subspace h3 (hD.map φ) U hU0 hUt hDU)
      · have hdiv := hdvd.trans (hSp (D.map φ) d hd hd5 (hD.map φ) (by
          rw [MonoidHom.range_eq_map]
          exact Subgroup.map_mono le_top))
        have hd5' : d = 5 := by
          rw [show (51840 : ℕ) = 2 ^ 7 * 3 ^ 4 * 5 by norm_num] at hdiv
          rcases hd.dvd_mul.mp hdiv with h | h
          · rcases hd.dvd_mul.mp h with h | h
            · have := (Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp (hd.dvd_of_dvd_pow h)
              omega
            · have := (Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp (hd.dvd_of_dvd_pow h)
              omega
          · exact (Nat.prime_dvd_prime_iff_eq hd Nat.prime_five).mp h
        subst d
        exact hD0 (eq_bot_of_fiveGroup_of_invariant_subspace hW (hD.map φ) U hU0 hUt hDU)
    rw [hD0]
    exact bot_le

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.SmallSympDLeK

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
open SmallSympDLeK

theorem le_sup_pCore_three_of_isPGroup {X : Type} [Group X] [Finite X]
    (hC : Subgroup.centralizer (CFSG.pCore 3 X : Set X) ≤ CFSG.pCore 3 X)
    (hQ : CFSG.Open.pRank 3 (CFSG.pCore 3 X) ≤ 3)
    (hSp : Nat.card ↥(Matrix.symplecticGroup (Fin 2) (ZMod 3)) = 51840)
    {N : Subgroup X} (hNn : N.Normal) (hN : oPPrimeHull 3 N = N) (hN1 : ¬ N ≤ CFSG.pCore 3 X)
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) {D : Subgroup X} (hD : IsPGroup d D) :
    D ≤ N ⊔ CFSG.pCore 3 X := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨W, hWa, hWm, hWf, φ, hker, hdim⟩ := exists_smallSymp_rep (by norm_num) hC hQ
  let : AddCommGroup W := hWa
  let : Module (ZMod 3) W := hWm
  let : Module.Finite (ZMod 3) W := hWf
  have hN0 : N.map φ ≠ ⊥ := by
    intro h
    apply hN1
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker]
    have hmem : φ x ∈ N.map φ := Subgroup.mem_map_of_mem φ hx
    rwa [h, Subgroup.mem_bot] at hmem
  have hW4 : Module.finrank (ZMod 3) W ≤ 4 := by
    rcases hdim with h | ⟨h, -⟩ <;> omega
  have hcase : Module.finrank (ZMod 3) W ≤ 3 ∨
      (∀ D : Subgroup (Module.End (ZMod 3) W)ˣ, ∀ d : ℕ, d.Prime → 5 ≤ d →
        IsPGroup d D → D ≤ φ.range → Nat.card D ∣ 51840) := by
    rcases hdim with h3 | ⟨h4, B, hnd, halt, hsim⟩
    · exact Or.inl h3
    · refine Or.inr ?_
      intro D' d' hd' hd5' hD' hDr
      rw [← hSp]
      exact card_dvd_symplectic_of_odd_prime h4 B hnd halt hd' (by omega) hD' fun x hx => by
        obtain ⟨y, rfl⟩ := hDr hx
        exact hsim y
  have hle : D.map φ ≤ N.map φ := le_normal_of_small_rep φ hNn hN hN0 hW4 hcase hd hd5 hD
  have hpre : D ≤ N ⊔ φ.ker := by
    have h := (Subgroup.map_le_map_iff).mp hle
    simpa using h
  exact hpre.trans (sup_le_sup_left hker N)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
