module

public import CFSG.ClassicalInvolution.Uniform.U5Glue
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHBase
public import CFSG.ClassicalInvolution.Q3.Q3CSBase
public import CFSG.ClassicalInvolution.Q3.Q3DThm5
public import CFSG.ClassicalInvolution.Uniform.U5Alpha
public import CFSG.ClassicalInvolution.Uniform.UExact

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement


theorem thm5NonGenBelowU_of_compGen3
    (hmodel : ∀ (t : StatedLieTag) (k : ℕ), IsFundTag t → StatedLieAdmissible t k 3 1 →
      CompGen3 (compModel 3 1 t k)) {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) :
    Q3.Disc3.Thm5NonGenBelowU n := by
  intro G _ _ hlt Ω hΩ _ hO K hK J hJ z hz A hA hAKJ hzA
  have hJΩ : J ∈ Ω := hJ.1
  have hne : J ≠ K := hJ.2.1
  obtain ⟨D⟩ := exists_omegaLieU hn hΩ ⟨K, hK⟩ hO hlt
  have hex : ExactMembers Ω := D.exactMembers hΩ
  have h24 : ∀ L ∈ Ω, Nat.card L = 24 := fun L hL => D.card_eq (by norm_num) L hL
  have hHn : (omegaGen Ω).Normal := omegaGen_normal hΩ.conjInvariant
  have hKH : K ≤ omegaGen Ω := le_omegaGen hK
  have hJH : J ≤ omegaGen Ω := le_omegaGen hJΩ
  have hAH : A ≤ omegaGen Ω := hAKJ.trans (sup_le hKH hJH)
  have hcardH : Nat.card ↥(omegaGen Ω) < n :=
    lt_of_le_of_lt (Subgroup.card_le_card_group _) hlt
  have hLieH : Q3.Q3C.HasLieSystem3 (omegaGen Ω) :=
    ⟨restrictFamily Ω (omegaGen Ω), (lieSystemModU_sl2_of_eq_three (p := 3) (f := 1)
      (by norm_num)).mp (hn ↥(omegaGen Ω) hcardH _ (inClassU_restrict_omegaGen hΩ ⟨K, hK⟩))⟩
  have hHbot : CFSG.Open.classicalInvolutionOddCore ↥(omegaGen Ω) = ⊥ := oddCore_normal_eq_bot _ hO
  have hA2 : ∀ x ∈ A, x * x = 1 := hA.2
  have hA1 : ∃ a ∈ A, a ≠ 1 := ⟨z, hzA, hz.ne_one⟩
  have hN : ∀ a ∈ A, a ≠ 1 →
      oddCoreOf (Subgroup.centralizer ({a} : Set G)) ⊓ omegaGen Ω = ⊥ := by
    intro a ha ha1
    have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact hA2 a ha) ha1
    have h1 := Q3.Q3C.involutionOddCore_inf_le_oddCoreIn Q3.lieSystemOddCentralizer3_proved hLieH
      (x := a) (x' := a) (hAH ha) ha2 (fun _ _ => Iff.rfl)
    have hOH : Balance.oddCoreIn (omegaGen Ω) = ⊥ := by
      show (CFSG.Open.classicalInvolutionOddCore ↥(omegaGen Ω)).map (omegaGen Ω).subtype = ⊥
      rw [hHbot, Subgroup.map_bot]
    rw [hOH] at h1
    have h2 : oddCoreOf (Subgroup.centralizer ({a} : Set G)) ⊓ omegaGen Ω ≤ ⊥ := h1
    exact le_bot_iff.mp h2
  refine alphaOf_eq_bot_of_generation (omegaGen Ω) hO hAH hA2 hA1 hN ?_
  set T : Subgroup G :=
    ⨆ a ∈ A, ⨆ (_ : a ≠ 1), Subgroup.centralizer ({a} : Set G) ⊓ omegaGen Ω with hT
  have hcentT : ∀ a ∈ A, a ≠ 1 → ∀ l : Fin D.card,
      (∀ y ∈ (D.hom l).range, a * y = y * a) → (D.hom l).range ≤ T := by
    intro a ha ha1 l hl y hy
    have hle : Subgroup.centralizer ({a} : Set G) ⊓ omegaGen Ω ≤ T :=
      le_iSup₂_of_le a ha (le_iSup_of_le ha1 le_rfl)
    exact hle ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hl y hy).symm,
      D.comp_le_omegaGen l hy⟩
  rw [← D.generate]
  refine iSup_le fun l => ?_
  obtain ⟨i, R₁, hR₁, hKR⟩ := D.fundamental K hK
  obtain ⟨j, R₂, hR₂, hJR⟩ := D.fundamental J hJΩ
  have hKi : K ≤ D.comp i := hKR ▸ Subgroup.map_le_range _ _
  have hJj : J ≤ D.comp j := hJR ▸ Subgroup.map_le_range _ _
  by_cases hli : l = i
  · subst hli
    by_cases hlj : l = j
    ·
      subst hlj
      have hCG : CompGen3 (D.kind l) := by
        rcases D.valid l with ⟨t, k, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
        · have he1 : e = 1 := by rcases he with h | ⟨-, h⟩ <;> omega
          subst he1
          rw [hc]
          exact hmodel t k ht hadm
        · rw [hc]
          exact compGen3_sl23
        · rw [hc]
          exact compGen3_m11
      obtain ⟨Q, hQJ, hQ8, hQN⟩ := exists_sylow_of_omegaNbr hΩ hex hJ
      have hv := (hΩ.omega4 K hK J hJΩ hne.symm).1
      subst hKR
      subst hJR
      have key := hCG G (D.hom l) (D.ker_le_center l) R₁ hR₁ R₂ hR₂ (h24 _ hK) (h24 _ hJΩ)
        hne.symm ⟨Q, hQJ, hQ8, hQN⟩ hv
        (fun z' hz1 hz2 => commutes_of_twins hΩ hex hK hJΩ hne.symm hz1 hz2) z hz A hA hAKJ hzA
      refine key.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
      exact le_iSup₂_of_le a ha (le_iSup_of_le ha1
        (inf_le_inf_left _ (D.comp_le_omegaGen l)))
    ·
      have hKJ : Commutes K J := fun x hx y hy => D.comp_commute hlj x (hKi hx) y (hJj hy)
      obtain ⟨z', hz'⟩ := hΩ.classical K hK
      obtain ⟨eK⟩ := hz'.nonempty_equiv_sl2_of_exact (hex K hK)
      have hF : Nat.card (GaloisField 3 1) = 3 := by
        rw [GaloisField.card 3 1 (by norm_num)]
        norm_num
      have hZ := thm5IH_center_of_exact (by rw [hF]; decide) hz eK
      have hA4 : Nat.card A = 4 := by simpa using hA.1
      have hAN : A ≤ Subgroup.normalizer (D.comp l : Set G) := by
        intro a ha
        rw [Subgroup.mem_normalizer_iff]
        intro x
        refine ⟨fun hx => D.mem_comp_conj (hAH ha) hx, fun hx => ?_⟩
        have := D.mem_comp_conj ((omegaGen Ω).inv_mem (hAH ha)) hx
        simpa [mul_assoc] using this
      have hJL : ∀ j' ∈ J, ∀ x ∈ D.comp l, j' * x = x * j' := fun j' hj' x hx =>
        D.comp_commute (Ne.symm hlj) j' (hJj hj') x hx
      obtain ⟨a, haA, ha1, hac⟩ := thm5IH_exists_centralizing hKJ hz hZ hA2 hA4 hAKJ hzA hAN hJL
      exact hcentT a haA ha1 l hac
  ·
    refine hcentT z hzA hz.ne_one l fun y hy => ?_
    exact D.comp_commute (Ne.symm hli) z (hKi hz.mem) y hy

end CFSG.ClassicalInvolution.Uniform
