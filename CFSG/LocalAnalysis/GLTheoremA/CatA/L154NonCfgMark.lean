module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcOutdiag
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Assembly (LargeEvenInLambda2 LargeEvenLabel LargeEvenMarkProp LargeEvenMarking
  LargeEvenRawCont LargeEvenProj LargeEvenSpGroup)

open CFSG.StandardType (GGOutdiagPrime exists_mul_ne_mul_centerQuot_of_perfect markChar markDeg
  markRank markTag nonabelian_of_mulEquiv nonempty_b2der_equiv_alternatingGroup)

open CFSG.StandardType.Canonical (largeEvenMarking_mono)

open CFSG.Blueprint (LieModel)

open CFSG.LocalAnalysis.GLTheoremA.MI (CAll)


@[expose] def L154GoodModel (t : CFSG.Open.StatedLieTag) (n : ℕ) : Prop :=
  (t = .PSL ∧ n = 2) ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .G2 ∨ t = .F4 ∨
    t = .E7 ∨ t = .E8 ∨ t = .trialityD4

@[expose] def L154NonCfgModel (X : Type) [Group X] : Prop :=
  (∃ (t : CFSG.Open.StatedLieTag) (n f : ℕ), LieModel X t n 2 f ∧ L154GoodModel t n) ∨
    Nonempty (X ≃* alternatingGroup (Fin 6))

theorem l154_notCfg_of_good {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    {t : CFSG.Open.StatedLieTag} {n : ℕ} (hg : L154GoodModel t n) (ht : markTag lab = t)
    (hn : markRank lab = n) (hc : markChar lab = 2) : ¬ L154OutdiagCfg p lab := by
  have h2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  obtain ⟨tg, l, k⟩ := lab
  rintro hcfg
  rcases hg with ⟨rfl, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases tg <;>
    simp [markTag, markRank, markChar, L154OutdiagCfg] at ht hn hc hcfg
  · exact h2 (by rw [show l = 1 by omega] at hcfg; exact hcfg.1)
  all_goals first | omega | (by_cases h3 : l = 3 <;> by_cases h2' : l = 2 <;>
    simp_all [markTag, markRank])

theorem canon_marking_and_labelAll_simple_on {X : Type*} [Group X] {P : LargeEvenMarkProp X}
    {S : LargeEvenLabel → Prop} {P' : LargeEvenRawCont}
    (hall : ∀ lab, LargeEvenInLambda2 lab → S lab →
      CAll lab (CFSG.StandardType.LargeEvenSimpleGuard P'))
    (hS : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), P lab R I F θ → S lab)
    (h : LargeEvenMarking X P) :
    LargeEvenMarking X fun lab R _ I F θ => P lab R I F θ ∧ P' R I F := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hP⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hraw' := hall lab hlab (hS lab R I F θ hP) _ hraw
  refine ⟨hX, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw'⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hP'⟩
  exact ⟨hs, hna, θ, hθ, hP' hs hna⟩

theorem l154_marking_b2der_label {X : Type} [Group X] (hX : commutator X = ⊤)
    [IsSimpleGroup (X ⧸ Subgroup.center X)]
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) :
    LargeEvenMarking X fun lab _ _ _ _ _ => lab.tag = .B2der := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  obtain ⟨e₆⟩ := nonempty_b2der_equiv_alternatingGroup hK
  have hnab := exists_mul_ne_mul_centerQuot_of_perfect hX inferInstance
  let θ := e.trans e₆.symm
  refine ⟨hX, ⟨.B2der, 0, 1⟩, ⟨le_rfl, rfl, rfl⟩, ZMod 2, inferInstance, inferInstance, hK, ?_⟩
  exact ⟨θ.symm.isSimpleGroup, nonabelian_of_mulEquiv θ hnab, θ, rfl⟩

section Certs


theorem l154_marking_of_nonCfgModel {X : Type} [Group X] (hX : CFSG.IsQuasisimple X) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : L154NonCfgModel (X ⧸ Subgroup.center X)) :
    LargeEvenMarking X fun _ R' _ I _ _ => GGOutdiagPrime p R' I := by
  have hperf : commutator X = ⊤ := Group.isPerfect_def.mp hX.1
  rcases h with ⟨t, n, f, hM, hg⟩ | h6
  · have h1 := CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hperf hM
    have h2 := canon_marking_and_labelAll_simple_on (P' := fun R _ I _ => GGOutdiagPrime p R I)
      (S := fun lab => markTag lab = t ∧ markRank lab = n ∧ markChar lab = 2 ∧ markDeg lab = f)
      (fun lab hlab hl => l154_outdiagPrime hp hp2 hlab
        (l154_notCfg_of_good hp hp2 hg hl.1 hl.2.1 hl.2.2.1))
      (by intro _ _ _ _ _ _ h; exact h) h1
    refine largeEvenMarking_mono ?_ h2
    intro _ _ _ _ _ _ h
    exact h.2
  · obtain ⟨e⟩ := h6
    haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2.1
    have h2 := canon_marking_and_labelAll_simple_on (P' := fun R _ I _ => GGOutdiagPrime p R I)
      (S := fun lab => lab.tag = .B2der)
      (fun lab hlab hb => l154_outdiagPrime hp hp2 hlab (by
        intro hcfg
        simp [L154OutdiagCfg, hb] at hcfg))
      (by intro _ _ _ _ _ _ h; exact h) (l154_marking_b2der_label hperf e)
    refine largeEvenMarking_mono ?_ h2
    intro _ _ _ _ _ _ h
    exact h.2

end Certs

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
