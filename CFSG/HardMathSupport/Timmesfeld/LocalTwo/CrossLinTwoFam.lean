module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinTwoField
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearFamily

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG CFSG.GorensteinWalter CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.HardMathSupport.Timmesfeld.DefChar

section Model

variable {F : Type} [Field F] [Finite F]

theorem innerPlaneBalance_psl_two {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hpF : ¬ p ∣ Nat.card F)
    (hinj : Function.Injective (MulAut.conj : PSL2 F →* MulAut (PSL2 F))) :
    InnerPlaneBalance p (PSL2 F) := by
  intro E hEin hE hEc H hH
  have hE₁ : (E.comap (MulAut.conj : PSL2 F →* MulAut (PSL2 F))).map
      (MulAut.conj : PSL2 F →* MulAut (PSL2 F)) = E :=
    Subgroup.map_comap_eq_self hEin
  have hE₁el := isElemAbelian_comap _ hinj hE
  have hE₁c : Nat.card (E.comap (MulAut.conj : PSL2 F →* MulAut (PSL2 F))) = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hE₁, hEc]
  rw [← hE₁]
  by_cases hs : p ∣ Nat.card F - 1
  · exact localDeltaIn_eq_bot_psl_split (n := 2) hp (by omega) hs
      (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega) (by norm_num) hinj _ hE₁el hE₁c hH
  · exact localDeltaIn_eq_bot_psl_nonsplit (n := 2) hp (Or.inl (by omega)) hpF hs (by norm_num)
      hinj _ hE₁el hE₁c hH

theorem isLocallyBalancedAbs_two_psl_two {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hF4 : 4 ≤ Nat.card F) (hpF : ¬ p ∣ Nat.card F) :
    IsLocallyBalancedAbs p 2 (PSL2 F) := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF4)
  have hsimple := CFSG.LinearGroups.linear_projective_simple (n := 2) (K := F) (by norm_num)
    (Or.inr ⟨s, hs⟩)
  have hperf := (CFSG.LinearGroups.linear_projective_perfect (n := 2) (K := F) (by norm_num)
    (Or.inr ⟨s, hs⟩)).commutator_eq_top
  have := hsimple.2.1
  have hinj := CFSG.LieType.SeitzGeneration.conj_injective_of_simple_perfect hperf
  have : Finite (PSL2 F) := hsimple.2.2 inferInstance
  exact isLocallyBalancedAbs_two_of_planes_and_fields hp hinj
    (innerPlaneBalance_psl_two hp hp5 hpF hinj)
    (fun D hD hc hDin => fieldCoreAt_of_outer hp hp5 hpF hinj hD hc hDin)

end Model

@[expose] def regimeAOne (idx : TauCeti.ValidLieTypeIndex) (_p : ℕ) : Prop :=
  ∃ q : TauCeti.PrimePower, idx.1 = .A 1 q

theorem crossCharTwoFamAt_A_one : CrossCharTwoFamAt .A regimeAOne := by
  rintro ⟨d, hv⟩ _ p hp hp5 hc ⟨q, hd⟩ _
  change d = _ at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have h4 : 4 ≤ q.card := hrange.2 (by omega)
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hpF : ¬ p ∣ Nat.card (GaloisField q.p q.exponent) := by
    rw [hcardF, TauCeti.PrimePower.card_def]
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).mp (hp.dvd_of_dvd_pow hdvd))
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_two_psl_two (F := GaloisField q.p q.exponent) hp hp5
      (by rw [hcardF]; exact h4) hpF)

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
