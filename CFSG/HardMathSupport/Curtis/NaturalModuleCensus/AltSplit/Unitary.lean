module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltSplit.Core
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbedding.LieOut CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section SU

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

include hF in
theorem exists_quasisimple_of_node_su_split {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hZ : ∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : Y) ∈ J)
    {nW : Fin (rootDatum hF n).rank → SU (unitaryInvolution F 2 f) n}
    {H : Fin (rootDatum hF n).rank → Subgroup (SU (unitaryInvolution F 2 f) n)}
    {π : SU (unitaryInvolution F 2 f) n →* ↥L ⧸ Subgroup.center ↥L} {M : ℕ}
    (h : BorelQuotient (rootDatum hF n) nW H π M)
    {π' : SU (unitaryInvolution F 2 f) n →* ↥L ⧸ Subgroup.center ↥L}
    (hker : π'.ker = π.ker) {i : Fin (n / 2)}
    (hiJ : (rankOne (rootDatum hF n).rootGroup i).map π' ≤ quotImage L J)
    {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hf : 1 ≤ f) (hpf : p ∣ 2 ^ f - 1) :
    ∃ X : Subgroup Y, X ≤ J ∧ CFSG.Open.IsQuasisimple ↥X ∧ p ∣ Nat.card X ∧
      ∀ φ : ↥X →* alternatingGroup (Fin p), ¬ φ.ker ≤ Subgroup.center ↥X := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨hf3, hbig⟩ := split_exponent hp57 hf hpf
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hq2 : p ∣ (2 ^ f) ^ 2 - 1 := dvd_sq_sub_one_of_dvd hpf
  by_cases hk : i.val + 1 < n / 2
  ·
    set e := rankOneShortEquiv (hσ := hσ) hk
    refine exists_quasisimple_of_sl2_hom hZ h hker hiJ (k := F)
      (φ := (rankOne (rootGroup _ hσ n) i).subtype.comp e.symm.toMonoidHom)
      (Subtype.val_injective.comp e.symm.injective) (le_of_eq (range_subtype_comp_symm e))
      hp57 (Or.inl ?_) ?_
    · rw [hF]
      exact sixteen_dvd_two_pow_sq hf3
    · rw [hF]
      exact dvd_sq_sub_one_of_dvd hq2
  · by_cases he : Even n
    ·
      obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
      set e := (rankOneLastEvenEquiv hF he hk).trans (hypEquiv hζ0 hζ).symm
      refine exists_quasisimple_of_sl2_hom hZ h hker hiJ (k := fixedSubfield F 2 f)
        (φ := (rankOne (rootGroup _ hσ n) i).subtype.comp e.symm.toMonoidHom)
        (Subtype.val_injective.comp e.symm.injective) (le_of_eq (range_subtype_comp_symm e))
        hp57 ?_ ?_
      · rw [card_fixedSubfield hF]
        exact sixteen_or_eight hp57 hf hpf
      · rw [card_fixedSubfield hF]
        exact hq2
    ·
      have hnq : ((3 : ℕ), 2 ^ f) ≠ (3, 2) := fun h' => by
        have := (Prod.mk.inj h').2
        omega
      have hQ : CFSG.Open.IsQuasisimple (SU (unitaryInvolution F 2 f) 3) := by
        obtain ⟨hperf, hsimple, -⟩ := isQuasisimple_SU hF le_rfl hnq
        exact ⟨hperf.commutator_eq_top, hsimple⟩
      have hc2 := not_dvd_card_center_su_three (F := F) hF hq4 (r := 2) Nat.prime_two
        (by norm_num)
      have hp3 : p ≠ 3 := by rcases hp57 with rfl | rfl <;> norm_num
      have hcp := not_dvd_card_center_su_three (F := F) hF hq4 (r := p) hpp hp3
      refine exists_quasisimple_of_node_equiv hZ h hker hiJ (p := p) hpp
        (rankOneLastOddEquiv hF he hk) hQ ?_ hcp ?_
      · rw [card_SU_three hF]
        exact (Dvd.dvd.mul_left hq2 _).mul_right _
      · refine NoAp.of_dvd (r := 16) (not_sixteen_dvd_card_alt hp57) ?_
        have h16 : 16 ∣ Nat.card (SU (unitaryInvolution F 2 f) 3) := by
          rw [card_SU_three hF]
          refine ((Dvd.dvd.mul_right ?_ _).mul_right _)
          calc 16 = 2 ^ 4 := by norm_num
            _ ∣ 2 ^ (f * 3) := pow_dvd_pow 2 (by omega)
            _ = (2 ^ f) ^ 3 := pow_mul 2 f 3
        have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
          (Subgroup.center (SU (unitaryInvolution F 2 f) 3))
        have hcop : Nat.Coprime 16
            (Nat.card (Subgroup.center (SU (unitaryInvolution F 2 f) 3))) := by
          have := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hc2
          exact Nat.Coprime.pow_left 4 this
        rw [hcard] at h16
        exact hcop.dvd_of_dvd_mul_right h16

end SU

theorem false_of_altSq_split_psu {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} {p : ℕ}
    (h : CompParabE L J) (hp57 : p = 5 ∨ p = 7) (hAlt : PerfectSectionsAltSq p J) {n f : ℕ}
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU n 2 f)
    (hpf : p ∣ 2 ^ f - 1) : False := by
  obtain ⟨⟨-, hf, hn, -⟩, F, hFf, hFfin, hcard, ⟨e⟩⟩ := hmodel
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have : Finite (SU (unitaryInvolution F 2 f) n) := Finite.of_injective _ Subtype.val_injective
  have hB := borelQuotient_su hcard (by omega) ζ hζ e
  exact false_of_altSq_of_borel h hp57 hAlt hB fun hZ π' hker i hi =>
    exists_quasisimple_of_node_su_split hcard hZ hB hker hi hp57 hf hpf

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
