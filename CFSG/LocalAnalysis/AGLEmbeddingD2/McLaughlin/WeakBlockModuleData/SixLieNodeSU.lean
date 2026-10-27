module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOneNodeLie
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieNodeSylow
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.QuasithinUnique CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg

section SU

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem diag_entries_su_four (hF : Nat.card F = (2 ^ 1) ^ 2)
    {g : SU (unitaryInvolution F 2 1) 4} {t : Fin 4 → F}
    (ht : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal t) :
    t 3 = t 0 ∧ t 2 = t 1 ∧ t 0 * t 1 = 1 := by
  have := Fintype.ofFinite F
  have hF4 : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]; norm_num
  have hu := unitary_of_coe_eq_diagonal ht
  have h0 : ∀ s, t s ≠ 0 := ne_zero_of_unitary hu
  have hc : ∀ s, t s ^ 3 = 1 := fun s => by
    have := FiniteField.pow_card_sub_one_eq_one (t s) (h0 s)
    rwa [hF4] at this
  have hs : ∀ s, t s ^ 2 * t (Fin.rev s) = 1 := fun s => by
    have := hu s
    rwa [unitaryInvolution_apply] at this
  have h3 : t 3 = t 0 := by
    have h := hs 0
    have : t 0 ^ 3 * t 3 = t 0 := by
      calc t 0 ^ 3 * t 3 = t 0 * (t 0 ^ 2 * t (Fin.rev 0)) := by
            simp [Fin.rev]; ring
        _ = t 0 := by rw [h, mul_one]
    rwa [hc, one_mul] at this
  have h2 : t 2 = t 1 := by
    have h := hs 1
    have : t 1 ^ 3 * t 2 = t 1 := by
      calc t 1 ^ 3 * t 2 = t 1 * (t 1 ^ 2 * t (Fin.rev 1)) := by
            simp [Fin.rev]; ring
        _ = t 1 := by rw [h, mul_one]
    rwa [hc, one_mul] at this
  refine ⟨h3, h2, ?_⟩
  have hdet : ∏ s, t s = 1 := by
    have := g.2.1
    rw [ht, Matrix.det_diagonal] at this
    exact this
  rw [Fin.prod_univ_four, h3, h2] at hdet
  have hsq : (t 0 * t 1) ^ 2 = 1 := by rw [← hdet]; ring
  have hcu : (t 0 * t 1) ^ 3 = 1 := by rw [mul_pow, hc, hc, one_mul]
  have hne : t 0 * t 1 ≠ 0 := mul_ne_zero (h0 0) (h0 1)
  have hx : t 0 * t 1 = (t 0 * t 1) ^ 3 * ((t 0 * t 1) ^ 2)⁻¹ := by field_simp
  rw [hx, hcu, hsq]
  norm_num

theorem card_dvd_three_of_le_diagSubgroup_su_four (hF : Nat.card F = (2 ^ 1) ^ 2)
    {A : Subgroup (SU (unitaryInvolution F 2 1) 4)}
    (hA : A ≤ diagSubgroup (unitaryInvolution F 2 1) 4) : Nat.card A ∣ 3 := by
  have := Fintype.ofFinite F
  have hF1 : Nat.card F - 1 = 3 := by rw [hF]; norm_num
  have hinj : Function.Injective fun g : A =>
      ((((g : SU (unitaryInvolution F 2 1) 4) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0) := by
    intro g g' hgg
    obtain ⟨t, ht⟩ := hA g.2
    obtain ⟨t', ht'⟩ := hA g'.2
    obtain ⟨a3, a2, a01⟩ := diag_entries_su_four hF ht
    obtain ⟨b3, b2, b01⟩ := diag_entries_su_four hF ht'
    simp only [ht, ht', Matrix.diagonal_apply_eq] at hgg
    have h1 : t 1 = t' 1 := by
      have e1 : t 1 = (t 0)⁻¹ := eq_inv_of_mul_eq_one_right a01
      have e2 : t' 1 = (t' 0)⁻¹ := eq_inv_of_mul_eq_one_right b01
      rw [e1, e2, hgg]
    have htt : t = t' := by
      funext s
      fin_cases s
      · exact hgg
      · exact h1
      · exact a2.trans (h1.trans b2.symm)
      · exact a3.trans (hgg.trans b3.symm)
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [ht, ht', htt]
  have hle : Nat.card A ≤ 4 := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [hF] at this
  have hp : IsPGroup 3 A := fun g => ⟨1, by
    have := diag_pow_eq_one (hA g.2)
    rw [hF1] at this
    apply Subtype.ext
    simpa using this⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hk]
  exact dvd_trans (pow_dvd_pow 3 hk1) (by norm_num)

end SU

theorem card_inf_threePrimeSub_of_model_psu_four {Y : Type} [Group Y] [Finite Y]
    (h : StatedClassicalModel Y .PSU 4 2 1) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    {E : Subgroup Y} (hEJ : E ≤ J) (hE : Nat.card E = 9) :
    Nat.card (E ⊓ threePrimeSub J : Subgroup Y) = 3 := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := id h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  have : Finite (SU (unitaryInvolution F 2 1) 4) := Finite.of_injective _ Subtype.val_injective
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have hB := borelQuotient_su hcard (by omega) ζ hζ e
  refine card_inf_threePrimeSub_of_oneNode hB (twoLevi_su hcard) (fun _ _ h => h.elim)
    (fun i => hasOrderThree_su hcard i) (fun i => ?_) ?_ ?_ T J hNJ hJ hperf hEJ hE
  · by_cases hk : i.val + 1 < 4 / 2
    · exact Or.inl (commutator_eq_self_of_isPerfect (su_short_isPerfect hcard hk))
    · exact Or.inr (dvd_of_eq (su_last_even_card hcard (by decide) hk))
  · intro i j hij _
    have hne := Fin.val_ne_of_ne hij
    have hr : (rootDatum hcard 4).rank = 2 := rfl
    have hi : i.val < 2 := by have := i.2; omega
    have hj : j.val < 2 := by have := j.2; omega
    by_cases hi0 : i.val + 1 < 4 / 2
    · exact Or.inl (commutator_eq_self_of_isPerfect (su_short_isPerfect hcard hi0))
    · have hj0 : j.val + 1 < 4 / 2 := by omega
      exact Or.inr (commutator_eq_self_of_isPerfect (su_short_isPerfect hcard hj0))
  · exact card_dvd_three_of_le_diagSubgroup_su_four hcard
      (iSup_le fun k => levelTorus_le_diagSubgroup k)

theorem card_dvd_three_of_le_normalizer_psu_four {Y : Type} [Group Y] [Finite Y]
    (h : StatedClassicalModel Y .PSU 4 2 1) (T : Sylow 2 Y) (V : Subgroup Y)
    (hV : V ≤ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hV3 : IsPGroup 3 V) :
    Nat.card V ∣ 3 := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := id h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  have : Finite (SU (unitaryInvolution F 2 1) 4) := Finite.of_injective _ Subtype.val_injective
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have hB := borelQuotient_su hcard (by omega) ζ hζ e
  exact (card_dvd_of_le_normalizer_borel hB ⟨⟨0, by show 0 < 4 / 2; omega⟩⟩ T V hV hV3).trans
    (card_dvd_three_of_le_diagSubgroup_su_four hcard
      (iSup_le fun k => levelTorus_le_diagSubgroup k))

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
