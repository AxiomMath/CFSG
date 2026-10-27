module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrTwoHub
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSpin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSpinMinus

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt CFSG.LieType.CurtisTits
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped commutatorElement

section Sp

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LieType.Steinberg.Sp CFSG.LieType.RootSystem CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (ne_succ')

variable {K : Type} [Field K] {n : ℕ}

theorem sp_tail_exc_idx [Finite K] (hK : Nat.card K = 2) {k : Fin n} (hk2 : k.val + 2 = n) :
    ∃ V : Subgroup (StatedSp n K),
      V ≤ rankOne (rootGroup n K) k ⊔ rankOne (rootGroup n K) ⟨k.val + 1, by omega⟩ ∧
        ⁅V, V⁆ = V ∧ Nat.card ↥(rankOne (rootGroup n K) k ⊔
          rankOne (rootGroup n K) ⟨k.val + 1, by omega⟩) ∣ 2 * Nat.card V := by
  have hk : k.val + 1 < n := by omega
  have hlong : ¬(⟨k.val + 1, hk⟩ : Fin n).val + 1 < n := by
    simp only
    omega
  have hsup : rankOne (rootGroup n K) k ⊔ rankOne (rootGroup n K) ⟨k.val + 1, hk⟩ =
      (spEmbed (K := K) (pairMap k ⟨k.val + 1, hk⟩) (pairMap_injective (ne_succ' hk))).range := by
    rw [← range_shortBlock_eq_rankOne hk, ← range_longBlock_eq_rankOne hlong]
    exact shortBlock_sup_longBlock (ne_succ' hk)
  have := Fintype.ofFinite K
  have hK2 : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  set θ := spEmbed (K := K) (pairMap k ⟨k.val + 1, hk⟩) (pairMap_injective (ne_succ' hk)) with hθ
  have hθinj : Function.Injective θ := spEmbed_injective (pairMap_injective (ne_succ' hk))
  let Φ : θ.range ≃* Equiv.Perm (Fin 6) :=
    (MonoidHom.ofInjective hθinj).symm.trans
      (CFSG.QuasithinUnique.Bridge.Alt57Model.spEquivPerm K hK2)
  obtain ⟨V, hVS, hV, h360, h720⟩ := exists_perfect_of_equiv_perm_six Φ
  refine ⟨V, hsup ▸ hVS, hV, ?_⟩
  rw [hsup, h720, h360]

theorem spTail_idx [Finite K] (hK : Nat.card K = 2) (i j : Fin n) (hij : spTail n i j) :
    ∃ V : Subgroup (StatedSp n K),
      V ≤ rankOne (rootDatum n K).rootGroup i ⊔ rankOne (rootDatum n K).rootGroup j ∧
        ⁅V, V⁆ = V ∧ Nat.card ↥(rankOne (rootDatum n K).rootGroup i ⊔
          rankOne (rootDatum n K).rootGroup j) ∣ 2 * Nat.card V := by
  rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hi1 : i.val + 1 < n := by omega
    have hk : j = ⟨i.val + 1, hi1⟩ := Fin.ext (by simp; omega)
    subst hk
    exact sp_tail_exc_idx hK h1
  · have hj1 : j.val + 1 < n := by omega
    have hk : i = ⟨j.val + 1, hj1⟩ := Fin.ext (by simp; omega)
    subst hk
    rw [sup_comm]
    exact sp_tail_exc_idx hK h1

theorem twoHub_of_model_psp {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 1) : TwoHub Y := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hcard
  have := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  exact borelQuotient_twoHub (borelQuotient_sp e) (by rw [hK2]; norm_num) (twoLevi_sp hK2)
    (spTail_idx hK2)

end Sp

theorem twoHub_of_model_psl {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : StatedClassicalModel Y .PSL n 2 1) : TwoHub Y := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact borelQuotient_twoHub (borelQuotient_sl
    ((projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans e.symm))
    (by rw [hF2]; norm_num) (twoLevi_sl hF2) (fun _ _ h => h.elim)

theorem twoHub_of_model_pomegaPlus {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 1) : TwoHub Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  have hb := borelQuotient_spinPlus hn3 e
  exact borelQuotient_twoHub hb (by rw [hF2]; norm_num)
    (twoLevi_spinPlus hF2 hn3 hb.ct hb.extras) (fun _ _ h => h.elim)

theorem twoHub_of_model_pomegaMinus {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 1) : TwoHub Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hb := borelQuotient_spinMinus hirr (by omega) e
  exact borelQuotient_twoHub hb (by rw [hF2]; norm_num)
    (twoLevi_spinMinus hirr hb.ct hb.extras hF2) (fun _ _ h => h.elim)

theorem twoHub_of_model_psu {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 1) : TwoHub Y := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have : Finite (SU (unitaryInvolution F 2 1) n) := Finite.of_injective _ Subtype.val_injective
  exact borelQuotient_twoHub (borelQuotient_su hcard (by omega) ζ hζ e)
    (by rw [hcard]; norm_num) (twoLevi_su hcard) (fun _ _ h => h.elim)

end CFSG.AGLEmbedding.ParabAutIrr
