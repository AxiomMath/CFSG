module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviBorel
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSpin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSpinMinus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagBadAux

public section

namespace CFSG.AGLEmbedding.ParabHub

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

theorem card_rankOne_dvd_six_of_sl2 {K : Type*} [Group K] {D : UniversalRootDatum K}
    {i : Fin D.rank} {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2)
    {x : (Fin D.rank → ℤ) → k → K}
    (hx : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup x)
    {ρ : Matrix.SpecialLinearGroup (Fin 2) k →* K}
    (hU : ∀ c, ρ (sl2Upper c) = x (Pi.single i 1) c)
    (hL : ∀ c, ρ (sl2Lower c) = x (-Pi.single i 1) c) :
    Nat.card (rankOne D.rootGroup i) ∣ 6 := by
  rw [rankOne_eq_range_of_sl2 hx hU hL]
  exact (Subgroup.card_range_dvd ρ).trans (by rw [card_sl2, hk]; norm_num)

section Tail

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal.Symplectic
open CFSG.LieType.Universal.Symplectic.SpExtras (ne_succ')

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem sp_tail_exc_three (hK : Nat.card K = 2) {k : Fin n} (hk2 : k.val + 2 = n) :
    ∃ V : Subgroup (StatedSp n K),
      V ≤ rankOne (rootGroup n K) k ⊔ rankOne (rootGroup n K) ⟨k.val + 1, by omega⟩ ∧
        ⁅V, V⁆ = V ∧ ∃ v ∈ V, v ^ 3 = 1 ∧ v ∉ Subgroup.center (StatedSp n K) := by
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
  set S : Subgroup (StatedSp n K) := θ.range with hS
  let Φ : S ≃* Equiv.Perm (Fin 6) :=
    (MonoidHom.ofInjective hθinj).symm.trans
      (CFSG.QuasithinUnique.Bridge.Alt57Model.spEquivPerm K hK2)
  have h5 : 5 ≤ Nat.card (Fin 6) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  set C : Subgroup S := commutator S with hC
  have hCA : C.map Φ.toMonoidHom = alternatingGroup (Fin 6) := by
    rw [hC, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ Φ.surjective, ← commutator_def,
      alternatingGroup.commutator_perm_eq h5]
  have hCperf : ⁅C, C⁆ = C := by
    apply Subgroup.map_injective (f := Φ.toMonoidHom) Φ.injective
    rw [Subgroup.map_commutator, hCA, commutator_alternatingGroup_eq_self h5]
  obtain ⟨x, hx, y, hy, h3, c, hc⟩ := (hasSL2Node_sp (F := K) k).hasOrderThree
  have hvS : x * y ∈ S := hsup ▸ Subgroup.mem_sup_left
    (mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy))
  have hvC : (⟨x * y, hvS⟩ : S) ∈ C := by
    have h3' : (Φ ⟨x * y, hvS⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x * y, hvS⟩ : S) ^ 3 = 1 := Subtype.ext (by simpa using h3)
      rw [this, map_one]
    have hsign : Φ ⟨x * y, hvS⟩ ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      have := congrArg Equiv.Perm.sign h3'
      rw [map_pow, map_one] at this
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Φ ⟨x * y, hvS⟩)) with h | h
      · exact h
      · rw [h] at this
        exact absurd this (by decide)
    rw [← hCA] at hsign
    obtain ⟨w, hw, hwe⟩ := hsign
    rwa [Φ.injective hwe] at hw
  refine ⟨C.map S.subtype, (Subgroup.map_subtype_le C).trans hsup.ge, ?_, x * y, ⟨_, hvC, rfl⟩,
    h3, fun hcen => hc (Subgroup.mem_center_iff.1 hcen c).symm⟩
  rw [← Subgroup.map_commutator, hCperf]

end Tail

section Families

variable {Y : Type} [Group Y] [Finite Y]

theorem isElemAbelian_of_model_psl_two {n : ℕ} (h : StatedClassicalModel Y .PSL n 2 1)
    (T : Sylow 2 Y) (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    ∀ U : Subgroup Y, U ≤ J → IsPGroup 3 U → IsElemAbelian 3 U := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine (borelQuotient_sl ((projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans
    e.symm)).isElemAbelian_of_threePerfect (by rw [hF2]; norm_num) (twoLevi_sl hF2)
    (fun _ _ h => h.elim) (fun i => (hasSL2Node_sl i).hasOrderThree) (fun i => Or.inr ?_)
    T J hNJ hJ hperf
  obtain ⟨φ, -, hx, hy⟩ := SL.rankOne (F := F) i
  exact card_rankOne_dvd_six_of_sl2 hF2 SL.isParametrization hx hy

open CFSG.LieType.Universal.Spin in
theorem isElemAbelian_of_model_pomegaPlus_two {n : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 1) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    ∀ U : Subgroup Y, U ≤ J → IsPGroup 3 U → IsElemAbelian 3 U := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  have hB := borelQuotient_spinPlus hn3 e
  refine hB.isElemAbelian_of_threePerfect (by rw [hF2]; norm_num)
    (twoLevi_spinPlus hF2 hn3 hB.ct hB.extras) (fun _ _ h => h.elim)
    (fun i => (hasSL2Node_spinPlus hn3 i).hasOrderThree) (fun i => Or.inr ?_) T J hNJ hJ hperf
  obtain ⟨φ, -, hx, hy⟩ := SpinPlus.rankOne (K := F) hn3 i
  exact card_rankOne_dvd_six_of_sl2 hF2 (SpinPlus.isParametrization hn3) hx hy

open CFSG.LieType.Universal.Spin in
theorem isElemAbelian_of_model_pomegaMinus_two {n : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 1) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    ∀ U : Subgroup Y, U ≤ J → IsPGroup 3 U → IsElemAbelian 3 U := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hB := borelQuotient_spinMinus hirr (by omega) e
  refine hB.isElemAbelian_of_threePerfect (by rw [hF2]; norm_num)
    (twoLevi_spinMinus hirr hB.ct hB.extras hF2) (fun _ _ h => h.elim)
    (fun i => hasOrderThree_spinMinus hirr i) (fun i => ?_) T J hNJ hJ hperf
  by_cases hk : i.val + 1 < n - 1
  · exact Or.inr (dvd_of_eq (spinMinus_long_card hirr hF2 hk))
  · exact Or.inl (spinMinus_short_perfect hirr hF2 hk)

theorem isElemAbelian_of_model_psp_two {n : ℕ} (h : StatedClassicalModel Y .PSp n 2 1)
    (T : Sylow 2 Y) (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    ∀ U : Subgroup Y, U ≤ J → IsPGroup 3 U → IsElemAbelian 3 U := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hcard
  have := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  refine (borelQuotient_sp e).isElemAbelian_of_threePerfect (by rw [hK2]; norm_num)
    (twoLevi_sp hK2) (fun (i j : Fin n) hij => ?_) (fun i => (hasSL2Node_sp i).hasOrderThree)
    (fun i => Or.inr ?_) T J hNJ hJ hperf
  · rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hj : j = ⟨i.val + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [hj]
      exact sp_tail_exc_three hK2 h1
    · have hi : i = ⟨j.val + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [hi, sup_comm]
      exact sp_tail_exc_three hK2 h1
  · obtain ⟨φ, -, hx, hy⟩ := Sp.rankOne (F := K) i
    exact card_rankOne_dvd_six_of_sl2 hK2 Sp.isParametrization hx hy

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits in
theorem isElemAbelian_of_su_even {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ} (hn : 4 ≤ n) (he : Even n)
    (α : SU (unitaryInvolution F 2 1) n →* Y) (hα : Function.Surjective α)
    (hker : α.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 1) n))
    (T : Sylow 2 Y) (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    ∀ U : Subgroup Y, U ≤ J → IsPGroup 3 U → IsElemAbelian 3 U := by
  have : Finite (SU (unitaryInvolution F 2 1) n) := Finite.of_injective _ Subtype.val_injective
  obtain ⟨nW, H, hB⟩ := CFSG.AGLEmbedding.LieOut.borelQuotient_su_of_surjective (hF := hF)
    (by omega) (fun h => by simp at h; omega) α hα hker
  refine hB.isElemAbelian_of_threePerfect (by rw [hF]; norm_num) (twoLevi_su hF)
    (fun _ _ h => h.elim) (fun i => hasOrderThree_su hF i) (fun i => ?_) T J hNJ hJ hperf
  by_cases hk : i.val + 1 < n / 2
  · exact Or.inl (commutator_eq_self_of_isPerfect (su_short_isPerfect hF hk))
  · exact Or.inr (dvd_of_eq (su_last_even_card hF he hk))

end Families

end CFSG.AGLEmbedding.ParabHub
