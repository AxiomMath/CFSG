module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSUOdd
import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviBorel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSU

public section

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.LieType.CurtisTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ}

include hF in
theorem exists_lastNode_decomposition_su (hn4 : 4 ≤ n) {k : Fin (n / 2)}
    (hk : ¬k.val + 1 < n / 2) {W : Type} [Group W] [Finite W]
    (α : SU (unitaryInvolution F 2 1) n →* W) (hα : Function.Surjective α)
    (hker : α.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 1) n))
    (T : Sylow 2 W) (J : Subgroup W)
    (hNJ : Subgroup.normalizer ((T : Subgroup W) : Set W) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup W) : Set W))
    (hperf : ∀ U : Subgroup W, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    ∃ (ζ : traceZero (unitaryInvolution F 2 1)) (π' : SU (unitaryInvolution F 2 1) n →* W),
      BorelQuotient (rootDatum hF n) (levelWeyl (unitaryInvolution_involutive hF) ζ)
        (levelTorus (unitaryInvolution F 2 1)) π' (Nat.card F - 1) ∧
      (rankOne (rootDatum hF n).rootGroup k).map π' ≤ J ∧
      (⨆ i, levelTorus (unitaryInvolution F 2 1) (n := n) i).map π' ≤ J ∧
      (posUnipotentExcept (rootDatum hF n) k).map π' ≤ J ∧
      ∀ z ∈ J, ∃ l ∈ rankOne (rootDatum hF n).rootGroup k,
        ∃ t ∈ ⨆ i, levelTorus (unitaryInvolution F 2 1) (n := n) i,
          ∃ u ∈ posUnipotentExcept (rootDatum hF n) k, z = π' (l * t * u) := by
  have : Finite (SU (unitaryInvolution F 2 1) n) := Finite.of_injective _ Subtype.val_injective
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hB := borelQuotient_su_level hF (by omega) (fun h => by simp at h; omega) hζ α hα hker
  obtain ⟨π', hπ', hker', hT⟩ := hB.exists_conj_eq T
  have hQ : BorelQuotient (rootDatum hF n) (levelWeyl (unitaryInvolution_involutive hF) ζ)
      (levelTorus (unitaryInvolution F 2 1)) π' (Nat.card F - 1) :=
    { ct := hB.ct, extras := hB.extras, pGroup := hB.pGroup, surj := hπ', odd := hB.odd
      torus_pow := hB.torus_pow
      ker_central := fun z hz => hB.ker_central z (hker' ▸ hz)
      ker_pow := fun z hz => hB.ker_pow z (hker' ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1))).map π' ≤ J :=
    hNπ ▸ hNJ
  have hBA : borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) ≤ J.comap π' :=
    fun b hb => hBJ ⟨b, hb, rfl⟩
  have hnodes : ∀ i ∈ negIndices (rootDatum hF n) (J.comap π'), i = k := by
    intro i hi
    by_contra hik
    have hshort : i.val + 1 < n / 2 := by
      have h1 : i.val < n / 2 := i.isLt
      have h2 : i.val ≠ k.val := fun h => hik (Fin.ext h)
      have h3 : k.val < n / 2 := k.isLt
      omega
    have hLi := rankOne_le_of_mem_negIndices hBA hi
    obtain ⟨a, ha, b, hb, hab3, c, hc⟩ := hasOrderThree_su hF i
    have habL : a * b ∈ rankOne (rootDatum hF n).rootGroup i :=
      mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
    have hord : orderOf (π' (a * b)) = 3 :=
      orderOf_eq_prime (by rw [← map_pow, hab3, map_one]) fun h1 =>
        hc (Subgroup.mem_center_iff.1 (hQ.ker_central _ h1) c).symm
    have hdvd : 3 ∣ Nat.card ((rankOne (rootDatum hF n).rootGroup i).map π') := by
      have := Subgroup.orderOf_dvd_natCard ((rankOne (rootDatum hF n).rootGroup i).map π')
        ⟨a * b, habL, rfl⟩
      rwa [hord] at this
    have hp := commutator_eq_self_of_isPerfect (su_short_isPerfect hF hshort)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (hperf _ (Subgroup.map_le_iff_le_comap.2 hLi) (by rw [← Subgroup.map_commutator, hp])) hdvd
  have hAne : J.comap π' ≠ borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) := by
    intro he
    apply hJ
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ']
  obtain ⟨i₀, hi₀⟩ := negIndices_nonempty_of_ne hQ.ct hQ.extras hBA hAne
  have hk₀ : k ∈ negIndices (rootDatum hF n) (J.comap π') := hnodes i₀ hi₀ ▸ hi₀
  have hLJ : (rankOne (rootDatum hF n).rootGroup k).map π' ≤ J :=
    Subgroup.map_le_iff_le_comap.2 (rankOne_le_of_mem_negIndices hBA hk₀)
  have hTJ : (⨆ i, levelTorus (unitaryInvolution F 2 1) (n := n) i).map π' ≤ J :=
    (Subgroup.map_mono (iSup_le_borel (D := rootDatum hF n)
      (H := levelTorus (unitaryInvolution F 2 1)))).trans hBJ
  have hUJ : (posUnipotentExcept (rootDatum hF n) k).map π' ≤ J :=
    (Subgroup.map_mono ((posUnipotentExcept_le_posUnipotent (D := rootDatum hF n) k).trans
      (posUnipotent_le_borel (D := rootDatum hF n)
        (H := levelTorus (unitaryInvolution F 2 1))))).trans hBJ
  have hTL := iSup_torus_le_normalizer_rankOne hQ.ct k
  have hLU := rankOne_le_normalizer_posUnipotentExcept hQ.ct hQ.extras k
  refine ⟨ζ, π', hQ, hLJ, hTJ, hUJ, fun z hz => ?_⟩
  obtain ⟨g, hg, _, ⟨b, hb, rfl⟩, rfl⟩ := exists_mul_of_mem_of_borel_le hQ.ct hQ.extras hπ'
    hBJ hz
  have hle : (⨆ i ∈ negIndices (rootDatum hF n) (J.comap π'),
      (rankOne (rootDatum hF n).rootGroup i).map π') ≤
        (rankOne (rootDatum hF n).rootGroup k).map π' := iSup₂_le fun i hi => by
    obtain rfl := hnodes i hi
    exact le_rfl
  obtain ⟨l, hl, rfl⟩ := hle hg
  obtain ⟨t, ht, u, hu, w, hw, rfl⟩ := exists_eq_mul_mul_of_mem_borel hQ.ct hQ.extras k hb
  have hwL : w ∈ rankOne (rootDatum hF n).rootGroup k := Subgroup.mem_sup_left hw
  refine ⟨l * (t * w * t⁻¹), mul_mem hl ((Subgroup.mem_normalizer_iff.1 (hTL ht) w).1 hwL), t,
    ht, w⁻¹ * u * w, ?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.1 (hLU (inv_mem hwL)) u).1 hu
    rwa [inv_inv] at this
  · rw [← map_mul]
    congr 1
    group

include hF in
theorem isThreeExceptional_of_su_odd (hn5 : 5 ≤ n) (hn : ¬Even n) {W : Type} [Group W]
    [Finite W] (α : SU (unitaryInvolution F 2 1) n →* W) (hα : Function.Surjective α)
    (hker : α.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 1) n))
    (T : Sylow 2 W) (J : Subgroup W)
    (hNJ : Subgroup.normalizer ((T : Subgroup W) : Set W) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup W) : Set W))
    (hperf : ∀ U : Subgroup W, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    IsThreeExceptional J := by
  have : Finite (SU (unitaryInvolution F 2 1) n) := Finite.of_injective _ Subtype.val_injective
  set k : Fin (n / 2) := ⟨n / 2 - 1, by omega⟩ with hkdef
  have hk : ¬k.val + 1 < n / 2 := by simp only [hkdef]; omega
  obtain ⟨ζ, π', hQ, hLJ, hTJ, hUJ, hdec⟩ :=
    exists_lastNode_decomposition_su hF (by omega) hk α hα hker T J hNJ hJ hperf
  obtain ⟨x, y, hE⟩ := endNodeSUThree_su hF hn5 hn hk hQ
  refine hE.isThreeExceptional hQ.surj hQ.ker_central (fun c hc => ?_) hLJ hTJ hUJ hdec
  have h3 := hQ.ker_pow c hc
  rwa [hF] at h3

end CFSG.AGLEmbedding
