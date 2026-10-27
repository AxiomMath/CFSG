module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.NoSL29Criterion
public import CFSG.Sporadic.SmallOddCore.HSLocal
public import CFSG.GroupTheory.PerfectLeOfPGroupQuotient

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier

theorem noPerfect720_of_hsP
    {τ : Equiv.Perm (Fin 3850)} (hτP : τ ∈ CFSG.Sporadic.Schreier.hsP) (hτ : orderOf τ = 2)
    {F : Subgroup (Equiv.Perm (Fin 3850))}
    (hF : F ≤ CFSG.Sporadic.Schreier.hsP ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 3850))))
    (hperf : ⁅F, F⁆ = F) (hcard : Nat.card F = 720) : False := by
  obtain ⟨r, hr, g, hg, hτeq⟩ := hs_reps.2.2.2.2 τ hτP hτ
  set F' : Subgroup (Equiv.Perm (Fin 3850)) := F.map (MulAut.conj g⁻¹).toMonoidHom with hF'def
  have hconj : ∀ y : Equiv.Perm (Fin 3850), (MulAut.conj g⁻¹) ((MulAut.conj g) y) = y := by
    intro y
    simp only [MulAut.conj_apply, inv_inv]
    group
  have hCτ : CFSG.Sporadic.Schreier.hsP ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 3850))) =
      (CFSG.Sporadic.Schreier.hsP ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 3850)))).map
        (MulAut.conj g).toMonoidHom := by
    rw [hτeq]
    exact inf_centralizer_conj CFSG.Sporadic.Schreier.hsP hg r
  have hF'le : F' ≤ CFSG.Sporadic.Schreier.hsP ⊓
      centralizer ({r} : Set (Equiv.Perm (Fin 3850))) := by
    rw [hF'def, Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap]
    have hxτ : x ∈ CFSG.Sporadic.Schreier.hsP ⊓
        centralizer ({τ} : Set (Equiv.Perm (Fin 3850))) := hF hx
    rw [hCτ, Subgroup.mem_map] at hxτ
    obtain ⟨y, hy, rfl⟩ := hxτ
    rw [show (MulEquiv.toMonoidHom (MulAut.conj g⁻¹))
        ((MulEquiv.toMonoidHom (MulAut.conj g)) y) = y from hconj y]
    exact hy
  have hperf' : ⁅F', F'⁆ = F' := by
    rw [hF'def, ← Subgroup.map_commutator F F (MulAut.conj g⁻¹).toMonoidHom, hperf]
  have hcard' : Nat.card F' = 720 := by
    rw [hF'def, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcard]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl
  · have hle : F' ≤ hsC1 := hF'le
    have hdvd : 720 ∣ 7680 := by
      have h := Subgroup.card_dvd_of_le hle
      rw [hcard', hs_reps.2.2.1] at h
      exact h
    norm_num at hdvd
  · obtain ⟨-, hDcard, hDC2, hC2D, -⟩ := hs_D_facts
    have hle : F' ≤ hsC2 := hF'le
    have hidx8 : (genGroup 3850 hsDGens hsDPerm).relIndex hsC2 = 8 := by
      have h8 : (genGroup 3850 hsDGens hsDPerm).relIndex hsC2 * 360 = 8 * 360 := by
        have h := Subgroup.relIndex_mul_card (H := genGroup 3850 hsDGens hsDPerm) (K := hsC2)
        rw [inf_eq_left.mpr hDC2, hDcard, hs_reps.2.2.2.1] at h
        rw [show (2880 : ℕ) = 8 * 360 by norm_num] at h
        exact h
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h8
    have hidx : (genGroup 3850 hsDGens hsDPerm).relIndex hsC2 = 2 ^ 3 := by
      rw [hidx8]; norm_num
    have hFD : F' ≤ genGroup 3850 hsDGens hsDPerm :=
      Subgroup.le_of_commutator_eq_self_of_relIndex_eq_prime_pow (p := 2) (k := 3)
        Nat.prime_two hDC2 hC2D hidx hle hperf'
    have h720 : Nat.card F' ≤ Nat.card (genGroup 3850 hsDGens hsDPerm) :=
      Subgroup.card_le_of_le hFD
    rw [hcard', hDcard] at h720
    omega

theorem noPerfect720Centralizing_hsP :
    NoPerfect720Centralizing ↥CFSG.Sporadic.Schreier.hsP := by
  intro z hz H hle hperf hcard
  refine noPerfect720_of_hsP (F := H.map CFSG.Sporadic.Schreier.hsP.subtype)
    z.2 (by rw [Subgroup.orderOf_coe, hz]) ?_ ?_ ?_
  · rintro x ⟨h, hh, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨h.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcz := Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
    simpa using congrArg Subtype.val hcz
  · rw [← Subgroup.map_commutator H H CFSG.Sporadic.Schreier.hsP.subtype, hperf]
  · rw [Subgroup.card_map_of_injective CFSG.Sporadic.Schreier.hsP.subtype_injective, hcard]

theorem noSL29_of_isSporadic_hs
    {N : Type} [Group N] [Finite N]
    (hN : CFSG.Blueprint.NativeSporadic.IsSporadic N .HS) (K : Type) [Group K] [Finite K]
    (hK : commutator K = ⊤) (hZ : Nat.card (center K) = 2)
    (hA : Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 6))) (f : K →* N)
    (hf : Function.Injective f) : False := by
  obtain ⟨e⟩ := hN
  have e' : N ≃* CFSG.Blueprint.NativeSporadic.HS := e
  exact false_of_injective_of_noPerfect720Centralizing
    (NoPerfect720Centralizing.of_mulEquiv (e'.trans CFSG.Sporadic.Schreier.hsPermEquiv)
      noPerfect720Centralizing_hsP) K hK hZ hA f hf

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

