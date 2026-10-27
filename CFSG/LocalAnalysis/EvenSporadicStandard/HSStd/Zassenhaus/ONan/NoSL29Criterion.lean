module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.NoSL29Reduction

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup

@[expose] def NoPerfect720Centralizing (N : Type*) [Group N] : Prop :=
  ∀ z : N, orderOf z = 2 → ∀ H : Subgroup N, H ≤ centralizer ({z} : Set N) → ⁅H, H⁆ = H →
    Nat.card H = 720 → False

theorem false_of_injective_of_noPerfect720Centralizing {N : Type*} [Group N] [Finite N]
    (hN : NoPerfect720Centralizing N) (K : Type*) [Group K] [Finite K]
    (hK : commutator K = ⊤) (hZ : Nat.card (center K) = 2)
    (hA : Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 6))) (f : K →* N)
    (hf : Function.Injective f) : False := by
  classical
  obtain ⟨e⟩ := hA
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hK720 : Nat.card K = 720 := by
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
    have heq : Nat.card (K ⧸ center K) = 360 := by
      rw [Nat.card_congr e.toEquiv, hA6]
    rw [heq, hZ] at hq
    omega
  have hHcard : Nat.card f.range = Nat.card K :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  obtain ⟨c, hcne, -⟩ := (Nat.card_eq_two_iff' (1 : center K)).1 hZ
  have hc2 : orderOf ((c : center K) : K) = 2 := by
    rw [Subgroup.orderOf_coe]
    have hdvd : orderOf c ∣ 2 := by
      rw [← hZ]; exact orderOf_dvd_natCard c
    have hne1 : orderOf c ≠ 1 := (orderOf_eq_one_iff (x := c)).not.mpr hcne
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hz : orderOf (f (c : K)) = 2 := by
    rw [orderOf_injective f hf, hc2]
  have hle : f.range ≤ centralizer ({f (c : K)} : Set N) := by
    rintro x ⟨k, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← f.map_mul, ← f.map_mul,
      Subgroup.mem_center_iff.1 c.property k]
  have hperf : ⁅f.range, f.range⁆ = f.range := by
    have htop : (⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆) = (⊤ : Subgroup K) := by
      rw [← _root_.commutator_def]; exact hK
    rw [MonoidHom.range_eq_map]
    rw [show (⁅(⊤ : Subgroup K).map f, (⊤ : Subgroup K).map f⁆) =
        ((⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ : Subgroup K).map f) from
      (Subgroup.map_commutator (⊤ : Subgroup K) (⊤ : Subgroup K) f).symm, htop]
  exact hN (f (c : K)) hz f.range hle hperf (by rw [hHcard, hK720])

theorem noPerfect720Centralizing_of_forall {N : Type*} [Group N] [Finite N]
    (h : ∀ z : N, orderOf z = 2 → ¬ 720 ∣ Nat.card (centralizer ({z} : Set N)) ∨
      ∃ D : Subgroup N, (∀ H : Subgroup N, H ≤ centralizer ({z} : Set N) → ⁅H, H⁆ = H → H ≤ D) ∧
        Nat.card D < 720) :
    NoPerfect720Centralizing N := by
  intro z hz H hle hperf hcard
  rcases h z hz with hndvd | ⟨D, hD, hDlt⟩
  · exact hndvd (hcard ▸ Subgroup.card_dvd_of_le hle)
  · have hleD : Nat.card H ≤ Nat.card D := Subgroup.card_le_of_le (hD H hle hperf)
    omega

theorem NoPerfect720Centralizing.of_mulEquiv {N M : Type*} [Group N] [Group M] (e : N ≃* M)
    (hM : NoPerfect720Centralizing M) : NoPerfect720Centralizing N := by
  intro z hz H hle hperf hcard
  have hz' : orderOf (e.toMonoidHom z) = 2 := by
    change orderOf (e z) = 2
    rw [MulEquiv.orderOf_eq]; exact hz
  refine hM (e.toMonoidHom z) hz' (H.map e.toMonoidHom) ?_ ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa only [map_mul] using
      congrArg (fun w => e.toMonoidHom w)
        (Subgroup.mem_centralizer_singleton_iff.mp (hle hy))
  · rw [← Subgroup.map_commutator, hperf]
  · rw [Subgroup.card_map_of_injective e.injective, hcard]

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
