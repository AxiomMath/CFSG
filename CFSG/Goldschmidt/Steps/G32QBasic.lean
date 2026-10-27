module

public import CFSG.Goldschmidt.Steps.G3aBorel
import CFSG.Goldschmidt.Steps.GoldTypeBender
import CFSG.LieType.Steinberg.Collection

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le)

namespace G32Q

section Closure

variable {L : Type*} [Group L]

theorem stronglyClosed_of_isSStarIn [Finite L] {A : Subgroup L} (hA : IsSStarIn ⊤ A)
    (T : Sylow 2 L) (hAT : A ≤ T) : fusionStronglyClosed (A : Set L) (T : Subgroup L) := by
  obtain ⟨-, -, T₀, hT₀, -, hcl, -⟩ := hA
  let S₀ : Sylow 2 L :=
    { toSubgroup := T₀
      isPGroup' := hT₀.2.1
      is_maximal' := fun {Q} hQ hTQ => hT₀.2.2 Q le_top hQ hTQ }
  exact stronglyClosed_of_le_sylow S₀ T (fun x hx g hg => hcl x hx g (Subgroup.mem_top g) hg) hAT

theorem normalizer_le_normalizer {A T : Subgroup L} (hAT : A ≤ T)
    (hcl : fusionStronglyClosed (A : Set L) T) :
    Subgroup.normalizer (T : Set L) ≤ Subgroup.normalizer (A : Set L) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · intro hx
    have h1 : g⁻¹⁻¹ * x * g⁻¹ ∈ T := by
      rw [inv_inv]
      exact (hg x).mp (hAT hx)
    have h2 := hcl x hx g⁻¹ h1
    rwa [inv_inv] at h2
  · intro hx
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    have h1 : g⁻¹ * (g * x * g⁻¹) * g ∈ T := by
      rw [e]
      exact (hg x).mpr (hAT hx)
    have h2 := hcl _ hx g h1
    rwa [e] at h2

end Closure

section Borel

variable {X : Type} [Group X] [Finite X] {T : Sylow 2 X} {D : Subgroup X}

omit [Finite X] in
theorem le_normalizer_sylowCenter (h : G3a.BorelSetup T D) :
    D ≤ Subgroup.normalizer (sylowCenter (T : Subgroup X) : Set X) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => h.conj_mem_center hd hz, fun hz => ?_⟩
  have := h.conj_mem_center (D.inv_mem hd) hz
  simpa [mul_assoc] using this

theorem le_sylowCenter
    (h : G3a.BorelSetup T D) (hX : fusionIsBenderGroup X) {B : Subgroup X}
    (hBT : B ≤ T) (hB : IsMulCommutative B) (hDB : D ≤ Subgroup.normalizer (B : Set X)) :
    B ≤ sylowCenter (T : Subgroup X) := by
  by_cases hab : IsMulCommutative (T : Subgroup X)
  · intro x hx
    refine mem_sylowCenter.mpr ⟨hBT hx, fun t ht => ?_⟩
    exact congrArg Subtype.val (hab.is_comm.comm ⟨t, ht⟩ ⟨x, hBT hx⟩)
  have hcase : (Nat.card (T : Subgroup X) = Nat.card (sylowCenter (T : Subgroup X)) ^ 2 ∧
        Nat.card D = Nat.card (sylowCenter (T : Subgroup X)) - 1) ∨
      (Nat.card (T : Subgroup X) = Nat.card (sylowCenter (T : Subgroup X)) ^ 3 ∧
        Nat.card D = (Nat.card (sylowCenter (T : Subgroup X)) ^ 2 - 1) /
          Nat.gcd 3 (Nat.card (sylowCenter (T : Subgroup X)) + 1)) := by
    rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exact absurd (GoldType.isMulCommutative_of_psl2_even hf e T) hab
    · obtain ⟨hZc, hTc, hDc⟩ := h.orders_psu3 hf e
      right
      rw [hZc, hTc, hDc]
      exact ⟨rfl, rfl⟩
    · obtain ⟨hZc, hTc, hDc⟩ := h.orders_sz hn e
      left
      rw [hZc, hTc, hDc]
      exact ⟨rfl, rfl⟩
  have hYT : B ⊔ sylowCenter (T : Subgroup X) ≤ T := sup_le hBT (sylowCenter_le _)
  rcases h.eq_or_eq_of_invariant hcase le_sup_right hYT
      (CFSG.LieType.Steinberg.le_normalizer_sup hDB (le_normalizer_sylowCenter h)) with hY | hY
  · exact le_sup_left.trans hY.le
  · exfalso
    apply hab
    have hZB : sylowCenter (T : Subgroup X) ≤ Subgroup.centralizer (B : Set X) := fun z hz =>
      Subgroup.mem_centralizer_iff.mpr fun b hb => (mem_sylowCenter.mp hz).2 b (hBT hb)
    have hB' : B ≤ Subgroup.centralizer
        ((B ⊔ sylowCenter (T : Subgroup X) : Subgroup X) : Set X) :=
      Subgroup.le_centralizer_iff.mpr
        (sup_le (Subgroup.le_centralizer_iff_isMulCommutative.mpr hB) hZB)
    have hZ' : sylowCenter (T : Subgroup X) ≤ Subgroup.centralizer
        ((B ⊔ sylowCenter (T : Subgroup X) : Subgroup X) : Set X) := fun z hz =>
      Subgroup.centralizer_le hYT
        (Subgroup.mem_centralizer_iff.mpr fun t ht => (mem_sylowCenter.mp hz).2 t ht)
    have hc := sup_le hB' hZ'
    rw [hY] at hc
    exact Subgroup.le_centralizer_iff_isMulCommutative.mp hc

theorem eq_sylowCenter
    (h : G3a.BorelSetup T D) (hX : fusionIsBenderGroup X) {B : Subgroup X}
    (hBT : B ≤ T) (hB : IsMulCommutative B) (hDB : D ≤ Subgroup.normalizer (B : Set X))
    (hB1 : B ≠ ⊥) : B = sylowCenter (T : Subgroup X) := by
  have hle := le_sylowCenter h hX hBT hB hDB
  refine le_antisymm hle fun z hz => ?_
  by_cases hz1 : z = 1
  · rw [hz1]
    exact B.one_mem
  obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
  obtain ⟨d, hd, hdz⟩ := h.trans (hle b.2) hz (fun h1 => hb1 (Subtype.ext h1)) hz1
  rw [← hdz]
  have := (Subgroup.mem_normalizer_iff.mp (hDB (D.inv_mem hd)) b).mp b.2
  simpa using this

theorem inf_centralizer_sylowCenter_eq_bot (h : G3a.BorelSetup T D)
    (hD : Nat.card D = Nat.card (sylowCenter (T : Subgroup X)) - 1) :
    D ⊓ Subgroup.centralizer (sylowCenter (T : Subgroup X) : Set X) = ⊥ := by
  have hmul := h.card_eq_mul
  rw [hD] at hmul
  have hq : 0 < Nat.card (sylowCenter (T : Subgroup X)) - 1 := by
    have := h.four
    omega
  exact Subgroup.card_eq_one.mp
    (Nat.eq_of_mul_eq_mul_left hq (hmul.symm.trans (mul_one _).symm))

omit [Finite X] in
theorem mem_of_commute_sylowCenter (h : G3a.BorelSetup T D)
    (hker : D ⊓ Subgroup.centralizer (sylowCenter (T : Subgroup X) : Set X) = ⊥) {g : X}
    (hg : g ∈ Subgroup.normalizer ((T : Subgroup X) : Set X))
    (hgZ : ∀ z ∈ sylowCenter (T : Subgroup X), g * z = z * g) : g ∈ (T : Subgroup X) := by
  obtain ⟨t, ht, d, hd, rfl⟩ := h.exists_mul hg
  have hdC : d ∈ Subgroup.centralizer (sylowCenter (T : Subgroup X) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 := hgZ z hz
    have h2 : t * z = z * t := (mem_sylowCenter.mp hz).2 t ht
    have h3 : t * (d * z) = t * (z * d) := by
      calc t * (d * z) = t * d * z := by group
        _ = z * (t * d) := h1
        _ = z * t * d := by group
        _ = t * z * d := by rw [h2]
        _ = t * (z * d) := by group
    exact (mul_left_cancel h3).symm
  have hd1 : d ∈ D ⊓ Subgroup.centralizer (sylowCenter (T : Subgroup X) : Set X) := ⟨hd, hdC⟩
  rw [hker, Subgroup.mem_bot] at hd1
  rw [hd1, mul_one]
  exact ht

end Borel

end G32Q

end CFSG.Goldschmidt
