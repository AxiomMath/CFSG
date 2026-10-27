module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.FixLarge

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

structure ExcQuot (Q : Type) [Group Q] : Prop where
  center_eq_bot : center Q = ⊥
  card_mulAut_dvd : Nat.card (MulAut Q) ∣ 6 * Nat.card Q
  fixLarge : FixLarge Q
  two_pow_dvd : 2 ^ 12 ∣ Nat.card Q
  involution_centralizer : ∀ q : Q, q * q = 1 → q ≠ 1 →
    2 ^ 12 ∣ Nat.card (centralizer ({q} : Set Q)) ∨
      (4 < Nat.card (centralizer ({q} : Set Q)) ∧
        ¬ 7 ∣ Nat.card (centralizer ({q} : Set Q)) ∧
        ¬ 11 ∣ Nat.card (centralizer ({q} : Set Q)))

theorem fixedSubgroup_conj_eq_centralizer {G : Type*} [Group G] (s : G) :
    fixedSubgroup (MulAut.conj s) = Subgroup.centralizer ({s} : Set G) := by
  ext x
  change MulAut.conj s x = x ↔ _
  rw [MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * s = s * x * s⁻¹ * s := by rw [h]
      _ = s * x := by group
  · intro h
    rw [← h, mul_inv_cancel_right]

theorem card_centralizer_quotient_dvd {K : Type} [Group K] [Finite K] (k : K) :
    Nat.card (centralizer ({(k : K ⧸ center K)} : Set (K ⧸ center K))) ∣
      Nat.card (centralizer ({k} : Set K)) := by
  have h := card_fixed_centerQuotAut_dvd (MulAut.conj k)
  rwa [centerQuotAut_conj, fixedSubgroup_conj_eq_centralizer,
    fixedSubgroup_conj_eq_centralizer] at h

theorem fixLarge_of_excQuot {K : Type} [Group K] [Finite K] (h : ExcQuot (K ⧸ center K)) :
    FixLarge K := by
  intro ζ hζ
  have hσ : centerQuotAut ζ * centerQuotAut ζ = 1 := by
    rw [← centerQuotAut_mul, hζ, centerQuotAut_one]
  have hlarge : 4 < Nat.card (fixedSubgroup (centerQuotAut ζ)) := h.fixLarge _ hσ
  have hdvd : Nat.card (fixedSubgroup (centerQuotAut ζ)) ∣ Nat.card (fixedSubgroup ζ) :=
    card_fixed_centerQuotAut_dvd ζ
  have hpos : 0 < Nat.card (fixedSubgroup ζ) :=
    Nat.card_pos_iff.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
  exact lt_of_lt_of_le hlarge (Nat.le_of_dvd hpos hdvd)

theorem card_centralizer_mulEquiv {K L : Type*} [Group K] [Group L] (e : K ≃* L) (u : K) :
    Nat.card (Subgroup.centralizer ({e u} : Set L)) =
      Nat.card (Subgroup.centralizer ({u} : Set K)) := by
  have h : (Subgroup.centralizer ({u} : Set K)).map e.toMonoidHom =
      Subgroup.centralizer ({e u} : Set L) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul, hz]
    · intro hy
      refine ⟨e.symm y, e.injective ?_, e.apply_symm_apply y⟩
      rw [map_mul, map_mul, e.apply_symm_apply, hy]
  rw [← h, Subgroup.card_map_of_injective e.injective]

theorem ExcQuot.of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (h : ExcQuot Q) :
    ExcQuot Q' where
  center_eq_bot := by
    rw [← Subgroup.map_center_eq e, h.center_eq_bot, Subgroup.map_bot]
  card_mulAut_dvd := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv.symm, Nat.card_congr e.toEquiv.symm]
    exact h.card_mulAut_dvd
  fixLarge := FixLarge.of_mulEquiv e h.fixLarge
  two_pow_dvd := by
    rw [Nat.card_congr e.toEquiv.symm]
    exact h.two_pow_dvd
  involution_centralizer := fun q' hq2 hq1 => by
    obtain ⟨q, rfl⟩ := e.surjective q'
    have hq2' : q * q = 1 := e.injective (by rw [map_mul, hq2, map_one])
    have hq1' : q ≠ 1 := fun h1 => hq1 (by rw [h1, map_one])
    rw [card_centralizer_mulEquiv e q]
    exact h.involution_centralizer q hq2' hq1'

theorem card_centralizer_subtype_eq_card_inf {G : Type*} [Group G] (K : Subgroup G) (x : K) :
    Nat.card (centralizer ({x} : Set K)) =
      Nat.card ↥(K ⊓ Subgroup.centralizer ({(x : G)} : Set G)) := by
  have h : (centralizer ({x} : Set K)).map K.subtype =
      K ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, congrArg Subtype.val hz⟩
    · rintro ⟨hy, hyc⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyc, rfl⟩
  rw [← h, Subgroup.card_map_of_injective K.subtype_injective]

theorem card_mulAut_eq_of_card_outer {Q : Type} [Group Q] (hc : center Q = ⊥) {m : ℕ}
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Q) = m) :
    Nat.card (MulAut Q) = m * Nat.card Q := by
  have hinj : Function.Injective (MulAut.conj : Q →* MulAut Q) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hmem : x ∈ center Q := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h := congrArg (fun e : MulAut Q => e y) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc y * x = x * y * x⁻¹ * x := by rw [h]
        _ = x * y := by group
    rw [hc] at hmem
    simpa using hmem
  have hcard : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner Q) =
      Nat.card Q := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h := Subgroup.card_mul_index (CFSG.ComponentClassification.OuterAutomorphisms.inner Q)
  rw [hcard] at h
  rw [← h, ← hout, mul_comm]
  rfl

end CFSG.EvenSporadicStandard.Co3Std.CentT
