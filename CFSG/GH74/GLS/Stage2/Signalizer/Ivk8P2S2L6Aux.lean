module

public import CFSG.GH74.GLS.Stage2.Local.Lemma23eRes
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4

section SL23

theorem sl23_conj4 : ∀ x y : SL23, (x ^ 4 = 1 ∧ x ^ 2 ≠ 1) → (y ^ 4 = 1 ∧ y ^ 2 ≠ 1) →
    ∃ g : SL23, y = g * x * g⁻¹ := by
  decide +kernel

theorem sl2_three_conj4 {Y : Type} [Group Y] {L : Subgroup Y}
    (h : HasSL2Model ↥L (fun r => r = 3)) :
    ∀ x ∈ L, ∀ y ∈ L, (x ^ 4 = 1 ∧ x ^ 2 ≠ 1) → (y ^ 4 = 1 ∧ y ^ 2 ≠ 1) →
      ∃ g ∈ L, y = g * x * g⁻¹ := by
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := h
  have hq' : Nat.card F = 3 := hq
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hq', ZMod.card]
  let φ : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hcard
  let Φ : ↥L ≃* SL23 :=
    (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm).trans
      (slMapEquiv φ)
  have conv : ∀ u : Y, ∀ hu : u ∈ L, (u ^ 4 = 1 ∧ u ^ 2 ≠ 1) →
      ((Φ ⟨u, hu⟩) ^ 4 = 1 ∧ (Φ ⟨u, hu⟩) ^ 2 ≠ 1) := by
    intro u hu ⟨h4, h2⟩
    refine ⟨?_, ?_⟩
    · rw [← map_pow, show (⟨u, hu⟩ : ↥L) ^ 4 = 1 from Subtype.ext (by simpa using h4), map_one]
    · intro h
      apply h2
      have : (⟨u, hu⟩ : ↥L) ^ 2 = 1 := Φ.injective (by rw [map_pow, h, map_one])
      simpa using congrArg Subtype.val this
  intro x hx y hy hxo hyo
  obtain ⟨g, hg⟩ := sl23_conj4 _ _ (conv x hx hxo) (conv y hy hyo)
  refine ⟨((Φ.symm g : ↥L) : Y), (Φ.symm g).2, ?_⟩
  have h2 : (⟨y, hy⟩ : ↥L) = Φ.symm g * ⟨x, hx⟩ * (Φ.symm g)⁻¹ :=
    Φ.injective (by rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]; exact hg)
  simpa using congrArg Subtype.val h2

end SL23

section HallHigman

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem centralizes_of_mul_eq {A : Subgroup X} [A.Normal] (hA : Odd (Nat.card A)) {s n a : X}
    (hs : ∃ k : ℕ, s ^ (2 ^ k) = 1) (hn : ∀ x ∈ A, n * x = x * n) (ha : a ∈ A) (hsna : s = n * a) :
    ∀ x ∈ A, s * x = x * s := by
  obtain ⟨k, hk⟩ := hs
  let ψ : MulAut ↥A := MulAut.conjNormal s
  let χ : MulAut ↥A := MulAut.conjNormal a
  have hψχ : ψ = χ := by
    ext x
    show s * (x : X) * s⁻¹ = a * (x : X) * a⁻¹
    have hax : a * (x : X) * a⁻¹ ∈ A := (inferInstance : A.Normal).conj_mem _ x.2 a
    have h1 := hn _ hax
    calc s * (x : X) * s⁻¹ = n * (a * x * a⁻¹) * n⁻¹ := by rw [hsna]; group
      _ = (a * x * a⁻¹ * n) * n⁻¹ := by rw [h1]
      _ = a * x * a⁻¹ := by group
  have hψ1 : ψ ^ (2 ^ k) = 1 := by
    have : ψ ^ (2 ^ k) = MulAut.conjNormal (s ^ (2 ^ k)) :=
      (map_pow (MulAut.conjNormal : X →* MulAut ↥A) s (2 ^ k)).symm
    rw [this, hk, map_one]
  have hao : orderOf a ∣ Nat.card A := by
    have h1 : orderOf (⟨a, ha⟩ : A) ∣ Nat.card A := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk] at h1
  have hodd : (orderOf a).Coprime 2 := Nat.coprime_two_right.2 (Odd.of_dvd_nat hA hao)
  have hχ1 : ψ ^ (orderOf a) = 1 := by
    have : ψ ^ (orderOf a) = MulAut.conjNormal (a ^ (orderOf a)) := by
      rw [hψχ]
      exact (map_pow (MulAut.conjNormal : X →* MulAut ↥A) a (orderOf a)).symm
    rw [this, pow_orderOf_eq_one, map_one]
  have h2 : orderOf ψ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hψ1
  have h3 : orderOf ψ ∣ orderOf a := orderOf_dvd_of_pow_eq_one hχ1
  have h4 : orderOf ψ = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k hodd) h3 h2
  have hψ : ψ = 1 := orderOf_eq_one_iff.1 h4
  intro x hx
  have h5 := congrArg (fun φ : MulAut ↥A => ((φ ⟨x, hx⟩ : ↥A) : X)) hψ
  change s * x * s⁻¹ = x at h5
  calc s * x = (s * x * s⁻¹) * s := by group
    _ = x * s := by rw [h5]

end HallHigman


end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2
