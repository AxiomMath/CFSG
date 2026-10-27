module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LocalAnalysis.ComponentClassification.GS82L34Omega
public import CFSG.GH74.GLS.Basic
public import CFSG.GH74.GLS.TwoThin.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import CFSG.Certificates.Kernel.ThDemp.OrbCent

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace LiftAux

theorem inv_pow_mul_pow_mem {G : Type*} [Group G] {N : Subgroup G} {a c : G}
    (hN : ∀ n ∈ N, a⁻¹ * n * a ∈ N) (h : a⁻¹ * c ∈ N) (m : ℕ) : (a ^ m)⁻¹ * c ^ m ∈ N := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : (a ^ (m + 1))⁻¹ * c ^ (m + 1) = (a⁻¹ * ((a ^ m)⁻¹ * c ^ m) * a) * (a⁻¹ * c) := by
      rw [pow_succ, pow_succ]; group
    rw [e]
    exact mul_mem (hN _ ih) h

end LiftAux

open LiftAux

theorem exists_lift_sqrt {X : Type} [Group X] [Finite X] (t : X) (ht : orderOf t = 2)
    (B : Subgroup X) (hB : IsPGroup 2 B) (hBt : B ≤ centralizer ({t} : Set X))
    (Ω : X) (hΩt : Ω ∈ centralizer ({t} : Set X))
    (hΩB : ∀ b ∈ B, Ω⁻¹ * (b * Ω * b⁻¹) ∈ GH74.GLS.pPrimeCoreOf 2 (centralizer ({t} : Set X)))
    (hΩ2 : (Ω * Ω)⁻¹ * t ∈ GH74.GLS.pPrimeCoreOf 2 (centralizer ({t} : Set X)))
    (hΩe : ∃ n : ℕ, Ω ^ 2 ^ n ∈ GH74.GLS.pPrimeCoreOf 2 (centralizer ({t} : Set X)))
    (hΩc : ∀ y ∈ GH74.GLS.pLayerOf 2 (centralizer ({t} : Set X)),
      y⁻¹ * (Ω⁻¹ * y * Ω) ∈ GH74.GLS.pPrimeCoreOf 2 (centralizer ({t} : Set X))) :
    ∃ ω : X, ω ∈ centralizer (B : Set X) ∧ ω ^ 2 = t ∧ (∃ n : ℕ, ω ^ 2 ^ n = 1) ∧
      ∀ y ∈ GH74.GLS.pLayerOf 2 (centralizer ({t} : Set X)),
        y⁻¹ * (ω⁻¹ * y * ω) ∈ GH74.GLS.pPrimeCoreOf 2 (centralizer ({t} : Set X)) := by
  have hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := centralizer ({t} : Set X) with hY
  set O := GH74.GLS.pPrimeCoreOf 2 Y with hO
  have hOY : O ≤ Y := GH74.GLS.TwoThin.pPrimeCoreOf_le Y
  have hOodd : Odd (Nat.card O) := GH74.GLS.TwoThin.card_pPrimeCoreOf_odd Y
  have hconj : ∀ k ∈ Y, ∀ o ∈ O, k * o * k⁻¹ ∈ O := fun k hk o ho =>
    GH74.GLS.TwoThin.pPrimeCoreOf_normalized Y hk ho
  have hLY : GH74.GLS.pLayerOf 2 Y ≤ Y := sSup_le fun _ hL => hL.1
  set α : ↥B →* MulAut X := MulAut.conj.comp B.subtype with hα
  have hα_apply : ∀ (b : ↥B) (x : X), α b x = (b : X) * x * (b : X)⁻¹ := fun b x => rfl
  have hcop : ¬ 2 ∣ Nat.card O := fun h => (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h)
  obtain ⟨c, hcO, hcfix⟩ := (Semidihedral.Principal.coprime_invariant_coset_fixed 2 hB α O hcop Ω).2
    (by
      intro b x hx
      rw [hα_apply]
      have e : Ω⁻¹ * ((b : X) * x * (b : X)⁻¹) =
          (Ω⁻¹ * ((b : X) * Ω * (b : X)⁻¹)) * ((b : X) * (Ω⁻¹ * x) * (b : X)⁻¹) := by group
      rw [e]
      exact mul_mem (hΩB b b.2) (hconj b (hBt b.2) _ hx))
  have hcY : c ∈ Y := by
    have : Ω * (Ω⁻¹ * c) ∈ Y := mul_mem hΩt (hOY hcO)
    simpa using this
  have hcB : ∀ b ∈ B, b * c = c * b := by
    intro b hb
    have h := hcfix ⟨b, hb⟩
    rw [hα_apply] at h
    calc b * c = (b * c * b⁻¹) * b := by group
      _ = c * b := by rw [h]
  have hΩN : ∀ n ∈ O, Ω⁻¹ * n * Ω ∈ O := fun n hn => by
    simpa using hconj Ω⁻¹ (inv_mem hΩt) n hn
  obtain ⟨N, hN⟩ := hΩe
  obtain ⟨a, r, hr, hcr⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hrc : Nat.Coprime r (2 ^ N) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hr)
  set m := r ^ Nat.totient (2 ^ N) with hm
  have hmmod : m ≡ 1 [MOD 2 ^ N] := Nat.ModEq.pow_totient hrc
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by rintro rfl; simp at hr))
  obtain ⟨j, hj⟩ : 2 ^ N ∣ m - 1 := (Nat.modEq_iff_dvd' hm1).mp hmmod.symm
  have hmj : m = 2 ^ N * j + 1 := by omega
  have hrm : r ∣ m := dvd_pow_self r (Nat.totient_pos.mpr (by positivity)).ne'
  set ω := c ^ m with hω
  have hω2a : ω ^ 2 ^ a = 1 := by
    rw [hω, ← pow_mul, orderOf_dvd_iff_pow_eq_one.symm, hcr]
    obtain ⟨s, hs⟩ := hrm
    exact ⟨s, by rw [hs]; ring⟩
  have hωY : ω ∈ Y := pow_mem hcY m
  have hΩm : Ω⁻¹ * Ω ^ m ∈ O := by
    rw [hmj, pow_add, pow_one, pow_mul]
    have : Ω⁻¹ * ((Ω ^ 2 ^ N) ^ j * Ω) = Ω⁻¹ * (Ω ^ 2 ^ N) ^ j * Ω := by group
    rw [this]
    exact hΩN _ (pow_mem hN j)
  have hΩω : Ω⁻¹ * ω ∈ O := by
    have e : Ω⁻¹ * ω = (Ω⁻¹ * Ω ^ m) * ((Ω ^ m)⁻¹ * c ^ m) := by rw [hω]; group
    rw [e]
    exact mul_mem hΩm (inv_pow_mul_pow_mem hΩN hcO m)
  have hωt : ω ^ 2 = t := by
    have hz : (ω ^ 2)⁻¹ * t ∈ O := by
      have h1 := inv_pow_mul_pow_mem hΩN hΩω 2
      have h2 : (Ω ^ 2)⁻¹ * t ∈ O := by rw [pow_two]; exact hΩ2
      have e : (ω ^ 2)⁻¹ * t = ((Ω ^ 2)⁻¹ * ω ^ 2)⁻¹ * ((Ω ^ 2)⁻¹ * t) := by group
      rw [e]
      exact mul_mem (inv_mem h1) h2
    have htω : Commute t ω := (mem_centralizer_singleton_iff.mp hωY).symm
    have hcomm : Commute (ω ^ 2)⁻¹ t := ((htω.pow_right 2).inv_right).symm
    have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
    have hp1 : (ω ^ 2) ^ 2 ^ (a + 1) = 1 := by
      rw [← pow_mul, pow_succ, show 2 * (2 ^ a * 2) = 2 ^ a * 4 by ring, pow_mul, hω2a, one_pow]
    have hp2 : t ^ 2 ^ (a + 1) = 1 := by
      rw [pow_succ, mul_comm, pow_mul, ht2, one_pow]
    have hzpow : ((ω ^ 2)⁻¹ * t) ^ 2 ^ (a + 1) = 1 := by
      rw [hcomm.mul_pow, inv_pow, hp1, hp2]; simp
    have hd1 : orderOf ((ω ^ 2)⁻¹ * t) ∣ 2 ^ (a + 1) := orderOf_dvd_of_pow_eq_one hzpow
    have hd2 : orderOf ((ω ^ 2)⁻¹ * t) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hz
    have hcop2 : Nat.Coprime (2 ^ (a + 1)) (Nat.card O) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hOodd)
    have h1 : orderOf ((ω ^ 2)⁻¹ * t) = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop2) hd2
    rw [orderOf_eq_one_iff, inv_mul_eq_one] at h1
    exact h1
  refine ⟨ω, ?_, hωt, ⟨a, hω2a⟩, ?_⟩
  · rw [mem_centralizer_iff]
    intro b hb
    exact ((Commute.pow_right (hcB b hb) m) : b * c ^ m = c ^ m * b)
  · intro y hy
    have hyY := hLY hy
    set o := Ω⁻¹ * ω with ho
    have hωo : ω = Ω * o := by rw [ho]; group
    have e : y⁻¹ * (ω⁻¹ * y * ω) = (y⁻¹ * o⁻¹ * y⁻¹⁻¹) * (y⁻¹ * (Ω⁻¹ * y * Ω)) * o := by
      rw [hωo]; group
    rw [e]
    exact mul_mem (mul_mem (hconj _ (inv_mem hyY) _ (inv_mem hΩω)) (hΩc y hy)) hΩω

theorem Eight2.CtxA0.false_of_fixed_sqrt_mod
    {X : Type} [Group X] [Finite X] (c : Eight2.CtxA0 X)
    (hA : ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)))
    (hq7 : c.s.p ^ c.s.f = 7) (Ω : X)
    (hΩt : Ω ∈ centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))
    (hΩB : ∀ b ∈ c.s.h.secB0 c.s.y, Ω⁻¹ * (b * Ω * b⁻¹) ∈
      GH74.GLS.pPrimeCoreOf 2 (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)))
    (hΩ2 : (Ω * Ω)⁻¹ * (c.s.h.a * c.b * c.Z.z) ∈
      GH74.GLS.pPrimeCoreOf 2 (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)))
    (hΩe : ∃ n : ℕ, Ω ^ 2 ^ n ∈
      GH74.GLS.pPrimeCoreOf 2 (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)))
    (hΩc : ∀ y ∈ GH74.GLS.pLayerOf 2 (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X)),
      y⁻¹ * (Ω⁻¹ * y * Ω) ∈
        GH74.GLS.pPrimeCoreOf 2 (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))) :
    False := by
  have hLC : Seven.Lay c.s.h c.s.y ≤ centralizer (c.s.h.secB0 c.s.y : Set X) :=
    Seven.Lay_le_centralizer_secB0 c.s.h c.s.y
  have hB₀Y : c.s.h.secB0 c.s.y ≤ centralizer ({c.s.h.a * c.b * c.Z.z} : Set X) := fun b hb =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hLC c.delta_mem_Lay) b hb)
  obtain ⟨ω, hωB, hω2, hωe, hωc⟩ := exists_lift_sqrt _ c.orderOf_abz _
    (c.s.h.isPGroup_secB0 c.s.y) hB₀Y Ω hΩt hΩB hΩ2 hΩe hΩc
  exact c.lemmaOmega hA hq7 ω hωB hω2 hωe hωc

end CFSG.ComponentClassification.GSThmB
