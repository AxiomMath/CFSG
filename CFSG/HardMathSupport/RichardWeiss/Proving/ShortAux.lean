module

public import CFSG.HardMathSupport.RichardWeiss.Proving.OddLift
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Shape
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0 Equiv Equiv.Perm
open scoped commutatorElement

section E0Comm

variable {N : ℕ} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)} {Δ₀ : Finset (Fin N)}

theorem e0_P_comm (h : E0Shape P ω Δ₀) {p q : Perm (Fin N)} (hp : p ∈ P) (hq : q ∈ P) :
    p * q = q * p := by
  have h1 : p * q * (p * q) = 1 := h.Psq _ (P.mul_mem hp hq)
  have hp' : p⁻¹ = p := (eq_inv_of_mul_eq_one_left (h.Psq p hp)).symm
  have hq' : q⁻¹ = q := (eq_inv_of_mul_eq_one_left (h.Psq q hq)).symm
  have h2 : p * q = (p * q)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [mul_inv_rev, hp', hq'] at h2
  exact h2

theorem e0_eprop_fix (h : E0Shape P ω Δ₀) {σ : Perm (Fin N)} (hσ : E0Shape.Eprop P ω Δ₀ σ)
    {z : Fin N} (hz : z ∉ Δ₀) (hσz : σ z = z) : σ (ω z) = ω z := by
  have hωz : ω z ∉ Δ₀ := h.ω_not_mem hz
  rcases hσ.2 (ω z) hωz with h1 | h1
  · exact h1
  · rw [h.ωω] at h1
    have : ω z = z := σ.injective (h1.trans hσz.symm)
    exact absurd this (h.ωfree z hz)

theorem e0_eprop_swap (h : E0Shape P ω Δ₀) {σ : Perm (Fin N)} (hσ : E0Shape.Eprop P ω Δ₀ σ)
    {z : Fin N} (hz : z ∉ Δ₀) (hσz : σ z = ω z) : σ (ω z) = z := by
  have hωz : ω z ∉ Δ₀ := h.ω_not_mem hz
  rcases hσ.2 (ω z) hωz with h1 | h1
  · exact absurd (σ.injective (h1.trans hσz.symm)) (h.ωfree z hz)
  · rwa [h.ωω] at h1

theorem e0_eprop_comm (h : E0Shape P ω Δ₀) {σ τ : Perm (Fin N)}
    (hσ : E0Shape.Eprop P ω Δ₀ σ) (hτ : E0Shape.Eprop P ω Δ₀ τ) : σ * τ = τ * σ := by
  refine Equiv.ext fun z => ?_
  simp only [Perm.mul_apply]
  by_cases hz : z ∈ Δ₀
  · obtain ⟨p, hp, hpx⟩ := hσ.1
    obtain ⟨q, hq, hqx⟩ := hτ.1
    rw [hqx z hz, hpx z hz, hpx _ (h.P_mem hq hz), hqx _ (h.P_mem hp hz)]
    have := e0_P_comm h hp hq
    exact congrArg (fun f : Perm (Fin N) => f z) this
  · rcases hτ.2 z hz with h1 | h1 <;> rcases hσ.2 z hz with h2 | h2
    · rw [h1, h2, h1]
    · rw [h1, h2, e0_eprop_fix h hτ hz h1]
    · rw [h1, h2, h1, e0_eprop_fix h hσ hz h2]
    · rw [h1, h2, e0_eprop_swap h hτ hz h1, e0_eprop_swap h hσ hz h2]

end E0Comm

theorem exists_odd_lift {G H : Type*} [Group G] [Finite G] [Group H] (θ : G →* H) {g : G} {σ : H}
    (hg : θ g = σ) (h3 : orderOf σ = 3) :
    ∃ n : ℕ, Odd (orderOf (g ^ n)) ∧ θ (g ^ n) = σ := by
  obtain ⟨k, hk, h⟩ := exists_odd_pow_two_pow_map_eq θ (g := g) (by rw [hg]; exact h3)
  rw [hg] at h
  rcases h with h | h
  · exact ⟨2 ^ k, hk, by rw [h]⟩
  · refine ⟨2 ^ k * 2, ?_, ?_⟩
    · rw [pow_mul]
      exact Odd.of_dvd_nat hk (orderOf_pow_dvd 2)
    · rw [pow_mul, map_pow, h, inv_pow, sq_eq_inv_of_orderOf_eq_three h3, inv_inv]

theorem conj_eq_of_odd {G : Type*} [Group G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) {g c : G}
    (hQg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hc : c ∈ Q) (hodd : Odd (orderOf g))
    {d : G} (hd : d = (g * c * g⁻¹)⁻¹ * c) (hgd : g * d = d * g) : g * c * g⁻¹ = c := by
  have hdQ : d ∈ Q := hd ▸ Q.mul_mem (Q.inv_mem (hQg c hc)) hc
  have hcomm : Commute g d := hgd
  have hac : g * c * g⁻¹ = c * d⁻¹ := by
    rw [hd]; group
  have key : ∀ k : ℕ, g ^ k * c * (g ^ k)⁻¹ = c * (d ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hgdk : g * (d ^ k)⁻¹ * g⁻¹ = (d ^ k)⁻¹ := by
        rw [mul_inv_eq_iff_eq_mul]
        exact ((hcomm.pow_right k).inv_right).eq
      have e : g ^ (k + 1) * c * (g ^ (k + 1))⁻¹ = g * (g ^ k * c * (g ^ k)⁻¹) * g⁻¹ := by
        rw [pow_succ']; group
      rw [e, ih]
      calc g * (c * (d ^ k)⁻¹) * g⁻¹ = (g * c * g⁻¹) * (g * (d ^ k)⁻¹ * g⁻¹) := by group
        _ = c * d⁻¹ * (d ^ k)⁻¹ := by rw [hac, hgdk]
        _ = c * (d ^ (k + 1))⁻¹ := by
          rw [pow_succ, mul_inv_rev]
          group
  have hk := key (orderOf g)
  rw [pow_orderOf_eq_one] at hk
  have hdk : d ^ orderOf g = 1 := by
    have : c = c * (d ^ orderOf g)⁻¹ := by simpa using hk
    simpa using this.symm
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.1 hQ) ⟨d, hdQ⟩
  have he' : orderOf d = 2 ^ e := (Subgroup.orderOf_coe (⟨d, hdQ⟩ : Q)).trans he
  have hdvd : 2 ^ e ∣ orderOf g := he' ▸ orderOf_dvd_of_pow_eq_one hdk
  have he0 : e = 0 := by
    by_contra hne
    have : 2 ∣ orderOf g := (dvd_pow_self 2 hne).trans hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 this)
  rw [he0, pow_zero, orderOf_eq_one_iff] at he'
  rw [hac, he']
  simp

variable {G : Type*} [Group G]

theorem commutator_characteristic {Y S : Subgroup G} (hYS : Y ≤ S)
    (hY : (Y.subgroupOf S).Characteristic) : ((⁅Y, S⁆).subgroupOf S).Characteristic := by
  have hc : (⁅Y.subgroupOf S, (⊤ : Subgroup S)⁆).Characteristic := inferInstance
  have hmap : (⁅Y.subgroupOf S, (⊤ : Subgroup S)⁆).map S.subtype = ⁅Y, S⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hYS,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have : (⁅Y, S⁆).subgroupOf S = ⁅Y.subgroupOf S, (⊤ : Subgroup S)⁆ := by
    rw [← hmap]
    exact Subgroup.comap_map_eq_self_of_injective S.subtype_injective _
  rw [this]
  exact hc

theorem centralizer_characteristic {Y S : Subgroup G} (hYS : Y ≤ S)
    (hY : (Y.subgroupOf S).Characteristic) :
    ((S ⊓ Subgroup.centralizer (Y : Set G)).subgroupOf S).Characteristic := by
  have hc := Subgroup.characteristic_centralizer (H := Y.subgroupOf S)
  have e : (S ⊓ Subgroup.centralizer (Y : Set G)).subgroupOf S =
      Subgroup.centralizer ((Y.subgroupOf S : Subgroup S) : Set S) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      SetLike.mem_coe]
    constructor
    · rintro ⟨-, h⟩ y hy
      apply Subtype.ext
      exact h _ hy
    · intro h
      refine ⟨x.2, fun y hy => ?_⟩
      have := h ⟨y, hYS hy⟩ hy
      exact congrArg Subtype.val this
  rw [e]
  exact hc

end CFSG.HardMathSupport.RichardWeiss.Proving
