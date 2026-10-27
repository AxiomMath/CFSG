module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13CI6
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13CI7
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13CI1

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem card_inf_ge {G : Type*} [Group G] [Finite G] {Y Q R₀ : Subgroup G} (hY : Y ≤ R₀)
    (hQ : Q ≤ R₀) (hYc : Nat.card Y = 1024) (hQc : Nat.card Q = 1024)
    (hR : Nat.card R₀ ≤ 4096) : 256 ≤ Nat.card ↥(Y ⊓ Q) := by
  have hYQ : Y ⊓ Q ≤ R₀ := inf_le_left.trans hY
  have e1 := Subgroup.relIndex_mul_card (H := Y) (K := R₀)
  have e2 := Subgroup.relIndex_mul_card (H := Q) (K := R₀)
  have e3 := Subgroup.relIndex_mul_card (H := Y ⊓ Q) (K := R₀)
  rw [inf_eq_left.2 hY, hYc] at e1
  rw [inf_eq_left.2 hQ, hQc] at e2
  rw [inf_eq_left.2 hYQ] at e3
  have e4 : (Y ⊓ Q).relIndex R₀ ≤ Y.relIndex R₀ * Q.relIndex R₀ := Subgroup.relIndex_inf_le
  have hR0 : 0 < Nat.card R₀ := Nat.card_pos
  set i := Y.relIndex R₀ with hi
  set j := Q.relIndex R₀ with hj
  set k := (Y ⊓ Q).relIndex R₀ with hk
  have hij : i = j := by omega
  have hi4 : i ≤ 4 := by omega
  have hipos : 0 < i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h] at e1; omega
    · exact h
  have h5 : 1024 * i ≤ i * i * Nat.card ↥(Y ⊓ Q) := by
    calc 1024 * i = Nat.card R₀ := by omega
      _ = k * Nat.card ↥(Y ⊓ Q) := e3.symm
      _ ≤ (i * j) * Nat.card ↥(Y ⊓ Q) := Nat.mul_le_mul_right _ e4
      _ = i * i * Nat.card ↥(Y ⊓ Q) := by rw [← hij]
  have h6 : 1024 ≤ i * Nat.card ↥(Y ⊓ Q) := by
    have : i * 1024 ≤ i * (i * Nat.card ↥(Y ⊓ Q)) := by
      calc i * 1024 = 1024 * i := by ring
        _ ≤ i * i * Nat.card ↥(Y ⊓ Q) := h5
        _ = i * (i * Nat.card ↥(Y ⊓ Q)) := by ring
    exact Nat.le_of_mul_le_mul_left this hipos
  nlinarith

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  {c : I13Ctx L z t T₀ E Q x β B S α} {π : MulAut ↥E →* Equiv.Perm (Fin 5)}
  {Rs : Subgroup G}

namespace IsRs

variable (hR : c.IsRs Rs) (hπ : EPi E π)
  (hI : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔
    π a ∈ alternatingGroup (Fin 5) ∧ π b = π a)

include hR hπ hI

theorem card_R0_le : Nat.card ↥(Rs ⊓ c.N1) ≤ 4096 := by
  have h1 := c.card_le_four_Rhat (inf_le_right : Rs ⊓ c.N1 ≤ c.N1) hR.R_inf_KR_le
  have h2 := c.card_pgroup_range_le hπ hI (c.Rhat_pgroup hR.R_pgroup) (c.Rhat_le_range _)
  omega

theorem normalizes_Qs
    (hfix : ∀ φ : MulAut ↥E, BInv E π φ → Nat.card {e : ↥E // φ e = e} = 4)
    {n : G} (hn : ∀ r : G, r ∈ Rs ↔ n * r * n⁻¹ ∈ Rs) (q : G) :
    q ∈ c.Qs ↔ n * q * n⁻¹ ∈ c.Qs := by
  set Y : Subgroup G := c.Qs.map (MulAut.conj n).toMonoidHom with hY
  have hmemY : ∀ y : G, y ∈ Y ↔ n⁻¹ * y * n ∈ c.Qs := by
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      have : n⁻¹ * (MulAut.conj n).toMonoidHom u * n = u := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
      rw [this]; exact hu
    · intro h
      refine ⟨n⁻¹ * y * n, h, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  have hYcard : Nat.card Y = 1024 := by
    rw [hY, Subgroup.card_map_of_injective (MulAut.conj n).injective, c.card_Qs]
  have hZ := hR.map_Zs_eq hn
  have hmemZ : ∀ a ∈ c.Zs, n⁻¹ * a * n ∈ c.Zs := by
    intro a ha
    have h1 : a ∈ c.Zs.map (MulAut.conj n).toMonoidHom := by rw [hZ]; exact ha
    obtain ⟨u, hu, rfl⟩ := h1
    have : n⁻¹ * (MulAut.conj n).toMonoidHom u * n = u := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [this]; exact hu
  have hmemZ' : ∀ w : G, n⁻¹ * w * n ∈ c.Zs → w ∈ c.Zs := by
    intro w hw
    have h1 : w ∈ c.Zs.map (MulAut.conj n).toMonoidHom := by
      refine ⟨n⁻¹ * w * n, hw, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [hZ] at h1; exact h1
  have hYR : Y ≤ Rs := by
    rintro _ ⟨u, hu, rfl⟩
    exact (hn u).1 (hR.Qs_le hu)
  have hYcomm : ∀ y ∈ Y, ∀ a ∈ c.Zs, y * a = a * y := by
    intro y hy a ha
    have hq' := (hmemY y).1 hy
    have ha' := hmemZ a ha
    have h1 := c.Zs_comm_Qs ha' hq'
    calc y * a = n * ((n⁻¹ * y * n) * (n⁻¹ * a * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * a * n) * (n⁻¹ * y * n)) * n⁻¹ := by rw [← h1]
      _ = a * y := by group
  have hYN : Y ≤ c.N1 := fun y hy =>
    c.mem_N1.2 ⟨hR.le_Nc (hYR hy), by
      have := hYcomm y hy α c.alpha_mem_Zs
      calc y * α * y⁻¹ = (α * y) * y⁻¹ := by rw [this]
        _ = α := by group⟩
  have hYcomm2 : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' * y⁻¹ * y'⁻¹ ∈ c.Zs := by
    intro y hy y' hy'
    apply hmemZ'
    have h1 := c.comm_Qs_mem_Zs ((hmemY y).1 hy) ((hmemY y').1 hy')
    have e : n⁻¹ * (y * y' * y⁻¹ * y'⁻¹) * n =
        (n⁻¹ * y * n) * (n⁻¹ * y' * n) * (n⁻¹ * y * n)⁻¹ * (n⁻¹ * y' * n)⁻¹ := by group
    rw [e]; exact h1
  have hQR0 : c.Qs ≤ Rs ⊓ c.N1 := le_inf hR.Qs_le c.Qs_le_N1
  have hYR0 : Y ≤ Rs ⊓ c.N1 := le_inf hYR hYN
  have hYQ : Y ≤ c.Qs := by
    intro y hyY
    by_contra hyQ
    have hyR : y ∈ Rs ⊓ c.N1 := hYR0 hyY
    have hbig := card_inf_ge hYR0 hQR0 hYcard c.card_Qs (hR.card_R0_le hπ hI)
    have hsub : Y ⊓ c.Qs ≤ c.Cprime c.Qs_le_N1 y := fun u hu =>
      ⟨hu.2, hYcomm2 u hu.1 y hyY⟩
    have h64 := hR.card_Cprime_Qs_le hπ hI hfix hyR hyQ
    have := Subgroup.card_le_of_le hsub
    omega
  have hYeq : Y = c.Qs := Subgroup.eq_of_le_of_card_ge hYQ (by rw [hYcard, c.card_Qs])
  constructor
  · intro hq
    have h1 : n * q * n⁻¹ ∈ Y := (hmemY _).2 (by
      have : n⁻¹ * (n * q * n⁻¹) * n = q := by group
      rw [this]; exact hq)
    rwa [hYeq] at h1
  · intro h
    have h1 : n * q * n⁻¹ ∈ Y := by rw [hYeq]; exact h
    have h2 := (hmemY _).1 h1
    have : n⁻¹ * (n * q * n⁻¹) * n = q := by group
    rwa [this] at h2

end IsRs

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
