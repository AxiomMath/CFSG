module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieCoreX
public import CFSG.GH74.Generic.S1.Exo.Q3SL2

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup
open scoped MatrixGroups

variable {X : Type} [Group X]
variable {L : Subgroup X} [L.Normal] {i : X} {R : Subgroup X}
  (hRodd : Odd (Nat.card R)) (hRi : ∀ r ∈ R, r * i = i * r)
  (hRconj : ∀ s ∈ L ⊓ centralizer ({i} : Set X), Odd (orderOf s) → ∀ r ∈ R, s * r * s⁻¹ ∈ R)
include hRodd hRi hRconj

theorem commute_of_sl23 {H : Subgroup X}
    (hHT : H ≤ oddClosure (L ⊓ centralizer ({i} : Set X)))
    (hHn : ∀ t ∈ oddClosure (L ⊓ centralizer ({i} : Set X)), ∀ h ∈ H, t * h * t⁻¹ ∈ H)
    {F₀ : Type} [Field F₀] [Finite F₀] (hF : Nat.card F₀ = 3) (e : SL(2, F₀) ≃* H)
    {r : X} (hr : r ∈ R) {q : X} (hq : q ∈ H) {a : ℕ} (hqa : q ^ (2 ^ a) = 1) :
    r * q = q * r := by
  set C := L ⊓ centralizer ({i} : Set X) with hC
  set T := oddClosure C with hT
  have hTC := oddClosure_le C
  have hRC : ∀ r ∈ R, ∀ c ∈ C, r * c * r⁻¹ ∈ C := by
    intro r hr c hc
    obtain ⟨hcL, hci⟩ := mem_inf.mp hc
    refine mem_inf.mpr ⟨(inferInstance : L.Normal).conj_mem c hcL r, ?_⟩
    rw [mem_centralizer_singleton_iff] at hci ⊢
    have hri := hRi r hr
    have hri' : r⁻¹ * i = i * r⁻¹ := by
      calc r⁻¹ * i = r⁻¹ * (i * r) * r⁻¹ := by group
        _ = r⁻¹ * (r * i) * r⁻¹ := by rw [hri]
        _ = i * r⁻¹ := by group
    calc r * c * r⁻¹ * i = r * c * (i * r⁻¹) := by rw [mul_assoc, hri']
      _ = r * (c * i) * r⁻¹ := by group
      _ = r * (i * c) * r⁻¹ := by rw [hci]
      _ = (r * i) * c * r⁻¹ := by group
      _ = i * (r * c * r⁻¹) := by rw [hri]; group
  have hRT : ∀ r ∈ R, ∀ t ∈ T, r * t * r⁻¹ ∈ T := by
    intro r hr t ht
    have hle : T ≤ T.comap (MulAut.conj r).toMonoidHom := by
      rw [hT, oddClosure, closure_le]
      rintro g ⟨hgC, hgo⟩
      refine Subgroup.subset_closure ⟨hRC r hr g hgC, ?_⟩
      change Odd (orderOf (r * g * r⁻¹))
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hgo
    have := hle ht
    simpa using this
  have hTR : ∀ t ∈ T, ∀ r ∈ R, t * r * t⁻¹ ∈ R := by
    have hle : T ≤ normalizer (R : Set X) := by
      rw [hT, oddClosure, closure_le]
      rintro s ⟨hsC, hso⟩
      rw [SetLike.mem_coe, mem_normalizer_iff]
      intro r'
      refine ⟨fun h => hRconj s hsC hso r' h, fun h => ?_⟩
      have := hRconj s⁻¹ (inv_mem hsC) (by rwa [orderOf_inv]) _ h
      simpa [mul_assoc] using this
    intro t ht r hr
    exact (mem_normalizer_iff.mp (hle ht) r).mp hr
  set N := R ⊓ T with hN
  have hNodd : Odd (Nat.card N) := Odd.of_dvd_nat hRodd (card_dvd_of_le inf_le_left)
  have hNconj : ∀ t ∈ T, ∀ m ∈ N, t * m * t⁻¹ ∈ N := by
    intro t ht m hm
    obtain ⟨hmR, hmT⟩ := mem_inf.mp hm
    exact mem_inf.mpr ⟨hTR t ht m hmR, mul_mem (mul_mem ht hmT) (inv_mem ht)⟩
  have hHN : ∀ h ∈ H, ∀ m ∈ N, h * m = m * h := by
    set M : Subgroup H := (N ⊓ H).subgroupOf H with hM
    have hMn : M.Normal := by
      constructor
      intro x hx g
      rw [hM, mem_subgroupOf] at hx ⊢
      obtain ⟨hxN, -⟩ := mem_inf.mp hx
      refine mem_inf.mpr ⟨?_, (g * x * g⁻¹).2⟩
      simp only [coe_mul, coe_inv]
      exact hNconj _ (hHT g.2) _ hxN
    have hModd : Odd (Nat.card M) := by
      have h1 : Nat.card M = Nat.card (N ⊓ H : Subgroup X) := by
        rw [hM]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
      rw [h1]
      exact Odd.of_dvd_nat hNodd (card_dvd_of_le inf_le_left)
    have hM1 := CFSG.GH74.Generic.S1.Exo.sl23_no_odd_normal hF e M hModd
    intro h hh m hm
    have hc : h * m * h⁻¹ * m⁻¹ ∈ N ⊓ H := by
      refine mem_inf.mpr ⟨mul_mem (hNconj h (hHT hh) m hm) (inv_mem hm), ?_⟩
      have := hHn m (mem_inf.mp hm).2 h⁻¹ (inv_mem hh)
      rw [show h * m * h⁻¹ * m⁻¹ = h * (m * h⁻¹ * m⁻¹) by group]
      exact mul_mem hh this
    have hc' : (⟨h * m * h⁻¹ * m⁻¹, (mem_inf.mp hc).2⟩ : H) ∈ M := by
      rw [hM, mem_subgroupOf]
      exact hc
    rw [hM1, mem_bot] at hc'
    have h1 : h * m * h⁻¹ * m⁻¹ = 1 := congrArg Subtype.val hc'
    calc h * m = h * m * h⁻¹ * m⁻¹ * m * h := by group
      _ = m * h := by rw [h1, one_mul]
  have hcN : ∀ x ∈ H, r * x * r⁻¹ * x⁻¹ ∈ N := by
    intro x hx
    refine mem_inf.mpr ⟨?_, mul_mem (hRT r hr x (hHT hx)) (inv_mem (hHT hx))⟩
    have := hTR x (hHT hx) r⁻¹ (inv_mem hr)
    rw [show r * x * r⁻¹ * x⁻¹ = r * (x * r⁻¹ * x⁻¹) by group]
    exact mul_mem hr this
  have hpow : ∀ j : ℕ, r * q ^ j * r⁻¹ * (q ^ j)⁻¹ = (r * q * r⁻¹ * q⁻¹) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hc := hHN q hq _ (hcN (q ^ j) (pow_mem hq j))
      calc r * q ^ (j + 1) * r⁻¹ * (q ^ (j + 1))⁻¹ =
          (r * q * r⁻¹ * q⁻¹) * (q * (r * q ^ j * r⁻¹ * (q ^ j)⁻¹)) * q⁻¹ := by
            rw [pow_succ']
            group
        _ = (r * q * r⁻¹ * q⁻¹) * ((r * q ^ j * r⁻¹ * (q ^ j)⁻¹) * q) * q⁻¹ := by rw [hc]
        _ = (r * q * r⁻¹ * q⁻¹) ^ (j + 1) := by rw [ih, pow_succ']; group
  have h1 : (r * q * r⁻¹ * q⁻¹) ^ (2 ^ a) = 1 := by
    rw [← hpow, hqa, mul_one, mul_inv_cancel, inv_one, mul_one]
  have hm := hcN q hq
  have h2 : (r * q * r⁻¹ * q⁻¹) ^ Nat.card N = 1 := by
    have := pow_card_eq_one' (G := N) (x := ⟨_, hm⟩)
    exact congrArg Subtype.val this
  have hcop : Nat.Coprime (Nat.card N) (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hNodd)
  have h3 : orderOf (r * q * r⁻¹ * q⁻¹) = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
  rw [orderOf_eq_one_iff] at h3
  calc r * q = r * q * r⁻¹ * q⁻¹ * q * r := by group
    _ = q * r := by rw [h3, one_mul]

end CFSG.ComponentClassification.Foote5.OddLieCore
