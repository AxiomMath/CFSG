module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Subgroup
open scoped commutatorElement

section Aut

variable {Q : Type*} [Group Q]

theorem eq_one_of_fix_centralizer {p : ℕ} [Fact p.Prime] [Finite Q] (hQ : IsPGroup p Q)
    (w : MulAut Q) (hw : Nat.Coprime (orderOf w) p) (v : Q) (hv : w v = v)
    (hC : ∀ u : Q, u * v = v * u → w u = u) : w = 1 := by
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have key : ∀ i : ℕ, ∀ u : Q, ⁅u, v⁆ ∈ Subgroup.upperCentralSeries Q i → w u = u := by
    intro i
    induction i with
    | zero =>
      intro u hu
      rw [Subgroup.upperCentralSeries_zero, Subgroup.mem_bot,
        commutatorElement_eq_one_iff_mul_comm] at hu
      exact hC u hu
    | succ i ih =>
      intro u hu
      have hZ : ∀ z ∈ Subgroup.upperCentralSeries Q (i + 1), w z = z := fun z hz =>
        ih z (Subgroup.mem_upperCentralSeries_succ_iff.1 hz v)
      have h1 : w ⁅u, v⁆ = ⁅u, v⁆ := hZ _ hu
      have h2 : ⁅w u, v⁆ = ⁅u, v⁆ := by
        have : w ⁅u, v⁆ = ⁅w u, w v⁆ := by simp [commutatorElement_def]
        rw [hv] at this
        rw [← this, h1]
      set c : Q := u⁻¹ * w u with hc
      have hwu : w u = u * c := by rw [hc]; group
      have hcv : c * v = v * c := by
        have h3 : (u * c) * v * (u * c)⁻¹ * v⁻¹ = u * v * u⁻¹ * v⁻¹ := by
          have := h2
          rw [hwu] at this
          simp only [commutatorElement_def] at this
          exact this
        have h4 : u * (c * v * c⁻¹) * u⁻¹ = u * v * u⁻¹ := by
          have e1 : (u * c) * v * (u * c)⁻¹ * v⁻¹ = (u * (c * v * c⁻¹) * u⁻¹) * v⁻¹ := by group
          rw [e1] at h3
          exact mul_right_cancel h3
        have h5 : c * v * c⁻¹ = v := mul_left_cancel (mul_right_cancel h4)
        exact mul_inv_eq_iff_eq_mul.1 h5
      have hwc : w c = c := hC c hcv
      have hpow : ∀ k : ℕ, (w ^ k) u = u * c ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ihk =>
          have e : (w ^ (k + 1)) u = w ((w ^ k) u) := by rw [pow_succ']; rfl
          rw [e, ihk, map_mul, map_pow, hwu, hwc, pow_succ']
          group
      have hn := hpow (orderOf w)
      rw [pow_orderOf_eq_one, MulAut.one_apply] at hn
      have hcn : c ^ orderOf w = 1 := by
        have := congrArg (fun t => u⁻¹ * t) hn
        simpa using this.symm
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hQ) c
      have hdvd : orderOf c ∣ orderOf w := orderOf_dvd_of_pow_eq_one hcn
      have hcop : Nat.Coprime (p ^ k) (orderOf w) :=
        Nat.Coprime.pow_left k hw.symm
      have hone : orderOf c = 1 := by
        rw [hk] at hdvd ⊢
        exact hcop.eq_one_of_dvd hdvd
      have hc1 : c = 1 := orderOf_eq_one_iff.1 hone
      rw [hwu, hc1, mul_one]
  ext u
  have := key (Group.nilpotencyClass Q) u (by
    rw [Subgroup.upperCentralSeries_nilpotencyClass]; exact Subgroup.mem_top _)
  simpa using this

end Aut

section Group

variable {G : Type*} [Group G]

theorem oPrime_centralizer_eq_bot [Finite G] {p : ℕ} [Fact p.Prime] {Q : Subgroup G}
    (hQp : IsPGroup p Q) (hQn : Q.Normal) (hcent : Subgroup.centralizer (Q : Set G) ≤ Q) {v : G}
    (hv : v ∈ Q) {W : Subgroup G} (hWv : ∀ w ∈ W, w * v = v * w)
    (hWn : ∀ c : G, c * v = v * c → ∀ w ∈ W, c * w * c⁻¹ ∈ W)
    (hWp : Nat.Coprime (Nat.card W) p) : W = ⊥ := by
  have hinter : ∀ x ∈ W, x ∈ Q → x = 1 := by
    intro x hxW hxQ
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hQp) ⟨x, hxQ⟩
    have h1 : orderOf x ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W hxW
    have h2 : orderOf x = p ^ k := by
      have := hk
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (p ^ k) (Nat.card W) := Nat.Coprime.pow_left k hWp.symm
    have : orderOf x = 1 := by
      rw [h2] at h1 ⊢
      exact hcop.eq_one_of_dvd h1
    exact orderOf_eq_one_iff.1 this
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  have := hQn
  set α : MulAut Q := MulAut.conjNormal (H := Q) w with hα
  have hord : Nat.Coprime (orderOf α) p := by
    have h1 : orderOf α ∣ orderOf w := orderOf_map_dvd (MulAut.conjNormal (H := Q)) w
    have h2 : orderOf w ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W hw
    exact Nat.Coprime.coprime_dvd_left (h1.trans h2) hWp
  have hαv : α ⟨v, hv⟩ = ⟨v, hv⟩ := by
    apply Subtype.ext
    rw [hα, MulAut.conjNormal_apply]
    have := hWv w hw
    calc w * v * w⁻¹ = v * w * w⁻¹ := by rw [this]
      _ = v := by group
  have hαC : ∀ u : Q, u * ⟨v, hv⟩ = ⟨v, hv⟩ * u → α u = u := by
    intro u hu
    have huv : (u : G) * v = v * u := congrArg Subtype.val hu
    apply Subtype.ext
    rw [hα, MulAut.conjNormal_apply]
    have h1 : (u : G) * w⁻¹ * (u : G)⁻¹ ∈ W := hWn u huv w⁻¹ (W.inv_mem hw)
    have hcommW : w * ((u : G) * w⁻¹ * (u : G)⁻¹) ∈ W := W.mul_mem hw h1
    have hcommQ : w * ((u : G) * w⁻¹ * (u : G)⁻¹) ∈ Q := by
      have h2 : w * (u : G) * w⁻¹ ∈ Q := hQn.conj_mem _ u.2 w
      have : w * ((u : G) * w⁻¹ * (u : G)⁻¹) = (w * (u : G) * w⁻¹) * (u : G)⁻¹ := by group
      rw [this]
      exact Q.mul_mem h2 (Q.inv_mem u.2)
    have h3 := hinter _ hcommW hcommQ
    have : w * (u : G) * w⁻¹ = u := by
      have h4 : w * (u : G) * w⁻¹ * (u : G)⁻¹ = 1 := by
        calc w * (u : G) * w⁻¹ * (u : G)⁻¹ = w * ((u : G) * w⁻¹ * (u : G)⁻¹) := by group
          _ = 1 := h3
      exact mul_inv_eq_one.1 h4
    exact this
  have hα1 : α = 1 :=
    eq_one_of_fix_centralizer hQp α hord ⟨v, hv⟩ hαv hαC
  have hwQ : w ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := congrArg (fun φ : MulAut Q => (φ ⟨u, hu⟩ : G)) hα1
    simp only [hα, MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc u * w = (w * u * w⁻¹) * w := by rw [this]
      _ = w * u := by group
  exact hinter w hw (hcent hwQ)

end Group

end CFSG.GH74.GLS.Stage2.OddAut
