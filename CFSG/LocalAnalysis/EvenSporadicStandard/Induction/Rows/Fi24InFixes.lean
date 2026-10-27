module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Second

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

section Lift

variable {K K' : Type} [Group K] [Group K'] (π : K →* K')

theorem fi24in_eq_one_of_odd {N : Subgroup K} (hodd : Odd (Nat.card N)) {c : K} (hc : c ∈ N)
    (h2 : c * c = 1) : c = 1 := by
  have h1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  have h3 : orderOf c ∣ Nat.card N := by
    have : orderOf (⟨c, hc⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk] at this
  have h4 : orderOf c ∣ Nat.gcd 2 (Nat.card N) := Nat.dvd_gcd h1 h3
  rw [Nat.coprime_two_left.2 hodd] at h4
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)

theorem fi24in_mul_self_eq_one (hcent : ∀ x ∈ π.ker, x ∈ Subgroup.center K)
    (hodd : Odd (Nat.card π.ker)) {x y : K} (hx : x * x = 1) (hy : y * y = 1)
    (hcomm : π x * π y = π y * π x) : x * y * (x * y) = 1 := by
  have hx1 : π x * π x = 1 := by rw [← map_mul, hx, map_one]
  have hy1 : π y * π y = 1 := by rw [← map_mul, hy, map_one]
  set c := x * y * x * y with hc
  have hπc : c ∈ π.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_mul]
    calc π x * π y * π x * π y = π x * (π y * π x) * π y := by group
      _ = π x * (π x * π y) * π y := by rw [hcomm]
      _ = (π x * π x) * (π y * π y) := by group
      _ = 1 := by rw [hx1, hy1, one_mul]
  have hcc : c * c = 1 := by
    have hcen := Subgroup.mem_center_iff.1 (hcent c hπc)
    have hcinv : c⁻¹ = y * x * y * x := by
      rw [hc]
      have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
      have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
      simp only [mul_inv_rev, hxi, hyi, mul_assoc]
    have h1 : c = x * c⁻¹ * x := by
      rw [hcinv, hc]
      calc x * y * x * y = x * (y * x * y * x) * x := by
            calc x * y * x * y = x * y * x * y * 1 := by rw [mul_one]
              _ = x * y * x * y * (x * x) := by rw [hx]
              _ = x * (y * x * y * x) * x := by group
        _ = _ := rfl
    have h2 : x * c⁻¹ * x = c⁻¹ := by
      have hcen' := Subgroup.mem_center_iff.1 ((Subgroup.center K).inv_mem (hcent c hπc))
      rw [hcen' x, mul_assoc, hx, mul_one]
    exact mul_eq_one_iff_eq_inv.2 (h1.trans h2)
  have hc1 : c = 1 := fi24in_eq_one_of_odd hodd hπc hcc
  rw [← hc1, hc]
  exact (mul_assoc (x * y) x y).symm

theorem fi24in_aut_eq_one_of_central (hcent : ∀ x ∈ π.ker, x ∈ Subgroup.center K)
    (hperf : commutator K = ⊤) (α : MulAut K) (h : ∀ g : K, π (α g) = π g) : α = 1 := by
  have hδ : ∀ g : K, g⁻¹ * α g ∈ Subgroup.center K := fun g => hcent _ (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h g, inv_mul_cancel])
  let δ : K →* K :=
    { toFun := fun g => g⁻¹ * α g
      map_one' := by simp
      map_mul' := fun g k => by
        have hc := Subgroup.mem_center_iff.1 (hδ g) k⁻¹
        show (g * k)⁻¹ * α (g * k) = (g⁻¹ * α g) * (k⁻¹ * α k)
        calc (g * k)⁻¹ * α (g * k) = k⁻¹ * (g⁻¹ * α g) * α k := by
              rw [mul_inv_rev, map_mul]; group
          _ = (g⁻¹ * α g) * k⁻¹ * α k := by rw [← hc]
          _ = _ := by rw [mul_assoc] }
  have hker : commutator K ≤ δ.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact (commutatorElement_eq_one_iff_mul_comm.2
      ((Subgroup.mem_center_iff.1 (hδ a) (δ b)).symm))
  ext g
  have : δ g = 1 := by
    have := hker (by rw [hperf]; trivial : g ∈ commutator K)
    exact this
  have h1 : g⁻¹ * α g = 1 := this
  simpa using (mul_eq_one_iff_eq_inv.1 h1).symm

theorem fi24in_involutionFixesElem_of_central_odd [Finite K] (hπ : Function.Surjective π)
    (hcent : ∀ x ∈ π.ker, x ∈ Subgroup.center K) (hodd : Odd (Nat.card π.ker))
    (hperf : commutator K = ⊤) (hchar : ∀ (α : MulAut K), ∀ x ∈ π.ker, α x ∈ π.ker) {n : ℕ}
    (h : InvolutionFixesElem K' n) : InvolutionFixesElem K n := by
  intro α hα1 hα2
  have hαα : ∀ g : K, α (α g) = g := fun g => by
    have := congrArg (fun β : MulAut K => β g) hα2
    simpa using this
  have hle : π.ker ≤ (π.comp α.toMonoidHom).ker := fun x hx => hchar α x hx
  let ᾱh : K' →* K' := π.liftOfRightInverse (Function.surjInv hπ)
    (Function.rightInverse_surjInv hπ) ⟨π.comp α.toMonoidHom, hle⟩
  have hᾱ : ∀ g : K, ᾱh (π g) = π (α g) := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨π.comp α.toMonoidHom, hle⟩ g
  have hᾱᾱ : ∀ y : K', ᾱh (ᾱh y) = y := fun y => by
    obtain ⟨g, rfl⟩ := hπ y
    rw [hᾱ, hᾱ, hαα]
  let ᾱ : MulAut K' :=
    { toFun := ᾱh
      invFun := ᾱh
      left_inv := hᾱᾱ
      right_inv := hᾱᾱ
      map_mul' := map_mul ᾱh }
  have hne : ᾱ ≠ 1 := fun h1 => hα1 (fi24in_aut_eq_one_of_central π hcent hperf α fun g => by
    have := congrArg (fun β : MulAut K' => β (π g)) h1
    simp only [MulAut.one_apply] at this
    exact (hᾱ g).symm.trans this)
  have hsq : ᾱ * ᾱ = 1 := by
    ext y
    exact hᾱᾱ y
  obtain ⟨Ē, hfix, hsq1, hcomm, hcard⟩ := h ᾱ hne hsq
  have hinv : ∀ {x : K}, x * x = 1 → x⁻¹ = x := fun hx => inv_eq_of_mul_eq_one_right hx
  let E : Subgroup K :=
    { carrier := {x | π x ∈ Ē ∧ x * x = 1}
      mul_mem' := fun {x y} hx hy => by
        refine ⟨by rw [map_mul]; exact Ē.mul_mem hx.1 hy.1, ?_⟩
        exact fi24in_mul_self_eq_one π hcent hodd hx.2 hy.2 (hcomm _ hx.1 _ hy.1)
      one_mem' := ⟨by rw [map_one]; exact Ē.one_mem, mul_one 1⟩
      inv_mem' := fun {x} hx => by
        refine ⟨by rw [map_inv]; exact Ē.inv_mem hx.1, ?_⟩
        rw [hinv hx.2]
        exact hx.2 }
  have hinj : ∀ x ∈ E, ∀ y ∈ E, π x = π y → x = y := by
    intro x hx y hy hxy
    have hxy1 : x * y ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, ← hxy]
      rw [← map_mul, hx.2, map_one]
    have h1 : x * y = 1 := fi24in_eq_one_of_odd hodd hxy1 (E.mul_mem hx hy).2
    calc x = x * (y * y) := by rw [hy.2, mul_one]
      _ = (x * y) * y := by rw [mul_assoc]
      _ = y := by rw [h1, one_mul]
  have hsurj : ∀ e ∈ Ē, ∃ x ∈ E, π x = e := by
    intro e he
    obtain ⟨g, rfl⟩ := hπ e
    have hg2 : g * g ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul]
      exact hsq1 _ he
    have hpowN : (π g) ^ Nat.card π.ker = π g := by
      obtain ⟨m, hm⟩ := hodd
      rw [hm, pow_succ, pow_mul, pow_two, hsq1 _ he, one_pow, one_mul]
    refine ⟨g ^ Nat.card π.ker, ⟨by rw [map_pow, hpowN]; exact he, ?_⟩, by rw [map_pow, hpowN]⟩
    have h1 : (⟨g * g, hg2⟩ : π.ker) ^ Nat.card π.ker = 1 := pow_card_eq_one'
    have h2 : (g * g) ^ Nat.card π.ker = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    calc g ^ Nat.card π.ker * g ^ Nat.card π.ker = (g * g) ^ Nat.card π.ker := by
          rw [← pow_add, ← two_mul, pow_mul, pow_two]
      _ = 1 := h2
  have hfixE : ∀ x ∈ E, α x = x := by
    intro x hx
    have hπx : π (α x) = π x := by
      rw [← hᾱ x]
      exact hfix _ hx.1
    exact hinj (α x) ⟨by rw [hπx]; exact hx.1, by rw [← map_mul, hx.2, map_one]⟩ x hx hπx
  have hcardE : Nat.card Ē = Nat.card E := by
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun x : E => (⟨π x, x.2.1⟩ : Ē)) ⟨?_, ?_⟩)
    · intro x y hxy
      exact Subtype.ext (hinj x x.2 y y.2 (congrArg Subtype.val hxy))
    · rintro ⟨e, he⟩
      obtain ⟨x, hx, rfl⟩ := hsurj e he
      exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨E, hfixE, fun x hx => hx.2, fun x hx y hy => ?_, hcardE ▸ hcard⟩
  have h1 := (E.mul_mem hx hy).2
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hinv hx.2, hinv hy.2]

end Lift

section Reduction

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

end Reduction

end CFSG.EvenSporadicStandard.Induction
