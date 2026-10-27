module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Pair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf3Lift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped MatrixGroups

theorem sl2Three_cent_sq : ∀ g : SL(2, ZMod 3),
    (∀ q : SL(2, ZMod 3), q ^ 4 = 1 → g * q = q * g) → g ^ 2 = 1 := by
  decide +kernel

theorem sl2Three_three_moves : ∀ g q : SL(2, ZMod 3), g ^ 3 = 1 → g ≠ 1 → q ^ 4 = 1 → q ^ 2 ≠ 1 →
    g * q * g⁻¹ ≠ q ∧ g * q * g⁻¹ ≠ q⁻¹ := by
  decide +kernel

theorem map_mk_eq_of_map_eq {H K : Type} [Group H] [Group K] (ψ : H →* K) (N : Subgroup H)
    [N.Normal] (hψ : ∀ x, ψ x = 1 ↔ x ∈ N) {A B : Subgroup H} (h : A.map ψ = B.map ψ) :
    A.map (QuotientGroup.mk' N) = B.map (QuotientGroup.mk' N) := by
  have key : ∀ {A B : Subgroup H}, A.map ψ = B.map ψ →
      A.map (QuotientGroup.mk' N) ≤ B.map (QuotientGroup.mk' N) := by
    intro A B h y hy
    obtain ⟨a, ha, rfl⟩ := hy
    have h1 : ψ a ∈ B.map ψ := h ▸ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hab⟩ := h1
    refine ⟨b, hb, ?_⟩
    have h2 : a⁻¹ * b ∈ N := (hψ _).mp (by rw [map_mul, map_inv, hab, inv_mul_cancel])
    exact (QuotientGroup.eq.mpr h2).symm
  exact le_antisymm (key h) (key h.symm)


section Sec

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {n : ℕ}

theorem lie_fusion_section (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hlt : Nat.card X < n) (hS : TwinDisc.Q8Section X Φ) (hno : TwinDisc.NoExit X Φ)
    {J₁ J₂ : Subgroup X} (h₁ : J₁ ∈ Φ) (h₂ : J₂ ∈ Φ) (hne : J₁ ≠ J₂) {w : X}
    (hw₁ : IsUniqueInvolution J₁ w) (hw₂ : IsUniqueInvolution J₂ w) :
    ∃ x : X, Odd (orderOf x) ∧ x ∈ Subgroup.normalizer (J₁ : Set X) ∧ (∀ b ∈ J₂, x * b = b * x) ∧
      (∃ j ∈ J₁, x * j ≠ j * x) ∧
      ∀ j ∈ J₁, j ^ 2 ≠ 1 → x * j * x⁻¹ ≠ j ∧ x * j * x⁻¹ ≠ j⁻¹ := by
  classical
  obtain ⟨h2all, hl, -⟩ := TwinDisc.lifts_of_noExit hP hlt hS hno
  obtain ⟨L₁', u₁, hL₁'⟩ := hl J₁ h₁
  obtain ⟨L₂', u₂, hL₂'⟩ := hl J₂ h₂
  have e₁ : w = u₁ := hw₁.eq hL₁'.inv
  have e₂ : w = u₂ := hw₂.eq hL₂'.inv
  subst e₁
  subst e₂
  obtain ⟨hP₁, hP₂, L₁, L₂, hL₁, hL₂, hJL₁, hJL₂, hLne, hcomm, -, -⟩ :=
    TwinExitPf10.exists_lifted_pair_Y hcit hS.hyp hS.two hS.q8 hlt hS.oddFree h₁ h₂ hne hw₁ hw₂
      ⟨_, hL₁'⟩ ⟨_, hL₂'⟩ (MulEquiv.refl X)
      (fun K hK => by
        rw [show (MulEquiv.refl X).toMonoidHom = MonoidHom.id X from rfl, Subgroup.map_id]
        exact hK)
      (fun _ j _ => rfl) (fun _ j _ => rfl)
  have hJ1S : IsSylow2In J₁ J₁ := ⟨le_rfl, hP₁, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨eQ⟩ := hS.q8 J₁ h₁ J₁ hJ1S
  have hJ4 : ∀ y ∈ J₁, y ^ 4 = 1 := by
    intro y hy
    have hq : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
    have h1 : (⟨y, hy⟩ : ↥J₁) ^ 4 = 1 := by
      have h2 := congrArg eQ.symm (hq (eQ ⟨y, hy⟩))
      rwa [map_pow, MulEquiv.symm_apply_apply, map_one] at h2
    simpa using congrArg (fun z : ↥J₁ => (z : X)) h1
  have hJcard : Nat.card ↥J₁ = 8 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨ψ, hψs, hψk⟩ := hL₁.exists_hom
  set N : Subgroup ↥L₁ := classicalInvolutionOddCore ↥L₁ with hNdef
  have hNodd : Odd (Nat.card N) := hL₁.odd_card_oddCore
  set A : Subgroup ↥L₁ := J₁.subgroupOf L₁ with hAdef
  have hAJ : ↥A ≃* ↥J₁ := Subgroup.subgroupOfEquivOfLe hJL₁
  have hA2 : IsPGroup 2 ↥A := hP₁.of_equiv hAJ.symm
  have hAcard : Nat.card ↥A = 8 := by rw [Nat.card_congr hAJ.toEquiv, hJcard]
  have hA4 : ∀ y ∈ A, y ^ 4 = 1 := by
    intro y hy
    have : ((y : ↥L₁) : X) ^ 4 = 1 := hJ4 _ (Subgroup.mem_subgroupOf.mp hy)
    exact Subtype.ext (by simpa using this)
  have hAN : A ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hA2 le_rfl
      (hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  have hψinj : ∀ y₁ ∈ A, ∀ y₂ ∈ A, ψ y₁ = ψ y₂ → y₁ = y₂ := by
    intro y₁ h₁ y₂ h₂ h
    have h1 : y₁⁻¹ * y₂ ∈ A ⊓ N :=
      ⟨A.mul_mem (A.inv_mem h₁) h₂, (hψk _).mp (by rw [map_mul, map_inv, h, inv_mul_cancel])⟩
    rw [hAN, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  have hψAle : A.map ψ ≤ sl2ThreeQ := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_sl2ThreeQ_iff, ← map_pow, hA4 y hy, map_one]
  have hψAcard : Nat.card ↥(A.map ψ) = 8 := by
    have : Nat.card ↥(A.map ψ) = Nat.card ↑(ψ '' (A : Set ↥L₁)) := by
      rw [← Subgroup.coe_map]
      rfl
    rw [this, Nat.card_image_of_injOn (fun a ha a' ha' h => hψinj a ha a' ha' h)]
    exact hAcard
  have hψA : A.map ψ = sl2ThreeQ :=
    Subgroup.eq_of_le_of_card_ge hψAle (by rw [hψAcard, natCard_sl2ThreeQ])
  obtain ⟨g₀, hg₀⟩ := sl2Three_exists_orderOf_three
  obtain ⟨y₀, hy₀⟩ := hψs g₀
  have hg₀3 : g₀ ^ 3 = 1 := by
    have := pow_orderOf_eq_one g₀
    rwa [hg₀] at this
  have hg₀1 : g₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg₀
    exact absurd hg₀ (by norm_num)
  set A₀ : Subgroup ↥L₁ := conjSub y₀ A with hA₀
  have hA₀2 : IsPGroup 2 ↥A₀ := isPGroup_conjSub y₀ hA2
  have hψA₀ : A₀.map ψ = A.map ψ := by
    rw [hψA]
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hz' : y₀⁻¹ * z * y₀ ∈ A := mem_conjSub_iff.mp hz
      have h1 : ψ (y₀⁻¹ * z * y₀) ∈ sl2ThreeQ := hψA ▸ ⟨_, hz', rfl⟩
      have h2 := sl2ThreeQ_normal.conj_mem _ h1 g₀
      have h3 : g₀ * ψ (y₀⁻¹ * z * y₀) * g₀⁻¹ = ψ z := by
        rw [map_mul, map_mul, map_inv, hy₀]; group
      rwa [h3] at h2
    · intro q hq
      have h1 := sl2ThreeQ_normal.conj_mem q hq g₀⁻¹
      obtain ⟨a, ha, hav⟩ : g₀⁻¹ * q * g₀⁻¹⁻¹ ∈ A.map ψ := by rw [hψA]; exact h1
      refine ⟨y₀ * a * y₀⁻¹, conj_mem_conjSub (n := y₀) ha, ?_⟩
      rw [map_mul, map_mul, map_inv, hy₀, hav]; group
  obtain ⟨n₁, hn₁, hconj⟩ := exists_odd_conj N hNodd hA₀2 hA2
    (map_mk_eq_of_map_eq ψ N hψk hψA₀)
  set x₁ : ↥L₁ := n₁ * y₀ with hx₁
  have hx₁A : conjSub x₁ A = A := by rw [hx₁, conjSub_mul, ← hA₀, hconj]
  have hψx₁ : ψ x₁ = g₀ := by
    rw [hx₁, map_mul, (hψk n₁).mpr hn₁, one_mul, hy₀]
  have hx₁odd : Odd (orderOf x₁) := by
    have h1 : x₁ ^ 3 ∈ N := (hψk _).mp (by rw [map_pow, hψx₁, hg₀3])
    have h2 : Odd (orderOf (x₁ ^ 3)) := hNodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N h1)
    have h3 : x₁ ^ (3 * orderOf (x₁ ^ 3)) = 1 := by rw [pow_mul, pow_orderOf_eq_one]
    exact (Odd.mul (by decide) h2).of_dvd_nat (orderOf_dvd_of_pow_eq_one h3)
  set x : X := (x₁ : X) with hxdef
  have hxJ : ∀ y ∈ J₁, x * y * x⁻¹ ∈ J₁ := by
    intro y hy
    have h1 : (⟨y, hJL₁ hy⟩ : ↥L₁) ∈ A := Subgroup.mem_subgroupOf.mpr hy
    have h2 : x₁ * ⟨y, hJL₁ hy⟩ * x₁⁻¹ ∈ A := by
      have := conj_mem_conjSub (n := x₁) h1
      rwa [hx₁A] at this
    exact Subgroup.mem_subgroupOf.mp h2
  have hxJ' : ∀ y ∈ J₁, x⁻¹ * y * x ∈ J₁ := by
    intro y hy
    have h1 : (⟨y, hJL₁ hy⟩ : ↥L₁) ∈ A := Subgroup.mem_subgroupOf.mpr hy
    have h2 : x₁⁻¹ * ⟨y, hJL₁ hy⟩ * x₁ ∈ A := by
      have h3 : ⟨y, hJL₁ hy⟩ ∈ conjSub x₁ A := by rw [hx₁A]; exact h1
      exact mem_conjSub_iff.mp h3
    exact Subgroup.mem_subgroupOf.mp h2
  refine ⟨x, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxdef, Subgroup.orderOf_coe]
    exact hx₁odd
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hxJ h hh
    · intro hh
      have := hxJ' _ hh
      rwa [show x⁻¹ * (x * h * x⁻¹) * x = h by group] at this
  · intro b hb
    exact hcomm x x₁.2 b (hJL₂ hb)
  · by_contra hcon
    push Not at hcon
    have hcent : ∀ q : SL(2, ZMod 3), q ^ 4 = 1 → g₀ * q = q * g₀ := by
      intro q hq
      have hqA : q ∈ A.map ψ := by rw [hψA]; exact mem_sl2ThreeQ_iff.mpr hq
      obtain ⟨a, ha, rfl⟩ := hqA
      have h1 : x * (a : X) = (a : X) * x := hcon _ (Subgroup.mem_subgroupOf.mp ha)
      have h2 : x₁ * a = a * x₁ := Subtype.ext h1
      rw [← hψx₁, ← map_mul, ← map_mul, h2]
    have hsq := sl2Three_cent_sq g₀ hcent
    apply hg₀1
    calc g₀ = g₀ ^ 3 * (g₀ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hg₀3, hsq]; simp
  · intro j hj hj2
    have hjA : (⟨j, hJL₁ hj⟩ : ↥L₁) ∈ A := Subgroup.mem_subgroupOf.mpr hj
    set q : SL(2, ZMod 3) := ψ ⟨j, hJL₁ hj⟩ with hq
    have hq4 : q ^ 4 = 1 := by rw [hq, ← map_pow, hA4 _ hjA, map_one]
    have hq2 : q ^ 2 ≠ 1 := by
      intro h
      apply hj2
      have h1 : ψ (⟨j, hJL₁ hj⟩ ^ 2) = ψ 1 := by rw [map_pow, ← hq, h, map_one]
      have h2 := hψinj _ (A.pow_mem hjA 2) _ A.one_mem h1
      simpa using congrArg (fun z : ↥L₁ => (z : X)) h2
    have hmv := sl2Three_three_moves g₀ q hg₀3 hg₀1 hq4 hq2
    have hψconj : ψ (x₁ * ⟨j, hJL₁ hj⟩ * x₁⁻¹) = g₀ * q * g₀⁻¹ := by
      rw [map_mul, map_mul, map_inv, hψx₁]
    constructor
    · intro h
      apply hmv.1
      rw [← hψconj]
      have h1 : x₁ * ⟨j, hJL₁ hj⟩ * x₁⁻¹ = ⟨j, hJL₁ hj⟩ := Subtype.ext h
      rw [h1]
    · intro h
      apply hmv.2
      rw [← hψconj]
      have h1 : x₁ * ⟨j, hJL₁ hj⟩ * x₁⁻¹ = (⟨j, hJL₁ hj⟩ : ↥L₁)⁻¹ := Subtype.ext h
      rw [h1, map_inv]

end Sec

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus
