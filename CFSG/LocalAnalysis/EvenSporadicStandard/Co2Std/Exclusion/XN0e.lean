module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XModule
public import Mathlib.GroupTheory.FixedPointFree

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup

variable {V : Type*} [Group V] {X : Type*} [Group X] {ρ : X →* MulAut V} {Q : Subgroup X}
  {V₁ V₂ : Subgroup V} {z : X} {Q₁ : Subgroup (MulAut ↥V₁)} {t₁ : ↥V₁}

theorem XHyp.eq_bot_or_eq_top (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) (hX : zpowers z ⊔ Q ≠ ⊤)
    {U : Subgroup V} (hU : ∀ x : X, ∀ u ∈ U, ρ x u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  rcases h.invariant_cases (fun g _ u hu => hU g u hu) with hbot | hV₁ | hV₂ | hCV | htop
  · exact Or.inl hbot
  · exfalso
    subst U
    have hV₁bot : V₁ = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro v hv
      have hzV₁ : ρ z v ∈ V₁ := hU z v hv
      have hzV₂ : ρ z v ∈ V₂ := (h.swap v).mp hv
      have hz1 : ρ z v = 1 := by
        have hmem : ρ z v ∈ V₁ ⊓ V₂ := ⟨hzV₁, hzV₂⟩
        rwa [h.inf_eq_bot] at hmem
      exact (ρ z).injective (by rw [hz1, map_one])
    have hcard := h.card₁
    rw [hV₁bot, Subgroup.card_bot] at hcard
    norm_num at hcard
  · exfalso
    subst U
    have hV₂bot : V₂ = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro v hv
      have hzV₁ : ρ z v ∈ V₁ := h.swap₂ hv
      have hzV₂ : ρ z v ∈ V₂ := hU z v hv
      have hz1 : ρ z v = 1 := by
        have hmem : ρ z v ∈ V₁ ⊓ V₂ := ⟨hzV₁, hzV₂⟩
        rwa [h.inf_eq_bot] at hmem
      exact (ρ z).injective (by rw [hz1, map_one])
    have hcard := h.card₂
    rw [hV₂bot, Subgroup.card_bot] at hcard
    norm_num at hcard
  · exfalso
    apply hX
    refine h.fixed ?_
    intro x v hv
    have hvU : v ∈ U := (hCV v).mpr hv
    exact (hCV (ρ x v)).mp (hU x v hvU)
  · exact Or.inr htop

theorem XHyp.eq_bot_of_isPGroup [Finite X] [Finite V] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    (hX : zpowers z ⊔ Q ≠ ⊤) {P : Subgroup X} (hP : P.Normal) (h2 : IsPGroup 2 P) : P = ⊥ := by
  letI : MulAction ↥P V := MulAction.compHom V (ρ.comp P.subtype)
  let U : Subgroup V :=
    { carrier := MulAction.fixedPoints ↥P V
      one_mem' := by
        rw [MulAction.mem_fixedPoints]
        intro p
        exact map_one (ρ.comp P.subtype p)
      mul_mem' := by
        intro a b ha hb
        rw [MulAction.mem_fixedPoints] at ha hb ⊢
        intro p
        change (ρ.comp P.subtype p) (a * b) = a * b
        have ha' : (ρ.comp P.subtype p) a = a := ha p
        have hb' : (ρ.comp P.subtype p) b = b := hb p
        rw [map_mul, ha', hb']
      inv_mem' := by
        intro a ha
        rw [MulAction.mem_fixedPoints] at ha ⊢
        intro p
        change (ρ.comp P.subtype p) a⁻¹ = a⁻¹
        have ha' : (ρ.comp P.subtype p) a = a := ha p
        rw [map_inv, ha'] }
  have hU : ∀ x : X, ∀ u ∈ U, ρ x u ∈ U := by
    intro x u hu
    have hu' : ∀ p : ↥P, (ρ.comp P.subtype p) u = u := fun p =>
      MulAction.mem_fixedPoints.mp hu p
    show ρ x u ∈ MulAction.fixedPoints ↥P V
    rw [MulAction.mem_fixedPoints]
    intro p
    change (ρ.comp P.subtype p) (ρ x u) = ρ x u
    have hmem : x⁻¹ * (p : X) * x ∈ P := hP.conj_mem' (p : X) p.2 x
    calc
      (ρ.comp P.subtype p) (ρ x u) = ρ (p : X) (ρ x u) := rfl
      _ = ρ ((p : X) * x) u := by rw [map_mul]; rfl
      _ = ρ (x * (x⁻¹ * (p : X) * x)) u := by congr 1; group
      _ = ρ x (ρ (x⁻¹ * (p : X) * x) u) := by rw [map_mul]; rfl
      _ = ρ x u := by
        have hfix : ρ (x⁻¹ * (p : X) * x) u = u := hu' ⟨x⁻¹ * (p : X) * x, hmem⟩
        rw [hfix]
  have hpV : 2 ∣ Nat.card V := by
    rw [h.card_V]
    norm_num
  have h1fix : (1 : V) ∈ MulAction.fixedPoints ↥P V := by
    rw [MulAction.mem_fixedPoints]
    intro p
    change (ρ.comp P.subtype p) 1 = 1
    exact map_one _
  obtain ⟨b, hb, hbne⟩ := h2.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hpV h1fix
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hbU : b ∈ U := hb
    have hb1 : b = 1 := by
      have hmem : b ∈ (⊥ : Subgroup V) := hbot ▸ hbU
      simpa using hmem
    exact hbne hb1.symm
  rcases h.eq_bot_or_eq_top hX hU with hbot | htop
  · exact absurd hbot hUne
  · rw [Subgroup.eq_bot_iff_forall]
    intro p hp
    have htriv : ρ p = 1 := by
      ext v
      have hv : v ∈ U := by rw [htop]; exact Subgroup.mem_top v
      have hv' : ∀ q : ↥P, (ρ.comp P.subtype q) v = v := fun q =>
        MulAction.mem_fixedPoints.mp hv q
      have hfix : ρ p v = v := hv' ⟨p, hp⟩
      simpa using hfix
    exact h.injective (by rw [htriv, map_one])

private noncomputable def conjZHom (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {O : Subgroup X}
    (hO : O.Normal) : ↥O →* ↥O where
  toFun o := ⟨z * (o : X) * z⁻¹, hO.conj_mem (o : X) o.2 z⟩
  map_one' := by
    ext
    simp
  map_mul' a b := by
    ext
    simp only [Subgroup.coe_mul]
    group

private theorem inf_centralizer_eq_bot (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {O : Subgroup X}
    (hO : O.Normal) (hodd : Odd (Nat.card O)) :
    O ⊓ Subgroup.centralizer ({z} : Set X) = ⊥ := by
  have hCnorm : ∀ c ∈ Subgroup.centralizer ({z} : Set X),
      ∀ y ∈ O ⊓ Subgroup.centralizer ({z} : Set X),
        c * y * c⁻¹ ∈ O ⊓ Subgroup.centralizer ({z} : Set X) := by
    intro c hc y hy
    obtain ⟨hyO, hyC⟩ := hy
    refine ⟨hO.conj_mem y hyO c, ?_⟩
    have hcEq : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hyEq : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    have hc' : c⁻¹ * z = z * c⁻¹ := by
      have hinv : c⁻¹ ∈ Subgroup.centralizer ({z} : Set X) :=
        (Subgroup.centralizer ({z} : Set X)).inv_mem hc
      exact Subgroup.mem_centralizer_singleton_iff.mp hinv
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc
        (c * y * c⁻¹) * z = c * (y * (c⁻¹ * z)) := by simp only [mul_assoc]
        _ = c * (y * (z * c⁻¹)) := by rw [hc']
        _ = c * ((y * z) * c⁻¹) := by simp only [mul_assoc]
        _ = c * ((z * y) * c⁻¹) := by rw [hyEq]
        _ = (c * z) * (y * c⁻¹) := by simp only [mul_assoc]
        _ = (z * c) * (y * c⁻¹) := by rw [hcEq]
        _ = z * (c * y * c⁻¹) := by simp only [mul_assoc])
  rcases h.le_zpowers_or_le (Y := O ⊓ Subgroup.centralizer ({z} : Set X)) inf_le_right hCnorm
    with hCz | hQ'C
  · rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    have hcz : c ∈ zpowers z := hCz hc
    have hcO : c ∈ O := hc.1
    have hodd_c : Odd (orderOf c) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hcO)
    have hdvd : orderOf c ∣ 2 := by
      have hdvd' := orderOf_dvd_of_mem_zpowers hcz
      rwa [h.orderOf_z] at hdvd'
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      exact (Nat.not_even_iff_odd.mpr hodd_c) (by rw [h2]; exact even_two)
  · exfalso
    have hdvd : Nat.card ↥⁅Q, Q⁆ ∣ Nat.card O :=
      (Subgroup.card_dvd_of_le hQ'C).trans (Subgroup.card_dvd_of_le inf_le_left)
    rw [h.card_commutator] at hdvd
    exact hodd.not_two_dvd_nat ((show (2 : ℕ) ∣ 443520 by norm_num).trans hdvd)

private theorem conjZHom_fixedPointFree (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {O : Subgroup X}
    (hO : O.Normal) (hodd : Odd (Nat.card O)) :
    MonoidHom.FixedPointFree (conjZHom h hO) := by
  intro o ho
  have hcoe : z * (o : X) * z⁻¹ = (o : X) := by
    simpa [conjZHom] using congrArg Subtype.val ho
  have hcomm : (o : X) * z = z * (o : X) := by
    calc
      (o : X) * z = (z * (o : X) * z⁻¹) * z := by rw [hcoe]
      _ = z * (o : X) := by group
  have hoC : (o : X) ∈ O ⊓ Subgroup.centralizer ({z} : Set X) := by
    refine ⟨o.2, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hbot := inf_centralizer_eq_bot h hO hodd
  have ho1 : (o : X) = 1 := by
    have hmem : (o : X) ∈ (⊥ : Subgroup X) := hbot ▸ hoC
    simpa using hmem
  exact Subtype.ext ho1

private theorem conjZHom_involutive (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {O : Subgroup X}
    (hO : O.Normal) : Function.Involutive (conjZHom h hO) := by
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.mul_self
  intro o
  ext
  show z * (z * (o : X) * z⁻¹) * z⁻¹ = (o : X)
  rw [hz]
  calc
    z * (z * (o : X) * z) * z = (z * z) * (o : X) * (z * z) := by group
    _ = (o : X) := by rw [h.mul_self]; group

theorem XHyp.conj_eq_inv_of_odd [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {O : Subgroup X}
    (hO : O.Normal) (hodd : Odd (Nat.card O)) {o : X} (ho : o ∈ O) : z * o * z⁻¹ = o⁻¹ := by
  haveI : Finite ↥O := Subtype.finite
  have hff := conjZHom_fixedPointFree h hO hodd
  have hinv := conjZHom_involutive h hO
  have hcoe := MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hff hinv
  have hval := congrArg Subtype.val (congrFun hcoe ⟨o, ho⟩)
  simpa [conjZHom] using hval

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
