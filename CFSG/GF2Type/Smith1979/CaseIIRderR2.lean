module

public import CFSG.GF2Type.Smith1979.CaseIIRderR1
public import CFSG.GF2Type.Smith1979.CaseIIRderFix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

@[expose] def conjSelf {M : Type*} [Group M] (y : M) (A : Subgroup M)
    (hA : ∀ a ∈ A, y * a * y⁻¹ ∈ A) : A → A :=
  fun b => ⟨y * b * y⁻¹, hA b b.2⟩

theorem conjSelf_val {M : Type*} [Group M] (y : M) (A : Subgroup M)
    (hA : ∀ a ∈ A, y * a * y⁻¹ ∈ A) (b : A) :
    ((conjSelf y A hA b : A) : M) = y * b * y⁻¹ :=
  rfl

theorem conjSelf_iterate {M : Type*} [Group M] (y : M) (A : Subgroup M)
    (hA : ∀ a ∈ A, y * a * y⁻¹ ∈ A) (k : ℕ) (a : A) :
    (((conjSelf y A hA)^[k] a : A) : M) = y ^ k * a * (y ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', conjSelf_val, ih, pow_succ]
    group

theorem not_mem_Nbar_of_orderOf (hNsq : ∀ a ∈ Nbar S g t, a * a = 1) {y : S.O}
    (hy : orderOf y = 7) : y ∉ Nbar S g t := by
  intro hN
  have h2 : y ^ 2 = 1 := by
    rw [pow_two]
    exact hNsq y hN
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  rw [hy] at hdvd
  omega

theorem conj_mem_Nbar_of_Rbar (D : Data S g t) {y : S.O} (hy : y ∈ Rbar S g t) {n : S.O}
    (hn : n ∈ Nbar S g t) : y * n * y⁻¹ ∈ Nbar S g t := by
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hy)
  have hρk : S.ρ k * t = t * S.ρ k := by
    rw [hk]
    exact commute_of_mem_Rbar D.H.conj_mem hy
  have h := conj_mem_Nbar D.H.conj_mem hρk hn
  rwa [hk] at h

theorem conj_mem_Sbar (D : Data S g t) (hCE : S4.CentralExtInput.{u}) {y : S.O}
    (hy : y ∈ Rder S g t) {s : S.O} (hs : s ∈ Rder S g t ⊓ Nbar S g t) :
    y * s * y⁻¹ ∈ Rder S g t ⊓ Nbar S g t :=
  ⟨(Rder S g t).mul_mem ((Rder S g t).mul_mem hy hs.1) ((Rder S g t).inv_mem hy),
    conj_mem_Nbar_of_Rbar D (Rder_le_Rbar' D hCE hy) hs.2⟩

theorem Vt_card (D : Data S g t) : Nat.card (Vt S g t) = 8 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), D.h3, Nat.card_zmod]
  norm_num

theorem seven_orbit_facts {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : Nat.card V = 8) (h : V ≃ₗ[ZMod 2] V) (h7 : h ^ 7 = 1) (h1 : h ≠ 1) :
    (∀ v : V, h v = v → v = 0) ∧
      ∀ v₀ : V, v₀ ≠ 0 → ∀ w : V, w ≠ 0 → ∃ k : ℕ, (⇑h)^[k] v₀ = w := by
  have hf7 : (⇑h)^[7] = id := by
    rw [← LinearEquiv.coe_pow, h7]
    rfl
  have hfix : ∀ v : V, h v = v → v = 0 := by
    have hne : ∃ v : V, h v ≠ v := by
      by_contra hcon
      push Not at hcon
      apply h1
      apply LinearEquiv.ext
      intro v
      change h v = v
      exact hcon v
    exact unique_fixed_of_seven hV (⇑h) hf7 (map_zero h) hne
  exact ⟨hfix, fun v₀ hv₀ w hw => orbit_of_seven hV (⇑h) hf7 (map_zero h) hfix hv₀ hw⟩

theorem action_one_of_orbit {A : Type*} [Group A] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (ψ : A →* (V ≃ₗ[ZMod 2] V)) (z a₀ : A) (v₀ : V)
    (hcomm : Commute z a₀) (hz : ψ z v₀ = v₀)
    (horb : ∀ w : V, w ≠ 0 → ∃ j : ℕ, (⇑(ψ a₀))^[j] v₀ = w) : ψ z = 1 := by
  have hcf : Function.Commute (⇑(ψ z)) (⇑(ψ a₀)) := by
    intro v
    have := congrArg (fun e : V ≃ₗ[ZMod 2] V => e v) (hcomm.map ψ).eq
    simpa only [LinearEquiv.mul_apply] using this
  have hpres : ∀ j : ℕ, ψ z ((⇑(ψ a₀))^[j] v₀) = (⇑(ψ a₀))^[j] v₀ := by
    intro j
    have hc := (hcf.symm.iterate_left j) v₀
    rw [hz] at hc
    exact hc.symm
  apply LinearEquiv.ext
  intro w
  change ψ z w = w
  by_cases hw : w = 0
  · rw [hw, map_zero]
  · obtain ⟨j, hj⟩ := horb w hw
    rw [← hj]
    exact hpres j

theorem exists_orderOf_seven_Rder (D : Data S g t) (hCE : S4.CentralExtInput.{u}) :
    ∃ y₀ : ↥(Rder S g t), orderOf y₀ = 7 := by
  obtain ⟨-, -, -, -, -, -, -, hcardP, -, -, -, -, -⟩ := Rbar_structure_II D hCE
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact exists_prime_orderOf_dvd_card' 7 (by rw [hcardP]; exact ⟨192, by norm_num⟩)

theorem Sbar_fixed_eq_one (D : Data S g t) (hCE : S4.CentralExtInput.{u}) {y : S.O}
    (hyP : y ∈ Rder S g t) (hy7 : orderOf y = 7) :
    ∀ s ∈ Rder S g t ⊓ Nbar S g t, y * s * y⁻¹ = s → s = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hcardS, -, -, hNsq⟩ := Rbar_structure_II D hCE
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hy7p : y ^ 7 = 1 := by
    rw [← hy7]
    exact pow_orderOf_eq_one y
  have hA : ∀ a ∈ Rder S g t ⊓ Nbar S g t, y * a * y⁻¹ ∈ Rder S g t ⊓ Nbar S g t :=
    fun a ha => conj_mem_Sbar D hCE hyP ha
  have hf7 : (conjSelf y _ hA)^[7] = id := by
    funext a
    apply Subtype.ext
    rw [conjSelf_iterate, hy7p]
    simp
  have hne : ∃ a : ↥(Rder S g t ⊓ Nbar S g t), conjSelf y _ hA a ≠ a := by
    by_contra hcon
    push Not at hcon
    apply not_mem_Nbar_of_orderOf hNsq hy7
    refine Rder_faithful_on_Sbar D hCE y hyP ?_
    intro s hs
    exact congrArg Subtype.val (hcon ⟨s, hs⟩)
  have hx0 : conjSelf y _ hA ⟨1, (Rder S g t ⊓ Nbar S g t).one_mem⟩ =
      ⟨1, (Rder S g t ⊓ Nbar S g t).one_mem⟩ := by
    apply Subtype.ext
    simp [conjSelf_val]
  have huniq := unique_fixed_of_seven hcardS (conjSelf y _ hA) hf7 hx0 hne
  intro s hs hs'
  have h1 := huniq ⟨s, hs⟩ (Subtype.ext hs')
  exact congrArg Subtype.val h1

theorem exists_seven_Rder (D : Data S g t) (hCE : S4.CentralExtInput.{u}) :
    ∃ y ∈ Rder S g t, orderOf y = 7 ∧
      (∀ s ∈ Rder S g t ⊓ Nbar S g t, y * s * y⁻¹ = s → s = 1) ∧
      ∀ x ∈ Rder S g t, x * y = y * x → x ∈ Subgroup.zpowers y := by
  obtain ⟨-, -, -, hle, -, -, -, -, -, hcardS, -, -, hNsq⟩ := Rbar_structure_II D hCE
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨y₀, hy₀⟩ := exists_orderOf_seven_Rder D hCE
  have hy₀p : y₀ ^ 7 = 1 := by
    rw [← hy₀]
    exact pow_orderOf_eq_one y₀
  have hyP : (y₀ : S.O) ∈ Rder S g t := y₀.2
  have hy7 : orderOf (y₀ : S.O) = 7 := by
    rw [Subgroup.orderOf_coe, hy₀]
  have hyN : (y₀ : S.O) ∉ Nbar S g t := not_mem_Nbar_of_orderOf hNsq hy7
  have hfixS := Sbar_fixed_eq_one D hCE hyP hy7
  have hψ7 : psiP D.H.conj_mem t hle y₀ ^ 7 = 1 := by
    rw [← map_pow, hy₀p, map_one]
  have hψ1 : psiP D.H.conj_mem t hle y₀ ≠ 1 := fun h1 =>
    hyN ((psiP_eq_one_iff D.H.conj_mem t hle y₀).mp h1)
  obtain ⟨-, horbV⟩ := seven_orbit_facts (Vt_card D) _ hψ7 hψ1
  haveI : Finite (Vt S g t) := Module.finite_of_finite (ZMod 2) (M := Vt S g t)
  haveI : Nontrivial (Vt S g t) :=
    (Finite.one_lt_card_iff_nontrivial).mp (by rw [Vt_card D]; norm_num)
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : Vt S g t)
  refine ⟨(y₀ : S.O), hyP, hy7, hfixS, ?_⟩
  intro x hx hxy
  have hw0 : psiP D.H.conj_mem t hle ⟨x, hx⟩ v₀ ≠ 0 := fun h0 =>
    hv₀ ((LinearEquiv.map_eq_zero_iff _).mp h0)
  obtain ⟨k, hk⟩ := horbV v₀ hv₀ _ hw0
  have hk' : (psiP D.H.conj_mem t hle y₀ ^ k) v₀ = psiP D.H.conj_mem t hle ⟨x, hx⟩ v₀ :=
    (congrFun (LinearEquiv.coe_pow _ k) v₀).trans hk
  have hz : psiP D.H.conj_mem t hle ((y₀ ^ k)⁻¹ * ⟨x, hx⟩) v₀ = v₀ := by
    rw [map_mul, map_inv, map_pow, LinearEquiv.mul_apply, ← hk', ← LinearEquiv.mul_apply,
      inv_mul_cancel]
    rfl
  have hxc : Commute (⟨x, hx⟩ : ↥(Rder S g t)) y₀ := Subtype.ext hxy
  have hcomm : Commute ((y₀ ^ k)⁻¹ * ⟨x, hx⟩) y₀ :=
    (((Commute.refl y₀).pow_left k).inv_left).mul_left hxc
  have hz1 := action_one_of_orbit (psiP D.H.conj_mem t hle) _ y₀ v₀ hcomm hz
    (horbV v₀ hv₀)
  generalize hz_eq : (y₀ ^ k)⁻¹ * (⟨x, hx⟩ : ↥(Rder S g t)) = z at hz1 hcomm
  have hzN : (z : S.O) ∈ Nbar S g t := (psiP_eq_one_iff D.H.conj_mem t hle z).mp hz1
  have hzcent : (y₀ : S.O) * (z : S.O) * (y₀ : S.O)⁻¹ = (z : S.O) := by
    have h2 : (z : S.O) * (y₀ : S.O) = (y₀ : S.O) * (z : S.O) := congrArg Subtype.val hcomm.eq
    rw [← h2, mul_inv_cancel_right]
  have hzone : (z : S.O) = 1 := hfixS (z : S.O) ⟨z.2, hzN⟩ hzcent
  have h4 : ((y₀ : S.O) ^ k)⁻¹ * x = 1 := by
    have h5 : (z : S.O) = ((y₀ : S.O) ^ k)⁻¹ * x := by
      rw [← hz_eq]
      simp [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    rw [← h5, hzone]
  rw [(inv_mul_eq_one.mp h4).symm]
  exact pow_mem (Subgroup.mem_zpowers _) k

theorem exists_six_Rder (D : Data S g t) (hCE : S4.CentralExtInput.{u}) :
    ∃ x ∈ Rder S g t, orderOf x = 6 := by
  obtain ⟨-, -, -, -, -, -, -, hcardP, -, hcardS, -, -, hNsq⟩ := Rbar_structure_II D hCE
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y₃, hy₃⟩ : ∃ y₃ : ↥(Rder S g t), orderOf y₃ = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [hcardP]; exact ⟨448, by norm_num⟩)
  have hyP : (y₃ : S.O) ∈ Rder S g t := y₃.2
  have hy3 : orderOf (y₃ : S.O) = 3 := by
    rw [Subgroup.orderOf_coe, hy₃]
  have hy3p : (y₃ : S.O) ^ 3 = 1 := by
    rw [← hy3]
    exact pow_orderOf_eq_one _
  have hA : ∀ a ∈ Rder S g t ⊓ Nbar S g t,
      (y₃ : S.O) * a * (y₃ : S.O)⁻¹ ∈ Rder S g t ⊓ Nbar S g t :=
    fun a ha => conj_mem_Sbar D hCE hyP ha
  have hf3 : (conjSelf (y₃ : S.O) _ hA)^[3] = id := by
    funext a
    apply Subtype.ext
    rw [conjSelf_iterate, hy3p]
    simp
  have hx0 : conjSelf (y₃ : S.O) _ hA ⟨1, (Rder S g t ⊓ Nbar S g t).one_mem⟩ =
      ⟨1, (Rder S g t ⊓ Nbar S g t).one_mem⟩ := by
    apply Subtype.ext
    simp [conjSelf_val]
  obtain ⟨u, hu, hu1⟩ := exists_fixed_ne_of_three hcardS (conjSelf (y₃ : S.O) _ hA) hf3 hx0
  have hufix : (y₃ : S.O) * (u : S.O) * (y₃ : S.O)⁻¹ = (u : S.O) := congrArg Subtype.val hu
  have hu1' : (u : S.O) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huu : (u : S.O) * (u : S.O) = 1 := hNsq _ u.2.2
  have hu2 : orderOf (u : S.O) = 2 :=
    orderOf_eq_prime (p := 2) (by rw [pow_two]; exact huu) hu1'
  have hcomm : Commute (u : S.O) (y₃ : S.O) := (mul_inv_eq_iff_eq_mul.mp hufix).symm
  have hord : orderOf ((u : S.O) * (y₃ : S.O)) = 6 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hu2, hy3]; decide), hu2, hy3]
  exact ⟨(u : S.O) * (y₃ : S.O), (Rder S g t).mul_mem u.2.1 y₃.2, hord⟩

end CFSG.GF2Type.Smith1979.Case2
