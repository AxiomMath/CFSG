module

public import CFSG.LargeExtraspecial.S8A5C
public import CFSG.LargeExtraspecial.S8A5B
public import CFSG.LargeExtraspecial.S8ThreeD
public import CFSG.LargeExtraspecial.S9TIX

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.CGT.Timmesfeld75

universe u

section Abstract

variable {X : Type*} [Group X]

theorem conj_mem_normalizer_conjSubgroup {A : Subgroup X} {x y : X}
    (hy : y ∈ normalizer (A : Set X)) :
    x * y * x⁻¹ ∈ normalizer (conjSubgroup x A : Set X) := by
  rw [mem_normalizer_iff]
  intro h
  rw [mem_conjSubgroup, mem_conjSubgroup,
    show x⁻¹ * (x * y * x⁻¹ * h * (x * y * x⁻¹)⁻¹) * x = y * (x⁻¹ * h * x) * y⁻¹ by group]
  exact (mem_normalizer_iff.mp hy _)

theorem card_le_card_inf_centralizer_sq [Finite X] {A : Subgroup X} (hA : ∀ a ∈ A, a * a = 1)
    {s : X} (hs : s ∈ normalizer (A : Set X)) (hss : s * s = 1) :
    Nat.card A ≤ Nat.card (A ⊓ centralizer ({s} : Set X) : Subgroup X) ^ 2 := by
  have hcomm : ∀ {a b : X}, a ∈ A → b ∈ A → a * b = b * a := fun ha hb =>
    S9.TIX.comm_of_sq hA ha hb
  have hsA : ∀ a ∈ A, s * a * s⁻¹ ∈ A := fun a ha => (mem_normalizer_iff.mp hs a).mp ha
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  let φ : A →* A :=
    { toFun := fun a => ⟨(a : X) * (s * a * s⁻¹), mul_mem a.2 (hsA a a.2)⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have h1 := hcomm b.2 (hsA a a.2)
        calc (a : X) * b * (s * (a * b) * s⁻¹) = a * (b * (s * a * s⁻¹)) * (s * b * s⁻¹) := by
              group
          _ = a * ((s * a * s⁻¹) * b) * (s * b * s⁻¹) := by rw [h1]
          _ = a * (s * a * s⁻¹) * (b * (s * b * s⁻¹)) := by group }
  have hφ : ∀ a : A, ((φ a : A) : X) = a * (s * a * s⁻¹) := fun a => rfl
  have hker : ∀ a : A, a ∈ φ.ker → (a : X) ∈ A ⊓ centralizer ({s} : Set X) := by
    intro a ha
    refine ⟨a.2, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : (a : X) * (s * a * s⁻¹) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
      rwa [hφ] at this
    have hainv : (a : X)⁻¹ = a := inv_eq_of_mul_eq_one_right (hA a a.2)
    have h2 : s * a * s⁻¹ = a := by
      have := eq_inv_of_mul_eq_one_right h1
      rwa [hainv] at this
    calc (a : X) * s = (s * a * s⁻¹) * s := by rw [h2]
      _ = s * a := by group
  have hrange : ∀ a : A, a ∈ φ.range → (a : X) ∈ A ⊓ centralizer ({s} : Set X) := by
    rintro a ⟨b, rfl⟩
    refine ⟨(φ b).2, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [hφ]
    have h1 := hcomm (hsA b b.2) b.2
    calc (b : X) * (s * b * s⁻¹) * s = (b * (s * b * s⁻¹)) * s := by group
      _ = ((s * b * s⁻¹) * b) * s := by rw [h1]
      _ = s * (b * (s * b * s⁻¹)) := by rw [hsinv]; group
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
  have h2 : Nat.card φ.ker ≤ Nat.card (A ⊓ centralizer ({s} : Set X) : Subgroup X) :=
    Nat.card_le_card_of_injective (fun a => ⟨a.1.1, hker a.1 a.2⟩) (fun a b h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h))
  have h3 : Nat.card φ.range ≤ Nat.card (A ⊓ centralizer ({s} : Set X) : Subgroup X) :=
    Nat.card_le_card_of_injective (fun a => ⟨a.1.1, hrange a.1 a.2⟩) (fun a b h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h))
  rw [h1, pow_two]
  exact Nat.mul_le_mul h3 h2

end Abstract

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem mem_normalizer_Abar_of_fix_a (H : Hyp4 S g) {τ : S.O} (hτM : τ ∈ S.Mbar)
    (hτt : τ * t = t * τ)
    (hτa : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹)) :
    τ ∈ normalizer ((S.Lbar g ⊓ Nbar S g t : Subgroup S.O) : Set S.O) := by
  have hτL : τ ∈ normalizer (S.Lbar g : Set S.O) := by
    have h := mem_normalizer_of_fix H.conj_mem H.conj_ne (h := 1) hτM (by
      simp only [OneMemClass.coe_one, one_mul]
      exact hτa)
    simpa only [OneMemClass.coe_one, one_mul] using h
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hτM
  have hτN : ∀ n ∈ Nbar S g t, S.ρ k * n * (S.ρ k)⁻¹ ∈ Nbar S g t :=
    fun n hn => conj_mem_Nbar H.conj_mem hτt hn
  have hτN' : ∀ n ∈ Nbar S g t, (S.ρ k)⁻¹ * n * S.ρ k ∈ Nbar S g t := by
    intro n hn
    have h1 : S.ρ k⁻¹ * t = t * S.ρ k⁻¹ := by
      rw [map_inv]
      calc (S.ρ k)⁻¹ * t = (S.ρ k)⁻¹ * (t * S.ρ k) * (S.ρ k)⁻¹ := by group
        _ = (S.ρ k)⁻¹ * (S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hτt]
        _ = t * (S.ρ k)⁻¹ := by group
    have := conj_mem_Nbar H.conj_mem h1 hn
    rwa [map_inv, inv_inv] at this
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨hyL, hyN⟩
    exact ⟨(mem_normalizer_iff.mp hτL y).mp hyL, hτN y hyN⟩
  · rintro ⟨hyL, hyN⟩
    refine ⟨(mem_normalizer_iff.mp hτL y).mpr hyL, ?_⟩
    have := hτN' _ hyN
    rwa [show (S.ρ k)⁻¹ * (S.ρ k * y * (S.ρ k)⁻¹) * S.ρ k = y by group] at this

theorem comm_of_mem_normalizer_conj (ht : t ∈ S.Lbar g) (htN : t ∈ Nbar S g t)
    (h5 : ∀ y ∈ S.Mbar, y * t * y⁻¹ ∈ S.Lbar g → y * t * y⁻¹ = t) {x : S.O} (hxM : x ∈ S.Mbar)
    {α : S.O} (hαM : α ∈ S.Mbar)
    (hα : α ∈ normalizer (conjSubgroup x (S.Lbar g ⊓ Nbar S g t) : Set S.O)) :
    α * (x * t * x⁻¹) = (x * t * x⁻¹) * α := by
  have hσ : x * t * x⁻¹ ∈ conjSubgroup x (S.Lbar g ⊓ Nbar S g t) := by
    rw [mem_conjSubgroup, show x⁻¹ * (x * t * x⁻¹) * x = t by group]
    exact ⟨ht, htN⟩
  have h1 := (mem_normalizer_iff.mp hα _).mp hσ
  rw [mem_conjSubgroup, show x⁻¹ * (α * (x * t * x⁻¹) * α⁻¹) * x =
    (x⁻¹ * α * x) * t * (x⁻¹ * α * x)⁻¹ by group] at h1
  have h3 := h5 _ (S.Mbar.mul_mem (S.Mbar.mul_mem (inv_mem hxM) hαM) hxM) h1.1
  calc α * (x * t * x⁻¹) = x * ((x⁻¹ * α * x) * t * (x⁻¹ * α * x)⁻¹) * x⁻¹ * α := by group
    _ = x * t * x⁻¹ * α := by rw [h3]

theorem fix_commSpace_of_good (D : Std H C ht ht1 hVQ) {σ : S.O}
    (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hgood : Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) {α : S.O}
    (hαN : α ∈ Nbar S g t) (hασ : α * σ = σ * α) :
    ∀ v ∈ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt), (α : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  intro v hv
  have hvW := commSpace_le_Wt_of_fix hσV hv
  have h1 : (α : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g t := D.hN α hαN v hvW
  have h2 : (α : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    obtain ⟨y, rfl⟩ := mem_commSpace.mp hv
    refine Submodule.sub_mem _ (mem_commSpace.mpr ⟨(α : S.Qt ≃ₗ[ZMod 2] S.Qt) y, ?_⟩)
      (sub_mem_commSpace _ y)
    rw [map_sub, ← coe_mul_apply, ← coe_mul_apply, hασ]
  have h3 : (α : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈
      Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨h1, h2⟩
  rw [hgood, Submodule.mem_bot, sub_eq_zero] at h3
  exact h3

theorem mem_normalizer_conj_of_good (D : Std H C ht ht1 hVQ) {x σ : S.O} (hxM : x ∈ S.Mbar)
    (hxσ : σ = x * t * x⁻¹) (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hgood : Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) {α : S.O}
    (hαA : α ∈ S.Lbar g ⊓ Nbar S g t) (hασ : α * σ = σ * α) :
    α ∈ normalizer (conjSubgroup x (S.Lbar g ⊓ Nbar S g t) : Set S.O) := by
  have hfix := fix_commSpace_of_good D hσV hgood hαA.2 hασ
  have hαM : α ∈ S.Mbar := Rbar_le_Mbar (Nbar_le_Rbar hαA.2)
  have hyM : x⁻¹ * α * x ∈ S.Mbar := S.Mbar.mul_mem (S.Mbar.mul_mem (inv_mem hxM) hαM) hxM
  have hασ' : α * (x * t * x⁻¹) = (x * t * x⁻¹) * α := hxσ ▸ hασ
  have hyt : x⁻¹ * α * x * t = t * (x⁻¹ * α * x) := by
    calc x⁻¹ * α * x * t = x⁻¹ * (α * (x * t * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * t * x⁻¹) * α) * x := by rw [hασ']
      _ = t * (x⁻¹ * α * x) := by group
  have hyV : ∀ v ∈ Vt S g t, ((x⁻¹ * α * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro v hv
    have hxv : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [hxσ, commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1]
      exact ⟨v, hv, rfl⟩
    rw [coe_mul_apply, coe_mul_apply, hfix _ hxv, inv_apply_apply_O]
  have hyN := mem_normalizer_Abar_of_fix H ht hyM hyt hyV
  have := conj_mem_normalizer_conjSubgroup (x := x) hyN
  rwa [show x * (x⁻¹ * α * x) * x⁻¹ = α by group] at this

theorem five_le_finrank_clSub_inf_of_good (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2) {x σ : S.O}
    (hxM : x ∈ S.Mbar) (hxσ : σ = x * t * x⁻¹) (hσt : σ * t = t * σ)
    (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hgood : Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (hU : (Wt S g t).map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t =
      Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    5 ≤ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓
      (Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt))) := by
  have hσM : σ ∈ S.Mbar := by
    rw [hxσ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hUinv : ∀ r ∈ Rbar S g t, ∀ u ∈ Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [← hU]; exact comm_sup_Vt_invariant D hσM hσt hσV
  have hVU : Vt S g t ≤ Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := le_sup_left
  have hUW : Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Wt S g t :=
    sup_le (Vt_le_Wt H ht1) (commSpace_le_Wt_of_fix hσV)
  obtain ⟨-, -, htwo⟩ := finrank_map_mkQ_of_invariant hCE hNo hΩ D hVU hUW hUinv
  set P := S.clSub (S.QG ⊓ S.Qa g) with hP
  set U := Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hUdef
  set X := P ⊓ Wt S g t ⊔ Vt S g t with hX
  have hdimσ : finrank (ZMod 2) (commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t) := by
    rw [hxσ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj',
      (commSpace_t_eq H C ht ht1 hVQ).1]
  have hdimV := D.hdim
  rw [hm2] at hdimV
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (Vt S g t)
    (commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt))
  rw [hgood, finrank_bot, ← hUdef] at e1
  have e2 := finrank_map_add_finrank_inf_ker (Vt S g t).mkQ U
  rw [Submodule.ker_mkQ, inf_eq_right.mpr hVU] at e2
  have hVUX : Vt S g t ≤ U ⊓ X := le_inf hVU le_sup_right
  have e3 := finrank_map_add_finrank_inf_ker (Vt S g t).mkQ (U ⊓ X)
  rw [Submodule.ker_mkQ, inf_eq_right.mpr hVUX] at e3
  have hle : U ⊓ X ≤ P ⊓ U ⊔ Vt S g t := by
    rintro y ⟨hyU, hyX⟩
    obtain ⟨p, hp, v, hv, rfl⟩ := Submodule.mem_sup.mp hyX
    have hpU : p ∈ U := by
      have h1 := U.sub_mem hyU (hVU hv)
      rwa [add_sub_cancel_right] at h1
    exact Submodule.add_mem_sup ⟨hp.1, hpU⟩ hv
  have e4 := Submodule.finrank_mono hle
  have e5 := Submodule.finrank_sup_add_finrank_inf_eq (P ⊓ U) (Vt S g t)
  have e6 : P ⊓ U ⊓ Vt S g t = P ⊓ Vt S g t := by rw [inf_assoc, inf_eq_right.mpr hVU]
  rw [e6] at e5
  have e7 := finrank_clSub_inf_Vt H C ht ht1 hVQ
  rw [← hP] at e7
  omega

theorem four_mul_card_le_of_good (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2) {x σ : S.O}
    (hxM : x ∈ S.Mbar) (hxσ : σ = x * t * x⁻¹) (hσt : σ * t = t * σ)
    (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hgood : Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (hU : (Wt S g t).map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t =
      Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (hF : ∀ α ∈ S.Lbar g ⊓ Nbar S g t,
      α ∈ normalizer (conjSubgroup x (S.Lbar g ⊓ Nbar S g t) : Set S.O) → α * σ = σ * α) :
    4 * Nat.card (S.Lbar g ⊓ Nbar S g t ⊓
      normalizer (conjSubgroup x (S.Lbar g ⊓ Nbar S g t) : Set S.O) : Subgroup S.O) ≤
      Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
  set F := S.Lbar g ⊓ Nbar S g t ⊓
    normalizer (conjSubgroup x (S.Lbar g ⊓ Nbar S g t) : Set S.O) with hFdef
  have hFL : F ≤ S.Lbar g := fun α hα => hα.1.1
  have hcard := card_mul_two_pow_finrank_fix H C hFL
  have h5 := five_le_finrank_clSub_inf_of_good hCE hNo hΩ D hm2 hxM hxσ hσt hσV hgood hU
  have hle : S.clSub (S.QG ⊓ S.Qa g) ⊓ (Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤
      S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S F := by
    rintro u ⟨hu1, hu2⟩
    refine ⟨hu1, (mem_fixSub S).mpr fun α hα => ?_⟩
    have hασ := hF α hα.1 hα.2
    obtain ⟨v, hv, c, hc, rfl⟩ := Submodule.mem_sup.mp hu2
    rw [map_add, (mem_Nbar.mp hα.1.2).2 v hv,
      fix_commSpace_of_good D hσV hgood hα.1.2 hασ c hc]
  have h6 := Submodule.finrank_mono hle
  have hA := D.hA
  rw [D.hdim, hm2, show (2 : ℕ) ^ (2 * 2 - 1) = 8 by norm_num] at hA
  have h7 : Nat.card F * 2 ^ 5 ≤ Nat.card F * 2 ^ finrank (ZMod 2)
      ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S F) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (h5.trans h6))
  have h8 : Nat.card F * 32 ≤ 2 ^ S.width := h7.trans hcard.le
  omega

theorem two_lt_card_of_good (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) {x σ : S.O}
    (hxM : x ∈ S.Mbar) (hxσ : σ = x * t * x⁻¹) (hσt : σ * t = t * σ)
    (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hF : ∀ α ∈ S.Lbar g ⊓ Nbar S g t, α * σ = σ * α →
      α ∈ normalizer (conjSubgroup x (S.Lbar g ⊓ Nbar S g t) : Set S.O)) :
    2 < Nat.card (S.Lbar g ⊓ Nbar S g t ⊓
      normalizer (conjSubgroup x (S.Lbar g ⊓ Nbar S g t) : Set S.O) : Subgroup S.O) := by
  have haQ := H.conj_mem
  have hσM : σ ∈ S.Mbar := by
    rw [hxσ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hσσ : σ * σ = 1 := by
    rw [hxσ]
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  have hσA := mem_normalizer_Abar_of_fix H ht hσM hσt hσV
  have hsq : ∀ a ∈ S.Lbar g ⊓ Nbar S g t, a * a = 1 := fun a ha =>
    mul_self_of_mem_Lbar S haQ ha.1
  have h1 := card_le_card_inf_centralizer_sq hsq hσA hσσ
  have hle : S.Lbar g ⊓ Nbar S g t ⊓ centralizer ({σ} : Set S.O) ≤ S.Lbar g ⊓ Nbar S g t ⊓
      normalizer (conjSubgroup x (S.Lbar g ⊓ Nbar S g t) : Set S.O) := by
    rintro α ⟨hαA, hαC⟩
    exact ⟨hαA, hF α hαA (mem_centralizer_singleton_iff.mp hαC)⟩
  have h2 := Subgroup.card_le_of_le hle
  have hA := D.hA
  rw [D.hdim, hm2, show (2 : ℕ) ^ (2 * 2 - 1) = 8 by norm_num] at hA
  have hw := D.finrank_WV
  have h8 := eight_le_finrank_WV hCE hNo hΩ D hm2 hmin hA7
  rw [hm2] at hw
  have hn : 8 ≤ S.width := by omega
  have h256 : 2 ^ 8 ≤ 2 ^ S.width := Nat.pow_le_pow_right (by norm_num) hn
  by_contra hcon
  push Not at hcon
  have h3 : Nat.card (S.Lbar g ⊓ Nbar S g t ⊓ centralizer ({σ} : Set S.O) : Subgroup S.O) ^ 2 ≤
      2 ^ 2 := Nat.pow_le_pow_left (h2.trans hcon) 2
  omega

theorem conj_Abar_eq_of_inf_A5 (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2) (hmin : D.IsMinus)
    {y : S.O} (hyM : y ∈ S.Mbar) (hyt : y * t = t * y) {a : S.O}
    (ha : a ∈ S.Lbar g ⊓ Nbar S g t ⊓ conjSubgroup y (S.Lbar g ⊓ Nbar S g t))
    (hat : a ∉ zpowers t) :
    conjSubgroup y (S.Lbar g ⊓ Nbar S g t) = S.Lbar g ⊓ Nbar S g t := by
  have haQ := H.conj_mem
  set A := S.Lbar g ⊓ Nbar S g t with hA
  set yC : CMt S t := ⟨y, mem_CMt.mpr ⟨hyM, hyt⟩⟩ with hyC
  set α := resCV S g haQ t yC (aV ht) with hα
  have hα0 : α ≠ 0 := fun h =>
    aV_ne_zero H ht ((resCV S g haQ t yC).injective (h.trans (map_zero _).symm))
  have hQα : D.Q α = 0 := by rw [hα, D.Q_resCV]; exact D.hQa
  have hαorb := (D.hsing α hα0).mp hQα
  obtain ⟨k, hk, hkα⟩ := exists_of_mem_orbit ((mem_orbitOf_RmodN_iff haQ ht).mp hαorb) haQ
  have hαc : (α : S.Qt) = (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := rfl
  have hka : ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := ρ_cl_conj_z S k haQ
  have hkt : S.ρ k * t = t * S.ρ k := commute_of_mem_Rbar haQ hk
  have hzM : (S.ρ k)⁻¹ * y ∈ S.Mbar := S.Mbar.mul_mem (inv_mem (Rbar_le_Mbar hk)) hyM
  have hzt : (S.ρ k)⁻¹ * y * t = t * ((S.ρ k)⁻¹ * y) := by
    calc (S.ρ k)⁻¹ * y * t = (S.ρ k)⁻¹ * (t * y) := by rw [mul_assoc, hyt]
      _ = (S.ρ k)⁻¹ * (t * S.ρ k) * ((S.ρ k)⁻¹ * y) := by group
      _ = (S.ρ k)⁻¹ * (S.ρ k * t) * ((S.ρ k)⁻¹ * y) := by rw [hkt]
      _ = t * ((S.ρ k)⁻¹ * y) := by group
  have hza : (((S.ρ k)⁻¹ * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := by
    rw [coe_mul_apply, ← hαc, hkα, ← hka, inv_apply_apply_O]
  have hzA := mem_normalizer_Abar_of_fix_a H hzM hzt hza
  have hyA : conjSubgroup y A = conjSubgroup (S.ρ k) A := by
    rw [show y = S.ρ k * ((S.ρ k)⁻¹ * y) by group, S9.TIX.conjSubgroup_mul,
      S9.TIX.conjSubgroup_eq_self_iff.mpr hzA]
  rw [hyA] at ha ⊢
  by_cases hca : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) = S.cl (g * S.z * g⁻¹)
  ·
    rw [← hka] at hca
    exact S9.TIX.conjSubgroup_eq_self_iff.mpr
      (mem_normalizer_Abar_of_fix_a H (Rbar_le_Mbar hk) hkt hca)
  · exfalso
    have hαa : α ≠ aV ht := fun h => hca (by rw [← hkα, h]; rfl)
    have hpolβ : ∀ u w : Vt S g t, polar D.Q u w = beta H C ht ht1 hVQ u w := fun u w => by
      rw [← polarBilin_apply_apply, D.hpol]
    have hβ : beta H C ht ht1 hVQ (aV ht) α = 1 := by
      rcases zmod2_eq_zero_or_eq_one (beta H C ht ht1 hVQ (aV ht) α) with h0 | h1
      · exfalso
        have hli : LinearIndependent (ZMod 2) ![aV ht, α] := by
          refine (LinearIndependent.pair_iff' (aV_ne_zero H ht)).mpr fun c hc => ?_
          rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
          · rw [zero_smul] at hc; exact hα0 hc.symm
          · rw [one_smul] at hc; exact hαa hc.symm
        have hT : ∀ w ∈ Submodule.span (ZMod 2) {aV ht, α}, D.Q w = 0 := by
          intro w hw
          obtain ⟨a', b', rfl⟩ := Submodule.mem_span_pair.mp hw
          rw [QuadraticMap.map_add D.Q (a' • aV ht) (b' • α), QuadraticMap.map_smul,
            QuadraticMap.map_smul, D.hQa, hQα, polar_smul_left, polar_smul_right, hpolβ, h0]
          simp
        have h2 := hmin _ hT
        rw [finrank_span_pair hli, hm2] at h2
        omega
      · exact h1
    have hcQ : (k : G) * g * S.z * ((k : G) * g)⁻¹ ∉ S.Qa g := by
      intro hmem
      have h1 : (α : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa g) := by
        rw [hkα]
        exact S.cl_mem_clSub ⟨conj_mem_QG' S k.2 haQ, hmem⟩ (conj_mem_QG' S k.2 haQ)
      rw [← beta_aV_eq_zero_iff H C ht ht1 hVQ, hβ] at h1
      exact one_ne_zero h1
    have h65 := (timmesfeld_6_5_bar H C ht ht1 hVQ D.hgen D.hN0 hk hcQ).2
    have haL : a ∈ S.Lbar g ⊓ S.Lbar ((k : G) * g) := by
      refine ⟨ha.1.1, ?_⟩
      have h1 := (mem_conjSubgroup.mp ha.2).1
      rw [Lbar_mul S k g]
      exact ⟨_, h1, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [h65] at haL
    exact hat haL

end CFSG.LargeExtraspecial.S8
