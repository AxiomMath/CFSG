module

public import CFSG.LargeExtraspecial.S6Pkg
public import CFSG.LargeExtraspecial.S2Three

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4

section Swap

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]

theorem finrank_le_of_swap (y : U →ₗ[ZMod 2] U) (hyy : ∀ u, y (y u) = u)
    {X B B' W F : Submodule (ZMod 2) U} (hyX : ∀ x ∈ X, y x ∈ X) (hXB : X ≤ B)
    (hsup : B ⊔ B' = W) (hinf : B ⊓ B' = X) (hyB : ∀ u ∈ B, y u ∈ B')
    (hyB' : ∀ u ∈ B', y u ∈ B) (hFW : F ≤ W) (hF : ∀ w ∈ F, y w - w ∈ X) :
    finrank (ZMod 2) F ≤ finrank (ZMod 2) B := by
  set φ : U →ₗ[ZMod 2] U ⧸ X := X.mkQ ∘ₗ (LinearMap.id + y) with hφ
  have hφapp : ∀ u, φ u = Submodule.Quotient.mk (u + y u) := fun u => rfl
  have hFmap : F.map X.mkQ ≤ B.map φ := by
    rintro _ ⟨w, hw, rfl⟩
    have hwW := hFW hw
    rw [← hsup] at hwW
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hwW
    have h1 := hF _ hw
    have h2 : y u' - u ∈ X := by
      rw [← hinf]
      refine ⟨sub_mem (hyB' u' hu') hu, ?_⟩
      have h3 : y (u + u') - (u + u') - (y u - u') = y u' - u := by rw [map_add]; abel
      rw [← h3]
      exact sub_mem ((hinf ▸ inf_le_right : X ≤ B') h1) (sub_mem (hyB u hu) hu')
    refine ⟨u, hu, ?_⟩
    rw [hφapp, Submodule.mkQ_apply, Submodule.Quotient.eq]
    have h4 : u + y u - (u + u') = -(y (y u' - u)) := by
      rw [map_sub, hyy]
      abel
    rw [h4]
    exact neg_mem (hyX _ h2)
  have hker : X ≤ B ⊓ LinearMap.ker φ := by
    intro x hx
    refine ⟨hXB hx, ?_⟩
    change φ x = 0
    rw [hφapp, Submodule.Quotient.mk_eq_zero]
    exact add_mem hx (hyX x hx)
  have hFX : F ⊓ LinearMap.ker X.mkQ ≤ X := by
    intro w hw
    rw [Submodule.ker_mkQ] at hw
    exact hw.2
  have e1 := S2.finrank_map_add_finrank_inf_ker X.mkQ F
  have e2 := S2.finrank_map_add_finrank_inf_ker φ B
  have i1 := Submodule.finrank_mono hFmap
  have i2 := Submodule.finrank_mono hker
  have i3 := Submodule.finrank_mono hFX
  omega

theorem finrank_le_of_swap' (y : U ≃ₗ[ZMod 2] U) (hyy : ∀ u, y (y u) = u)
    {X B B' W F : Submodule (ZMod 2) U} (hyX : ∀ x ∈ X, y x ∈ X) (hXB : X ≤ B)
    (hsup : B ⊔ B' = W) (hinf : B ⊓ B' = X) (hyB : ∀ u ∈ B, y u ∈ B')
    (hyB' : ∀ u ∈ B', y u ∈ B) (hFW : F ≤ W) (hF : ∀ w ∈ F, y w - w ∈ X) :
    finrank (ZMod 2) F ≤ finrank (ZMod 2) B :=
  finrank_le_of_swap y.toLinearMap hyy hyX hXB hsup hinf hyB hyB' hFW hF

end Swap

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem card_Lbar_mul_inf_Nbar (H : Hyp4 S g) {t : S.O} {k : S.M} (hk : S.ρ k ∈ Rbar S g t) :
    Nat.card (S.Lbar ((k : G) * g) ⊓ Nbar S g t : Subgroup S.O) =
      Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
  have hc := commute_of_mem_Rbar H.conj_mem hk
  have hN : (Nbar S g t).map (MulAut.conj (S.ρ k)).toMonoidHom = Nbar S g t := by
    refine le_antisymm ?_ fun x hx => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact conj_mem_Nbar H.conj_mem hc hx
    · refine ⟨(S.ρ k)⁻¹ * x * S.ρ k, ?_, by simp [mul_assoc]⟩
      have hc' : S.ρ k⁻¹ * t = t * S.ρ k⁻¹ := by
        rw [map_inv]
        exact commute_inv hc
      have := conj_mem_Nbar H.conj_mem hc' hx
      simpa [map_inv] using this
  have e : S.Lbar ((k : G) * g) ⊓ Nbar S g t =
      (S.Lbar g ⊓ Nbar S g t).map (MulAut.conj (S.ρ k)).toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj (S.ρ k)).injective, hN, Lbar_mul S k g]
  rw [e, card_map_of_injective (MulAut.conj (S.ρ k)).injective]

theorem RadBound.mul (H : Hyp4 S g) {t : S.O} (hR : RadBound S g t) {k : S.M}
    (hk : S.ρ k ∈ Rbar S g t) : RadBound S ((k : G) * g) t := by
  unfold RadBound at hR ⊢
  rw [Vt_mul, Nbar_mul, card_Lbar_mul_inf_Nbar H hk, Lbar_mul S k g,
    card_map_of_injective (MulAut.conj (S.ρ k)).injective]
  exact hR

@[expose] def PairInt (S : Setting G) (g : G) (t : S.O) : Prop :=
  ∀ k k' : S.M, S.ρ k ∈ Rbar S g t → S.ρ k' ∈ Rbar S g t →
    (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g) →
    S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ≤ Vt S g t

theorem pairInt_of_radBound (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hR : RadBound S g t) : PairInt S g t := by
  intro k k' hk hk' hkk'
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have hcoe : (((k' * k⁻¹ : S.M) : G) * ((k : G) * g)) = (k' : G) * g := by
    simp [mul_assoc]
  have hk'' : S.ρ (k' * k⁻¹) ∈ Rbar S ((k : G) * g) t := by
    rw [Rbar_mul, map_mul, map_inv]; exact mul_mem hk' (inv_mem hk)
  have h1 := clSub_inf_clSub_le_Vt (H.mul k) (C.mul k) htk ht1 (not_V_le_Qa_mul H hVQ hk)
    hk'' (by rw [hcoe]; exact hkk') (hR.mul H hk)
  rw [hcoe, Vt_mul] at h1
  exact h1

section Fix

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
include H C ht ht1 hVQ hh

theorem mem_sup_Vt_of_fix {y : S.M} (hyL : (y : G) ∈ S.L0 g)
    (hyb : (y : G) * ((h : G) * g) * S.z * ((y : G) * ((h : G) * g))⁻¹ ∉ S.Qa ((h : G) * g))
    (hP : S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓
      S.clSub (S.QG ⊓ S.Qa ((y : G) * ((h : G) * g))) ≤ Vt S g t)
    {w : S.Qt} (hw : w ∈ Wt S g t)
    (hfix : ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) :
    w ∈ (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t := by
  have hth := mem_Lbar_of_pair H ht hh
  have hyLb : S.ρ y ∈ S.Lbar g := ρ_mem_Lbar S hyL
  have hyR : S.ρ y ∈ Rbar S g t := Lbar_le_Rbar ht hyLb
  have hyR₁ : S.ρ y ∈ Rbar S ((h : G) * g) t := by rw [Rbar_mul]; exact hyR
  have hVQ₁ := not_V_le_Qa_mul H hVQ hh
  have hP₁ : S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓
      S.clSub (S.QG ⊓ S.Qa ((y : G) * ((h : G) * g))) ≤ Vt S ((h : G) * g) t := by
    rw [Vt_mul]; exact hP
  have hinf := sup_Vt_inf_sup_Vt (H.mul h) (C.mul h) hth ht1 hVQ₁ hyR₁ hyb hP₁
  have hdec := sup_eq_Wt (H.mul h) (C.mul h) hth ht1 hVQ₁ hyR₁ hyb hP₁
  have dB := finrank_sup_Vt (H.mul h) (C.mul h) hth ht1 hVQ₁
  have dA := finrank_sup_Vt H C ht ht1 hVQ
  rw [Wt_mul, Vt_mul] at hinf dB
  rw [Wt_mul] at hdec
  set ψ : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hψ
  have hyy : S.ρ y * S.ρ y = 1 := mul_self_of_mem_Lbar S H.conj_mem hyLb
  have hinv : (S.ρ y)⁻¹ = S.ρ y := inv_eq_of_mul_eq_one_right hyy
  have hψψ : ∀ u, ψ (ψ u) = u := fun u => by
    rw [hψ, ← coe_mul_apply, hyy]
    rfl
  set A := (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t with hA
  set B := (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t with hB
  set B' := (S.clSub (S.QG ⊓ S.Qa ((y : G) * ((h : G) * g))) ⊓ Wt S g t) ⊔ Vt S g t with hB'
  have hψV : ∀ v ∈ Vt S g t, ψ v ∈ Vt S g t := fun v hv =>
    apply_mem_Vt_of_mem_Rbar H.conj_mem hyR hv
  have hψW : ∀ v ∈ Wt S g t, ψ v ∈ Wt S g t := fun v hv => apply_mem_Wt H hyR hv
  have hsup : B ⊔ B' = Wt S g t := by
    refine le_antisymm (sup_le (sup_le inf_le_right (Vt_le_Wt H ht1))
      (sup_le inf_le_right (Vt_le_Wt H ht1))) ?_
    conv_lhs => rw [← hdec]
    exact sup_le_sup le_sup_left le_sup_left
  have hψB : ∀ u ∈ B, ψ u ∈ B' := by
    intro u hu
    obtain ⟨x, hx, v, hv, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    exact add_mem (Submodule.mem_sup_left ⟨apply_mem_clSub_Qa_mul y hx.1, hψW x hx.2⟩)
      (Submodule.mem_sup_right (hψV v hv))
  have hψB' : ∀ u ∈ B', ψ u ∈ B := by
    intro u hu
    obtain ⟨x, hx, v, hv, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    refine add_mem (Submodule.mem_sup_left ⟨?_, hψW x hx.2⟩)
      (Submodule.mem_sup_right (hψV v hv))
    have := (mem_clSub_Qa_mul_iff y).mp hx.1
    rwa [hinv] at this
  set F := Wt S g t ⊓ (Vt S g t).comap ((ψ : S.Qt →ₗ[ZMod 2] S.Qt) - LinearMap.id) with hF
  have hFle := finrank_le_of_swap (ψ : S.Qt →ₗ[ZMod 2] S.Qt) hψψ hψV le_sup_right hsup hinf
    hψB hψB' (inf_le_left : F ≤ Wt S g t) fun w hw => hw.2
  have hAF : A ≤ F := by
    intro u hu
    refine ⟨sup_le inf_le_right (Vt_le_Wt H ht1) hu, ?_⟩
    obtain ⟨x, hx, v, hv, rfl⟩ := Submodule.mem_sup.mp hu
    change ψ (x + v) - (x + v) ∈ Vt S g t
    rw [map_add, show ψ x + ψ v - (x + v) = (ψ x - x) + (ψ v - v) by abel]
    refine add_mem ?_ (sub_mem (hψV v hv) hv)
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr (cl_a_mem_Vt ht)
      (Lbar_apply_sub_mem_span' H.conj_mem hx.1 hyLb)
  have hAF' : A = F := Submodule.eq_of_le_of_finrank_le hAF (hFle.trans (dB.trans dA.symm).le)
  rw [hAF']
  exact ⟨hw, hfix⟩

theorem forall_apply_sub_mem_Vt_iff {y : S.M} (hyL : (y : G) ∈ S.L0 g)
    (hyb : (y : G) * ((h : G) * g) * S.z * ((y : G) * ((h : G) * g))⁻¹ ∉ S.Qa ((h : G) * g))
    (hP : S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓
      S.clSub (S.QG ⊓ S.Qa ((y : G) * ((h : G) * g))) ≤ Vt S g t)
    {w : S.Qt} (hw : w ∈ Wt S g t) :
    (∀ l ∈ S.Lbar g, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) ↔
      w ∈ (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t := by
  constructor
  · intro hl
    exact mem_sup_Vt_of_fix H C ht ht1 hVQ hh hyL hyb hP hw (hl _ (ρ_mem_Lbar S hyL))
  · intro hu l hl
    obtain ⟨x, hx, v, hv, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add, show (l : S.Qt ≃ₗ[ZMod 2] S.Qt) x + (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - (x + v) =
      ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) + ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) by abel]
    refine add_mem ?_ (sub_mem (apply_mem_Vt_of_mem_Rbar H.conj_mem (Lbar_le_Rbar ht hl) hv) hv)
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr (cl_a_mem_Vt ht)
      (Lbar_apply_sub_mem_span' H.conj_mem hx.1 hl)

end Fix

end CFSG.LargeExtraspecial.S6
