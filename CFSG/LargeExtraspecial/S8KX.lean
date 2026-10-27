module

public import CFSG.LargeExtraspecial.S8KW
public import CFSG.LargeExtraspecial.S8KB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem tauBil_eq_zero_of_mem {τ : S.O} {k y : S.Qt}
    (hk : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) k - k ∈ Vt S g t) (hy : y ∈ Wt S g t) :
    tauBil S τ k y = 0 := by
  rw [tauBil_apply]
  exact mem_Wt.mp hy _ hk

namespace Bad3

variable {D : Std H C ht ht1 hVQ} {τ : S.O} (B : Bad3 D τ)
include B

theorem exists_pair : ∃ w₁ ∈ S.clSub (S.QG ⊓ S.Qa ((D.h : G) * g)) ⊓ Wt S g t,
    ∃ w₂ ∈ S.clSub (S.QG ⊓ S.Qa ((D.h : G) * g)) ⊓ Wt S g t,
      ∀ z ∈ S.clSub (S.QG ⊓ S.Qa ((D.h : G) * g)) ⊓ Wt S g t, ∃ a b : ZMod 2,
        (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) (z - (a • w₁ + b • w₂)) - (z - (a • w₁ + b • w₂)) ∈
          Vt S g t := by
  have e3 := B.finrank_U
  have e4 := B.finrank_U_inf
  have hmeet := sup_Vt_inf_sup_Vt H C ht ht1 hVQ D.hh D.hb D.hPab
  set U := (Wt S g t).map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t with hU
  set Xa := S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ⊔ Vt S g t with hXa
  set Pb := S.clSub (S.QG ⊓ S.Qa ((D.h : G) * g)) ⊓ Wt S g t with hPb
  set Xb := Pb ⊔ Vt S g t with hXb
  set T : S.Qt →ₗ[ZMod 2] S.Qt ⧸ Vt S g t :=
    (Vt S g t).mkQ ∘ₗ ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) with hT
  have hle : Pb.map T ≤ (U ⊓ Xb).map (Vt S g t).mkQ := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) z, ⟨?_, ?_⟩, rfl⟩
    · exact Submodule.mem_sup_left ⟨z, hz.2, rfl⟩
    · refine Submodule.mem_sup_left ⟨?_, ?_⟩
      · exact sub_mem (B.apply_mem_clSub_b hz.1) hz.1
      · exact sub_mem (apply_mem_Wt_of_commute H C ht ht1 hVQ B.τt hz.2) hz.2
  have hdisj : (U ⊓ Xa).map (Vt S g t).mkQ ⊓ (U ⊓ Xb).map (Vt S g t).mkQ = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨⟨y₁, hy₁, rfl⟩, ⟨y₂, hy₂, hy⟩⟩ := hx
    rw [Submodule.mem_bot]
    have hd : y₁ - y₂ ∈ Vt S g t := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      change (Vt S g t).mkQ y₁ - (Vt S g t).mkQ y₂ = 0
      rw [hy, sub_self]
    have hy₁b : y₁ ∈ Xb := by
      have h1 := Xb.add_mem hy₂.2 ((le_sup_right : Vt S g t ≤ Xb) hd)
      have e : y₂ + (y₁ - y₂) = y₁ := by abel
      rwa [e] at h1
    have hy₁V : y₁ ∈ Vt S g t := by
      rw [← hmeet]
      exact ⟨hy₁.2, hy₁b⟩
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hy₁V
  have hsupU : (U ⊓ Xa).map (Vt S g t).mkQ ⊔ (U ⊓ Xb).map (Vt S g t).mkQ ≤
      U.map (Vt S g t).mkQ :=
    sup_le (Submodule.map_mono inf_le_left) (Submodule.map_mono inf_le_left)
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq ((U ⊓ Xa).map (Vt S g t).mkQ)
    ((U ⊓ Xb).map (Vt S g t).mkQ)
  rw [hdisj, finrank_bot, add_zero] at e1
  have e2 := Submodule.finrank_mono hsupU
  have e5 := Submodule.finrank_mono hle
  have hI2 : finrank (ZMod 2) (Pb.map T) ≤ 2 := by omega
  obtain ⟨u₁, hu₁, u₂, hu₂, hspan⟩ := exists_pair_of_finrank_le_two hI2
  obtain ⟨w₁, hw₁, rfl⟩ := hu₁
  obtain ⟨w₂, hw₂, rfl⟩ := hu₂
  refine ⟨w₁, hw₁, w₂, hw₂, fun z hz => ?_⟩
  obtain ⟨a, b, hab⟩ := hspan (T z) ⟨z, hz, rfl⟩
  refine ⟨a, b, ?_⟩
  have h0 : T (z - (a • w₁ + b • w₂)) = 0 := by
    rw [map_sub, map_add, map_smul, map_smul, hab, sub_self]
  rw [hT, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  simpa only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply] using h0

theorem false : False := by
  have haQ := H.conj_mem
  obtain ⟨w₁, hw₁, w₂, hw₂, hspan⟩ := B.exists_pair
  let F : S.Lbar g →* Multiplicative (ZMod 2 × ZMod 2 × ZMod 2) :=
    { toFun := fun l => Multiplicative.ofAdd
        (tauBil S τ ((((l : S.Lbar g) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁ - w₁) w₁,
          tauBil S τ ((((l : S.Lbar g) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁ - w₁) w₂,
          tauBil S τ ((((l : S.Lbar g) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂) w₂)
      map_one' := by
        have e : ∀ w : S.Qt, ((((1 : S.Lbar g) : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w = 0 :=
          fun w => sub_eq_zero.mpr rfl
        simp only [e, map_zero, LinearMap.zero_apply]
        rfl
      map_mul' := fun l l' => by
        have e : ∀ w : S.Qt, ((((l * l' : S.Lbar g)) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
            (((l : S.O) * (l' : S.O) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w := fun w => rfl
        rw [e, e]
        rw [B.tauBil_comm_mul l.2 l'.2 hw₁.2, B.tauBil_comm_mul l.2 l'.2 hw₁.2,
          B.tauBil_comm_mul l.2 l'.2 hw₂.2]
        rfl }
  have hker : F.ker ≤ (S.Lbar g ⊓ Nbar S g t).subgroupOf (S.Lbar g) := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h3 := congrArg Multiplicative.toAdd hl
    simp only [F, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, toAdd_one,
      Prod.mk_eq_zero] at h3
    obtain ⟨h11, h12, h22⟩ := h3
    have hlL : ((l : S.Lbar g) : S.O) ∈ S.Lbar g := l.2
    have h21 : tauBil S τ ((((l : S.Lbar g) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂) w₁ = 0 := by
      rw [← B.tauBil_comm_symm hlL hw₁.2 hw₂.2]
      exact h12
    have hall : ∀ z₁ ∈ S.clSub (S.QG ⊓ S.Qa ((D.h : G) * g)) ⊓ Wt S g t,
        ∀ z₂ ∈ S.clSub (S.QG ⊓ S.Qa ((D.h : G) * g)) ⊓ Wt S g t,
          tauBil S τ ((((l : S.Lbar g) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) z₁ - z₁) z₂ = 0 := by
      intro z₁ hz₁ z₂ hz₂
      obtain ⟨a₁, b₁, hk₁⟩ := hspan z₁ hz₁
      obtain ⟨a₂, b₂, hk₂⟩ := hspan z₂ hz₂
      obtain ⟨k₁, hk₁def⟩ : ∃ k, k = z₁ - (a₁ • w₁ + b₁ • w₂) := ⟨_, rfl⟩
      obtain ⟨k₂, hk₂def⟩ : ∃ k, k = z₂ - (a₂ • w₁ + b₂ • w₂) := ⟨_, rfl⟩
      rw [← hk₁def] at hk₁
      rw [← hk₂def] at hk₂
      have hk₁W : k₁ ∈ Wt S g t := by
        rw [hk₁def]
        exact sub_mem hz₁.2 (add_mem (Submodule.smul_mem _ _ hw₁.2)
          (Submodule.smul_mem _ _ hw₂.2))
      have hk₂W : k₂ ∈ Wt S g t := by
        rw [hk₂def]
        exact sub_mem hz₂.2 (add_mem (Submodule.smul_mem _ _ hw₁.2)
          (Submodule.smul_mem _ _ hw₂.2))
      have ez₁ : z₁ = a₁ • w₁ + b₁ • w₂ + k₁ := by rw [hk₁def]; abel
      have ez₂ : z₂ = a₂ • w₁ + b₂ • w₂ + k₂ := by rw [hk₂def]; abel
      have n₁ : ∀ x ∈ Wt S g t,
          tauBil S τ ((((l : S.Lbar g) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) k₁ - k₁) x = 0 := by
        intro x hx
        rw [B.tauBil_comm_symm hlL hk₁W hx, B.tauBil_symm]
        exact tauBil_eq_zero_of_mem hk₁ (sub_mem (apply_mem_Wt H (Lbar_le_Rbar ht hlL) hx) hx)
      have n₂ : ∀ x ∈ Wt S g t, tauBil S τ x k₂ = 0 := fun x hx => by
        rw [B.tauBil_symm]
        exact tauBil_eq_zero_of_mem hk₂ hx
      have hX₁ : (((l : S.Lbar g) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁ - w₁ ∈ Wt S g t :=
        sub_mem (apply_mem_Wt H (Lbar_le_Rbar ht hlL) hw₁.2) hw₁.2
      have hX₂ : (((l : S.Lbar g) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂ ∈ Wt S g t :=
        sub_mem (apply_mem_Wt H (Lbar_le_Rbar ht hlL) hw₂.2) hw₂.2
      have eL : (((l : S.Lbar g) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (a₁ • w₁ + b₁ • w₂ + k₁) -
          (a₁ • w₁ + b₁ • w₂ + k₁) =
          a₁ • ((((l : S.Lbar g) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁ - w₁) +
            b₁ • ((((l : S.Lbar g) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂) +
              ((((l : S.Lbar g) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) k₁ - k₁) := by
        simp only [map_add, map_smul, smul_sub]
        abel
      rw [ez₁, eL, ez₂]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        h11, h12, h21, h22, n₁ _ hw₁.2, n₁ _ hw₂.2, n₁ _ hk₂W, n₂ _ hX₁, n₂ _ hX₂, mul_zero,
        add_zero]
    rw [mem_subgroupOf]
    refine ⟨hlL, ?_⟩
    exact mem_Nbar_of_forall_apply_sub_mem B.hΩ D B.six_le B.U_le_Wt B.U_invariant
      B.not_forall_apply_sub_mem (Lbar_le_Rbar ht hlL)
      (fun u hu => B.apply_sub_mem_Vt_of_forall hlL hall hu)
  have hcard := Subgroup.card_ker_mul_card_range F
  have hr : Nat.card F.range ≤ 8 := by
    calc Nat.card F.range ≤ Nat.card (Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)) :=
          Subgroup.card_le_card_group _
      _ = 8 := by
          rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  have hk : Nat.card F.ker ≤ Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
    calc Nat.card F.ker ≤ Nat.card ((S.Lbar g ⊓ Nbar S g t).subgroupOf (S.Lbar g)) :=
          Subgroup.card_le_of_le hker
      _ = Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) :=
          Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hL := card_Lbar_eq_mul haQ ht
  have hLN := card_LmodN_of_omegaCase H C ht ht1 hVQ B.hΩ
  rw [D.hdim, B.hm3] at hLN
  norm_num at hLN
  have hpos : 0 < Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := Nat.card_pos
  have hle := Nat.mul_le_mul hk hr
  rw [hcard, hL, hLN] at hle
  omega

end Bad3

theorem timmesfeld83PlusGlobal3 : Timmesfeld83PlusGlobal3.{u} := by
  intro G _ _ S g hCE _ H hNo C t ht ht1 hVQ hΩ D hm3 _ hA7 hn hsub x hxM hxt
  by_contra hN
  have hτM : x * t * x⁻¹ ∈ S.Mbar :=
    mul_mem (mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  exact Bad3.false (D := D) ⟨hCE, hNo, hΩ, hm3, hA7, hn, hsub, ⟨hτM, hxt, x, hxM, rfl⟩, hN⟩

end CFSG.LargeExtraspecial.S8
