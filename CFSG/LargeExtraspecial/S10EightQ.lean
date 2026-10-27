module

public import CFSG.LargeExtraspecial.S10EightP

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
theorem fix_τ₂_qf : ∀ m : M2, act τ₂ m = m → act τ₁ m ≠ m → pf E00 m = 0 → qf m = 0 := by
  decide +kernel

theorem comm_eq_mul_comm {X' : Type*} [Group X'] {A : Subgroup X'}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {z₁ y b : X'} (hy : y ∈ A)
    (hbz : b * z₁⁻¹ * b⁻¹ ∈ A) (hby : b * y * b⁻¹ ∈ A) :
    (z₁ * y⁻¹) * b * (z₁ * y⁻¹)⁻¹ * b⁻¹ =
      (z₁ * b * z₁⁻¹ * b⁻¹) * (y⁻¹ * b * y * b⁻¹) := by
  have e1 : (z₁ * y⁻¹) * b * (z₁ * y⁻¹)⁻¹ * b⁻¹ =
      z₁ * y⁻¹ * (b * y * b⁻¹) * (b * z₁⁻¹ * b⁻¹) := by group
  have e2 : (z₁ * b * z₁⁻¹ * b⁻¹) * (y⁻¹ * b * y * b⁻¹) =
      z₁ * (b * z₁⁻¹ * b⁻¹) * (y⁻¹ * (b * y * b⁻¹)) := by group
  rw [e1, e2]
  have h1 : y⁻¹ * (b * y * b⁻¹) ∈ A := mul_mem (inv_mem hy) hby
  have h2 := hA _ h1 _ hbz
  calc z₁ * y⁻¹ * (b * y * b⁻¹) * (b * z₁⁻¹ * b⁻¹) =
        z₁ * ((y⁻¹ * (b * y * b⁻¹)) * (b * z₁⁻¹ * b⁻¹)) := by group
    _ = z₁ * ((b * z₁⁻¹ * b⁻¹) * (y⁻¹ * (b * y * b⁻¹))) := by rw [h2]
    _ = z₁ * (b * z₁⁻¹ * b⁻¹) * (y⁻¹ * (b * y * b⁻¹)) := by group

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

variable {k : S.M}

theorem false_of_fix_y (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) (h7 : 7 ≤ S.width)
    (hinf : (S.Lbar g ⊓ Xb) ⊓ (S.Lbar g ⊓ Xb).map (cK S k) = ⊥)
    (hkP : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hk1 : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹))
    {σ : S.O} (hσE : σ ∈ S.Lbar g ⊓ Xb)
    (hσf : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) (hσ1 : σ ≠ 1) (Y : Hyp10 S g σ)
    {Xσ : Subgroup S.O} (hEσ : S.Lbar g ⊓ Xσ = S.Lbar g ⊓ Xb) (F : Frame Y)
    (hFX : Xσ = F.pre Γ₁) {y : S.O} (hyL : y ∈ S.Lbar g)
    (hπy : F.π ⟨y, Lbar_le_Rbar Y.ht hyL⟩ = τ₂)
    (hyf : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹))
    {x₀ : S.O} (hx₀ : x₀ ∈ S.Lbar g ⊓ Xb)
    (hx₀f : (x₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) ≠
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) : False := by
  have hfV := D.mem_Vt_sigma hCE hP h7 hinf hkP hk1 hσE hσf Y
  set fv' : Vt S g σ := ⟨_, hfV⟩ with hfv'
  have hx₀N : x₀ ∉ Nbar S g σ := fun h =>
    hx₀f (D.Abar_fix hCE hP h7 hinf hkP hk1 hσE hσf Y x₀ ⟨hx₀.1, h⟩)
  have hx₀R := Lbar_le_Rbar Y.ht hx₀.1
  have hx₀X : x₀ ∈ Xσ := by
    have : x₀ ∈ S.Lbar g ⊓ Xσ := by rw [hEσ]; exact hx₀
    exact this.2
  have hπx₀ : F.π ⟨x₀, hx₀R⟩ = τ₁ := by
    have h1 := hx₀X
    rw [hFX] at h1
    obtain ⟨hR', h2⟩ := (F.mem_pre).mp h1
    exact eq_τ₁_of_stab_Γ₁ _ (F.π_mem_stabA hx₀.1) (mem_Γ₁.mp h2)
      fun h => hx₀N ((F.ker _).mp h)
  have hτ₂ : act τ₂ (F.φ fv') = F.φ fv' := by
    have h1 := F.compat ⟨y, Lbar_le_Rbar Y.ht hyL⟩ fv'
    have h2 : resV Y.haQ σ ⟨y, Lbar_le_Rbar Y.ht hyL⟩ fv' = fv' :=
      Subtype.ext (by rw [coe_resV_apply]; exact hyf)
    rw [h2, hπy] at h1
    exact h1.symm
  have hτ₁ : act τ₁ (F.φ fv') ≠ F.φ fv' := by
    intro h
    have h1 := F.compat ⟨x₀, hx₀R⟩ fv'
    rw [hπx₀, h] at h1
    have h2 := congrArg Subtype.val (F.φ.injective h1)
    rw [coe_resV_apply] at h2
    exact hx₀f h2
  have hpf : pf E00 (F.φ fv') = 0 := by
    rw [← F.base, ← F.beta_eq]
    exact (beta_aV_eq_zero_iff Y.H Y.C Y.ht Y.ht1 Y.hVQ fv').mpr hkP
  have hq := fix_τ₂_qf _ hτ₂ hτ₁ hpf
  have hne : fv' ≠ 0 := fun h => cl_conj_z_ne_zero S (conj_mem_QG' S k.2 X.haQ)
    (conj_ne_z' S k.2 X.H.conj_ne) (congrArg Subtype.val h)
  obtain ⟨e, ⟨r, hrR, hre⟩, hea⟩ := (F.sing fv' hne).mpr hq
  obtain ⟨kr, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hrR)
  have hra : S.cl ((kr : G) * g * S.z * ((kr : G) * g)⁻¹) =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
    rw [← ρ_cl_conj_z S kr X.haQ]
    have h1 := hre (aV Y.ht)
    rw [hea] at h1
    exact h1.symm
  have hL : S.Lbar ((kr : G) * g) = S.Lbar ((k : G) * g) :=
    Lbar_eq_of_cl_eq S (conj_mem_QG' S k.2 X.haQ) (conj_ne_z' S k.2 X.H.conj_ne)
      (conj_mem_QG' S kr.2 X.haQ) hra
  have hFeq := D.map_eq_of_Lbar_eq hCE hP hL
  have hσF : σ ∈ (S.Lbar g ⊓ Xb).map (cK S k) := by
    rw [← hFeq, mem_map_cK_iff]
    have hc := commute_of_mem_Rbar Y.haQ hrR
    rw [show (S.ρ kr)⁻¹ * σ * S.ρ kr = σ by
      calc (S.ρ kr)⁻¹ * σ * S.ρ kr = (S.ρ kr)⁻¹ * (σ * S.ρ kr) := by group
        _ = (S.ρ kr)⁻¹ * (S.ρ kr * σ) := by rw [hc]
        _ = σ := by group]
    exact hσE
  have h0 : σ ∈ (S.Lbar g ⊓ Xb) ⊓ (S.Lbar g ⊓ Xb).map (cK S k) := ⟨hσE, hσF⟩
  rw [hinf, Subgroup.mem_bot] at h0
  exact hσ1 h0

theorem false_of_not_fix_y (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) (h7 : 7 ≤ S.width)
    (hinf : (S.Lbar g ⊓ Xb) ⊓ (S.Lbar g ⊓ Xb).map (cK S k) = ⊥)
    (hkP : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hk1 : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹))
    {σ : S.O} (hσE : σ ∈ S.Lbar g ⊓ Xb)
    (hσf : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) (Y : Hyp10 S g σ)
    {Xσ Yσ : Subgroup S.O} (Dσ : Dec108 Y Xσ Yσ) (hEσ : S.Lbar g ⊓ Xσ = S.Lbar g ⊓ Xb)
    {y : S.O} (hyY : y ∈ Yσ) (hyL : y ∈ S.Lbar g)
    (hyf : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) ≠
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹))
    {x₀ : S.O} (hx₀ : x₀ ∈ S.Lbar g ⊓ Xb)
    (hx₀f : (x₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) ≠
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) : False := by
  set fv := S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) with hfv
  set av := S.cl (g * S.z * g⁻¹) with hav
  have hyf' := (Lbar_apply_eq_or X.haQ hkP hyL).resolve_left hyf
  have hx₀f' := (Lbar_apply_eq_or X.haQ hkP hx₀.1).resolve_left hx₀f
  rw [← hav] at hyf' hx₀f'
  have hx₀a : (x₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) av = av :=
    S.mem_fixLbar.mp (S.cl_mem_fixLbar_self X.haQ) x₀ hx₀.1
  have hz₁L : x₀ * y ∈ S.Lbar g := mul_mem hx₀.1 hyL
  have hz₁f : ((x₀ * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) fv = fv := by
    rw [coe_mul_apply, hyf', map_add, hx₀f', hx₀a, add_assoc, add_self_zmod2, add_zero]
  obtain ⟨mz, hmz⟩ := MonoidHom.mem_range.mp (S.Lbar_le_Mbar g hz₁L)
  have hLab : ∀ a ∈ S.Lbar g, ∀ b ∈ S.Lbar g, a * b = b * a := fun a ha b hb =>
    S4.Lbar_comm S X.haQ ha hb
  have hyy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (S4.mul_self_of_mem_Lbar S X.haQ hyL)
  set B₀ := (S.Lbar g ⊓ Xb).map (cK S k) ⊓ vecFix S av with hB₀
  set P₁ := S.Lbar g ⊓ (S.Lbar g ⊓ Xb).map (cK S k) with hP₁
  set P₂ := S.Lbar g ⊓ (zpowers σ ⊔ Yσ) with hP₂
  have hmem : ∀ b : B₀, ((x₀ * y) * (b : S.O) * (x₀ * y)⁻¹ * (b : S.O)⁻¹ ∈ P₁ ∧
      y⁻¹ * (b : S.O) * y * (b : S.O)⁻¹ ∈ P₂) ∧
      x₀ * (b : S.O) * x₀⁻¹ * (b : S.O)⁻¹ = ((x₀ * y) * (b : S.O) * (x₀ * y)⁻¹ * (b : S.O)⁻¹) *
        (y⁻¹ * (b : S.O) * y * (b : S.O)⁻¹) := by
    intro b
    have hbF := (Subgroup.mem_inf.mp b.2).1
    have hba : ((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) av = av := (Subgroup.mem_inf.mp b.2).2
    obtain ⟨mb, hmb⟩ := MonoidHom.mem_range.mp
      (S.Lbar_le_Mbar _ (map_le_Lbar_mul (g := g) (Xb := Xb) k hbF))
    have hbN : S.ρ mb ∈ normalizer (S.Lbar g : Set S.O) :=
      mem_normalizer_of_fix X.H (by rw [hmb]; exact hba)
    have hbL : ∀ l ∈ S.Lbar g, (b : S.O) * l * (b : S.O)⁻¹ ∈ S.Lbar g := fun l hl => by
      rw [← hmb]
      exact (mem_normalizer_iff.mp hbN l).mp hl
    have hbσ : S.ρ mb * σ = σ * S.ρ mb := by
      rw [hmb]
      exact (D.commute_of_fix hCE hP hinf hσE hσf hbF hba).symm
    have hbi : S.ρ mb⁻¹ * σ = σ * S.ρ mb⁻¹ := inv_commute_of_commute hbσ
    have hbiE : ∀ e ∈ S.Lbar g ⊓ Xσ, S.ρ mb⁻¹ * e * (S.ρ mb⁻¹)⁻¹ ∈ S.Lbar g ⊓ Xσ := by
      intro e he
      rw [hEσ] at he ⊢
      refine D.conj_mem_of_fix hCE hP ?_ he
      rw [map_inv, hmb]
      exact inv_apply_of_apply hba
    have hbX : ∀ x ∈ Xσ, (b : S.O)⁻¹ * x * b ∈ Xσ := fun x hx => by
      have := Dσ.conj_mem_Xb_of_normalize hCE hbi hbiE hx
      rwa [map_inv, inv_inv, hmb] at this
    refine ⟨⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩, ?_⟩
    · have e1 : (x₀ * y) * (b : S.O) * (x₀ * y)⁻¹ * (b : S.O)⁻¹ =
          (x₀ * y) * ((b : S.O) * (x₀ * y)⁻¹ * (b : S.O)⁻¹) := by group
      rw [e1]
      exact mul_mem hz₁L (hbL _ (inv_mem hz₁L))
    · have h1 : S.ρ mz * (b : S.O) * (S.ρ mz)⁻¹ ∈ (S.Lbar g ⊓ Xb).map (cK S k) :=
        D.conj_mem_map_of_fix hCE hP (by rw [hmz]; exact hz₁f) hbF
      rw [hmz] at h1
      exact mul_mem h1 (inv_mem hbF)
    · have e1 : y⁻¹ * (b : S.O) * y * (b : S.O)⁻¹ = y⁻¹ * ((b : S.O) * y * (b : S.O)⁻¹) := by
        group
      rw [e1]
      exact mul_mem (inv_mem hyL) (hbL _ hyL)
    · have hby : (b : S.O) * y * (b : S.O)⁻¹ ∈ zpowers σ ⊔ Yσ := by
        refine Dσ.mem_sup_of_commute_Xb hCE (k₁ := 1) (by rw [map_one]; exact one_mem _)
          (by rw [Subgroup.coe_one, one_mul]; exact hbL _ hyL) fun x hx => ?_
        have h1 := Dσ.dec.comm _ (hbX x hx) y hyY
        calc (b : S.O) * y * (b : S.O)⁻¹ * x =
              (b : S.O) * (y * ((b : S.O)⁻¹ * x * b)) * (b : S.O)⁻¹ := by group
          _ = (b : S.O) * (((b : S.O)⁻¹ * x * b) * y) * (b : S.O)⁻¹ := by rw [h1]
          _ = x * ((b : S.O) * y * (b : S.O)⁻¹) := by group
      have e1 : y⁻¹ * (b : S.O) * y * (b : S.O)⁻¹ = y⁻¹ * ((b : S.O) * y * (b : S.O)⁻¹) := by
        group
      rw [e1]
      exact mul_mem (Subgroup.mem_sup_right (inv_mem hyY)) hby
    · have h := comm_eq_mul_comm (A := S.Lbar g) hLab hyL (hbL _ (inv_mem hz₁L)) (hbL _ hyL)
      rw [show x₀ * y * y⁻¹ = x₀ by group] at h
      exact h
  have hinj : Function.Injective fun b : B₀ =>
      ((⟨_, (hmem b).1.1⟩ : P₁), (⟨_, (hmem b).1.2⟩ : P₂)) := by
    intro b₁ b₂ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    refine D.injective_comm hCE hP h7 hinf hkP hx₀ hx₀f ?_
    have h1' : (x₀ * y) * (b₁ : S.O) * (x₀ * y)⁻¹ * (b₁ : S.O)⁻¹ =
        (x₀ * y) * (b₂ : S.O) * (x₀ * y)⁻¹ * (b₂ : S.O)⁻¹ := congrArg Subtype.val h1
    have h2' : y⁻¹ * (b₁ : S.O) * y * (b₁ : S.O)⁻¹ = y⁻¹ * (b₂ : S.O) * y * (b₂ : S.O)⁻¹ :=
      congrArg Subtype.val h2
    change x₀ * (b₁ : S.O) * x₀⁻¹ * (b₁ : S.O)⁻¹ = x₀ * (b₂ : S.O) * x₀⁻¹ * (b₂ : S.O)⁻¹
    rw [(hmem b₁).2, (hmem b₂).2, h1', h2']
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at h1
  have h2 := D.card_Lbar_inf_map_le hCE hinf
  have h3 := Dσ.card_Lbar_inf_sup_le hCE
  have h4 : 2 ^ (S.width - 3) ≤ Nat.card B₀ := D.card_B0 hCE h7 hkP hk1
  have h5 : 2 ^ 4 ≤ 2 ^ (S.width - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h6 : Nat.card P₁ * Nat.card P₂ ≤ 2 * 4 := Nat.mul_le_mul h2 h3
  omega

theorem map_commutator_eq_of_mem_clSub (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g)
    (h7 : 7 ≤ S.width)
    (hkP : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hk1 : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹)) :
    ⁅Yb, Yb⁆.map (cK S k) = ⁅Yb, Yb⁆ := by
  by_cases hinf : (S.Lbar g ⊓ Xb) ⊓ (S.Lbar g ⊓ Xb).map (cK S k) = ⊥
  · exfalso
    obtain ⟨σ, hσE, hσf, hσ1, Y⟩ := D.exists_sigma hCE h7 hkP
    obtain ⟨Xσ, Yσ, ⟨Dσ⟩, hEσ, -⟩ := D.exists_dec108_of_hyp10 hCE hσE Y
    obtain ⟨F, -, hFX, y, hyY, hyL, hπy⟩ := Dσ.exists_frame hCE
    obtain ⟨x₀, hx₀, hx₀f⟩ := D.exists_not_fix hCE hP h7 hinf
    by_cases hyf : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
        S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)
    · exact D.false_of_fix_y hCE hP h7 hinf hkP hk1 hσE hσf hσ1 Y hEσ F hFX hyL hπy hyf hx₀ hx₀f
    · exact D.false_of_not_fix_y hCE hP h7 hinf hkP hk1 hσE hσf Y Dσ hEσ hyY hyL hyf hx₀ hx₀f
  · obtain ⟨⟨τ, hτ⟩, hτ1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hinf
    have hτ1 : τ ≠ 1 := fun h => hτ1' (Subtype.ext h)
    exact D.map_commutator_eq hCE hP hτ.1 hτ1 hτ.2

theorem map_commutator_eq_of_mem_clSub_mul (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g)
    (h7 : 7 ≤ S.width) {k₀ : S.M} (hk₀ : ⁅Yb, Yb⁆.map (cK S k₀) = ⁅Yb, Yb⁆)
    (hkP : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((k₀ : G) * g))) :
    ⁅Yb, Yb⁆.map (cK S k) = ⁅Yb, Yb⁆ := by
  set m := k₀⁻¹ * k with hm
  have hcl : S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) =
      (((S.ρ k₀)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) := by
    rw [← ρ_cl_conj_z S m X.haQ, ← ρ_cl_conj_z S k X.haQ, ← coe_mul_apply, hm, map_mul,
      map_inv]
  have hmP : S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    rw [hcl]
    exact (mem_clSub_Qa_mul_iff k₀).mp hkP
  have hmY : ⁅Yb, Yb⁆.map (cK S m) = ⁅Yb, Yb⁆ := by
    by_cases hm1 : S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) = S.cl (g * S.z * g⁻¹)
    ·
      have hfix : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
          S.cl (g * S.z * g⁻¹) := by rw [ρ_cl_conj_z S m X.haQ, hm1]
      have htk : t ∈ (S.Lbar g ⊓ Xb).map (cK S m) := by
        rw [mem_map_cK_iff]
        have := D.conj_mem_of_fix hCE hP (m := m⁻¹) (by rw [map_inv]; exact inv_apply_of_apply hfix)
          (D.t_mem_Ebar hCE)
        rwa [map_inv, inv_inv] at this
      exact D.map_commutator_eq hCE hP (D.t_mem_Ebar hCE) X.ht1 htk
    · exact D.map_commutator_eq_of_mem_clSub hCE hP h7 hmP hm1
  have hk : k = k₀ * m := by rw [hm]; group
  rw [hk]
  have e : ⁅Yb, Yb⁆.map (cK S (k₀ * m)) = (⁅Yb, Yb⁆.map (cK S m)).map (cK S k₀) := by
    rw [cK, cK, cK, map_conj_map_conj, map_mul]
  rw [e, hmY, hk₀]

end Dec108

end CFSG.LargeExtraspecial.S10
