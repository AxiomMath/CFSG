module

public import CFSG.LargeExtraspecial.S10EightN
public import CFSG.LargeExtraspecial.S10FourN

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
theorem stab_inv_mul_mem_Γ₁ : ∀ γ δ : Gm, act γ E00 = E00 → act δ E00 = E00 → γ.2 ≠ 1 →
    δ.2 ≠ 1 → (γ⁻¹ * δ).2 = 1 := by
  decide +kernel

theorem perm_three_inv_eq : ∀ p q : Equiv.Perm (Fin 3), p * p = 1 → q * q = 1 →
    (p * q) * (p * q) = 1 → p = 1 ∨ q = 1 ∨ p = q := by
  decide +kernel

theorem two_mul_card_le_of_le {X : Type*} [Group X] [Finite X] {H K : Subgroup X} (hle : H ≤ K)
    {x : X} (hxK : x ∈ K) (hxH : x ∉ H) : 2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card K := Nat.card_pos
    omega
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [mul_one] at hc
    exact hxH ((Subgroup.eq_of_le_of_card_ge hle hc.le) ▸ hxK)
  rw [hc]
  have : 2 ≤ c := by omega
  nlinarith

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem mem_normalizer_of_fix (H : Hyp4 S g) {m : S.M}
    (hm : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹)) :
    S.ρ m ∈ normalizer (S.Lbar g : Set S.O) := by
  have hL : S.Lbar ((m : G) * g) = S.Lbar g :=
    Lbar_eq_of_cl_eq S H.conj_mem H.conj_ne (conj_mem_QG' S m.2 H.conj_mem)
      (by rw [← ρ_cl_conj_z S m H.conj_mem, hm])
  rw [Lbar_mul] at hL
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hL]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hL] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : S.ρ m * y * (S.ρ m)⁻¹ = S.ρ m * x * (S.ρ m)⁻¹ := hyx
    have : y = x := by
      have := congrArg (fun w => (S.ρ m)⁻¹ * w * S.ρ m) hyx'
      simpa [mul_assoc] using this
    rw [← this]
    exact hy

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem exists_sigma (hCE : CentralExtInput.{u}) (h7 : 7 ≤ S.width) {k : S.M}
    (hkP : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    ∃ σ ∈ S.Lbar g ⊓ Xb, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
        S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∧ σ ≠ 1 ∧ Hyp10 S g σ := by
  set fv := S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) with hfv
  rcases timmesfeld_10_5 hCE X (timmesfeld_10_4_self hCE X h7) with h6 | ⟨k₁, hk₁, hτA, hτt⟩
  · omega
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = S.ρ k₁ * t * (S.ρ k₁)⁻¹ := ⟨_, rfl⟩
  rw [← hτ] at hτA hτt
  have htE := D.t_mem_Ebar hCE
  have hτE : τ ∈ S.Lbar g ⊓ Xb := ⟨hτA.1, D.dec.Nbar_le hCE X hτA.2⟩
  by_cases htf : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) fv = fv
  · exact ⟨t, htE, htf, X.ht1, X⟩
  by_cases hτf : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) fv = fv
  · exact ⟨τ, hτE, hτf, (X.conj' hk₁ hτ).ht1, X.conj' hk₁ hτ⟩
  have htf' := (Lbar_apply_eq_or X.haQ hkP X.ht).resolve_left htf
  have hτf' := (Lbar_apply_eq_or X.haQ hkP hτA.1).resolve_left hτf
  obtain ⟨h, hhN, hhτ⟩ := exists_conj_eq_mul_t hCE X hk₁ hτ hτA.2 hτt
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar (Nbar_le_Rbar hhN))
  have hmL : S.ρ m ∈ normalizer (S.Lbar g : Set S.O) := by
    rw [hm]
    exact Nbar_le_normalizer X.haQ X.H.conj_ne (Lbar_mem_Dset X.ht) hhN
  have hkm : S.ρ (m * k₁) ∈ normalizer (S.Lbar g : Set S.O) := by
    rw [map_mul]
    exact mul_mem hmL hk₁
  have hτ' : τ * t = S.ρ (m * k₁) * t * (S.ρ (m * k₁))⁻¹ := by
    rw [map_mul, mul_inv_rev, hm, ← hhτ, hτ]
    group
  have hcomm : t * τ = τ * t := S4.Lbar_comm S X.haQ X.ht hτA.1
  have htt : t⁻¹ = t := by
    have := S4.mul_self_of_mem_Lbar S X.haQ X.ht
    exact inv_eq_of_mul_eq_one_right this
  refine ⟨τ * t, mul_mem hτE htE, ?_, ?_, X.conj' hkm hτ'⟩
  · rw [← hcomm, ← htt, coe_mul_apply, hτf', ← htf']
    exact inv_apply_apply_O t fv
  · intro h1
    apply hτt
    calc τ = τ * t * t⁻¹ := by group
      _ = t⁻¹ := by rw [h1, one_mul]
      _ = t := htt

variable {k : S.M}

theorem Abar_fix (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) (h7 : 7 ≤ S.width)
    (hinf : (S.Lbar g ⊓ Xb) ⊓ (S.Lbar g ⊓ Xb).map (cK S k) = ⊥)
    (hkP : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hk1 : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹))
    {σ : S.O} (hσE : σ ∈ S.Lbar g ⊓ Xb)
    (hσf : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) (Y : Hyp10 S g σ) :
    ∀ x ∈ S.Lbar g ⊓ Nbar S g σ, (x : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
        S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
  set fv := S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) with hfv
  set av := S.cl (g * S.z * g⁻¹) with hav
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁, hx₁f⟩ := hcon
  obtain ⟨Xσ, Yσ, ⟨Dσ⟩, hEσ, -⟩ := D.exists_dec108_of_hyp10 hCE hσE Y
  have hx₁E : x₁ ∈ S.Lbar g ⊓ Xb := by
    rw [← hEσ]
    exact ⟨hx₁.1, Dσ.dec.Nbar_le hCE Y hx₁.2⟩
  have hx₁f' := (Lbar_apply_eq_or X.haQ hkP hx₁.1).resolve_left hx₁f
  rw [← hav] at hx₁f'
  have hx₁a : (x₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) av = av :=
    S.mem_fixLbar.mp (S.cl_mem_fixLbar_self X.haQ) x₁ hx₁.1
  have hx₁i : ((x₁⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) fv = fv + av := by
    have e1 : (x₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (fv + av) = fv := by
      rw [map_add, hx₁f', hx₁a, add_assoc, add_self_zmod2, add_zero]
    conv_lhs => rw [← e1]
    exact inv_apply_apply_O x₁ _
  set B₀ := (S.Lbar g ⊓ Xb).map (cK S k) ⊓ vecFix S av with hB₀
  set A' := (S.Lbar g ⊓ Nbar S g σ) ⊓ vecFix S fv with hA'
  have hmem : ∀ b : B₀, x₁ * (b : S.O) * x₁⁻¹ * (b : S.O)⁻¹ ∈ A' := by
    intro b
    have hbF := (Subgroup.mem_inf.mp b.2).1
    have hba : ((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) av = av := (Subgroup.mem_inf.mp b.2).2
    have hbL := map_le_Lbar_mul (g := g) (Xb := Xb) k hbF
    have hbf : ((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) fv = fv :=
      S.mem_fixLbar.mp (S.cl_mem_fixLbar_self (conj_mem_QG' S k.2 X.haQ)) b hbL
    obtain ⟨mb, hmb⟩ := MonoidHom.mem_range.mp (S.Lbar_le_Mbar _ hbL)
    have hbσ : S.ρ mb * σ = σ * S.ρ mb := by
      rw [hmb]
      exact (D.commute_of_fix hCE hP hinf hσE hσf hbF hba).symm
    have hbN : S.ρ mb ∈ normalizer (S.Lbar g : Set S.O) :=
      mem_normalizer_of_fix X.H (by rw [hmb]; exact hba)
    have h1 : (b : S.O) * x₁⁻¹ * (b : S.O)⁻¹ ∈ S.Lbar g ⊓ Nbar S g σ := by
      rw [← hmb]
      exact ⟨(mem_normalizer_iff.mp hbN _).mp (inv_mem hx₁.1),
        conj_mem_Nbar X.haQ hbσ (inv_mem hx₁.2)⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have e1 : x₁ * (b : S.O) * x₁⁻¹ * (b : S.O)⁻¹ = x₁ * ((b : S.O) * x₁⁻¹ * (b : S.O)⁻¹) := by
        group
      rw [e1]
      exact mul_mem hx₁ h1
    · rw [mem_vecFix, coe_mul_apply, coe_mul_apply, coe_mul_apply, inv_apply_of_apply hbf,
        hx₁i, map_add, hbf, hba]
      rw [map_add, hx₁f', hx₁a, add_assoc, add_self_zmod2, add_zero]
  have hinj : Function.Injective fun b : B₀ =>
      (⟨x₁ * (b : S.O) * x₁⁻¹ * (b : S.O)⁻¹, hmem b⟩ : A') := by
    intro b₁ b₂ h
    exact D.injective_comm hCE hP h7 hinf hkP hx₁E hx₁f (congrArg Subtype.val h)
  have h1 := Nat.card_le_card_of_injective _ hinj
  have h2 : 2 ^ (S.width - 3) ≤ Nat.card B₀ := D.card_B0 hCE h7 hkP hk1
  have h3 := two_mul_card_le_of_le (H := A') (K := S.Lbar g ⊓ Nbar S g σ) inf_le_left hx₁
    (fun h => hx₁f (Subgroup.mem_inf.mp h).2)
  have h4 := Y.card_Lbar_eq
  rw [X.C.card_Lbar] at h4
  have h5 : 2 ^ (S.width - 1) = 4 * 2 ^ (S.width - 3) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have h6 : 0 < 2 ^ (S.width - 3) := by positivity
  omega

theorem mem_Vt_sigma (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) (h7 : 7 ≤ S.width)
    (hinf : (S.Lbar g ⊓ Xb) ⊓ (S.Lbar g ⊓ Xb).map (cK S k) = ⊥)
    (hkP : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hk1 : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹))
    {σ : S.O} (hσE : σ ∈ S.Lbar g ⊓ Xb)
    (hσf : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) (Y : Hyp10 S g σ) :
    S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g σ := by
  have h := (clSub_inf_fixSub_Abar Y).le
    ⟨hkP, fun x hx => D.Abar_fix hCE hP h7 hinf hkP hk1 hσE hσf Y x hx⟩
  exact h.2

theorem conj_mem_Xb_of_normalize (hCE : CentralExtInput.{u}) {m : S.M}
    (hm : S.ρ m * t = t * S.ρ m)
    (hmE : ∀ e ∈ S.Lbar g ⊓ Xb, S.ρ m * e * (S.ρ m)⁻¹ ∈ S.Lbar g ⊓ Xb) {x : S.O}
    (hx : x ∈ Xb) : S.ρ m * x * (S.ρ m)⁻¹ ∈ Xb := by
  obtain ⟨F, -, hFX, -⟩ := D.exists_frame hCE
  obtain ⟨x₀, hx₀L, hπx₀⟩ := F.exists_Lbar_of_stab
    (by rw [mem_stabA, act_E00_iff]; exact Or.inr (Or.inl rfl))
  have hx₀X : x₀ ∈ Xb := by
    rw [hFX]
    exact (F.mem_pre).mpr ⟨_, by rw [hπx₀]; exact τ₁_mem_Γ₁⟩
  have hNX := D.dec.Nbar_le hCE X
  have hle : F.pre Γ₁ ≤ Xb.comap (MulAut.conj (S.ρ m)).toMonoidHom := by
    refine F.pre_Γ₁_le_of hx₀L hπx₀ (fun n hn => ?_) (fun r hr => ?_)
    · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hNX (conj_mem_Nbar X.haQ hm hn)
    · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hrk := conj_mem_Rbar hm hr
      have hx₀k := (hmE x₀ ⟨hx₀L, hx₀X⟩).2
      have e1 : S.ρ m * (r * x₀ * r⁻¹) * (S.ρ m)⁻¹ =
          (S.ρ m * r * (S.ρ m)⁻¹) * (S.ρ m * x₀ * (S.ρ m)⁻¹) *
            (S.ρ m * r * (S.ρ m)⁻¹)⁻¹ := by group
      rw [e1, hFX]
      exact F.conj_mem_pre_Γ₁ hrk (hFX ▸ hx₀k)
  rw [hFX] at hx
  have := hle hx
  simpa using this

theorem inv_mul_mem_Xb (hCE : CentralExtInput.{u}) {a b : S.O} (ha : a ∈ S.Lbar g)
    (haX : a ∉ Xb) (hb : b ∈ S.Lbar g) (hbX : b ∉ Xb) : a⁻¹ * b ∈ Xb := by
  obtain ⟨F, -, hFX, -⟩ := D.exists_frame hCE
  have haR := Lbar_le_Rbar X.ht ha
  have hbR := Lbar_le_Rbar X.ht hb
  have ha2 : (F.π ⟨a, haR⟩).2 ≠ 1 := fun h => haX (by
    rw [hFX]
    exact (F.mem_pre).mpr ⟨haR, mem_Γ₁.mpr h⟩)
  have hb2 : (F.π ⟨b, hbR⟩).2 ≠ 1 := fun h => hbX (by
    rw [hFX]
    exact (F.mem_pre).mpr ⟨hbR, mem_Γ₁.mpr h⟩)
  have h := stab_inv_mul_mem_Γ₁ _ _ (F.π_mem_stabA ha) (F.π_mem_stabA hb) ha2 hb2
  rw [hFX]
  refine (F.mem_pre).mpr ⟨mul_mem (inv_mem haR) hbR, mem_Γ₁.mpr ?_⟩
  have e : (⟨a⁻¹ * b, mul_mem (inv_mem haR) hbR⟩ : Rbar S g t) =
      (⟨a, haR⟩ : Rbar S g t)⁻¹ * ⟨b, hbR⟩ := Subtype.ext (by simp)
  rw [e, map_mul, map_inv]
  exact h

theorem card_Lbar_inf_map_le (hCE : CentralExtInput.{u})
    (hinf : (S.Lbar g ⊓ Xb) ⊓ (S.Lbar g ⊓ Xb).map (cK S k) = ⊥) :
    Nat.card (S.Lbar g ⊓ (S.Lbar g ⊓ Xb).map (cK S k) : Subgroup S.O) ≤ 2 := by
  have hX : ∀ a ∈ S.Lbar g ⊓ (S.Lbar g ⊓ Xb).map (cK S k), a ∈ Xb → a = 1 := by
    intro a ha haX
    have h0 : a ∈ (S.Lbar g ⊓ Xb) ⊓ (S.Lbar g ⊓ Xb).map (cK S k) :=
      ⟨⟨ha.1, haX⟩, ha.2⟩
    rw [hinf, Subgroup.mem_bot] at h0
    exact h0
  have h := card_le_two_mul_of_mem (H := ⊥)
    (K := S.Lbar g ⊓ (S.Lbar g ⊓ Xb).map (cK S k)) fun a ha ha1 b hb hb1 => by
      have haX : a ∉ Xb := fun h => ha1 ((Subgroup.mem_bot).mpr (hX a ha h))
      have hbX : b ∉ Xb := fun h => hb1 ((Subgroup.mem_bot).mpr (hX b hb h))
      exact (Subgroup.mem_bot).mpr (hX _ (mul_mem (inv_mem ha) hb)
        (D.inv_mul_mem_Xb hCE ha.1 haX hb.1 hbX))
  rw [Subgroup.card_bot] at h
  omega

theorem card_Lbar_inf_sup_le (hCE : CentralExtInput.{u}) :
    Nat.card (S.Lbar g ⊓ (zpowers t ⊔ Yb) : Subgroup S.O) ≤ 4 := by
  have htX : t ∈ Xb := (D.t_mem_Ebar hCE).2
  have hcomm : ∀ a ∈ zpowers t, ∀ b ∈ Yb, a * b = b * a := by
    intro a ha b hb
    rcases mem_zpowers_of_orderOf_two X.orderOf_t ha with rfl | rfl
    · simp
    · exact D.dec.comm _ htX b hb
  have h1 := card_le_two_mul_of_mem (H := (S.Lbar g ⊓ (zpowers t ⊔ Yb)) ⊓ Yb)
    (K := S.Lbar g ⊓ (zpowers t ⊔ Yb)) fun a ha haH b hb hbH => by
      have haY : a ∉ Yb := fun h => haH ⟨ha, h⟩
      have hbY : b ∉ Yb := fun h => hbH ⟨hb, h⟩
      obtain ⟨s₁, hs₁, y₁, hy₁, rfl⟩ :=
        exists_mul_of_mem_sup_of_commute (A := zpowers t) (B := Yb) hcomm ha.2
      obtain ⟨s₂, hs₂, y₂, hy₂, rfl⟩ :=
        exists_mul_of_mem_sup_of_commute (A := zpowers t) (B := Yb) hcomm hb.2
      have hs₁t : s₁ = t := by
        rcases mem_zpowers_of_orderOf_two X.orderOf_t hs₁ with rfl | h
        · exact absurd (by simpa using hy₁) haY
        · exact h
      have hs₂t : s₂ = t := by
        rcases mem_zpowers_of_orderOf_two X.orderOf_t hs₂ with rfl | h
        · exact absurd (by simpa using hy₂) hbY
        · exact h
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem ha) hb, ?_⟩
      have e : (s₁ * y₁)⁻¹ * (s₂ * y₂) = y₁⁻¹ * y₂ := by rw [hs₁t, hs₂t]; group
      rw [e]
      exact mul_mem (inv_mem hy₁) hy₂
  obtain ⟨e⟩ := D.dec.iso
  have h2 := card_le_two_mul_of_mem (H := ⊥)
    (K := (S.Lbar g ⊓ (zpowers t ⊔ Yb)) ⊓ Yb) fun a ha ha1 b hb hb1 => by
      have haa : a * a = 1 := S4.mul_self_of_mem_Lbar S X.haQ ha.1.1
      have hbb : b * b = 1 := S4.mul_self_of_mem_Lbar S X.haQ hb.1.1
      have hab : (a * b) * (a * b) = 1 :=
        S4.mul_self_of_mem_Lbar S X.haQ (mul_mem ha.1.1 hb.1.1)
      have he := perm_three_inv_eq (e ⟨a, ha.2⟩) (e ⟨b, hb.2⟩)
        (by rw [← map_mul, show (⟨a, ha.2⟩ : Yb) * ⟨a, ha.2⟩ = 1 from Subtype.ext haa, map_one])
        (by rw [← map_mul, show (⟨b, hb.2⟩ : Yb) * ⟨b, hb.2⟩ = 1 from Subtype.ext hbb, map_one])
        (by
          rw [← map_mul, ← map_mul, show (⟨a, ha.2⟩ : Yb) * ⟨b, hb.2⟩ * (⟨a, ha.2⟩ * ⟨b, hb.2⟩) = 1
            from Subtype.ext hab, map_one])
      rcases he with h | h | h
      · exact absurd ((Subgroup.mem_bot).mpr (congrArg Subtype.val
          (e.injective (h.trans (map_one e).symm)))) ha1
      · exact absurd ((Subgroup.mem_bot).mpr (congrArg Subtype.val
          (e.injective (h.trans (map_one e).symm)))) hb1
      · have hab' : a = b := congrArg Subtype.val (e.injective h)
        rw [hab', inv_mul_cancel]
        exact one_mem _
  rw [Subgroup.card_bot] at h2
  omega

end Dec108

end CFSG.LargeExtraspecial.S10
