module

public import CFSG.LargeExtraspecial.S8KC
public import CFSG.LargeExtraspecial.S8KB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

theorem closure_comm_and_sq {X : Type*} [Group X] {s : Set X}
    (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) (hsq : ∀ a ∈ s, a * a = 1) :
    ∀ a ∈ closure s, ∀ b ∈ closure s, a * b = b * a ∧ a * a = 1 := by
  have h1 : ∀ a ∈ closure s, ∀ b ∈ s, a * b = b * a := by
    intro a ha b hb
    induction ha using closure_induction with
    | mem x hx => exact hcomm x hx b hb
    | one => simp
    | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
    | inv x _ hx =>
      calc x⁻¹ * b = x⁻¹ * (b * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * b) * x⁻¹ := by rw [hx]
        _ = b * x⁻¹ := by group
  have h2 : ∀ a ∈ closure s, ∀ b ∈ closure s, a * b = b * a := by
    intro a ha b hb
    induction hb using closure_induction with
    | mem y hy => exact h1 a ha y hy
    | one => simp
    | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
    | inv x _ hx =>
      calc a * x⁻¹ = x⁻¹ * (x * a) * x⁻¹ := by group
        _ = x⁻¹ * (a * x) * x⁻¹ := by rw [hx]
        _ = x⁻¹ * a := by group
  intro a ha b hb
  refine ⟨h2 a ha b hb, ?_⟩
  induction ha using closure_induction with
  | mem x hx => exact hsq x hx
  | one => simp
  | mul x y hxs hys hx hy =>
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [h2 y hys x hxs]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx, hy, one_mul]
  | inv x _ hx =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [hx, inv_one]

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S g) in
@[expose] noncomputable def N1bar (t τ : S.O) : Subgroup S.O :=
  closure (insert t {c | ∃ n ∈ Nbar S g t, c = n * τ * n⁻¹ * τ⁻¹})

theorem t_mem_N1bar {t τ : S.O} : t ∈ N1bar S g t τ :=
  subset_closure (Set.mem_insert t _)

theorem comm_mem_N1bar {t τ n : S.O} (hn : n ∈ Nbar S g t) :
    n * τ * n⁻¹ * τ⁻¹ ∈ N1bar S g t τ :=
  subset_closure (Set.mem_insert_of_mem t ⟨n, hn, rfl⟩)

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem comm_Nbar_mem_and_sq_and_commute (D : Std H C ht ht1 hVQ) (hm3 : 3 ≤ D.m)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    {n : S.O} (hn : n ∈ Nbar S g t) :
    n * τ * n⁻¹ * τ⁻¹ ∈ Nbar S g t ∧ (n * τ * n⁻¹ * τ⁻¹) * (n * τ * n⁻¹ * τ⁻¹) = 1 ∧
      (n * τ * n⁻¹ * τ⁻¹) * τ = τ * (n * τ * n⁻¹ * τ⁻¹) := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hτM : τ ∈ S.Mbar := by
    rw [hxτ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hττ : τ * τ = 1 := by
    rw [hxτ]
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hτM
  have hconj : ∀ y ∈ Nbar S g t, τ * y * τ⁻¹ ∈ Nbar S g t := fun y hy => by
    have := conj_mem_Nbar haQ (k := k) (by rw [hk]; exact hτt) hy
    rwa [hk] at this
  obtain ⟨c, hc⟩ : ∃ c, c = n * τ * n⁻¹ * τ⁻¹ := ⟨_, rfl⟩
  rw [← hc]
  have hcN : c ∈ Nbar S g t := by
    rw [hc, show n * τ * n⁻¹ * τ⁻¹ = n * (τ * n⁻¹ * τ⁻¹) by group]
    exact mul_mem hn (hconj _ (inv_mem hn))
  have hcτ : τ * c * τ⁻¹ = c⁻¹ := by
    rw [hc, hτi]
    calc τ * (n * τ * n⁻¹ * τ) * τ = τ * n * τ * n⁻¹ * (τ * τ) := by group
      _ = (n * τ * n⁻¹ * τ)⁻¹ := by
        rw [hττ, mul_one, show (n * τ * n⁻¹ * τ)⁻¹ = τ⁻¹ * n * τ⁻¹ * n⁻¹ by group, hτi]
  have hcomm : c * τ * c⁻¹ * τ⁻¹ = c * c := by
    calc c * τ * c⁻¹ * τ⁻¹ = c * (τ * c * τ⁻¹)⁻¹ := by group
      _ = c * c := by rw [hcτ, inv_inv]
  have hsq : c * c = 1 := by
    rcases eq_one_or_eq_of_mem_zpowers htt (D.hNsq c hcN) with h | h
    · exact h
    · exfalso
      apply conj_ne_mul_of_not_mem_Nbar D hm3 hfus hsub hxM hxτ hτV hτN c
      calc c * τ * c⁻¹ = (c * τ * c⁻¹ * τ⁻¹) * τ := by group
        _ = t * τ := by rw [hcomm, h]
  refine ⟨hcN, hsq, ?_⟩
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hsq
  have h1 : τ * c * τ⁻¹ = c := by rw [hcτ, hci]
  calc c * τ = (τ * c * τ⁻¹) * τ := by rw [h1]
    _ = τ * c := by group

theorem comm_Nbar_commute (D : Std H C ht ht1 hVQ) (hm3 : 3 ≤ D.m)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    {n₁ n₂ : S.O} (hn₁ : n₁ ∈ Nbar S g t) (hn₂ : n₂ ∈ Nbar S g t) :
    (n₁ * τ * n₁⁻¹ * τ⁻¹) * (n₂ * τ * n₂⁻¹ * τ⁻¹) =
      (n₂ * τ * n₂⁻¹ * τ⁻¹) * (n₁ * τ * n₁⁻¹ * τ⁻¹) := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  obtain ⟨hνN, -, hντ⟩ :=
    comm_Nbar_mem_and_sq_and_commute D hm3 hfus hsub hxM hxτ hτt hτV hτN hn₁
  obtain ⟨ν, hν⟩ : ∃ ν, ν = n₁ * τ * n₁⁻¹ * τ⁻¹ := ⟨_, rfl⟩
  rw [← hν] at hνN hντ ⊢
  have htn : t * n₂ = n₂ * t := (commute_of_mem_Rbar haQ (Nbar_le_Rbar hn₂)).symm
  obtain ⟨z, hzdef⟩ : ∃ z, z = ν * n₂ * ν⁻¹ * n₂⁻¹ := ⟨_, rfl⟩
  have hz : z ∈ zpowers t := by rw [hzdef]; exact D.hNc ν hνN n₂ hn₂
  have hν2 : ν * (n₂ * τ * n₂⁻¹) = (n₂ * τ * n₂⁻¹) * ν := by
    have e2 : ν⁻¹ * τ * ν = τ := by
      calc ν⁻¹ * τ * ν = ν⁻¹ * (τ * ν) := by group
        _ = ν⁻¹ * (ν * τ) := by rw [hντ]
        _ = τ := by group
    have key : ν * (n₂ * τ * n₂⁻¹) * ν⁻¹ = z * (n₂ * τ * n₂⁻¹) * z⁻¹ := by
      calc ν * (n₂ * τ * n₂⁻¹) * ν⁻¹ = ν * n₂ * (ν⁻¹ * τ * ν) * n₂⁻¹ * ν⁻¹ := by
            rw [e2]; group
        _ = z * (n₂ * τ * n₂⁻¹) * z⁻¹ := by rw [hzdef]; group
    have key2 : z * (n₂ * τ * n₂⁻¹) * z⁻¹ = n₂ * τ * n₂⁻¹ := by
      rcases eq_one_or_eq_of_mem_zpowers htt hz with h | h
      · rw [h]; group
      · rw [h]
        calc t * (n₂ * τ * n₂⁻¹) * t⁻¹ = (t * n₂) * τ * (t * n₂)⁻¹ := by group
          _ = (n₂ * t) * τ * (n₂ * t)⁻¹ := by rw [htn]
          _ = n₂ * (t * τ * t⁻¹) * n₂⁻¹ := by group
          _ = n₂ * τ * n₂⁻¹ := by rw [← hτt, mul_inv_cancel_right]
    calc ν * (n₂ * τ * n₂⁻¹) = ν * (n₂ * τ * n₂⁻¹) * ν⁻¹ * ν := by group
      _ = (n₂ * τ * n₂⁻¹) * ν := by rw [key, key2]
  have hνi : ν * τ⁻¹ = τ⁻¹ * ν := by
    calc ν * τ⁻¹ = τ⁻¹ * (τ * ν) * τ⁻¹ := by group
      _ = τ⁻¹ * (ν * τ) * τ⁻¹ := by rw [hντ]
      _ = τ⁻¹ * ν := by group
  calc ν * (n₂ * τ * n₂⁻¹ * τ⁻¹) = (ν * (n₂ * τ * n₂⁻¹)) * τ⁻¹ := by group
    _ = (n₂ * τ * n₂⁻¹) * (ν * τ⁻¹) := by rw [hν2]; group
    _ = (n₂ * τ * n₂⁻¹ * τ⁻¹) * ν := by rw [hνi]; group

theorem N1bar_elemAbelian (D : Std H C ht ht1 hVQ) (hm3 : 3 ≤ D.m)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t) :
    N1bar S g t τ ≤ Nbar S g t ∧
      (∀ a ∈ N1bar S g t τ, ∀ b ∈ N1bar S g t τ, a * b = b * a ∧ a * a = 1) ∧
      ∀ a ∈ N1bar S g t τ, a * τ = τ * a := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have htN := self_mem_Nbar H ht
  have hgen := fun {n} (hn : n ∈ Nbar S g t) =>
    comm_Nbar_mem_and_sq_and_commute D hm3 hfus hsub hxM hxτ hτt hτV hτN hn
  have hsN : insert t {c | ∃ n ∈ Nbar S g t, c = n * τ * n⁻¹ * τ⁻¹} ⊆ Nbar S g t := by
    intro c hc
    rcases hc with hc | ⟨n, hn, hc⟩ <;> rw [hc]
    · exact htN
    · exact (hgen hn).1
  have hscomm : ∀ a ∈ insert t {c | ∃ n ∈ Nbar S g t, c = n * τ * n⁻¹ * τ⁻¹},
      ∀ b ∈ insert t {c | ∃ n ∈ Nbar S g t, c = n * τ * n⁻¹ * τ⁻¹}, a * b = b * a := by
    intro a ha b hb
    rcases ha with ha | ⟨n₁, hn₁, ha⟩ <;> rcases hb with hb | ⟨n₂, hn₂, hb⟩ <;> rw [ha, hb]
    · exact (commute_of_mem_Rbar haQ (Nbar_le_Rbar (hgen hn₂).1)).symm
    · exact commute_of_mem_Rbar haQ (Nbar_le_Rbar (hgen hn₁).1)
    · exact comm_Nbar_commute D hm3 hfus hsub hxM hxτ hτt hτV hτN hn₁ hn₂
  have hssq : ∀ a ∈ insert t {c | ∃ n ∈ Nbar S g t, c = n * τ * n⁻¹ * τ⁻¹}, a * a = 1 := by
    intro a ha
    rcases ha with ha | ⟨n, hn, ha⟩ <;> rw [ha]
    · exact htt
    · exact (hgen hn).2.1
  refine ⟨(closure_le _).mpr hsN, closure_comm_and_sq hscomm hssq, ?_⟩
  have hτc : closure (insert t {c | ∃ n ∈ Nbar S g t, c = n * τ * n⁻¹ * τ⁻¹}) ≤
      centralizer ({τ} : Set S.O) := by
    rw [closure_le]
    intro c hc
    rcases hc with hc | ⟨n, hn, hc⟩ <;> rw [hc]
    · exact mem_centralizer_singleton_iff.mpr hτt.symm
    · exact mem_centralizer_singleton_iff.mpr (hgen hn).2.2
  intro a ha
  exact mem_centralizer_singleton_iff.mp (hτc ha)

theorem fix_of_mem_N1bar (D : Std H C ht ht1 hVQ) {τ : S.O}
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) {w : S.Qt} (hw : w ∈ Wt S g t)
    (hτw : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) {ν : S.O} (hν : ν ∈ N1bar S g t τ) :
    (ν : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  have hfix : w ∈ fixSub S (N1bar S g t τ) := by
    rw [N1bar, mem_fixSub_closure]
    intro c hc
    rcases hc with hc | ⟨n, hn, hc⟩ <;> rw [hc]
    · have hW := (commSpace_t_eq H C ht ht1 hVQ).2
      rw [← hW] at hw
      exact mem_fixSpace.mp hw
    · have hτi : ((τ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
        conv_lhs => rw [← hτw]
        exact inv_apply_apply_O τ w
      have hu := D.hN _ (inv_mem hn) w hw
      have hτu := hτV _ hu
      have e1 : ((n⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
          w + (((n⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by abel
      rw [coe_mul_apply, coe_mul_apply, coe_mul_apply, hτi, e1, map_add, hτw, hτu, ← e1,
        apply_inv_apply_O]
  exact (mem_fixSub S).mp hfix ν hν

theorem sup_le_inf_fixSpace (H : Hyp4 S g) (ht1 : t ≠ 1) {τ : S.O}
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hττ : τ * τ = 1) :
    Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      Wt S g t ⊓ fixSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  refine sup_le (le_inf (Vt_le_Wt H ht1) fun v hv => mem_fixSpace.mpr (hτV v hv)) ?_
  refine le_inf (commSpace_le_Wt_of_fix hτV) fun v hv => ?_
  obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
  rw [mem_fixSpace, map_sub, ← coe_mul_apply, hττ]
  change u - (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) u = (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u
  rw [← neg_sub, neg_eq_iff_add_eq_zero, add_self_zmod2]

theorem apply_sub_mem_of_mem_N1bar (D : Std H C ht ht1 hVQ) {τ : S.O}
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) {ν : S.O}
    (hν : ν ∈ N1bar S g t τ) (u : S.Qt) :
    (ν : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have hperp : S2.perp S.q (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      Wt S g t ⊓ fixSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [perp_sup, fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate τ.2]
    rfl
  rw [← perp_perp S.q_nondegenerate (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)), hperp]
  refine S2.mem_perp.mpr fun y hy => ?_
  have hνy := fix_of_mem_N1bar D hτV hy.1 (mem_fixSpace.mp hy.2) hν
  have h1 : polar S.q y ((ν : S.Qt ≃ₗ[ZMod 2] S.Qt) u) = polar S.q y u := by
    conv_lhs => rw [← hνy]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup ν.2 y u
  rw [polar_sub_right, h1, sub_self]

end CFSG.LargeExtraspecial.S8
