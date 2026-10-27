module

public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.Theta

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4MinusC

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S7
  CFSG.LargeExtraspecial.S8 CFSG.Open Subgroup Module QuadraticMap
open CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S) in
@[expose] def IsTypeA (s : S.O) : Prop :=
  ∀ v : S.Qt, S.q ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) = 0

theorem isTypeA_t (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) : IsTypeA S t := fun v => by
  have hv : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g t := by
    rw [← (commSpace_t_eq H C ht ht1 hVQ).1]
    exact mem_commSpace.mpr ⟨v, rfl⟩
  exact q_eq_zero_of_mem_Vt H ht1 hv

theorem isTypeA_conj {s : S.O} (hs : IsTypeA S s) (x : S.O) : IsTypeA S (x * s * x⁻¹) := by
  intro v
  have e : ((x * s * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v =
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) -
          ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
    rw [map_sub, coe_mul_apply, coe_mul_apply]
    congr 1
    rw [← coe_mul_apply, mul_inv_cancel]
    rfl
  rw [e, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2]
  exact hs _

theorem mem_CMt_of_mem_Lbar (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) {k : S.O}
    (hk : k ∈ S.Lbar g) : k ∈ S8.CMt S t :=
  S8.mem_CMt.mpr ⟨S.Lbar_le_Mbar g hk, Lbar_comm S H.conj_mem hk ht⟩

theorem q_mul_sub (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (D : S8.Std H C ht ht1 hVQ) {k : S.O} (hk : k ∈ S.Lbar g) (v : S.Qt) (x : Vt S g t)
    (hx : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v = x) :
    S.q (((t * k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) =
      S.q ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) +
        D.Q (S8.resCV S g H.conj_mem t ⟨k, mem_CMt_of_mem_Lbar H ht hk⟩ x - x) := by
  set e := S8.resCV S g H.conj_mem t ⟨k, mem_CMt_of_mem_Lbar H ht hk⟩ with he
  have hkt : Commute k t := Lbar_comm S H.conj_mem hk ht
  have hex : ((e x : Vt S g t) : S.Qt) = (k : S.Qt ≃ₗ[ZMod 2] S.Qt) x := rfl
  have heO : e ∈ TauCeti.QuadraticMap.orthogonalGroup D.Q :=
    W4As.resCV_mem_orthogonalGroup_omega H hNo C ht ht1 hVQ hΩ D.hsing _
  have hneg : ∀ a : ZMod 2, -a = a := by decide
  have h1 : ((t * k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v =
      ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) + (k : S.Qt ≃ₗ[ZMod 2] S.Qt) x := by
    rw [← hkt.eq, coe_mul_apply, ← hx, map_sub]
    abel
  have hkx : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) x ∈ Vt S g t := by
    rw [← hex]
    exact (e x).2
  have hq0 : S.q ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) x) = 0 := q_eq_zero_of_mem_Vt H ht1 hkx
  have hxv : polar S.q (x : S.Qt) v = 0 := by
    rw [← beta_apply H C ht ht1 hVQ x x hx]
    exact beta_isAlt H C ht ht1 hVQ x
  have hβ : beta H C ht ht1 hVQ (e x) x = polar S.q ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) x) v := by
    rw [beta_apply H C ht ht1 hVQ (e x) x hx, hex]
  have hQe : D.Q (e x) = D.Q x := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup heO x
  have hpolQ : polar D.Q (e x) x = beta H C ht ht1 hVQ (e x) x := by
    rw [← QuadraticMap.polarBilin_apply_apply, D.hpol]
  have hR : D.Q (e x - x) = polar S.q ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) x) v := by
    rw [sub_eq_add_neg, QuadraticMap.map_add (⇑D.Q), QuadraticMap.map_neg, hQe, polar_neg_right,
      CFSG.LargeExtraspecial.OrthoF2.zmod2_add_self, zero_add, hneg, hpolQ, hβ]
  rw [h1, QuadraticMap.map_add (⇑S.q), hq0, add_zero, polar_sub_left,
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup k.2, polar_comm S.q v (x : S.Qt),
    hxv, zero_sub, hneg, polar_comm, hR]

theorem mem_zpowers_of_isTypeA (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hP : ¬ PlusAt H C) {k : S.O} (hk : k ∈ S.Lbar g)
    (hkA : IsTypeA S k) (htkA : IsTypeA S (t * k)) : k ∈ zpowers t := by
  obtain ⟨D⟩ := S8.Std.nonempty hCE hNo hΩ
  set e := S8.resCV S g H.conj_mem t ⟨k, mem_CMt_of_mem_Lbar H ht hk⟩ with he
  have heO : e ∈ TauCeti.QuadraticMap.orthogonalGroup D.Q :=
    W4As.resCV_mem_orthogonalGroup_omega H hNo C ht ht1 hVQ hΩ D.hsing _
  have h0 : ∀ x, D.Q (e x - x) = 0 := by
    intro x
    obtain ⟨v, hv⟩ := exists_t_sub_eq H C ht ht1 hVQ x
    have h1 := q_mul_sub H hNo C ht ht1 hVQ hΩ D hk v x hv
    rw [htkA v, hkA v, zero_add] at h1
    exact h1.symm
  have he1 : e = 1 :=
    eq_one_of_forall_sub_singular D.hQ (hmin_of_not_plusAt H C ht ht1 hVQ hΩ h4 hP D) heO h0
  have hN := W4As.Nbar_eq_zpowers_omega4 hCE hw H hNo C ht ht1 hVQ hΩ h4
  refine CaseIClosure.mem_zpowers_of_resL_eq_one H ht hN hk ?_
  refine LinearEquiv.ext fun v => Subtype.ext ?_
  have h2 : ((e v : Vt S g t) : S.Qt) = v := by rw [he1]; rfl
  exact h2

theorem mul_not_mem_Delta (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hP : ¬ PlusAt H C) {d d' : S.O}
    (hd : d ∈ Delta S g t) (hd' : d' ∈ Delta S g t) (hne : d ≠ d') : d * d' ∉ Delta S g t := by
  intro hdd
  obtain ⟨n, hn, rfl⟩ := hd
  have hk : n⁻¹ * d' * n⁻¹⁻¹ ∈ Delta S g t := Case25.conj_mem_Delta (inv_mem hn) hd'
  have htk : n⁻¹ * (n * t * n⁻¹ * d') * n⁻¹⁻¹ ∈ Delta S g t :=
    Case25.conj_mem_Delta (inv_mem hn) hdd
  have e1 : n⁻¹ * (n * t * n⁻¹ * d') * n⁻¹⁻¹ = t * (n⁻¹ * d' * n⁻¹⁻¹) := by group
  rw [e1] at htk
  have hA : ∀ x ∈ Delta S g t, IsTypeA S x := by
    rintro x ⟨m, -, rfl⟩
    exact isTypeA_conj (isTypeA_t H C ht ht1 hVQ) m
  have hkL := Case25.delta_subset_Lbar ht hk
  have hz := mem_zpowers_of_isTypeA hCE hw H hNo C ht ht1 hVQ hΩ h4 hP hkL (hA _ hk) (hA _ htk)
  have htt : t * t = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem ht
  rcases S8.eq_one_or_eq_of_mem_zpowers htt hz with h1 | h1
  ·
    obtain ⟨m, -, hm⟩ := hd'
    apply ht1
    have : n⁻¹ * (m * t * m⁻¹) * n⁻¹⁻¹ = 1 := by rw [← hm]; exact h1
    calc t = (n⁻¹ * m)⁻¹ * (n⁻¹ * (m * t * m⁻¹) * n⁻¹⁻¹) * (n⁻¹ * m) := by group
      _ = 1 := by rw [this]; group
  · apply hne
    calc n * t * n⁻¹ = n * (n⁻¹ * d' * n⁻¹⁻¹) * n⁻¹ := by rw [h1]
      _ = d' := by group

end CFSG.GF2Type.Smith1979.W4MinusC
