module

public import CFSG.LargeExtraspecial.S5OneZ
public import CFSG.LargeExtraspecial.S5Two

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.Open CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

structure CompAt (S : Setting G) (g : G) where
  X : Subgroup S.O
  t : S.O
  isComponentOf : IsComponentOf X S.Mbar
  norm : ∀ h : S.M, S.Lbar ((h : G) * g) ≤ normalizer (X : Set S.O)
  mem_Lbar : t ∈ S.Lbar g
  ne_one : t ≠ 1
  comm : ∀ x ∈ X, x * t = t * x

namespace CompAt

variable {S : Setting G} {g : G} (A : CompAt S g)

theorem isQuasisimple : CFSG.Open.IsQuasisimple A.X := A.isComponentOf.2.2

theorem normL : S.Lbar g ≤ normalizer (A.X : Set S.O) := by simpa using A.norm 1

theorem rho_comm {x : S.O} (hx : x ∈ A.X) : ∃ k : S.M, S.ρ k = x ∧ S.ρ k * A.t = A.t * S.ρ k := by
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (A.isComponentOf.1 hx)
  exact ⟨k, hk, hk ▸ A.comm x hx⟩

theorem le_Rbar (hIrr : Irr S) (H : Hyp4 S g) : A.X ≤ Rbar S g A.t := by
  have haQ := H.conj_mem
  have hq := A.isQuasisimple
  have hnorm : ∀ a ∈ A.X, ∀ n ∈ A.X ⊓ Rbar S g A.t, a * n * a⁻¹ ∈ A.X ⊓ Rbar S g A.t := by
    intro a ha n hn
    obtain ⟨k, rfl, hkt⟩ := A.rho_comm ha
    exact ⟨A.X.mul_mem (A.X.mul_mem ha hn.1) (A.X.inv_mem ha), conj_mem_Rbar hkt hn.2⟩
  rcases commute_or_eq_of_normalized hq inf_le_left hnorm with hcen | heq
  · exfalso
    have hXne : A.X ≠ ⊥ := ne_bot_of_isQuasisimple hq
    obtain ⟨s, hs, x₀, hx₀, hsx₀⟩ := exists_not_commute hIrr H hXne A.norm
    have : Group.IsPerfect A.X := ⟨hq.1⟩
    have hss : s * s = 1 := S4.mul_self_of_mem_Lbar S haQ hs
    have h1 : ⁅A.X, zpowers s⁆ ≤ A.X ⊓ Rbar S g A.t := by
      rw [commutator_le]
      intro x hx y hy
      rcases (Setting.mem_zpowers_iff_of_mul_self hss).mp hy with rfl | rfl
      · rw [commutatorElement_one_right]
        exact one_mem _
      · refine ⟨?_, ?_⟩
        · have h2 : y * x⁻¹ * y⁻¹ ∈ A.X :=
            (mem_normalizer_iff.mp (A.normL hs) _).mp (A.X.inv_mem hx)
          have := A.X.mul_mem hx h2
          simpa [commutatorElement_def, mul_assoc] using this
        · obtain ⟨k, rfl, hkt⟩ := A.rho_comm hx
          have htk : A.t ∈ S.Lbar ((k : G) * g) := by
            have := conj_mem_Lbar_mul S k A.mem_Lbar
            rwa [hkt, mul_inv_cancel_right] at this
          have h3 : S.ρ k * y * (S.ρ k)⁻¹ ∈ Rbar S g A.t :=
            Lbar_mul_le_Rbar htk (conj_mem_Lbar_mul S k hs)
          have h4 : y⁻¹ ∈ Rbar S g A.t := Lbar_le_Rbar A.mem_Lbar (inv_mem hs)
          simpa [commutatorElement_def] using mul_mem h3 h4
    have h2 : ⁅A.X ⊓ Rbar S g A.t, A.X⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      intro n hn
      rw [mem_centralizer_iff]
      intro a ha
      exact (hcen n hn a ha).symm
    have hdouble : ⁅⁅A.X, zpowers s⁆, A.X⁆ = ⊥ :=
      le_bot_iff.mp (h2 ▸ commutator_mono h1 le_rfl)
    have hcomm := Quasisimple.perfect_double_commutator A.X (zpowers s) hdouble
    have hc : x₀ * s * x₀⁻¹ * s⁻¹ ∈ ⁅A.X, zpowers s⁆ :=
      commutator_mem_commutator hx₀ (mem_zpowers s)
    rw [hcomm, mem_bot] at hc
    apply hsx₀
    calc s * x₀ = (x₀ * s * x₀⁻¹ * s⁻¹)⁻¹ * (x₀ * s) := by group
      _ = x₀ * s := by rw [hc, inv_one, one_mul]
  · rw [← heq]
    exact inf_le_right

theorem Rbar_le_normalizer : Rbar S g A.t ≤ normalizer (A.X : Set S.O) :=
  sSup_le fun _ ⟨h, hX, _⟩ => hX ▸ A.norm h

theorem isSubnormal (hIrr : Irr S) (H : Hyp4 S g) : IsSubnormal A.X (Rbar S g A.t) :=
  CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf (A.le_Rbar hIrr H)
    (normal_subgroupOf_of_le_normalizer A.Rbar_le_normalizer)

theorem not_le_Nbar (hIrr : Irr S) (H : Hyp4 S g) (C : Cons311 S g) :
    ¬ A.X ≤ Nbar S g A.t := by
  intro h
  have haQ := H.conj_mem
  have hq := A.isQuasisimple
  have hnormL : ∀ y ∈ A.X, y ∈ normalizer (S.Lbar g : Set S.O) := fun y hy =>
    Nbar_le_normalizer haQ H.conj_ne (Lbar_mem_Dset A.mem_Lbar) (h hy)
  have hnorm : ∀ a ∈ A.X, ∀ n ∈ A.X ⊓ S.Lbar g, a * n * a⁻¹ ∈ A.X ⊓ S.Lbar g :=
    fun a ha n hn => ⟨A.X.mul_mem (A.X.mul_mem ha hn.1) (A.X.inv_mem ha),
      (mem_normalizer_iff.mp (hnormL a ha) n).mp hn.2⟩
  apply Lbar_inf_ne_bot hIrr H C A.isComponentOf A.norm
  rcases commute_or_eq_of_normalized hq inf_le_left hnorm with hcen | heq
  · rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    have hx' : x ∈ A.X ⊓ S.Lbar g := ⟨hx.2, hx.1⟩
    have hxx : x ^ (2 ^ 1) = 1 := by
      rw [pow_one, pow_two]
      exact S4.mul_self_of_mem_Lbar S haQ hx.1
    exact eq_one_of_mem_center_of_pow S A.isComponentOf.2.1 hx.2 (hcen x hx') hxx
  · exfalso
    have hXL : A.X ≤ S.Lbar g := by rw [← heq]; exact inf_le_right
    exact not_isSolvable_of_isQuasisimple hq (SwapData.isSolvable_of_le_Lbar H hXL)

theorem Rbar_ne (hIrr : Irr S) (H : Hyp4 S g) : Rbar S g A.t ≠ S.Lbar g := fun h =>
  not_isSolvable_of_isQuasisimple A.isQuasisimple
    (SwapData.isSolvable_of_le_Lbar H (h ▸ A.le_Rbar hIrr H))

theorem isQuasisimple_img (hIrr : Irr S) (H : Hyp4 S g) (C : Cons311 S g) :
    CFSG.Open.IsQuasisimple (imgR H.conj_mem A.t A.X) :=
  isQuasisimple_imgR H.conj_mem (A.le_Rbar hIrr H) A.isQuasisimple (A.not_le_Nbar hIrr H C)

theorem isSubnormal_img (hIrr : Irr S) (H : Hyp4 S g) :
    IsSubnormal (imgR H.conj_mem A.t A.X) (RmodN S g A.t) :=
  isSubnormal_imgR H.conj_mem (A.le_Rbar hIrr H) (A.isSubnormal hIrr H)

theorem hyp45q (hIrr : Irr S) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (Q : Hyp45Q H C) :
    ((∀ x ∈ RmodN S g A.t, ∃ k ∈ imgR H.conj_mem A.t A.X, ∃ e ∈ LmodN S g A.t, x = k * e) ∧
      (LmodN S g A.t ⊓ imgR H.conj_mem A.t A.X).relIndex (LmodN S g A.t) ≤ 2) ∧
    (V S g A.t ≤ S.Qa g →
      imgR H.conj_mem A.t A.X = RmodN S g A.t ∧ 3 ≤ finrank (ZMod 2) (Vt S g A.t)) :=
  let h := Q.quasisimple hNo A.mem_Lbar A.ne_one (A.Rbar_ne hIrr H) (A.isSubnormal_img hIrr H)
    (A.isQuasisimple_img hIrr H C)
  ⟨h.1, h.2.1⟩

theorem commute_of_mem_Nbar (hIrr : Irr S) (H : Hyp4 S g) (C : Cons311 S g) {x : S.O}
    (hxL : x ∈ S.Lbar g) (hxN : x ∈ Nbar S g A.t) {y : S.O} (hy : y ∈ A.X) : x * y = y * x :=
  commute_of_mem_Lbar_inf_Nbar H A.mem_Lbar (A.le_Rbar hIrr H) A.isQuasisimple
    (A.not_le_Nbar hIrr H C)
    (fun _ hs y' hy' => (mem_normalizer_iff.mp (A.normL hs) y').mp hy')
    (fun _ hz hc _ hk => eq_one_of_mem_center_of_pow S A.isComponentOf.2.1 hz hc hk) hxL hxN hy

theorem mem_Nbar_of_commute (hIrr : Irr S) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (Q : Hyp45Q H C) {s : S.O} (hsL : s ∈ S.Lbar g) (hsX : ∀ y ∈ A.X, s * y = y * s) :
    s ∈ Nbar S g A.t := by
  refine ⟨Lbar_le_Rbar A.mem_Lbar hsL, fun v hv => ?_⟩
  have hfac := (A.hyp45q hIrr H hNo C Q).1.1
  rw [Vt_eq_span_orbit H A.mem_Lbar] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨r, hr, rfl⟩ := hv
    obtain ⟨y, hyX, -, hya⟩ := exists_apply_eq_of_factor H A.mem_Lbar hfac hr
    rw [← hya, ← coe_mul_apply, hsX y hyX, coe_mul_apply]
    have hsa : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
      (mem_fixSub S).mp (by rw [H.fixSub_eq]; exact Submodule.mem_span_singleton_self _) s hsL
    rw [hsa]
  | zero => simp
  | add u w _ _ hu hw => rw [map_add, hu, hw]
  | smul c u _ hu => rw [map_smul, hu]

theorem eq_one_or_eq (hIrr : Irr S) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (Q : Hyp45Q H C) (hVQ : ¬ V S g A.t ≤ S.Qa g) {s : S.O} (hsL : s ∈ S.Lbar g)
    (hsX : ∀ y ∈ A.X, s * y = y * s) : s = 1 ∨ s = A.t :=
  eq_one_or_eq_of_factor H C A.mem_Lbar A.ne_one hVQ (A.hyp45q hIrr H hNo C Q).1.1 hsL hsX

theorem card_Lbar_inf_Nbar_le_two (hIrr : Irr S) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) (Q : Hyp45Q H C) (hVQ : ¬ V S g A.t ≤ S.Qa g) :
    Nat.card (S.Lbar g ⊓ Nbar S g A.t : Subgroup S.O) ≤ 2 :=
  card_le_two_of_subset fun _ hx => A.eq_one_or_eq hIrr H hNo C Q hVQ hx.1
    fun _ hy => A.commute_of_mem_Nbar hIrr H C hx.1 hx.2 hy

end CompAt

end CFSG.LargeExtraspecial.S5
