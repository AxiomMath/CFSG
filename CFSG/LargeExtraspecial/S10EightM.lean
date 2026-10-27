module

public import CFSG.LargeExtraspecial.S10EightL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem card_le_two_mul_of_mem {X : Type*} [Group X] [Finite X] {H K : Subgroup X}
    (h : ∀ a ∈ K, a ∉ H → ∀ b ∈ K, b ∉ H → a⁻¹ * b ∈ H) :
    Nat.card K ≤ 2 * Nat.card H := by
  classical
  by_cases hK : ∃ a ∈ K, a ∉ H
  · obtain ⟨a, haK, haH⟩ := hK
    let f : K → H ⊕ H := fun x =>
      if hx : (x : X) ∈ H then Sum.inl ⟨x, hx⟩
      else Sum.inr ⟨a⁻¹ * x, h a haK haH x x.2 hx⟩
    have hf : Function.Injective f := by
      intro x y hxy
      by_cases hx : (x : X) ∈ H <;> by_cases hy : (y : X) ∈ H <;>
        simp only [f, hx, hy, dite_true, dite_false, Sum.inl.injEq, Sum.inr.injEq,
          reduceCtorEq] at hxy
      · exact Subtype.ext (congrArg (fun z : H => (z : X)) hxy)
      · exact Subtype.ext (mul_left_cancel (congrArg (fun z : H => (z : X)) hxy))
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_sum] at this
    omega
  · push Not at hK
    have hle : K ≤ H := fun x hx => hK x hx
    have := Subgroup.card_le_of_le hle
    omega

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem Hyp10.mem_Qa_of_mem_clSub (X : Hyp10 S g t) {f : G} (hfQ : f ∈ S.QG)
    (hfP : S.cl f ∈ S.clSub (S.QG ⊓ S.Qa g)) : f ∈ S.Qa g := by
  obtain ⟨x, hx, hxQ, hxf⟩ := S.mem_clSub_iff.mp hfP
  have hzQa : S.z ∈ S.Qa g := S.z_mem_Qa_of_mem_QG rfl X.haQ X.H.conj_ne
  rcases (S.cl_eq_cl_iff hxQ hfQ).mp hxf with h | h
  · rw [h]
    exact hx.2
  · rw [h]
    exact mul_mem hx.2 hzQa

theorem Hyp10.mem_clSub_symm (X : Hyp10 S g t) {k : S.M}
    (hkP : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hk1 : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹)) :
    S.cl (g * S.z * g⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) := by
  set T := S.conjBy g with hT
  have hfQ := conj_mem_QG' S k.2 X.haQ
  have hfQa := X.mem_Qa_of_mem_clSub hfQ hkP
  have hTz : T.z = g * S.z * g⁻¹ := rfl
  have hgt : (k : G) * T.z * (k : G)⁻¹ = (k : G) * g * S.z * ((k : G) * g)⁻¹ := by
    rw [hTz]
    group
  have hne : (k : G) * g * S.z * ((k : G) * g)⁻¹ ≠ T.z := fun h => hk1 (by rw [h, hTz])
  have h1 : T.z ∈ T.Qa (k : G) := T.z_mem_Qa_of_mem_QG hgt hfQa hne
  have h2 : T.Qa (k : G) = S.Qa ((k : G) * g) := by
    rw [Setting.Qa_eq_map, S4.Qa_mul S]
    rfl
  rw [h2] at h1
  exact S.cl_mem_clSub ⟨X.haQ, h1⟩ X.haQ

variable (S) in
@[expose] def vecFix (v : S.Qt) : Subgroup S.O where
  carrier := {x | (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v}
  mul_mem' := fun {x y} hx hy => by
    change ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
    rw [show ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v from hy]
    exact hx
  one_mem' := rfl
  inv_mem' := fun {x} hx => by
    change ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
    have hx' : ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := hx
    conv_lhs => rw [← hx']
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl

theorem mem_vecFix {v : S.Qt} {x : S.O} : x ∈ vecFix S v ↔ (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
  Iff.rfl

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem isWeaklyClosed_Ebar (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g)
    (h7 : 7 ≤ S.width) : IsWeaklyClosedInNormalizer ((S.Lbar g ⊓ Xb).subgroupOf S.Mbar) := by
  have hEM : S.Lbar g ⊓ Xb ≤ S.Mbar := inf_le_left.trans (S.Lbar_le_Mbar g)
  intro x hx
  have hmap : ∀ y : S.Mbar, y ∈ ((S.Lbar g ⊓ Xb).subgroupOf S.Mbar).map
      (MulAut.conj x).toMonoidHom ↔ (x : S.O)⁻¹ * y * x ∈ S.Lbar g ⊓ Xb := by
    intro y
    rw [mem_map_conj_iff, mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have h3 := D.timmesfeld_10_8_three hCE hP h7 x.2 (fun e he => by
    have hxe : (x : S.O) * e * (x : S.O)⁻¹ ∈ S.Mbar :=
      mul_mem (mul_mem x.2 (hEM he)) (inv_mem x.2)
    have hin : (⟨_, hxe⟩ : S.Mbar) ∈ ((S.Lbar g ⊓ Xb).subgroupOf S.Mbar).map
        (MulAut.conj x).toMonoidHom := (hmap _).mpr (by simpa [mul_assoc] using he)
    have hN := hx hin
    rw [mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have h1 := (mem_normalizer_iff.mp hN ⟨w, hEM hw⟩).mp (mem_subgroupOf.mpr hw)
      exact mem_subgroupOf.mp h1
    · intro hw
      have hwM : w ∈ S.Mbar := by
        have e1 : w = ((x : S.O) * e * (x : S.O)⁻¹)⁻¹ *
            ((x : S.O) * e * (x : S.O)⁻¹ * w * ((x : S.O) * e * (x : S.O)⁻¹)⁻¹) *
              ((x : S.O) * e * (x : S.O)⁻¹) := by group
        rw [e1]
        exact mul_mem (mul_mem (inv_mem hxe) (hEM hw)) hxe
      have h1 := (mem_normalizer_iff.mp hN ⟨w, hwM⟩).mpr (mem_subgroupOf.mpr hw)
      exact mem_subgroupOf.mp h1)
  ext y
  rw [hmap, mem_subgroupOf]
  constructor
  · intro hy
    have := h3 _ hy
    simpa [mul_assoc] using this
  · intro hy
    have hle : (S.Lbar g ⊓ Xb).map (MulAut.conj (x : S.O)).toMonoidHom ≤ S.Lbar g ⊓ Xb := by
      rintro _ ⟨e, he, rfl⟩
      exact h3 e he
    have heq := Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj (x : S.O)).injective).symm.le
    have hy' : (y : S.O) ∈ (S.Lbar g ⊓ Xb).map (MulAut.conj (x : S.O)).toMonoidHom := by
      rw [heq]
      exact hy
    rw [mem_map_conj_iff] at hy'
    exact hy'

theorem conj_mem_Ebar_of_commute (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g)
    (h7 : 7 ≤ S.width) {e m : S.O} (he : e ∈ S.Lbar g ⊓ Xb) (hm : m ∈ S.Mbar)
    (hc : ∀ x ∈ S.Lbar g ⊓ Xb, m * e * m⁻¹ * x = x * (m * e * m⁻¹)) :
    m * e * m⁻¹ ∈ S.Lbar g ⊓ Xb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEM : S.Lbar g ⊓ Xb ≤ S.Mbar := inf_le_left.trans (S.Lbar_le_Mbar g)
  have hAp : IsPGroup 2 ((S.Lbar g ⊓ Xb).subgroupOf S.Mbar) := by
    intro x
    refine ⟨1, ?_⟩
    have h1 : ((x : S.Mbar) : S.O) * ((x : S.Mbar) : S.O) = 1 :=
      S4.mul_self_of_mem_Lbar S X.haQ (mem_subgroupOf.mp x.2).1
    have h2 : (x : S.Mbar) * (x : S.Mbar) = 1 := Subtype.ext h1
    have h3 : x * x = 1 := Subtype.ext h2
    rw [pow_one, _root_.sq, h3]
  have hAc : ∀ a ∈ (S.Lbar g ⊓ Xb).subgroupOf S.Mbar,
      ∀ b ∈ (S.Lbar g ⊓ Xb).subgroupOf S.Mbar, a * b = b * a := fun _ ha _ hb =>
    Subtype.ext (S4.Lbar_comm S X.haQ (mem_subgroupOf.mp ha).1 (mem_subgroupOf.mp hb).1)
  have hsc := lemma_3_12_isStronglyClosedIn hAp hAc (D.isWeaklyClosed_Ebar hCE hP h7)
  have he' : (⟨e, hEM he⟩ : S.Mbar) ∈ (S.Lbar g ⊓ Xb).subgroupOf S.Mbar := mem_subgroupOf.mpr he
  have key := hsc.2 ⟨e, hEM he⟩ he' (⟨m, hm⟩ : S.Mbar)⁻¹ (by
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : ((x : S.Mbar) : S.O) ∈ S.Lbar g ⊓ Xb := mem_subgroupOf.mp hx
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    exact (hc _ hx').symm)
  have := mem_subgroupOf.mp key
  simpa using this

theorem exists_dec108_of_hyp10 (hCE : CentralExtInput.{u}) {τ : S.O}
    (hτ : τ ∈ S.Lbar g ⊓ Xb) (Y : Hyp10 S g τ) :
    ∃ Xτ Yτ : Subgroup S.O, Nonempty (Dec108 Y Xτ Yτ) ∧ S.Lbar g ⊓ Xτ = S.Lbar g ⊓ Xb ∧
      ⁅Yτ, Yτ⁆ = ⁅Yb, Yb⁆ := by
  obtain ⟨x, hx, hxN⟩ : ∃ x ∈ S.Lbar g ⊓ Xb, x ∉ Nbar S g τ := by
    by_contra hcon
    push Not at hcon
    have := D.card_LmodN_le_two hCE hτ hcon
    rw [Y.card_LmodN] at this
    omega
  obtain ⟨k, hkY', -, hne, hPa, -⟩ := D.exists_d hCE
  have hkY := ((D.dec.mem_commutator_iff).mp hkY').1
  obtain ⟨F, -, -, -⟩ := D.exists_frame hCE
  have hkR := D.dec.le_Rbar_right hkY
  have hπk : act (F.π ⟨S.ρ k, hkR⟩) E00 ≠ E00 := by
    intro h
    have hth := D.mem_Lbar_mul (D.t_mem_Ebar hCE) hkY
    have h1 : F.φ (bV hth) = F.φ (aV X.ht) := by
      rw [bV_eq_resV X hkR hth, F.φ_resV_aV, h, F.base]
    have h2 := congrArg Subtype.val (F.φ.injective h1)
    rw [coe_bV] at h2
    exact hne h2
  have hdim := finrank_commSpace_le_four_of_fixW X F hkR hπk hPa hx.1 (D.fixW x hx.2)
    (D.mem_Lbar_mul hx hkY)
  have hxW := mem_fixWstar_of_finrank_le Y hx.1 hxN hdim
  obtain ⟨F₀⟩ := Y.exists_frame
  obtain ⟨F', hπx⟩ : ∃ F' : Frame Y, F'.π ⟨x, Lbar_le_Rbar Y.ht hx.1⟩ = τ₁ := by
    rcases pi_eq_τ₁_or_τ₂ hCE Y F₀ hx.1 hxN hxW with h | h
    · exact ⟨F₀, h⟩
    · exact ⟨F₀.swap, by rw [F₀.swap_π, h, τ₂_swap]⟩
  obtain ⟨-, Yτ, -, hiso, hsup, hinf, hcomm, hW, y, hyY, hyL, hπy⟩ :=
    timmesfeld_10_2_frame hCE Y F' hx.1 hxW hπx
  have Dτ : Dec108 Y (R0 S g τ x) Yτ := ⟨⟨hsup, hinf, hcomm, hiso⟩, hW, y, hyY, hyL,
    fun h => τ₂_ne_one (hπy.symm.trans ((F'.ker _).mpr h))⟩
  obtain ⟨hidx, hc⟩ := timmesfeld_10_3_hyperplane hCE X D.dec
  have heq : ⁅Yb, Yb⁆ = ⁅Yτ, Yτ⁆ := timmesfeld_10_3_beta hCE Y Dτ.dec
    (fun w hw => D.Yb_le_Rbar hτ ((D.dec.mem_commutator_iff).mp hw).1)
    (by rw [D.dec.card_commutator]; decide) D.dec.commutator_ne_bot inf_le_left hidx hc
  refine ⟨R0 S g τ x, Yτ, ⟨Dτ⟩, ?_, heq.symm⟩
  obtain ⟨⟨d, hdY'⟩, hd1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp D.dec.commutator_ne_bot
  have hd1 : d ≠ 1 := fun h => hd1' (Subtype.ext h)
  have hdτ : d ∈ ⁅Yτ, Yτ⁆ := by rw [← heq]; exact hdY'
  ext e
  constructor
  · rintro ⟨heL, heX⟩
    refine ⟨heL, D.mem_Xb_of_commute hCE hdY' hd1 heL ?_⟩
    exact Dτ.dec.comm e heX d ((Dτ.dec.mem_commutator_iff).mp hdτ).1
  · rintro ⟨heL, heX⟩
    refine ⟨heL, Dτ.mem_Xb_of_commute hCE hdτ hd1 heL ?_⟩
    exact D.dec.comm e heX d ((D.dec.mem_commutator_iff).mp hdY').1

end Dec108

end CFSG.LargeExtraspecial.S10
