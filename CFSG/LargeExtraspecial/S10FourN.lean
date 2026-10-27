module

public import CFSG.LargeExtraspecial.S10FourM
public import CFSG.LargeExtraspecial.S10FourB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem StronglyClosedL.commute_Abar_mul_of_conj_of_fix (hSC : StronglyClosedL S g t)
    (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X) (hfixAll : FixVtConj S g t)
    {m : S.M}
    (hne : S.ρ m * t * (S.ρ m)⁻¹ ≠ t)
    (hcomm : (S.ρ m * t * (S.ρ m)⁻¹) * t = t * (S.ρ m * t * (S.ρ m)⁻¹)) {k : S.M}
    (hk : S.ρ k ∈ Rbar S g t) {y : S.O} (hy : y ∈ S.Lbar ((k : G) * g) ⊓ Nbar S g t) :
    y * (S.ρ m * t * (S.ρ m)⁻¹) = (S.ρ m * t * (S.ρ m)⁻¹) * y := by
  have hkt : S.ρ k * t = t * S.ρ k := commute_of_mem_Rbar X.haQ hk
  have hkt' : (S.ρ k)⁻¹ * t = t * (S.ρ k)⁻¹ := by
    calc (S.ρ k)⁻¹ * t = (S.ρ k)⁻¹ * (t * S.ρ k) * (S.ρ k)⁻¹ := by group
      _ = (S.ρ k)⁻¹ * (S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hkt]
      _ = t * (S.ρ k)⁻¹ := by group
  have e : S.ρ (k⁻¹ * m) * t * (S.ρ (k⁻¹ * m))⁻¹ =
      (S.ρ k)⁻¹ * (S.ρ m * t * (S.ρ m)⁻¹) * S.ρ k := by
    rw [map_mul, map_inv]
    group
  have hne' : S.ρ (k⁻¹ * m) * t * (S.ρ (k⁻¹ * m))⁻¹ ≠ t := by
    rw [e]
    intro h
    apply hne
    calc S.ρ m * t * (S.ρ m)⁻¹ =
          S.ρ k * ((S.ρ k)⁻¹ * (S.ρ m * t * (S.ρ m)⁻¹) * S.ρ k) * (S.ρ k)⁻¹ := by group
      _ = S.ρ k * t * (S.ρ k)⁻¹ := by rw [h]
      _ = t := by rw [hkt]; group
  have hcomm' : (S.ρ (k⁻¹ * m) * t * (S.ρ (k⁻¹ * m))⁻¹) * t =
      t * (S.ρ (k⁻¹ * m) * t * (S.ρ (k⁻¹ * m))⁻¹) := by
    rw [e]
    obtain ⟨T, hT⟩ : ∃ T : S.O, T = S.ρ m * t * (S.ρ m)⁻¹ := ⟨_, rfl⟩
    rw [← hT] at hcomm ⊢
    calc (S.ρ k)⁻¹ * T * S.ρ k * t = (S.ρ k)⁻¹ * T * (S.ρ k * t) := by group
      _ = (S.ρ k)⁻¹ * T * (t * S.ρ k) := by rw [hkt]
      _ = (S.ρ k)⁻¹ * (T * t) * S.ρ k := by group
      _ = (S.ρ k)⁻¹ * (t * T) * S.ρ k := by rw [hcomm]
      _ = ((S.ρ k)⁻¹ * t) * T * S.ρ k := by group
      _ = (t * (S.ρ k)⁻¹) * T * S.ρ k := by rw [hkt']
      _ = t * ((S.ρ k)⁻¹ * T * S.ρ k) := by group
  have hx : (S.ρ k)⁻¹ * y * S.ρ k ∈ S.Lbar g ⊓ Nbar S g t := by
    refine Subgroup.mem_inf.mpr ⟨(mem_Lbar_mul_iff S k g).mp (Subgroup.mem_inf.mp hy).1, ?_⟩
    have hkt₁ : S.ρ k⁻¹ * t = t * S.ρ k⁻¹ := by
      rw [map_inv]
      calc (S.ρ k)⁻¹ * t = (S.ρ k)⁻¹ * (t * S.ρ k) * (S.ρ k)⁻¹ := by group
        _ = (S.ρ k)⁻¹ * (S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hkt]
        _ = t * (S.ρ k)⁻¹ := by group
    have := conj_mem_Nbar X.haQ hkt₁ (Subgroup.mem_inf.mp hy).2
    rwa [map_inv, inv_inv] at this
  have h1 := hSC.commute_Abar_of_conj_of_fix hCE X F hfixAll hne' hcomm' hx
  rw [e] at h1
  calc y * (S.ρ m * t * (S.ρ m)⁻¹) = S.ρ k * ((S.ρ k)⁻¹ * y * S.ρ k *
        ((S.ρ k)⁻¹ * (S.ρ m * t * (S.ρ m)⁻¹) * S.ρ k)) * (S.ρ k)⁻¹ := by group
    _ = S.ρ k * ((S.ρ k)⁻¹ * (S.ρ m * t * (S.ρ m)⁻¹) * S.ρ k *
        ((S.ρ k)⁻¹ * y * S.ρ k)) * (S.ρ k)⁻¹ := by rw [h1]
    _ = (S.ρ m * t * (S.ρ m)⁻¹) * y := by group

theorem StronglyClosedL.false_of_conj_of_fix (hSC : StronglyClosedL S g t)
    (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X) (hfixAll : FixVtConj S g t)
    {m : S.M}
    (hne : S.ρ m * t * (S.ρ m)⁻¹ ≠ t)
    (hcomm : (S.ρ m * t * (S.ρ m)⁻¹) * t = t * (S.ρ m * t * (S.ρ m)⁻¹)) : False := by
  have haQ := X.haQ
  obtain ⟨k, hk, -, hb⟩ := X.exists_pair
  obtain ⟨hsup, -, -, -, hN⟩ := timmesfeld_10_1_two hCE X hk hb
  have hfixV := hfixAll m hne hcomm
  have hA : ∀ x ∈ S.Lbar g ⊓ Nbar S g t,
      x * (S.ρ m * t * (S.ρ m)⁻¹) = (S.ρ m * t * (S.ρ m)⁻¹) * x :=
    fun x hx => hSC.commute_Abar_of_conj_of_fix hCE X F hfixAll hne hcomm hx
  have hB : ∀ y ∈ S.Lbar ((k : G) * g) ⊓ Nbar S g t,
      y * (S.ρ m * t * (S.ρ m)⁻¹) = (S.ρ m * t * (S.ρ m)⁻¹) * y :=
    fun y hy => hSC.commute_Abar_mul_of_conj_of_fix hCE X F hfixAll hne hcomm hk hy
  have hzero : ∀ {v : S.Qt}, v ∈ Vt S g t →
      v ∈ commSpace ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) → v = 0 :=
    fun hv hv' => hSC.eq_zero_of_mem_inf_of_fix hCE X F hfixAll hne hcomm hv hv'
  have hkQ := conj_mem_QG' S k.2 haQ
  have hkt : S.ρ k * t = t * S.ρ k := commute_of_mem_Rbar X.haQ hk
  obtain ⟨t', ht'⟩ : ∃ t' : S.O, t' = S.ρ m * t * (S.ρ m)⁻¹ := ⟨_, rfl⟩
  rw [← ht'] at hfixV hA hB hcomm hzero
  have hTt : (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm]
  obtain ⟨-, hTW⟩ := apply_mem_Vt_Wt_of_commute X hTt
  have hcent : ∀ x ∈ Nbar S g t, x * t' = t' * x → ∀ w ∈ Wt S g t,
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t' : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) =
        (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w := by
    intro x hxN hxt w hw
    have hδ := hfixV _ (hN x hxN w hw)
    have hxtw : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t' : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
        (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul,
        ← Subgroup.coe_mul, hxt]
    rw [map_sub, hxtw, show (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
      w + ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) by abel, map_add, hδ]
    abel
  have hzb : S.z ∈ S.Qa ((k : G) * g) := S.z_mem_Qa_of_mem_QG rfl hkQ (conj_ne_z' S k.2 X.H.conj_ne)
  have hzQa : S.z ∈ S.Qa g := S.z_mem_Qa_of_mem_QG rfl haQ X.H.conj_ne
  have haPb : S.cl (g * S.z * g⁻¹) ∉ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) := fun h =>
    S6.not_mem_Qa_symm hb (mem_Qa_of_cl_mem' hzb haQ h)
  have hbPa : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∉ S.clSub (S.QG ⊓ S.Qa g) := fun h =>
    hb (mem_Qa_of_cl_mem' hzQa hkQ h)
  have hbV : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t :=
    cl_mem_Vt (mem_Lbar_mul_of_mem_Rbar X.H X.ht hk)
  have hWV : ∀ w ∈ Wt S g t, (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
    intro w hw
    have huW : (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Wt S g t := sub_mem (hTW w hw) hw
    rw [← hsup] at huW
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp huW
    have hsplit : ∀ x : S.O, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (p + q) = p + q →
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q := by
      intro x hx
      rw [map_add] at hx
      have : ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) + ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q) = 0 := by
        rw [show ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) + ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q) =
          ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) p + (x : S.Qt ≃ₗ[ZMod 2] S.Qt) q) - (p + q) by abel, hx,
          sub_self]
      rw [← ZModModule.sub_eq_add, sub_eq_zero] at this
      exact this
    have hpV : p ∈ Vt S g t := by
      have hpfix : ∀ x ∈ S.Lbar g ⊓ Nbar S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p := by
        intro x hx
        obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.mp hx
        have hxu := hcent x hxN (hA x hx) w hw
        rw [← hpq] at hxu
        have h3 := hsplit x hxu
        obtain ⟨x₀, hx₀⟩ := MonoidHom.mem_range.mp (S.Lbar_le_Mbar g hxL)
        have hxb : ((S.ρ x₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
              S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
          rw [hx₀]
          exact (mem_Nbar.mp hxN).2 _ hbV
        have hxq := apply_mem_clSub_of_fix X hxb hq.1
        rw [hx₀] at hxq
        rcases mem_span_singleton_zmod2.mp (Lbar_apply_sub_mem_span' haQ hp.1 hxL) with h | h
        · exact sub_eq_zero.mp h
        · exact absurd (by rw [← h, h3]; exact sub_mem hxq hq.1) haPb
      have := (clSub_inf_fixSub_Abar X).le ⟨hp.1, hpfix⟩
      exact this.2
    have hqV : q ∈ Vt S g t := by
      have hqfix : ∀ y ∈ S.Lbar ((k : G) * g) ⊓ Nbar S g t,
          (y : S.Qt ≃ₗ[ZMod 2] S.Qt) q = q := by
        intro y hy
        obtain ⟨hyL, hyN⟩ := Subgroup.mem_inf.mp hy
        have hyu := hcent y hyN (hB y hy) w hw
        rw [← hpq] at hyu
        have h3 := hsplit y hyu
        obtain ⟨y₀, hy₀⟩ := MonoidHom.mem_range.mp (S.Lbar_le_Mbar _ hyL)
        have hya : ((S.ρ y₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (S.cl (((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹)) =
              S.cl (((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹) := by
          rw [hy₀]
          simpa using (mem_Nbar.mp hyN).2 _ (cl_a_mem_Vt X.ht)
        have hyp := apply_mem_clSub_of_fix X hya (by simpa using hp.1)
        rw [hy₀] at hyp
        simp only [Subgroup.coe_one, one_mul] at hyp
        rcases mem_span_singleton_zmod2.mp (Lbar_apply_sub_mem_span' hkQ hq.1 hyL) with h | h
        · exact sub_eq_zero.mp h
        · exact absurd (by rw [← h, ← h3]; exact sub_mem hyp hp.1) hbPa
      have hq' : (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) q ∈
          S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) := by
        refine ⟨(mem_clSub_Qa_mul_iff k).mp hq.1, fun x hx => ?_⟩
        obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.mp hx
        have hxk : S.ρ k * x * (S.ρ k)⁻¹ ∈ S.Lbar ((k : G) * g) ⊓ Nbar S g t :=
          Subgroup.mem_inf.mpr ⟨conj_mem_Lbar_mul S k hxL, conj_mem_Nbar X.haQ hkt hxN⟩
        have h1 := hqfix _ hxk
        have h2 := congrArg (fun v => (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) h1
        simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at h2
        rw [inv_apply_apply_O] at h2
        exact h2
      rw [clSub_inf_fixSub_Abar X] at hq'
      have := apply_mem_Vt_of_mem_Rbar X.haQ hk hq'.2
      rwa [apply_inv_apply_O] at this
    rw [← hpq]
    exact add_mem hpV hqV
  have hW0 : ∀ w ∈ Wt S g t, (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := fun w hw =>
    sub_eq_zero.mp (hzero (hWV w hw) (sub_mem_commSpace _ w))
  have hCV : ∀ v ∈ commSpace (t' : S.Qt ≃ₗ[ZMod 2] S.Qt), v ∈ Vt S g t := by
    intro v hv
    obtain ⟨z, rfl⟩ := mem_commSpace.mp hv
    have hmem : (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z ∈
        LinearMap.BilinForm.orthogonal S.q.polarBilin (Wt S g t) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      rw [polarBilin_apply_apply, polar_sub_right, ← hW0 w hw,
        TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup t'.2, hW0 w hw, sub_self]
    rwa [orthogonal_Wt] at hmem
  have hbot : commSpace (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    exact (Submodule.mem_bot _).mpr (hzero (hCV v hv) hv)
  have h4 := finrank_commSpace_conj_t X m
  rw [← ht', hbot, finrank_bot] at h4
  exact absurd h4 (by decide)

theorem timmesfeld_10_4_self_of_fix (hCE : CentralExtInput.{u}) (X : Hyp10 S g t)
    (hfix : StronglyClosedL S g t → FixVtConj S g t) :
    ∃ k : S.M, S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g ∧ S.ρ k * t * (S.ρ k)⁻¹ ≠ t := by
  by_contra hcon
  push Not at hcon
  have hSC : StronglyClosedL S g t := hcon
  obtain ⟨F⟩ := X.exists_frame
  obtain ⟨m, hne, hcomm⟩ := exists_conj_commute_ne X
  exact hSC.false_of_conj_of_fix hCE X F (hfix hSC) hne hcomm

theorem timmesfeld_10_4_self (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (h7 : 7 ≤ S.width) :
    ∃ k : S.M, S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g ∧ S.ρ k * t * (S.ρ k)⁻¹ ≠ t := by
  obtain ⟨F⟩ := X.exists_frame
  exact timmesfeld_10_4_self_of_fix hCE X fun hSC => hSC.fixVtConj hCE X F h7

end CFSG.LargeExtraspecial.S10
