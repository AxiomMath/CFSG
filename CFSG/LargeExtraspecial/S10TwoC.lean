module

public import CFSG.LargeExtraspecial.S10TwoB
public import CFSG.LargeExtraspecial.S4EightMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem Hyp10.isPGroup_Nbar (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) :
    IsPGroup 2 (Nbar S g t) :=
  isPGroup_Nbar_of_eq X.H X.ht (Nbar_eq_N0bar_of_omegaCase hCE X.H X.hNo X.C X.ht X.ht1 X.hVQ X.hΩ)

namespace Frame

variable {X : Hyp10 S g t} (F : Frame X)

theorem exists_cube_lift (hCE : CentralExtInput.{u}) {γ : Gm} (hγ : γ ^ 3 = 1) :
    ∃ k : S.M, ∃ hk : S.ρ k ∈ Rbar S g t, (S.ρ k) ^ 3 = 1 ∧ F.π ⟨S.ρ k, hk⟩ = γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := F.surj γ
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp (X.isPGroup_Nbar hCE)
  have hr3 : ((r : S.O)) ^ 3 ∈ Nbar S g t := by
    have := (F.ker (r ^ 3)).mp (by rw [map_pow, hr, hγ])
    simpa using this
  have hpow : (((r : S.O)) ^ 3) ^ (2 ^ e) = 1 := by
    have := pow_card_eq_one' (G := Nbar S g t) (x := ⟨_, hr3⟩)
    rw [he] at this
    exact congrArg Subtype.val this
  set h : Rbar S g t := r ^ (4 ^ e) with hh
  have hh3 : (h : S.O) ^ 3 = 1 := by
    rw [hh, Subgroup.coe_pow, ← pow_mul, show 4 ^ e * 3 = 3 * 2 ^ e * 2 ^ e by
      rw [show (4 : ℕ) = 2 * 2 by rfl, mul_pow]; ring, pow_mul, pow_mul, hpow, one_pow]
  have hπh : F.π h = γ := by
    rw [hh, map_pow, hr, pow_four_pow_of_cube hγ e]
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar h.2)
  have hkR : S.ρ k ∈ Rbar S g t := hk ▸ h.2
  refine ⟨k, hkR, by rw [hk]; exact hh3, ?_⟩
  have : (⟨S.ρ k, hkR⟩ : Rbar S g t) = h := Subtype.ext hk
  rw [this, hπh]

theorem φ_resV_aV (r : Rbar S g t) : F.φ (resV X.haQ t r (aV X.ht)) = act (F.π r) E00 := by
  rw [F.compat, F.base]

end Frame

theorem bV_eq_resV (X : Hyp10 S g t) {k : S.M} (hk : S.ρ k ∈ Rbar S g t)
    (hth : t ∈ S.Lbar ((k : G) * g)) :
    bV hth = resV X.haQ t ⟨S.ρ k, hk⟩ (aV X.ht) :=
  Subtype.ext (by rw [coe_bV, coe_resV_apply]; exact (ρ_cl_conj_z S k X.haQ).symm)

theorem Abar_inf_Lbar_conj (X : Hyp10 S g t) (F : Frame X) {k : S.M}
    (hk : S.ρ k ∈ Rbar S g t) (hkW : S.ρ k ∈ fixWstar X)
    (hs : (F.π ⟨S.ρ k, hk⟩).2 = 1) (hs3 : (F.π ⟨S.ρ k, hk⟩) ^ 3 = 1)
    (hs1 : F.π ⟨S.ρ k, hk⟩ ≠ 1) :
    (S.Lbar g ⊓ Nbar S g t) ⊓ S.Lbar ((k : G) * g) = zpowers t := by
  have hth := mem_Lbar_mul_of_mem_Rbar X.H X.ht hk
  have hVQk := not_V_le_Qa_mul X.H X.hVQ hk
  have d1 := finrank_clSub_inf_Wt X.H X.C X.ht X.ht1 X.hVQ
  have d2 := finrank_clSub_inf_Wt (X.H.mul k) (X.C.mul k) hth X.ht1 hVQk
  rw [Wt_mul] at d2
  have d3 := finrank_sup_Vt X.H X.C X.ht X.ht1 X.hVQ
  have e1 := finrank_clSub_inf_Vt X.H X.C X.ht X.ht1 X.hVQ
  have e2 := finrank_clSub_inf_Vt (X.H.mul k) (X.C.mul k) hth X.ht1 hVQk
  rw [Vt_mul] at e2
  have h4 := X.h4
  have hsub : S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t ≤
      (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t := by
    intro w hw
    have hkinv : (S.ρ k)⁻¹ ∈ Rbar S g t := inv_mem hk
    have hw1 : (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈
        S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t :=
      ⟨(mem_clSub_Qa_mul_iff k).mp hw.1, apply_mem_Wt X.H hkinv hw.2⟩
    have hw2 := hkW.2 _ hw1.2
    rw [apply_inv_apply_O] at hw2
    have e : w = (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w +
        (w - (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by abel
    rw [e]
    exact add_mem (Submodule.mem_sup_left hw1) (Submodule.mem_sup_right hw2)
  have hc : S.width ≤ finrank (ZMod 2) ↥((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊓
      (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t)) + 2 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t)
      (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t)
    have h2 := Submodule.finrank_mono (sup_le le_sup_left hsub)
    omega
  obtain ⟨m, hm1, hm2⟩ := exists_pf_sep_Γ₁ _ hs hs3 hs1
  set y : Vt S g t := F.φ.symm m with hy
  have hyA : (y : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    rw [← beta_aV_eq_zero_iff X.H X.C X.ht X.ht1 X.hVQ, F.beta_eq, F.base, hy,
      LinearEquiv.apply_symm_apply]
    exact hm1
  have hyC : (y : S.Qt) ∉ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) := by
    rw [← beta_bV_eq_zero_iff X.H X.C X.ht X.ht1 X.hVQ hk hth, F.beta_eq,
      bV_eq_resV X hk hth, F.φ_resV_aV, hy, LinearEquiv.apply_symm_apply, hm2]
    exact one_ne_zero
  have hd : finrank (ZMod 2) ↥((S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊓
      (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Vt S g t)) ≤ 2 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t)
      (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Vt S g t)
    have h2 : finrank (ZMod 2) ↥((S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊔
        (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Vt S g t)) ≤ 4 := by
      rw [← h4]
      exact Submodule.finrank_mono (sup_le inf_le_right inf_le_right)
    have hlt : S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Vt S g t <
        (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊔
          (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Vt S g t) := by
      refine lt_of_le_of_ne le_sup_right fun heq => hyC ?_
      have : (y : S.Qt) ∈ (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊔
          (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Vt S g t) :=
        Submodule.mem_sup_left ⟨hyA, y.2⟩
      rw [← heq] at this
      exact this.1
    have h3 := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have he : S.width ≤ finrank (ZMod 2) ↥((S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊔
      ((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊓
        (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t))) + 1 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t)
      ((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊓ (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t))
    have h2 : (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊓ ((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊓
        (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t)) ≤
          (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊓ (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Vt S g t) :=
      fun v hv => ⟨hv.1, hv.2.2.1, hv.1.2⟩
    have h3 := Submodule.finrank_mono h2
    omega
  set K' := (S.Lbar g ⊓ Nbar S g t) ⊓ S.Lbar ((k : G) * g) with hK'
  have hK'L : K' ≤ S.Lbar g := inf_le_left.trans inf_le_left
  have hca : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹) := by
    intro heq
    have h1 : F.φ (bV hth) = F.φ (aV X.ht) := congrArg F.φ (Subtype.ext heq)
    rw [bV_eq_resV X hk hth, F.φ_resV_aV, F.base] at h1
    exact E00_ne_zero (fpf_Γ₁ _ hs hs3 hs1 E00 h1)
  have hCfix : (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) ⊔ ((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊓
      (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t)) ≤
        S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S K' := by
    refine sup_le (fun v hv => ⟨hv.1, fun x hx => (mem_Nbar.mp hx.1.2).2 v hv.2⟩)
      (fun v hv => ⟨hv.1.1, fun x hx => ?_⟩)
    have h1 := Lbar_apply_sub_mem_span' X.haQ hv.1.1 hx.1.1
    have h2 := Lbar_apply_sub_mem_span' (conj_mem_QG' S k.2 X.haQ) hv.2.1 hx.2
    rcases mem_span_cl_iff.mp h1 with h0 | ha
    · exact sub_eq_zero.mp h0
    · rcases mem_span_cl_iff.mp h2 with h0 | hc'
      · exact sub_eq_zero.mp h0
      · exact absurd (hc'.symm.trans ha) hca
  have hcard := card_mul_two_pow_finrank_fix X.H X.C hK'L
  have hf := Submodule.finrank_mono hCfix
  have hK'2 : Nat.card K' ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have h1 : 2 ^ (S.width - 1) ≤ 2 ^ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S K') :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 3 * 2 ^ (S.width - 1) ≤ 2 ^ S.width := by
      rw [← hcard]
      exact Nat.mul_le_mul hcon h1
    have h3 : 2 ^ S.width = 2 * 2 ^ (S.width - 1) := by
      rw [← pow_succ']
      congr 1
      have := X.five_le_width
      omega
    have h5 : 0 < 2 ^ (S.width - 1) := by positivity
    rw [h3] at h2
    omega
  have hle : zpowers t ≤ K' :=
    (zpowers_le).mpr ⟨X.t_mem_Abar, mem_Lbar_mul_of_mem_Rbar X.H X.ht hk⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, X.orderOf_t]
  exact hK'2

end CFSG.LargeExtraspecial.S10
