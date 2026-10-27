module

public import CFSG.LargeExtraspecial.S4FiveBeta
public import CFSG.LargeExtraspecial.S4OmegaQ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2

section Abstract

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {β : LinearMap.BilinForm (ZMod 2) U}

theorem card_ge_of_le_spPointRadical (hβ : β.IsAlt) (hnd : β.Nondegenerate) {b : U} (hb : b ≠ 0)
    {E : Subgroup (U ≃ₗ[ZMod 2] U)} (hEU : E ≤ spPointRadical β b)
    (hfix : ∀ u, β b u = 0 → (∀ e ∈ E, e u = u) → u ∈ (ZMod 2) ∙ b) :
    2 ^ (finrank (ZMod 2) U - 2) ≤ Nat.card E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite U := Module.finite_of_finite (ZMod 2)
  have : Finite (U ≃ₗ[ZMod 2] U) := finite_linearEquiv_of_finite
  set A : Submodule (ZMod 2) U := LinearMap.ker (β b) with hA
  have hAinv : ∀ (e : E) u, u ∈ A → E.subtype e u ∈ A := by
    intro e u hu
    have h1 := hEU e.2
    rw [LinearMap.mem_ker] at hu ⊢
    rw [← h1.2.1, coe_subtype, TauCeti.BilinForm.mem_isometryGroup_iff.mp h1.1]
    exact hu
  set ψ := restrictHom E.subtype A hAinv with hψ
  have hbA : b ∈ A := LinearMap.mem_ker.mpr (hβ.self_eq_zero b)
  have hψc : ∀ e (u : A), ψ e u - u ∈ (ZMod 2) ∙ (⟨b, hbA⟩ : A) := by
    intro e u
    rw [mem_span_singleton_subtype]
    exact (hEU e.2).2.2.1 u (LinearMap.mem_ker.mp u.2)
  have hEp : IsPGroup 2 E :=
    (IsPGroup.of_card (card_spPointRadical hβ hnd hb)).to_le hEU
  obtain ⟨hcard, -⟩ := card_range_of_transvections hEp ψ _ hψc
  have hb0 : (⟨b, hbA⟩ : A) ≠ 0 := fun h => hb (congrArg Subtype.val h)
  have hfix' : finrank (ZMod 2) (fixSpaceOf ψ.range) ≤ 1 := by
    have hle : fixSpaceOf ψ.range ≤ (ZMod 2) ∙ (⟨b, hbA⟩ : A) := by
      intro u hu
      rw [mem_fixSpaceOf_range] at hu
      rw [mem_span_singleton_subtype]
      exact hfix u (LinearMap.mem_ker.mp u.2) fun e he => congrArg Subtype.val (hu ⟨e, he⟩)
    exact (Submodule.finrank_mono hle).trans (finrank_span_singleton hb0).le
  have hβ0 : β b ≠ 0 := fun h0 => hb (hnd.1 _ fun y => by rw [h0, LinearMap.zero_apply])
  have hrange : LinearMap.range (β b) = ⊤ := by
    obtain ⟨y, hy⟩ : ∃ y, β b y ≠ 0 := by
      by_contra h
      push Not at h
      exact hβ0 (LinearMap.ext h)
    have hy1 := zmod2_eq_one_of_ne_zero hy
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • y, by rw [map_smul, hy1, smul_eq_mul, mul_one]⟩
  have hdimA := LinearMap.finrank_range_add_finrank_ker (β b)
  rw [hrange, finrank_top, finrank_self, ← hA] at hdimA
  have hle := Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd ψ)
  rw [hcard] at hle
  refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) hle
  omega

end Abstract

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S) in
@[expose] def LhmodN (g : G) (t : S.O) (h : S.M) : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t) where
  carrier := {e | ∃ x ∈ S.Lbar ((h : G) * g), ∀ v : Vt S g t, ((e v : Vt S g t) : S.Qt) =
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v}
  mul_mem' := by
    rintro e f ⟨x, hx, hex⟩ ⟨y, hy, hfy⟩
    refine ⟨x * y, mul_mem hx hy, fun v => ?_⟩
    rw [LinearEquiv.mul_apply, hex, hfy]
    rfl
  one_mem' := ⟨1, one_mem _, fun v => rfl⟩
  inv_mem' := by
    rintro e ⟨x, hx, hex⟩
    refine ⟨x⁻¹, inv_mem hx, fun v => ?_⟩
    have h1 := hex (e⁻¹ v)
    rw [show e (e⁻¹ v) = v from e.apply_symm_apply v] at h1
    rw [h1, inv_apply_apply_O]

@[expose] noncomputable def bV {t : S.O} {h : S.M} (hth : t ∈ S.Lbar ((h : G) * g)) : Vt S g t :=
  ⟨S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹), cl_mem_Vt hth⟩

theorem coe_bV {t : S.O} {h : S.M} (hth : t ∈ S.Lbar ((h : G) * g)) :
    (bV hth : S.Qt) = S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) :=
  rfl

theorem bV_ne_zero (H : Hyp4 S g) {t : S.O} {h : S.M} (hth : t ∈ S.Lbar ((h : G) * g)) :
    bV hth ≠ 0 := fun h0 =>
  cl_conj_z_ne_zero S (H.mul h).conj_mem (H.mul h).conj_ne (congrArg Subtype.val h0)

theorem LhmodN_le_RmodN {t : S.O} {h : S.M} (hth : t ∈ S.Lbar ((h : G) * g)) :
    LhmodN S g t h ≤ RmodN S g t := by
  rintro e ⟨x, hx, hex⟩
  exact ⟨x, Lbar_mul_le_Rbar hth hx, hex⟩

theorem resV_mem_LhmodN (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} {h : S.M}
    (hth : t ∈ S.Lbar ((h : G) * g)) {x : S.O} (hx : x ∈ S.Lbar ((h : G) * g)) :
    resV haQ t ⟨x, Lbar_mul_le_Rbar hth hx⟩ ∈ LhmodN S g t h :=
  ⟨x, hx, fun v => coe_resV_apply haQ _ v⟩

theorem coe_inv_apply_of_forall {t : S.O} {e : Vt S g t ≃ₗ[ZMod 2] Vt S g t} {x : S.O}
    (hex : ∀ v : Vt S g t, ((e v : Vt S g t) : S.Qt) = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
    (v : Vt S g t) :
    ((e⁻¹ v : Vt S g t) : S.Qt) = ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
  have h1 := hex (e⁻¹ v)
  rw [show e (e⁻¹ v) = v from e.apply_symm_apply v] at h1
  rw [h1, inv_apply_apply_O]

theorem LhmodN_eq_map_conj (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) {h : S.M}
    (hth : t ∈ S.Lbar ((h : G) * g)) {e : Vt S g t ≃ₗ[ZMod 2] Vt S g t} (he : e ∈ RmodN S g t)
    (hea : e (aV ht) = bV hth) :
    LhmodN S g t h = (LmodN S g t).map (MulAut.conj e).toMonoidHom := by
  obtain ⟨x, hx, hex⟩ := he
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hx)
  have hcl : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) =
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
    rw [← ρ_cl_conj_z S k H.conj_mem, ← coe_bV hth, ← hea, hex]
    rfl
  have hL : S.Lbar ((h : G) * g) = (S.Lbar g).map (MulAut.conj (S.ρ k)).toMonoidHom := by
    rw [← Lbar_mul S k g]
    exact (Lbar_eq_of_cl_eq S (H.mul h).conj_mem (H.mul h).conj_ne (H.mul k).conj_mem hcl).symm
  ext f
  rw [mem_map]
  constructor
  · rintro ⟨y, hy, hfy⟩
    rw [hL, mem_map] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    refine ⟨e⁻¹ * f * e, ⟨y', hy', fun v => ?_⟩, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, coe_inv_apply_of_forall hex, hfy, hex]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [coe_mul_apply, coe_mul_apply, ← coe_mul_apply (S.ρ k)⁻¹, inv_mul_cancel,
      inv_apply_apply_O]
    rfl
  · rintro ⟨f', ⟨y', hy', hfy'⟩, rfl⟩
    refine ⟨S.ρ k * y' * (S.ρ k)⁻¹, ?_, fun v => ?_⟩
    · rw [hL]
      exact ⟨y', hy', rfl⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hex, hfy', coe_inv_apply_of_forall hex,
        coe_mul_apply, coe_mul_apply]

theorem RmodN_le_closure_conj (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hD : ∀ (h : S.M) (hth : t ∈ S.Lbar ((h : G) * g)),
      bV hth ∈ orbitOf (RmodN S g t) (aV ht)) :
    RmodN S g t ≤ closure {u | ∃ x ∈ RmodN S g t, ∃ e ∈ LmodN S g t, u = x * e * x⁻¹} := by
  set P := closure {u | ∃ x ∈ RmodN S g t, ∃ e ∈ LmodN S g t, u = x * e * x⁻¹} with hP
  let K : Subgroup S.O :=
    { carrier := {r | r ∈ Rbar S g t ∧ ∃ e ∈ P, ∀ v : Vt S g t,
        ((e v : Vt S g t) : S.Qt) = (r : S.Qt ≃ₗ[ZMod 2] S.Qt) v}
      mul_mem' := by
        rintro r s ⟨hr, e, he, hre⟩ ⟨hs, f, hf, hsf⟩
        refine ⟨mul_mem hr hs, e * f, mul_mem he hf, fun v => ?_⟩
        rw [LinearEquiv.mul_apply, hre, hsf]
        rfl
      one_mem' := ⟨one_mem _, 1, one_mem _, fun v => rfl⟩
      inv_mem' := by
        rintro r ⟨hr, e, he, hre⟩
        exact ⟨inv_mem hr, e⁻¹, inv_mem he, coe_inv_apply_of_forall hre⟩ }
  have hRK : Rbar S g t ≤ K := by
    refine sSup_le fun X hX => ?_
    obtain ⟨h, rfl, hth⟩ := hX
    intro y hy
    refine ⟨Lbar_mul_le_Rbar hth hy, resV H.conj_mem t ⟨y, Lbar_mul_le_Rbar hth hy⟩, ?_,
      fun v => coe_resV_apply H.conj_mem _ v⟩
    obtain ⟨e₀, he₀, he₀a⟩ := hD h hth
    have hmem := resV_mem_LhmodN H.conj_mem hth hy
    rw [LhmodN_eq_map_conj H ht hth he₀ he₀a, mem_map] at hmem
    obtain ⟨f, hf, hfe⟩ := hmem
    rw [← hfe]
    exact subset_closure ⟨e₀, he₀, f, hf, rfl⟩
  intro u ⟨r, hr, hur⟩
  obtain ⟨-, e, he, hre⟩ := hRK hr
  have : u = e := LinearEquiv.ext fun v => Subtype.ext (by rw [hur, hre])
  rw [this]
  exact he

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g)
include H C ht ht1 hVQ

theorem mem_clSub_of_beta_bV_eq_zero {h : S.M} (hth : t ∈ S.Lbar ((h : G) * g)) {y : Vt S g t}
    (hy : beta H C ht ht1 hVQ (bV hth) y = 0) :
    (y : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) := by
  obtain ⟨y', hy'⟩ := exists_t_sub_eq H C ht ht1 hVQ y
  rw [beta_apply H C ht ht1 hVQ _ _ hy'] at hy
  obtain ⟨w, hwQ, rfl⟩ := S.exists_cl y'
  have hwa : w ∈ S.QG ⊓ centralizer ({(h : G) * g * S.z * ((h : G) * g)⁻¹} : Set G) :=
    ⟨hwQ, mem_centralizer_singleton_iff.mpr
      ((S.polar_cl_eq_zero_iff (H.mul h).conj_mem hwQ).mp hy).symm⟩
  rw [← hy']
  exact (C.mul h).comm_le w hwa t hth

theorem LhmodN_le_spPointRadical {h : S.M} (hth : t ∈ S.Lbar ((h : G) * g)) :
    LhmodN S g t h ≤ spPointRadical (beta H C ht ht1 hVQ) (bV hth) := by
  intro e he
  have heR := LhmodN_le_RmodN hth he
  have hiso := RmodN_le_isometryGroup H C ht ht1 hVQ heR
  obtain ⟨s, hs, hes⟩ := he
  have hea : e (bV hth) = bV hth := Subtype.ext (by
    rw [hes]
    exact (mem_fixSub S).mp (by rw [(H.mul h).fixSub_eq]; exact Submodule.mem_span_singleton_self _)
      s hs)
  refine ⟨hiso, hea, fun x hx => ?_, fun v => ?_⟩
  · rw [mem_span_singleton_subtype]
    have hxP := mem_clSub_of_beta_bV_eq_zero H C ht ht1 hVQ hth hx
    obtain ⟨w, hw, -, hwx⟩ := S.mem_clSub_iff.mp hxP
    have := Lbar_apply_sub_mem_span (H.mul h).conj_mem hw hs
    rw [hwx] at this
    change ((e x : Vt S g t) : S.Qt) - x ∈ _
    rw [hes]
    exact this
  · have h1 := TauCeti.BilinForm.mem_isometryGroup_iff.mp hiso (bV hth) v
    rw [hea] at h1
    rw [map_sub, h1, sub_self]

theorem card_LhmodN_ge {h : S.M} (hth : t ∈ S.Lbar ((h : G) * g)) :
    2 ^ (finrank (ZMod 2) (Vt S g t) - 2) ≤ Nat.card (LhmodN S g t h) := by
  refine card_ge_of_le_spPointRadical (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) (bV_ne_zero H hth)
    (LhmodN_le_spPointRadical H C ht ht1 hVQ hth) fun u _ hu => ?_
  rw [mem_span_singleton_subtype]
  change (u : S.Qt) ∈ (ZMod 2) ∙ S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)
  rw [← (H.mul h).fixSub_eq]
  intro s hs
  have := congrArg Subtype.val (hu _ (resV_mem_LhmodN H.conj_mem hth hs))
  rw [coe_resV_apply] at this
  exact this

end CFSG.LargeExtraspecial.S4
