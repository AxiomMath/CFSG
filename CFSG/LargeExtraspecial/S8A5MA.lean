module

public import CFSG.LargeExtraspecial.S8A5M
public import CFSG.LargeExtraspecial.S8A5A
public import CFSG.LargeExtraspecial.S8A5C

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem apply_sub_mem_Vt_of_mem_Xa (H : Hyp4 S g) (ht : t ∈ S.Lbar g) {l : S.O}
    (hl : l ∈ S.Lbar g) {c : S.Qt}
    (hc : c ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ⊔ Vt S g t) :
    (l : S.Qt ≃ₗ[ZMod 2] S.Qt) c - c ∈ Vt S g t := by
  obtain ⟨p, hp, v, hv, rfl⟩ := Submodule.mem_sup.mp hc
  rw [map_add, show (l : S.Qt ≃ₗ[ZMod 2] S.Qt) p + (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - (p + v) =
    ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) + ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) by abel]
  refine add_mem ?_ (sub_mem (apply_mem_Vt_of_mem_Rbar H.conj_mem (Lbar_le_Rbar ht hl) hv) hv)
  exact (Submodule.span_singleton_le_iff_mem _ _).mpr (cl_a_mem_Vt ht)
    (Lbar_apply_sub_mem_span' H.conj_mem hp.1 hl)

theorem apply_sub_mem_Xa_of_mem_Wt (H : Hyp4 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g)
    {l : S.O} (hl : l ∈ S.Lbar g) {y : S.Qt} (hy : y ∈ Wt S g t) :
    (l : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ⊔ Vt S g t :=
  Submodule.mem_sup_left ⟨apply_sub_mem_clSub_of_mem_Wt C (cl_a_mem_Vt ht) H.conj_mem hy hl,
    sub_mem (apply_mem_Wt H (Lbar_le_Rbar ht hl) hy) hy⟩

theorem forall_apply_sub_mem_Vt_of_not_mem_Nbar (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) {Y : Submodule (ZMod 2) S.Qt} (hYW : Y ≤ Wt S g t)
    (hY : ∀ r ∈ Rbar S g t, ∀ u ∈ Y, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ Y)
    {l : S.O} (hl : l ∈ S.Lbar g) (hlN : l ∉ Nbar S g t) {y : S.Qt} (hy : y ∈ Y)
    (hly : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y ∈ Vt S g t) :
    ∀ l' ∈ S.Lbar g, (l' : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y ∈ Vt S g t := by
  have haQ := H.conj_mem
  obtain ⟨ρ, hρ, hD⟩ := timmesfeld_6_1_two hCE H hNo C ht ht1 hVQ hΩ D.hh D.hb D.hX D.hE
  have hUinv := map_mkQ_invariant D hρ hYW hY
  have hres : ∀ l' (hl' : l' ∈ S.Lbar g),
      resV haQ t ⟨l', Lbar_le_Rbar ht hl'⟩ ∈ omegaGroup D.Q D.hQ := fun l' hl' => by
    rw [← D.hX, ← range_resV haQ t]; exact ⟨_, rfl⟩
  have hrad : ∀ l' (hl' : l' ∈ S.Lbar g),
      resV haQ t ⟨l', Lbar_le_Rbar ht hl'⟩ ∈ radFix D.Q ⊥ (aV ht) := fun l' hl' => by
    rw [radFix_bot, ← D.hE]; exact ⟨l', hl', fun v => rfl⟩
  have hx1 : resV haQ t ⟨l, Lbar_le_Rbar ht hl⟩ ≠ 1 := fun h =>
    hlN ((resV_eq_one_iff haQ _).mp h)
  have hmin' : IsMinusType D.Q ⊥ 2 := fun T _ hT => by
    have h := hmin T hT
    rwa [hm2] at h
  have hxa : ¬ IsTypeA D.Q (resV haQ t ⟨l, Lbar_le_Rbar ht hl⟩) 2 :=
    not_isTypeA_of_minus_two D.hQ hmin' (aV_ne_zero H ht) D.hQa D.polar_aV_bV
      (by rw [← radFix_bot]; exact hrad l hl) hx1
  have hb0 := (timmesfeld_2_1_b0_of_invariant ρ D.hm D.hdim (aV_ne_zero H ht) D.hQa D.Q_bV
    D.polar_aV_bV hD hUinv ⟨_, hres l hl⟩ (hrad l hl) hx1 hxa).1
  have hyW := hYW hy
  have hfx : ρ ⟨_, hres l hl⟩ (secMk (Vt S g t) hyW) = secMk (Vt S g t) hyW := by
    apply Subtype.ext
    rw [hρ ⟨_, hres l hl⟩ ⟨l, Lbar_le_Rbar ht hl⟩ rfl y hyW, coe_secMk, ← sub_eq_zero,
      ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hly
  have hmem : secMk (Vt S g t) hyW ∈
      (Y.map (Vt S g t).mkQ).comap ((Wt S g t).map (Vt S g t).mkQ).subtype ⊓
        fixSpace (ρ ⟨_, hres l hl⟩) := ⟨⟨y, hy, rfl⟩, mem_fixSpace.mpr hfx⟩
  rw [hb0] at hmem
  intro l' hl'
  have h' := congrArg Subtype.val (hmem.2 ⟨_, hres l' hl'⟩ (hrad l' hl'))
  rw [hρ ⟨_, hres l' hl'⟩ ⟨l', Lbar_le_Rbar ht hl'⟩ rfl y hyW, coe_secMk] at h'
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
  change (Vt S g t).mkQ _ - (Vt S g t).mkQ y = 0
  rw [h', sub_self]

theorem finrank_inf_Xa_of_invariant (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) {Y : Submodule (ZMod 2) S.Qt}
    (hVY : Vt S g t ≤ Y) (hYW : Y ≤ Wt S g t)
    (hY : ∀ r ∈ Rbar S g t, ∀ u ∈ Y, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ Y)
    (hdimY : finrank (ZMod 2) Y = finrank (ZMod 2) (Vt S g t) + 4) :
    finrank (ZMod 2) ↥(Y ⊓ (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ⊔ Vt S g t)) =
      finrank (ZMod 2) (Vt S g t) + 2 := by
  obtain ⟨-, -, htwo⟩ := finrank_map_mkQ_of_invariant hCE hNo hΩ D hVY hYW hY
  have e2 := finrank_map_add_finrank_inf_ker (Vt S g t).mkQ Y
  rw [Submodule.ker_mkQ, inf_eq_right.mpr hVY] at e2
  have hVYX : Vt S g t ≤ Y ⊓ (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ⊔ Vt S g t) :=
    le_inf hVY le_sup_right
  have e3 := finrank_map_add_finrank_inf_ker (Vt S g t).mkQ
    (Y ⊓ (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ⊔ Vt S g t))
  rw [Submodule.ker_mkQ, inf_eq_right.mpr hVYX] at e3
  omega

theorem exists_pair_not_mem_Nbar (H : Hyp4 S g) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2) :
    ∃ l₁ ∈ S.Lbar g, ∃ l₂ ∈ S.Lbar g,
      l₁ ∉ Nbar S g t ∧ l₂ ∉ Nbar S g t ∧ l₁ * l₂ ∉ Nbar S g t := by
  have hcard : Nat.card (pointRadical D.Q (aV ht)) = 4 := by
    rw [card_pointRadical D.hQ (aV_ne_zero H ht) D.hQa, D.hdim, hm2]
    norm_num
  have := isElementaryAbelian_pointRadical D.hQ (aV_ne_zero H ht) D.hQa
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  obtain ⟨e₁, he₁, he₁1⟩ : ∃ e₁ ∈ pointRadical D.Q (aV ht), e₁ ≠ 1 := by
    by_contra h
    push Not at h
    rw [(Subgroup.eq_bot_iff_forall _).mpr h, Subgroup.card_bot] at hcard
    omega
  have hsq : e₁ ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian e₁ he₁
  obtain ⟨e₂, he₂, he₂K⟩ : ∃ e₂ ∈ pointRadical D.Q (aV ht), e₂ ∉ zpowers e₁ := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (fun e he => h e he :
      pointRadical D.Q (aV ht) ≤ zpowers e₁)
    rw [hcard, Nat.card_zpowers] at h1
    have h2 := orderOf_le_of_pow_eq_one (by norm_num) hsq
    omega
  rw [← D.hE] at he₁ he₂
  obtain ⟨l₁, hl₁, he₁l⟩ := he₁
  obtain ⟨l₂, hl₂, he₂l⟩ := he₂
  have hfix : ∀ {e : Vt S g t ≃ₗ[ZMod 2] Vt S g t} {l : S.O},
      (∀ v : Vt S g t, ((e v : Vt S g t) : S.Qt) = (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v) →
      l ∈ Nbar S g t → e = 1 := fun hel hl =>
    LinearEquiv.ext fun v => Subtype.ext ((hel v).trans ((mem_Nbar.mp hl).2 v v.2))
  refine ⟨l₁, hl₁, l₂, hl₂, fun h => he₁1 (hfix he₁l h), fun h => he₂K ?_, fun h => he₂K ?_⟩
  · rw [hfix he₂l h]
    exact one_mem _
  · have h12 : e₁ * e₂ = 1 := hfix (l := l₁ * l₂) (fun v => by
      rw [LinearEquiv.mul_apply, he₁l, he₂l, coe_mul_apply]) h
    rw [eq_inv_of_mul_eq_one_right h12]
    exact inv_mem (mem_zpowers e₁)

theorem apply_cl_b_ne (H : Hyp4 S g) (D : Std H C ht ht1 hVQ) {l : S.O} (hl : l ∈ S.Lbar g)
    (hlN : l ∉ Nbar S g t) (μ ν : ZMod 2) :
    (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((D.h : G) * g * S.z * ((D.h : G) * g)⁻¹)) ≠
      μ • S.cl (g * S.z * g⁻¹) + ν • S.cl ((D.h : G) * g * S.z * ((D.h : G) * g)⁻¹) := by
  have haQ := H.conj_mem
  have he : resV haQ t ⟨l, Lbar_le_Rbar ht hl⟩ ∈ pointRadical D.Q (aV ht) := by
    rw [← D.hE]; exact ⟨l, hl, fun v => rfl⟩
  have he1 : resV haQ t ⟨l, Lbar_le_Rbar ht hl⟩ ≠ 1 := fun h =>
    hlN ((resV_eq_one_iff haQ _).mp h)
  have h := apply_not_mem_span_pair_of_mem_pointRadical D.hQ (aV_ne_zero H ht) D.hQa
    D.polar_aV_bV he he1
  intro heq
  refine h (Submodule.mem_span_pair.mpr ⟨μ, ν, Subtype.ext ?_⟩)
  rw [coe_resV_apply]
  exact heq.symm

theorem rank_dichotomy_A5 (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) {x σ : S.O} (hxM : x ∈ S.Mbar) (hxσ : σ = x * t * x⁻¹)
    (hσt : σ * t = t * σ) (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hgood : Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (hU : (Wt S g t).map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t =
      Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt))
    {w : S.O} (hwA : w ∈ S.Lbar g ⊓ Nbar S g t) :
    (∀ y ∈ Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt),
        (w : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) ∨
      finrank (ZMod 2) ↥(commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
        fixSpace (w : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 1 := by
  have hσM : σ ∈ S.Mbar := by
    rw [hxσ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  obtain ⟨Y, hYdef⟩ : ∃ Y : Submodule (ZMod 2) S.Qt,
      Y = Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : Submodule (ZMod 2) S.Qt,
      X = S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ⊔ Vt S g t := ⟨_, rfl⟩
  have hYinv : ∀ r ∈ Rbar S g t, ∀ u ∈ Y, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ Y := by
    rw [hYdef, ← hU]; exact comm_sup_Vt_invariant D hσM hσt hσV
  have hVY : Vt S g t ≤ Y := hYdef ▸ le_sup_left
  have hYW : Y ≤ Wt S g t := hYdef ▸ sup_le (Vt_le_Wt H ht1) (commSpace_le_Wt_of_fix hσV)
  have hdimσ : finrank (ZMod 2) (commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t) := by
    rw [hxσ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj',
      (commSpace_t_eq H C ht ht1 hVQ).1]
  have hdimY : finrank (ZMod 2) Y = finrank (ZMod 2) (Vt S g t) + 4 := by
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq (Vt S g t)
      (commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt))
    rw [hgood, finrank_bot, ← hYdef] at e1
    have := D.hdim
    rw [hm2] at this
    omega
  have hdimC : finrank (ZMod 2) ↥(Y ⊓ X) = finrank (ZMod 2) (Vt S g t) + 2 :=
    hXdef ▸ finrank_inf_Xa_of_invariant hCE hNo hΩ D hVY hYW hYinv hdimY
  have hPI := pairInt_of_radBound H C ht ht1 hVQ D.hR
  obtain ⟨l₁, hl₁, l₂, hl₂, hl₁N, hl₂N, hl₁₂N⟩ := exists_pair_not_mem_Nbar H D hm2
  have hF : ∀ l ∈ S.Lbar g, l ∉ Nbar S g t → ∀ y ∈ Y,
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y ∈ Vt S g t → y ∈ Y ⊓ X :=
    fun l hl hlN y hy hly => ⟨hy, hXdef ▸ (forall_apply_sub_mem_Vt_iff_a H hNo C ht ht1 hVQ
      D.hh D.hb hPI (hYW hy)).mp (forall_apply_sub_mem_Vt_of_not_mem_Nbar hCE hNo hΩ D hm2
        hmin hYW hYinv hl hlN hy hly)⟩
  have hwV : ∀ v ∈ Vt S g t, (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := (mem_Nbar.mp hwA.2).2
  rcases rank_lemma_A5 (V := Vt S g t) (Y := Y) (C := Y ⊓ X) (a := S.cl (g * S.z * g⁻¹))
      (L := (fun l : S.O => (l : S.Qt ≃ₗ[ZMod 2] S.Qt)) '' (S.Lbar g : Set S.O))
      (w := (w : S.Qt ≃ₗ[ZMod 2] S.Qt)) (le_inf hVY (hXdef ▸ le_sup_right)) inf_le_left hdimC
      (by
        rintro _ ⟨l, hl, rfl⟩ y hy
        exact ⟨sub_mem (hYinv l (Lbar_le_Rbar ht hl) y hy) hy,
          hXdef ▸ apply_sub_mem_Xa_of_mem_Wt H C ht hl (hYW hy)⟩)
      (by
        rintro _ ⟨l, hl, rfl⟩ c hc
        exact apply_sub_mem_Vt_of_mem_Xa H ht hl (hXdef ▸ hc.2))
      hwV
      (by
        rintro _ ⟨l, hl, rfl⟩
        exact congrArg Subtype.val (S.Lbar_comm H.conj_mem hl hwA.1))
      (fun v hv => by
        have h : v ∈ fixSub S (S.Lbar g) := fun l hl => hv _ ⟨l, hl, rfl⟩
        rwa [H.fixSub_eq] at h)
      ⟨l₁, hl₁, rfl⟩ ⟨l₂, hl₂, rfl⟩ (hF l₁ hl₁ hl₁N) (hF l₂ hl₂ hl₂N)
      (hF (l₁ * l₂) (mul_mem hl₁ hl₂) hl₁₂N) with h | h
  · exact Or.inl (hYdef ▸ h)
  · right
    have h2 := finrank_sup_inf_fixSpace hgood (fun v hv => mem_fixSpace.mpr (hwV v hv))
    rw [← hYdef, h] at h2
    omega

end CFSG.LargeExtraspecial.S8
