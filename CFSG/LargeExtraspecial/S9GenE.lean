module

public import CFSG.LargeExtraspecial.S9GenD
public import CFSG.LargeExtraspecial.S9GenC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
open CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_of_mem_nqSub {t : S.O} [NQHyp S g t] {X : Subgroup S.O} {m : NQ S g t}
    (hm : m ∈ nqSub S g t X) : ∃ x : Nbar S g t, (x : S.O) ∈ X ∧ nqMk x = m :=
  hm

theorem coe_fqHom_apply {t : S.O} [NQHyp S g t] (γ : GamF S g t)
    (w : nqSub S g t (Fbar S g t)) {x : Nbar S g t} (hxF : (x : S.O) ∈ Fbar S g t)
    (hx : nqMk x = (w : NQ S g t)) {x' : Nbar S g t}
    (hx' : (x' : S.O) = γ * x * (γ : S.O)⁻¹) :
    ((fqHom S g t γ w : nqSub S g t (Fbar S g t)) : NQ S g t) = nqMk x' := by
  have hw : w = ⟨nqMk x, ⟨x, hxF, rfl⟩⟩ := Subtype.ext hx.symm
  subst hw
  rw [coe_fqHom_mk γ hxF]
  have : nConjC (Subgroup.inclusion inf_le_left γ) x = x' := Subtype.ext (by
    rw [coe_nConjC, hx']
    rfl)
  rw [this]

section Trans

variable {t : S.O} [NQHyp S g t] (hFN : conjL S g t ⊆ Nbar S g t) {γ : S.O}
  (hγ : γ ∈ GamF S g t)
include hFN hγ

theorem fqHom_eq_or_eq {c : nqSub S g t (Fbar S g t)} {fc : Nbar S g t}
    (hfc : nqMk fc = (c : NQ S g t))
    (hact : ∀ x ∈ Fbar S g t, γ * x * γ⁻¹ = x ∨ γ * x * γ⁻¹ = x * fc)
    (w : nqSub S g t (Fbar S g t)) :
    fqHom S g t ⟨γ, hγ⟩ w = w ∨ fqHom S g t ⟨γ, hγ⟩ w = w + c := by
  have hw2 : ∃ y : Nbar S g t, (y : S.O) ∈ Fbar S g t ∧ nqMk y = (w : NQ S g t) :=
    exists_of_mem_nqSub w.2
  obtain ⟨x, hxF, hx⟩ := hw2
  have hxN : γ * x * γ⁻¹ ∈ Nbar S g t :=
    Fbar_le_of_subset hFN ((mem_normalizer_iff.mp (mem_GamF.mp hγ).2 _).mp hxF)
  have hval := coe_fqHom_apply ⟨γ, hγ⟩ w hxF hx (x' := ⟨_, hxN⟩) rfl
  have hx0 := hact x hxF
  rcases hx0 with h | h
  · left
    have e1 : (⟨_, hxN⟩ : Nbar S g t) = x := Subtype.ext h
    exact Subtype.ext (hval.trans ((congrArg nqMk e1).trans hx))
  · right
    have e1 : (⟨_, hxN⟩ : Nbar S g t) = x * fc := Subtype.ext h
    have e2 : nqMk (x * fc) = (w : NQ S g t) + (c : NQ S g t) :=
      (nqMk_mul x fc).trans (by rw [hx, hfc])
    exact Subtype.ext (hval.trans ((congrArg nqMk e1).trans e2))

theorem fqHom_fix {c : nqSub S g t (Fbar S g t)} {fc : Nbar S g t}
    (hfcF : (fc : S.O) ∈ Fbar S g t) (hfc : nqMk fc = (c : NQ S g t))
    (hfix : γ * fc * γ⁻¹ = fc) : fqHom S g t ⟨γ, hγ⟩ c = c := by
  have hfcN : γ * fc * γ⁻¹ ∈ Nbar S g t :=
    Fbar_le_of_subset hFN ((mem_normalizer_iff.mp (mem_GamF.mp hγ).2 _).mp hfcF)
  have hval := coe_fqHom_apply ⟨γ, hγ⟩ c hfcF hfc (x' := ⟨_, hfcN⟩) rfl
  have e1 : (⟨_, hfcN⟩ : Nbar S g t) = fc := Subtype.ext hfix
  exact Subtype.ext (hval.trans ((congrArg nqMk e1).trans hfc))

theorem fqHom_ne {v : nqSub S g t (Fbar S g t)} {fc fv : Nbar S g t}
    (hfvF : (fv : S.O) ∈ Fbar S g t) (hfv : nqMk fv = (v : NQ S g t))
    (hfc_t : (fc : S.O) ∉ zpowers t) (hmove : γ * fv * γ⁻¹ = fv * fc) :
    fqHom S g t ⟨γ, hγ⟩ v ≠ v := by
  intro he
  have hfvN : γ * fv * γ⁻¹ ∈ Nbar S g t :=
    Fbar_le_of_subset hFN ((mem_normalizer_iff.mp (mem_GamF.mp hγ).2 _).mp hfvF)
  have hval := coe_fqHom_apply ⟨γ, hγ⟩ v hfvF hfv (x' := ⟨_, hfvN⟩) rfl
  have e1 : (⟨_, hfvN⟩ : Nbar S g t) = fv * fc := Subtype.ext hmove
  have h1 : nqMk (fv * fc) = nqMk fv :=
    (congrArg nqMk e1).symm.trans (hval.symm.trans ((congrArg Subtype.val he).trans hfv.symm))
  have h2 : nqMk fv + nqMk fc = nqMk fv := (nqMk_mul fv fc).symm.trans h1
  exact hfc_t ((nqMk_eq_zero_iff fc).mp (add_eq_left.mp h2))

theorem exists_fqHom_actsTv_of_conj {c v : nqSub S g t (Fbar S g t)} (hc : c ≠ 0)
    {fc fv : Nbar S g t} (hfcF : (fc : S.O) ∈ Fbar S g t) (hfc : nqMk fc = (c : NQ S g t))
    (hfvF : (fv : S.O) ∈ Fbar S g t) (hfv : nqMk fv = (v : NQ S g t))
    (hfc_t : (fc : S.O) ∉ zpowers t)
    (hact : ∀ x ∈ Fbar S g t, γ * x * γ⁻¹ = x ∨ γ * x * γ⁻¹ = x * fc)
    (hfix : γ * fc * γ⁻¹ = fc) (hmove : γ * fv * γ⁻¹ = fv * fc) :
    ∃ γ : GamF S g t, ∃ μ : Dual (ZMod 2) (nqSub S g t (Fbar S g t)),
      μ c = 0 ∧ μ v ≠ 0 ∧ ActsTv (fqHom S g t) γ c μ := by
  have hμ0 := exists_actsTv_of_eq_or_eq hc (fqHom_eq_or_eq hFN hγ hfc hact)
  obtain ⟨μ, hμ⟩ := hμ0
  exact ⟨⟨γ, hγ⟩, μ, hμ.apply_eq_zero_of_fix hc (fqHom_fix hFN hγ hfcF hfc hfix),
    hμ.apply_ne_zero_of_ne (fqHom_ne hFN hγ hfvF hfv hfc_t hmove), hμ⟩

end Trans

section Step6

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
  [hN : NQHyp S g t] (hFN : conjL S g t ⊆ Nbar S g t)
  (hkey : ∀ τ ∈ conjL S g t, τ ≠ t → ∃ y ∈ Nbar S g t, y * τ * y⁻¹ = τ * t)
include H C ht hFN hkey

omit hN hFN in
theorem exists_Nbar_conj_eq_mul {f : S.O} (hf : f ∈ Fbar S g t) (hft : f ∉ zpowers t) :
    ∃ y ∈ Nbar S g t, y * f * y⁻¹ = f * t :=
  exists_conj_eq_mul_of_mem_Fbar H C ht (Nbar_le_Rbar.trans Rbar_le_Mbar) hkey hf hft

theorem exists_Nbar_fix_move {s u : S.O} (hsF : s ∈ Fbar S g t) (huF : u ∈ Fbar S g t)
    (hu : u ∉ zpowers t) (hus : u * s ∉ zpowers t) :
    ∃ y ∈ Nbar S g t, y * s * y⁻¹ = s ∧ y * u * y⁻¹ = u * t := by
  have haQ := H.conj_mem
  have hsN := Fbar_le_of_subset hFN hsF
  have hsL := Fbar_le_Lbar hsF
  have hst : s * t = t * s := Lbar_comm S haQ hsL ht
  have hyt : ∀ y ∈ Nbar S g t, y * t * y⁻¹ = t := fun y hy => by
    rw [commute_of_mem_Rbar haQ (Nbar_le_Rbar hy), mul_inv_cancel_right]
  obtain ⟨y₂, hy₂, h2u⟩ := exists_Nbar_conj_eq_mul H C ht hkey huF hu
  by_cases h2s : y₂ * s * y₂⁻¹ = s
  · exact ⟨y₂, hy₂, h2s, h2u⟩
  have h2s' := (conj_eq_or_eq_mul_t H ht hy₂ hsN hsL).resolve_left h2s
  obtain ⟨y₃, hy₃, h3us⟩ := exists_Nbar_conj_eq_mul H C ht hkey (mul_mem huF hsF) hus
  rcases conj_eq_or_eq_mul_t H ht hy₃ hsN hsL with h3s | h3s
  · refine ⟨y₃, hy₃, h3s, ?_⟩
    calc y₃ * u * y₃⁻¹ = (y₃ * (u * s) * y₃⁻¹) * (y₃ * s * y₃⁻¹)⁻¹ := by group
      _ = u * (s * t) * s⁻¹ := by rw [h3us, h3s, mul_assoc u s t]
      _ = u * t := by rw [hst]; group
  · refine ⟨y₂ * y₃, mul_mem hy₂ hy₃, ?_, ?_⟩
    · calc y₂ * y₃ * s * (y₂ * y₃)⁻¹ = y₂ * (y₃ * s * y₃⁻¹) * y₂⁻¹ := by group
        _ = (y₂ * s * y₂⁻¹) * (y₂ * t * y₂⁻¹) := by rw [h3s]; group
        _ = s := by rw [h2s', hyt y₂ hy₂, mul_assoc, mul_self_of_mem_Lbar S haQ ht, mul_one]
    · have h3u : y₃ * u * y₃⁻¹ = u := by
        calc y₃ * u * y₃⁻¹ = (y₃ * (u * s) * y₃⁻¹) * (y₃ * s * y₃⁻¹)⁻¹ := by group
          _ = u := by rw [h3us, h3s]; group
      calc y₂ * y₃ * u * (y₂ * y₃)⁻¹ = y₂ * (y₃ * u * y₃⁻¹) * y₂⁻¹ := by group
        _ = u * t := by rw [h3u, h2u]

theorem exists_GamF_conj {fc fv : S.O} (hfcF : fc ∈ Fbar S g t) (hfvF : fv ∈ Fbar S g t)
    (hfc_t : fc ∉ zpowers t) (hfv_t : fv ∉ zpowers t) (hfvc : fv⁻¹ * fc ∉ zpowers t) :
    ∃ γ ∈ GamF S g t, (∀ x ∈ Fbar S g t, γ * x * γ⁻¹ = x ∨ γ * x * γ⁻¹ = x * fc) ∧
      γ * fc * γ⁻¹ = fc ∧ γ * fv * γ⁻¹ = fv * fc := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hkeyM : ∀ τ ∈ conjL S g t, τ ≠ t → ∃ y ∈ S.Mbar, y * τ * y⁻¹ = τ * t := by
    intro τ hτ hτt
    have hy0 := hkey τ hτ hτt
    obtain ⟨y, hy, he⟩ := hy0
    exact ⟨y, Rbar_le_Mbar (Nbar_le_Rbar hy), he⟩
  have hfcD := mem_conjL_of_mem_Fbar_of_ne_one H C ht hkeyM hfcF
    (fun h => hfc_t (h ▸ one_mem _))
  have hn0 := exists_normalizer_conj_eq H C ht hfcD
  obtain ⟨n, hnM, hnN, hfcn⟩ := hn0
  have hconj : ∀ x ∈ Fbar S g t, n⁻¹ * x * n ∈ Fbar S g t := fun x hx => by
    simpa using conj_mem_Fbar (inv_mem hnM) (inv_mem hnN) hx
  have hsF := hconj t (self_mem_Fbar ht)
  have huF := hconj _ hfvF
  have hfvu : fv = n * (n⁻¹ * fv * n) * n⁻¹ := by group
  have hu : n⁻¹ * fv * n ∉ zpowers t := by
    intro h
    rcases S8.eq_one_or_eq_of_mem_zpowers htt h with h1 | h1
    · exact hfv_t (by rw [hfvu, h1]; simp)
    · exact hfvc (by rw [hfvu, h1, ← hfcn, inv_mul_cancel]; exact one_mem _)
  have hus : n⁻¹ * fv * n * (n⁻¹ * t * n) ∉ zpowers t := by
    intro h
    have hsL := Fbar_le_Lbar hsF
    rcases S8.eq_one_or_eq_of_mem_zpowers htt h with h1 | h1
    · have : fv = t := by
        calc fv = n * (n⁻¹ * fv * n * (n⁻¹ * t * n)) * (n⁻¹ * t * n)⁻¹ * n⁻¹ := by group
          _ = t := by
            rw [h1, mul_one, inv_eq_of_mul_eq_one_right (mul_self_of_mem_Lbar S haQ hsL)]
            group
      exact hfv_t (by rw [this]; exact mem_zpowers t)
    · have : fv⁻¹ * fc = t := by
        rw [hfcn]
        calc fv⁻¹ * (n * t * n⁻¹) = fv⁻¹ * (n * (n⁻¹ * fv * n * (n⁻¹ * t * n)) * n⁻¹) := by
              rw [h1]
          _ = t := by group
      exact hfvc (by rw [this]; exact mem_zpowers t)
  have hy0 := exists_Nbar_fix_move H C ht hFN hkey hsF huF hu hus
  obtain ⟨y, hyN, hys, hyu⟩ := hy0
  have hγt : n * y * n⁻¹ * t = t * (n * y * n⁻¹) := by
    calc n * y * n⁻¹ * t = n * (y * (n⁻¹ * t * n) * y⁻¹) * n⁻¹ * (n * y * n⁻¹) := by group
      _ = t * (n * y * n⁻¹) := by rw [hys]; group
  have hγ : n * y * n⁻¹ ∈ GamF S g t := by
    refine mem_GamF.mpr ⟨⟨mul_mem (mul_mem hnM (Rbar_le_Mbar (Nbar_le_Rbar hyN)))
      (inv_mem hnM), hγt⟩, ?_⟩
    have h1 := mem_normalizer_Fbar_of_mem t hnM hnN
    exact mul_mem (mul_mem h1 (mem_normalizer_Fbar_of_mem_Nbar H ht hFN hyN)) (inv_mem h1)
  refine ⟨n * y * n⁻¹, hγ, fun x hx => ?_, ?_, ?_⟩
  · have hx' := hconj x hx
    rcases conj_eq_or_eq_mul_t H ht hyN (Fbar_le_of_subset hFN hx') (Fbar_le_Lbar hx') with
      h | h
    · left
      calc (n * y * n⁻¹) * x * (n * y * n⁻¹)⁻¹ = n * (y * (n⁻¹ * x * n) * y⁻¹) * n⁻¹ := by group
        _ = x := by rw [h]; group
    · right
      calc (n * y * n⁻¹) * x * (n * y * n⁻¹)⁻¹ = n * (y * (n⁻¹ * x * n) * y⁻¹) * n⁻¹ := by group
        _ = x * fc := by rw [h, hfcn]; group
  · rw [hfcn]
    calc n * y * n⁻¹ * (n * t * n⁻¹) * (n * y * n⁻¹)⁻¹ = n * (y * t * y⁻¹) * n⁻¹ := by group
      _ = n * t * n⁻¹ := by rw [commute_of_mem_Rbar haQ (Nbar_le_Rbar hyN), mul_inv_cancel_right]
  · rw [hfcn]
    calc n * y * n⁻¹ * fv * (n * y * n⁻¹)⁻¹ = n * (y * (n⁻¹ * fv * n) * y⁻¹) * n⁻¹ := by group
      _ = fv * (n * t * n⁻¹) := by rw [hyu]; group

theorem exists_fqHom_actsTv {c v : nqSub S g t (Fbar S g t)} (hc : c ≠ 0)
    (hv : v ∉ (ZMod 2) ∙ c) :
    ∃ γ : GamF S g t, ∃ μ : Dual (ZMod 2) (nqSub S g t (Fbar S g t)),
      μ c = 0 ∧ μ v ≠ 0 ∧ ActsTv (fqHom S g t) γ c μ := by
  have hc2 : ∃ y : Nbar S g t, (y : S.O) ∈ Fbar S g t ∧ nqMk y = (c : NQ S g t) :=
    exists_of_mem_nqSub c.2
  obtain ⟨fc, hfcF, hfc⟩ := hc2
  have hv2 : ∃ y : Nbar S g t, (y : S.O) ∈ Fbar S g t ∧ nqMk y = (v : NQ S g t) :=
    exists_of_mem_nqSub v.2
  obtain ⟨fv, hfvF, hfv⟩ := hv2
  have hfc_t : (fc : S.O) ∉ zpowers t := by
    intro h
    have h0 : nqMk fc = 0 := (nqMk_eq_zero_iff fc).mpr h
    rw [hfc] at h0
    exact hc (Submodule.coe_eq_zero.mp h0)
  have hfv_t : (fv : S.O) ∉ zpowers t := by
    intro h
    have h0 : nqMk fv = 0 := (nqMk_eq_zero_iff fv).mpr h
    rw [hfv] at h0
    rw [Submodule.coe_eq_zero.mp h0] at hv
    exact hv (zero_mem _)
  have hfvc : (fv : S.O)⁻¹ * fc ∉ zpowers t := by
    intro h
    have h0 : nqMk fv = nqMk fc := (nqMk_eq_iff fv fc).mpr h
    rw [hfv, hfc] at h0
    rw [show v = c from Subtype.ext h0] at hv
    exact hv (Submodule.mem_span_singleton_self c)
  have hγ0 := exists_GamF_conj H C ht hFN hkey hfcF hfvF hfc_t hfv_t hfvc
  obtain ⟨γ, hγ, hact, hfix, hmove⟩ := hγ0
  exact exists_fqHom_actsTv_of_conj hFN hγ hc hfcF hfc hfvF hfv hfc_t hact hfix hmove

theorem fix_or_prod_dvd_card (h3 : 3 ≤ finrank (ZMod 2) (nqSub S g t (Fbar S g t))) :
    (∀ r ∈ Rbar S g t ⊓ normalizer (Fbar S g t : Set S.O), ∀ f ∈ Fbar S g t,
        (r * f * r⁻¹)⁻¹ * f ∈ zpowers t) ∨
      (∏ i ∈ Finset.range (finrank (ZMod 2) (nqSub S g t (Fbar S g t))), (2 ^ (i + 1) - 1)) ∣
        Nat.card ↥(Rbar S g t ⊓ normalizer (Fbar S g t : Set S.O)) := by
  have haQ := H.conj_mem
  by_cases hfix : ∀ r ∈ Rbar S g t ⊓ normalizer (Fbar S g t : Set S.O), ∀ f ∈ Fbar S g t,
      (r * f * r⁻¹)⁻¹ * f ∈ zpowers t
  · exact Or.inl hfix
  right
  push Not at hfix
  obtain ⟨r, hr, f, hfF, hrf⟩ := hfix
  have hRG : Rbar S g t ⊓ normalizer (Fbar S g t : Set S.O) ≤ GamF S g t := fun x hx =>
    mem_GamF.mpr ⟨⟨Rbar_le_Mbar hx.1, commute_of_mem_Rbar haQ hx.1⟩, hx.2⟩
  let Δ : Subgroup (GamF S g t) :=
    (Rbar S g t ⊓ normalizer (Fbar S g t : Set S.O)).subgroupOf (GamF S g t)
  have hΔ : Δ.Normal := by
    constructor
    intro x hx γ
    rw [mem_subgroupOf] at hx ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    obtain ⟨⟨hγM, hγt⟩, hγF⟩ := mem_GamF.mp γ.2
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hγM
    refine mem_inf.mpr ⟨?_, mul_mem (mul_mem hγF hx.2) (inv_mem hγF)⟩
    have := conj_mem_Rbar (k := k) (by rw [hk]; exact hγt) hx.1
    rw [hk] at this
    exact this
  have hδ₀ : (⟨r, hRG hr⟩ : GamF S g t) ∈ Δ := by
    rw [mem_subgroupOf]
    exact hr
  have hfN : f ∈ Nbar S g t := Fbar_le_of_subset hFN hfF
  have hrfN : r * f * r⁻¹ ∈ Nbar S g t :=
    Fbar_le_of_subset hFN ((mem_normalizer_iff.mp hr.2 _).mp hfF)
  have hv₀ : fqHom S g t ⟨r, hRG hr⟩ ⟨nqMk ⟨f, hfN⟩, ⟨⟨f, hfN⟩, hfF, rfl⟩⟩ ≠
      ⟨nqMk ⟨f, hfN⟩, ⟨⟨f, hfN⟩, hfF, rfl⟩⟩ := by
    intro he
    apply hrf
    have h1 := congrArg Subtype.val he
    rw [coe_fqHom_apply _ _ hfF rfl (x' := ⟨_, hrfN⟩) rfl, nqMk_eq_iff] at h1
    exact h1
  have hT := forall_actsTv_of_exists (ρ := fqHom S g t)
    (fun c v hc hv => exists_fqHom_actsTv H C ht hFN hkey hc hv)
  have hdvd := prod_dvd_card_of_forall_actsTv (forall_actsTv_of_normal hT hΔ h3 hδ₀ hv₀)
  rwa [show Nat.card Δ = Nat.card ↥(Rbar S g t ⊓ normalizer (Fbar S g t : Set S.O)) from
    Nat.card_congr (subgroupOfEquivOfLe hRG).toEquiv] at hdvd

end Step6

end CFSG.LargeExtraspecial.S9
