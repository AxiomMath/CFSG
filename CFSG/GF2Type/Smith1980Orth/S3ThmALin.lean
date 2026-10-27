module

public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.ClassicalGroups.Orthogonal.Eichler
import CFSG.LargeExtraspecial.FS77Orth
import CFSG.LargeExtraspecial.S14SMKDeltaLin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

private theorem polar_apply_of_isometry {c : V ≃ₗ[ZMod 2] V} (hc : ∀ v, Q (c v) = Q v)
    (u v : V) : polar Q (c u) (c v) = polar Q u v :=
  TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hc) u v

private theorem mem_orthogonal_iff' {P : Submodule (ZMod 2) V} {x : V} :
    x ∈ LinearMap.BilinForm.orthogonal Q.polarBilin P ↔ ∀ n ∈ P, polar Q n x = 0 :=
  LinearMap.BilinForm.mem_orthogonal_iff

theorem eichler_mul_comm_of_mem {u : V ≃ₗ[ZMod 2] V} (hu : ∀ v, Q (u v) = Q v)
    (huu : u * u = 1) {e f : V} (he : e ∈ commSpace u) (hf : f ∈ fixSpace u) (hqe : Q e = 0)
    (hef : polar Q e f = 0) : eichler Q e f * u = u * eichler Q e f := by
  have hue : u e = e := mem_fixSpace.mp (commSpace_le_fixSpace huu he)
  have huf : u f = f := mem_fixSpace.mp hf
  have h1 : ∀ x, polar Q (u x) e = polar Q x e := fun x => by
    have h := polar_apply_of_isometry hu x e
    rwa [hue] at h
  have h2 : ∀ x, polar Q (u x) f = polar Q x f := fun x => by
    have h := polar_apply_of_isometry hu x f
    rwa [huf] at h
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, eichler_apply_zmod2 hqe hef,
    eichler_apply_zmod2 hqe hef, h1, h2, map_add, map_add, map_smul, map_smul, hue, huf]

private theorem comp_sub_eq_zero {P : Submodule (ZMod 2) V} {e : V}
    (he : e ∈ LinearMap.BilinForm.orthogonal Q.polarBilin P) (hqe : Q e = 1)
    {c₁ c₂ : V ≃ₗ[ZMod 2] V} (h₁ : ∀ v, Q (c₁ v) = Q v) (h₂ : ∀ v, Q (c₂ v) = Q v)
    (hP₂ : ∀ p ∈ P, c₂ p = p)
    (hN₁ : ∀ a ∈ LinearMap.BilinForm.orthogonal Q.polarBilin P, c₁ a - a ∈ (ZMod 2) ∙ e)
    (hN₂ : ∀ a ∈ LinearMap.BilinForm.orthogonal Q.polarBilin P, c₂ a - a ∈ (ZMod 2) ∙ e) (v : V) :
    c₁ (c₂ v - v) = c₂ v - v := by
  have hc₂e : c₂ e = e := by
    rcases mem_span_singleton_iff.mp (hN₂ e he) with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have h0 : c₂ e = 0 := by
        rw [eq_add_of_sub_eq h, vec_add_self]
      have h1 := h₂ e
      rw [h0, map_zero, hqe] at h1
      exact zero_ne_one h1
  have ha : c₂ v - v ∈ LinearMap.BilinForm.orthogonal Q.polarBilin P :=
    S14.SMK.sub_mem_orthogonal (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr h₂) hP₂ v
  have hae : polar Q (c₂ v - v) e = 0 := by
    have h := polar_apply_of_isometry h₂ v e
    rw [hc₂e] at h
    rw [QuadraticMap.polar_sub_left, h, sub_self]
  rcases mem_span_singleton_iff.mp (hN₁ _ ha) with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have h1 : c₁ (c₂ v - v) = (c₂ v - v) + e := eq_add_of_sub_eq' h
    have h2 := h₁ (c₂ v - v)
    rw [h1, map_add_eq, hqe, hae] at h2
    have h4 : (1 : ZMod 2) = 0 := by linear_combination h2
    exact one_ne_zero h4

theorem commute_of_sub_mem_span {P : Submodule (ZMod 2) V}
    (_hP : P ≤ LinearMap.BilinForm.orthogonal Q.polarBilin P)
    {e : V} (he : e ∈ LinearMap.BilinForm.orthogonal Q.polarBilin P) (hqe : Q e = 1)
    {c₁ c₂ : V ≃ₗ[ZMod 2] V} (h₁ : ∀ v, Q (c₁ v) = Q v) (h₂ : ∀ v, Q (c₂ v) = Q v)
    (hP₁ : ∀ p ∈ P, c₁ p = p) (hP₂ : ∀ p ∈ P, c₂ p = p)
    (hN₁ : ∀ a ∈ LinearMap.BilinForm.orthogonal Q.polarBilin P, c₁ a - a ∈ (ZMod 2) ∙ e)
    (hN₂ : ∀ a ∈ LinearMap.BilinForm.orthogonal Q.polarBilin P, c₂ a - a ∈ (ZMod 2) ∙ e) :
    c₁ * c₂ = c₂ * c₁ := by
  refine LinearEquiv.ext fun v => ?_
  have e12 := comp_sub_eq_zero he hqe h₁ h₂ hP₂ hN₁ hN₂ v
  have e21 := comp_sub_eq_zero he hqe h₂ h₁ hP₁ hN₂ hN₁ v
  rw [map_sub] at e12 e21
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have f12 : c₁ (c₂ v) = c₂ v + c₁ v - v := by
    rw [← sub_eq_zero] at e12 ⊢
    rw [← e12]
    abel
  have f21 : c₂ (c₁ v) = c₁ v + c₂ v - v := by
    rw [← sub_eq_zero] at e21 ⊢
    rw [← e21]
    abel
  rw [f12, f21]
  abel

section Finite

variable [FiniteDimensional (ZMod 2) V]

private instance instFiniteOfFDLin : Finite V := Module.finite_of_finite (ZMod 2)

theorem card_le_two_of_forall_apply_eq (hQ : Q.polarBilin.Nondegenerate)
    {A : Submodule (ZMod 2) V} (hA : finrank (ZMod 2) V ≤ finrank (ZMod 2) A + 1)
    (H : Subgroup (V ≃ₗ[ZMod 2] V)) (hHQ : ∀ e ∈ H, ∀ v, Q (e v) = Q v)
    (hHA : ∀ e ∈ H, ∀ a ∈ A, e a = a) : Nat.card H ≤ 2 := by
  by_cases hAtop : A = ⊤
  · have : Subsingleton H := ⟨fun a b => Subtype.ext (LinearEquiv.ext fun v => by
      rw [hHA a a.2 v (hAtop ▸ Submodule.mem_top), hHA b b.2 v (hAtop ▸ Submodule.mem_top)])⟩
    have h1 : Nat.card H ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr this
    omega
  · obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ ∉ A := by
      by_contra! h
      exact hAtop (eq_top_iff.mpr fun v _ => h v)
    have hsup : A ⊔ (ZMod 2) ∙ v₀ = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      have h1 := Submodule.finrank_le (A ⊔ (ZMod 2) ∙ v₀)
      have h2 := Submodule.finrank_sup_span_singleton hv₀
      omega
    have hmem : ∀ e : H, (e : V ≃ₗ[ZMod 2] V) v₀ - v₀ ∈
        LinearMap.BilinForm.orthogonal Q.polarBilin A := fun e =>
      S14.SMK.sub_mem_orthogonal (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hHQ e e.2))
        (hHA e e.2) v₀
    let f : H → LinearMap.BilinForm.orthogonal Q.polarBilin A :=
      fun e => ⟨(e : V ≃ₗ[ZMod 2] V) v₀ - v₀, hmem e⟩
    have hinj : Function.Injective f := by
      intro e e' h
      have h' : (e : V ≃ₗ[ZMod 2] V) v₀ = (e' : V ≃ₗ[ZMod 2] V) v₀ :=
        sub_left_inj.mp (congrArg Subtype.val h)
      refine Subtype.ext (LinearEquiv.ext fun v => ?_)
      have hv : v ∈ A ⊔ (ZMod 2) ∙ v₀ := hsup ▸ Submodule.mem_top
      obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_add, map_add, map_smul, map_smul, hHA e e.2 a ha, hHA e' e'.2 a ha, h']
    have hcard1 : Nat.card H ≤ Nat.card (LinearMap.BilinForm.orthogonal Q.polarBilin A) :=
      Nat.card_le_card_of_injective f hinj
    have hcard2 : Nat.card (LinearMap.BilinForm.orthogonal Q.polarBilin A) =
        2 ^ finrank (ZMod 2) (LinearMap.BilinForm.orthogonal Q.polarBilin A) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have hdim : finrank (ZMod 2) (LinearMap.BilinForm.orthogonal Q.polarBilin A) ≤ 1 := by
      rw [LinearMap.BilinForm.finrank_orthogonal hQ]
      omega
    calc Nat.card H ≤ 2 ^ finrank (ZMod 2) (LinearMap.BilinForm.orthogonal Q.polarBilin A) :=
          hcard1.trans hcard2.le
      _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hdim
      _ = 2 := by norm_num

theorem exists_singular_fixed_of_invariant (hQ : Q.polarBilin.Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) V) {u : V ≃ₗ[ZMod 2] V} (hu : ∀ v, Q (u v) = Q v)
    (huu : u * u = 1) (hA : ∀ x ∈ commSpace u, Q x = 0) (hsing : ∃ p : V, p ≠ 0 ∧ Q p = 0)
    {U : Submodule (ZMod 2) V} (hU0 : U ≠ ⊥)
    (hU : ∀ e f : V, Q e = 0 → polar Q e f = 0 → eichler Q e f * u = u * eichler Q e f →
      ∀ v ∈ U, eichler Q e f v ∈ U) :
    ∃ p ∈ U, p ≠ 0 ∧ Q p = 0 ∧ u p = p := by
  have hO : u ∈ orthogonalGroup Q := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hu
  by_cases hu1 : u = 1
  · subst hu1
    have hUtop : U = ⊤ :=
      (FS77.eichler_invariant_submodule hQ h3 U fun e f he hef x hx =>
        hU e f he hef (by rw [mul_one, one_mul]) x hx).resolve_left hU0
    obtain ⟨p, hp0, hpQ⟩ := hsing
    exact ⟨p, hUtop ▸ Submodule.mem_top, hp0, hpQ, rfl⟩
  have hPfix : commSpace u ≤ fixSpace u := commSpace_le_fixSpace huu
  have hfixP : fixSpace u = LinearMap.BilinForm.orthogonal Q.polarBilin (commSpace u) :=
    fixSpace_eq_orthogonal_commSpace hQ hO huu
  have hPiso : ∀ y ∈ commSpace u, ∀ y' ∈ commSpace u, polar Q y y' = 0 := fun y hy y' hy' =>
    polar_commSpace_eq_zero hO huu hy hy'
  have hP2 : 2 ≤ finrank (ZMod 2) (commSpace u) := by
    have h1 := one_le_finrank_commSpace hu1
    have hdim := finrank_commSpace_add_finrank_fixSpace u
    by_contra hlt
    rcases eq_one_or_eq_transvection_of_finrank_fixSpace hQ hO (by omega) with
      h | ⟨c, hqc, -, hc, -⟩
    · exact hu1 h
    · have hcmem : c ∈ commSpace u := hc ▸ Submodule.mem_span_singleton_self c
      have h0 := hA c hcmem
      rw [hqc] at h0
      exact one_ne_zero h0
  have key : ∀ p ∈ commSpace u, p ≠ 0 → p ∈ U → ∃ p ∈ U, p ≠ 0 ∧ Q p = 0 ∧ u p = p :=
    fun p hp hp0 hpU => ⟨p, hpU, hp0, hA p hp, mem_fixSpace.mp (hPfix hp)⟩
  obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  by_cases hvP : v ∈ commSpace u
  · exact key v hvP hv0 hvU
  by_cases hvperp : v ∈ LinearMap.BilinForm.orthogonal Q.polarBilin (commSpace u)
  ·
    have hvP' : v ∉ LinearMap.BilinForm.orthogonal Q.polarBilin
        (LinearMap.BilinForm.orthogonal Q.polarBilin (commSpace u)) := by
      rwa [LinearMap.BilinForm.orthogonal_orthogonal hQ (isRefl_polarBilin Q)]
    obtain ⟨f, hf, hvf⟩ : ∃ f ∈ LinearMap.BilinForm.orthogonal Q.polarBilin (commSpace u),
        polar Q f v ≠ 0 := by
      by_contra! hcon
      exact hvP' (mem_orthogonal_iff'.mpr hcon)
    have hvf1 : polar Q v f = 1 := by
      rw [polar_comm]
      exact zmod2_eq_one_of_ne_zero hvf
    obtain ⟨e, he, he0⟩ : ∃ e ∈ commSpace u, e ≠ 0 := by
      refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => ?_
      rw [h, finrank_bot] at hP2
      omega
    have hfe : polar Q e f = 0 := (mem_orthogonal_iff'.mp hf) e he
    have hcomm := eichler_mul_comm_of_mem hu huu he (hfixP ▸ hf) (hA e he) hfe
    have hEU := hU e f (hA e he) hfe hcomm v hvU
    have hve : polar Q v e = 0 := by
      rw [polar_comm]
      exact (mem_orthogonal_iff'.mp hvperp) e he
    have hEv : eichler Q e f v - v = e := by
      rw [eichler_apply_zmod2 (hA e he) hfe, hve, hvf1, zero_smul, add_zero, mul_zero, add_zero,
        one_smul, add_sub_cancel_left]
    refine key e he he0 ?_
    have := U.sub_mem hEU hvU
    rwa [hEv] at this
  ·
    obtain ⟨e, he, hve⟩ : ∃ e ∈ commSpace u, polar Q e v ≠ 0 := by
      by_contra! hcon
      exact hvperp (mem_orthogonal_iff'.mpr hcon)
    have hve1 : polar Q v e = 1 := by
      rw [polar_comm]
      exact zmod2_eq_one_of_ne_zero hve
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [polar_zero_left] at hve
      exact hve rfl
    obtain ⟨e', he', hne'⟩ : ∃ e' ∈ commSpace u, e' ∉ (ZMod 2) ∙ e := by
      by_contra! hcon
      have h1 := Submodule.finrank_mono (show commSpace u ≤ (ZMod 2) ∙ e from hcon)
      rw [finrank_span_singleton he0] at h1
      omega
    have hee' : polar Q e e' = 0 := hPiso e he e' he'
    have hcomm := eichler_mul_comm_of_mem hu huu he (hPfix he') (hA e he) hee'
    have hEU := hU e e' (hA e he) hee' hcomm v hvU
    have hEv : eichler Q e e' v - v = e' + polar Q v e' • e := by
      rw [eichler_apply_zmod2 (hA e he) hee', hve1, hA e' he', one_smul, zero_mul, add_zero,
        add_assoc, add_sub_cancel_left]
    have hmemP : e' + polar Q v e' • e ∈ commSpace u :=
      Submodule.add_mem _ he' (Submodule.smul_mem _ _ he)
    have hmemU : e' + polar Q v e' • e ∈ U := by
      have := U.sub_mem hEU hvU
      rwa [hEv] at this
    have hne0 : e' + polar Q v e' • e ≠ 0 := by
      intro h
      apply hne'
      have h' : e' = -(polar Q v e' • e) := eq_neg_of_add_eq_zero_left h
      rw [h']
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
    exact key _ hmemP hne0 hmemU

theorem card_le_of_commSpace_eq (hQ : Q.polarBilin.Nondegenerate)
    {P : Submodule (ZMod 2) V} (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P)
    (h2 : 2 ≤ finrank (ZMod 2) P) (A : Subgroup (V ≃ₗ[ZMod 2] V))
    (hAQ : ∀ e ∈ A, ∀ v, Q (e v) = Q v) (hAP : ∀ e ∈ A, ∀ p ∈ P, e p = p)
    (hfull : ∀ e ∈ A, e ≠ 1 → commSpace e = P) :
    Nat.card A ≤ 2 ^ (finrank (ZMod 2) P - 1) := by
  have hmemP : ∀ x, x ∈ P ↔ ∀ n ∈ P, polar Q n x = 0 := fun x => by
    rw [← mem_orthogonal_iff', hP]
  have hiso : ∀ y ∈ P, ∀ y' ∈ P, polar Q y y' = 0 := fun y hy y' hy' => (hmemP y').mp hy' y hy
  have hdimV : finrank (ZMod 2) V = 2 * finrank (ZMod 2) P := by
    have h := LinearMap.BilinForm.finrank_orthogonal hQ P
    rw [hP] at h
    have h' := Submodule.finrank_le P
    omega
  obtain ⟨ξ, hξP, y₁, hy₁, hne⟩ : ∃ ξ, ξ ∉ P ∧ ∃ y ∈ P, Q y ≠ polar Q y ξ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨ξ₁, hξ₁⟩ : ∃ ξ₁, ξ₁ ∉ P := by
      by_contra! hall
      have hPtop : P = ⊤ := eq_top_iff.mpr fun v _ => hall v
      rw [hPtop, finrank_top] at h2 hdimV
      omega
    have hsup : P ⊔ (ZMod 2) ∙ ξ₁ = ⊤ := by
      rw [eq_top_iff]
      intro ξ _
      by_cases hξ : ξ ∈ P
      · exact Submodule.mem_sup_left hξ
      · have hperp : ξ + ξ₁ ∈ P := by
          rw [hmemP]
          intro n hn
          rw [polar_add_right, ← hcon ξ hξ n hn, ← hcon ξ₁ hξ₁ n hn, zmod2_add_self]
        have hξeq : ξ = (ξ + ξ₁) + ξ₁ := by rw [add_assoc, vec_add_self, add_zero]
        rw [hξeq]
        exact Submodule.add_mem_sup hperp (Submodule.mem_span_singleton_self ξ₁)
    have h := Submodule.finrank_sup_span_singleton hξ₁
    rw [hsup, finrank_top] at h
    omega
  let Y : Submodule (ZMod 2) V :=
    { carrier := {y | y ∈ P ∧ Q y = polar Q y ξ}
      add_mem' := by
        rintro y y' ⟨hy, hqy⟩ ⟨hy', hqy'⟩
        refine ⟨P.add_mem hy hy', ?_⟩
        rw [map_add_eq, hiso y hy y' hy', add_zero, hqy, hqy', polar_add_left]
      zero_mem' := ⟨P.zero_mem, by simp⟩
      smul_mem' := by
        rintro c y ⟨hy, hqy⟩
        refine ⟨P.smul_mem c hy, ?_⟩
        rw [map_smul_zmod2, polar_smul_left, hqy, smul_eq_mul] }
  have hYlt : Y < P := by
    refine lt_of_le_of_ne (fun y hy => hy.1) fun h => hne ?_
    have : y₁ ∈ Y := by rw [h]; exact hy₁
    exact this.2
  have hYdim : finrank (ZMod 2) Y ≤ finrank (ZMod 2) P - 1 := by
    have := Submodule.finrank_lt_finrank_of_lt hYlt
    omega
  have hmemY : ∀ e : A, (e : V ≃ₗ[ZMod 2] V) ξ - ξ ∈ Y := by
    intro e
    have he : (e : V ≃ₗ[ZMod 2] V) ∈ orthogonalGroup Q :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hAQ e e.2)
    refine ⟨?_, ?_⟩
    · have h := S14.SMK.sub_mem_orthogonal he (hAP e e.2) ξ
      rwa [hP] at h
    · show Q ((e : V ≃ₗ[ZMod 2] V) ξ - ξ) = polar Q ((e : V ≃ₗ[ZMod 2] V) ξ - ξ) ξ
      rw [map_sub_eq_polar he, QuadraticMap.polar_sub_left, polar_self_eq_zero, sub_zero]
  let f : A → Y := fun e => ⟨(e : V ≃ₗ[ZMod 2] V) ξ - ξ, hmemY e⟩
  have hinj : Function.Injective f := by
    intro e e' h
    have h1 : (e : V ≃ₗ[ZMod 2] V) ξ = (e' : V ≃ₗ[ZMod 2] V) ξ :=
      sub_left_inj.mp (congrArg Subtype.val h)
    have hg : (e' : V ≃ₗ[ZMod 2] V)⁻¹ * (e : V ≃ₗ[ZMod 2] V) ∈ A :=
      A.mul_mem (A.inv_mem e'.2) e.2
    have hgξ : ((e' : V ≃ₗ[ZMod 2] V)⁻¹ * (e : V ≃ₗ[ZMod 2] V)) ξ = ξ := by
      rw [LinearEquiv.mul_apply, h1, ← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
    by_cases hg1 : (e' : V ≃ₗ[ZMod 2] V)⁻¹ * (e : V ≃ₗ[ZMod 2] V) = 1
    · exact Subtype.ext (inv_mul_eq_one.mp hg1).symm
    · exfalso
      have hfix := fixSpace_eq_orthogonal_commSpace_of_mem hQ
        (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hAQ _ hg))
      rw [hfull _ hg hg1, hP] at hfix
      exact hξP (hfix ▸ mem_fixSpace.mpr hgξ)
  have hcard : Nat.card A ≤ Nat.card Y := Nat.card_le_card_of_injective f hinj
  have hcardY : Nat.card Y = 2 ^ finrank (ZMod 2) Y := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Y), Nat.card_zmod]
  exact hcard.trans (hcardY.le.trans (Nat.pow_le_pow_right (by norm_num) hYdim))

end Finite

end CFSG.GF2Type.Smith1980Orth
