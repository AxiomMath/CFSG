module

public import CFSG.LargeExtraspecial.S8FusD
public import CFSG.LargeExtraspecial.S8Mod
public import CFSG.LargeExtraspecial.S8Std

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

theorem finrank_map_mkQ_le_two_mul {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] {Vs W X X' : Submodule K E} (f : E →ₗ[K] E) (hVW : Vs ≤ W)
    (hXW : X ≤ W) (hX'W : X' ≤ W) (hsup : X ⊔ X' = W) (hinf : X ⊓ X' ≤ Vs)
    (hsplit : X ⊓ Vs ⊔ X' ⊓ Vs = Vs) (hfX : ∀ x ∈ X, f x ∈ X') (hfX' : ∀ x ∈ X', f x ∈ X) :
    finrank K (W.map Vs.mkQ) ≤ 2 * finrank K ((W.map (f - 1)).map Vs.mkQ) := by
  have hC : (W.map (f - 1)).map Vs.mkQ = W.map (Vs.mkQ ∘ₗ (f - 1)) := by
    rw [Submodule.map_comp]
  rw [hC]
  have hker : LinearMap.ker (Vs.mkQ ∘ₗ (f - 1)) = Vs.comap (f - 1) := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hbound : ∀ {Y Y' : Submodule K E}, Y ≤ W → Y' ≤ W → Y ⊔ Y' = W →
      (∀ y ∈ Y, f y ∈ Y') →
      finrank K W ≤
        finrank K (W.map (Vs.mkQ ∘ₗ (f - 1))) + finrank K (Y' ⊔ Vs : Submodule K E) := by
    intro Y Y' hYW hY'W hYY' hfY
    have h1 := finrank_map_add_finrank_inf_ker (Vs.mkQ ∘ₗ (f - 1)) Y
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq Y (Y' ⊔ Vs)
    have h3 : Y ⊔ (Y' ⊔ Vs) = W := le_antisymm (sup_le hYW (sup_le hY'W hVW))
      (hYY' ▸ sup_le le_sup_left (le_sup_left.trans le_sup_right))
    have h4 : Y ⊓ LinearMap.ker (Vs.mkQ ∘ₗ (f - 1)) ≤ Y ⊓ (Y' ⊔ Vs) := by
      rintro y ⟨hy, hyk⟩
      refine ⟨hy, ?_⟩
      rw [hker] at hyk
      have hyk' : f y - y ∈ Vs := hyk
      have e : y = f y - (f y - y) := by abel
      rw [e]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (hfY y hy)) (Submodule.mem_sup_right hyk')
    have h5 := Submodule.finrank_mono h4
    have h6 := Submodule.finrank_mono (Submodule.map_mono (f := Vs.mkQ ∘ₗ (f - 1)) hYW)
    rw [h3] at h2
    omega
  have hb1 := hbound hXW hX'W hsup hfX
  have hb2 := hbound hX'W hXW (by rw [sup_comm]; exact hsup) hfX'
  have hinfV : (X ⊔ Vs) ⊓ (X' ⊔ Vs) = Vs := by
    refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
    rintro y ⟨hy1, hy2⟩
    obtain ⟨x, hx, v, hv, rfl⟩ := Submodule.mem_sup.mp hy1
    obtain ⟨x', hx', v', hv', hxv⟩ := Submodule.mem_sup.mp hy2
    have hd : v' - v ∈ Vs := Vs.sub_mem hv' hv
    rw [← hsplit] at hd
    obtain ⟨u, hu, u', hu', huu⟩ := Submodule.mem_sup.mp hd
    have hxu : x - u ∈ X ⊓ X' := by
      refine ⟨X.sub_mem hx hu.1, ?_⟩
      have e : x - u = x' + u' := by
        have : x - x' = v' - v := by rw [sub_eq_sub_iff_add_eq_add, add_comm v' x', hxv, add_comm]
        rw [← huu] at this
        calc x - u = (x - x') - u + x' := by abel
          _ = x' + u' := by rw [this]; abel
      rw [e]
      exact X'.add_mem hx' hu'.1
    have hxV : x ∈ Vs := by
      have := Vs.add_mem (hinf hxu) hu.2
      rwa [sub_add_cancel] at this
    exact Vs.add_mem hxV hv
  have h7 := Submodule.finrank_sup_add_finrank_inf_eq (X ⊔ Vs) (X' ⊔ Vs)
  have hsup' : X ⊔ Vs ⊔ (X' ⊔ Vs) = W := le_antisymm
    (sup_le (sup_le hXW hVW) (sup_le hX'W hVW))
    (hsup ▸ sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
  rw [hinfV, hsup'] at h7
  have h8 := finrank_map_add_finrank_inf_ker Vs.mkQ W
  rw [Submodule.ker_mkQ, inf_eq_right.mpr hVW] at h8
  omega

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem QG_inf_Qa_eq_of_cl_eq {g g' : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (ha'Q : g' * S.z * g'⁻¹ ∈ S.QG)
    (h : S.cl (g' * S.z * g'⁻¹) = S.cl (g * S.z * g⁻¹)) : S.QG ⊓ S.Qa g' = S.QG ⊓ S.Qa g := by
  rcases (S.cl_eq_cl_iff haQ ha'Q).mp h.symm with h1 | h1
  · rw [S.Qa_eq_of_conj_eq h1]
  · exact S.QG_inf_Qa_eq_of_conj_eq_mul_z haQ hne h1

theorem exists_beta_bV_eq_one (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {d : Vt S g t} (hd : d ≠ 0) :
    ∃ k : S.M, ∃ hk : S.ρ k ∈ Rbar S g t,
      beta H C ht ht1 hVQ (bV (mem_Lbar_mul_of_mem_Rbar H ht hk)) d = 1 := by
  by_contra hcon
  push Not at hcon
  apply hd
  set f : Vt S g t →ₗ[ZMod 2] ZMod 2 := (beta H C ht ht1 hVQ).flip d with hf
  have hspan : Vt S g t ≤ (LinearMap.ker f).map (Vt S g t).subtype := by
    refine (Vt_eq_span_orbit H ht).le.trans ?_
    rw [Submodule.span_le]
    intro u hu
    obtain ⟨k, hk, rfl⟩ := exists_of_mem_orbit hu H.conj_mem
    have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
    refine ⟨bV htk, ?_, rfl⟩
    change beta H C ht ht1 hVQ (bV htk) d = 0
    rcases zmod2_eq_zero_or_eq_one (beta H C ht ht1 hVQ (bV htk) d) with h0 | h1
    · exact h0
    · exact absurd h1 (hcon k hk)
  exact (beta_nondegenerate H C ht ht1 hVQ).2 d fun v => by
    obtain ⟨v', hv', hvv'⟩ := hspan v.2
    have : v' = v := Subtype.ext hvv'
    rw [← this]
    exact hv'

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem finrank_WV_le_two_mul_finrank_commWV (D : Std H C ht ht1 hVQ)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    {d : Vt S g t} (hd : D.Q d = 1)
    (hτd : ∀ v : Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + polar D.Q v d • (d : S.Qt)) :
    finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) ≤
      2 * finrank (ZMod 2) (commWV S g t τ) := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hτM : τ ∈ S.Mbar := by
    rw [hxτ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hττ : τ * τ = 1 := by
    rw [hxτ]
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  have hpolβ : ∀ u v : Vt S g t, polar D.Q u v = beta H C ht ht1 hVQ u v := fun u v => by
    rw [← polarBilin_apply_apply, D.hpol]
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd
    exact zero_ne_one hd
  obtain ⟨k, hk, hkd⟩ := exists_beta_bV_eq_one H C ht ht1 hVQ hd0
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  set c : Vt S g t := bV htk with hc
  obtain ⟨k₀, hk₀⟩ := MonoidHom.mem_range.mp hτM
  have hτc : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) c = c + d := by
    rw [hτd c, hpolβ, hkd, one_smul]
  have hτcV : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) c ∈ Vt S g t := by
    rw [hτc]; exact (Vt S g t).add_mem c.2 d.2
  have hakQ : (k : G) * g * S.z * ((k : G) * g)⁻¹ ∈ S.QG := conj_mem_QG' S k.2 haQ
  have hcl0 : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) c =
      S.cl ((k₀ * k : S.M) * g * S.z * (((k₀ * k : S.M) : G) * g)⁻¹) := by
    rw [hc, coe_bV, ← hk₀, ρ_cl_conj_z S k₀ hakQ, Subgroup.coe_mul]
    simp only [mul_assoc]
  obtain ⟨k', hk', hk'c⟩ := exists_of_mem_orbit (hcl0 ▸ hfus (k₀ * k) (hcl0 ▸ hτcV)) haQ
  have htk' := mem_Lbar_mul_of_mem_Rbar H ht hk'
  set c' : Vt S g t := bV htk' with hc'
  have hcc' : (c' : S.Qt) = (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) c := by rw [hc', coe_bV, hk'c]
  have hc'eq : c' = c + d := Subtype.ext (by rw [hcc', hτc]; rfl)
  have hβcc' : beta H C ht ht1 hVQ c c' = 1 := by
    rw [hc'eq, map_add, (beta_isAlt H C ht ht1 hVQ) c, zero_add]
    exact hkd
  have hb' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g) := by
    intro hmem
    have hk'Q : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∈ S.QG := conj_mem_QG' S k'.2 haQ
    have h1 : (c' : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) := by
      rw [hc', coe_bV]
      exact S.cl_mem_clSub ⟨hk'Q, hmem⟩ hk'Q
    have h2 := (beta_bV_eq_zero_iff H C ht ht1 hVQ hk htk c').mpr h1
    rw [hβcc'] at h2
    exact one_ne_zero h2
  set h₁ : S.M := k' * k⁻¹ with hh₁
  have hh₁g : ((h₁ : S.M) : G) * ((k : G) * g) = (k' : G) * g := by
    rw [hh₁, Subgroup.coe_mul, InvMemClass.coe_inv]
    group
  have hh₁R : S.ρ h₁ ∈ Rbar S ((k : G) * g) t := by
    rw [Rbar_mul, hh₁, map_mul, map_inv]
    exact mul_mem hk' (inv_mem hk)
  have hb₁ : ((h₁ : S.M) : G) * ((k : G) * g) * S.z * (((h₁ : S.M) : G) * ((k : G) * g))⁻¹ ∉
      S.Qa ((k : G) * g) := by
    rw [hh₁g]; exact hb'
  have hVQ₁ := not_V_le_Qa_mul H hVQ hk
  have hP₁ := clSub_inf_clSub_le_Vt (H.mul k) (C.mul k) htk ht1 hVQ₁ hh₁R hb₁
    (RadBound.mul H D.hR hk)
  have hsup₁ := sup_eq_Wt (H.mul k) (C.mul k) htk ht1 hVQ₁ hh₁R hb₁ hP₁
  rw [hh₁g, Vt_mul] at hP₁
  rw [hh₁g, Wt_mul] at hsup₁
  set X := S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t with hX
  set X' := S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ⊓ Wt S g t with hX'
  have hQa1 : S.QG ⊓ S.Qa ((k₀ : G) * ((k : G) * g)) = S.QG ⊓ S.Qa ((k' : G) * g) := by
    refine QG_inf_Qa_eq_of_cl_eq (conj_mem_QG' S k'.2 haQ) (conj_ne_z' S k'.2 H.conj_ne)
      (conj_mem_QG' S k₀.2 hakQ) ?_
    rw [← ρ_cl_conj_z S k₀ hakQ, ← coe_bV htk, hk₀, ← hc, ← hcc', hc', coe_bV]
  have hakQ' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∈ S.QG := conj_mem_QG' S k'.2 haQ
  have hQa2 : S.QG ⊓ S.Qa ((k₀ : G) * ((k' : G) * g)) = S.QG ⊓ S.Qa ((k : G) * g) := by
    refine QG_inf_Qa_eq_of_cl_eq hakQ (conj_ne_z' S k.2 H.conj_ne)
      (conj_mem_QG' S k₀.2 hakQ') ?_
    rw [← ρ_cl_conj_z S k₀ hakQ', ← coe_bV htk', hk₀, ← hc', hcc', ← coe_mul_apply, hττ]
    rw [hc, coe_bV]
    rfl
  have hτX : ∀ v ∈ X, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X' := by
    rintro v ⟨hv1, hv2⟩
    refine ⟨?_, apply_mem_Wt_of_commute H C ht ht1 hVQ hτt hv2⟩
    have := apply_mem_clSub_Qa_mul (g := (k : G) * g) k₀ hv1
    rwa [hQa1, hk₀] at this
  have hτX' : ∀ v ∈ X', (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X := by
    rintro v ⟨hv1, hv2⟩
    refine ⟨?_, apply_mem_Wt_of_commute H C ht ht1 hVQ hτt hv2⟩
    have := apply_mem_clSub_Qa_mul (g := (k' : G) * g) k₀ hv1
    rwa [hQa2, hk₀] at this
  have hVW := Vt_le_Wt H ht1
  have hmemX : ∀ y : Vt S g t, beta H C ht ht1 hVQ c y = 0 → (y : S.Qt) ∈ X ⊓ Vt S g t :=
    fun y hy => ⟨⟨(beta_bV_eq_zero_iff H C ht ht1 hVQ hk htk y).mp hy, hVW y.2⟩, y.2⟩
  have hmemX' : ∀ y : Vt S g t, beta H C ht ht1 hVQ c' y = 0 → (y : S.Qt) ∈ X' ⊓ Vt S g t :=
    fun y hy => ⟨⟨(beta_bV_eq_zero_iff H C ht ht1 hVQ hk' htk' y).mp hy, hVW y.2⟩, y.2⟩
  have hsplit : X ⊓ Vt S g t ⊔ X' ⊓ Vt S g t = Vt S g t := by
    refine le_antisymm (sup_le inf_le_right inf_le_right) fun v hv => ?_
    set y : Vt S g t := ⟨v, hv⟩ with hy
    rcases zmod2_eq_zero_or_eq_one (beta H C ht ht1 hVQ c y) with h0 | h1
    · exact Submodule.mem_sup_left (hmemX y h0)
    rcases zmod2_eq_zero_or_eq_one (beta H C ht ht1 hVQ c' y) with h0' | h1'
    · exact Submodule.mem_sup_right (hmemX' y h0')
    have hc0 : c ≠ 0 := by
      rintro h
      rw [h, map_zero, LinearMap.zero_apply] at hkd
      exact zero_ne_one hkd
    have hcc'ne : c ≠ c' := by
      intro h
      rw [← h, (beta_isAlt H C ht ht1 hVQ) c] at hβcc'
      exact zero_ne_one hβcc'
    obtain ⟨w, hw1, hw2⟩ := exists_apply_eq_one_eq_zero (beta_nondegenerate H C ht ht1 hVQ) hc0
      hcc'ne
    have hyw : beta H C ht ht1 hVQ c (y - w) = 0 := by
      rw [map_sub, h1, hw1, sub_self]
    have e : v = ((y - w : Vt S g t) : S.Qt) + (w : S.Qt) := by
      rw [Submodule.coe_sub, sub_add_cancel]
    rw [e]
    exact Submodule.add_mem_sup (hmemX _ hyw) (hmemX' w hw2)
  exact finrank_map_mkQ_le_two_mul (τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap hVW inf_le_right
    inf_le_right hsup₁ (fun v hv => hP₁ ⟨hv.1.1, hv.2.1⟩) hsplit hτX hτX'

end CFSG.LargeExtraspecial.S8
