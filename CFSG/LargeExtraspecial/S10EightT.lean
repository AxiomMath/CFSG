module

public import CFSG.LargeExtraspecial.S10EightS
public import CFSG.LargeExtraspecial.S10EightQ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
theorem stab_move_Γ₂ : ∀ γ δ : Gm, act γ E00 = E00 → γ.2 ≠ 1 → δ.1 = 1 → δ ^ 3 = 1 → δ ≠ 1 →
    act γ (act δ E00) ≠ act δ E00 := by
  decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem mem_Xb_of_fix (hCE : CentralExtInput.{u}) {kd : S.M} (hkd : S.ρ kd ∈ ⁅Yb, Yb⁆)
    (hkd1 : S.ρ kd ≠ 1) {l : S.O} (hl : l ∈ S.Lbar g)
    (hlf : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((kd : G) * g * S.z * ((kd : G) * g)⁻¹)) =
      S.cl ((kd : G) * g * S.z * ((kd : G) * g)⁻¹)) : l ∈ Xb := by
  obtain ⟨F, hFY, hFX, -⟩ := D.exists_frame hCE
  obtain ⟨hσ1, hσ3, hσne⟩ := D.dec.pi_spec hCE hFY hkd hkd1
  by_contra hlX
  have hlR := Lbar_le_Rbar X.ht hl
  have hl2 : (F.π ⟨l, hlR⟩).2 ≠ 1 := fun h => hlX (by
    rw [hFX]
    exact (F.mem_pre).mpr ⟨hlR, mem_Γ₁.mpr h⟩)
  have hdR := D.dec.le_Rbar_right ((D.dec.mem_commutator_iff).mp hkd).1
  have hfix : resV X.haQ t ⟨l, hlR⟩ (resV X.haQ t ⟨S.ρ kd, hdR⟩ (aV X.ht)) =
      resV X.haQ t ⟨S.ρ kd, hdR⟩ (aV X.ht) := by
    refine Subtype.ext ?_
    rw [coe_resV_apply, coe_resV_apply]
    have e : ((S.ρ kd : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (aV X.ht : S.Qt) =
        S.cl ((kd : G) * g * S.z * ((kd : G) * g)⁻¹) := ρ_cl_conj_z S kd X.haQ
    rw [e]
    exact hlf
  have h1 := congrArg F.φ hfix
  rw [F.compat, F.φ_resV_aV] at h1
  exact stab_move_Γ₂ _ _ (F.π_mem_stabA hl) hl2 hσ1 hσ3 hσne h1

theorem good_of_commute (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g)
    (hF : S6.FusionCtl S g) (h7 : 7 ≤ S.width) {kd : S.M} (hkd : S.ρ kd ∈ ⁅Yb, Yb⁆)
    (hkd1 : S.ρ kd ≠ 1)
    (hne : S.cl ((kd : G) * g * S.z * ((kd : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹))
    (hPa : S.cl ((kd : G) * g * S.z * ((kd : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    {kx kf : S.M} (hx : ⁅Yb, Yb⁆.map (cK S kx) = ⁅Yb, Yb⁆)
    (hxf : (kx : G) * g * S.z * ((kx : G) * g)⁻¹ * ((kf : G) * g * S.z * ((kf : G) * g)⁻¹) =
      (kf : G) * g * S.z * ((kf : G) * g)⁻¹ * ((kx : G) * g * S.z * ((kx : G) * g)⁻¹))
    (hxα : (kx : G) * g * S.z * ((kx : G) * g)⁻¹ *
        (((kf * kd : S.M) : G) * g * S.z * (((kf * kd : S.M) : G) * g)⁻¹) =
      ((kf * kd : S.M) : G) * g * S.z * (((kf * kd : S.M) : G) * g)⁻¹ *
        ((kx : G) * g * S.z * ((kx : G) * g)⁻¹)) :
    ⁅Yb, Yb⁆.map (cK S kf) = ⁅Yb, Yb⁆ := by
  set x := (kx : G) * g * S.z * ((kx : G) * g)⁻¹ with hxdef
  set f := (kf : G) * g * S.z * ((kf : G) * g)⁻¹ with hfdef
  set α := (kd : G) * g * S.z * ((kd : G) * g)⁻¹ with hαdef
  set αf := ((kf * kd : S.M) : G) * g * S.z * (((kf * kd : S.M) : G) * g)⁻¹ with hαfdef
  have hxQ : x ∈ S.QG := conj_mem_QG' S kx.2 X.haQ
  have hfQ : f ∈ S.QG := conj_mem_QG' S kf.2 X.haQ
  have hαQ : α ∈ S.QG := conj_mem_QG' S kd.2 X.haQ
  have hαfQ : αf ∈ S.QG := conj_mem_QG' S (kf * kd).2 X.haQ
  have hxz : x ≠ S.z := conj_ne_z' S kx.2 X.H.conj_ne
  have hfz : f ≠ S.z := conj_ne_z' S kf.2 X.H.conj_ne
  by_cases hxQf : x ∈ S.Qa ((kf : G) * g)
  ·
    refine D.map_commutator_eq_of_mem_clSub_mul hCE hP h7 hx ?_
    by_cases hxf' : x = f
    · change S.cl f ∈ S.clSub (S.QG ⊓ S.Qa ((kx : G) * g))
      rw [← hxf']
      exact cl_mem_clSub_self hxQ
    · exact S.cl_mem_clSub ⟨hfQ, S.mem_Qa_symm hxf' hxQf⟩ hfQ
  have hαQa : α ∈ S.Qa g := X.mem_Qa_of_mem_clSub hαQ hPa
  have hαfe : αf = (kf : G) * α * (kf : G)⁻¹ := by
    rw [hαfdef, hαdef, Subgroup.coe_mul]
    group
  have hαfQf : αf ∈ S.Qa ((kf : G) * g) := by
    rw [hαfe]
    exact conj_mem_Qa_mul S hαQa
  have hclf : S.cl f = ((S.ρ kf : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) :=
    (ρ_cl_conj_z S kf X.haQ).symm
  have hclαf : S.cl αf = ((S.ρ kf : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl α) := by
    rw [hαfe, S.ρ_cl kf hαQ]
  have hαff : S.cl αf ≠ S.cl f := by
    rw [hclαf, hclf]
    exact fun h => hne (((S.ρ kf : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).injective h)
  have hff : f * f = 1 := (S.conjBy ((kf : G) * g)).z_mul_z
  have hfz' : f * S.z = S.z * f := S.mem_M_iff.mp (S.QG_le_M hfQ)
  have hαcl : αf ∉ closure ({f, S.z} : Set G) := by
    intro h
    rcases (mem_closure_pair_iff hff S.z_mul_z hfz').mp h with h1 | h1 | h1 | h1
    · exact conj_z_ne_one S _ h1
    · exact hαff (by rw [h1])
    · exact conj_ne_z' S (kf * kd).2 X.H.conj_ne h1
    · exact hαff (by rw [h1, S.cl_mul_z hfQ])
  obtain ⟨s, hs, hsz, hsf⟩ := S.lemma_3_8_2 (g := (kf : G) * g) (t := f) rfl hfQ hfz hαfQ hαfQf
    hαcl f (by simp) S.z (by simp) hfz
  have hsα : s * αf = αf * s := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hs).2
  have hkfz : (kf : G) * S.z * (kf : G)⁻¹ = S.z := by
    rw [S.mem_M_iff.mp kf.2, mul_inv_cancel_right]
  set g₁ := s * (kf : G) with hg₁
  have hg₁z : g₁ * S.z * g₁⁻¹ = f := by
    calc g₁ * S.z * g₁⁻¹ = s * ((kf : G) * S.z * (kf : G)⁻¹) * s⁻¹ := by rw [hg₁]; group
      _ = f := by rw [hkfz, hsz]
  have hg₁a : g₁ * (g * S.z * g⁻¹) * g₁⁻¹ = S.z := by
    calc g₁ * (g * S.z * g⁻¹) * g₁⁻¹ = s * f * s⁻¹ := by rw [hg₁, hfdef]; group
      _ = S.z := hsf
  have hg₁a' : g₁⁻¹ * S.z * g₁ = g * S.z * g⁻¹ := by
    calc g₁⁻¹ * S.z * g₁ = g₁⁻¹ * (g₁ * (g * S.z * g⁻¹) * g₁⁻¹) * g₁ := by rw [hg₁a]
      _ = g * S.z * g⁻¹ := by group
  have hg₁α : g₁ * α * g₁⁻¹ = αf := by
    calc g₁ * α * g₁⁻¹ = s * αf * s⁻¹ := by rw [hg₁, hαfe]; group
      _ = αf := by rw [hsα, mul_inv_cancel_right]
  have hτM : g₁⁻¹ * x * g₁ ∈ S.M := by
    refine S.mem_M_iff.mpr ?_
    have e : S.z = g₁⁻¹ * f * g₁ := by rw [← hg₁z]; group
    calc g₁⁻¹ * x * g₁ * S.z = g₁⁻¹ * (x * f) * g₁ := by rw [e]; group
      _ = g₁⁻¹ * (f * x) * g₁ := by rw [hxf]
      _ = S.z * (g₁⁻¹ * x * g₁) := by rw [e]; group
  set τ' : S.M := ⟨g₁⁻¹ * x * g₁, hτM⟩ with hτ'
  have hQaeq : ∀ h : G, h * S.z * h⁻¹ = g * S.z * g⁻¹ → S.Qa h = S.Qa g := fun h hh =>
    S.Qa_eq_of_conj_eq hh
  have hτQa : g₁⁻¹ * x * g₁ ∈ S.Qa g := by
    have h1 : g₁⁻¹ * x * g₁⁻¹⁻¹ ∈ S.Qa (g₁⁻¹ * 1) :=
      conj_mem_Qa_mul S (by rw [Setting.Qa_one]; exact hxQ)
    rw [inv_inv, hQaeq _ (by rw [← hg₁a']; group)] at h1
    exact h1
  have hτL : S.ρ τ' ∈ S.Lbar g := ρ_mem_Lbar S ⟨hτQa, hτM⟩
  have hτX : S.ρ τ' ∈ Xb := by
    refine D.mem_Xb_of_fix hCE hkd hkd1 hτL ?_
    rw [S.ρ_cl τ' hαQ]
    congr 1
    have hxαf : x * αf = αf * x := hxα
    calc (τ' : G) * α * (τ' : G)⁻¹ = g₁⁻¹ * (x * (g₁ * α * g₁⁻¹) * x⁻¹) * g₁ := by
          rw [hτ']; group
      _ = g₁⁻¹ * (x * αf * x⁻¹) * g₁ := by rw [hg₁α]
      _ = g₁⁻¹ * αf * g₁ := by rw [hxαf, mul_inv_cancel_right]
      _ = α := by rw [← hg₁α]; group
  have hτ1 : S.ρ τ' ≠ 1 := by
    intro h
    apply hxQf
    have h1 : (τ' : G) ∈ S.QG := (S.ρ_eq_one_iff τ').mp h
    have h2 : g₁ * (τ' : G) * g₁⁻¹ ∈ S.Qa (g₁ * 1) :=
      conj_mem_Qa_mul S (by rw [Setting.Qa_one]; exact h1)
    rw [S.Qa_eq_of_conj_eq (g := g₁ * 1) (h := (kf : G) * g) (by rw [mul_one, hg₁z])] at h2
    have e : g₁ * (τ' : G) * g₁⁻¹ = x := by rw [hτ']; group
    rwa [e] at h2
  set u := g₁⁻¹ * ((kx : G) * g) with hu
  have hτu : (τ' : G) = u * S.z * u⁻¹ := by
    show g₁⁻¹ * x * g₁ = u * S.z * u⁻¹
    rw [hu, hxdef]
    group
  have haQu : g * S.z * g⁻¹ ∈ S.Qa u := by
    have hzx : S.z ∈ S.Qa ((kx : G) * g) := S.z_mem_Qa_of_mem_QG rfl hxQ hxz
    have h1 : g₁⁻¹ * S.z * g₁⁻¹⁻¹ ∈ S.Qa (g₁⁻¹ * ((kx : G) * g)) := conj_mem_Qa_mul S hzx
    have e : g₁⁻¹ * S.z * g₁⁻¹⁻¹ = g * S.z * g⁻¹ := by rw [inv_inv, hg₁a']
    rwa [e] at h1
  obtain ⟨c, ⟨⟨hcQ, hcg⟩, hcu⟩, ⟨w, hcw⟩, hca⟩ :=
    D.exists_point hCE hP hF h7 ⟨hτL, hτX⟩ hτ1 rfl hτu haQu
  set c₁ := g₁ * c * g₁⁻¹ with hc₁
  have hc₁Q : c₁ ∈ S.QG := by
    have h1 : g₁ * c * g₁⁻¹ ∈ S.Qa (g₁ * g) := conj_mem_Qa_mul S hcg
    rw [S.Qa_eq_of_conj_eq (g := g₁ * g) (h := 1) (by
      rw [show (g₁ * g) * S.z * (g₁ * g)⁻¹ = g₁ * (g * S.z * g⁻¹) * g₁⁻¹ by group, hg₁a]
      group), Setting.Qa_one] at h1
    exact h1
  have hc₁f : c₁ ∈ S.Qa ((kf : G) * g) := by
    have h1 : g₁ * c * g₁⁻¹ ∈ S.Qa (g₁ * 1) := conj_mem_Qa_mul S (by rw [Setting.Qa_one]; exact hcQ)
    rwa [S.Qa_eq_of_conj_eq (g := g₁ * 1) (h := (kf : G) * g) (by rw [mul_one, hg₁z])] at h1
  have hc₁x : c₁ ∈ S.Qa ((kx : G) * g) := by
    have h1 : g₁ * c * g₁⁻¹ ∈ S.Qa (g₁ * u) := conj_mem_Qa_mul S hcu
    rwa [show g₁ * u = (kx : G) * g by rw [hu]; group] at h1
  have hc₁z : c₁ ≠ S.z := by
    intro h
    apply hca
    have e : c = g * S.z * g⁻¹ := by
      calc c = g₁⁻¹ * c₁ * g₁ := by rw [hc₁]; group
        _ = g₁⁻¹ * S.z * g₁ := by rw [h]
        _ = g * S.z * g⁻¹ := hg₁a'
    rw [e]
  have hc₁w : (g₁ * w) * S.z * (g₁ * w)⁻¹ = c₁ := by rw [hc₁, hcw]; group
  obtain ⟨m, hm, hma⟩ := hF (g₁ * w) (by rw [hc₁w]; exact hc₁Q) (by rw [hc₁w]; exact hc₁z)
  set m' : S.M := ⟨m, hm⟩ with hm'
  have hm'c : (m' : G) * g * S.z * ((m' : G) * g)⁻¹ = c₁ := by
    rw [← hc₁w, ← hma, hm']
    group
  have hGm : ⁅Yb, Yb⁆.map (cK S m') = ⁅Yb, Yb⁆ := by
    refine D.map_commutator_eq_of_mem_clSub_mul hCE hP h7 hx ?_
    rw [hm'c]
    exact S.cl_mem_clSub ⟨hc₁Q, hc₁x⟩ hc₁Q
  refine D.map_commutator_eq_of_mem_clSub_mul hCE hP h7 hGm ?_
  by_cases hcf : c₁ = f
  · have e : f = (m' : G) * g * S.z * ((m' : G) * g)⁻¹ := by rw [hm'c, hcf]
    change S.cl f ∈ S.clSub (S.QG ⊓ S.Qa ((m' : G) * g))
    rw [e]
    exact cl_mem_clSub_self (conj_mem_QG' S m'.2 X.haQ)
  · have h1 : (m' : G) * g * S.z * ((m' : G) * g)⁻¹ ∈ S.Qa ((kf : G) * g) := by
      rw [hm'c]
      exact hc₁f
    have h2 := S.mem_Qa_symm (by rw [hm'c]; exact hcf) h1
    exact S.cl_mem_clSub ⟨hfQ, h2⟩ hfQ

theorem good_of_space (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) (hF : S6.FusionCtl S g)
    (h7 : 7 ≤ S.width)
    (hU : ∃ U : Submodule (ZMod 2) S.Qt, finrank (ZMod 2) U = 3 ∧ ∀ v ∈ U, v ≠ 0 →
      ∃ k : S.M, v = S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∧
        ⁅Yb, Yb⁆.map (cK S k) = ⁅Yb, Yb⁆)
    (kf : S.M) : ⁅Yb, Yb⁆.map (cK S kf) = ⁅Yb, Yb⁆ := by
  obtain ⟨U, hU3, hUg⟩ := hU
  obtain ⟨kd, hkd, hkd1, hne, hPa, -⟩ := D.exists_d hCE
  set fv := S.cl ((kf : G) * g * S.z * ((kf : G) * g)⁻¹) with hfv
  set αv := S.cl (((kf * kd : S.M) : G) * g * S.z * (((kf * kd : S.M) : G) * g)⁻¹) with hαv
  set L : U →ₗ[ZMod 2] ZMod 2 × ZMod 2 :=
    (LinearMap.prod (S.q.polarBilin fv) (S.q.polarBilin αv)).comp U.subtype with hL
  have hrk := LinearMap.finrank_range_add_finrank_ker L
  have hr : finrank (ZMod 2) (LinearMap.range L) ≤ 2 := by
    refine (Submodule.finrank_le _).trans ?_
    rw [Module.finrank_prod, Module.finrank_self]
  have hker : LinearMap.ker L ≠ ⊥ := by
    intro h
    rw [h, finrank_bot, hU3] at hrk
    omega
  obtain ⟨y, hyk, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hv0' : (y : S.Qt) ≠ 0 := fun h => hy0 (Subtype.ext h)
  obtain ⟨kx, hvx, hgx⟩ := hUg y y.2 hv0'
  have hLv : L y = 0 := hyk
  have h1 : S.q.polarBilin fv (y : S.Qt) = 0 := congrArg Prod.fst hLv
  have h2 : S.q.polarBilin αv (y : S.Qt) = 0 := congrArg Prod.snd hLv
  rw [polarBilin_apply_apply, hvx] at h1 h2
  have hxQ := conj_mem_QG' S kx.2 X.haQ
  have hxf := (S.polar_cl_eq_zero_iff (conj_mem_QG' S kf.2 X.haQ) hxQ).mp h1
  have hxα := (S.polar_cl_eq_zero_iff (conj_mem_QG' S (kf * kd).2 X.haQ) hxQ).mp h2
  exact D.good_of_commute hCE hP hF h7 hkd hkd1 hne hPa hgx hxf.symm hxα.symm

end Dec108

end CFSG.LargeExtraspecial.S10
