module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S9Diag
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S9Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S9Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Toolbox

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus
open CFSG.QuasithinUnique.Setup.X3Aut

section

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem PA8.ub_cent_L₁ (a : PA8 L t E z) :
    (∀ k ∈ a.L₁, Commute a.ub k) ∧ ∀ k ∈ a.L₁, Commute a.ub (t * k * t⁻¹) := by
  have hF : a.ub ∈ a.F₀ := by
    cases h : a.dcase
    · obtain ⟨-, -, -, -, hF₀, -⟩ := a.d8_props h
      rw [hF₀]
      exact mem_sup_left (mem_zpowers _)
    · rw [(a.F₀_e4 h).1]
      exact mem_zpowers _
  rw [← a.CPE_eq] at hF
  obtain ⟨-, hc⟩ := hF
  have hle : a.L₁ ⊔ conjSub t a.L₁ ≤ Cen a.ub := by
    intro g hg
    exact mem_Cen.2 (mem_centralizer_iff.1 hc g hg)
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · exact (mem_Cen.1 (hle (mem_sup_left hk))).symm
  · exact (mem_Cen.1 (hle (mem_sup_right (show t * k * t⁻¹ ∈ conjSub t a.L₁ from
      ⟨k, hk, rfl⟩)))).symm

theorem u_mem_Cen_ub (hb : PAB G L t E W z) (a : PA8 L t E z) (hub : a.ub = t * a.u) :
    a.u ∈ Cen a.ub := by
  rw [mem_Cen, hub]
  have hut : a.u * t = t * a.u := mem_centralizer_iff.1 hb.t_cent a.u (a.K₀_le a.u_mem).1
  calc a.u * (t * a.u) = (a.u * t) * a.u := by rw [mul_assoc]
    _ = t * a.u * a.u := by rw [hut]

theorem rho_u_eq_tau (hb : PAB G L t E W z) (a : PA8 L t E z) (hub : a.ub = t * a.u) :
    (PA8.pairData hb a).rho ⟨a.u, u_mem_Cen_ub hb a hub⟩ = tau := by
  have pd := PA8.pairData hb a
  have hubP : a.ub ∈ Cen a.ub := mem_Cen.2 rfl
  have h1 : pd.rho ⟨a.ub, hubP⟩ = 1 := by
    rw [pd.rho_eq_one_iff]
    exact PA8.ub_cent_L₁ a
  have h2 : (⟨a.u, u_mem_Cen_ub hb a hub⟩ : ↥(Cen a.ub)) =
      ⟨t, pd.t_mem⟩ * ⟨a.ub, hubP⟩ := by
    refine Subtype.ext ?_
    show a.u = t * a.ub
    rw [hub, ← mul_assoc, hb.t_mul_t, one_mul]
  rw [h2, map_mul, h1, mul_one]
  exact pd.rho_t

theorem innR_normal : innR.Normal :=
  ⟨fun a ⟨b, hb⟩ g => ⟨g b, by
    rw [← hb]
    exact (conj_thetaEquiv_apply g b).symm⟩⟩

theorem PA8.u_sq_twisted (hb : PAB G L t E W z) (a : PA8 L t E z) (hub : a.ub = t * a.u) :
    a.u * a.u = 1 ∧ a.u ≠ 1 := by
  have hut : a.u * t = t * a.u := mem_centralizer_iff.1 hb.t_cent a.u (a.K₀_le a.u_mem).1
  have h1 : a.ub * a.ub = 1 := mul_self_eq_one_of_orderOf_eq_two_fullness a.ub_ord
  refine ⟨?_, ?_⟩
  · rw [hub] at h1
    have : t * a.u * (t * a.u) = (t * t) * (a.u * a.u) := by
      calc t * a.u * (t * a.u) = t * (a.u * t) * a.u := by simp only [mul_assoc]
        _ = t * (t * a.u) * a.u := by rw [hut]
        _ = (t * t) * (a.u * a.u) := by simp only [mul_assoc]
    rw [this, hb.t_mul_t, one_mul] at h1
    exact h1
  · intro h
    apply a.ub_nconj
    rw [hub, h, mul_one]

theorem exists_pgl_class (hb : PAB G L t E W z) (a : PA8 L t E z) (hub : a.ub = t * a.u) :
    ∃ ℓ : G, ∃ hℓ : ℓ ∈ Cen a.ub, ℓ ∈ L ∧ ℓ * ℓ = 1 ∧ IsConj a.u ℓ ∧
      ∃ γ : MulAut ↥a.L₁, (PA8.pairData hb a).rho ⟨ℓ, hℓ⟩ = base γ γ ∧
        Nat.card (centralizer ({γ} : Set (MulAut ↥a.L₁))) ≤ 40 := by
  have pd := PA8.pairData hb a
  have hL : IsSporadic ↥L .HS := hb.setting.2.1
  have hperf : commutator ↥a.L₁ = ⊤ := a.L₁_comp.2.2.2.1
  obtain ⟨e⟩ := a.L₁_A6
  have hA : Nat.card (MulAut ↥a.L₁) ≤ 1440 :=
    (card_mulAut_le_of_perfect hperf e).trans (by rw [card_mulAut_alt6])
  have huL : a.u ∈ L := (a.K₀_le a.u_mem).1
  have hut : a.u * t = t * a.u := mem_centralizer_iff.1 hb.t_cent a.u huL
  obtain ⟨hu2, hu1⟩ := PA8.u_sq_twisted hb a hub
  have huP : a.u ∈ Cen a.ub := u_mem_Cen_ub hb a hub
  have hAbP : a.Abar ≤ Cen a.ub := fun x hx => by
    have hxu : x * a.u = a.u * x := mem_Cen.1 (a.Abar_le hx).2
    have hxt : x * t = t * x := mem_centralizer_iff.1 hb.t_cent x (a.Abar_le hx).1
    rw [mem_Cen, hub]
    calc x * (t * a.u) = (x * t) * a.u := by rw [mul_assoc]
      _ = t * (x * a.u) := by rw [hxt, mul_assoc]
      _ = t * (a.u * x) := by rw [hxu]
      _ = t * a.u * x := by rw [mul_assoc]
  have hAbt : ∀ x ∈ a.Abar, x * t = t * x := fun x hx =>
    mem_centralizer_iff.1 hb.t_cent x (a.Abar_le hx).1
  have hCJ : ∀ x ∈ a.Abar, (∀ j ∈ (derivedIn a.Abar : Subgroup G), x * j = j * x) → x = 1 := by
    intro x hx h
    have hxC : x ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) :=
      mem_centralizer_iff.2 fun j hj => (h j hj).symm
    have hxm : x ∈ L ⊓ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) :=
      ⟨(a.Abar_le hx).1, hxC⟩
    rw [a.C_L_J] at hxm
    exact (Subgroup.disjoint_def.1 a.Abar_disj) hxm hx
  have hAb : Nat.card a.Abar = 1440 := by
    rw [Nat.card_congr a.eAbar.toEquiv]
    exact card_mulAut_alt6
  obtain ⟨θ, hθ⟩ := rho_diag_iso pd a.Abar (derivedIn a.Abar) hAbP hAbt (derivedIn_le a.Abar)
    a.J_le hCJ hAb hA
  let Φ : MulAut ↥a.L₁ ≃* MulAut (alternatingGroup (Fin 6)) := autEquiv hperf e (by
    rw [card_mulAut_alt6, Nat.card_congr θ.toEquiv.symm, hAb])
  obtain ⟨α, hα2, hαinn, hαfix⟩ := exists_pgl_involution
  have hα1 : α ≠ 1 := fun h => hαinn (h ▸ one_mem _)
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hnab : ∃ x y : alternatingGroup (Fin 6), x * y ≠ y * x := by
    refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
      ⟨Equiv.swap 0 1 * Equiv.swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩, ?_⟩
    intro h
    have := congrArg Subtype.val h
    revert this
    decide
  set a₀ : MulAut ↥a.L₁ := Φ.symm α with ha₀
  set x' : ↥a.Abar := θ.symm a₀ with hx'
  have hΦa₀ : Φ a₀ = α := MulEquiv.apply_symm_apply Φ α
  have hθx : θ x' = a₀ := MulEquiv.apply_symm_apply θ a₀
  let Ψ : MulAut (MulAut (alternatingGroup (Fin 6))) := (Φ.symm.trans θ.symm).trans a.eAbar
  obtain ⟨β, hβ⟩ := mulAut_mulAut_eq_conj hnab Ψ
  have hΨα : a.eAbar x' = β * α * β⁻¹ := by
    have h1 : Ψ α = a.eAbar x' := rfl
    rw [← h1, hβ, MulAut.conj_apply]
  have hxinn : a.eAbar x' ∉ innR := by
    intro h
    rw [hΨα] at h
    have hN := innR_normal
    have := hN.conj_mem _ h β⁻¹
    apply hαinn
    simpa [mul_assoc] using this
  have hxfix : ∀ y : alternatingGroup (Fin 6), orderOf y = 3 → a.eAbar x' y ≠ y := by
    intro y hy h
    rw [hΨα] at h
    apply hαfix (β⁻¹ y)
    · rw [MulEquiv.orderOf_eq]; exact hy
    · have h2 : β (α (β⁻¹ y)) = y := h
      have := congrArg (fun w => β⁻¹ w) h2
      simpa using this
  have hx1 : (x' : G) ≠ 1 := by
    intro h
    apply hxinn
    have : x' = 1 := Subtype.ext h
    rw [this, map_one]
    exact one_mem _
  have hx2 : (x' : G) * x' = 1 := by
    have : x' * x' = 1 := by
      apply θ.injective
      rw [map_mul, hθx, map_one, ha₀, ← map_mul, hα2, map_one]
    simpa using congrArg Subtype.val this
  obtain ⟨hc1, hc2⟩ := a.tab_PGL (x' : G) x'.2 hx2 hx1 hxinn hxfix
  have hxL : (x' : G) ∈ L := (a.Abar_le x'.2).1
  have hxu : (x' : G) * a.u = a.u * x' := mem_Cen.1 (a.Abar_le x'.2).2
  have hxP : (x' : G) ∈ Cen a.ub := hAbP x'.2
  have hcen : Nat.card (centralizer ({a₀} : Set (MulAut ↥a.L₁))) ≤ 40 := by
    refine card_centralizer_le_of_equiv Φ 40 a₀ ?_
    rw [hΦa₀]
    exact card_centralizer_aut_le_forty α hα2 hα1 hαfix
  have hordu : orderOf a.u = 2 := orderOf_eq_two_of_sq hu2 hu1
  have hdf := hθ x'
  rw [hθx] at hdf
  rcases hdf with h | h
  ·
    have hxo : orderOf (x' : G) = 2 := orderOf_eq_two_of_sq hx2 hx1
    refine ⟨x', hxP, hxL, hx2, ?_, a₀, h, hcen⟩
    obtain ⟨g, hg, hgx⟩ := exists_conj_in_L hL huL hxL hordu hxo (a.card_Lu.trans hc1.symm)
    exact isConj_iff.2 ⟨g, hgx⟩
  ·
    have hux2 : (a.u * x') * (a.u * x') = 1 := by
      calc a.u * x' * (a.u * x') = a.u * (x' * a.u) * x' := by simp only [mul_assoc]
        _ = a.u * (a.u * x') * x' := by rw [hxu]
        _ = (a.u * a.u) * (x' * x') := by simp only [mul_assoc]
        _ = 1 := by rw [hu2, hx2, one_mul]
    have hux1 : a.u * x' ≠ 1 := by
      intro h1
      have hxinv : (x' : G) = a.u⁻¹ := eq_inv_of_mul_eq_one_right h1
      have hui : a.u⁻¹ = a.u := inv_eq_of_mul_eq_one_right hu2
      have hxu' : (x' : G) = a.u := hxinv.trans hui
      have hmem : a.u ∈ a.Abar := hxu' ▸ x'.2
      exact hu1 ((Subgroup.disjoint_def.1 a.Abar_disj) (mem_zpowers a.u) hmem)
    have huxo : orderOf (a.u * x') = 2 := orderOf_eq_two_of_sq hux2 hux1
    have huxL : a.u * x' ∈ L := L.mul_mem huL hxL
    refine ⟨a.u * x', mul_mem huP hxP, huxL, hux2, ?_, a₀, ?_, hcen⟩
    · obtain ⟨g, hg, hgx⟩ := exists_conj_in_L hL huL huxL hordu huxo (a.card_Lu.trans hc2.symm)
      exact isConj_iff.2 ⟨g, hgx⟩
    · have hρu := rho_u_eq_tau hb a hub
      have : (⟨a.u * x', mul_mem huP hxP⟩ : ↥(Cen a.ub)) = ⟨a.u, huP⟩ * ⟨x', hxP⟩ := rfl
      rw [this, map_mul, hρu]
      have h' : pd.rho ⟨x', hxP⟩ = base a₀ a₀ * tau := h
      rw [h', ← mul_assoc, tau_mul_base, mul_assoc, tau_mul_tau, mul_one]

end

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
