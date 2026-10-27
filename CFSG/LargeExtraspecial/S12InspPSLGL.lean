module

public import CFSG.LargeExtraspecial.S12InspPSLPair
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Submodule QuadraticMap CFSG.RankThree.OrthogonalInvolutions S12InspPSL
open CFSG.ComponentClassification.OutcomeLocal (IsF2Transvection tv)

namespace S12InspPSL

theorem nonempty_gl_mulEquiv_sl {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {n : ℕ} (h : finrank (ZMod 2) W = n) :
    Nonempty (LinearMap.GeneralLinearGroup (ZMod 2) W ≃*
      Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
  ⟨(LinearMap.GeneralLinearGroup.congrLinearEquiv
      (Module.finBasisOfFinrankEq (ZMod 2) W h).equivFun).trans
    (Matrix.GeneralLinearGroup.toLin.symm.trans
      (CFSG.QuasithinUnique.Setup.Family.slEquivGL n).symm)⟩

end S12InspPSL

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem psl_isF2Transvection_of_mem_Ebar12 {g : G} {t : S.O} (hS : S.S12Standing g t)
    {U : Submodule (ZMod 2) S.Qt} (hU : IsInv (S.actX12 g) U) {c : S.Qt} (hc : c ∈ U)
    (htc : ∀ u ∈ U, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ span (ZMod 2) {c})
    (hne : ∃ u ∈ U, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) u ≠ u) {e : S.Xbar12 g}
    (he : (e : S.O) ∈ S.Ebar12 g) : IsF2Transvection (resGL (S.actX12 g) U hU e) := by
  obtain ⟨x, hx, hex⟩ := hS.cls _ he
  have hxU : ∀ {u}, u ∈ U → (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U := fun hu => hU ⟨x, hx⟩ _ hu
  have hx'U : ∀ {u}, u ∈ U → ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U := fun hu =>
    hU ⟨x⁻¹, (S.Xbar12 g).inv_mem hx⟩ _ hu
  have happ : ∀ u, S.actX12 g e u = (x : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u)) := fun u => by
    rw [actX12_apply, hex, Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply]
  refine isF2Transvection_resGL hU (hxU hc) (fun u hu => ?_) ?_
  · have h := htc _ (hx'U hu)
    rw [mem_span_singleton_iff] at h ⊢
    rw [happ]
    rcases h with h | h
    · left
      rw [sub_eq_zero.mp h, psl_apply_inv_apply, sub_self]
    · right
      rw [sub_eq_iff_eq_add.mp h, map_add, psl_apply_inv_apply, add_sub_cancel_right]
  · obtain ⟨u, hu, htu⟩ := hne
    refine ⟨(x : S.Qt ≃ₗ[ZMod 2] S.Qt) u, hxU hu, fun h => htu ?_⟩
    rw [happ, psl_inv_apply_apply] at h
    exact (x : S.Qt ≃ₗ[ZMod 2] S.Qt).injective h

theorem psl_range_eq_top_of_pow_six {g : G} {t : S.O} (hS : S.S12Standing g t)
    {U : Submodule (ZMod 2) S.Qt} (hU : IsInv (S.actX12 g) U) {c : S.Qt} (hc : c ∈ U)
    (htc : ∀ u ∈ U, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ span (ZMod 2) {c})
    (hne : ∃ u ∈ U, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) u ≠ u)
    (hirr : ∀ V : Submodule (ZMod 2) S.Qt, V ≤ U → IsInv (S.actX12 g) V → V = ⊥ ∨ V = U)
    {d e : S.O} (hd : d ∈ S.Ebar12 g) (he : e ∈ S.Ebar12 g)
    (hz : ∃ u ∈ U, (((d * e) ^ 6 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ≠ u) :
    (resGL (S.actX12 g) U hU).range = ⊤ := by
  set d' : S.Xbar12 g := ⟨d, subset_Xbar12 hd⟩
  set e' : S.Xbar12 g := ⟨e, subset_Xbar12 he⟩
  have htv : ∀ x ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)),
      IsF2Transvection (resGL (S.actX12 g) U hU x) := fun x hx =>
    psl_isF2Transvection_of_mem_Ebar12 hS hU hc htc hne hx
  obtain ⟨φ, a, ha, hφ, ha0, hda, -⟩ := exists_tv_of_isF2Transvection hU (htv d' hd)
  obtain ⟨ψ, b, hb, hψ, hb0, heb, -⟩ := exists_tv_of_isF2Transvection hU (htv e' he)
  have hdih : φ b ≠ ψ a := by
    intro hs
    obtain ⟨u, hu, hzu⟩ := hz
    apply hzu
    have h6 : resGL (S.actX12 g) U hU ((d' * e') ^ 6) = 1 := by
      rw [map_pow, map_mul, hda, heb]
      exact tv_mul_tv_pow_six ha hb hs
    have := (resGL_eq_one_iff hU _).mp h6 u hu
    rw [actX12_apply] at this
    exact this
  exact range_eq_top_of_dihedral hU (s12_closure_preimage_eq_top rfl) htv hirr ha hb hφ hψ ha0
    hb0 hda heb hdih

theorem psl_apply_eq_of_compl {t : S.O} {W W' : Submodule (ZMod 2) S.Qt}
    (hsing : ∀ w ∈ W, S.q w = 0) (hdim : finrank (ZMod 2) W = S.width) (hinf : W ⊓ W' = ⊥)
    {c c' : S.Qt} (hc' : c' ∈ W') (hc'0 : c' ≠ 0) (hcc' : polar S.q c c' = 0)
    (htc : ∀ w ∈ W, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ span (ZMod 2) {c})
    (htc' : ∀ w ∈ W', (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ span (ZMod 2) {c'})
    (hne' : ∃ w ∈ W', (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w) :
    ∀ w ∈ W, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + polar S.q w c' • c := by
  obtain ⟨w₀, hw₀, htw₀⟩ := hne'
  have ht0 : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w₀ = w₀ + c' := by
    have h := htc' w₀ hw₀
    rw [mem_span_singleton_iff] at h
    rcases h with h | h
    · exact absurd (sub_eq_zero.mp h) htw₀
    · rw [← h, add_sub_cancel]
  have key : ∀ w ∈ W, ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w ∧ polar S.q w c' = 0) ∨
      ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + c ∧ polar S.q w c' = polar S.q c w₀) := by
    intro w hw
    have hiso := psl_polar_apply_apply t w w₀
    rw [ht0] at hiso
    have h := htc w hw
    rw [mem_span_singleton_iff] at h
    rcases h with h | h
    · left
      refine ⟨sub_eq_zero.mp h, ?_⟩
      rw [sub_eq_zero.mp h, polar_add_right] at hiso
      exact add_eq_left.mp hiso
    · right
      have htw : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + c := by rw [← h, add_sub_cancel]
      refine ⟨htw, ?_⟩
      rw [htw, polar_add_right, polar_add_left, polar_add_left, hcc', add_zero] at hiso
      have e : polar S.q w c' + polar S.q c w₀ = 0 := by
        have := congrArg (fun r => r - polar S.q w w₀) hiso
        simp only [sub_self] at this
        rw [← this]
        ring
      rw [← sub_eq_zero, sub_eq_add']
      exact e
  have hκ : polar S.q c w₀ = 1 := by
    rcases zmod2_cases (polar S.q c w₀) with h0 | h1
    · exfalso
      have hmem : c' ∈ W := psl_mem_of_polar_eq_zero hsing hdim fun w hw => by
        rcases key w hw with ⟨-, h⟩ | ⟨-, h⟩
        · exact h
        · rw [h, h0]
      have : c' ∈ W ⊓ W' := ⟨hmem, hc'⟩
      rw [hinf, Submodule.mem_bot] at this
      exact hc'0 this
    · exact h1
  intro w hw
  rcases key w hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, zero_smul, add_zero]
  · rw [h1, h2, hκ, one_smul]

theorem pslPair_of_pow_six {g : G} {t : S.O} (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (htX : t ∈ S.Xbar12 g) (hS : S.S12Standing g t) {W W' : Submodule (ZMod 2) S.Qt}
    (hinf : W ⊓ W' = ⊥) (hsup : W ⊔ W' = ⊤) (hW : IsInv (S.actX12 g) W)
    (hW' : IsInv (S.actX12 g) W')
    (hirr : ∀ U, U ≤ W → IsInv (S.actX12 g) U → U = ⊥ ∨ U = W)
    (hirr' : ∀ U, U ≤ W' → IsInv (S.actX12 g) U → U = ⊥ ∨ U = W')
    (hdim : finrank (ZMod 2) W = finrank (ZMod 2) W')
    (hne : ∃ w ∈ W, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w)
    (hne' : ∃ w ∈ W', (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w)
    {d e : S.O} (hd : d ∈ S.Ebar12 g) (he : e ∈ S.Ebar12 g)
    (hz : ∃ u ∈ W, (((d * e) ^ 6 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ≠ u) :
    Nonempty (S.PSLPair g t) := by
  obtain ⟨⟨c, hc, hc0, hcT, htc⟩, ⟨c', hc', hc'0, hc'T, htc'⟩, -⟩ :=
    psl_comm_lines htA htX hW hW' hinf hne hne'
  have hz6 : (d * e) ^ 6 ∈ S.Xbar12 g :=
    pow_mem (mul_mem (subset_Xbar12 hd) (subset_Xbar12 he)) 6
  have htop := psl_range_eq_top_of_pow_six hS hW hc htc hne hirr hd he hz
  have hlift : ∀ (ψ : S.Qt →ₗ[ZMod 2] ZMod 2) (u : S.Qt), u ∈ W → ψ u = 0 →
      ∃ x ∈ S.Xbar12 g, ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + ψ w • u := by
    intro ψ u hu hψu
    obtain ⟨x, hx⟩ := exists_lift_tv hW htop ψ hu hψu
    exact ⟨x, x.2, hx⟩
  have hsing := psl_sing_of_lift hlift hc hc0 (htA.2.2.2.2 c hcT)
  have hdimW := psl_finrank_eq_width_of_compl hinf hsup hdim
  have hz' : ∃ u ∈ W', (((d * e) ^ 6 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ≠ u := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u, hu, hzu⟩ := hz
    exact hzu (psl_fix_of_fix_compl hsing hsup (fun w hw => hW ⟨_, hz6⟩ w hw) hcon u hu)
  have htop' := psl_range_eq_top_of_pow_six hS hW' hc' htc' hne' hirr' hd he hz'
  have hlift' : ∀ (ψ : S.Qt →ₗ[ZMod 2] ZMod 2) (u : S.Qt), u ∈ W' → ψ u = 0 →
      ∃ x ∈ S.Xbar12 g, ∀ w ∈ W', (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + ψ w • u := by
    intro ψ u hu hψu
    obtain ⟨x, hx⟩ := exists_lift_tv hW' htop' ψ hu hψu
    exact ⟨x, x.2, hx⟩
  have hsing' := psl_sing_of_lift hlift' hc' hc'0 (htA.2.2.2.2 c' hc'T)
  have hdimW' : finrank (ZMod 2) W' = S.width := hdim ▸ hdimW
  have hcc' : polar S.q c c' = 0 := polar_commSpace_eq_zero t.2 htA.2.2.1 hcT hc'T
  have htW := psl_apply_eq_of_compl hsing hdimW hinf hc' hc'0 hcc' htc htc' hne'
  have htW' := psl_apply_eq_of_compl hsing' hdimW' (by rw [inf_comm]; exact hinf) hc hc0
    (by rw [polar_comm]; exact hcc') htc' htc hne
  have hinj : Function.Injective (resGL (S.actX12 g) W hW) := by
    refine (injective_iff_map_eq_one _).mpr fun x hx => Subtype.ext ?_
    exact psl_eq_one_of_fix hsing hdimW hinf hsup (fun w hw => hW' x w hw)
      ((resGL_eq_one_iff hW x).mp hx)
  have hsurj : Function.Surjective (resGL (S.actX12 g) W hW) := MonoidHom.range_eq_top.mp htop
  obtain ⟨e₂⟩ := nonempty_gl_mulEquiv_sl hdimW
  exact ⟨⟨W, W', c, c', hinf, hsup, hW, hW', hsing, hsing', hdimW, hdimW', hc, hc', hc0, hc'0,
    htW, htW', hlift, hlift', ⟨(MulEquiv.ofBijective _ ⟨hinj, hsurj⟩).trans e₂⟩⟩⟩

theorem irred_or_pslPair {g : G} {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hS : S.S12Standing g t)
    (hred : ¬ S.IsReducible12) (hnd : S.IsNondeg12 g) :
    (∀ U : Submodule (ZMod 2) S.Qt, IsInv (S.actX12 g) U → U = ⊥ ∨ U = ⊤) ∨
      Nonempty (S.PSLPair g t) := by
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  rcases psl_decomp ht htA hS hred with hirr | ⟨W, W', hinf, hsup, hW, hW', hirr, hirr', hdim,
    hne, hne'⟩
  · exact Or.inl hirr
  right
  obtain ⟨d, hd, e, he, h4⟩ := hnd
  have hz1 : (d * e) ^ 6 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [h4] at this
    norm_num at this
  have hz : (∃ u ∈ W, (((d * e) ^ 6 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ≠ u) ∨
      (∃ u ∈ W', (((d * e) ^ 6 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ≠ u) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    apply hz1
    apply Subtype.ext
    refine LinearEquiv.ext fun v => ?_
    have hv : v ∈ W ⊔ W' := hsup ▸ mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hv
    rw [map_add, h1 y hy, h2 z hz]
    rfl
  rcases hz with hz | hz
  · exact pslPair_of_pow_six htA htX hS hinf hsup hW hW' hirr hirr' hdim hne hne' hd he hz
  · exact pslPair_of_pow_six htA htX hS (by rw [inf_comm]; exact hinf)
      (by rw [sup_comm]; exact hsup) hW' hW hirr' hirr hdim.symm hne' hne hd he hz

end Setting

end CFSG.LargeExtraspecial
