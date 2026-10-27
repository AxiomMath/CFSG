module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoCase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Q3.AE

section Rho


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem secAut_one (hc : P23Cfg n Y R S t K' W u e g) (q : SecQ R e) :
    TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) 1 q = q := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ q
  exact TwinExitPf6.secAut_mk (hΩ_of hc) (hc2e_of hc) 1 h h (by simp)

@[expose] noncomputable def actHom (hc : P23Cfg n Y R S t K' W u e g) {H : Subgroup Y}
    (hH : H ≤ Subgroup.centralizer ({e} : Set Y)) : ↥H →* MulAut (SecQ R e) where
  toFun x := TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨x, hH x.2⟩
  map_one' := by
    ext q
    exact secAut_one hc q
  map_mul' x x' := by
    ext q
    exact secAut_mul hc ⟨x, hH x.2⟩ ⟨x', hH x'.2⟩ q

theorem actHom_apply (hc : P23Cfg n Y R S t K' W u e g) {H : Subgroup Y}
    (hH : H ≤ Subgroup.centralizer ({e} : Set Y)) (x : ↥H) (q : SecQ R e) :
    actHom hc hH x q = TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨x, hH x.2⟩ q := rfl

theorem actHom_inner (hc : P23Cfg n Y R S t K' W u e g) {H : Subgroup Y}
    (hH : H ≤ Subgroup.centralizer ({e} : Set Y)) (x : ↥H) (hxE : (x : Y) ∈ rLayer (Om R) e)
    (q : SecQ R e) :
    actHom hc hH x q = piE hc ⟨x, hxE⟩ * q * (piE hc ⟨x, hxE⟩)⁻¹ := by
  obtain ⟨x', rfl⟩ := piE_surjective hc q
  have hcx : (x : Y) * (x' : Y) * (x : Y)⁻¹ ∈ rLayer (Om R) e :=
    (rLayer (Om R) e).mul_mem ((rLayer (Om R) e).mul_mem hxE x'.2) ((rLayer (Om R) e).inv_mem hxE)
  rw [actHom_apply, secAut_piE hc (hH x.2) x' hcx]
  show piE hc ⟨(x : Y) * (x' : Y) * (x : Y)⁻¹, hcx⟩ = piE hc ⟨x, hxE⟩ * piE hc x' * (piE hc ⟨x, hxE⟩)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem e_comm_t (hc : P23Cfg n Y R S t K' W u e g) : e * t = t * e :=
  Q3CL.Thompson.commutes_of_mem_WSet (hΩ_of hc) hc.data.hW e (T7K.e_mem_inf hc.data).1 t
    hc.data.hzW

theorem exists_rho_of_odd (hc : P23Cfg n Y R S t K' W u e g)
    (D : AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) {y : Y}
    (hyC : y ∈ Subgroup.centralizer ({e} : Set Y)) (hy2 : y * y = 1) {w : Wr 6}
    (hw : D.toAEData.Acts (TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩) w)
    (hodd : Equiv.Perm.sign w.perm = -1) :
    ∃ ρ : ↥(Subgroup.closure ({e, t, y} : Set Y) ⊔ rLayer (Om R) e) →* Equiv.Perm (Fin 6),
      Function.Surjective ρ ∧
      ρ.ker ≤ (rLayer (Om R) e).subgroupOf (Subgroup.closure ({e, t, y} : Set Y) ⊔ rLayer (Om R) e) := by
  classical
  set E := rLayer (Om R) e with hEdef
  set Γ := Subgroup.closure ({e, t, y} : Set Y) ⊔ E with hΓdef
  have hΩ := hΩ_of hc
  have hgenC : Subgroup.closure ({e, t, y} : Set Y) ≤ Subgroup.centralizer ({e} : Set Y) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · rw [hx]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (e_comm_t hc).symm
    · rw [hx]
      exact hyC
  have hEC : E ≤ Subgroup.centralizer ({e} : Set Y) := F7C.rLayer_le_centralizer e
  have hΓC : Γ ≤ Subgroup.centralizer ({e} : Set Y) := sup_le hgenC hEC
  have hyΓ : y ∈ Γ := Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hα : ∀ x : ↥Γ, ∀ L ∈ TwinDisc.secFam (Om R) e,
      L.map (actHom hc hΓC x).toMonoidHom ∈ TwinDisc.secFam (Om R) e :=
    fun x L hL => secAut_preserves hc ⟨x, hΓC x.2⟩ hL
  obtain ⟨ρ, hρ⟩ := D.toAEData.exists_rho (actHom hc hΓC) hα
  have even_of_mem : ∀ x : ↥Γ, (x : Y) ∈ E → Equiv.Perm.sign (ρ x) = 1 := by
    intro x hxE
    obtain ⟨w', hw'perm, hw'⟩ := hρ x
    have hAct : D.toAEData.Acts (fun q => piE hc ⟨x, hxE⟩ * q * (piE hc ⟨x, hxE⟩)⁻¹) w' := by
      intro q
      show D.φ (piE hc ⟨x, hxE⟩ * q * (piE hc ⟨x, hxE⟩)⁻¹) = _
      rw [← actHom_inner hc hΓC x hxE q]
      exact hw' q
    rw [← hw'perm]
    exact D.toAEData.sign_eq_one_of_inner _ hAct
  have inner_surj : ∀ s : Equiv.Perm (Fin 6), Equiv.Perm.sign s = 1 →
      ∃ x : ↥Γ, (x : Y) ∈ E ∧ ρ x = s := by
    intro s hs
    obtain ⟨q₀, hq₀⟩ := D.toAEData.exists_inner_perm s hs
    obtain ⟨x₀, rfl⟩ := piE_surjective hc q₀
    set x : ↥Γ := ⟨x₀, Subgroup.mem_sup_right x₀.2⟩ with hx
    refine ⟨x, x₀.2, ?_⟩
    obtain ⟨w', hw'perm, hw'⟩ := hρ x
    have hAct : D.toAEData.Acts (fun q => piE hc x₀ * q * (piE hc x₀)⁻¹) w' := by
      intro q
      have := actHom_inner hc hΓC x x₀.2 q
      show D.φ (piE hc x₀ * q * (piE hc x₀)⁻¹) = _
      have h3 : piE hc ⟨(x : Y), x₀.2⟩ = piE hc x₀ := rfl
      rw [h3] at this
      rw [← this]
      exact hw' q
    have h1 := D.toAEData.acts_perm_unique hAct hq₀
    rw [← hw'perm, h1]
    rfl
  have odd_y : Equiv.Perm.sign (ρ ⟨y, hyΓ⟩) = -1 := by
    obtain ⟨w', hw'perm, hw'⟩ := hρ ⟨y, hyΓ⟩
    have h1 := D.toAEData.acts_perm_unique hw' hw
    rw [← hw'perm, h1]
    exact hodd
  refine ⟨ρ, ?_, ?_⟩
  · intro σ
    by_cases hσ : Equiv.Perm.sign σ = 1
    · obtain ⟨x, -, hx⟩ := inner_surj σ hσ
      exact ⟨x, hx⟩
    · have hσ' : Equiv.Perm.sign σ = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · exact absurd h hσ
        · exact h
      obtain ⟨x, -, hx⟩ := inner_surj (σ * (ρ ⟨y, hyΓ⟩)⁻¹) (by
        rw [map_mul, map_inv, odd_y, hσ']
        decide)
      refine ⟨x * ⟨y, hyΓ⟩, ?_⟩
      rw [map_mul, hx]
      group
  ·
    have hyN : ∀ a ∈ E, y * a * y⁻¹ ∈ E := by
      intro a ha
      have := conj_mem_conjSub (n := y) ha
      rwa [conjSub_rLayer_eq hΩ hyC] at this
    let T : Subgroup Y :=
      { carrier := {g | g ∈ E ∨ y * g ∈ E}
        mul_mem' := by
          rintro a b (ha | ha) (hb | hb)
          · exact Or.inl (E.mul_mem ha hb)
          · right
            have : y * (a * b) = (y * a * y⁻¹) * (y * b) := by group
            rw [this]
            exact E.mul_mem (hyN a ha) hb
          · right
            have : y * (a * b) = (y * a) * b := by group
            rw [this]
            exact E.mul_mem ha hb
          · left
            have : a * b = (y * (y * a) * y⁻¹) * (y * b) := by
              calc a * b = (y * y) * (a * b) := by rw [hy2, one_mul]
                _ = (y * (y * a) * y⁻¹) * (y * b) := by group
            rw [this]
            exact E.mul_mem (hyN _ ha) hb
        one_mem' := Or.inl E.one_mem
        inv_mem' := by
          rintro a (ha | ha)
          · exact Or.inl (E.inv_mem ha)
          · right
            have : y * a⁻¹ = (y * (y * a)⁻¹ * y⁻¹) := by
              calc y * a⁻¹ = (y * (y * a)⁻¹ * y⁻¹) * (y * y) := by group
                _ = (y * (y * a)⁻¹ * y⁻¹) := by rw [hy2, mul_one]
            rw [this]
            exact hyN _ (E.inv_mem ha) }
    have hΓT : Γ ≤ T := by
      refine sup_le ?_ (fun a ha => Or.inl ha)
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx
      · rw [hx]
        exact Or.inl (t_e_mem_rLayer hc).2
      · rw [hx]
        exact Or.inl (t_e_mem_rLayer hc).1
      · rw [hx]
        right
        show y * y ∈ E
        rw [hy2]
        exact E.one_mem
    intro gg hgg
    have hgg1 : ρ gg = 1 := hgg
    rw [Subgroup.mem_subgroupOf]
    rcases hΓT gg.2 with hgE | hygE
    · exact hgE
    · exfalso
      set g' : ↥Γ := ⟨y, hyΓ⟩ * gg with hg'
      have h1 : Equiv.Perm.sign (ρ g') = 1 := even_of_mem g' (by simpa [hg'] using hygE)
      have h2 : ρ g' = ρ ⟨y, hyΓ⟩ := by rw [hg', map_mul, hgg1, mul_one]
      rw [h2, odd_y] at h1
      revert h1
      decide

end Rho

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo
