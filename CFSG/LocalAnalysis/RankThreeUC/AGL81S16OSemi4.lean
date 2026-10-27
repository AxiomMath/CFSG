module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OSemi1
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OSemi3
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OTs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite)

section Final

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F} {θ : F →+* F} {σ : OW F → OW F}

theorem semi_le_of_fixed (hadd : ∀ x y, σ (x + y) = σ x + σ y)
    (hsm : ∀ (r : F) x, σ (r • x) = θ r • σ x) (hσσ : ∀ x, σ (σ x) = x) {t : F}
    (ht : t + θ t = 1) {P S : Submodule F (OW F)} (hP : ∀ x ∈ P, σ x ∈ P)
    (hfix : ∀ z ∈ P, σ z = z → z ∈ S) : P ≤ S := by
  intro x hx
  obtain ⟨a, b, ha, hb, hxab⟩ := semi_decomp (M := ↥P) (fun y => (⟨σ y, hP y y.2⟩ : P)) θ
    (fun y y' => Subtype.ext (hadd y y')) (fun r y => Subtype.ext (hsm r y))
    (fun y => Subtype.ext (hσσ y)) ht ⟨x, hx⟩
  have ha' : (a : OW F) ∈ S := hfix a a.2 (congrArg Subtype.val ha)
  have hb' : (b : OW F) ∈ S := hfix b b.2 (congrArg Subtype.val hb)
  have hx' : x = (a : OW F) + t • (a : OW F) + (b : OW F) := congrArg Subtype.val hxab
  rw [hx']
  exact S.add_mem (S.add_mem ha' (S.smul_mem t ha')) hb'

theorem semi_plane_false (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hθ : θ ≠ RingHom.id F)
    (hθθ : ∀ r, θ (θ r) = r) (h : SemiInvol b c θ σ) {w u : OW F}
    (hli : LinearIndependent F ![w, u]) (hw : quadMinus 3 F b c w = 0)
    (hu : quadMinus 3 F b c u = 0) (hwu : polar (quadMinus 3 F b c) w u = 0)
    (hσw : σ w = w) {t₁ : F} (hσu : σ u = u + t₁ • w) : False := by
  classical
  obtain ⟨t, ht⟩ := semi_exists_trace_one θ hθ hθθ
  obtain ⟨Y, hYdim, hYmem⟩ : ∃ Y : Submodule F (OW F), Module.finrank F Y = 2 ∧
      ∀ x, x ∈ Y ↔ ∃ a a' : F, a • w + a' • u = x := by
    refine ⟨Submodule.span F {w, u}, ?_, fun x => Submodule.mem_span_pair⟩
    have h1 := finrank_span_eq_card hli
    have h2 : Set.range ![w, u] = ({w, u} : Set (OW F)) := by
      ext x
      simp [Fin.exists_fin_two, eq_comm, or_comm]
    rw [h2] at h1
    simpa using h1
  obtain ⟨P, hPdim, hPmem⟩ : ∃ P : Submodule F (OW F), 4 ≤ Module.finrank F P ∧
      ∀ x, x ∈ P ↔ polar (quadMinus 3 F b c) x w = 0 ∧ polar (quadMinus 3 F b c) x u = 0 := by
    let Φ : OW F →ₗ[F] F × F :=
      LinearMap.prod ((polarBilin (quadMinus 3 F b c)).flip w)
        ((polarBilin (quadMinus 3 F b c)).flip u)
    refine ⟨LinearMap.ker Φ, ?_, fun x => ?_⟩
    · have h1 := LinearMap.finrank_range_add_finrank_ker Φ
      have h2 : Module.finrank F (LinearMap.range Φ) ≤ 2 := by
        calc Module.finrank F (LinearMap.range Φ) ≤ Module.finrank F (F × F) :=
              Submodule.finrank_le _
          _ = 2 := by rw [Module.finrank_prod, Module.finrank_self]
      have h3 : Module.finrank F (OW F) = 6 := by
        rw [Module.finrank_fintype_fun_eq_card]
        simp
      omega
    · simp [Φ, LinearMap.mem_ker, Prod.ext_iff, polarBilin_apply_apply]
  have hPσ : ∀ x ∈ P, σ x ∈ P := by
    intro x hx
    obtain ⟨hxw, hxu⟩ := (hPmem x).mp hx
    refine (hPmem _).mpr ⟨?_, ?_⟩
    · have h1 := h.polar_eq x w
      rw [hσw, hxw, map_zero] at h1
      exact h1
    · have h1 := h.polar_eq x (σ u)
      rw [h.invol u, hσu, polar_add_right, polar_smul_right_eq, hxu, hxw, mul_zero, add_zero,
        map_zero] at h1
      exact h1
  have key : ∀ S : Submodule F (OW F), Module.finrank F S < 4 →
      ∃ z ∈ P, σ z = z ∧ z ∉ S := by
    intro S hS
    by_contra hno
    push Not at hno
    have hle : P ≤ S := semi_le_of_fixed h.add h.smul h.invol ht hPσ hno
    have h1 := Submodule.finrank_mono hle
    omega
  obtain ⟨z₁, hz₁P, hz₁f, hz₁Y⟩ := key Y (by omega)
  have hz₁0 : z₁ ≠ 0 := fun h0 => hz₁Y (by rw [h0]; exact Y.zero_mem)
  have hS₂ : Module.finrank F (Y ⊔ Submodule.span F {z₁} : Submodule F (OW F)) ≤ 3 := by
    calc Module.finrank F (Y ⊔ Submodule.span F {z₁} : Submodule F (OW F))
        ≤ Module.finrank F Y + Module.finrank F (Submodule.span F {z₁}) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
      _ = 3 := by rw [hYdim, finrank_span_singleton hz₁0]
  obtain ⟨z₂, hz₂P, hz₂f, hz₂S⟩ := key (Y ⊔ Submodule.span F {z₁}) (by omega)
  have hα : θ (quadMinus 3 F b c z₁) = quadMinus 3 F b c z₁ := by
    have h1 := h.quad z₁
    rw [hz₁f] at h1
    exact h1.symm
  have hγ : θ (quadMinus 3 F b c z₂) = quadMinus 3 F b c z₂ := by
    have h1 := h.quad z₂
    rw [hz₂f] at h1
    exact h1.symm
  have hβ : θ (polar (quadMinus 3 F b c) z₁ z₂) = polar (quadMinus 3 F b c) z₁ z₂ := by
    have h1 := h.polar_eq z₁ z₂
    rw [hz₁f, hz₂f] at h1
    exact h1.symm
  obtain ⟨c₁, c₂, hc, hbin⟩ := semi_exists_zero_binary θ hθ hθθ hα hβ hγ
  obtain ⟨z, hz⟩ : ∃ z : OW F, z = c₁ • z₁ + c₂ • z₂ := ⟨_, rfl⟩
  have hzP : z ∈ P := by
    rw [hz]
    exact P.add_mem (P.smul_mem _ hz₁P) (P.smul_mem _ hz₂P)
  have hzQ : quadMinus 3 F b c z = 0 := by
    rw [hz, QuadraticMap.map_add (quadMinus 3 F b c), map_smul_eq_sq, map_smul_eq_sq,
      polar_smul_left_eq, polar_smul_right_eq]
    linear_combination hbin
  have hzY : z ∉ Y := by
    intro hzY
    by_cases hc2 : c₂ = 0
    · have hc1 : c₁ ≠ 0 := by
        rcases hc with h1 | h2
        · exact h1
        · exact absurd hc2 h2
      apply hz₁Y
      have hzz : z = c₁ • z₁ := by rw [hz, hc2, zero_smul, add_zero]
      have h1 : z₁ = c₁⁻¹ • z := by rw [hzz, smul_smul, inv_mul_cancel₀ hc1, one_smul]
      rw [h1]
      exact Y.smul_mem _ hzY
    · apply hz₂S
      have h1 : z₂ = c₂⁻¹ • (z - c₁ • z₁) := by
        rw [hz, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc2, one_smul]
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.mem_sup_left hzY)
        (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z₁))))
  have hYQ : ∀ y ∈ Y, quadMinus 3 F b c y = 0 := by
    intro y hy
    obtain ⟨a, a', rfl⟩ := (hYmem y).mp hy
    rw [QuadraticMap.map_add (quadMinus 3 F b c), map_smul_eq_sq, map_smul_eq_sq,
      polar_smul_left_eq, polar_smul_right_eq, hw, hu, hwu]
    ring
  have hYB : ∀ y ∈ Y, polar (quadMinus 3 F b c) y z = 0 := by
    intro y hy
    obtain ⟨a, a', rfl⟩ := (hYmem y).mp hy
    obtain ⟨hzw, hzu⟩ := (hPmem z).mp hzP
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_comm _ w z,
      polar_comm _ u z, hzw, hzu]
    ring
  have hTQ : ∀ x ∈ Y ⊔ Submodule.span F {z}, quadMinus 3 F b c x = 0 := by
    intro x hx
    obtain ⟨y, hy, s, hs, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hs
    rw [QuadraticMap.map_add (quadMinus 3 F b c), hYQ y hy, map_smul_eq_sq, hzQ,
      polar_smul_right_eq, hYB y hy]
    ring
  obtain ⟨U, hTU, -, hUdim⟩ := exists_ts_span hirr
    (Y ⊔ Submodule.span F {z}).toAddSubgroup (fun x hx => by
      rw [← quadMinus_eq_stated]
      exact hTQ x hx)
  have hle : (Y ⊔ Submodule.span F {z} : Submodule F (OW F)) ≤ U := fun x hx => hTU x hx
  have h1 := Submodule.finrank_mono hle
  have hlt : Y < (Y ⊔ Submodule.span F {z} : Submodule F (OW F)) :=
    SetLike.lt_iff_le_and_exists.mpr
      ⟨le_sup_left, z, Submodule.mem_sup_right (Submodule.mem_span_singleton_self z), hzY⟩
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  omega

end Final

end CFSG.LocalAnalysis.RankThreeUC
