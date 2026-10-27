module

public import CFSG.LinearAlgebra.RootGroupSL.NoOuterGraphAux
import CFSG.LinearAlgebra.RootGroupSL.FpfArith

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open NoOuterGraph

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]
  [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]

theorem false_of_graph_form
    (hstar : 2 ≤ Module.finrank k E ∨
      (Module.finrank k E = 1 ∧ 4 ≤ Nat.card k ∧ 2 ≤ Module.finrank k X))
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (hR : (rootSL k E X).map α.toMonoidHom = rootSL k E X)
    (hC : ∀ h ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))),
      α h * h⁻¹ ∈ QK k E X ⊔ Subgroup.center (SpecialLinearGroup k (DSpace E X)))
    (σ : k ≃+* k) (T : Module.Dual k (DSpace E X) ≃+ DSpace E X)
    (hT : ∀ (c : k) (f : Module.Dual k (DSpace E X)), T (c • f) = σ c • T f)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace E X)) (f : Module.Dual k (DSpace E X)),
      α g (T f) = T (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap)) : False := by
  classical
  rcases hstar with hd | ⟨hd, hk, hX⟩
  · obtain ⟨s, hnorm, hadjoin⟩ :=
      exists_norm_eq_one_adjoin_eq_top (k := k) (E := E) hd
    have hs0 : s ≠ 0 := by
      intro hs
      have h : (0 : k) = 1 := by simpa [hs] using hnorm
      exact zero_ne_one h
    let a : E ≃ₗ[k] E := mulLeftEquiv k (Units.mk0 s hs0)
    have ha_apply : ∀ x : E, a x = s * x := by
      intro x
      rw [mulLeftEquiv_apply]
      rfl
    have hda : LinearEquiv.det a = 1 := by
      have he : (a : E →ₗ[k] E) = LinearMap.mulLeft k s := by
        ext x
        change a x = (LinearMap.mulLeft k s) x
        rw [ha_apply]
        rfl
      have hdet := det_mulLeft_eq_norm (k := k) (E := E) a s he
      rw [hnorm] at hdet
      exact Units.ext hdet
    have hdet : LinearEquiv.det a * LinearEquiv.det (1 : X ≃ₗ[k] X) *
        LinearEquiv.det (1 : E ≃ₗ[k] E) = 1 := by
      rw [hda]
      simp
    let h : SpecialLinearGroup k (DSpace E X) :=
      blockSL a (1 : X ≃ₗ[k] X) (1 : E ≃ₗ[k] E) hdet
    have hN : h ∈ RootN := by
      rw [blockSL_mem_normalizer_iff]
      intro t
      refine ⟨s * t, ?_⟩
      ext x
      change a (t * x) = (s * t) * x
      rw [ha_apply, mul_assoc]
    have htriv : ∀ v : DSpace E X,
        (SpecialLinearGroup.toLinearEquiv h) v - v ∈ flagK k E X := by
      intro v
      rw [mem_flagK_iff]
      simp [h, blockSL_apply]
    obtain ⟨c, hcW, _hcK⟩ := action_flagW_and_second α hC hN
    have hw0 : ((1 : E), (0 : X), (0 : E)) ∈ flagW k E X := by
      rw [mem_flagW_iff]
      simp
    have hw0h : h ((1 : E), (0 : X), (0 : E)) = (s, 0, 0) := by
      simp [h, blockSL_apply, ha_apply]
    have hfixw : α h ((1 : E), (0 : X), (0 : E)) =
        ((1 : E), (0 : X), (0 : E)) :=
      action_fixes_flagW_of_trivial_quotient α hR T hα htriv hw0
    have hfirst : (c : k) • s = 1 := by
      have hcw' : (c : k) • h ((1 : E), (0 : X), (0 : E)) =
          ((1 : E), (0 : X), (0 : E)) := by
        rw [← hcW _ hw0, hfixw]
      have hfst := congrArg Prod.fst hcw'
      rw [hw0h] at hfst
      simpa using hfst
    have hcsE : algebraMap k E (c : k) * s = 1 := by
      simpa [Algebra.smul_def] using hfirst
    have hs_inv : s = algebraMap k E ((c : k)⁻¹) := by
      rw [map_inv₀]
      exact eq_inv_of_mul_eq_one_right hcsE
    have hs_bot : s ∈ (⊥ : IntermediateField k E) := by
      rw [IntermediateField.mem_bot]
      exact ⟨(c : k)⁻¹, hs_inv.symm⟩
    have hadjoin_bot : IntermediateField.adjoin k ({s} : Set E) = ⊥ := by
      rw [IntermediateField.adjoin_eq_bot_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact hs_bot
    have hbot_top : (⊥ : IntermediateField k E) = ⊤ := by
      rw [← hadjoin_bot, hadjoin]
    have hfin : Module.finrank k E = 1 :=
      (IntermediateField.bot_eq_top_iff_finrank_eq_one).mp hbot_top
    omega
  · haveI : Fintype k := Fintype.ofFinite k
    have hcardk : 4 ≤ Fintype.card k := by
      simpa [Nat.card_eq_fintype_card] using hk
    have hcard_units : 3 ≤ Fintype.card kˣ := by
      rw [Fintype.card_units]
      omega
    have hlt : 1 < Fintype.card kˣ := by omega
    obtain ⟨s, hs1⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : kˣ)
    have hs2 : s ^ 2 ≠ 1 := by
      intro h2
      apply hs1
      apply Units.ext
      have h2k : (s : k) ^ 2 = 1 := by
        simpa using congrArg (fun u : kˣ => (u : k)) h2
      rcases (sq_eq_one_iff.mp h2k) with h | h
      · exact h
      · rw [CharTwo.neg_eq] at h
        exact h
    obtain ⟨g, hgdet, hgorder, hgev, hgfixvec, hgfixform⟩ :=
      exists_linearEquiv_det_pow_no_eigenvalue (k := k) (X := X) 1
        (by omega) s hs1 hs2
    have hdg : LinearEquiv.det g = s⁻¹ := by simpa using hgdet
    obtain ⟨f1, hf1ne, hf1fix⟩ := hgfixform (by omega)
    let sE : E := algebraMap k E (s : k)
    have hsE0 : sE ≠ 0 := by
      dsimp [sE]
      exact (map_ne_zero (algebraMap k E)).mpr (Units.ne_zero s)
    let a : E ≃ₗ[k] E := mulLeftEquiv k (Units.mk0 sE hsE0)
    have ha_apply : ∀ x : E, a x = sE * x := by
      intro x
      rw [mulLeftEquiv_apply]
      rfl
    have hda : LinearEquiv.det a = s := by
      have he : (a : E →ₗ[k] E) = LinearMap.mulLeft k sE := by
        ext x
        change a x = (LinearMap.mulLeft k sE) x
        rw [ha_apply]
        rfl
      have hdet := det_mulLeft_eq_norm (k := k) (E := E) a sE he
      have hnorm : Algebra.norm k sE = (s : k) := by
        dsimp [sE]
        rw [Algebra.norm_algebraMap, hd, pow_one]
      rw [hnorm] at hdet
      exact Units.ext hdet
    have hdet : LinearEquiv.det a * LinearEquiv.det g *
        LinearEquiv.det (1 : E ≃ₗ[k] E) = 1 := by
      rw [hda, hdg]
      simp
    let h : SpecialLinearGroup k (DSpace E X) :=
      blockSL a g (1 : E ≃ₗ[k] E) hdet
    have hN : h ∈ RootN := by
      rw [blockSL_mem_normalizer_iff]
      intro t
      refine ⟨sE * t, ?_⟩
      ext x
      change a (t * x) = (sE * t) * x
      rw [ha_apply, mul_assoc]
    have htriv : ∀ v : DSpace E X,
        (SpecialLinearGroup.toLinearEquiv h) v - v ∈ flagK k E X := by
      intro v
      rw [mem_flagK_iff]
      simp [h, blockSL_apply]
    obtain ⟨c, hcW, hcK⟩ := action_flagW_and_second α hC hN
    have hw0 : ((1 : E), (0 : X), (0 : E)) ∈ flagW k E X := by
      rw [mem_flagW_iff]
      simp
    have hw0h : h ((1 : E), (0 : X), (0 : E)) = (sE, 0, 0) := by
      simp [h, blockSL_apply, ha_apply]
    have hfixw : α h ((1 : E), (0 : X), (0 : E)) =
        ((1 : E), (0 : X), (0 : E)) :=
      action_fixes_flagW_of_trivial_quotient α hR T hα htriv hw0
    have hfirst : (c : k) • sE = 1 := by
      have hcw' : (c : k) • h ((1 : E), (0 : X), (0 : E)) =
          ((1 : E), (0 : X), (0 : E)) := by
        rw [← hcW _ hw0, hfixw]
      have hfst := congrArg Prod.fst hcw'
      rw [hw0h] at hfst
      simpa using hfst
    have hcs : (c : k) * (s : k) = 1 := by
      have hmap : algebraMap k E ((c : k) * (s : k)) = 1 := by
        rw [map_mul]
        simpa [sE, Algebra.smul_def] using hfirst
      exact (algebraMap k E).injective (by simpa using hmap)
    have hceq : (c : k) = (s : k)⁻¹ := eq_inv_of_mul_eq_one_left hcs
    have hcinv : (c : k)⁻¹ = (s : k) := by
      rw [hceq, inv_inv]
    let f : Module.Dual k (DSpace E X) :=
      f1.comp ((LinearMap.fst k X E).comp (LinearMap.snd k E (X × E)))
    have hfW : f ∈ AnnW k E X := by
      rw [Submodule.mem_dualAnnihilator]
      intro v hv
      simp [f, (mem_flagW_iff v).mp hv |>.1]
    have hfK : f ∉ AnnK k E X := by
      have hx_exists : ∃ x : X, f1 x ≠ 0 := by
        by_contra h
        push Not at h
        exact hf1ne (by ext y; exact h y)
      obtain ⟨x, hx⟩ := hx_exists
      intro hf
      have hzero := ((Submodule.mem_dualAnnihilator f).mp hf) ((0 : E), x, (0 : E))
        (by rw [mem_flagK_iff])
      exact hx (by simpa [f] using hzero)
    have hvK : T f ∈ flagK k E X :=
      T_mem_flagK_of_mem_dualAnnW α hR T hα hfW
    have hvW : T f ∉ flagW k E X := by
      intro hw
      exact hfK (mem_dualAnnK_of_T_mem_flagW α hR T hα hw)
    have hhinv : (SpecialLinearGroup.toLinearEquiv h⁻¹) =
        blockDiag a⁻¹ g.symm (1 : E ≃ₗ[k] E) := by
      rw [SpecialLinearGroup.toLinearEquiv_eq_coe, SpecialLinearGroup.coe_inv]
      change (blockDiag a g (1 : E ≃ₗ[k] E))⁻¹ =
        blockDiag a⁻¹ g.symm (1 : E ≃ₗ[k] E)
      rw [blockDiag_inv]
      rfl
    have hfixf : f ∘ₗ (SpecialLinearGroup.toLinearEquiv h⁻¹).toLinearMap = f := by
      apply LinearMap.ext
      intro v
      change f1 (((SpecialLinearGroup.toLinearEquiv h⁻¹) v).2.1) = f1 v.2.1
      rw [hhinv]
      simp only [blockDiag_apply]
      exact LinearMap.congr_fun hf1fix v.2.1
    have hfixv : α h (T f) = T f := by
      rw [hα h f, hfixf]
    have hvKb : (T f).2.2 = 0 := (mem_flagK_iff _).mp hvK
    have hv_apply : h (T f) = (a (T f).1, g (T f).2.1, (0 : E)) := by
      simp [h, blockSL_apply, hvKb]
    have hsec := hcK _ hvK
    rw [hfixv] at hsec
    have hx1eq : (T f).2.1 = (c : k) • g ((T f).2.1) := by
      simpa [hv_apply] using hsec
    have hgx : g ((T f).2.1) = (c : k)⁻¹ • (T f).2.1 := by
      have h := congrArg (fun y : X => (c : k)⁻¹ • y) hx1eq
      simpa [smul_smul] using h.symm
    have hgs : g ((T f).2.1) = (s : k) • (T f).2.1 := by
      rw [hgx, hcinv]
    have hxzero : (T f).2.1 = 0 := hgev _ hgs
    have hxne : (T f).2.1 ≠ 0 := by
      intro hx
      exact hvW ((mem_flagW_iff _).mpr ⟨hx, hvKb⟩)
    exact hxne hxzero


end CFSG.LinearAlgebra.RootGroupSL
