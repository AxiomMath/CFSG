module

public import Mathlib.LinearAlgebra.SpecialLinearGroup
import Mathlib.LinearAlgebra.Transvection.Basic

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] [Module.Finite E V]

private lemma det_prodCongr_aux {A B : Type} [AddCommGroup A] [Module E A] [Module.Finite E A]
    [AddCommGroup B] [Module E B] [Module.Finite E B]
    (e₁ : A ≃ₗ[E] A) (e₂ : B ≃ₗ[E] B) :
    LinearEquiv.det (e₁.prodCongr e₂) = LinearEquiv.det e₁ * LinearEquiv.det e₂ := by
  apply Units.ext
  simp only [LinearEquiv.coe_det, LinearEquiv.coe_prodCongr, Units.val_mul,
    LinearMap.det_prodMap]


private lemma linearIndependent_pair_of_forall_ne_smul {W : Type} [AddCommGroup W] [Module E W]
    {a b : W} (ha : a ≠ 0) (hb : ∀ c : E, b ≠ c • a) : LinearIndependent E ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right ha, rfl⟩
  · exfalso
    apply hb (-(t⁻¹ * s))
    have h : t • b = -(s • a) := eq_neg_of_add_eq_zero_right hst
    calc b = t⁻¹ • (t • b) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = -(t⁻¹ * s) • a := by rw [h, smul_neg, smul_smul, neg_smul]

private lemma exists_linearIndependent_pair {W : Type} [AddCommGroup W] [Module E W]
    [Module.Finite E W] (hW : 2 ≤ Module.finrank E W) {x : W} (hx : x ≠ 0) :
    ∃ y : W, LinearIndependent E ![x, y] := by
  have hne : Submodule.span E {x} ≠ ⊤ := by
    intro htop
    have h1 : Module.finrank E (Submodule.span E {x}) = 1 := finrank_span_singleton hx
    have h2 : Module.finrank E (⊤ : Submodule E W) = Module.finrank E W := finrank_top E W
    rw [htop, h2] at h1
    omega
  obtain ⟨y, hy⟩ := SetLike.exists_not_mem_of_ne_top (Submodule.span E {x}) hne
  refine ⟨y, linearIndependent_pair_of_forall_ne_smul hx ?_⟩
  intro c hc
  apply hy
  rw [hc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private theorem exists_specialLinear_apply_eq_of_independent {v w : V}
    (h : LinearIndependent E ![v, w]) :
    ∃ g : SpecialLinearGroup E V, g v = w := by
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one (K := E) (v := ![v, w])
    (s := Set.univ) h.linearIndepOn_univ
  have hfv : f v = 1 := hf 0 (Set.mem_univ _)
  have hfw : f w = 1 := hf 1 (Set.mem_univ _)
  have hzero : f (w - v) = 0 := by rw [map_sub, hfv, hfw, sub_self]
  refine ⟨⟨LinearEquiv.transvection hzero, LinearEquiv.transvection.det_eq_one hzero⟩, ?_⟩
  change (LinearEquiv.transvection hzero) v = w
  rw [LinearEquiv.transvection.apply hzero, hfv, one_smul]
  abel

theorem exists_specialLinear_apply_eq (hV : 2 ≤ Module.finrank E V) {v w : V} (hv : v ≠ 0)
    (hw : w ≠ 0) : ∃ g : SpecialLinearGroup E V, g v = w := by
  by_cases hind : LinearIndependent E ![v, w]
  · exact exists_specialLinear_apply_eq_of_independent hind
  ·
    have hex : ∃ c : E, c • v = w := by
      by_contra hcon
      apply hind
      rw [LinearIndependent.pair_iff' hv]
      intro a ha
      exact hcon ⟨a, ha⟩
    obtain ⟨c, hc⟩ := hex
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hc
      exact hw hc.symm
    obtain ⟨u, hvu⟩ := exists_linearIndependent_pair hV hv
    obtain ⟨g₁, hg₁⟩ := exists_specialLinear_apply_eq_of_independent hvu
    have hg₁' : (↑g₁ : V ≃ₗ[E] V) v = u := hg₁
    have huv : LinearIndependent E ![u, v] := LinearIndependent.pair_symm_iff.mp hvu
    have hucv : LinearIndependent E ![u, c • v] := by
      have h := (LinearIndependent.pair_smul_smul_iff (x := u) (y := v) (u := (1 : E))
        (v := c) isUnit_one (isUnit_iff_ne_zero.mpr hc0)).mpr huv
      simpa using h
    obtain ⟨g₂, hg₂⟩ := exists_specialLinear_apply_eq_of_independent hucv
    have hg₂' : (↑g₂ : V ≃ₗ[E] V) u = c • v := hg₂
    refine ⟨g₂ * g₁, ?_⟩
    change (↑g₂ : V ≃ₗ[E] V) ((↑g₁ : V ≃ₗ[E] V) v) = w
    rw [hg₁', hg₂', hc]

private theorem exists_specialLinear_comp_eq_of_independent {l l' : Module.Dual E V}
    (h : LinearIndependent E ![l, l']) :
    ∃ g : SpecialLinearGroup E V, ∀ v, l' (g v) = l v := by
  set d : Module.Dual E V := l - l' with hd
  have hl' : l' ≠ 0 := by
    intro h0
    have hz : (0 : E) • l + (1 : E) • l' = 0 := by
      rw [zero_smul, zero_add, one_smul, h0]
    exact one_ne_zero ((LinearIndependent.pair_iff.mp h) 0 1 hz).2
  have hll : l ≠ l' := by
    intro heq
    have hz : (1 : E) • l + (-1 : E) • l' = 0 := by
      have h1 : (-1 : E) • l' = -l' := neg_one_smul (R := E) l'
      rw [one_smul, h1, heq, add_neg_cancel]
    exact one_ne_zero ((LinearIndependent.pair_iff.mp h) 1 (-1) hz).1
  have hd0 : d ≠ 0 := by
    rw [hd]
    exact sub_ne_zero.mpr hll
  have hnotle : ¬ LinearMap.ker d ≤ LinearMap.ker l' := by
    intro hle
    have hmem : l' ∈ Submodule.span E (Set.range (fun _ : Unit => d)) :=
      mem_span_of_iInf_ker_le_ker (by simpa using hle)
    rw [Set.range_const, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hl' hc.symm
    have hrel : c • l = (1 + c) • l' := by
      have h1 : l' = c • l - c • l' := by
        calc l' = c • d := hc.symm
          _ = c • (l - l') := by rw [hd]
          _ = c • l - c • l' := smul_sub c l l'
      have h2 : c • l = l' + c • l' := (sub_eq_iff_eq_add).mp h1.symm
      rw [h2, add_smul, one_smul]
    have hzero : c • l + (-(1 + c)) • l' = 0 := by
      rw [hrel]
      have h1 : (-(1 + c) : E) • l' = -((1 + c) • l') := neg_smul (1 + c) l'
      rw [h1]
      exact add_neg_cancel _
    exact hc0 ((LinearIndependent.pair_iff.mp h) c (-(1 + c)) hzero).1
  obtain ⟨w, hwd, hwl⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hdw : d w = 0 := hwd
  have hlw : l' w ≠ 0 := hwl
  set F : Module.Dual E V := (l' w)⁻¹ • d with hF
  have hFw : F w = 0 := by
    rw [hF, LinearMap.smul_apply, hdw, smul_zero]
  refine ⟨⟨LinearEquiv.transvection hFw, LinearEquiv.transvection.det_eq_one hFw⟩, ?_⟩
  intro x
  change l' ((LinearEquiv.transvection hFw) x) = l x
  rw [LinearEquiv.transvection.apply hFw, map_add, map_smul, smul_eq_mul]
  have hFx : F x * l' w = d x := by
    rw [hF, LinearMap.smul_apply, smul_eq_mul]
    field_simp
  rw [hFx]
  simp only [hd, LinearMap.sub_apply]
  abel

theorem exists_specialLinear_comp_eq (hV : 2 ≤ Module.finrank E V) {l l' : Module.Dual E V}
    (hl : l ≠ 0) (hl' : l' ≠ 0) :
    ∃ g : SpecialLinearGroup E V, ∀ v, l' (g v) = l v := by
  by_cases hind : LinearIndependent E ![l, l']
  · exact exists_specialLinear_comp_eq_of_independent hind
  ·
    have hex : ∃ c : E, c • l = l' := by
      by_contra hcon
      apply hind
      rw [LinearIndependent.pair_iff' hl]
      intro a ha
      exact hcon ⟨a, ha⟩
    obtain ⟨c, hc⟩ := hex
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hc
      exact hl' hc.symm
    have hDual : 2 ≤ Module.finrank E (Module.Dual E V) := by
      rw [Subspace.dual_finrank_eq]
      exact hV
    obtain ⟨m, hlm⟩ := exists_linearIndependent_pair (W := Module.Dual E V) hDual hl
    have hlm' : LinearIndependent E ![l', m] := by
      have h := (LinearIndependent.pair_smul_smul_iff (x := l) (y := m) (u := c)
        (v := (1 : E)) (isUnit_iff_ne_zero.mpr hc0) isUnit_one).mpr hlm
      simpa [hc] using h
    obtain ⟨g₁, hg₁⟩ := exists_specialLinear_comp_eq_of_independent hlm'
    obtain ⟨g₂, hg₂⟩ := exists_specialLinear_comp_eq_of_independent hlm
    refine ⟨g₁⁻¹ * g₂, fun v => ?_⟩
    change l' ((↑(g₁⁻¹) : V ≃ₗ[E] V) ((↑g₂ : V ≃ₗ[E] V) v)) = l v
    have h1 : l' ((↑(g₁⁻¹) : V ≃ₗ[E] V) ((↑g₂ : V ≃ₗ[E] V) v)) =
        m ((↑g₂ : V ≃ₗ[E] V) v) := by
      have h := hg₁ ((↑(g₁⁻¹) : V ≃ₗ[E] V) ((↑g₂ : V ≃ₗ[E] V) v))
      simp only [] at h
      have happ : (↑g₁ : V ≃ₗ[E] V) ((↑(g₁⁻¹) : V ≃ₗ[E] V) ((↑g₂ : V ≃ₗ[E] V) v)) =
          (↑g₂ : V ≃ₗ[E] V) v := by
        rw [SpecialLinearGroup.coe_inv]
        exact LinearEquiv.apply_symm_apply _ _
      rw [happ] at h
      exact h.symm
    rw [h1, hg₂ v]

theorem exists_specialLinear_apply_eq_of_incident (hV : 3 ≤ Module.finrank E V) {w w' : V}
    {l l' : Module.Dual E V} (hw : w ≠ 0) (hw' : w' ≠ 0) (hl : l ≠ 0) (hl' : l' ≠ 0)
    (h : l w = 0) (h' : l' w' = 0) :
    ∃ g : SpecialLinearGroup E V, g w = w' ∧ ∀ v, l' (g v) = l v := by
  obtain ⟨h₀, hh₀⟩ := exists_specialLinear_comp_eq (by omega) hl hl'
  set w₀ : V := h₀ w with hw₀def
  have hw₀ : w₀ ≠ 0 := by
    intro hz
    apply hw
    have hw_eq : w = (↑(h₀⁻¹) : V ≃ₗ[E] V) w₀ := by
      rw [hw₀def]
      simp
    rw [hw_eq, hz]
    simp
  have hw₀ker : w₀ ∈ LinearMap.ker l' := by
    rw [LinearMap.mem_ker]
    exact (hh₀ w).trans h
  have hw'ker : w' ∈ LinearMap.ker l' := by
    rw [LinearMap.mem_ker]
    exact h'
  let K : Submodule E V := LinearMap.ker l'
  have hr : Module.finrank E (LinearMap.range l') = 1 := by
    rw [Module.Dual.range_eq_top_of_ne_zero hl', finrank_top E E,
      CommSemiring.finrank_self E]
  have hKfin : Module.finrank E (LinearMap.ker l') = Module.finrank E V - 1 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker l'
    omega
  have hK : 2 ≤ Module.finrank E K := by
    change 2 ≤ Module.finrank E (LinearMap.ker l')
    omega
  have hw₀K : (⟨w₀, hw₀ker⟩ : K) ≠ 0 := by simpa using hw₀
  have hw'K : (⟨w', hw'ker⟩ : K) ≠ 0 := by simpa using hw'
  obtain ⟨kK, hkK⟩ := exists_specialLinear_apply_eq (V := K) hK
    (v := ⟨w₀, hw₀ker⟩) (w := ⟨w', hw'ker⟩) hw₀K hw'K
  have hkK' : (↑kK : K ≃ₗ[E] K) ⟨w₀, hw₀ker⟩ = ⟨w', hw'ker⟩ := hkK
  obtain ⟨u', hu'⟩ := LinearMap.surjective hl' 1
  let L : Submodule E V := Submodule.span E {u'}
  have hLne : L ≠ ⊥ := by
    intro hbot
    have hu'bot : u' ∈ L := Submodule.subset_span (by simp)
    rw [hbot] at hu'bot
    rw [Submodule.mem_bot] at hu'bot
    rw [hu'bot] at hu'
    simp only [map_zero] at hu'
    exact one_ne_zero hu'.symm
  have hdisj : Disjoint K L := by
    rw [disjoint_iff_inf_le]
    intro x hx
    obtain ⟨hxK, hxL⟩ := hx
    change x ∈ LinearMap.ker l' at hxK
    rw [LinearMap.mem_ker] at hxK
    change x ∈ Submodule.span E {u'} at hxL
    rw [Submodule.mem_span_singleton] at hxL
    obtain ⟨c, rfl⟩ := hxL
    rw [map_smul, hu'] at hxK
    rw [smul_eq_zero] at hxK
    rcases hxK with hc | hc
    · rw [hc, zero_smul]
      simp
    · exact absurd hc one_ne_zero
  have hcompl : IsCompl K L := Module.Dual.isCompl_ker_of_disjoint_of_ne_bot hl' hdisj hLne
  let e : (K × L) ≃ₗ[E] V := Submodule.prodEquivOfIsCompl K L hcompl
  let block : (K × L) ≃ₗ[E] (K × L) :=
    (↑kK : K ≃ₗ[E] K).prodCongr (LinearEquiv.refl E L)
  let g₀ : V ≃ₗ[E] V := e.symm.trans (block.trans e)
  have hdetprod : LinearEquiv.det block = LinearEquiv.det (↑kK : K ≃ₗ[E] K) := by
    rw [show block = (↑kK : K ≃ₗ[E] K).prodCongr (LinearEquiv.refl E L) from rfl,
      det_prodCongr_aux, LinearEquiv.det_refl, mul_one]
  have hdet : LinearEquiv.det g₀ = 1 := by
    have hg₀ : g₀ = (e.symm.trans block).trans e := rfl
    rw [hg₀, LinearEquiv.det_conj, hdetprod, kK.prop]
  have hg₀w : g₀ w₀ = w' := by
    have hsymm : e.symm w₀ = (⟨w₀, hw₀ker⟩, 0) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left K L hcompl (⟨w₀, hw₀ker⟩ : K)
    calc g₀ w₀ = e (block (e.symm w₀)) := rfl
      _ = e (block (⟨w₀, hw₀ker⟩, 0)) := by rw [hsymm]
      _ = e ((↑kK : K ≃ₗ[E] K) ⟨w₀, hw₀ker⟩, (LinearEquiv.refl E L) 0) := by
            rw [LinearEquiv.prodCongr_apply]
      _ = e (⟨w', hw'ker⟩, 0) := by rw [hkK']; rfl
      _ = w' := by
            rw [Submodule.coe_prodEquivOfIsCompl']
            simp
  have hg₀form : ∀ x, l' (g₀ x) = l' x := by
    intro x
    let k : K := (e.symm x).1
    let y : L := (e.symm x).2
    have hxy : e.symm x = (k, y) := rfl
    have hx : x = ↑k + ↑y := by
      rw [← e.apply_symm_apply x, hxy, Submodule.coe_prodEquivOfIsCompl']
    have hgx : g₀ x = ↑((↑kK : K ≃ₗ[E] K) k) + ↑y := by
      calc g₀ x = e (block (e.symm x)) := rfl
        _ = e (block (k, y)) := by rw [hxy]
        _ = e ((↑kK : K ≃ₗ[E] K) k, (LinearEquiv.refl E L) y) := by
              rw [LinearEquiv.prodCongr_apply]
        _ = ↑((↑kK : K ≃ₗ[E] K) k) + ↑y := by
              rw [Submodule.coe_prodEquivOfIsCompl']; rfl
    have hk0 : l' (↑k) = 0 := k.2
    have hkK0 : l' (↑((↑kK : K ≃ₗ[E] K) k)) = 0 := ((↑kK : K ≃ₗ[E] K) k).2
    rw [hgx, hx, map_add, map_add, hk0, hkK0]
  let gS : SpecialLinearGroup E V := ⟨g₀, hdet⟩
  refine ⟨gS * h₀, ?_, ?_⟩
  · change (↑gS : V ≃ₗ[E] V) ((↑h₀ : V ≃ₗ[E] V) w) = w'
    rw [show (↑h₀ : V ≃ₗ[E] V) w = w₀ from hw₀def.symm, hg₀w]
  · intro v
    change l' ((↑gS : V ≃ₗ[E] V) ((↑h₀ : V ≃ₗ[E] V) v)) = l v
    rw [show (↑gS : V ≃ₗ[E] V) = g₀ from rfl, hg₀form, hh₀ v]

private theorem exists_ne_zero_apply_eq_zero_aux (hW : 2 ≤ Module.finrank E V)
    (l : Module.Dual E V) : ∃ w : V, w ≠ 0 ∧ l w = 0 := by
  have hlt : Module.finrank E E < Module.finrank E V := by
    rw [CommSemiring.finrank_self E]
    omega
  have hker : LinearMap.ker l ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt
  obtain ⟨w, hwmem, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨w, hw0, hwmem⟩

theorem exists_dual_ne_zero_apply_eq_zero (hV : 2 ≤ Module.finrank E V) (w : V) :
    ∃ l : Module.Dual E V, l ≠ 0 ∧ l w = 0 := by
  have hDual : 2 ≤ Module.finrank E (Module.Dual E V) := by
    rw [Subspace.dual_finrank_eq]
    exact hV
  obtain ⟨l, hl, hlw⟩ :=
    exists_ne_zero_apply_eq_zero_aux (V := Module.Dual E V) hDual (Module.Dual.eval E V w)
  exact ⟨l, hl, by simpa using hlw⟩

theorem exists_ne_zero_apply_eq_zero (hV : 2 ≤ Module.finrank E V) (l : Module.Dual E V) :
    ∃ w : V, w ≠ 0 ∧ l w = 0 :=
  exists_ne_zero_apply_eq_zero_aux hV l

end CFSG.LinearAlgebra.RootGroupSL
