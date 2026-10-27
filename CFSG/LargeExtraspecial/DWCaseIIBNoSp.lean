module

public import CFSG.LargeExtraspecial.DWCaseIIBConfig
public import CFSG.LargeExtraspecial.DWCaseIIBSL
public import CFSG.LargeExtraspecial.DWCaseIIG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.GroupTheory.GLnTwoSplitting
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}
  [IsElementaryAbelian 2 A]

theorem exists_dual_indep_of_ne_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {f : Module.Dual K V} (hf : f ≠ 0) {v : V} (hv : v ≠ 0)
    (h3 : 3 ≤ finrank K V) :
    ∃ g : Module.Dual K V, g v = 0 ∧
      ∀ r s : K, r • f + s • g = 0 → r = 0 ∧ s = 0 := by
  let U : Submodule K V := Submodule.span K {v}
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  have h2 : finrank K U = 1 := finrank_span_singleton hv
  have hA : 2 ≤ finrank K U.dualAnnihilator := by omega
  have hnot : ¬ U.dualAnnihilator ≤ Submodule.span K {f} := by
    intro hle
    have h4 := Submodule.finrank_mono hle
    have h5 : finrank K (Submodule.span K {f}) = 1 := finrank_span_singleton hf
    omega
  obtain ⟨g, hgA, hg⟩ := Set.not_subset.1 hnot
  have hgv : g v = 0 :=
    (Submodule.mem_dualAnnihilator _).1 hgA v (Submodule.mem_span_singleton_self v)
  refine ⟨g, hgv, fun r s hrs => ?_⟩
  by_cases hs : s = 0
  · subst hs
    rw [zero_smul, add_zero] at hrs
    exact ⟨(smul_eq_zero.1 hrs).resolve_right hf, rfl⟩
  · exfalso
    apply hg
    have hgs : g = (-(s⁻¹ * r)) • f := by
      have h6 : s • g = -(r • f) := eq_neg_of_add_eq_zero_right hrs
      calc g = s⁻¹ • (s • g) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
        _ = s⁻¹ • (-(r • f)) := by rw [h6]
        _ = (-(s⁻¹ * r)) • f := by rw [smul_neg, smul_smul]; exact (neg_smul _ _).symm
    rw [hgs]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self f)

theorem exists_linearEquiv_not_preserves_alt {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (h3 : 3 ≤ finrank K V) :
    ∃ f : V ≃ₗ[K] V, ∃ x y : V, B (f x) (f y) ≠ B x y := by
  classical
  have hpos : 0 < finrank K V := by omega
  obtain ⟨w, hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hθ : B w ≠ 0 := by
    intro h
    apply hw0
    apply hnd.1
    intro y
    have := congrArg (fun φ : Module.Dual K V => φ y) h
    simpa using this
  obtain ⟨g, hgw, hgind⟩ := exists_dual_indep_of_ne_zero (f := B w) hθ hw0 h3
  let f : V ≃ₗ[K] V := LinearEquiv.transvection hgw
  refine ⟨f, ?_⟩
  by_contra hcon
  push Not at hcon
  have hformula : ∀ x y : V, g x * B w y = g y * B w x := by
    intro x y
    have h := hcon x y
    change B (x + g x • w) (y + g y • w) = B x y at h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hB.self_eq_zero, mul_zero, add_zero, zero_add] at h
    rw [← hB.neg_eq w x] at h
    linear_combination h
  obtain ⟨y0, hy0⟩ : ∃ y0 : V, B w y0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hθ (LinearMap.ext h)
  let c : K := g y0 / B w y0
  have hg_eq : g = c • (B w) := by
    ext x
    change g x = (g y0 / B w y0) * (B w) x
    rw [div_mul_eq_mul_div, eq_div_iff hy0]
    exact hformula x y0
  have hzero : (-c) • (B w) + (1 : K) • g = 0 := by
    ext x
    have hx := congrArg (fun φ : Module.Dual K V => φ x) hg_eq
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply, one_smul,
      smul_eq_mul] at hx ⊢
    rw [hx]
    ring
  exact one_ne_zero (hgind (-c) 1 hzero).2

theorem IsHypFamily.eq_of_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {U : Submodule (ZMod 2) V} {H : V → Submodule (ZMod 2) V} (h : IsHypFamily U H)
    {c c' : V} (hc : c ∈ U) (hc' : c' ∈ U) (hc0 : c ≠ 0) (hc'0 : c' ≠ 0)
    (hH : H c = H c') : c = c' := by
  have key : (⟨c, hc⟩ : U) = ⟨c', hc'⟩ := by
    have hzero : (⟨c, hc⟩ : U) - ⟨c', hc'⟩ = 0 := by
      refine h.form_separating _ fun v => ?_
      have h1 : h.form (⟨c, hc⟩ : U) v = h.form (⟨c', hc'⟩ : U) v := by
        rw [h.form_apply, h.form_apply, h.hypFun_symm hc v.2, h.hypFun_symm hc' v.2]
        rcases zmod2_dichotomy (hypFun H (v : V) c) with e | e
        · have hvc : (v : V) ∈ H c := (hypFun_eq_zero_iff hc0).mp e
          rw [e, (hypFun_eq_zero_iff hc'0).mpr (hH ▸ hvc)]
        · have hvc : (v : V) ∉ H c := (hypFun_eq_one_iff.mp e).2
          rw [e, hypFun_eq_one_iff.mpr ⟨hc'0, fun h => hvc (by rwa [← hH] at h)⟩]
      rw [map_sub, LinearMap.sub_apply, h1, sub_self]
    exact sub_eq_zero.mp hzero
  exact congrArg Subtype.val key

theorem conjSub_inf_conjSub {G : Type*} [Group G] (A : Subgroup G) (g k : G) :
    conjSub A g ⊓ conjSub A k = conjSub (A ⊓ conjSub A (g⁻¹ * k)) g := by
  ext b
  simp only [Subgroup.mem_inf, mem_conjSub]
  have e : (g⁻¹ * k)⁻¹ * (g⁻¹ * b * g) * (g⁻¹ * k) = k⁻¹ * b * k := by group
  simp only [e]

theorem card_conjSub_inf_conjSub {G : Type*} [Group G] (A : Subgroup G) (g k : G) :
    Nat.card (conjSub A g ⊓ conjSub A k : Subgroup G) =
      Nat.card (A ⊓ conjSub A (g⁻¹ * k) : Subgroup G) := by
  rw [conjSub_inf_conjSub]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

namespace MaxEA

theorem card_inf_conjSub (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)
    (hD : spanD S = S.clSub A) {h : G} (hhA : h * S.z * h⁻¹ ∈ A)
    (hhz : h * S.z * h⁻¹ ≠ S.z) :
    Nat.card (A ⊓ conjSub A h : Subgroup G) = 2 * 2 ^ finrank (ZMod 2) (axisD S h) := by
  have hz : S.z ∈ A ⊓ conjSub A h := ⟨hA.z_mem, hA.z_mem_conjSub hM hhA hhz⟩
  have hXQ : A ⊓ conjSub A h ≤ S.QG := inf_le_left.trans hA.le_QG
  have h1 := S.card_clPre (S.clSub (A ⊓ conjSub A h))
  rw [S.clPre_clSub hXQ hz] at h1
  have h2 : S.clSub (A ⊓ conjSub A h) = axisD S h := by
    rw [hA.axisD_eq hII hhA hhz, hD]
    show S.clSub (A ⊓ conjSub A h) = S.clSub (A ⊓ conjSub A h) ⊓ S.clSub A
    exact (inf_eq_left.mpr (S.clSub_mono inf_le_left)).symm
  rw [h1, S.card_submodule, h2]

theorem false_of_hyp (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)
    (hbad : ∀ g : G, g * S.z * g⁻¹ ∈ A → g * S.z * g⁻¹ ≠ S.z → ¬ A ≤ S.Qa g)
    (h3 : 3 ≤ S.width) {g : G} (hxA : g * S.z * g⁻¹ ∈ A) (hxz : g * S.z * g⁻¹ ≠ S.z)
    (hsp : finrank (ZMod 2) (spanD S) ≤ finrank (ZMod 2) (axisD S g) + 1) : False := by
  haveI : FiniteDimensional (ZMod 2) S.Qt := finiteDimensional_Qt (S := S)
  have hWs : ∀ v ∈ spanD S, S.q v = 0 := q_spanD hII
  have hxQ : g * S.z * g⁻¹ ∈ S.QG := hA.le_QG hxA
  have hx0 : S.cl (g * S.z * g⁻¹) ≠ 0 := (cl_ne_zero_iff hxQ).mpr hxz
  have hD : spanD S = S.clSub A := hA.spanD_eq_clSub hM hII hxA hxz (by omega) hbad
  have hfam : IsHypFamily (spanD S) (axisV S) :=
    hA.isHypFamily_axisV hM hII hbad hxA hxz hsp
  have hne : axisD S g ≠ spanD S :=
    hA.axisD_ne_spanD hM hII hxA hxz (hbad g hxA hxz)
  have hlt : finrank (ZMod 2) (axisD S g) < finrank (ZMod 2) (spanD S) :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (axisD_le_spanD g) hne)
  have hdw : finrank (ZMod 2) (spanD S) = S.width := by rw [hD, hA.finrank_clSub]
  have hdim : finrank (ZMod 2) (axisD S g) = S.width - 1 := by omega
  have hlt1 : finrank (ZMod 2) (ZMod 2 ∙ S.cl (g * S.z * g⁻¹)) <
      finrank (ZMod 2) (axisD S g) := by
    rw [finrank_span_singleton hx0]
    omega
  obtain ⟨c, hcC, hcS⟩ := exists_mem_notMem_of_finrank_lt hlt1
  have hcD : c ∈ spanD S := axisD_le_spanD g hcC
  have hc0 : c ≠ 0 := fun h => hcS (by rw [h]; exact Submodule.zero_mem _)
  obtain ⟨hk1, hk2, hk3⟩ := repD_spec hWs hcD hc0
  have hkA : repD S c * S.z * (repD S c)⁻¹ ∈ A := hII _ hk1
  have hcQa : repD S c * S.z * (repD S c)⁻¹ ∈ S.Qa g := by
    refine (cl_mem_axisD_iff hxQ hxz hk1).mp ?_
    rw [hk3]
    exact hcC
  have hkx : repD S c * S.z * (repD S c)⁻¹ ∈ conjSub A g :=
    hA.mem_conjSub_of_mem_Qa' hM hII hcQa hkA
  have hx2ne : repD S c * S.z * (repD S c)⁻¹ ≠ g * S.z * g⁻¹ := by
    intro e
    apply hcS
    rw [← hk3, e]
    exact Submodule.mem_span_singleton_self _
  have hk'A : (g⁻¹ * repD S c) * S.z * (g⁻¹ * repD S c)⁻¹ ∈ A := by
    rw [show (g⁻¹ * repD S c) * S.z * (g⁻¹ * repD S c)⁻¹ =
      g⁻¹ * (repD S c * S.z * (repD S c)⁻¹) * g by group]
    exact mem_conjSub.mp hkx
  have hk'Q : (g⁻¹ * repD S c) * S.z * (g⁻¹ * repD S c)⁻¹ ∈ S.QG := hA.le_QG hk'A
  have hk'z : (g⁻¹ * repD S c) * S.z * (g⁻¹ * repD S c)⁻¹ ≠ S.z := by
    intro e
    apply hx2ne
    have := congrArg (fun t => g * t * g⁻¹) e
    simpa [mul_assoc] using this
  have hcg : Nat.card (A ⊓ conjSub A g : Subgroup G) =
      2 * 2 ^ finrank (ZMod 2) (axisD S g) :=
    hA.card_inf_conjSub hM hII hD hxA hxz
  have hck : Nat.card (A ⊓ conjSub A (repD S c) : Subgroup G) =
      2 * 2 ^ finrank (ZMod 2) (axisD S g) := by
    rw [hA.card_inf_conjSub hM hII hD hkA hk2,
      finrank_axisD_eq hWs hk1 hk2 hxQ hxz]
  have hck' : Nat.card (A ⊓ conjSub A (g⁻¹ * repD S c) : Subgroup G) =
      2 * 2 ^ finrank (ZMod 2) (axisD S g) := by
    rw [hA.card_inf_conjSub hM hII hD hk'A hk'z,
      finrank_axisD_eq hWs hk'Q hk'z hxQ hxz]
  have hcinf : Nat.card (conjSub A g ⊓ conjSub A (repD S c) : Subgroup G) =
      2 * 2 ^ finrank (ZMod 2) (axisD S g) := by
    rw [card_conjSub_inf_conjSub A g (repD S c)]
    exact hck'
  by_cases hleQ : conjSub A g ⊓ conjSub A (repD S c) ≤ S.QG
  ·
    have hleA : conjSub A g ⊓ conjSub A (repD S c) ≤ A := by
      intro y hy
      have hy2 : y ∈ conjSub (S.clPre (S.clSub A)) (repD S c) := by
        rw [hA.clPre_clSub]
        exact hy.2
      have h := mem_clPre_of_mem_conjSub (W := S.clSub A) (hW := isMbarInvariant_clSub hM)
        (hDQ := fun h hh => cl_conj_mem_clSub hII hh) (hleQ hy) hy2
      rwa [hA.clPre_clSub] at h
    have hle1 : conjSub A g ⊓ conjSub A (repD S c) ≤ A ⊓ conjSub A g :=
      le_inf hleA inf_le_left
    have hEq1 : conjSub A g ⊓ conjSub A (repD S c) = A ⊓ conjSub A g :=
      Subgroup.eq_of_le_of_card_ge hle1 (by rw [hcinf, hcg])
    have hle2 : conjSub A g ⊓ conjSub A (repD S c) ≤ A ⊓ conjSub A (repD S c) :=
      le_inf hleA inf_le_right
    have hEq2 : conjSub A g ⊓ conjSub A (repD S c) = A ⊓ conjSub A (repD S c) :=
      Subgroup.eq_of_le_of_card_ge hle2 (by rw [hcinf, hck])
    have hAg : axisD S g = S.clSub (A ⊓ conjSub A g) := by
      rw [hA.axisD_eq hII hxA hxz, hD]
      show S.clSub (A ⊓ conjSub A g) ⊓ S.clSub A = S.clSub (A ⊓ conjSub A g)
      exact inf_eq_left.mpr (S.clSub_mono inf_le_left)
    have hAk : axisD S (repD S c) = S.clSub (A ⊓ conjSub A (repD S c)) := by
      rw [hA.axisD_eq hII hkA hk2, hD]
      show S.clSub (A ⊓ conjSub A (repD S c)) ⊓ S.clSub A =
        S.clSub (A ⊓ conjSub A (repD S c))
      exact inf_eq_left.mpr (S.clSub_mono inf_le_left)
    have hclEq : S.clSub (A ⊓ conjSub A g) = S.clSub (A ⊓ conjSub A (repD S c)) := by
      rw [← hEq1, hEq2]
    have haxisEq : axisD S g = axisD S (repD S c) := by rw [hAg, hclEq, ← hAk]
    have hH : axisV S (S.cl (g * S.z * g⁻¹)) = axisV S c := by
      rw [axisV_cl hWs hxQ hxz, haxisEq]
      rfl
    have hceq : S.cl (g * S.z * g⁻¹) = c :=
      hfam.eq_of_eq (cl_conj_mem_spanD hxQ) hcD hx0 hc0 hH
    exact hcS (by rw [hceq]; exact Submodule.mem_span_singleton_self _)
  ·
    obtain ⟨y, hy, hyQ⟩ := SetLike.not_le_iff_exists.mp hleQ
    have hyG : y ∈ conjSub A g := hy.1
    have hyK : y ∈ conjSub A (repD S c) := hy.2
    have hyM : y ∈ S.M := hA.conjSub_le_M hM hxA hxz hyG
    have hdisj : ∀ u : S.Qt, u ∈ ZMod 2 ∙ S.cl (g * S.z * g⁻¹) →
        u ∈ ZMod 2 ∙ c → u = 0 := by
      intro u hu1 hu2
      rw [mem_span_singleton_iff_two] at hu1 hu2
      rcases hu1 with rfl | rfl
      · rfl
      · rcases hu2 with h | h
        · exact h
        · exfalso
          exact hcS (by rw [← h]; exact Submodule.mem_span_singleton_self _)
    have hfix : ∀ w ∈ S.clSub A,
        ((S.ρ ⟨y, hyM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
      intro w hw
      have h1 := hA.Abar_sub_mem_span hM hII hxA hxz
        (mem_Abar.mpr ⟨y, ⟨hyG, hyM⟩, rfl⟩) hw
      have h2 := hA.Abar_sub_mem_span hM hII hkA hk2
        (mem_Abar.mpr ⟨y, ⟨hyK, hyM⟩, rfl⟩) hw
      rw [hk3] at h2
      exact sub_eq_zero.mp (hdisj _ h1 h2)
    have hρ : S.ρ ⟨y, hyM⟩ = 1 :=
      hA.eq_one_of_forall_clSub hM ⟨⟨y, hyM⟩, rfl⟩ hfix
    exact hyQ (S.mem_QG_iff.mpr ⟨hyM, S.mem_Q_of_ρ_eq_one hρ⟩)

theorem false_of_bad (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)
    (hbad : ∀ g : G, g * S.z * g⁻¹ ∈ A → g * S.z * g⁻¹ ≠ S.z → ¬ A ≤ S.Qa g)
    (h4 : 4 ≤ S.width) {g₀ : G} (hg₀A : g₀ * S.z * g₀⁻¹ ∈ A)
    (hg₀z : g₀ * S.z * g₀⁻¹ ≠ S.z) : False := by
  have hWs := q_spanD hII
  have hD := hA.spanD_eq_clSub hM hII hg₀A hg₀z (by omega) hbad
  rcases hA.finrank_axisD_le_one_or hM hII hbad hg₀A hg₀z with hsl | hsp
  · exfalso
    have hslall : ∀ h : G, h * S.z * h⁻¹ ∈ A → h * S.z * h⁻¹ ≠ S.z →
        axisA S A h = ZMod 2 ∙ S.cl (h * S.z * h⁻¹) := by
      intro h hhA hhz
      have hhQ := hA.le_QG hhA
      have hdim := finrank_axisD_eq hWs hhQ hhz (hA.le_QG hg₀A) hg₀z
      have hax : axisD S h = axisA S A h := by
        rw [hA.axisD_eq hII hhA hhz, hD]
        exact inf_eq_left.mpr (S.clSub_mono inf_le_left)
      refine (Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr
        (hA.cl_mem_axisA hhA)) ?_).symm
      rw [finrank_span_singleton ((cl_ne_zero_iff hhQ).mpr hhz), ← hax, hdim]
      exact hsl
    exact hA.false_of_sl hM hII hbad hD (by omega) hslall hg₀A hg₀z
  · exact hA.false_of_hyp hM hII hbad (by omega) hg₀A hg₀z hsp

theorem resAt_surjective_of_good (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    {g₀ : G} (hgA : g₀ * S.z * g₀⁻¹ ∈ A) (hne : g₀ * S.z * g₀⁻¹ ≠ S.z)
    (hQa : A ≤ S.Qa g₀) : Function.Surjective (resAt S A hM) := by
  have : Finite (Additive (AN A)) := inferInstanceAs (Finite (AN A))
  have : FiniteDimensional (ZMod 2) (Additive (AN A)) := Module.Finite.of_finite
  have hsurj : Function.Surjective (conjLinear (AN A)) := by
    rw [← MonoidHom.range_eq_top]
    exact eq_top_of_transvections _ {x | ∃ g : G, g * S.z * g⁻¹ = elt x ∧ A ≤ S.Qa g}
      (hA.span_good_eq_top hM hgA hne hQa) fun x ⟨g, hg, hgQ⟩ f hf =>
        hA.exists_conjLinear_transvection_of_le_Qa hgQ hg.symm hf
  exact hA.resAt_surjective hM hsurj

theorem false_of_spConfig_of_surjective (hA : MaxEA S A)
    (hM : S.M ≤ normalizer (A : Set G)) (h3 : 3 ≤ S.width) (hS : SpConfig S A hM)
    (hsurj : Function.Surjective (resAt S A hM)) : False := by
  obtain ⟨ω, hnd, hωa, hrange⟩ := hS
  haveI : Finite (Additive S.Q) := inferInstanceAs (Finite S.Q)
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  haveI : FiniteDimensional (ZMod 2) (S.clSub A) := Module.Finite.of_finite
  have hdim : finrank (ZMod 2) (S.clSub A) = S.width := hA.finrank_clSub
  have h3' : 3 ≤ finrank (ZMod 2) (S.clSub A) := by rw [hdim]; exact h3
  obtain ⟨f, x, y, hxy⟩ := exists_linearEquiv_not_preserves_alt ω hωa hnd h3'
  obtain ⟨m, hm⟩ := hsurj f
  exact hxy ((hrange f).mp (MonoidHom.mem_range.mpr ⟨m, hm⟩) x y)

theorem false_of_spConfig (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A) (h4 : 4 ≤ S.width)
    {g₀ : G} (hg₀A : g₀ * S.z * g₀⁻¹ ∈ A) (hg₀z : g₀ * S.z * g₀⁻¹ ≠ S.z)
    (hS : SpConfig S A hM) : False := by
  by_cases hgood : ∃ g : G, g * S.z * g⁻¹ ∈ A ∧ g * S.z * g⁻¹ ≠ S.z ∧ A ≤ S.Qa g
  · obtain ⟨g, h1, h2, h3⟩ := hgood
    exact hA.false_of_spConfig_of_surjective hM (by omega) hS
      (hA.resAt_surjective_of_good hM h1 h2 h3)
  · push Not at hgood
    exact hA.false_of_bad hM hII (fun g h1 h2 => hgood g h1 h2) h4 hg₀A hg₀z

end MaxEA

end CFSG.LargeExtraspecial.DW
