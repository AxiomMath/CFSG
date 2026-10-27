module

public import CFSG.LargeExtraspecial.S8Comm
public import CFSG.LargeExtraspecial.S8Std

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2

theorem false_of_coords (g11 g12 g22 c11 c12 c21 c22 : ZMod 2)
    (hG : ∀ a b : ZMod 2, (a, b) ≠ (0, 0) → a * g11 + b * g12 ≠ 0 ∨ a * g12 + b * g22 ≠ 0)
    (hC : ∀ a b : ZMod 2, (a, b) ≠ (0, 0) → a * c11 + b * c12 ≠ 0 ∨ a * c21 + b * c22 ≠ 0)
    (hCI : ∀ a b : ZMod 2, (a, b) ≠ (0, 0) →
      a + (a * c11 + b * c12) ≠ 0 ∨ b + (a * c21 + b * c22) ≠ 0)
    (h1 : c12 * g11 + c22 * g12 = c11 * g12 + c21 * g22)
    (h2 : c11 * g11 + c21 * g22 = c11 * g11 + c21 * g12)
    (h3 : c12 * g11 + c22 * g22 = c12 * g12 + c22 * g22) : False := by
  have h01 : ((0 : ZMod 2), (1 : ZMod 2)) ≠ (0, 0) := by decide
  have h10 : ((1 : ZMod 2), (0 : ZMod 2)) ≠ (0, 0) := by decide
  have h11 : ((1 : ZMod 2), (1 : ZMod 2)) ≠ (0, 0) := by decide
  have hG1 := hG 0 1 h01
  have hG2 := hG 1 0 h10
  have hG3 := hG 1 1 h11
  have hC1 := hC 0 1 h01
  have hC2 := hC 1 0 h10
  have hC3 := hC 1 1 h11
  have hCI1 := hCI 0 1 h01
  have hCI2 := hCI 1 0 h10
  have hCI3 := hCI 1 1 h11
  clear hG hC hCI h01 h10 h11
  rcases zmod2_eq_zero_or_eq_one g11 with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one g12 with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one g22 with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one c11 with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one c12 with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one c21 with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one c22 with rfl | rfl <;>
    revert hG1 hG2 hG3 hC1 hC2 hC3 hCI1 hCI2 hCI3 h1 h2 h3 <;> decide

section Abstract

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
  {qM : QuadraticForm (ZMod 2) M}

omit [FiniteDimensional (ZMod 2) M] in
theorem polar_map_of_forall_eq {X : M ≃ₗ[ZMod 2] M} (hX : ∀ v, qM (X v) = qM v) (u v : M) :
    polar qM (X u) (X v) = polar qM u v := by
  simp only [polar, ← map_add, hX]

omit [FiniteDimensional (ZMod 2) M] in
theorem polar_sub_comm {X : M ≃ₗ[ZMod 2] M} (hX : ∀ v, qM (X v) = qM v)
    {P : Submodule (ZMod 2) M} (hXc : commSpace X = P)
    (hiso : ∀ u ∈ P, ∀ u' ∈ P, polar qM u u' = 0) (w w' : M) :
    polar qM w (X w' - w') = polar qM w' (X w - w) := by
  have hw : X w - w ∈ P := hXc ▸ sub_mem_commSpace X w
  have hw' : X w' - w' ∈ P := hXc ▸ sub_mem_commSpace X w'
  have h := polar_map_of_forall_eq hX w w'
  have e1 : X w = w + (X w - w) := by abel
  have e2 : X w' = w' + (X w' - w') := by abel
  rw [e1, e2, polar_add_left, polar_add_right, polar_add_right, hiso _ hw _ hw', add_zero,
    add_assoc, add_eq_left] at h
  rw [polar_comm qM w' (X w - w)]
  have := congrArg (· + polar qM (X w - w) w') h
  simp only [zero_add] at this
  rw [← this, add_assoc, CharTwo.add_self_eq_zero, add_zero]

omit [FiniteDimensional (ZMod 2) M] in
theorem map_sub_eq_polar {X : M ≃ₗ[ZMod 2] M} (hX : ∀ v, qM (X v) = qM v) (w : M) :
    qM (X w - w) = polar qM w (X w - w) := by
  have h0 : qM (w + (X w - w)) = qM w := by rw [add_sub_cancel]; exact hX w
  rw [QuadraticMap.map_add qM w (X w - w), add_assoc] at h0
  have h1 : qM (X w - w) + polar qM w (X w - w) = 0 := by
    have := congrArg (fun z => z - qM w) h0
    simpa using this
  have h2 := eq_neg_of_add_eq_zero_left h1
  rw [h2, ZModModule.neg_eq_self]

theorem false_of_unipotent_triple (hqM : qM.polarBilin.Nondegenerate)
    (h4 : finrank (ZMod 2) M = 4) {X Y : M ≃ₗ[ZMod 2] M} (hX : ∀ v, qM (X v) = qM v)
    (hY : ∀ v, qM (Y v) = qM v) {P : Submodule (ZMod 2) M} (hXf : fixSpace X = P)
    (hXc : commSpace X = P) (hYf : fixSpace Y = P) (hYc : commSpace Y = P)
    (hXYf : fixSpace (X * Y) = P) : False := by
  have hP2 : finrank (ZMod 2) P = 2 := by
    have := finrank_commSpace_add_finrank_fixSpace X
    rw [hXc, hXf, h4] at this
    omega
  have hiso : ∀ u ∈ P, ∀ u' ∈ P, polar qM u u' = 0 := by
    intro u hu u' hu'
    rw [← hXc] at hu'
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hu'
    have hXu : X u = u := mem_fixSpace.mp (hXf ▸ hu)
    rw [polar_sub_right, ← polar_map_of_forall_eq hX u w, hXu, sub_self]
  obtain ⟨P', hPP'⟩ := Submodule.exists_isCompl P
  have hP'2 : finrank (ZMod 2) P' = 2 := by
    have := Submodule.finrank_add_eq_of_isCompl hPP'
    omega
  set b := Module.finBasisOfFinrankEq (ZMod 2) P' hP'2 with hb
  set e₁ : M := (b 0 : M) with he₁
  set e₂ : M := (b 1 : M) with he₂
  have hspan : ∀ w ∈ P', ∃ a c : ZMod 2, w = a • e₁ + c • e₂ := by
    intro w hw
    refine ⟨b.repr ⟨w, hw⟩ 0, b.repr ⟨w, hw⟩ 1, ?_⟩
    have := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)
    rw [Fin.sum_univ_two] at this
    simp only [Submodule.coe_add, Submodule.coe_smul] at this
    exact this.symm
  have hind : ∀ a c : ZMod 2, a • e₁ + c • e₂ = 0 → a = 0 ∧ c = 0 := by
    intro a c h
    have hli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have h' : ∑ i, (![a, c] i) • b i = 0 := by
      rw [Fin.sum_univ_two]
      apply Subtype.ext
      simpa using h
    exact ⟨by simpa using hli _ h' 0, by simpa using hli _ h' 1⟩
  have he₁P' : e₁ ∈ P' := (b 0).2
  have he₂P' : e₂ ∈ P' := (b 1).2
  have hcomb : ∀ a c : ZMod 2, a • e₁ + c • e₂ ∈ P' := fun a c =>
    P'.add_mem (P'.smul_mem a he₁P') (P'.smul_mem c he₂P')
  set φ : M → M := fun w => X w - w with hφ
  set ψ : M → M := fun w => Y w - w with hψ
  have hφP : ∀ w, φ w ∈ P := fun w => hXc ▸ sub_mem_commSpace X w
  have hψP : ∀ w, ψ w ∈ P := fun w => hYc ▸ sub_mem_commSpace Y w
  have hφadd : ∀ w w', φ (w + w') = φ w + φ w' := fun w w' => by
    simp only [hφ, map_add]; abel
  have hφsmul : ∀ (a : ZMod 2) w, φ (a • w) = a • φ w := fun a w => by
    simp only [hφ, map_smul, smul_sub]
  have hψadd : ∀ w w', ψ (w + w') = ψ w + ψ w' := fun w w' => by
    simp only [hψ, map_add]; abel
  have hψsmul : ∀ (a : ZMod 2) w, ψ (a • w) = a • ψ w := fun a w => by
    simp only [hψ, map_smul, smul_sub]
  have hinj : ∀ {Z : M ≃ₗ[ZMod 2] M}, fixSpace Z = P → ∀ w ∈ P', Z w - w = 0 → w = 0 := by
    intro Z hZ w hw h0
    have : w ∈ P ⊓ P' := ⟨hZ ▸ mem_fixSpace.mpr (sub_eq_zero.mp h0), hw⟩
    rw [hPP'.inf_eq_bot, Submodule.mem_bot] at this
    exact this
  have hXY : ∀ w, (X * Y) w - w = φ w + ψ w := by
    intro w
    have hXψ : X (ψ w) = ψ w := mem_fixSpace.mp (hXf ▸ hψP w)
    simp only [hφ, hψ] at hXψ ⊢
    rw [LinearEquiv.mul_apply, show Y w = w + (Y w - w) by abel, map_add, hXψ]
    abel
  have hpre : ∀ u ∈ P, ∃ w ∈ P', φ w = u := by
    intro u hu
    rw [← hXc] at hu
    obtain ⟨m, rfl⟩ := mem_commSpace.mp hu
    obtain ⟨p, hp, p', hp', rfl⟩ := Submodule.mem_sup.mp (hPP'.sup_eq_top ▸ Submodule.mem_top :
      m ∈ P ⊔ P')
    refine ⟨p', hp', ?_⟩
    have hXp : X p = p := mem_fixSpace.mp (hXf ▸ hp)
    simp only [hφ]
    rw [map_add, hXp]
    abel
  obtain ⟨w₁, hw₁, hφw₁⟩ := hpre _ (hψP e₁)
  obtain ⟨w₂, hw₂, hφw₂⟩ := hpre _ (hψP e₂)
  obtain ⟨c11, c21, hw₁c⟩ := hspan w₁ hw₁
  obtain ⟨c12, c22, hw₂c⟩ := hspan w₂ hw₂
  set g11 := polar qM e₁ (φ e₁) with hg11
  set g12 := polar qM e₁ (φ e₂) with hg12
  set g22 := polar qM e₂ (φ e₂) with hg22
  have hg21 : polar qM e₂ (φ e₁) = g12 := (polar_sub_comm hX hXc hiso e₁ e₂).symm
  have hφlin : ∀ a c : ZMod 2, φ (a • e₁ + c • e₂) = a • φ e₁ + c • φ e₂ := fun a c => by
    rw [hφadd, hφsmul, hφsmul]
  have hψlin : ∀ a c : ZMod 2, ψ (a • e₁ + c • e₂) = a • ψ e₁ + c • ψ e₂ := fun a c => by
    rw [hψadd, hψsmul, hψsmul]
  have hψe₁ : ψ e₁ = c11 • φ e₁ + c21 • φ e₂ := by rw [← hφw₁, hw₁c, hφlin]
  have hψe₂ : ψ e₂ = c12 • φ e₁ + c22 • φ e₂ := by rw [← hφw₂, hw₂c, hφlin]
  have hG : ∀ a c : ZMod 2, (a, c) ≠ (0, 0) → a * g11 + c * g12 ≠ 0 ∨ a * g12 + c * g22 ≠ 0 := by
    intro a c hac
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hw0 : φ (a • e₁ + c • e₂) ≠ 0 := fun h0 => by
      have := hinj hXf _ (hcomb a c) h0
      obtain ⟨ha, hc⟩ := hind a c this
      exact hac (by rw [ha, hc])
    apply hw0
    refine hqM.1 _ fun m => ?_
    obtain ⟨p, hp, p', hp', rfl⟩ := Submodule.mem_sup.mp (hPP'.sup_eq_top ▸ Submodule.mem_top :
      m ∈ P ⊔ P')
    obtain ⟨a', c', rfl⟩ := hspan p' hp'
    rw [polarBilin_apply_apply, polar_comm, polar_add_left, hiso p hp _ (hφP _), zero_add,
      polar_add_left, polar_smul_left, polar_smul_left, hφlin, polar_add_right, polar_smul_right,
      polar_smul_right, polar_add_right, polar_smul_right, polar_smul_right, hg21]
    simp only [smul_eq_mul]
    linear_combination a' * h1 + c' * h2
  have hqP : ∀ (a c : ZMod 2) (u v : M), u ∈ P → v ∈ P →
      qM (a • u + c • v) = a * qM u + c * qM v := by
    intro a c u v hu hv
    rw [QuadraticMap.map_add qM (a • u) (c • v), polar_smul_left, polar_smul_right,
      hiso u hu v hv, QuadraticMap.map_smul, QuadraticMap.map_smul]
    rcases zmod2_eq_zero_or_eq_one a with rfl | rfl <;>
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl <;> simp
  have hC : ∀ a c : ZMod 2, (a, c) ≠ (0, 0) → a * c11 + c * c12 ≠ 0 ∨ a * c21 + c * c22 ≠ 0 := by
    intro a c hac
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hψ0 : Y (a • e₁ + c • e₂) - (a • e₁ + c • e₂) = 0 := by
      change ψ (a • e₁ + c • e₂) = 0
      rw [hψlin, hψe₁, hψe₂]
      have e : a • (c11 • φ e₁ + c21 • φ e₂) + c • (c12 • φ e₁ + c22 • φ e₂) =
          (a * c11 + c * c12) • φ e₁ + (a * c21 + c * c22) • φ e₂ := by
        simp only [smul_add, smul_smul, add_smul]; abel
      rw [e, h1, h2, zero_smul, zero_smul, add_zero]
    obtain ⟨ha, hc⟩ := hind a c (hinj hYf _ (hcomb a c) hψ0)
    exact hac (by rw [ha, hc])
  have hCI : ∀ a c : ZMod 2, (a, c) ≠ (0, 0) →
      a + (a * c11 + c * c12) ≠ 0 ∨ c + (a * c21 + c * c22) ≠ 0 := by
    intro a c hac
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have h0 : (X * Y) (a • e₁ + c • e₂) - (a • e₁ + c • e₂) = 0 := by
      rw [hXY, hφlin, hψlin, hψe₁, hψe₂]
      have e : a • φ e₁ + c • φ e₂ +
          (a • (c11 • φ e₁ + c21 • φ e₂) + c • (c12 • φ e₁ + c22 • φ e₂)) =
          (a + (a * c11 + c * c12)) • φ e₁ + (c + (a * c21 + c * c22)) • φ e₂ := by
        simp only [smul_add, smul_smul, add_smul]; abel
      rw [e, h1, h2, zero_smul, zero_smul, add_zero]
    obtain ⟨ha, hc⟩ := hind a c (hinj hXYf _ (hcomb a c) h0)
    exact hac (by rw [ha, hc])
  have h1 : c12 * g11 + c22 * g12 = c11 * g12 + c21 * g22 := by
    have h := polar_sub_comm hY hYc hiso e₁ e₂
    change polar qM e₁ (ψ e₂) = polar qM e₂ (ψ e₁) at h
    rw [hψe₂, hψe₁, polar_add_right, polar_smul_right, polar_smul_right, polar_add_right,
      polar_smul_right, polar_smul_right, hg21] at h
    simp only [smul_eq_mul] at h
    linear_combination h
  have hqφ : ∀ w, qM (φ w) = polar qM w (φ w) := fun w => map_sub_eq_polar hX w
  have hqψ : ∀ w, qM (ψ w) = polar qM w (ψ w) := fun w => map_sub_eq_polar hY w
  have h2 : c11 * g11 + c21 * g22 = c11 * g11 + c21 * g12 := by
    have h := hqψ e₁
    rw [hψe₁, hqP _ _ _ _ (hφP _) (hφP _), hqφ, hqφ, polar_add_right, polar_smul_right,
      polar_smul_right] at h
    simp only [smul_eq_mul] at h
    linear_combination h
  have h3 : c12 * g11 + c22 * g22 = c12 * g12 + c22 * g22 := by
    have h := hqψ e₂
    rw [hψe₂, hqP _ _ _ _ (hφP _) (hφP _), hqφ, hqφ, polar_add_right, polar_smul_right,
      polar_smul_right, hg21] at h
    simp only [smul_eq_mul] at h
    linear_combination h
  exact false_of_coords g11 g12 g22 c11 c12 c21 c22 hG hC hCI h1 h2 h3

end Abstract


section Setting

open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_quadraticForm_WV (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1) :
    ∃ qM : QuadraticForm (ZMod 2) ↥((Wt S g t).map (Vt S g t).mkQ),
      qM.polarBilin.Nondegenerate ∧ ∀ w (hw : w ∈ Wt S g t), qM (secMk (Vt S g t) hw) = S.q w := by
  set W := Wt S g t with hW
  set V := Vt S g t with hV
  have hVW : V ≤ W := Vt_le_Wt H ht1
  have hqV : ∀ v ∈ V, S.q v = 0 := fun v hv => q_eq_zero_of_mem_Vt H ht1 hv
  have hpolVW : ∀ v ∈ V, ∀ w ∈ W, polar S.q v w = 0 := fun v hv w hw => (mem_Wt.mp hw) v hv
  obtain ⟨C₀, hC₀⟩ := Submodule.exists_isCompl (V.comap W.subtype)
  set C := C₀.map W.subtype with hC
  have hCW : C ≤ W := by rintro _ ⟨c, -, rfl⟩; exact c.2
  have hCV : C ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨c, hc, rfl⟩, hcV⟩
    have : c ∈ V.comap W.subtype ⊓ C₀ := ⟨hcV, hc⟩
    rw [hC₀.inf_eq_bot, Submodule.mem_bot] at this
    rw [this]
    rfl
  have hCVW : ∀ w ∈ W, ∃ c ∈ C, w - c ∈ V := by
    intro w hw
    obtain ⟨v, hv, c, hc, hcv⟩ := Submodule.mem_sup.mp (hC₀.sup_eq_top ▸ Submodule.mem_top :
      (⟨w, hw⟩ : W) ∈ V.comap W.subtype ⊔ C₀)
    refine ⟨c, ⟨c, hc, rfl⟩, ?_⟩
    have : (v : S.Qt) + c = w := congrArg Subtype.val hcv
    rw [← this, add_sub_cancel_right]
    exact hv
  set ι₀ : C →ₗ[ZMod 2] ↥(W.map V.mkQ) :=
    LinearMap.codRestrict (W.map V.mkQ) (V.mkQ ∘ₗ C.subtype)
      (fun c => Submodule.mem_map_of_mem (hCW c.2)) with hι₀
  have hι₀inj : Function.Injective ι₀ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    have h1 : (c : S.Qt) ∈ V := by
      have := congrArg Subtype.val hc
      simpa [hι₀] using this
    have : (c : S.Qt) ∈ C ⊓ V := ⟨c.2, h1⟩
    rw [hCV, Submodule.mem_bot] at this
    exact (Submodule.mem_bot _).mpr (Subtype.ext this)
  have hι₀surj : Function.Surjective ι₀ := by
    rintro ⟨u, hu⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨c, hc, hwc⟩ := hCVW w hw
    refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
    simp only [hι₀, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.mkQ_apply]
    exact (Submodule.Quotient.eq V).mpr (by rw [← neg_mem_iff, neg_sub]; exact hwc)
  set ι := LinearEquiv.ofBijective ι₀ ⟨hι₀inj, hι₀surj⟩ with hι
  set qM : QuadraticForm (ZMod 2) ↥(W.map V.mkQ) :=
    (S.q.comp C.subtype).comp ι.symm.toLinearMap with hqM
  have hqMsec : ∀ w (hw : w ∈ W), qM (secMk V hw) = S.q w := by
    intro w hw
    obtain ⟨c, hc, hwc⟩ := hCVW w hw
    have hιc : ι ⟨c, hc⟩ = secMk V hw := Subtype.ext (by
      change V.mkQ c = V.mkQ w
      exact (Submodule.Quotient.eq V).mpr (by rw [← neg_mem_iff, neg_sub]; exact hwc))
    have : ι.symm (secMk V hw) = ⟨c, hc⟩ := by rw [← hιc, LinearEquiv.symm_apply_apply]
    change S.q ((ι.symm (secMk V hw) : C) : S.Qt) = S.q w
    rw [this]
    change S.q c = S.q w
    have e : w = c + (w - c) := by abel
    rw [e, QuadraticMap.map_add S.q c (w - c), hqV _ hwc, add_zero, polar_comm,
      hpolVW _ hwc c (hCW hc), add_zero]
  have hpolqM : ∀ u v, polar qM u v =
      polar S.q ((ι.symm u : C) : S.Qt) ((ι.symm v : C) : S.Qt) := by
    intro u v
    simp only [hqM, polar, QuadraticMap.comp_apply, map_add, LinearEquiv.coe_coe,
      Submodule.subtype_apply]
  have hsep : ∀ u, (∀ v, polar qM u v = 0) → u = 0 := by
    intro u hu
    set c := ((ι.symm u : C) : S.Qt) with hcdef
    have hcC : c ∈ C := (ι.symm u).2
    have hcW : c ∈ W := hCW hcC
    have hcperp : ∀ w' ∈ W, polar S.q c w' = 0 := by
      intro w' hw'
      obtain ⟨c', hc', hwc'⟩ := hCVW w' hw'
      have h1 := hu (ι ⟨c', hc'⟩)
      rw [hpolqM, LinearEquiv.symm_apply_apply] at h1
      have e : w' = c' + (w' - c') := by abel
      rw [e, polar_add_right, h1, zero_add, polar_comm]
      exact hpolVW _ hwc' c hcW
    have hcV : c ∈ V := by
      have hperp : LinearMap.BilinForm.orthogonal S.q.polarBilin W = V :=
        LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate (isRefl_polarBilin S.q) V
      rw [← hperp, LinearMap.BilinForm.mem_orthogonal_iff]
      intro w' hw'
      change S.q.polarBilin w' c = 0
      rw [polarBilin_apply_apply, polar_comm]
      exact hcperp w' hw'
    have hc0 : c = 0 := by
      have : c ∈ C ⊓ V := ⟨hcC, hcV⟩
      rwa [hCV, Submodule.mem_bot] at this
    have : ι.symm u = 0 := Subtype.ext hc0
    rw [← ι.apply_symm_apply u, this, map_zero]
  refine ⟨qM, ⟨fun u hu => hsep u fun v => ?_, fun v hv => hsep v fun u => ?_⟩, hqMsec⟩
  · rw [← polarBilin_apply_apply]; exact hu v
  · rw [polar_comm, ← polarBilin_apply_apply]; exact hv u


theorem exists_nonsingular_pair {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥)
    (h : 4 ≤ finrank (ZMod 2) (perp q F) ∨
      (2 ≤ finrank (ZMod 2) (perp q F) ∧ ∀ v ∈ perp q F, q v = 0 → v = 0)) :
    ∃ u ∈ perp q F, ∃ u' ∈ perp q F, q u = 1 ∧ q u' = 1 ∧ polar q u u' = 1 := by
  have hne : perp q F ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at h
    omega
  obtain ⟨u, huF, hu⟩ := exists_mem_perp_map_eq_one hq hF hne
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [map_zero] at hu
    exact zero_ne_one hu
  obtain ⟨v, hvF, hvu⟩ := exists_mem_perp_polar_eq_one hq hF huF hu0
  have huv : polar q u v = 1 := by rw [polar_comm]; exact hvu
  rcases zmod2_eq_zero_or_eq_one (q v) with hv | hv
  · rcases h with h4 | ⟨-, ha⟩
    ·
      have hF₂ := sup_span_pair_inf_perp_eq_bot hF huF hvF huv
      have hdim₂ := finrank_perp_sup_span_pair hq hF huF hvF huv
      have hne₂ : perp q (F ⊔ Submodule.span (ZMod 2) {u, v}) ≠ ⊥ := by
        intro h0
        rw [h0, finrank_bot] at hdim₂
        omega
      obtain ⟨w, hwF, hw⟩ := exists_mem_perp_map_eq_one hq hF₂ hne₂
      obtain ⟨hwF', huw, hvw⟩ := mem_perp_sup_span_pair.mp hwF
      refine ⟨u, huF, v + w, (perp q F).add_mem hvF hwF', hu, ?_, ?_⟩
      · rw [QuadraticMap.map_add q v w, hv, hw, hvw]
        rfl
      · rw [polar_add_right, huv, huw, add_zero]
    · exfalso
      have hv0 : v ≠ 0 := by
        rintro rfl
        rw [polar_zero_right] at huv
        exact zero_ne_one huv
      exact hv0 (ha v hvF hv)
  · exact ⟨u, huF, v, hvF, hu, hv, huv⟩

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem fixSpace_eq_and_commSpace_eq {V M : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
    {hq : q.polarBilin.Nondegenerate} [AddCommGroup M] [Module (ZMod 2) M]
    [FiniteDimensional (ZMod 2) M] (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)) {m : ℕ}
    (hm : 2 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V} (hp : q p = 0)
    (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1) (hD : RadDecomp ρ ⊥ ⊤ p p₁)
    (x : omegaGroup q hq) (hx : (x : V ≃ₗ[ZMod 2] V) ∈ pointRadical q p)
    (hx1 : (x : V ≃ₗ[ZMod 2] V) ≠ 1) (hxa : ¬ IsTypeA q x 2) :
    fixSpace (ρ x) = fixOf ρ (radFix q ⊥ p : Set (V ≃ₗ[ZMod 2] V)) ∧
      commSpace (ρ x) = fixOf ρ (radFix q ⊥ p : Set (V ≃ₗ[ZMod 2] V)) := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hpp₁' : polar q p₁ p = 1 := by rw [polar_comm]; exact hpp₁
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ perp q ⊥ = ⊥ := bot_inf_eq _
  have hdimV : finrank (ZMod 2) (perp q (⊥ : Submodule (ZMod 2) V)) = 2 * m := by
    rw [perp_bot, finrank_top]; exact hdim
  have hmem : ∀ v : V, v ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun v => by
    rw [perp_bot]; exact Submodule.mem_top
  have hx' : (x : V ≃ₗ[ZMod 2] V) ∈ radFix q ⊥ p := by rw [radFix_bot]; exact hx
  obtain ⟨h1, h2⟩ := timmesfeld_2_1_b0 ρ hF hm hdimV (fun _ _ _ _ => Submodule.mem_top) (hmem _)
    (hmem _) hp₁0 hp₁ hp hpp₁' hD.symm x hx' hx1 hxa
  simp only [top_inf_eq] at h1 h2
  refine ⟨h1, ?_⟩
  rw [← h2, Submodule.map_top]

theorem false_of_finrank_WV_eq_four (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) = 4)
    {x y : omegaGroup D.Q D.hQ}
    (hx : (x : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ pointRadical D.Q (aV ht))
    (hx1 : (x : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ≠ 1) (hxa : ¬ IsTypeA D.Q x 2)
    (hy : (y : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ pointRadical D.Q (aV ht))
    (hy1 : (y : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ≠ 1) (hya : ¬ IsTypeA D.Q y 2)
    (hxy1 : ((x * y : omegaGroup D.Q D.hQ) : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ≠ 1)
    (hxya : ¬ IsTypeA D.Q (x * y : omegaGroup D.Q D.hQ) 2) : False := by
  obtain ⟨ρ, hρ, hD⟩ := timmesfeld_6_1_two hCE H hNo C ht ht1 hVQ hΩ D.hh D.hb D.hX D.hE
  obtain ⟨qM, hqM, hqMsec⟩ := exists_quadraticForm_WV H ht1 (g := g)
  have hinv : ∀ (e : omegaGroup D.Q D.hQ) u, qM (ρ e u) = qM u := by
    intro e u
    have heR : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ (resV H.conj_mem t).range := by
      rw [range_resV, D.hX]; exact e.2
    obtain ⟨r, hr⟩ := heR
    obtain ⟨w, hw, hwu⟩ := Submodule.mem_map.mp u.2
    have hu : u = secMk (Vt S g t) hw := Subtype.ext hwu.symm
    have hrw : ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wt S g t :=
      apply_mem_Wt_of_commute H C ht ht1 hVQ (commute_of_mem_Rbar H.conj_mem r.2) hw
    have hρu : ρ e u = secMk (Vt S g t) hrw := by
      rw [hu]
      exact Subtype.ext (hρ e r hr.symm w hw)
    rw [hρu, hqMsec, hu, hqMsec]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (r : S.O).2 w
  have hm := D.hm
  obtain ⟨hXf, hXc⟩ := fixSpace_eq_and_commSpace_eq ρ hm D.hdim D.hQa D.Q_bV D.polar_aV_bV hD
    x hx hx1 hxa
  obtain ⟨hYf, hYc⟩ := fixSpace_eq_and_commSpace_eq ρ hm D.hdim D.hQa D.Q_bV D.polar_aV_bV hD
    y hy hy1 hya
  have hxy : ((x * y : omegaGroup D.Q D.hQ) : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈
      pointRadical D.Q (aV ht) := mul_mem hx hy
  obtain ⟨hXYf, -⟩ := fixSpace_eq_and_commSpace_eq ρ hm D.hdim D.hQa D.Q_bV D.polar_aV_bV hD
    (x * y) hxy hxy1 hxya
  rw [map_mul] at hXYf
  exact false_of_unipotent_triple hqM h4 (hinv x) (hinv y) hXf hXc hYf hYc hXYf

theorem finrank_WV_ne_four (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hgen : 3 ≤ D.m ∨ D.IsMinus) :
    finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) ≠ 4 := by
  intro h4
  set p := aV ht with hp
  set p₁ := bV (mem_Lbar_of_pair H ht D.hh) with hp₁
  have hp0 : p ≠ 0 := aV_ne_zero H ht
  have hF : (⊥ : Submodule (ZMod 2) (Vt S g t)) ⊓ perp D.Q ⊥ = ⊥ := bot_inf_eq _
  have hmem : ∀ v : Vt S g t, v ∈ perp D.Q (⊥ : Submodule (ZMod 2) (Vt S g t)) := fun v => by
    rw [perp_bot]; exact Submodule.mem_top
  have hK := sup_span_pair_inf_perp_eq_bot hF (hmem p) (hmem p₁) D.polar_aV_bV
  have hKdim := finrank_perp_sup_span_pair D.hQ hF (hmem p) (hmem p₁) D.polar_aV_bV
  rw [perp_bot, finrank_top, D.hdim] at hKdim
  have hm := D.hm
  obtain ⟨u, huK, u', hu'K, hu, hu', huu'⟩ := exists_nonsingular_pair D.hQ hK (by
    rcases hgen with h3 | hmin
    · left; omega
    · rcases Nat.lt_or_ge D.m 3 with h2 | h3
      · right
        refine ⟨by omega, fun w hwK hw => ?_⟩
        by_contra hw0
        obtain ⟨-, hpw, -⟩ := mem_perp_sup_span_pair.mp hwK
        have hli : LinearIndependent (ZMod 2) ![p, w] := by
          refine (LinearIndependent.pair_iff' hp0).mpr fun a ha => ?_
          have h0 : polar D.Q p₁ (a • p) = 0 := by
            rw [ha]; exact (mem_perp_sup_span_pair.mp hwK).2.2
          rw [polar_smul_right, polar_comm, D.polar_aV_bV, smul_eq_mul, mul_one] at h0
          rw [h0, zero_smul] at ha
          exact hw0 ha.symm
        have hT : ∀ v ∈ Submodule.span (ZMod 2) {p, w}, D.Q v = 0 := by
          intro v hv
          obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
          rw [QuadraticMap.map_add D.Q (a • p) (b • w), QuadraticMap.map_smul,
            QuadraticMap.map_smul, D.hQa, hw, polar_smul_left, polar_smul_right, hpw]
          simp
        have h2' := hmin _ hT
        rw [finrank_span_pair hli] at h2'
        omega
      · left; omega)
  obtain ⟨-, hpu, -⟩ := mem_perp_sup_span_pair.mp huK
  obtain ⟨-, hpu', -⟩ := mem_perp_sup_span_pair.mp hu'K
  have hpuu' : polar D.Q p (u + u') = 0 := by rw [polar_add_right, hpu, hpu', add_zero]
  have hquu' : D.Q (u + u') = 1 := by
    rw [QuadraticMap.map_add D.Q u u', hu, hu', huu']
    rfl
  have hli : ∀ {w : Vt S g t}, D.Q w = 1 → LinearIndependent (ZMod 2) ![p, w] := by
    intro w hw
    refine (LinearIndependent.pair_iff' hp0).mpr fun a ha => ?_
    have h0 : D.Q (a • p) = 1 := by rw [ha, hw]
    rw [QuadraticMap.map_smul, D.hQa, smul_zero] at h0
    exact zero_ne_one h0
  have hrad : ∀ {w : Vt S g t}, polar D.Q p w = 0 →
      CFSG.ClassicalGroups.Orthogonal.eichler D.Q p w ∈ omegaGroup D.Q D.hQ := fun hw =>
    S2.pointRadical_le_omegaGroup D.hQ hp0 D.hQa (eichler_mem_pointRadical D.hQa hw)
  set x : omegaGroup D.Q D.hQ := ⟨_, hrad hpu⟩ with hx
  set y : omegaGroup D.Q D.hQ := ⟨_, hrad hpu'⟩ with hy
  have hxy : ((x * y : omegaGroup D.Q D.hQ) : Vt S g t ≃ₗ[ZMod 2] Vt S g t) =
      CFSG.ClassicalGroups.Orthogonal.eichler D.Q p (u + u') := by
    rw [Subgroup.coe_mul]
    exact CFSG.ClassicalGroups.Orthogonal.eichler_mul hpu hpu'
  refine false_of_finrank_WV_eq_four hCE hNo hΩ D h4 (x := x) (y := y)
    (eichler_mem_pointRadical D.hQa hpu) (eichler_ne_one D.hQ D.hQa hpu (hli hu))
    (not_isTypeA_eichler D.hQ hp0 D.hQa hpu hu)
    (eichler_mem_pointRadical D.hQa hpu') (eichler_ne_one D.hQ D.hQa hpu' (hli hu'))
    (not_isTypeA_eichler D.hQ hp0 D.hQa hpu' hu') ?_ ?_
  · rw [hxy]; exact eichler_ne_one D.hQ D.hQa hpuu' (hli hquu')
  · rw [hxy]; exact not_isTypeA_eichler D.hQ hp0 D.hQa hpuu' hquu'

end Setting

end CFSG.LargeExtraspecial.S8
