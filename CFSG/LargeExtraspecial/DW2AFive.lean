module

public import CFSG.LargeExtraspecial.DW2AFiveMod
public import CFSG.LargeExtraspecial.DW2AFiveTv
public import CFSG.LargeExtraspecial.DW2ModSix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule
open CFSG.ComponentClassification.OutcomeLocal (IsF2Transvection tv tv_apply tv_ext
  isF2Transvection_iff exists_apply_eq_one commutatorSpace)

section Class

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Y : Subgroup (V ≃ₗ[ZMod 2] V)}
  {D : Set (V ≃ₗ[ZMod 2] V)}

theorem class_of_bijective {ρ : Y →* LinearMap.GeneralLinearGroup (ZMod 2) E}
    (hρ : Function.Bijective ρ) {d₀ : V ≃ₗ[ZMod 2] V} (hd₀ : d₀ ∈ Y)
    (hD : ∀ d, d ∈ D ↔ ∃ g ∈ Y, d = g * d₀ * g⁻¹) (hτ₀ : IsF2Transvection (ρ ⟨d₀, hd₀⟩)) :
    (∀ τ, IsF2Transvection τ → ∃ y : Y, (y : V ≃ₗ[ZMod 2] V) ∈ D ∧ ρ y = τ) ∧
      ∀ y : Y, IsF2Transvection (ρ y) → (y : V ≃ₗ[ZMod 2] V) ∈ D := by
  have key : ∀ τ, IsF2Transvection τ → ∃ g : Y, ρ (g * ⟨d₀, hd₀⟩ * g⁻¹) = τ := by
    intro τ hτ
    obtain ⟨h, hh⟩ := exists_conj_of_isF2Transvection hτ₀ hτ
    obtain ⟨g, rfl⟩ := hρ.2 h
    exact ⟨g, by rw [map_mul, map_mul, map_inv, hh]⟩
  have hmem : ∀ g : Y, ((g * ⟨d₀, hd₀⟩ * g⁻¹ : Y) : V ≃ₗ[ZMod 2] V) ∈ D :=
    fun g => (hD _).mpr ⟨g, g.2, rfl⟩
  refine ⟨fun τ hτ => ?_, fun y hy => ?_⟩
  · obtain ⟨g, hg⟩ := key τ hτ
    exact ⟨_, hmem g, hg⟩
  · obtain ⟨g, hg⟩ := key _ hy
    have := hmem g
    rwa [hρ.1 hg] at this

theorem three_le_finrank_of_four {τ₁ τ₂ : LinearMap.GeneralLinearGroup (ZMod 2) E}
    (h1 : IsF2Transvection τ₁) (h2 : IsF2Transvection τ₂) (hne : τ₁ ≠ τ₂)
    (h12 : IsF2Transvection (τ₁ * τ₂)) : 3 ≤ finrank (ZMod 2) E := by
  by_contra hlt
  push Not at hlt
  obtain ⟨φ, c, hφc, hφ, hc, rfl⟩ := (isF2Transvection_iff _).mp h1
  obtain ⟨φ', c', hφc', hφ', hc', rfl⟩ := (isF2Transvection_iff _).mp h2
  have hker : ∀ (ψ : Dual (ZMod 2) E) (a : E), ψ ≠ 0 → a ≠ 0 → ψ a = 0 →
      ∀ v, ψ v = 0 → v = 0 ∨ v = a := by
    intro ψ a hψ ha hψa v hv
    have h1' := finrank_ker_add_one hψ
    have hK : finrank (ZMod 2) (LinearMap.ker ψ) ≤ 1 := by omega
    by_cases hv0 : v = 0
    · exact Or.inl hv0
    · right
      have hsub : ∀ w ∈ LinearMap.ker ψ, w ≠ 0 → w = a := by
        intro w hw hw0
        have hspan : LinearMap.ker ψ = ZMod 2 ∙ a := by
          refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
          · rw [Submodule.span_le, Set.singleton_subset_iff]
            exact hψa
          · rw [finrank_span_singleton ha]
            exact hK
        rw [hspan] at hw
        obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rcases zmod2_cases μ with rfl | rfl
        · exact absurd (zero_smul _ a) hw0
        · exact one_smul _ a
      exact hsub v hv hv0
  have hcc : c ≠ c' := by
    intro hcc
    subst hcc
    apply hne
    have hφφ : φ = φ' := by
      by_contra hφφ
      obtain ⟨y, hy1, hy2⟩ := exists_apply_eq_one_apply_eq_zero hφ hφφ
      rcases hker φ' c hφ' hc hφc' y hy2 with rfl | rfl
      · rw [map_zero] at hy1
        exact zero_ne_one hy1
      · rw [hφc] at hy1
        exact zero_ne_one hy1
    subst hφφ
    rfl
  have hφc'1 : φ c' = 1 := by
    rcases zmod2_cases (φ c') with h0 | h0
    · rcases hker φ c hφ hc hφc c' h0 with h | h
      · exact absurd h hc'
      · exact absurd h.symm hcc
    · exact h0
  have hφφ : φ ≠ φ' := fun e => by rw [e, hφc'] at hφc'1; exact zero_ne_one hφc'1
  have happ : ∀ v, ((tv φ c hφc * tv φ' c' hφc' : LinearMap.GeneralLinearGroup (ZMod 2) E) :
      E →ₗ[ZMod 2] E) v = v + φ v • c + φ' v • (c' + c) := by
    intro v
    change ((tv φ c hφc : LinearMap.GeneralLinearGroup (ZMod 2) E) : E →ₗ[ZMod 2] E)
      (((tv φ' c' hφc' : LinearMap.GeneralLinearGroup (ZMod 2) E) : E →ₗ[ZMod 2] E) v) = _
    rw [tv_apply, tv_apply, map_add, map_smul, hφc'1, smul_eq_mul, mul_one, add_smul, smul_add]
    abel
  obtain ⟨φ'', a, hφ''a, -, ha0, he⟩ := (isF2Transvection_iff _).mp h12
  have hmem : ∀ v, φ v • c + φ' v • (c' + c) ∈ ZMod 2 ∙ a := by
    intro v
    have h1' : ((tv φ c hφc * tv φ' c' hφc' : LinearMap.GeneralLinearGroup (ZMod 2) E) :
        E →ₗ[ZMod 2] E) v = ((tv φ'' a hφ''a : LinearMap.GeneralLinearGroup (ZMod 2) E) :
        E →ₗ[ZMod 2] E) v := by rw [he]
    rw [happ, tv_apply] at h1'
    have : φ v • c + φ' v • (c' + c) = φ'' v • a := by
      have := congrArg (· - v) h1'
      simpa [add_assoc] using this
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  obtain ⟨y₁, hy₁, hy₁'⟩ := exists_apply_eq_one_apply_eq_zero hφ hφφ
  obtain ⟨y₂, hy₂, hy₂'⟩ := exists_apply_eq_one_apply_eq_zero hφ' (Ne.symm hφφ)
  have hm1 := hmem y₁
  have hm2 := hmem y₂
  rw [hy₁, hy₁', one_smul, zero_smul, add_zero] at hm1
  rw [hy₂, hy₂', one_smul, zero_smul, zero_add] at hm2
  have hc'0 : c' + c ≠ 0 := fun h => hcc (by
    have := congrArg (· + c) h
    simpa [add_assoc, add_self_zmod2] using this.symm)
  have hle : finrank (ZMod 2) (ZMod 2 ∙ a) ≤ 1 := (finrank_span_singleton ha0).le
  have e1 := eq_of_finrank_le_one' hle hm1 hm2 hc hc'0
  apply hc'
  have := congrArg (· + c) e1
  simpa [add_assoc, add_self_zmod2] using this.symm

end Class

section Main

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Y : Subgroup (V ≃ₗ[ZMod 2] V)} {f : LinearMap.BilinForm (ZMod 2) V}
  {D : Set (V ≃ₗ[ZMod 2] V)} (hf : f.Nondegenerate) (halt : f.IsAlt)
  (hY : Y ≤ TauCeti.BilinForm.isometryGroup f)

include hf halt in
theorem finrank_inf_orth_add (U F : Submodule (ZMod 2) V) :
    finrank (ZMod 2) (U ⊓ f.orthogonal F : Submodule (ZMod 2) V) + finrank (ZMod 2) F =
      finrank (ZMod 2) U + finrank (ZMod 2) (F ⊓ f.orthogonal U : Submodule (ZMod 2) V) := by
  have hr : f.IsRefl := halt.isRefl
  have h1 := orth_inf hf F (f.orthogonal U)
  rw [LinearMap.BilinForm.orthogonal_orthogonal hf hr U] at h1
  have h2 := LinearMap.BilinForm.finrank_orthogonal hf (F ⊓ f.orthogonal U)
  have h3 := LinearMap.BilinForm.finrank_orthogonal hf F
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq (f.orthogonal F) U
  rw [← h1, h2, h3, inf_comm (f.orthogonal F) U] at h4
  have h5 := Submodule.finrank_le (F ⊓ f.orthogonal U)
  have h6 := Submodule.finrank_le F
  omega

include hf halt hY in
theorem rad_stab_eq_bot (hD : IsA2Class f Y D) (hO2 : S12NoNormalTwo Y) (h4 : HasFourGroup D)
    (h2 : ¬ OneFactor Y) : rad f (stab Y ⊤) = ⊥ := by
  classical
  have hr : f.IsRefl := halt.isRefl
  obtain ⟨F, hR, hF, hFac, hFU, hiso, hfac2, htR, -, -, hbij⟩ :=
    exists_bijective_secHom hf halt hY hD hO2 h4 h2
  set U := stab Y ⊤ with hUdef
  set R := rad f U with hRdef
  have hU : IsInv Y U := isInv_stab isInv_top
  have hRF : R ≤ F := hFac.2.2.1
  have hF' : IsInv Y (U ⊓ f.orthogonal F) := hU.inf (isInv_orth hY hF)
  have hFF' : F ≤ U ⊓ f.orthogonal F := le_inf hFU.le hiso
  obtain ⟨d₀, hd₀, hDcl⟩ := hD.2.1
  have hDY : ∀ d ∈ D, d ∈ Y := fun d hd => hD.mem hd
  have hcl' : ∀ d ∈ D, ∀ d' ∈ D, ∃ g ∈ Y, d' = g * d * g⁻¹ := fun d hd d' hd' =>
    hD.exists_conj hd hd'
  set S₁ := commSub Y F with hS₁
  have hS₁F : S₁ ≤ F := commSub_le_of_isInv hF
  have hS₁R : S₁ ⊔ R = F := by
    rcases hFac.2.2.2.2 (S₁ ⊔ R) ((isInv_commSub hF).sup hR) le_sup_right (sup_le hS₁F hRF) with
      h | h
    · exact absurd (h ▸ le_sup_left) hFac.2.2.2.1
    · exact h
  have hrank : ∀ d ∈ D, secRank d ⊥ F ≤ 1 ∧ secRank d R F = 1 ∧
      secRank d (U ⊓ f.orthogonal F) U = 1 ∧ secRank d S₁ U ≤ 1 := by
    intro d hd
    have hdY := hDY d hd
    have r1 := one_le_secRank hD.1 hcl' hR hF hFac.not_isUnip hd
    have r2 := one_le_secRank hD.1 hcl' hF' hU hfac2.not_isUnip hd
    have s1 := secRank_add_le (g := d) (bot_le : ⊥ ≤ R) hRF (hR d hdY)
    have s2 := secRank_add_le (g := d) hFF' inf_le_left (hF' d hdY)
    have s3 := secRank_add_le (g := d) (hFF'.trans inf_le_left) (le_top : U ≤ ⊤) (hU d hdY)
    have s4 := secRank_add_le (g := d) (bot_le : ⊥ ≤ F) le_top (hF d hdY)
    have hrk := secRank_bot_top d
    rw [(hD.2.2 d hd).2.2.2.1] at hrk
    have hb : 1 ≤ secRank d ⊥ S₁ := by
      by_contra h0
      have h0' : secRank d ⊥ S₁ = 0 := by omega
      rw [secRank_eq_zero_iff] at h0'
      have hfix : ∀ w ∈ F, d w - w ∈ R := by
        intro w hw
        rw [← hS₁R] at hw
        obtain ⟨x, hx, r, hr', rfl⟩ := Submodule.mem_sup.mp hw
        have hx' := h0' x hx
        rw [Submodule.mem_bot] at hx'
        rw [map_add, show d x = x by rw [← sub_eq_zero]; exact hx', htR d hdY r hr']
        rw [sub_self]
        exact zero_mem _
      have := secRank_eq_zero_iff.mpr hfix
      omega
    have s5 := secRank_add_le (g := d) (bot_le : ⊥ ≤ S₁) (hS₁F.trans (hFF'.trans inf_le_left))
      ((isInv_commSub hF) d hdY)
    have s6 := secRank_add_le (g := d) (bot_le : ⊥ ≤ U) le_top (hU d hdY)
    omega
  have htvB : ∀ y : Y, (y : V ≃ₗ[ZMod 2] V) ∈ D → IsF2Transvection (secHom R F Y hR hF y) :=
    fun y hy => isF2Transvection_secHom hR hF hRF (hrank _ hy).2.1
  have hd₀Y := hDY d₀ hd₀
  obtain ⟨hsurjB, hclB⟩ := class_of_bijective hbij hd₀Y hDcl (htvB ⟨d₀, hd₀Y⟩ hd₀)
  have hdim : 3 ≤ finrank (ZMod 2) (Sec R F) := by
    obtain ⟨a, ha, b, hb, -, -, hab⟩ := h4
    obtain ⟨t1, t2, tne, t12⟩ := fourGroup_secHom hD hR hF hRF (fun d hd => (hrank d hd).2.1)
      ha hb hab
    exact three_le_finrank_of_four t1 t2 tne t12
  have hbot : finrank (ZMod 2) S₁ ≤ finrank (ZMod 2) (Sec R F) := by
    have := finrank_commSub_sup_le hR hF bot_le hRF hbij.1
      (fun y hy => (hrank _ hy).1) hclB hD.1 htvB hsurjB hdim
    rwa [sup_bot_eq, finrank_bot, zero_add] at this
  have hFR : F ⊓ f.orthogonal U ≤ R := fun x hx => ⟨hFU.le hx.1, hx.2⟩
  have hRFU : F ⊓ f.orthogonal U = R :=
    le_antisymm hFR (le_inf hRF inf_le_right)
  have hdimeq : finrank (ZMod 2) (Sec (U ⊓ f.orthogonal F) U) = finrank (ZMod 2) (Sec R F) := by
    rw [finrank_sec inf_le_left, finrank_sec hRF]
    have h1 := finrank_inf_orth_add hf halt U F
    rw [hRFU] at h1
    have h2 := Submodule.finrank_mono (inf_le_left : U ⊓ f.orthogonal F ≤ U)
    have h3 := Submodule.finrank_mono hRF
    omega
  have hinjT : Function.Injective (secHom (U ⊓ f.orthogonal F) U Y hF' hU) := by
    refine (injective_iff_map_eq_one _).mpr fun y hy => ?_
    have h1 := (secHom_eq_one_iff hF' hU).mp hy
    have h2 := inv_sub_mem_of_forall hr hY hF hFR y.2 fun u hu => (h1 u hu).2
    have h3 : secHom R F Y hR hF y⁻¹ = 1 := (secHom_eq_one_iff hR hF).mpr fun w hw => h2 w hw
    have h4 := hbij.1 (h3.trans (map_one _).symm)
    rw [inv_eq_one] at h4
    exact h4
  have hbijT : Function.Bijective (secHom (U ⊓ f.orthogonal F) U Y hF' hU) := by
    have : Finite V := Module.finite_of_finite (ZMod 2)
    have : Finite (V ≃ₗ[ZMod 2] V) :=
      Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V)) fun a b h =>
        LinearEquiv.ext (congrFun h)
    have : Finite (Sec R F) := Module.finite_of_finite (ZMod 2)
    have : Finite (Sec (U ⊓ f.orthogonal F) U) := Module.finite_of_finite (ZMod 2)
    have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) (Sec (U ⊓ f.orthogonal F) U)) :=
      Finite.of_injective (fun g => ⇑(g : Module.End (ZMod 2) (Sec (U ⊓ f.orthogonal F) U)))
        fun a b h => Units.ext (LinearMap.ext (congrFun h))
    have e₁ := Nat.card_congr (Equiv.ofBijective _ hbij)
    let e : Sec R F ≃ₗ[ZMod 2] Sec (U ⊓ f.orthogonal F) U :=
      LinearEquiv.ofFinrankEq _ _ hdimeq.symm
    have e₂ := Nat.card_congr (LinearMap.GeneralLinearGroup.congrLinearEquiv e).toEquiv
    refine ⟨hinjT, ?_⟩
    exact (Function.Injective.bijective_of_nat_card_le hinjT (by rw [e₁, e₂])).2
  have htvT : ∀ y : Y, (y : V ≃ₗ[ZMod 2] V) ∈ D →
      IsF2Transvection (secHom (U ⊓ f.orthogonal F) U Y hF' hU y) :=
    fun y hy => isF2Transvection_secHom hF' hU inf_le_left (hrank _ hy).2.2.1
  obtain ⟨hsurjT, hclT⟩ := class_of_bijective hbijT hd₀Y hDcl (htvT ⟨d₀, hd₀Y⟩ hd₀)
  have hS₁B : S₁ ≤ U ⊓ f.orthogonal F := hS₁F.trans hFF'
  have htop := finrank_commSub_sup_le hF' hU hS₁B inf_le_left hinjT
    (fun y hy => (hrank _ hy).2.2.2) hclT hD.1 htvT hsurjT (by rw [hdimeq]; exact hdim)
  rw [commSub_stab isInv_top, sup_eq_left.mpr (hS₁B.trans inf_le_left), hdimeq] at htop
  have hUF := finrank_sec (inf_le_left : U ⊓ f.orthogonal F ≤ U)
  have hRF' := finrank_sec hRF
  have hFF := Submodule.finrank_mono hFF'
  have hUU := Submodule.finrank_mono (inf_le_left : U ⊓ f.orthogonal F ≤ U)
  have hRR := Submodule.finrank_mono hRF
  rw [hdimeq] at hUF
  have h0 : finrank (ZMod 2) R = 0 := by omega
  exact Submodule.finrank_eq_zero.mp h0

end Main

end CFSG.LargeExtraspecial.DW
