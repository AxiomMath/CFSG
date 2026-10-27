module

public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.Setup
public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.Eigen
public import CFSG.GF2Type.Smith1979.WidthFourKP.TriConf.Lines
public import CFSG.LargeExtraspecial.S14Early
public import CFSG.LargeExtraspecial.S12Seven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.TriPlus

open Subgroup Module CFSG.Open CFSG.GroupTheory CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S5 CFSG.LargeExtraspecial.S7
open CFSG.GroupTheory.DiagonalTwentySeven CFSG.GF2Type.Smith1979.TriConf

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev rhoO (S : Setting G) : Representation (ZMod 2) S.O S.Qt :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp S.O.subtype

@[simp] theorem rhoO_apply (S : Setting G) (x : S.O) :
    rhoO S x = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := rfl

private theorem negAt_single_self (i : Fin 3) :
    negAt i (Pi.single i 1) = -(Pi.single i 1 : Fin 3 → ZMod 3) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [negAt]
  · simp [negAt, h]

private theorem negAt_single_of_ne {i j : Fin 3} (h : j ≠ i) :
    negAt i (Pi.single j 1) = (Pi.single j 1 : Fin 3 → ZMod 3) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [negAt, Pi.single_eq_of_ne (Ne.symm h)]
  · simp [negAt, hk]

private theorem apply_eprod_of_fixes {S : Setting G}
    {σ : Multiplicative (Fin 3 → ZMod 3) →* S.O} (w : S.Qt)
    (hw : ∀ i, rhoO S (eb σ i) w = w) (c : Fin 3 → ZMod 3) :
    rhoO S (eprod (eb σ) c) w = w := by
  have hpow : ∀ (i : Fin 3) (n : ℕ),
      ((((eb σ i : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) ^ n) w = w := by
    intro i n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, LinearEquiv.mul_apply]
        rw [show ((eb σ i : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w from hw i, ih]
  rw [rhoO_apply, eprod]
  change ((((eb σ 0 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ (c 0).val *
    ((eb σ 1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ (c 1).val *
      ((eb σ 2 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ (c 2).val) w = w)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [hpow]

private theorem eq_cl_of_mem_span {S : Setting G} {g : G} {u : S.Qt} (hu : u ≠ 0)
    (hmem : u ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) :
    u = S.cl (g * S.z * g⁻¹) := by
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc1 : c = 1 := by
    have h : c = 0 ∨ c = 1 := by
      have h' : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide
      exact h' c
    rcases h with h0 | h1
    · rw [h0, zero_smul] at hc
      exact absurd hc.symm hu
    · exact h1
  rw [hc1, one_smul] at hc
  exact hc.symm

theorem planeHyp_of_eigenBasis {S : Setting G} (hirr : ¬ S.IsReducible) {g : G} (H : Hyp4 S g)
    {σ : Multiplicative (Fin 3 → ZMod 3) →* S.O} {l : Fin 3 → S.O}
    (E : EigenBasis (S7.Obar S) (S.Lbar g) σ l) :
    (∀ i, eb σ i ^ 3 = 1) ∧ (∀ i j, Commute (eb σ i) (eb σ j)) ∧
      (∀ i, l i * l i = 1) ∧ (∀ i j, Commute (l i) (l j)) ∧
      (∀ i, l i * eb σ i * (l i)⁻¹ = (eb σ i)⁻¹) ∧
      (∀ i j, i ≠ j → l i * eb σ j * (l i)⁻¹ = eb σ j) ∧
      (∀ c : Fin 3 → ZMod 3, rhoO S (eprod (eb σ) c) = 1 → c = 0) ∧
      (∀ w : S.Qt, (∀ i, rhoO S (eb σ i) w = w) → w = 0) ∧
      (∀ v w : S.Qt, v ≠ 0 → w ≠ 0 → (∀ i, rhoO S (l i) v = v) →
        (∀ i, rhoO S (l i) w = w) → v = w) := by
  have he3 : ∀ i, eb σ i ^ 3 = 1 := by
    intro i
    rw [← E.orderOf_eb i]
    exact pow_orderOf_eq_one _
  have hec : ∀ i j, Commute (eb σ i) (eb σ j) := fun i j =>
    (commute_iff_eq _ _).mpr (E.comm (E.eb_mem i) (E.eb_mem j))
  have hl2 : ∀ i, l i * l i = 1 := fun i =>
    S4.mul_self_of_mem_Lbar S H.conj_mem (E.l_mem i)
  have hlc : ∀ i j, Commute (l i) (l j) := fun i j =>
    (commute_iff_eq _ _).mpr (S4.Lbar_comm S H.conj_mem (E.l_mem i) (E.l_mem j))
  have hinv : ∀ i, l i * eb σ i * (l i)⁻¹ = (eb σ i)⁻¹ := by
    intro i
    have h := E.act i (Pi.single i 1)
    rw [negAt_single_self, ofAdd_neg, map_inv] at h
    simpa [eb] using h
  have hfix : ∀ i j, i ≠ j → l i * eb σ j * (l i)⁻¹ = eb σ j := by
    intro i j hij
    have h := E.act i (Pi.single j 1)
    rw [negAt_single_of_ne (Ne.symm hij)] at h
    simpa [eb] using h
  have hfaith : ∀ c : Fin 3 → ZMod 3, rhoO S (eprod (eb σ) c) = 1 → c = 0 := by
    intro c hc
    rw [← E.apply_eq_eprod c] at hc
    have h2 : σ (Multiplicative.ofAdd c) = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      simpa [rhoO_apply] using congrArg (fun f : S.Qt →ₗ[ZMod 2] S.Qt => f v) hc
    have h3 : Multiplicative.ofAdd c = 1 := E.inj (by simpa using h2)
    simpa using congrArg Multiplicative.toAdd h3
  have hCY : ∀ w : S.Qt, (∀ i, rhoO S (eb σ i) w = w) → w = 0 := by
    have hObar : S7.Obar S ≠ ⊥ := by
      intro hbot
      have hmem : eb σ 0 ∈ σ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
      rw [E.range_eq, hbot] at hmem
      have h2 : orderOf (eb σ 0) = 1 := by
        rw [Subgroup.mem_bot.mp hmem, orderOf_one]
      rw [E.orderOf_eb 0] at h2
      exact absurd h2 (by norm_num)
    have hbot : fixSub S (S7.Obar S) = ⊥ :=
      S5.fixSub_eq_bot (S14.irr_of_not_isReducible hirr) H hObar fun h =>
        (S.Lbar_le_Mbar ((h : G) * g)).trans (Mbar_le_normalizer_Obar S)
    intro w hw
    have hmem : w ∈ fixSub S (S7.Obar S) := by
      rw [mem_fixSub]
      intro x hx
      have hx' : x ∈ σ.range := by rwa [E.range_eq]
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx'
      rw [show a = Multiplicative.ofAdd a.toAdd from (ofAdd_toAdd a).symm,
        E.apply_eq_eprod a.toAdd]
      simpa [rhoO_apply] using apply_eprod_of_fixes w hw a.toAdd
    rwa [hbot, Submodule.mem_bot] at hmem
  have hCL : ∀ v w : S.Qt, v ≠ 0 → w ≠ 0 → (∀ i, rhoO S (l i) v = v) →
      (∀ i, rhoO S (l i) w = w) → v = w := by
    have hfix_of : ∀ {u : S.Qt}, (∀ i, rhoO S (l i) u = u) →
        u ∈ fixSub S (S.Lbar g) := by
      intro u hu
      rw [mem_fixSub]
      intro x hx
      have hgen : ∀ y ∈ Subgroup.closure (Set.range l),
          ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
        intro y hy
        exact Subgroup.closure_induction (p := fun y _ =>
          ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u)
          (by
            rintro y ⟨i, rfl⟩
            simpa [rhoO_apply] using hu i)
          (by simp)
          (by
            intro a b _ _ ha hb
            rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hb, ha])
          (by
            intro a _ ha
            have h := congrArg ((a⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ha
            simpa [← LinearEquiv.mul_apply, ← Subgroup.coe_mul] using h.symm) hy
      exact hgen x (E.gen hx)
    have hspan : ∀ {u : S.Qt}, (∀ i, rhoO S (l i) u = u) →
        u ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
      intro u hu
      rw [← H.fixSub_eq]
      exact hfix_of hu
    intro v w hv0 hw0 hvf hwf
    rw [eq_cl_of_mem_span hv0 (hspan hvf), eq_cl_of_mem_span hw0 (hspan hwf)]
  exact ⟨he3, hec, hl2, hlc, hinv, hfix, hfaith, hCY, hCL⟩

theorem fpf_iff_of_eigenBasis {S : Setting G} (hirr : ¬ S.IsReducible) {g : G} (H : Hyp4 S g)
    {σ : Multiplicative (Fin 3 → ZMod 3) →* S.O} {l : Fin 3 → S.O}
    (E : EigenBasis (S7.Obar S) (S.Lbar g) σ l) (c : Fin 3 → ZMod 3) :
    (∀ v : S.Qt, ((σ (Multiplicative.ofAdd c) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0) ↔
      ∃ i, c i ≠ 0 ∧ ∀ j, j ≠ i → c j = 0 := by
  obtain ⟨he3, hec, hl2, hlc, hinv, hfix, hfaith, hCY, hCL⟩ :=
    planeHyp_of_eigenBasis hirr H E
  constructor
  · intro hfpf
    have hc0 : c ≠ 0 := by
      intro hc
      have h1 : rhoO S (σ (Multiplicative.ofAdd c)) (S.cl (g * S.z * g⁻¹)) =
          S.cl (g * S.z * g⁻¹) := by
        rw [hc]
        simp
      have h2 : rhoO S (eprod (eb σ) c) (S.cl (g * S.z * g⁻¹)) =
          S.cl (g * S.z * g⁻¹) := by
        rw [← E.apply_eq_eprod c]
        exact h1
      exact S4.cl_conj_z_ne_zero S H.conj_mem H.conj_ne
        (hfpf _ (by simpa [rhoO_apply, ← E.apply_eq_eprod c] using h2))
    have hfpf' : ∀ w : S.Qt, rhoO S (eprod (eb σ) c) w = w → w = 0 := by
      intro w hw
      apply hfpf w
      rwa [← E.apply_eq_eprod c, rhoO_apply] at hw
    obtain ⟨i, hi⟩ := eq_single_of_fpf (rhoO S) (eb σ) l he3 hec hl2 hlc hinv hfix
      hfaith hCY hCL c hc0 hfpf'
    refine ⟨i, ?_, hi⟩
    intro hci
    exact hc0 (funext fun j => by
      by_cases hj : j = i
      · subst hj
        exact hci
      · exact hi j hj)
  · rintro ⟨i, hci, hsup⟩ v hv
    have hc_eq : c = (Pi.single i (c i) : Fin 3 → ZMod 3) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · rw [hsup j hj]
        simp [Pi.single_eq_of_ne hj]
    have hc_nsmul : c = (c i).val • (Pi.single i 1 : Fin 3 → ZMod 3) := by
      rw [hc_eq]
      simpa using single_eq_nsmul_single i (c i)
    have hF : ((σ (Multiplicative.ofAdd c) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        ((((eb σ i : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) ^ (c i).val) := by
      conv_lhs => rw [hc_nsmul]
      rw [ofAdd_nsmul, map_pow, Subgroup.coe_pow]
      rfl
    have hval : (c i).val = 1 ∨ (c i).val = 2 := by
      have hlt : (c i).val < 3 := ZMod.val_lt (c i)
      have hne : (c i).val ≠ 0 := fun h0 => hci ((ZMod.val_eq_zero (c i)).mp h0)
      omega
    rcases hval with h1 | h1
    · rw [hF, h1, pow_one] at hv
      exact fpf_e (rhoO S) (eb σ) l he3 hec hl2 hlc hinv hfix hfaith hCY hCL i v
        (by simpa [rhoO_apply] using hv)
    · rw [hF, h1] at hv
      let F : S.Qt ≃ₗ[ZMod 2] S.Qt := ((eb σ i : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      have h3 : F ^ 3 = 1 := by
        dsimp [F]
        rw [← Subgroup.coe_pow, he3 i]
        simp
      have hvv : (F ^ 2) v = v := by simpa [F] using hv
      have hGvv : F v = v := by
        calc F v = F ((F ^ 2) v) := by rw [hvv]
          _ = (F * F ^ 2) v := by rw [LinearEquiv.mul_apply]
          _ = (F ^ 3) v := by rw [show F ^ 3 = F * F ^ 2 from by rw [pow_succ']]
          _ = (1 : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by rw [h3]
          _ = v := rfl
      exact fpf_e (rhoO S) (eb σ) l he3 hec hl2 hlc hinv hfix hfaith hCY hCL i v
        (by simpa [F, rhoO_apply] using hGvv)

theorem fix_cl_of_eigenBasis {S : Setting G} (hirr : ¬ S.IsReducible) {g : G} (H : Hyp4 S g)
    {σ : Multiplicative (Fin 3 → ZMod 3) →* S.O} {l : Fin 3 → S.O}
    (E : EigenBasis (S7.Obar S) (S.Lbar g) σ l) (c : Fin 3 → ZMod 3)
    (hc : ((σ (Multiplicative.ofAdd c) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹)) : c = 0 := by
  obtain ⟨he3, hec, hl2, hlc, hinv, hfix, hfaith, hCY, hCL⟩ :=
    planeHyp_of_eigenBasis hirr H E
  have ha0 : S.cl (g * S.z * g⁻¹) ≠ 0 :=
    S4.cl_conj_z_ne_zero S H.conj_mem H.conj_ne
  have haL : ∀ i, rhoO S (l i) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
    intro i
    have hmem : S.cl (g * S.z * g⁻¹) ∈ fixSub S (S.Lbar g) := by
      rw [H.fixSub_eq]
      exact Submodule.subset_span (Set.mem_singleton _)
    exact hmem (l i) (E.l_mem i)
  have hc' : rhoO S (eprod (eb σ) c) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := by
    rw [← E.apply_eq_eprod c]
    simpa [rhoO_apply] using hc
  exact eq_zero_of_fix (rhoO S) (eb σ) l he3 hec hl2 hlc hinv hfix hfaith hCY hCL
    (S.cl (g * S.z * g⁻¹)) ha0 haL c hc'

end CFSG.GF2Type.Smith1979.TriPlus

end
