module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4R2
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4D1Three

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

theorem commutator_sup_le_of {G : Type*} [Group G] {N A B : Subgroup G}
    (hA : A ≤ normalizer (N : Set G)) (hB : B ≤ normalizer (N : Set G))
    (hAA : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ N) (hBB : ∀ b ∈ B, ∀ b' ∈ B, ⁅b, b'⁆ ∈ N)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ N) : ⁅A ⊔ B, A ⊔ B⁆ ≤ N := by
  have hBA : ∀ b ∈ B, ∀ a ∈ A, ⁅b, a⁆ ∈ N := fun b hb a ha => by
    rw [← commutatorElement_inv]
    exact inv_mem (hAB a ha b hb)
  have step1 : ∀ g, (g ∈ A ∨ g ∈ B) → A ⊔ B ≤ centModSub N g := fun g hg => by
    refine sup_le (fun a ha => mem_centModSub.2 ⟨hA ha, ?_⟩)
      fun b hb => mem_centModSub.2 ⟨hB hb, ?_⟩
    · rw [← commutatorElement_def]
      rcases hg with hg | hg
      · exact hAA a ha g hg
      · exact hAB a ha g hg
    · rw [← commutatorElement_def]
      rcases hg with hg | hg
      · exact hBA b hb g hg
      · exact hBB b hb g hg
  have step2 : ∀ s ∈ A ⊔ B, A ⊔ B ≤ centModSub N s := fun s hs => by
    refine sup_le (fun a ha => mem_centModSub.2 ⟨hA ha, ?_⟩)
      fun b hb => mem_centModSub.2 ⟨hB hb, ?_⟩
    · rw [← commutatorElement_def, ← commutatorElement_inv]
      have := (mem_centModSub.1 (step1 a (Or.inl ha) hs)).2
      rw [← commutatorElement_def] at this
      exact inv_mem this
    · rw [← commutatorElement_def, ← commutatorElement_inv]
      have := (mem_centModSub.1 (step1 b (Or.inr hb) hs)).2
      rw [← commutatorElement_def] at this
      exact inv_mem this
  rw [commutator_le]
  intro x hx y hy
  have := (mem_centModSub.1 (step2 y hy hx)).2
  rwa [← commutatorElement_def] at this

theorem conj_mem_commutator_self_of_mem_normalizer {G : Type*} [Group G] {K : Subgroup G} {g : G}
    (hg : g ∈ normalizer (K : Set G)) {x : G} (hx : x ∈ ⁅K, K⁆) : g * x * g⁻¹ ∈ ⁅K, K⁆ := by
  have hle : ⁅K, K⁆ ≤ ⁅K, K⁆.comap (MulAut.conj g).toMonoidHom := by
    rw [commutator_le]
    intro a ha b hb
    change g * ⁅a, b⁆ * g⁻¹ ∈ ⁅K, K⁆
    rw [show g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ by
      simp only [commutatorElement_def]
      group]
    exact commutator_mem_commutator ((mem_normalizer_iff.1 hg a).1 ha)
      ((mem_normalizer_iff.1 hg b).1 hb)
  exact hle hx

theorem conj_mem_inf_centralizer {G : Type*} [Group G] {K M : Subgroup G} {g : G}
    (hK : g ∈ normalizer (K : Set G)) (hM : g ∈ normalizer (M : Set G)) {x : G}
    (hx : x ∈ K ⊓ centralizer (M : Set G)) : g * x * g⁻¹ ∈ K ⊓ centralizer (M : Set G) := by
  obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 hK x).1 hxK, mem_centralizer_iff.2
    fun m hm => ?_⟩
  have hm' : g⁻¹ * m * g ∈ M := by
    have := (mem_normalizer_iff.1 (inv_mem hM) m).1 hm
    rwa [inv_inv] at this
  have e := mem_centralizer_iff.1 hxC _ hm'
  calc m * (g * x * g⁻¹) = g * ((g⁻¹ * m * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * m * g)) * g⁻¹ := by rw [e]
    _ = g * x * g⁻¹ * m := by group

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem XF_le_A₂ : d.X₄ ⊔ d.F ≤ d.A₂ := sup_le (d.pull_mono X₄sub_le_A₂sub) d.F_le_A₂

omit [Finite G] in
theorem XF_le_S : d.X₄ ⊔ d.F ≤ d.S := XF_le_A₂.trans d.A₂_le_S

theorem XF_comm_Y
    (h : d.Hyp) {x y : G} (hx : x ∈ d.X₄ ⊔ d.F)
    (hy : y ∈ d.Y) : x * y = y * x :=
  h.Y_comm_A₂ hy (XF_le_A₂ hx)

omit [Finite G] in
theorem S_conj_mem_F {s f : G} (hs : s ∈ d.S) (hf : f ∈ d.F) : s * f * s⁻¹ ∈ d.F := by
  obtain ⟨σ, hσ, rfl⟩ := hs
  obtain ⟨φ, hφ, rfl⟩ := hf
  refine ⟨σ * φ * σ⁻¹, mem_Fsub_of_central (Ssub_conj_mem_A₂sub hσ (Fsub_le_A₂sub hφ))
    fun a ha => ?_, by simp only [map_mul, map_inv]⟩
  have e := Fsub_comm_A₂ (Ssub_conj_mem_A₂sub (inv_mem hσ) ha) hφ
  rw [inv_inv] at e
  calc a * (σ * φ * σ⁻¹) = σ * ((σ⁻¹ * a * σ) * φ) * σ⁻¹ := by group
    _ = σ * (φ * (σ⁻¹ * a * σ)) * σ⁻¹ := by rw [e]
    _ = σ * φ * σ⁻¹ * a := by group

theorem R_le_normalizer_F (h : d.Hyp) : d.R ≤ normalizer (d.F : Set G) := by
  refine sup_le (fun s hs => mem_normalizer_fintype fun f hf => S_conj_mem_F hs hf)
    (zpowers_le.2 (mem_normalizer_fintype fun f hf => ?_))
  rw [← h.t_comm_F hf, mul_inv_cancel_right]
  exact hf

theorem commutator_R_le (h : d.Hyp) :
    ⁅d.R, d.R⁆ ≤ d.X₄ ⊔ d.F := by
  rw [← commutator_S_eq]
  refine commutator_sup_le_of (fun s hs => mem_normalizer_fintype fun x hx =>
      conj_mem_commutator_S ((d.S).le_normalizer hs) hx)
    (zpowers_le.2 (mem_normalizer_fintype fun x hx => ?_))
    (fun a ha a' ha' => commutator_mem_commutator ha ha') (fun b hb b' hb' => ?_)
    fun a ha b hb => ?_
  · have hxS : x ∈ d.S := (commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) hx
    rw [← h.t_comm_of_mem_L (d.pull_le_L _ hxS), mul_inv_cancel_right]
    exact hx
  · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hb
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb'
    rw [commutatorElement_def, (Commute.zpow_zpow_self d.t m n).eq,
      show d.t ^ n * d.t ^ m * (d.t ^ m)⁻¹ * (d.t ^ n)⁻¹ = 1 by group]
    exact one_mem _
  · obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
    rw [commutatorElement_def, (Commute.zpow_right (h.t_comm_of_mem_L (d.pull_le_L _ ha)) n).eq,
      show d.t ^ n * a * a⁻¹ * (d.t ^ n)⁻¹ = 1 by group]
    exact one_mem _

theorem R_le_normalizer_XFW
    (h : d.Hyp) :
    d.R ≤ normalizer (((d.X₄ ⊔ d.F) ⊔ d.W : Subgroup G) : Set G) := fun r hr => by
  refine mem_normalizer_sup ?_ ?_
  · have hle : d.R ≤ normalizer ((d.X₄ ⊔ d.F : Subgroup G) : Set G) := by
      refine sup_le (fun s hs => mem_normalizer_fintype fun x hx => ?_)
        (zpowers_le.2 (mem_normalizer_fintype fun x hx => ?_))
      · rw [← commutator_S_eq] at hx ⊢
        exact conj_mem_commutator_S ((d.S).le_normalizer hs) hx
      · rw [← h.t_comm_of_mem_L (d.pull_le_L _ (XF_le_S hx)), mul_inv_cancel_right]
        exact hx
    exact hle hr
  · refine (sup_le (fun s hs => mem_normalizer_fintype fun w hw => ?_)
      (zpowers_le.2 (mem_normalizer_fintype fun w hw => ?_)) : d.R ≤ _) hr
    · rw [mem_centralizer_iff.1 (d.W_le_centralizer hw) s hs, mul_inv_cancel_right]
      exact hw
    · rw [h.t_inv]
      exact h.t_conj_mem_W hw

theorem V₂_comm_XFW
    (h : d.Hyp) {v x : G}
    (hv : v ∈ d.V₂) (hx : x ∈ (d.X₄ ⊔ d.F) ⊔ d.W) : v * x = x * v := by
  have hvY := h.V₂_le_Y hv
  have hle : (d.X₄ ⊔ d.F) ⊔ d.W ≤ centralizer ({v} : Set G) := sup_le
    (fun a ha => mem_centralizer_singleton_iff.2 (h.XF_comm_Y ha hvY))
    (fun w hw => mem_centralizer_singleton_iff.2 (h.Y_comm (d.W_le_Y hw) hvY))
  exact (mem_centralizer_singleton_iff.1 (hle hx)).symm

omit [Finite G] in
theorem XF_le_commutator_R₂ :
    d.X₄ ⊔ d.F ≤ ⁅d.R₂, d.R₂⁆ := by
  rw [← commutator_S_eq]
  exact commutator_mono (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_left)

theorem normalizer_R_le_normalizer_ZR
    (h : d.Hyp) :
    normalizer (d.R : Set G) ≤ normalizer (d.ZR : Set G) := fun g hg => by
  have hZR : d.ZR ≤ d.R := sup_le_sup_right
    (d.pull_mono (ZX₄sub_le_X₄sub.trans (le_sup_right : X₄sub ≤ Ssub))) _
  have hcen : ∀ z ∈ d.ZR, ∀ r ∈ d.R, z * r = r * z := fun z hz r hr => by
    have hle : d.R ≤ centralizer ({z} : Set G) := by
      refine sup_le (fun s hs => mem_centralizer_singleton_iff.2 ?_)
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 ?_))
      · have hle' : d.ZR ≤ centralizer ({s} : Set G) := sup_le
          (fun a ha => mem_centralizer_singleton_iff.2 (ZX₄_comm_S ha hs).symm)
          (zpowers_le.2 (mem_centralizer_singleton_iff.2
            (h.t_comm_of_mem_L (d.pull_le_L _ hs)).symm))
        exact (mem_centralizer_singleton_iff.1 (hle' hz)).symm
      · exact (mem_centralizer_singleton_iff.1 ((sup_le (fun a ha =>
          h.L_le_H (d.pull_le_L _ ha)) (zpowers_le.2 h.t_mem_H) : d.ZR ≤ d.H) hz)).symm
    exact (mem_centralizer_singleton_iff.1 (hle hr)).symm
  refine mem_normalizer_fintype fun z hz => ?_
  have hm : g * z * g⁻¹ ∈ d.R := (mem_normalizer_iff.1 hg z).1 (hZR hz)
  have hc := conj_central_of_mem_normalizer (inv_mem hg) fun r hr => hcen z hz r hr
  rw [inv_inv] at hc
  exact h.mem_ZR_of_comm_A₁ (mem_centralizer_singleton_iff.2
    (hc d.t (mem_sup_right (mem_zpowers _)))) fun a ha => hc a (mem_sup_left (d.A₁_le_S ha))

theorem inv_mul_mem_ZX₄_of_mem_W
    (h : d.Hyp) {w w' : G} (hw : w ∈ d.W) (hw' : w' ∈ d.W)
    (hwz : w ∉ d.ZX₄) (hw'z : w' ∉ d.ZX₄) : w⁻¹ * w' ∈ d.ZX₄ := by
  have hU : ∀ {x}, x ∈ d.W → x ∈ d.U := fun hx => h.E₂_le_U (h.Y_eq_E₂ ▸ d.W_le_Y hx)
  have hwi : w⁻¹ ∉ d.ZX₄ := fun hz => hwz (by simpa using inv_mem hz)
  have hc : (w⁻¹ * w')⁻¹ * d.t * (w⁻¹ * w') * d.t = 1 := by
    rw [crossed_mul h.t_mul_t (h.U_comm_F (hU hw') (h.U_crossed_mem_F (hU (inv_mem hw)))).symm,
      h.W_crossed_eq_z (inv_mem hw) hwi, h.W_crossed_eq_z hw' hw'z, z_mul_z]
  rw [← h.W_inf_H]
  exact Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hw) hw', mem_centralizer_singleton_iff.2
    ((crossed_eq_one_iff h.t_mul_t).1 hc)⟩

theorem R_le_normalizer_S (h : d.Hyp) : d.R ≤ normalizer (d.S : Set G) :=
  sup_le (d.S).le_normalizer (zpowers_le.2 (mem_normalizer_fintype fun s hs => by
    rw [← h.t_comm_of_mem_L (d.pull_le_L _ hs), mul_inv_cancel_right]
    exact hs))

theorem R_le_normalizer_W
    (h : d.Hyp) :
    d.R ≤ normalizer (d.W : Set G) :=
  sup_le (fun s hs => mem_normalizer_fintype fun w hw => by
      rw [mem_centralizer_iff.1 (d.W_le_centralizer hw) s hs, mul_inv_cancel_right]
      exact hw)
    (zpowers_le.2 (mem_normalizer_fintype fun w hw => by
      rw [h.t_inv]
      exact h.t_conj_mem_W hw))

theorem Y_comm_XFW
    (h : d.Hyp) {y x : G}
    (hy : y ∈ d.Y) (hx : x ∈ (d.X₄ ⊔ d.F) ⊔ d.W) : y * x = x * y := by
  have hle : (d.X₄ ⊔ d.F) ⊔ d.W ≤ centralizer ({y} : Set G) := sup_le
    (fun a ha => mem_centralizer_singleton_iff.2 (h.XF_comm_Y ha hy))
    (fun w hw => mem_centralizer_singleton_iff.2 (h.Y_comm (d.W_le_Y hw) hy))
  exact (mem_centralizer_singleton_iff.1 (hle hx)).symm

theorem mem_F_of_mem_S_of_mem_FV₂
    (h : d.Hyp) {x : G} (hxS : x ∈ d.S)
    (hx : x ∈ d.F ⊔ d.V₂) : x ∈ d.F := by
  obtain ⟨f, hf, v, hv, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun f hf v hv => h.Y_comm (h.F_le_Y hf) (h.V₂_le_Y hv)) hx
  have hvH : v ∈ d.H := by
    have := mul_mem (inv_mem (h.L_le_H (h.F_le_L hf))) (h.L_le_H (d.pull_le_L _ hxS))
    rwa [inv_mul_cancel_left] at this
  have hvZ : v ∈ d.Z₂ := by
    rw [← h.V₂_inf_H]
    exact Subgroup.mem_inf.2 ⟨hv, hvH⟩
  exact mul_mem hf (Z₂_le_F hvZ)

theorem exists_mul_of_mem_R₂_aux
    (h : d.Hyp)
    (hVN : d.V₂ ≤ normalizer ((d.R ⊔ d.W : Subgroup G) : Set G)) {x : G} (hx : x ∈ d.R₂) :
    ∃ r ∈ d.R, ∃ v ∈ d.V₂, x = r * v := by
  rw [h.R₂_eq_sup] at hx
  have hset := coe_mul_of_right_le_normalizer_left (d.R ⊔ d.W) d.V₂ hVN
  obtain ⟨k, hk, v, hv, rfl⟩ : x ∈ ((d.R ⊔ d.W : Subgroup G) : Set G) * (d.V₂ : Set G) := by
    rw [← hset]
    exact hx
  have hsetR := coe_mul_of_right_le_normalizer_left d.R d.W h.W_le_normalizer_R
  obtain ⟨r, hr, w, hw, rfl⟩ : k ∈ (d.R : Set G) * (d.W : Set G) := by
    rw [← hsetR]
    exact hk
  exact ⟨r, hr, w * v, mul_mem (h.W_le_V₂ hw) hv, by simp only [mul_assoc]⟩

end Data.Hyp

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem commutator_R₂_le
    (h : d.Hyp) :
    ⁅d.R₂, d.R₂⁆ ≤ (d.X₄ ⊔ d.F) ⊔ d.W := by
  have hVN : d.V₂ ≤ normalizer (((d.X₄ ⊔ d.F) ⊔ d.W : Subgroup G) : Set G) := fun v hv =>
    mem_normalizer_fintype fun x hx => by
      rw [h.V₂_comm_XFW hv hx, mul_inv_cancel_right]
      exact hx
  refine commutator_sup_le_of (h.R_le_normalizer_XFW) hVN
    (fun a ha a' ha' => mem_sup_left (commutator_R_le h (commutator_mem_commutator ha ha')))
    (fun b hb b' hb' => ?_) fun r hr v hv => ?_
  · rw [commutatorElement_def, h.Y_comm (h.V₂_le_Y hb) (h.V₂_le_Y hb'),
      show b' * b * b⁻¹ * b'⁻¹ = 1 by group]
    exact one_mem _
  · obtain ⟨hvY, hvW⟩ := (h.mem_V₂_iff).1 hv
    have hle : d.R ≤ centModSub ((d.X₄ ⊔ d.F) ⊔ d.W) v := by
      refine sup_le (fun s hs => mem_centModSub.2 ⟨h.R_le_normalizer_XFW (mem_sup_left hs),
        mem_sup_right (hvW s hs)⟩) (zpowers_le.2 (mem_centModSub.2
          ⟨h.R_le_normalizer_XFW (mem_sup_right (mem_zpowers _)), ?_⟩))
      have hz := Z₂_le_F (h.crossed_mem_Z₂_of_mem_V₂ hv)
      have e : d.t * v * d.t⁻¹ * v⁻¹ = v⁻¹ * d.t * v * d.t := by
        have hvφ : v * (v⁻¹ * d.t * v * d.t) = (v⁻¹ * d.t * v * d.t) * v :=
          h.Y_comm hvY (h.F_le_Y hz)
        rw [h.t_inv]
        calc d.t * v * d.t * v⁻¹ = v * (v⁻¹ * d.t * v * d.t) * v⁻¹ := by group
          _ = v⁻¹ * d.t * v * d.t := by rw [hvφ]; group
      rw [e]
      exact mem_sup_left (mem_sup_right hz)
    rw [commutatorElement_def]
    exact (mem_centModSub.1 (hle hr)).2

theorem W_le_commutator_R₂
    (h : d.Hyp) : d.W ≤ ⁅d.R₂, d.R₂⁆ := by
  by_contra hW
  have hle : ⁅d.R₂, d.R₂⁆ ≤ d.X₄ ⊔ d.F := fun x hx => by
    obtain ⟨a, ha, w, hw, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha w hw => (h.V₂_comm_XFW (h.W_le_V₂ hw) (mem_sup_left ha)).symm)
      (commutator_R₂_le h hx)
    have hwc : w ∈ ⁅d.R₂, d.R₂⁆ := by
      have := mul_mem (inv_mem (XF_le_commutator_R₂ ha)) hx
      rwa [inv_mul_cancel_left] at this
    by_cases hwz : w ∈ d.ZX₄
    · exact mul_mem ha (mem_sup_right (d.ZX₄_le_F hwz))
    · exfalso
      apply hW
      intro w' hw'
      by_cases hw'z : w' ∈ d.ZX₄
      · exact XF_le_commutator_R₂ (mem_sup_right (d.ZX₄_le_F hw'z))
      · have hk := h.inv_mul_mem_ZX₄_of_mem_W hw hw' hwz hw'z
        rw [show w' = w * (w⁻¹ * w') by group]
        exact mul_mem hwc (XF_le_commutator_R₂ (mem_sup_right (d.ZX₄_le_F hk)))
  have hRn : d.V₂ ≤ normalizer (d.R : Set G) := fun v hv => mem_normalizer_fintype fun r hr => by
    have hc : ⁅v, r⁆ ∈ ⁅d.R₂, d.R₂⁆ := commutator_mem_commutator (mem_sup_right hv)
      (mem_sup_left hr)
    rw [commutatorElement_def] at hc
    rw [show v * r * v⁻¹ = (v * r * v⁻¹ * r⁻¹) * r by group]
    exact mul_mem (mem_sup_left (XF_le_S (hle hc))) hr
  have hV : d.V₂ ≤ d.Z₂ ⊔ d.W := fun v hv =>
    (h.crossed_mem_ZX₄_iff hv).1 (h.conj_of_mem_normalizer_ZR
      (h.normalizer_R_le_normalizer_ZR (hRn hv))).1
  have := Subgroup.card_le_of_le hV
  rw [h.card_V₂, h.card_Z₂_sup_W] at this
  norm_num at this

theorem commutator_R₂_eq
    (h : d.Hyp) :
    ⁅d.R₂, d.R₂⁆ = (d.X₄ ⊔ d.F) ⊔ d.W :=
  le_antisymm (commutator_R₂_le h) (sup_le (XF_le_commutator_R₂)
    (W_le_commutator_R₂ h))

theorem exists_mul_of_mem_R₂
    (h : d.Hyp) {x : G}
    (hx : x ∈ d.R₂) : ∃ r ∈ d.R, ∃ v ∈ d.V₂, x = r * v :=
  h.exists_mul_of_mem_R₂_aux h.V₂_le_normalizer_RW hx

theorem commutator_t_mem_Z₂
    (h : d.Hyp) {v : G}
    (hv : v ∈ d.V₂) : ⁅d.t, v⁆ ∈ d.Z₂ := by
  have hvY := h.V₂_le_Y hv
  have hz := h.crossed_mem_Z₂_of_mem_V₂ hv
  have hvφ : v * (v⁻¹ * d.t * v * d.t) = (v⁻¹ * d.t * v * d.t) * v :=
    h.Y_comm hvY (h.F_le_Y (Z₂_le_F hz))
  rw [commutatorElement_def, h.t_inv, show d.t * v * d.t * v⁻¹ =
    v * (v⁻¹ * d.t * v * d.t) * v⁻¹ by group, hvφ, mul_inv_cancel_right]
  exact hz

theorem R₂_inf_centralizer_eq
    (h : d.Hyp) :
    d.R₂ ⊓ centralizer ((⁅d.R₂, d.R₂⁆ : Subgroup G) : Set G) = d.F ⊔ d.V₂ := by
  rw [commutator_R₂_eq h]
  have hY : d.Y ≤ centralizer (((d.X₄ ⊔ d.F) ⊔ d.W : Subgroup G) : Set G) := fun y hy =>
    mem_centralizer_iff.2 fun x hx => (h.Y_comm_XFW hy hx).symm
  refine le_antisymm (fun x hx => ?_) (le_inf (sup_le (fun f hf => mem_sup_left
    (mem_sup_left (d.A₂_le_S (d.F_le_A₂ hf)))) le_sup_right)
    (sup_le (h.F_le_Y.trans hY) (h.V₂_le_Y.trans hY)))
  obtain ⟨hxR, hxC⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨r, hr, v, hv, rfl⟩ := h.exists_mul_of_mem_R₂ hxR
  have hvC := hY (h.V₂_le_Y hv)
  have hrC : ∀ y ∈ (d.X₄ ⊔ d.F) ⊔ d.W, y * r = r * y := fun y hy => by
    have e1 := mem_centralizer_iff.1 hxC y hy
    have e2 := mem_centralizer_iff.1 hvC y hy
    calc y * r = y * (r * v) * v⁻¹ := by group
      _ = r * v * y * v⁻¹ := by rw [e1]
      _ = r * (v * y) * v⁻¹ := by group
      _ = r * (y * v) * v⁻¹ := by rw [e2]
      _ = r * y := by group
  have htS : ∀ k ∈ d.S, d.t * k * d.t ∈ d.S := fun k hk => by
    rw [← h.t_comm_of_mem_L (d.pull_le_L _ hk), mul_assoc, h.t_mul_t, mul_one]
    exact hk
  rcases (mem_sup_zpowers_iff h.t_mul_t htS).1 hr with hrS | hrS
  · obtain ⟨σ, hσ, rfl⟩ := hrS
    refine mul_mem (mem_sup_left ⟨σ, mem_Fsub_of_comm_commutator_Ssub hσ fun y hy =>
      d.ι_injective ?_, rfl⟩) (mem_sup_right hv)
    rw [map_mul, map_mul]
    have hyX : d.ι y ∈ (d.X₄ ⊔ d.F) ⊔ d.W := by
      have : d.ι y ∈ d.pull (X₄sub ⊔ Fsub) := ⟨y, commutator_Ssub_eq_X₄sub_sup_Fsub ▸ hy, rfl⟩
      rw [d.pull_sup] at this
      exact mem_sup_left this
    exact (hrC _ hyX).symm
  · exfalso
    apply h.not_comm_t_W
    intro w hw
    have e1 := hrC w (mem_sup_right hw)
    have e2 : (r * d.t) * w = w * (r * d.t) :=
      mem_centralizer_iff.1 (d.W_le_centralizer hw) _ hrS
    refine mul_left_cancel (a := r) ?_
    calc r * (w * d.t) = (w * r) * d.t := by rw [e1]; group
      _ = w * (r * d.t) := by group
      _ = r * d.t * w := e2.symm
      _ = r * (d.t * w) := by group

theorem mem_of_central_mod_FV₂
    (h : d.Hyp) {x : G}
    (hx : x ∈ d.R₂) (hc : ∀ y ∈ d.R₂, ⁅x, y⁆ ∈ d.F ⊔ d.V₂) :
    x ∈ ((d.X₄ ⊔ d.F) ⊔ d.V₂) ⊔ zpowers d.t := by
  obtain ⟨r, hr, k, hk, rfl⟩ := h.exists_mul_of_mem_R₂ hx
  obtain ⟨-, hkW⟩ := (h.mem_V₂_iff).1 hk
  have hrs : ∀ s ∈ d.S, ⁅r, s⁆ ∈ d.F := fun s hs => by
    have hcW : ⁅k, s⁆ ∈ d.W := by
      have := inv_mem (hkW s hs)
      rwa [show (s * k * s⁻¹ * k⁻¹)⁻¹ = ⁅k, s⁆ by rw [commutatorElement_def]; group] at this
    have hrW : r * ⁅k, s⁆ * r⁻¹ ∈ d.W :=
      (mem_normalizer_iff.1 (h.R_le_normalizer_W hr) _).1 hcW
    have e : ⁅r, s⁆ = (r * ⁅k, s⁆ * r⁻¹)⁻¹ * ⁅r * k, s⁆ := by
      simp only [commutatorElement_def]
      group
    have hmem : ⁅r, s⁆ ∈ d.F ⊔ d.V₂ := by
      rw [e]
      exact mul_mem (inv_mem (mem_sup_right (h.W_le_V₂ hrW))) (hc s (mem_sup_left
        (mem_sup_left hs)))
    have hS : ⁅r, s⁆ ∈ d.S := by
      rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.1 (h.R_le_normalizer_S hr) s).1 hs) (inv_mem hs)
    exact h.mem_F_of_mem_S_of_mem_FV₂ hS hmem
  have htS : ∀ k ∈ d.S, d.t * k * d.t ∈ d.S := fun k hk => by
    rw [← h.t_comm_of_mem_L (d.pull_le_L _ hk), mul_assoc, h.t_mul_t, mul_one]
    exact hk
  have key : ∀ s₀ ∈ d.S, (∀ s ∈ d.S, ⁅s₀, s⁆ ∈ d.F) → s₀ ∈ d.X₄ ⊔ d.F := fun s₀ hs₀ hs => by
    obtain ⟨σ, hσ, rfl⟩ := hs₀
    have hσX : σ ∈ X₄sub ⊔ Fsub := mem_X₄sub_sup_Fsub_iff.2 ⟨hσ, fun g hg => by
      have := inv_mem (hs _ ⟨g, hg, rfl⟩)
      rw [commutatorElement_inv, commutatorElement_def, ← map_inv, ← map_inv, ← map_mul,
        ← map_mul, ← map_mul] at this
      exact d.ι_mem_pull_iff.1 this⟩
    have : d.ι σ ∈ d.pull (X₄sub ⊔ Fsub) := ⟨σ, hσX, rfl⟩
    rw [d.pull_sup] at this
    exact this
  rcases (mem_sup_zpowers_iff h.t_mul_t htS).1 hr with hrS | hrS
  · exact mem_sup_left (mul_mem (mem_sup_left (key r hrS hrs)) (mem_sup_right hk))
  · have hs₀ : ∀ s ∈ d.S, ⁅r * d.t, s⁆ ∈ d.F := fun s hs => by
      rw [show ⁅r * d.t, s⁆ = ⁅r, s⁆ by
        simp only [commutatorElement_def]
        rw [show r * d.t * s * (r * d.t)⁻¹ * s⁻¹ = r * (d.t * s) * d.t⁻¹ * r⁻¹ * s⁻¹ by group,
          ← h.t_comm_of_mem_L (d.pull_le_L _ hs)]
        group]
      exact hrs s hs
    have hm := key _ hrS hs₀
    rw [show r * k = (r * d.t) * k * (k⁻¹ * d.t⁻¹ * k) by group]
    refine mul_mem (mem_sup_left (mul_mem (mem_sup_left hm) (mem_sup_right hk))) ?_
    rw [show k⁻¹ * d.t⁻¹ * k = (k⁻¹ * d.t⁻¹ * k * d.t) * d.t⁻¹ by group, h.t_inv]
    exact mul_mem (mem_sup_left (mem_sup_right (h.Z₂_le_V₂ (h.crossed_mem_Z₂_of_mem_V₂ hk))))
      (mem_sup_right (mem_zpowers _))

theorem commutator_t_mem_FV₂
    (h : d.Hyp) {y : G}
    (hy : y ∈ d.R₂) : ⁅d.t, y⁆ ∈ d.F ⊔ d.V₂ := by
  obtain ⟨r, hr, k, hk, rfl⟩ := h.exists_mul_of_mem_R₂ hy
  have htr : d.t * r = r * d.t := (mem_centralizer_singleton_iff.1 (h.R_le_H hr)).symm
  have hz := Z₂_le_F (h.commutator_t_mem_Z₂ hk)
  rw [show ⁅d.t, r * k⁆ = r * ⁅d.t, k⁆ * r⁻¹ by
    simp only [commutatorElement_def]
    rw [show d.t * (r * k) * d.t⁻¹ * (r * k)⁻¹ = (d.t * r) * k * d.t⁻¹ * k⁻¹ * r⁻¹ by group, htr]
    group]
  exact mem_sup_left ((mem_normalizer_iff.1 (h.R_le_normalizer_F hr) _).1 hz)

theorem crossed_mem_of_mem_normalizer_R₂
    (h : d.Hyp) {x : G}
    (hx : x ∈ normalizer (d.R₂ : Set G)) : x * d.t * x⁻¹ * d.t ∈ (d.X₄ ⊔ d.F) ⊔ d.V₂ := by
  have hxC : x ∈ normalizer ((d.F ⊔ d.V₂ : Subgroup G) : Set G) := by
    rw [← R₂_inf_centralizer_eq h]
    exact mem_normalizer_fintype fun y hy => conj_mem_inf_centralizer hx
      (mem_normalizer_fintype fun z hz => conj_mem_commutator_self_of_mem_normalizer hx hz) hy
  have hxD : x ∈ normalizer ((⁅d.R₂, d.R₂⁆ : Subgroup G) : Set G) :=
    mem_normalizer_fintype fun z hz => conj_mem_commutator_self_of_mem_normalizer hx hz
  have hXV : (d.X₄ ⊔ d.F) ⊔ d.V₂ = ⁅d.R₂, d.R₂⁆ ⊔ (d.F ⊔ d.V₂) := by
    rw [commutator_R₂_eq h]
    refine le_antisymm (sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_right))
      (sup_le (sup_le le_sup_left (h.W_le_V₂.trans le_sup_right)) (sup_le
        ((le_sup_right : d.F ≤ d.X₄ ⊔ d.F).trans le_sup_left) le_sup_right))
  have hxX : x ∈ normalizer (((d.X₄ ⊔ d.F) ⊔ d.V₂ : Subgroup G) : Set G) := by
    rw [hXV]
    exact mem_normalizer_sup hxD hxC
  have htR₂ : d.t ∈ d.R₂ := mem_sup_left (mem_sup_right (mem_zpowers _))
  have hm : x * d.t * x⁻¹ ∈ d.R₂ := (mem_normalizer_iff.1 hx _).1 htR₂
  have hcen : ∀ y ∈ d.R₂, ⁅x * d.t * x⁻¹, y⁆ ∈ d.F ⊔ d.V₂ := fun y hy => by
    have hy' : x⁻¹ * y * x ∈ d.R₂ := by
      have := (mem_normalizer_iff.1 (inv_mem hx) y).1 hy
      rwa [inv_inv] at this
    have e : ⁅x * d.t * x⁻¹, y⁆ = x * ⁅d.t, x⁻¹ * y * x⁆ * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (mem_normalizer_iff.1 hxC _).1 (h.commutator_t_mem_FV₂ hy')
  have hmem := h.mem_of_central_mod_FV₂ hm hcen
  have htn : ∀ k ∈ (d.X₄ ⊔ d.F) ⊔ d.V₂, d.t * k * d.t ∈ (d.X₄ ⊔ d.F) ⊔ d.V₂ := fun k hk => by
    have htN : d.t ∈ normalizer (((d.X₄ ⊔ d.F) ⊔ d.V₂ : Subgroup G) : Set G) := by
      refine mem_normalizer_sup (mem_normalizer_fintype fun a ha => ?_)
        (mem_normalizer_fintype fun v hv => ?_)
      · rw [← h.t_comm_of_mem_L (d.pull_le_L _ (XF_le_S ha)), mul_inv_cancel_right]
        exact ha
      · rw [h.t_inv, show d.t * v * d.t = v * (v⁻¹ * d.t * v * d.t) by group]
        exact mul_mem hv (h.Z₂_le_V₂ (h.crossed_mem_Z₂_of_mem_V₂ hv))
    have := (mem_normalizer_iff.1 htN k).1 hk
    rwa [h.t_inv] at this
  rcases (mem_sup_zpowers_iff h.t_mul_t htn).1 hmem with hk | hk
  · exfalso
    have htX : d.t ∈ (d.X₄ ⊔ d.F) ⊔ d.V₂ := by
      have := (mem_normalizer_iff.1 (inv_mem hxX) _).1 hk
      rwa [show x⁻¹ * (x * d.t * x⁻¹) * x⁻¹⁻¹ = d.t by group] at this
    obtain ⟨a, ha, v, hv, e⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha v hv => (h.Y_comm_XFW (h.V₂_le_Y hv) (mem_sup_left ha)).symm) htX
    have hvH : v ∈ d.H := by
      rw [show v = a⁻¹ * d.t by rw [← e]; group]
      exact mul_mem (inv_mem (h.L_le_H (d.pull_le_L _ (XF_le_S ha)))) h.t_mem_H
    have hvZ : v ∈ d.Z₂ := by
      rw [← h.V₂_inf_H]
      exact Subgroup.mem_inf.2 ⟨hv, hvH⟩
    apply h.t_not_mem_L
    rw [← e]
    exact mul_mem (d.pull_le_L _ (XF_le_S ha)) (d.pull_le_L _ (Z₂_le_A₁ hvZ))
  · exact hk

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
