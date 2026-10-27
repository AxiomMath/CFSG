module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBParts
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapQuasi
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3EThree

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups commutatorElement

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec52sinv_I_le_normalizer_L₁ (hB : d.CaseBHyp) : d.I ≤ normalizer (d.L₁ : Set G) := by
  have hd := hB.hyp
  have hB₆ : d.I ≤ normalizer (d.B₆ : Set G) := fun i hi => by
    have h1 := hd.I_le_normalizer_B₁ hi
    have hB₃ : i ∈ normalizer (d.B₃ : Set G) :=
      Common.mem_normalizer_sup (mem_normalizer_zpowers_t h1.2)
        (hd.normalizer_B₁_inf_le_normalizer_A₃ h1)
    exact d.normalizer_le_normalizer_B₆
      (Common.mem_normalizer_sup (hd.I_le_normalizer_F hB.gms hi) hB₃)
  intro i hi
  exact d.normalizer_D_le_normalizer_L₁ (mem_normalizer_D (hB₆ hi)
    (mem_normalizer_of_mem_centralizer' (d.I_le_centralizer_I₁ hi)))

namespace CaseBData

theorem sec52sinv_isQuasisimple_X (hd : d.Hyp) (c : d.CaseBData) :
    CFSG.Open.IsQuasisimple c.X :=
  hd.isQuasisimple_N₁.of_mulEquiv (c.φX.trans c.α.symm)

theorem sec52sinv_isQuasisimple_Y (hd : d.Hyp) (c : d.CaseBData) :
    CFSG.Open.IsQuasisimple c.Y :=
  hd.isQuasisimple_N₁.of_mulEquiv (c.φY.trans c.α.symm)

theorem sec52sinv_I_le_normalizer_X (hB : d.CaseBHyp) (c : d.CaseBData) :
    d.I ≤ normalizer (c.X : Set G) := by
  intro j hj
  have hd := hB.hyp
  have hjM : j ∈ normalizer ((c.X ⊔ c.Y : Subgroup G) : Set G) := by
    rw [c.X_sup_Y]
    exact d.I_le_normalizer_M₁ hj
  obtain ⟨hXp, hXb, hXd⟩ :=
    CFSG.SeitzReduction.F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple
      (sec52sinv_isQuasisimple_X hd c)
  obtain ⟨-, -, hYd⟩ :=
    CFSG.SeitzReduction.F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple
      (sec52sinv_isQuasisimple_Y hd c)
  have hjt : j * d.t = d.t * j := mem_centralizer_singleton_iff.1 (hd.I_le hj).1
  rcases CFSG.SeitzReduction.F4Pilot.map_conj_eq_or_eq_of_perfect c.Y_le_centralizer_X hXp hXb
    hXd hYd hjM with h1 | h1
  · exact CFSG.SeitzReduction.F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 h1
  ·
    have hY : c.Y.map (MulAut.conj j).toMonoidHom = c.X := by
      rw [← c.map_conj_t_X hd, CFSG.SeitzReduction.F4Pilot.map_conj_map_conj_toMonoidHom, hjt,
        ← CFSG.SeitzReduction.F4Pilot.map_conj_map_conj_toMonoidHom, h1, c.map_conj_t_Y hd]
    have hj2 : j * j ∈ normalizer (c.X : Set G) := by
      rw [CFSG.SeitzReduction.F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom,
        ← CFSG.SeitzReduction.F4Pilot.map_conj_map_conj_toMonoidHom, h1, hY]
    have hodd : Odd (orderOf j) :=
      Odd.of_dvd_nat d.odd_card_I (Subgroup.orderOf_dvd_natCard d.I hj)
    obtain ⟨m, hm⟩ := hodd
    have hpow : j = (j * j) ^ (m + 1) := by
      have h1 : j ^ (2 * m + 1) = 1 := hm ▸ pow_orderOf_eq_one j
      calc j = j ^ (2 * m + 1) * j := by rw [h1, one_mul]
        _ = j ^ (2 * (m + 1)) := by
          rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
          exact (pow_succ j (2 * m + 1)).symm
        _ = (j * j) ^ (m + 1) := by rw [pow_mul, sq]
    rw [hpow]
    exact Subgroup.pow_mem _ hj2 _

theorem sec52sinv_I_le_normalizer_Kc (hB : d.CaseBHyp) (c : d.CaseBData) :
    d.I ≤ normalizer (c.Kc : Set G) := by
  intro j hj
  have hjL₁ := sec52sinv_I_le_normalizer_L₁ hB hj
  have hjX := sec52sinv_I_le_normalizer_X hB c hj
  refine mem_normalizer_fintype fun x hx => ?_
  have hle : c.Kc ≤ c.Kc.comap (MulAut.conj j).toMonoidHom := by
    refine normalClosureIn_le (fun y hy => ?_) (fun g hg => ?_)
    · exact c.X_le_Kc hB ((mem_normalizer_iff.1 hjX y).1 hy)
    · rw [mem_normalizer_iff]
      intro y
      have hg' : j * g * j⁻¹ ∈ d.L₁ := (mem_normalizer_iff.1 hjL₁ g).1 hg
      have hconj : j * (g * y * g⁻¹) * j⁻¹ =
          (j * g * j⁻¹) * (j * y * j⁻¹) * (j * g * j⁻¹)⁻¹ := by group
      simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hconj]
      exact mem_normalizer_iff.1 (c.L₁_le_normalizer_Kc hg') (j * y * j⁻¹)
  exact hle hx

theorem sec52sinv_V_le_E (hB : d.CaseBHyp) : d.V ≤ d.E := by
  rw [← hB.hyp.centerIn_E hB.gms]
  exact inf_le_left

theorem sec52sinv_V_comm (hB : d.CaseBHyp) {v e : G} (hv : v ∈ d.V) (he : e ∈ d.E) :
    e * v = v * e := by
  have hz : v ∈ CFSG.centerIn d.E := by
    rw [hB.hyp.centerIn_E hB.gms]
    exact hv
  exact mem_centralizer_iff.1 hz.2 e he

theorem sec52sinv_mem_W₂_sup_V_iff (hB : d.CaseBHyp) (c : d.CaseBData)
    (h12 : CaseBData.Sec52Factors hB c) {x : G} :
    x ∈ c.W₂ ⊔ d.V ↔ x ∈ d.E ∧ ∀ e ∈ d.E, ⁅x, e⁆ ∈ d.V ⊓ c.Kc := by
  have hd := hB.hyp
  have hEN : ∀ e ∈ d.E, e ∈ normalizer (c.Kc : Set G) := fun e he =>
    c.L₁_le_normalizer_Kc ((c.E_le_S hB).trans (c.S_le_L₁ hB) he)
  have hVcomm : ∀ a ∈ c.W₂, ∀ b ∈ d.V, a * b = b * a := fun a ha b hb =>
    sec52sinv_V_comm hB hb ha.1
  constructor
  · intro hx
    refine ⟨sup_le inf_le_left (sec52sinv_V_le_E hB) hx, fun e he => ?_⟩
    obtain ⟨w, hw, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_commute hVcomm hx
    have hve : v * e = e * v := (sec52sinv_V_comm hB hv he).symm
    have hcomm : ⁅w * v, e⁆ = ⁅w, e⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc w * v * e * (w * v)⁻¹ * e⁻¹ = w * (v * e) * v⁻¹ * w⁻¹ * e⁻¹ := by group
        _ = w * (e * v) * v⁻¹ * w⁻¹ * e⁻¹ := by rw [hve]
        _ = w * e * w⁻¹ * e⁻¹ := by group
    rw [hcomm]
    refine ⟨(hd.elemAbMod_V_E hB.gms).2 w hw.1 e he, ?_⟩
    rw [commutatorElement_def]
    have : e * w⁻¹ * e⁻¹ ∈ c.Kc := (mem_normalizer_iff.1 (hEN e he) w⁻¹).1 (inv_mem hw.2)
    simpa [mul_assoc] using mul_mem hw.2 this
  · rintro ⟨hxE, hx⟩
    have hW₂t_le : c.W₂t ≤ c.Kt := Subgroup.map_mono inf_le_right
    have hcommW : ∀ a ∈ c.W₂, ∀ b ∈ c.W₂t, a * b = b * a := fun a ha b hb =>
      c.commute_of_mem_Kc_of_mem_Kt hB ha.2 (hW₂t_le hb)
    rw [h12.E_eq] at hxE
    obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hcommW hxE
    have he₂K : e₂ ∈ c.Kt := hW₂t_le he₂
    have he₂E : e₂ ∈ d.E := by
      rw [h12.E_eq]
      exact mem_sup_right he₂
    have hcomm₂ : ∀ e' ∈ c.W₂t, e₂ * e' = e' * e₂ := by
      intro e' he'
      have he'E : e' ∈ d.E := by
        rw [h12.E_eq]
        exact mem_sup_right he'
      have hu : e₁ * (e₂ * e' * e₂⁻¹) = (e₂ * e' * e₂⁻¹) * e₁ :=
        c.commute_of_mem_Kc_of_mem_Kt hB he₁.2
          (mul_mem (mul_mem he₂K (hW₂t_le he')) (inv_mem he₂K))
      have hcalc : ⁅e₁ * e₂, e'⁆ = ⁅e₂, e'⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc e₁ * e₂ * e' * (e₁ * e₂)⁻¹ * e'⁻¹
            = e₁ * (e₂ * e' * e₂⁻¹) * e₁⁻¹ * e'⁻¹ := by group
          _ = (e₂ * e' * e₂⁻¹) * e₁ * e₁⁻¹ * e'⁻¹ := by rw [hu]
          _ = e₂ * e' * e₂⁻¹ * e'⁻¹ := by group
      have hK : ⁅e₂, e'⁆ ∈ c.Kc := by
        rw [← hcalc]
        exact (hx e' he'E).2
      have hKt : ⁅e₂, e'⁆ ∈ c.Kt := by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem he₂K (hW₂t_le he')) (inv_mem he₂K))
          (inv_mem (hW₂t_le he'))
      have h1 : ⁅e₂, e'⁆ ∈ c.Kc ⊓ c.Kt := ⟨hK, hKt⟩
      rw [c.Kc_inf_Kt hB, mem_bot, commutatorElement_def, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hcomm₁ : ∀ a ∈ c.W₂, a * e₂ = e₂ * a := fun a ha =>
      c.commute_of_mem_Kc_of_mem_Kt hB ha.2 he₂K
    have hE_le : d.E ≤ centralizer ({e₂} : Set G) := by
      rw [h12.E_eq]
      exact sup_le (fun a ha => mem_centralizer_singleton_iff.2 (hcomm₁ a ha))
        (fun b hb => mem_centralizer_singleton_iff.2 (hcomm₂ b hb).symm)
    have he₂V : e₂ ∈ d.V := by
      rw [← hd.centerIn_E hB.gms]
      exact ⟨he₂E, mem_centralizer_iff.2 fun y hy =>
        mem_centralizer_singleton_iff.1 (hE_le hy)⟩
    exact mul_mem (mem_sup_left he₁) (mem_sup_right he₂V)

theorem sec52sinv_comm_V_of_mem_L₂ (hB : d.CaseBHyp) {g v : G} (hg : g ∈ d.L₂) (hv : v ∈ d.V) :
    g * v * g⁻¹ = v := by
  have hz : v ∈ CFSG.centerIn d.L₂ := hB.sec3_8.2.1 hv
  have := mem_centralizer_iff.1 hz.2 g hg
  rw [this]
  group

theorem sec52sinv_s_mem_W₂_sup_V (hB : d.CaseBHyp) (c : d.CaseBData)
    (h12 : CaseBData.Sec52Factors hB c) {x : G} (hx : x ∈ c.W₂ ⊔ d.V) :
    d.s * x * d.s⁻¹ ∈ c.W₂ ⊔ d.V := by
  rw [sec52sinv_mem_W₂_sup_V_iff hB c h12] at hx ⊢
  obtain ⟨hxE, hx⟩ := hx
  have hsE : d.s ∈ normalizer (d.E : Set G) := d.N₂_le_normalizer_E d.s_mem_N₂
  refine ⟨(mem_normalizer_iff.1 hsE x).1 hxE, fun e he => ?_⟩
  have he' : d.s⁻¹ * e * d.s ∈ d.E := by
    have := (mem_normalizer_iff.1 (inv_mem hsE) e).1 he
    simpa using this
  have key := hx _ he'
  have hconj : ⁅d.s * x * d.s⁻¹, e⁆ = d.s * ⁅x, d.s⁻¹ * e * d.s⁆ * d.s⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hconj, sec52sinv_comm_V_of_mem_L₂ hB (d.N₂_le_L₂ d.s_mem_N₂) key.1]
  exact key

theorem sec52sinv_map_W₂_sup_V (hB : d.CaseBHyp) (c : d.CaseBData)
    (h12 : CaseBData.Sec52Factors hB c) :
    (c.W₂ ⊔ d.V).map (MulAut.conj d.s).toMonoidHom = c.W₂ ⊔ d.V := by
  have hle : (c.W₂ ⊔ d.V).map (MulAut.conj d.s).toMonoidHom ≤ c.W₂ ⊔ d.V := by
    rintro _ ⟨x, hx, rfl⟩
    exact sec52sinv_s_mem_W₂_sup_V hB c h12 hx
  refine le_antisymm hle ?_
  have := Subgroup.map_mono (f := (MulAut.conj d.s).toMonoidHom) hle
  rwa [CFSG.SeitzReduction.F4Pilot.map_conj_map_conj_toMonoidHom, d.s_mul_s,
    CFSG.SeitzReduction.F4Pilot.map_conj_one_toMonoidHom] at this

theorem sec52sinv_J_le_normalizer_W₂ (hB : d.CaseBHyp) (c : d.CaseBData) :
    d.I ⊓ d.N₂ ≤ normalizer (c.W₂ : Set G) := fun _ hj =>
  Common.mem_normalizer_inf (d.N₂_le_normalizer_E hj.2) (sec52sinv_I_le_normalizer_Kc hB c hj.1)

theorem sec52sinv_commutator_mem_W₂ (hB : d.CaseBHyp) (c : d.CaseBData) {w j : G}
    (hw : w ∈ c.W₂) (hj : j ∈ d.I ⊓ d.N₂) : ⁅w, j⁆ ∈ c.W₂ := by
  have := (mem_normalizer_iff.1 (sec52sinv_J_le_normalizer_W₂ hB c hj) w⁻¹).1 (inv_mem hw)
  rw [commutatorElement_def]
  simpa [mul_assoc] using mul_mem hw this

theorem sec52sinv_commutator_sup_le (hB : d.CaseBHyp) (c : d.CaseBData) :
    ⁅c.W₂ ⊔ d.V, d.I ⊓ d.N₂⁆ ≤ c.W₂ := by
  refine commutator_le.2 fun x hx j hj => ?_
  have hVcomm : ∀ a ∈ c.W₂, ∀ b ∈ d.V, a * b = b * a := fun a ha b hb =>
    sec52sinv_V_comm hB hb ha.1
  obtain ⟨w, hw, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_commute hVcomm hx
  have hjv : j * v * j⁻¹ = v := sec52sinv_comm_V_of_mem_L₂ hB (d.N₂_le_L₂ hj.2) hv
  have hvj : v * j = j * v := by
    calc v * j = (j * v * j⁻¹) * j := by rw [hjv]
      _ = j * v := by group
  have hcomm : ⁅w * v, j⁆ = ⁅w, j⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc w * v * j * (w * v)⁻¹ * j⁻¹ = w * (v * j) * v⁻¹ * w⁻¹ * j⁻¹ := by group
      _ = w * (j * v) * v⁻¹ * w⁻¹ * j⁻¹ := by rw [hvj]
      _ = w * j * w⁻¹ * j⁻¹ := by group
  rw [hcomm]
  exact sec52sinv_commutator_mem_W₂ hB c hw hj

theorem sec52sinv_δ_conj (hB : d.CaseBHyp) (c : d.CaseBData) {g : G}
    (hg : g ∈ centralizer ({d.t} : Set G)) (y : c.Kc) (hgy : g * (y : G) * g⁻¹ ∈ c.Kc) :
    c.δ hB ⟨g * (y : G) * g⁻¹, hgy⟩ = g * c.δ hB y * g⁻¹ := by
  have hc : g * d.t = d.t * g :=
    (Subgroup.mem_centralizer_iff.1 hg d.t (Set.mem_singleton _)).symm
  have e1 : d.t⁻¹ * g = g * d.t⁻¹ := by
    calc d.t⁻¹ * g = d.t⁻¹ * (g * d.t) * d.t⁻¹ := by group
      _ = d.t⁻¹ * (d.t * g) * d.t⁻¹ := by rw [hc]
      _ = g * d.t⁻¹ := by group
  have e2 : g⁻¹ * d.t = d.t * g⁻¹ := by
    calc g⁻¹ * d.t = g⁻¹ * (d.t * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * d.t) * g⁻¹ := by rw [← hc]
      _ = d.t * g⁻¹ := by group
  have key : d.t⁻¹ * (g * (y : G) * g⁻¹) * d.t = g * (d.t⁻¹ * (y : G) * d.t) * g⁻¹ := by
    rw [show d.t⁻¹ * (g * (y : G) * g⁻¹) * d.t = (d.t⁻¹ * g) * (y : G) * (g⁻¹ * d.t) by group,
      e1, e2]
    group
  change (g * (y : G) * g⁻¹) * (d.t⁻¹ * (g * (y : G) * g⁻¹) * d.t) =
    g * ((y : G) * (d.t⁻¹ * (y : G) * d.t)) * g⁻¹
  rw [key]
  group

theorem sec52sinv_A₂_commutator_le (hB : d.CaseBHyp) (c : d.CaseBData)
    (h12 : CaseBData.Sec52Factors hB c) :
    ⁅d.A₂, d.I ⊓ d.N₂⁆ ≤ ((⁅c.W₂, d.I ⊓ d.N₂⁆).subgroupOf c.Kc).map (c.δ hB) := by
  refine commutator_le.2 fun a ha j hj => ?_
  rw [← h12.map_δ] at ha
  obtain ⟨u, hu, rfl⟩ := ha
  have huW : (u : G) ∈ c.W₂ := hu
  have hjt : j ∈ centralizer ({d.t} : Set G) := (hB.hyp.I_le hj.1).1
  have hjW : j * (u : G)⁻¹ * j⁻¹ ∈ c.W₂ :=
    (mem_normalizer_iff.1 (sec52sinv_J_le_normalizer_W₂ hB c hj) (u : G)⁻¹).1 (inv_mem huW)
  have hjK : j * ((u⁻¹ : c.Kc) : G) * j⁻¹ ∈ c.Kc := by simpa using hjW.2
  refine ⟨u * ⟨j * ((u⁻¹ : c.Kc) : G) * j⁻¹, hjK⟩, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_subgroupOf]
    have : ((u * ⟨j * ((u⁻¹ : c.Kc) : G) * j⁻¹, hjK⟩ : c.Kc) : G) = ⁅(u : G), j⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact Subgroup.commutator_mem_commutator huW hj
  · rw [map_mul, sec52sinv_δ_conj hB c hjt (u⁻¹) hjK, map_inv]
    simp [commutatorElement_def, mul_assoc]

theorem sec52sinv_commutator_W₂_J (hB : d.CaseBHyp) (c : d.CaseBData)
    (h12 : CaseBData.Sec52Factors hB c) : ⁅c.W₂, d.I ⊓ d.N₂⁆ = c.W₂ := by
  refine le_antisymm (commutator_le.2 fun w hw j hj => sec52sinv_commutator_mem_W₂ hB c hw hj) ?_
  intro w hw
  set u : c.Kc := ⟨w, hw.2⟩ with hu
  have hδu : c.δ hB u ∈ d.A₂ := by
    rw [← h12.map_δ]
    exact ⟨u, hw, rfl⟩
  have hR := sec52sinv_A₂_commutator_le hB c h12
  rw [d.commutator_A₂_I_inf_N₂] at hR
  obtain ⟨u', hu', hu'δ⟩ := hR hδu
  have hEq : u' = u := c.injective_δ hB hu'δ
  rw [hEq] at hu'
  exact hu'

theorem sec52sinv_commutator_sup_eq (hB : d.CaseBHyp) (c : d.CaseBData)
    (h12 : CaseBData.Sec52Factors hB c) : ⁅c.W₂ ⊔ d.V, d.I ⊓ d.N₂⁆ = c.W₂ :=
  le_antisymm (sec52sinv_commutator_sup_le hB c)
    ((sec52sinv_commutator_W₂_J hB c h12).symm.le.trans (commutator_mono le_sup_left le_rfl))

theorem sec52_sInv (hB : d.CaseBHyp) (c : d.CaseBData) (h11 : CaseBData.Sec52Sylow hB c)
    (h12 : CaseBData.Sec52Factors hB c) :
    c.W₂.map (MulAut.conj d.s).toMonoidHom = c.W₂ := by
  have hsJ : d.s ∈ normalizer ((d.I ⊓ d.N₂ : Subgroup G) : Set G) :=
    Common.mem_normalizer_inf
      (CFSG.SeitzReduction.F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2
        d.sec2_1_five.2.1)
      (le_normalizer d.s_mem_N₂)
  have hJs : (d.I ⊓ d.N₂).map (MulAut.conj d.s).toMonoidHom = d.I ⊓ d.N₂ :=
    map_conj_eq_of_mem_normalizer hsJ
  calc c.W₂.map (MulAut.conj d.s).toMonoidHom
      = (⁅c.W₂ ⊔ d.V, d.I ⊓ d.N₂⁆).map (MulAut.conj d.s).toMonoidHom := by
        rw [sec52sinv_commutator_sup_eq hB c h12]
    _ = ⁅(c.W₂ ⊔ d.V).map (MulAut.conj d.s).toMonoidHom,
          (d.I ⊓ d.N₂).map (MulAut.conj d.s).toMonoidHom⁆ := Subgroup.map_commutator _ _ _
    _ = ⁅c.W₂ ⊔ d.V, d.I ⊓ d.N₂⁆ := by rw [sec52sinv_map_W₂_sup_V hB c h12, hJs]
    _ = c.W₂ := sec52sinv_commutator_sup_eq hB c h12

end CaseBData

end Data

namespace CaseBParts

theorem sec52SInv : Sec52SInvStatement :=
  fun _ _ _ _ _ _ _ _ hB c h11 h12 => Data.CaseBData.sec52_sInv hB c h11 h12

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
