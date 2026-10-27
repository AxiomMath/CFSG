module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Root
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Weyl
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Cross
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Gen

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.OddStandard.Seitz77.CaseB45
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open scoped commutatorElement

section Gen

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G} {c : CaseB A R t}
  {M M' S A₁ B₁ : Subgroup G} (Sd : Side c M M' S A₁ B₁)

include Sd

theorem Side.cs_dg_eq {m : G} (hm : m ∈ M) {Y : Subgroup G} (hY : Y ≤ M) :
    cs (m * (t * m * t⁻¹)) Y = cs m Y := by
  ext z
  constructor
  · intro hz
    have hy : (m * (t * m * t⁻¹))⁻¹ * z * (m * (t * m * t⁻¹)) ∈ Y := mem_cs.mp hz
    have hz' : z = m * ((m * (t * m * t⁻¹))⁻¹ * z * (m * (t * m * t⁻¹))) * m⁻¹ := by
      calc z = (m * (t * m * t⁻¹)) * ((m * (t * m * t⁻¹))⁻¹ * z * (m * (t * m * t⁻¹))) *
            (m * (t * m * t⁻¹))⁻¹ := by group
        _ = _ := Sd.dg_conj_self hm (hY hy)
    rw [hz']
    exact mem_cs_iff.mpr hy
  · intro hz
    have hy : m⁻¹ * z * m ∈ Y := mem_cs.mp hz
    have hz' : z = (m * (t * m * t⁻¹)) * (m⁻¹ * z * m) * (m * (t * m * t⁻¹))⁻¹ := by
      rw [Sd.dg_conj_self hm (hY hy)]
      group
    rw [hz']
    exact mem_cs_iff.mpr hy

end Gen

section Comm

variable {G : Type} [Group G] [Finite G] {A V₁ V₂ : Subgroup G} {d : Datum A}
  {c₁ : CaseB A V₁ d.t} {c₂ : CaseB A V₂ d.t} {M₁ M₂ N₁ N₂ S A₁ B₁ : Subgroup G} {k : Type}
  [Field k] {e : ↥A₁ ≃* ↥(unipAll k)} (CS : CommonSylow c₁ c₂ M₁ M₂ N₁ N₂ S A₁ B₁ e)

include CS

theorem CommonSylow.commutator_M₁_N₂ (hR : Radicals d.V V₁ V₂) (hZ₁ : c₁.OddCoreCentral)
    (hZ₂ : c₂.OddCoreCentral) {σa σb : G} {Up Uq : Subgroup G}
    (W : WeylInput A d.V V₁ V₂ σa σb Up Uq) : ⁅M₁, N₂⁆ = ⊥ := by
  have S₁ := CS.side₁ hZ₁
  have S₂ := CS.side₂ hZ₂
  have P := CS.swapPair
  have hσaN : σa ∈ c₁.Ninf := perfectResidualOf_mono c₁.normalizer_A_R_le_N W.σa_mem
  have hσbN : σb ∈ c₂.Ninf := perfectResidualOf_mono c₂.normalizer_A_R_le_N W.σb_mem
  have hσaA : σa ∈ A := (perfectResidualOf_le' _ W.σa_mem).1
  have hσbA : σb ∈ A := (perfectResidualOf_le' _ W.σb_mem).1
  have hσat : σa * d.t = d.t * σa := d.comm_t_of_mem hσaA
  have hσbt : σb * d.t = d.t * σb := d.comm_t_of_mem hσbA
  obtain ⟨m, hm, hσam⟩ := CS.F₁.exists_diag hZ₁ hσaN hσat
  obtain ⟨n, hn, hσbn⟩ := CS.F₂.exists_diag hZ₂ hσbN hσbt
  have hVd : ∀ a ∈ A₁, a * (d.t * a * d.t⁻¹) ∈ d.V := fun a ha => (CS.syl.V_diag _).mpr ⟨a, ha, rfl⟩
  have hV : ∀ v ∈ d.V, ∃ a ∈ A₁, v = a * (d.t * a * d.t⁻¹) := fun v hv => (CS.syl.V_diag v).mp hv
  have hUgc : ∀ u ∈ V₁ ⊓ V₂, ∀ v ∈ d.V, u * v = v * u := by
    intro u hu v hv
    rw [hR.inf_eq] at hu
    exact (mem_centralizer_iff.mp hu.2 v hv).symm
  have hUg4 : Nat.card ↥(V₁ ⊓ V₂) = 4 := by rw [hR.inf_eq]; exact hR.card_center
  have hUp4 : Nat.card ↥Up = 4 := by
    rw [← nat_card_cs σa Up, W.cs_a1]; exact hUg4
  have hUq4 : Nat.card ↥Uq = 4 := by
    rw [← nat_card_cs σb Uq, W.cs_b1]; exact hUg4
  have hUpV : Up ≤ d.V := W.Up_le.trans hR.le₁
  have hUqV : Uq ≤ d.V := W.Uq_le.trans hR.le₂
  have hUp1 : Up ≤ c₁.W := W.Up_le.trans c₁.R_le_W
  have hUg1 : V₁ ⊓ V₂ ≤ c₁.W := inf_le_left.trans c₁.R_le_W
  have hUq2 : Uq ≤ c₂.W := W.Uq_le.trans c₂.R_le_W
  have hUg2 : V₁ ⊓ V₂ ≤ c₂.W := inf_le_right.trans c₂.R_le_W
  have hUq1 : Uq ⊓ V₁ = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [← W.Uq_inf]
    exact ⟨hx.1, hx.2, W.Uq_le hx.1⟩
  have hUp2 : Up ⊓ V₂ = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [← W.Up_inf]
    exact ⟨hx.1, W.Up_le hx.1, hx.2⟩
  have hneP : ∃ u ∈ Up, ∃ v ∈ d.V, u * v ≠ v * u := by
    by_contra hcon
    push Not at hcon
    have hle : Up ≤ V₁ ⊓ V₂ := by
      intro u hu
      rw [hR.inf_eq]
      exact ⟨hUpV hu, mem_centralizer_iff.mpr fun v hv => (hcon u hu v hv).symm⟩
    have : Up = ⊥ := by
      rw [← W.Up_inf]
      exact (inf_eq_left.mpr hle).symm
    rw [this] at hUp4
    simp at hUp4
  have hneQ : ∃ u ∈ Uq, ∃ v ∈ d.V, u * v ≠ v * u := by
    by_contra hcon
    push Not at hcon
    have hle : Uq ≤ V₁ ⊓ V₂ := by
      intro u hu
      rw [hR.inf_eq]
      exact ⟨hUqV hu, mem_centralizer_iff.mpr fun v hv => (hcon u hu v hv).symm⟩
    have : Uq = ⊥ := by
      rw [← W.Uq_inf]
      exact (inf_eq_left.mpr hle).symm
    rw [this] at hUq4
    simp at hUq4
  have t1 : cs m (Yof P Up) = Yof P (V₁ ⊓ V₂) :=
    S₁.cs_Yof hm hUp1 hUg1 (by rw [← hσam]; exact W.cs_a1)
  have t2 : cs m (Yof P (V₁ ⊓ V₂)) = Yof P Up :=
    S₁.cs_Yof hm hUg1 hUp1 (by rw [← hσam]; exact W.cs_a2)
  have t3 : cs n (Yof P Uq) = Yof P (V₁ ⊓ V₂) :=
    S₂.cs_Yof hn hUq2 hUg2 (by rw [← hσbn]; exact W.cs_b1)
  have t4 : cs n (Yof P (V₁ ⊓ V₂)) = Yof P Uq :=
    S₂.cs_Yof hn hUg2 hUq2 (by rw [← hσbn]; exact W.cs_b2)
  have hM₁ : ∀ Y : Subgroup G, Y ≤ A₁ → Y ≤ M₁ := fun Y hY => hY.trans CS.A₁_le_M₁
  have hN₁ : ∀ Y : Subgroup G, Y ≤ A₁ → Y ≤ N₁ := fun Y hY => hY.trans CS.A₁_le_N₁
  have hpg : cs σa (Yof P Up) = Yof P (V₁ ⊓ V₂) := by
    rw [hσam, S₁.cs_dg_eq hm (hM₁ _ (Yof_le P))]; exact t1
  have hgp : cs σa (Yof P (V₁ ⊓ V₂)) = Yof P Up := by
    rw [hσam, S₁.cs_dg_eq hm (hM₁ _ (Yof_le P))]; exact t2
  have hqg : cs σb (Yof P Uq) = Yof P (V₁ ⊓ V₂) := by
    rw [hσbn, S₂.cs_dg_eq hn (hN₁ _ (Yof_le P))]; exact t3
  have hgq : cs σb (Yof P (V₁ ⊓ V₂)) = Yof P Uq := by
    rw [hσbn, S₂.cs_dg_eq hn (hN₁ _ (Yof_le P))]; exact t4
  have hε : ∀ y ∈ A₁, ((σb * σa * σb)⁻¹ * (σa * σb * σa)) * y =
      y * ((σb * σa * σb)⁻¹ * (σa * σb * σa)) := by
    intro y hy
    have h1 := c₁.center_le_centralizer_W W.braid
    have h2 := c₂.center_le_centralizer_W W.braid
    have hS : S ≤ centralizer ({(σb * σa * σb)⁻¹ * (σa * σb * σa)} : Set G) := by
      rw [← CS.W_sup]
      exact sup_le (fun w hw => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h1 w hw))
        (fun w hw => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h2 w hw))
    exact (mem_centralizer_singleton_iff.mp (hS (CS.A₁_le_S hy))).symm
  have hcross := cross_of_weyl hσat hσbt hε (Yof_le P : Yof P Up ≤ A₁) (Yof_le P : Yof P Uq ≤ A₁)
    hpg hgp hqg hgq P.comm P.B_eq.symm
  have hUgW₁ : Yof P (V₁ ⊓ V₂) ≤ c₁.W ⊓ M₁ := by
    intro y hy
    obtain ⟨hyA, hyU⟩ := (mem_Yof P).mp hy
    exact ⟨S₁.mem_W_of_diag hyA (hUg1 hyU), CS.A₁_le_M₁ hyA⟩
  have hUgW₂ : Yof P (V₁ ⊓ V₂) ≤ c₂.W ⊓ N₁ := by
    intro y hy
    obtain ⟨hyA, hyU⟩ := (mem_Yof P).mp hy
    exact ⟨S₂.mem_W_of_diag hyA (hUg2 hyU), CS.A₁_le_N₁ hyA⟩
  have hYq4 : Nat.card ↥(Yof P Uq) = 4 := by rw [Yof_card P hV hUqV]; exact hUq4
  have hYp4 : Nat.card ↥(Yof P Up) = 4 := by rw [Yof_card P hV hUpV]; exact hUp4
  have hgen₁ : A₁ ⊔ cs m (Yof P Uq) = M₁ :=
    CS.F₁.eq_sup_cs_of_moves hZ₁ S₁.sylow S₁.W_inf_le hm (Yof_le P) hYq4 (S₁.Yof_inf_W hUq1) hUgW₁
      (Yof_comm P hVd hUgc) t2 (Yof_not_comm P hV hUpV hneP)
  have hgen₂ : A₁ ⊔ cs n (Yof P Up) = N₁ :=
    CS.F₂.eq_sup_cs_of_moves hZ₂ S₂.sylow S₂.W_inf_le hn (Yof_le P) hYp4 (S₂.Yof_inf_W hUp2) hUgW₂
      (Yof_comm P hVd hUgc) t4 (Yof_not_comm P hV hUqV hneQ)
  have hcross' : ∀ x ∈ cs m (Yof P Uq), ∀ y ∈ cs d.t (cs n (Yof P Up)), x * y = y * x := by
    intro x hx y hy
    rw [← S₁.cs_dg_eq hm (hM₁ _ (Yof_le P)), ← hσam] at hx
    rw [← S₂.cs_dg_eq hn (hN₁ _ (Yof_le P)), ← hσbn] at hy
    exact hcross x hx y hy
  have hxM : ∀ x ∈ cs m (Yof P Uq), x ∈ M₁ := by
    intro x hx
    have := mem_cs.mp hx
    have h2 : m⁻¹ * x * m ∈ M₁ := CS.A₁_le_M₁ (Yof_le P this)
    have e : x = m * (m⁻¹ * x * m) * m⁻¹ := by group
    rw [e]
    exact M₁.mul_mem (M₁.mul_mem hm h2) (M₁.inv_mem hm)
  have hN₂eq : N₂ = B₁ ⊔ cs d.t (cs n (Yof P Up)) := by
    rw [CS.N₂_eq, ← hgen₂, cs_sup, ← P.B_eq]
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← hgen₁]
  refine sup_le (fun a ha => ?_) (fun x hx => ?_)
  · rw [mem_centralizer_iff]
    intro y hy
    exact (CS.F₂.comm_elem hZ₂ (CS.A₁_le_N₁ ha) hy).symm
  · rw [mem_centralizer_iff]
    intro y hy
    have hle : N₂ ≤ centralizer ({x} : Set G) := by
      rw [hN₂eq]
      refine sup_le (fun b hb => ?_) (fun z hz => ?_)
      · exact mem_centralizer_singleton_iff.mpr
          (CS.F₁.comm_elem hZ₁ (hxM x hx) (CS.B₁_le_M₂ hb)).symm
      · exact mem_centralizer_singleton_iff.mpr (hcross' x hx z hz).symm
    exact mem_centralizer_singleton_iff.mp (hle hy)

theorem CommonSylow.commutator_G₁_G₂ (hR : Radicals d.V V₁ V₂) (hZ₁ : c₁.OddCoreCentral)
    (hZ₂ : c₂.OddCoreCentral) {σa σb : G} {Up Uq : Subgroup G}
    (W : WeylInput A d.V V₁ V₂ σa σb Up Uq) : ⁅M₁ ⊔ N₁, M₂ ⊔ N₂⁆ = ⊥ := by
  have h12 := CS.commutator_M₁_N₂ hR hZ₁ hZ₂ W
  have h11 : ⁅M₁, M₂⁆ = ⊥ := CS.F₁.comm_eq_bot hZ₁
  have h22 : ⁅N₁, N₂⁆ = ⊥ := CS.F₂.comm_eq_bot hZ₂
  have ht : d.t * d.t = 1 := c₁.t_mul_self
  have h21 : ⁅N₁, M₂⁆ = ⊥ := by
    have h := congrArg (cs d.t) h12
    rw [cs_commutator] at h
    have e1 : cs d.t M₁ = M₂ := CS.M₂_eq.symm
    have e2 : cs d.t N₂ = N₁ := by rw [CS.N₂_eq, ← cs_mul, ht, cs_one]
    have e3 : cs d.t (⊥ : Subgroup G) = ⊥ := by
      ext x
      rw [mem_cs, Subgroup.mem_bot, Subgroup.mem_bot]
      constructor
      · intro hx
        have : x = d.t * 1 * d.t⁻¹ := by rw [← hx]; group
        rw [this]; group
      · rintro rfl
        group
    rw [e1, e2, e3] at h
    rw [Subgroup.commutator_comm]
    exact h
  have c11 : M₁ ≤ centralizer (M₂ : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h11
  have c12 : M₁ ≤ centralizer (N₂ : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h12
  have c21 : N₁ ≤ centralizer (M₂ : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h21
  have c22 : N₁ ≤ centralizer (N₂ : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h22
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · rw [mem_centralizer_iff]
    intro y hy
    have hle : (M₂ ⊔ N₂ : Subgroup G) ≤ centralizer ({x} : Set G) :=
      sup_le (fun z hz => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (c11 hx) z hz))
        (fun z hz => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (c12 hx) z hz))
    exact mem_centralizer_singleton_iff.mp (hle hy)
  · rw [mem_centralizer_iff]
    intro y hy
    have hle : (M₂ ⊔ N₂ : Subgroup G) ≤ centralizer ({x} : Set G) :=
      sup_le (fun z hz => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (c21 hx) z hz))
        (fun z hz => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (c22 hx) z hz))
    exact mem_centralizer_singleton_iff.mp (hle hy)

end Comm

end CFSG.OddStandard.Seitz77
