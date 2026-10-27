module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Key

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

structure Sec11cProj (G : Type) [Group G] (z : G) (D Q V : Subgroup G) : Prop where
  DQ_comm : ∀ d ∈ D, ∀ q ∈ Q, d * q = q * d
  inf_eq : D ⊓ Q = zpowers z
  z_memD : z ∈ D
  z_memQ : z ∈ Q
  Q_z : ∀ q ∈ Q, q * z = z * q
  Q_el : IsElemAbelianMod z Q
  V_normD : ∀ v ∈ V, ∀ d ∈ D, v * d * v⁻¹ ∈ D
  V_normQ : ∀ v ∈ V, ∀ q ∈ Q, v * q * v⁻¹ ∈ Q
  V_z : ∀ v ∈ V, v * z = z * v
  V_el : IsElemAbelianMod z V

namespace Sec11cProj

variable {z : G} {D Q V : Subgroup G}

private theorem le_Csup (h : Sec11cProj G z D Q V) :
    V ⊓ (D ⊔ Q) ≤ V ⊓ (D ⊓ (V ⊔ Q) ⊔ Q) := by
  intro v hv
  rw [Subgroup.mem_inf] at hv
  obtain ⟨hvV, hvDQ⟩ := hv
  obtain ⟨d, hd, q, hq, hdq⟩ := exists_mul_of_mem_sup_of_commute h.DQ_comm hvDQ
  rw [Subgroup.mem_inf]
  refine ⟨hvV, ?_⟩
  have hdC : d ∈ D ⊓ (V ⊔ Q) := by
    refine ⟨hd, ?_⟩
    have : d = v * q⁻¹ := by rw [hdq]; group
    rw [this]
    exact Subgroup.mul_mem_sup hvV (Q.inv_mem hq)
  rw [hdq]
  exact Subgroup.mul_mem_sup hdC hq

private theorem le_normalizer (h : Sec11cProj G z D Q V) : V ≤ Subgroup.normalizer Q := by
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro q
  refine ⟨fun hq => h.V_normQ v hv q hq, fun hq => ?_⟩
  have h2 := h.V_normQ v⁻¹ (V.inv_mem hv) (v * q * v⁻¹) hq
  convert h2 using 1
  group

theorem mem_proj (h : Sec11cProj G z D Q V) {d : G} (hd : d ∈ D ⊓ (V ⊔ Q)) :
    ∃ q ∈ Q, d * q ∈ V := by
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right V Q h.le_normalizer
  have hdmem : d ∈ ((V : Set G) * (Q : Set G) : Set G) := by
    rw [← hcoe]
    exact hd.2
  obtain ⟨v, hv, q, hq, hvq⟩ := Set.mem_mul.mp hdmem
  refine ⟨q⁻¹, Q.inv_mem hq, ?_⟩
  have : d * q⁻¹ = v := by rw [← hvq]; group
  rwa [this]

theorem proj_mono {V' : Subgroup G} (hV' : V' ≤ V) : D ⊓ (V' ⊔ Q) ≤ D ⊓ (V ⊔ Q) :=
  inf_le_inf_left D (sup_le_sup_right hV' Q)

theorem comm (h : Sec11cProj G z D Q V) {g d q : G} (hg : g ∈ V) (hd : d ∈ D) (hq : q ∈ Q)
    (hdq : d * q ∈ V) : g * d * g⁻¹ * d⁻¹ ∈ zpowers z ∧ g * q * g⁻¹ * q⁻¹ ∈ zpowers z := by
  have hd' : g * d * g⁻¹ ∈ D := h.V_normD g hg d hd
  have hq' : g * q * g⁻¹ ∈ Q := h.V_normQ g hg q hq
  have hY : g * q * g⁻¹ * q⁻¹ ∈ Q := Q.mul_mem hq' (Q.inv_mem hq)
  have hcommDQ := h.DQ_comm d⁻¹ (D.inv_mem hd) (g * q * g⁻¹ * q⁻¹) hY
  have hzQ : zpowers z ≤ Q := (le_of_eq h.inf_eq.symm).trans inf_le_right
  have hprod : g * (d * q) * g⁻¹ * (d * q)⁻¹ =
      (g * d * g⁻¹ * d⁻¹) * (g * q * g⁻¹ * q⁻¹) := by
    have e1 : g * (d * q) * g⁻¹ * (d * q)⁻¹ =
        (g * d * g⁻¹) * ((g * q * g⁻¹) * q⁻¹ * d⁻¹) := by group
    have e2 : (g * q * g⁻¹) * q⁻¹ * d⁻¹ = d⁻¹ * ((g * q * g⁻¹) * q⁻¹) :=
      hcommDQ.symm
    rw [e1, e2]
    group
  have hzprod : (g * d * g⁻¹ * d⁻¹) * (g * q * g⁻¹ * q⁻¹) ∈ zpowers z := by
    rw [← hprod]
    exact (h.V_el g hg (d * q) hdq).1
  have hfirst : g * d * g⁻¹ * d⁻¹ ∈ zpowers z := by
    have hmem : g * d * g⁻¹ * d⁻¹ ∈ D ⊓ Q := by
      refine ⟨D.mul_mem hd' (D.inv_mem hd), ?_⟩
      have heq : g * d * g⁻¹ * d⁻¹ =
          ((g * d * g⁻¹ * d⁻¹) * (g * q * g⁻¹ * q⁻¹)) * (g * q * g⁻¹ * q⁻¹)⁻¹ := by
        group
      rw [heq]
      exact Q.mul_mem (hzQ hzprod) (Q.inv_mem hY)
    rwa [h.inf_eq] at hmem
  refine ⟨hfirst, ?_⟩
  have heq : g * q * g⁻¹ * q⁻¹ =
      (g * d * g⁻¹ * d⁻¹)⁻¹ * ((g * d * g⁻¹ * d⁻¹) * (g * q * g⁻¹ * q⁻¹)) := by
    group
  rw [heq]
  exact (zpowers z).mul_mem ((zpowers z).inv_mem hfirst) hzprod

theorem cent (h : Sec11cProj G z D Q V) {g : G} (hg : g ∈ V) :
    ∀ d ∈ D ⊓ (V ⊔ Q), g * d * g⁻¹ * d⁻¹ ∈ zpowers z := by
  intro d hd
  obtain ⟨q, hq, hdq⟩ := h.mem_proj hd
  exact (h.comm hg hd.1 hq hdq).1

theorem elemAb (h : Sec11cProj G z D Q V) : IsElemAbelianMod z (D ⊓ (V ⊔ Q)) := by
  intro a ha b hb
  obtain ⟨qa, hqa, hdqa⟩ := h.mem_proj ha
  obtain ⟨qb, hqb, hdqb⟩ := h.mem_proj hb
  have hcomm := h.comm hdqb ha.1 hqa hdqa
  refine ⟨?_, ?_⟩
  · have hba : b * a * b⁻¹ * a⁻¹ ∈ zpowers z := by
      have heq : (b * qb) * a * (b * qb)⁻¹ * a⁻¹ = b * a * b⁻¹ * a⁻¹ := by
        calc (b * qb) * a * (b * qb)⁻¹ * a⁻¹
            = b * (qb * a) * qb⁻¹ * b⁻¹ * a⁻¹ := by group
          _ = b * (a * qb) * qb⁻¹ * b⁻¹ * a⁻¹ := by rw [← h.DQ_comm a ha.1 qb hqb]
          _ = b * a * b⁻¹ * a⁻¹ := by group
      rw [← heq]
      exact hcomm.1
    have heq2 : a * b * a⁻¹ * b⁻¹ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by group
    rw [heq2]
    exact (zpowers z).inv_mem hba
  · have hsq : (a * qa) * (a * qa) ∈ zpowers z := (h.V_el (a * qa) hdqa (a * qa) hdqa).2
    have hqsq : qa * qa ∈ zpowers z := (h.Q_el qa hqa qa hqa).2
    have heq : (a * qa) * (a * qa) = (a * a) * (qa * qa) := by
      calc (a * qa) * (a * qa) = a * (qa * a) * qa := by group
        _ = a * (a * qa) * qa := by rw [← h.DQ_comm a ha.1 qa hqa]
        _ = (a * a) * (qa * qa) := by group
    have h1 : (a * a) * (qa * qa) ∈ zpowers z := by rw [← heq]; exact hsq
    have heq2 : a * a = ((a * a) * (qa * qa)) * (qa * qa)⁻¹ := by group
    rw [heq2]
    exact (zpowers z).mul_mem h1 ((zpowers z).inv_mem hqsq)

theorem inf_le (h : Sec11cProj G z D Q V) {g : G} (hg : g ∈ V) :
    V ⊓ (D ⊔ Q) ≤ D ⊓ (V ⊔ Q) ⊔ sec11Qg z g Q := by
  refine (h.le_Csup.trans ?_)
  exact sec11_inf_le_CQg (z := z) (g := g) (C := D ⊓ (V ⊔ Q)) (Q := Q) (V := V)
    (h.cent hg) (h.V_normQ g hg) (fun c hc q hq => h.DQ_comm c hc.1 q hq) h.Q_z hg h.V_el

theorem inf_le_pair (h : Sec11cProj G z D Q V) {g1 g2 : G} (hg1 : g1 ∈ V) (hg2 : g2 ∈ V) :
    V ⊓ (D ⊔ Q) ≤ D ⊓ (V ⊔ Q) ⊔ (sec11Qg z g1 Q ⊓ sec11Qg z g2 Q) := by
  refine (h.le_Csup.trans ?_)
  exact sec11_inf_le_CQg_pair (z := z) (g1 := g1) (g2 := g2) (C := D ⊓ (V ⊔ Q))
    (Q := Q) (V := V) (h.cent hg1) (h.V_normQ g1 hg1) (h.cent hg2) (h.V_normQ g2 hg2)
    (fun c hc q hq => h.DQ_comm c hc.1 q hq) h.Q_z hg1 hg2 h.V_el

theorem count [Finite G] (h : Sec11cProj G z D Q V) (hz2 : z * z = 1) (hz1 : z ≠ 1) {g : G}
    (hg : g ∈ V) :
    2 * Nat.card ↥(V ⊓ (D ⊔ Q)) ≤ Nat.card ↥(D ⊓ (V ⊔ Q)) * Nat.card ↥(sec11Qg z g Q) := by
  have hgz : g * z = z * g := h.V_z g hg
  have hinf : (D ⊓ (V ⊔ Q)) ⊓ sec11Qg z g Q = zpowers z := by
    apply le_antisymm
    · calc (D ⊓ (V ⊔ Q)) ⊓ sec11Qg z g Q ≤ (D ⊓ (V ⊔ Q)) ⊓ Q :=
          inf_le_inf le_rfl (sec11Qg_le z g Q)
        _ ≤ D ⊓ Q := inf_le_inf inf_le_left le_rfl
        _ = zpowers z := h.inf_eq
    · exact Subgroup.zpowers_le_of_mem
        ⟨⟨h.z_memD, Subgroup.mem_sup_right h.z_memQ⟩, sec11_z_mem_Qg h.z_memQ hgz⟩
  exact sec11_two_mul_card_le (C := D ⊓ (V ⊔ Q)) (Q' := sec11Qg z g Q)
    (H := V ⊓ (D ⊔ Q)) (fun c hc q hq => h.DQ_comm c hc.1 q (sec11Qg_le z g Q hq))
    hinf hz2 hz1 (h.inf_le hg)

theorem count_pair [Finite G] (h : Sec11cProj G z D Q V) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    {g1 g2 : G} (hg1 : g1 ∈ V) (hg2 : g2 ∈ V) :
    2 * Nat.card ↥(V ⊓ (D ⊔ Q)) ≤
      Nat.card ↥(D ⊓ (V ⊔ Q)) * Nat.card ↥(sec11Qg z g1 Q ⊓ sec11Qg z g2 Q) := by
  have hg1z : g1 * z = z * g1 := h.V_z g1 hg1
  have hg2z : g2 * z = z * g2 := h.V_z g2 hg2
  have hinf : (D ⊓ (V ⊔ Q)) ⊓ (sec11Qg z g1 Q ⊓ sec11Qg z g2 Q) = zpowers z := by
    apply le_antisymm
    · calc (D ⊓ (V ⊔ Q)) ⊓ (sec11Qg z g1 Q ⊓ sec11Qg z g2 Q)
          ≤ (D ⊓ (V ⊔ Q)) ⊓ Q :=
          inf_le_inf le_rfl (inf_le_left.trans (sec11Qg_le z g1 Q))
        _ ≤ D ⊓ Q := inf_le_inf inf_le_left le_rfl
        _ = zpowers z := h.inf_eq
    · exact Subgroup.zpowers_le_of_mem
        ⟨⟨h.z_memD, Subgroup.mem_sup_right h.z_memQ⟩,
          sec11_z_mem_Qg h.z_memQ hg1z, sec11_z_mem_Qg h.z_memQ hg2z⟩
  exact sec11_two_mul_card_le (C := D ⊓ (V ⊔ Q))
    (Q' := sec11Qg z g1 Q ⊓ sec11Qg z g2 Q) (H := V ⊓ (D ⊔ Q))
    (fun c hc q hq => h.DQ_comm c hc.1 q (sec11Qg_le z g1 Q hq.1)) hinf hz2 hz1
    (h.inf_le_pair hg1 hg2)

theorem card_le_of_le [Finite G] (h : Sec11cProj G z D Q V) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hVDQ : V ≤ D ⊔ Q) : 2 * Nat.card V ≤ Nat.card ↥(D ⊓ (V ⊔ Q)) * Nat.card Q := by
  have hc := h.count hz2 hz1 V.one_mem
  rw [inf_eq_left.mpr hVDQ] at hc
  calc 2 * Nat.card V ≤ Nat.card ↥(D ⊓ (V ⊔ Q)) * Nat.card ↥(sec11Qg z 1 Q) := hc
    _ ≤ Nat.card ↥(D ⊓ (V ⊔ Q)) * Nat.card Q :=
        Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (sec11Qg_le z 1 Q))

end Sec11cProj

end CFSG.OddStandard.SmallF3.Omega
