module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abT2c

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv

namespace KD8ab

open KD7

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace GData

variable (G : GData S T₁)

theorem act₁ : G.D₁.act = .one := act_one_of_abelian (F := frame₁ S) G.D₁ G.hq₁

theorem act₂ : G.D₂.act = .one := act_one_of_abelian (F := frame₂ S) G.D₂ G.hq₂

include G in
theorem d_mem_T₁ : C.d ∈ T₁ := G.D₁.T₁_eq.symm.le (mem_sup_left (mem_sup_left C.d_mem))

include G in
theorem d_conj_k : C.d * S.k * C.d⁻¹ = S.z * S.k := by
  rcases conj_k_of_ψ S C.d_mem (SDKD.ψX_d C) with h | h
  · exact h
  · exfalso
    have hk : ¬ ConjTo t S.k :=
      not_conjTo_of_mem_E0 (F := frame₁ S) G.D₁ G.act₁ (frame₁ S).kF_mem_E0
    apply hk
    obtain ⟨g, -, -, hg⟩ := exists_conj_t_mul (F := frame₂ S) G.D₂ G.act₂
      (frame₂ S).kF_mem_E0
    refine ⟨C.d⁻¹ * g, ?_⟩
    have hzkt : S.z * C.k * t = t * (S.z * S.k) := by
      rw [mul_assoc, show C.k * t = t * C.k from A.commute_t C.k_mem, ← mul_assoc,
        show S.z * t = t * S.z from A.commute_t (z_mem_T S), mul_assoc]; rfl
    calc C.d⁻¹ * g * t * (C.d⁻¹ * g)⁻¹ = C.d⁻¹ * (g * t * g⁻¹) * C.d := by group
      _ = C.d⁻¹ * (C.d * C.k * C.d⁻¹) * C.d := by rw [hg, h, hzkt]; rfl
      _ = S.k := by group; rfl

include G in
theorem d_inv_conj_k : C.d⁻¹ * S.k * C.d = S.z * S.k := by
  have h := d_conj_k G
  have h1 : C.d⁻¹ * (C.d * S.k * C.d⁻¹) * C.d = S.k := by group
  rw [h] at h1
  have h2 : C.d⁻¹ * (S.z * S.k) * C.d = (C.d⁻¹ * S.z * C.d) * (C.d⁻¹ * S.k * C.d) := by group
  rw [h2, d_inv_conj_z S] at h1
  calc C.d⁻¹ * S.k * C.d = S.z⁻¹ * (S.z * (C.d⁻¹ * S.k * C.d)) := by group
    _ = S.z * S.k := by rw [h1, z_inv S]

theorem w₁c_facts : G.V₁.w₁c ∈ T₁ ∧ G.V₁.w₁c * t * G.V₁.w₁c⁻¹ = t * S.z ∧
    G.V₁.w₁c * S.z * G.V₁.w₁c⁻¹ = S.z ∧ G.V₁.w₁c * S.k * G.V₁.w₁c⁻¹ = S.k ∧
    G.V₁.w₁c * S.y * G.V₁.w₁c⁻¹ = S.y ∧
    G.V₁.w₁c * (S.x * S.y) * G.V₁.w₁c⁻¹ = S.x * S.y := by
  refine ⟨G.V₁.w₁c_mem_T₁, G.V₁.w₁c_conj_t, G.V₁.w₁c_conj_E0 G.V₁.z_mem_E0,
    G.V₁.w₁c_conj_E0 G.V₁.ki_mem_E0, G.V₁.w₁c_conj_E0 G.V₁.yi_mem_E0, ?_⟩
  have h := G.V₁.w₁c_comm_u
  rw [show G.V₁.D.u = S.x * S.y from G.hu₁] at h
  rw [← h, mul_inv_cancel_right]

theorem vN_facts : G.V₁.vN ∈ T₁ ∧ G.V₁.vN * t * G.V₁.vN⁻¹ = t * S.k ∧
    G.V₁.vN * S.z * G.V₁.vN⁻¹ = S.z ∧ G.V₁.vN * S.k * G.V₁.vN⁻¹ = S.k ∧
    G.V₁.vN * S.y * G.V₁.vN⁻¹ = S.y ∧
    G.V₁.vN * (S.x * S.y) * G.V₁.vN⁻¹ = S.x * S.y := by
  refine ⟨G.V₁.vN_mem_T₁, G.V₁.vN_conj_t, G.V₁.vN_conj_z, G.V₁.vN_conj_ki, G.V₁.vN_conj_yi, ?_⟩
  have h := G.V₁.u_comm_vN
  rw [show G.V₁.D.u = S.x * S.y from G.hu₁] at h
  rw [← h, mul_inv_cancel_right]

theorem conj_d_inv_of {w : X} (hz : w * S.z * w⁻¹ = S.z) (hy : w * S.y * w⁻¹ = S.y)
    (hxy : w * (S.x * S.y) * w⁻¹ = S.x * S.y) :
    w * (C.d⁻¹ * S.y * C.d) * w⁻¹ = C.d⁻¹ * S.y * C.d ∧
      w * (C.d⁻¹ * (S.x * S.y) * C.d) * w⁻¹ = C.d⁻¹ * (S.x * S.y) * C.d := by
  have hzm : ∀ a, w * a * w⁻¹ = a → w * (S.z * a) * w⁻¹ = S.z * a := fun a ha => by
    rw [show w * (S.z * a) * w⁻¹ = (w * S.z * w⁻¹) * (w * a * w⁻¹) by group, hz, ha]
  constructor
  · rcases d_inv_conj_y S with h | h <;> rw [h]
    · exact hxy
    · exact hzm _ hxy
  · rcases d_inv_conj_xy S with h | h <;> rw [h]
    · exact hzm _ hy
    · exact hy

omit G in
theorem B_calc {c e W : X} (hc : c ∈ S.B) (he : e ∈ S.B) (hW : W ∈ S.B) :
    c * (t * e) * W * (c * t) = W * e := by
  have heW : e * W ∈ S.B := mul_mem he hW
  have hzWc : (e * W) * c = c * (e * W) := B_comm_B S heW hc
  have hzWt : (e * W) * t = t * (e * W) := B_comm_B S heW Frame.t_mem_B
  have hct' : t * c = c * t := B_comm_B S Frame.t_mem_B hc
  have hcc : c * c = 1 := by rw [← pow_two, sq_of_mem_B S hc]
  have hzW' : e * W = W * e := B_comm_B S he hW
  calc c * (t * e) * W * (c * t) = c * t * ((e * W) * c) * t := by group
    _ = c * t * (c * (e * W)) * t := by rw [hzWc]
    _ = c * t * c * ((e * W) * t) := by group
    _ = c * t * c * (t * (e * W)) := by rw [hzWt]
    _ = (c * (t * c) * t) * (e * W) := by group
    _ = (c * (c * t) * t) * (e * W) := by rw [hct']
    _ = (c * c) * (t * t) * (e * W) := by group
    _ = W * e := by rw [hcc, tt (A := A), one_mul, one_mul, hzW']

theorem d_conj_w₁c : ∃ c ∈ (zpowers S.z ⊔ zpowers S.k : Subgroup X),
    C.d * G.V₁.w₁c * C.d⁻¹ = G.V₁.w₁c * c := by
  obtain ⟨hwT, hwt, hwz, hwk, hwy, hwxy⟩ := G.w₁c_facts
  set w := G.V₁.w₁c with hwdef
  have hdT := d_mem_T₁ G
  obtain ⟨hdy, hdxy⟩ := conj_d_inv_of hwz hwy hwxy
  have hwinv : ∀ a, w * a * w⁻¹ = a → w⁻¹ * a * w = a := fun a ha => by
    calc w⁻¹ * a * w = w⁻¹ * (w * a * w⁻¹) * w := by rw [ha]
      _ = a := by group
  set g := w⁻¹ * (C.d * w * C.d⁻¹) with hgdef
  have hconj : ∀ a, g * a * g⁻¹ = w⁻¹ * (C.d * (w * (C.d⁻¹ * a * C.d) * w⁻¹) * C.d⁻¹) * w :=
    fun a => by rw [hgdef]; group
  have hg : g ∈ S.B := by
    refine mem_B_of_fix G.h4 (mul_mem (inv_mem hwT) (mul_mem (mul_mem hdT hwT) (inv_mem hdT)))
      ?_ ?_ ?_ ?_
    · have e1 : C.d * (t * S.z) * C.d⁻¹ = t * S.z := by
        rw [show C.d * (t * S.z) * C.d⁻¹ = (C.d * t * C.d⁻¹) * (C.d * S.z * C.d⁻¹) by group,
          d_conj_t, d_conj_z S]
      rw [hconj, d_inv_conj_t, hwt, e1, ← hwt]
      group
    · have e1 : w * (S.z * S.k) * w⁻¹ = S.z * S.k := by
        rw [show w * (S.z * S.k) * w⁻¹ = (w * S.z * w⁻¹) * (w * S.k * w⁻¹) by group, hwz, hwk]
      have e2 : C.d * (S.z * S.k) * C.d⁻¹ = S.k := by
        rw [show C.d * (S.z * S.k) * C.d⁻¹ = (C.d * S.z * C.d⁻¹) * (C.d * S.k * C.d⁻¹) by group,
          d_conj_z S, d_conj_k G, ← mul_assoc, zz S, one_mul]
      rw [hconj, d_inv_conj_k G, e1, e2, hwinv _ hwk]
    · rw [hconj, hdy, show C.d * (C.d⁻¹ * S.y * C.d) * C.d⁻¹ = S.y by group, hwinv _ hwy]
    · rw [hconj, hdxy, show C.d * (C.d⁻¹ * (S.x * S.y) * C.d) * C.d⁻¹ = S.x * S.y by group,
        hwinv _ hwxy]
  have hd : C.d * w * C.d⁻¹ = w * g := by rw [hgdef]; group
  refine ⟨g, ?_, hd⟩
  rcases G.V₁.mem_B_cases hg with h | h
  · exact h
  · exfalso
    set c := g * t with hcdef
    have hgc : g = c * t := by rw [hcdef, mul_assoc, tt (A := A), mul_one]
    have hcB : c ∈ S.B := G.V₁.zk_le_B h
    have hw2 : w * w ∈ zpowers S.z := by
      rw [← pow_two, hwdef, G.V₁.w₁c_sq]
      rcases G.V₁.hq with hq | hq
      · rw [G.V₁.w₁N_sq_of_elem hq]; exact one_mem _
      · rw [G.V₁.w₁N_sq_of_homoc hq]; exact mem_zpowers _
    have hw2B : w * w ∈ S.B := zpowers_le.mpr Frame.z_mem_B hw2
    have hwc : w * c * w⁻¹ = c := G.V₁.conj_zk_of_fix hwz hwk h
    have hsq1 : C.d * w * C.d⁻¹ * (C.d * w * C.d⁻¹) = w * w := by
      rw [show C.d * w * C.d⁻¹ * (C.d * w * C.d⁻¹) = C.d * (w * w) * C.d⁻¹ by group]
      rcases eq_one_or_eq_of_mem_zpowers (z_sq S) hw2 with h1 | h1 <;> rw [h1]
      · group
      · exact d_conj_z S
    rw [hd, hgc] at hsq1
    have h3 : w * (c * t) * (w * (c * t)) = (w * w) * S.z := by
      calc w * (c * t) * (w * (c * t)) = (w * c * w⁻¹) * (w * t * w⁻¹) * (w * w) * (c * t) := by
            group
        _ = c * (t * S.z) * (w * w) * (c * t) := by rw [hwc, hwt]
        _ = (w * w) * S.z := B_calc hcB Frame.z_mem_B hw2B
    rw [h3] at hsq1
    exact z_ne_one S (mul_eq_left.mp hsq1)

theorem d_conj_vN : ∃ c ∈ (zpowers S.z ⊔ zpowers S.k : Subgroup X),
    C.d * G.V₁.vN * C.d⁻¹ = G.V₁.vN * G.V₁.w₁c * c := by
  obtain ⟨hwT, hwt, hwz, hwk, hwy, hwxy⟩ := G.w₁c_facts
  obtain ⟨hvT, hvt, hvz, hvk, hvy, hvxy⟩ := G.vN_facts
  set w := G.V₁.w₁c with hwdef
  set v := G.V₁.vN with hvdef
  have hdT := d_mem_T₁ G
  obtain ⟨hdy, hdxy⟩ := conj_d_inv_of hvz hvy hvxy
  set n := v * w with hndef
  have hnfix : ∀ a, v * a * v⁻¹ = a → w * a * w⁻¹ = a → n * a * n⁻¹ = a := fun a h1 h2 => by
    rw [hndef, show v * w * a * (v * w)⁻¹ = v * (w * a * w⁻¹) * v⁻¹ by group, h2, h1]
  have hninv : ∀ a, n * a * n⁻¹ = a → n⁻¹ * a * n = a := fun a ha => by
    calc n⁻¹ * a * n = n⁻¹ * (n * a * n⁻¹) * n := by rw [ha]
      _ = a := by group
  have hnt : n * t * n⁻¹ = t * (S.z * S.k) := by
    rw [hndef, show v * w * t * (v * w)⁻¹ = v * (w * t * w⁻¹) * v⁻¹ by group, hwt,
      show v * (t * S.z) * v⁻¹ = (v * t * v⁻¹) * (v * S.z * v⁻¹) by group, hvt, hvz,
      mul_assoc, show S.k * S.z = S.z * S.k from B_comm_B S Frame.k_mem_B Frame.z_mem_B]
  set g := n⁻¹ * (C.d * v * C.d⁻¹) with hgdef
  have hconj : ∀ a, g * a * g⁻¹ = n⁻¹ * (C.d * (v * (C.d⁻¹ * a * C.d) * v⁻¹) * C.d⁻¹) * n :=
    fun a => by rw [hgdef]; group
  have hg : g ∈ S.B := by
    refine mem_B_of_fix G.h4 (mul_mem (inv_mem (mul_mem hvT hwT))
      (mul_mem (mul_mem hdT hvT) (inv_mem hdT))) ?_ ?_ ?_ ?_
    · have e1 : C.d * (t * S.k) * C.d⁻¹ = t * (S.z * S.k) := by
        rw [show C.d * (t * S.k) * C.d⁻¹ = (C.d * t * C.d⁻¹) * (C.d * S.k * C.d⁻¹) by group,
          d_conj_t, d_conj_k G]
      rw [hconj, d_inv_conj_t, hvt, e1, ← hnt]
      group
    · have e1 : v * (S.z * S.k) * v⁻¹ = S.z * S.k := by
        rw [show v * (S.z * S.k) * v⁻¹ = (v * S.z * v⁻¹) * (v * S.k * v⁻¹) by group, hvz, hvk]
      have e2 : C.d * (S.z * S.k) * C.d⁻¹ = S.k := by
        rw [show C.d * (S.z * S.k) * C.d⁻¹ = (C.d * S.z * C.d⁻¹) * (C.d * S.k * C.d⁻¹) by group,
          d_conj_z S, d_conj_k G, ← mul_assoc, zz S, one_mul]
      rw [hconj, d_inv_conj_k G, e1, e2, hninv _ (hnfix _ hvk hwk)]
    · rw [hconj, hdy, show C.d * (C.d⁻¹ * S.y * C.d) * C.d⁻¹ = S.y by group,
        hninv _ (hnfix _ hvy hwy)]
    · rw [hconj, hdxy, show C.d * (C.d⁻¹ * (S.x * S.y) * C.d) * C.d⁻¹ = S.x * S.y by group,
        hninv _ (hnfix _ hvxy hwxy)]
  have hd : C.d * v * C.d⁻¹ = n * g := by rw [hgdef]; group
  refine ⟨g, ?_, hd⟩
  rcases G.V₁.mem_B_cases hg with h | h
  · exact h
  · exfalso
    set c := g * t with hcdef
    have hgc : g = c * t := by rw [hcdef, mul_assoc, tt (A := A), mul_one]
    have hcB : c ∈ S.B := G.V₁.zk_le_B h
    have hn2 : n * n = 1 := by
      have := G.P₁.sq_g
      rwa [pow_two] at this
    have hnc : n * c * n⁻¹ = c := hnfix _ (G.V₁.conj_zk_of_fix hvz hvk h)
      (G.V₁.conj_zk_of_fix hwz hwk h)
    have hsq1 : C.d * v * C.d⁻¹ * (C.d * v * C.d⁻¹) = 1 := by
      rw [show C.d * v * C.d⁻¹ * (C.d * v * C.d⁻¹) = C.d * (v * v) * C.d⁻¹ by group,
        G.V₁.vN_mul_vN, mul_one, mul_inv_cancel]
    rw [hd, hgc] at hsq1
    have h3 : n * (c * t) * (n * (c * t)) = 1 * (S.z * S.k) := by
      calc n * (c * t) * (n * (c * t)) = (n * c * n⁻¹) * (n * t * n⁻¹) * (n * n) * (c * t) := by
            group
        _ = c * (t * (S.z * S.k)) * 1 * (c * t) := by rw [hnc, hnt, hn2]
        _ = 1 * (S.z * S.k) := B_calc hcB (mul_mem Frame.z_mem_B Frame.k_mem_B) (one_mem _)
    rw [h3, one_mul] at hsq1
    exact G.V₁.zk_ne_one hsq1

end GData

end KD8ab

end CFSG.OddStandard.SmallF3.L33.KD
