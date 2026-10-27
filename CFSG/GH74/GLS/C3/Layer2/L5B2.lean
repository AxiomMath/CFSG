module

public import CFSG.GH74.GLS.C3.Layer2.L5B0
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public import CFSG.GH74.GLS.C3.Layer2.L5B2Inputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2Inputs
public import Certificates.Certificate5045
public import Certificates.Certificate5049
public import Certificates.Certificate5091
public import Certificates.Certificate5092

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

structure SPair (α : Amb 5 → Amb 5) (u : Amb 5) : Prop where
  maps : ∀ t ∈ T5, α t ∈ T5
  mul : ∀ s ∈ T5, ∀ t ∈ T5, α (s * t) = α s * α t
  surj : ∀ t ∈ T5, ∃ s ∈ T5, α s = t
  P_Q : ∀ p ∈ Pm, α p ∈ Qm
  Q_P : ∀ q ∈ Qm, α q ∈ Pm
  u_mem : u ∈ T5
  sq : ∀ t ∈ T5, α (α t) = u * t * u⁻¹
  fix : α u = u
  moves : α f1 ≠ f1

theorem SPair.one
    {α : Amb 5 → Amb 5} {u : Amb 5} (h : SPair α u) : α 1 = 1 := by
  have h1 := h.mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h1
  exact mul_left_cancel (a := α 1) (by rw [mul_one]; exact h1.symm)

theorem Wl_cover_chk :
    allT5.all (fun t => Wl.any fun w => decide (evalW gT w = t)) = true :=
  Certificates.certificate5049.1

theorem Wl_cover
    {t : Amb 5} (ht : t ∈ T5) : ∃ w ∈ Wl, evalW gT w = t := by
  have h := Wl_cover_chk
  simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  exact h t (mem_allT5.2 ht)

theorem Rels_chk :
    Rels.all (fun r => decide (evalW gT r = 1)) = true :=
  Certificates.certificate5049.2.1

theorem Rels_eval : ∀ r ∈ Rels, evalW gT r = 1 := by
  have h := Rels_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h

theorem gT_mem_chk :
    T5b (gT 0) = true ∧ T5b (gT 1) = true ∧ T5b (gT 2) = true :=
  Certificates.certificate5049.2.2.1

theorem gT_mem (i : Fin 3) : gT i ∈ T5 := by
  obtain ⟨h0, h1, h2⟩ := gT_mem_chk
  fin_cases i
  · exact mem_T5_of_b h0
  · exact mem_T5_of_b h1
  · exact mem_T5_of_b h2

theorem foldl_hom {M : Type*} [Monoid M] {f : Amb 5 → M}
    (hf : ∀ s ∈ T5, ∀ t ∈ T5, f (s * t) = f s * f t) :
    ∀ (w : List (Fin 3)) (a : Amb 5), a ∈ T5 →
      f (w.foldl (fun a i => a * gT i) a) = w.foldl (fun m i => m * f (gT i)) (f a)
  | [], _, _ => rfl
  | i :: w, a, ha => by
      simp only [List.foldl_cons]
      rw [foldl_hom hf w (a * gT i) (mul_mem ha (gT_mem i)), hf a ha (gT i) (gT_mem i)]

theorem eq_of_gens {M : Type*} [Monoid M] {f f' : Amb 5 → M}
    (hf : ∀ s ∈ T5, ∀ t ∈ T5, f (s * t) = f s * f t)
    (hf' : ∀ s ∈ T5, ∀ t ∈ T5, f' (s * t) = f' s * f' t) (h1 : f 1 = f' 1)
    (h : ∀ i, f (gT i) = f' (gT i)) {t : Amb 5} (ht : t ∈ T5) : f t = f' t := by
  obtain ⟨w, -, rfl⟩ := Wl_cover ht
  unfold evalW
  rw [foldl_hom hf w 1 (one_mem _), foldl_hom hf' w 1 (one_mem _), h1]
  simp only [h]

theorem evalW_hom
    {α : Amb 5 → Amb 5} (hα : ∀ s ∈ T5, ∀ t ∈ T5, α (s * t) = α s * α t)
    (h1 : α 1 = 1) (w : List (Fin 3)) :
    α (evalW gT w) = evalW (fun i => α (gT i)) w := by
  unfold evalW
  rw [foldl_hom hα w 1 (one_mem _), h1]

theorem main27_true : main27 = true :=
  Certificates.certificate5049.2.2.2.1

theorem xChk_of_SPair
    {α : Amb 5 → Amb 5} {u : Amb 5} (h : SPair α u) :
    xChk (fun i => α (gT i)) = true := by
  have hev := evalW_hom h.mul h.one
  simp only [xChk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, imp_eq_true,
    List.any_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    rw [← hev, Rels_eval r hr, h.one]
  · intro w _
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hp
      rw [← hev]
      exact h.P_Q _ (mem_Pm.2 hp)
    · intro hq
      rw [← hev]
      exact h.Q_P _ (mem_Qm.2 hq)
    · intro hf
      rw [← hev, hf]
      exact h.moves
  · intro t ht
    obtain ⟨s, hs, e⟩ := h.surj t (mem_allT5.1 ht)
    obtain ⟨w, hw, rfl⟩ := Wl_cover hs
    exact ⟨_, List.mem_map.2 ⟨w, hw, rfl⟩, by rw [← hev, e]⟩

theorem uChk_of_SPair
    {α : Amb 5 → Amb 5} {u : Amb 5} (h : SPair α u) {w : List (Fin 3)}
    (hw : evalW gT w = u) : uChk (fun i => α (gT i)) w = true := by
  have hev := evalW_hom h.mul h.one
  simp only [uChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true]
  refine ⟨?_, ?_⟩
  · rw [← hev, hw]
    exact h.fix
  · intro i _
    obtain ⟨w', hw', e⟩ := Wl_cover (h.maps _ (gT_mem i))
    refine ⟨w', hw', e, ?_⟩
    rw [← hev, e, hw]
    exact h.sq _ (gT_mem i)

theorem e2_mem_Pm : e2 ∈ Pm := by simp [mem_Pm, Pml]

theorem classify_27_id
    {α : Amb 5 → Amb 5} {u : Amb 5} (h : SPair α u) (hu : u ∈ Rm) :
    ∃ t₀ ∈ T5, (∀ t ∈ T5, emb 5 (α t) =
        emb 5 t₀ * a0perm 5 * emb 5 t * (a0perm 5)⁻¹ * (emb 5 t₀)⁻¹) ∧
      emb 5 u = emb 5 t₀ * a0perm 5 * emb 5 t₀ * a0perm 5 := by
  have hxa : α f2 ∈ Pml := mem_Pm.1 (h.Q_P f2 f2_mem_Qm)
  have hxc : α e2 ∈ Qml := mem_Qm.1 (h.P_Q e2 e2_mem_Pm)
  have hxb : α (swap 2 3, swap 2 3) ∈ allT5 := mem_allT5.2 (h.maps _ (gT_mem 1))
  have hg : (fun i => α (gT i)) = ![α f2, α (swap 2 3, swap 2 3), α e2] := by
    funext i
    fin_cases i <;> rfl
  have hm := main27_true
  simp only [main27, List.all_eq_true] at hm
  have hc : candChk (fun i => α (gT i)) = true := by
    rw [hg]
    exact hm _ hxa _ hxc _ hxb
  obtain ⟨w, hw, hwu⟩ := Wl_cover h.u_mem
  have hX := xChk_of_SPair h
  have hU := uChk_of_SPair h hwu
  have hc2 : (Wl.all fun w => !(decide (evalW gT w ∈ Rml)) || !(uChk (fun i => α (gT i)) w) ||
      allT5.any fun t₀ => gensRel (fun i => α (gT i)) (evalW gT w) t₀) = true := by
    unfold candChk at hc
    rw [hX] at hc
    simpa only [Bool.not_true, Bool.false_or] using hc
  have h3 := List.all_eq_true.1 hc2 w hw
  rw [hwu, decide_eq_true (mem_Rm.1 hu), hU] at h3
  simp only [Bool.not_true, Bool.false_or] at h3
  obtain ⟨t₀, ht₀, hr⟩ := List.any_eq_true.1 h3
  simp only [gensRel, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr
  refine ⟨t₀, mem_allT5.1 ht₀, fun t ht => ?_, hr.1⟩
  refine eq_of_gens (f := fun t => emb 5 (α t))
    (f' := fun t => emb 5 t₀ * a0perm 5 * emb 5 t * (a0perm 5)⁻¹ * (emb 5 t₀)⁻¹) ?_ ?_ ?_ ?_ ht
  · intro s hs t ht
    simp only [h.mul s hs t ht, map_mul]
  · intro s hs t ht
    simp only [map_mul]
    group
  · simp only [h.one, map_one, mul_one]
    group
  · intro i
    exact hr.2 i (List.mem_finRange i)

theorem nm_id_chk :
    allT5.all (fun t => imp (decide (t * t = 1)) (imp (decide (t ≠ 1))
    (decide (nmE t = 8 ↔ (t ∈ Rml ∧ t ∉ Pml ∧ t ∉ Qml))))) = true :=
  Certificates.certificate5049.2.2.2.2.1

theorem nm_id :
    ∀ t ∈ T5, t * t = 1 → t ≠ 1 → (nmE t = 8 ↔ (t ∈ Rm ∧ t ∉ Pm ∧ t ∉ Qm)) := by
  have h := nm_id_chk
  simp only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] at h
  exact fun t ht h1 h2 => h t (mem_allT5.2 ht) h1 h2

theorem isAutOn_id : IsAutOn (id : Amb 5 → Amb 5) :=
  ⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ _ _ h => h, fun q hq => ⟨q, hq, rfl⟩⟩

theorem classify_27
    {α : Amb 5 → Amb 5} {u : Amb 5} (h : SPair α u) (hu : u ∈ Rm) :
    ∃ (b : Amb 5 → Amb 5) (t₀ : Amb 5), IsAutOn b ∧ t₀ ∈ T5 ∧
      (∀ t ∈ T5, emb 5 (b (α t)) =
        emb 5 t₀ * a0perm 5 * emb 5 (b t) * (a0perm 5)⁻¹ * (emb 5 t₀)⁻¹) ∧
      emb 5 (b u) = emb 5 t₀ * a0perm 5 * emb 5 t₀ * a0perm 5 ∧
      (∀ t ∈ T5, t * t = 1 → t ≠ 1 →
        (nmE (b t) = 8 ↔ (t ∈ Rm ∧ t ∉ Pm ∧ t ∉ Qm))) := by
  obtain ⟨t₀, ht₀, h1, h2⟩ := classify_27_id h hu
  exact ⟨id, t₀, isAutOn_id, ht₀, h1, h2, nm_id⟩

theorem a0_conj_PQ_chk : Pml.all (fun p => Qml.any fun q =>
    decide (a0perm 5 * emb 5 p * (a0perm 5)⁻¹ = emb 5 q)) = true :=
  Certificates.certificate5049.2.2.2.2.2.1

theorem a0_conj_QP_chk : Qml.all (fun q => Pml.any fun p =>
    decide (a0perm 5 * emb 5 q * (a0perm 5)⁻¹ = emb 5 p)) = true :=
  Certificates.certificate5049.2.2.2.2.2.2

theorem spair_model :
    ∃ α : Amb 5 → Amb 5, SPair α 1 := by
  classical
  have hn := a0_norm_T5
  let α : Amb 5 → Amb 5 := fun t => if h : t ∈ allT5 then (hn t h).choose else 1
  have hα : ∀ t ∈ T5, α t ∈ T5 ∧ emb 5 (α t) = a0perm 5 * emb 5 t * (a0perm 5)⁻¹ := by
    intro t ht
    have h := (hn t (mem_allT5.2 ht)).choose_spec
    have hdef : α t = (hn t (mem_allT5.2 ht)).choose := dite_eq_left (mem_allT5.2 ht)
    rw [hdef]
    exact ⟨mem_allT5.1 h.1, h.2.symm⟩
  have hmul : ∀ s ∈ T5, ∀ t ∈ T5, α (s * t) = α s * α t := by
    intro s hs t ht
    have h1 := hα (s * t) (mul_mem hs ht)
    have h2 := hα s hs
    have h3 := hα t ht
    apply emb_injective 5
    rw [h1.2, map_mul, map_mul, h2.2, h3.2]
    group
  have hsq : ∀ t ∈ T5, α (α t) = t := by
    intro t ht
    have h1 := hα t ht
    have h2 := hα _ h1.1
    apply emb_injective 5
    rw [h2.2, h1.2]
    calc a0perm 5 * (a0perm 5 * emb 5 t * (a0perm 5)⁻¹) * (a0perm 5)⁻¹
        = (a0perm 5 * a0perm 5) * emb 5 t * ((a0perm 5)⁻¹ * (a0perm 5)⁻¹) := by group
      _ = emb 5 t := by rw [a0_sq, ← mul_inv_rev, a0_sq]; simp
  have hone : α 1 = 1 := by
    have h1 := hα 1 (one_mem _)
    apply emb_injective 5
    rw [h1.2, map_one]
    group
  refine ⟨α, ?_⟩
  exact {
    maps := fun t ht => (hα t ht).1
    mul := hmul
    surj := fun t ht => ⟨α t, (hα t ht).1, hsq t ht⟩
    P_Q := by
      intro p hp
      have h := a0_conj_PQ_chk
      simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h
      obtain ⟨q, hq, hqe⟩ := h p hp
      have : α p = q := by
        apply emb_injective 5
        rw [(hα p (Pm_le_T5 hp)).2, hqe]
      rw [this]
      exact mem_Qm.2 hq
    Q_P := by
      intro q hq
      have h := a0_conj_QP_chk
      simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h
      obtain ⟨p, hp, hpe⟩ := h q hq
      have : α q = p := by
        apply emb_injective 5
        rw [(hα q (Qm_le_T5 hq)).2, hpe]
      rw [this]
      exact mem_Pm.2 hp
    u_mem := one_mem _
    sq := fun t ht => by rw [hsq t ht]; simp
    fix := hone
    moves := by
      have h1 := hα f1 f1_mem_T5
      have : α f1 = e1 := by
        apply emb_injective 5
        rw [h1.2, a0_f1]
      rw [this]
      exact elt_ne'.2.2.2.1 }

end CFSG.GH74.GLS.C3.Layer2.L5
