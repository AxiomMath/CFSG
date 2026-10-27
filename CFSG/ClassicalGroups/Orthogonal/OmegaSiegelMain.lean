module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelAxis
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelGen
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelCost
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelFrame

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.HardMathSupport.Kantor79 CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.RankThree.GF2n.Smith81 QuadraticMap Module

variable {K' : Type*} [Field K'] [CharP K' 2] [Finite K'] {N : Type*} [AddCommGroup N]
  [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N} {K : Type*} [Field K]
  [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Qf : QuadraticForm K V} {ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)}

private def listLine (e f p p' : N) (w : ℕ → N) (k j : ℕ) : N × N :=
  if j < k then (e, w j) else if j = k then (w 0, p) else if j = k + 1 then (f, w 0)
    else if j = k + 2 then (f, p) else if j = k + 3 then (f, p') else (0, 0)

private theorem listLine_lt {e f p p' : N} {w : ℕ → N} {k j : ℕ} (h : j < k) :
    listLine e f p p' w k j = (e, w j) := by
  unfold listLine
  rw [if_pos h]

private theorem listLine_k {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    listLine e f p p' w k k = (w 0, p) := by
  unfold listLine
  split_ifs <;> first | rfl | omega

private theorem listLine_k1 {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    listLine e f p p' w k (k + 1) = (f, w 0) := by
  unfold listLine
  split_ifs <;> first | rfl | omega

private theorem listLine_k2 {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    listLine e f p p' w k (k + 2) = (f, p) := by
  unfold listLine
  split_ifs <;> first | rfl | omega

private theorem listLine_k3 {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    listLine e f p p' w k (k + 3) = (f, p') := by
  unfold listLine
  split_ifs <;> first | rfl | omega

private theorem listLine_ge {e f p p' : N} {w : ℕ → N} {k j : ℕ} (h : k + 4 ≤ j) :
    listLine e f p p' w k j = (0, 0) := by
  unfold listLine
  split_ifs <;> first | rfl | omega

private noncomputable def lineAxis (ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)) (e f p p' : N)
    (w : ℕ → N) (k j : ℕ) : Submodule K V :=
  movedSpace (rhoE ρ (listLine e f p p' w k j).1 (listLine e f p p' w k j).2)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem lineAxis_lt {e f p p' : N} {w : ℕ → N} {k j : ℕ} (h : j < k) :
    lineAxis ρ e f p p' w k j = movedSpace (rhoE ρ e (w j)) := by
  unfold lineAxis
  rw [listLine_lt h]

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem lineAxis_k {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    lineAxis ρ e f p p' w k k = movedSpace (rhoE ρ (w 0) p) := by
  unfold lineAxis
  rw [listLine_k]

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem lineAxis_k1 {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    lineAxis ρ e f p p' w k (k + 1) = movedSpace (rhoE ρ f (w 0)) := by
  unfold lineAxis
  rw [listLine_k1]

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem lineAxis_k2 {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    lineAxis ρ e f p p' w k (k + 2) = movedSpace (rhoE ρ f p) := by
  unfold lineAxis
  rw [listLine_k2]

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem lineAxis_k3 {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    lineAxis ρ e f p p' w k (k + 3) = movedSpace (rhoE ρ f p') := by
  unfold lineAxis
  rw [listLine_k3]

omit [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem movedSpace_one_bot : movedSpace (1 : V ≃ₗ[K] V) = ⊥ := by
  unfold movedSpace
  rw [LinearMap.range_eq_bot]
  ext v
  simp

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem lineAxis_ge {e f p p' : N} {w : ℕ → N} {k j : ℕ} (h : k + 4 ≤ j) :
    lineAxis ρ e f p p' w k j = ⊥ := by
  unfold lineAxis
  rw [listLine_ge h]
  show movedSpace (rhoE ρ 0 0) = ⊥
  rw [rhoE_zero_right]
  exact movedSpace_one_bot

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem li_e_of {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ} (hs : OmegaSetting QN Qf ρ)
    (hF : IsListFrame QN e f p p' w k j₁) {x : N} (hx : x ≠ 0) (hxf : polar QN f x = 0) :
    LinearIndependent K' ![e, x] := by
  obtain ⟨z, hz⟩ := exists_polar_ne_zero hs.ndN hx
  refine linearIndependent_pair_of_polar (z₁ := f) (z₂ := z) ?_ ?_ hz
  · rw [hF.ef]; exact one_ne_zero
  · rw [polar_comm QN x f, hxf]

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem li_w0_p {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![w 0, p] :=
  linearIndependent_pair_of_polar (z₁ := w j₁) (z₂ := p') (by rw [hF.hyp]; exact one_ne_zero)
    (hF.w_p j₁ hF.j₁_lt) (by rw [hF.pp']; exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem li_w0_e {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![w 0, e] :=
  linearIndependent_pair_of_polar (z₁ := w j₁) (z₂ := f) (by rw [hF.hyp]; exact one_ne_zero)
    (hF.w_e j₁ hF.j₁_lt) (by rw [hF.ef]; exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem li_w0_f {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![w 0, f] :=
  linearIndependent_pair_of_polar (z₁ := w j₁) (z₂ := e) (by rw [hF.hyp]; exact one_ne_zero)
    (hF.w_f j₁ hF.j₁_lt) (by rw [polar_comm QN f e, hF.ef]; exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem li_w0_pe {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![w 0, p + e] :=
  linearIndependent_pair_of_polar (z₁ := w j₁) (z₂ := p') (by rw [hF.hyp]; exact one_ne_zero)
    (by rw [polar_add_left, hF.w_p j₁ hF.j₁_lt, hF.w_e j₁ hF.j₁_lt, add_zero])
    (by rw [polar_add_left, hF.pp', hF.ep', add_zero]; exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem li_w0_fp {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![w 0, f + p] :=
  linearIndependent_pair_of_polar (z₁ := w j₁) (z₂ := e) (by rw [hF.hyp]; exact one_ne_zero)
    (by rw [polar_add_left, hF.w_f j₁ hF.j₁_lt, hF.w_p j₁ hF.j₁_lt, add_zero])
    (by
      rw [polar_add_left, polar_comm QN f e, hF.ef, polar_comm QN p e, hF.ep, add_zero]
      exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem li_f_w0 {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![f, w 0] :=
  linearIndependent_pair_of_polar (z₁ := e) (z₂ := w j₁)
    (by rw [polar_comm QN f e, hF.ef]; exact one_ne_zero)
    (by rw [polar_comm QN (w 0) e, hF.w_e 0 hF.pos]) (by rw [hF.hyp]; exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem li_f_p {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![f, p] :=
  linearIndependent_pair_of_polar (z₁ := e) (z₂ := p')
    (by rw [polar_comm QN f e, hF.ef]; exact one_ne_zero)
    (by rw [polar_comm QN p e, hF.ep]) (by rw [hF.pp']; exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem li_f_p' {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![f, p'] :=
  linearIndependent_pair_of_polar (z₁ := e) (z₂ := p)
    (by rw [polar_comm QN f e, hF.ef]; exact one_ne_zero)
    (by rw [polar_comm QN p' e, hF.ep']) (by rw [polar_comm QN p' p, hF.pp']; exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem li_f_w0p {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![f, w 0 + p] :=
  linearIndependent_pair_of_polar (z₁ := e) (z₂ := p')
    (by rw [polar_comm QN f e, hF.ef]; exact one_ne_zero)
    (by
      rw [polar_add_left, polar_comm QN (w 0) e, hF.w_e 0 hF.pos, polar_comm QN p e, hF.ep,
        add_zero])
    (by
      rw [polar_add_left, polar_comm QN (w 0) p', hF.w_p' 0 hF.pos, hF.pp', zero_add]
      exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem li_f_w0p' {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![f, w 0 + p'] :=
  linearIndependent_pair_of_polar (z₁ := e) (z₂ := p)
    (by rw [polar_comm QN f e, hF.ef]; exact one_ne_zero)
    (by
      rw [polar_add_left, polar_comm QN (w 0) e, hF.w_e 0 hF.pos, polar_comm QN p' e, hF.ep',
        add_zero])
    (by
      rw [polar_add_left, polar_comm QN (w 0) p, hF.w_p 0 hF.pos, polar_comm QN p' p, hF.pp',
        zero_add]
      exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem listLine_spec {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ} (hs : OmegaSetting QN Qf ρ)
    (hF : IsListFrame QN e f p p' w k j₁) {j : ℕ} (hj : j < k + 4) :
    QN (listLine e f p p' w k j).1 = 0 ∧ QN (listLine e f p p' w k j).2 = 0 ∧
      polar QN (listLine e f p p' w k j).1 (listLine e f p p' w k j).2 = 0 ∧
      LinearIndependent K' ![(listLine e f p p' w k j).1, (listLine e f p p' w k j).2] := by
  rcases (show j < k ∨ j = k ∨ j = k + 1 ∨ j = k + 2 ∨ j = k + 3 by omega) with
    h | h | h | h | h
  · rw [listLine_lt h]
    exact ⟨hF.e_sing, hF.w_sing j h, hF.w_e j h, li_e_of hs hF (hF.w_ne j h) (hF.w_f j h)⟩
  · rw [h, listLine_k]
    exact ⟨hF.w_sing 0 hF.pos, hF.p_sing, (polar_comm QN (w 0) p).trans (hF.w_p 0 hF.pos),
      li_w0_p hF⟩
  · rw [h, listLine_k1]
    exact ⟨hF.f_sing, hF.w_sing 0 hF.pos, hF.w_f 0 hF.pos, li_f_w0 hF⟩
  · rw [h, listLine_k2]
    exact ⟨hF.f_sing, hF.p_sing, hF.fp, li_f_p hF⟩
  · rw [h, listLine_k3]
    exact ⟨hF.f_sing, hF.p'_sing, hF.fp', li_f_p' hF⟩

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem listLine_wit {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) {j : ℕ} (hj : j < k + 4) :
    ∃ b c : N, QN b = 0 ∧ QN c = 0 ∧
      polar QN (listLine e f p p' w k j).1 b = 0 ∧ polar QN (listLine e f p p' w k j).2 b = 0 ∧
      polar QN (listLine e f p p' w k j).1 c = 0 ∧ polar QN (listLine e f p p' w k j).2 c = 0 ∧
      polar QN b c = 1 := by
  rcases (show j < k ∨ j = k ∨ j = k + 1 ∨ j = k + 2 ∨ j = k + 3 by omega) with
    h | h | h | h | h
  · rw [listLine_lt h]
    exact ⟨p, p', hF.p_sing, hF.p'_sing, hF.ep, (polar_comm QN (w j) p).trans (hF.w_p j h),
      hF.ep', (polar_comm QN (w j) p').trans (hF.w_p' j h), hF.pp'⟩
  · rw [h, listLine_k]
    exact ⟨e, f, hF.e_sing, hF.f_sing, (polar_comm QN (w 0) e).trans (hF.w_e 0 hF.pos),
      (polar_comm QN p e).trans hF.ep, (polar_comm QN (w 0) f).trans (hF.w_f 0 hF.pos),
      (polar_comm QN p f).trans hF.fp, hF.ef⟩
  · rw [h, listLine_k1]
    exact ⟨p, p', hF.p_sing, hF.p'_sing, hF.fp, (polar_comm QN (w 0) p).trans (hF.w_p 0 hF.pos),
      hF.fp', (polar_comm QN (w 0) p').trans (hF.w_p' 0 hF.pos), hF.pp'⟩
  · rw [h, listLine_k2]
    exact ⟨w 0, w j₁, hF.w_sing 0 hF.pos, hF.w_sing j₁ hF.j₁_lt, hF.w_f 0 hF.pos,
      hF.w_p 0 hF.pos, hF.w_f j₁ hF.j₁_lt, hF.w_p j₁ hF.j₁_lt, hF.hyp⟩
  · rw [h, listLine_k3]
    exact ⟨w 0, w j₁, hF.w_sing 0 hF.pos, hF.w_sing j₁ hF.j₁_lt, hF.w_f 0 hF.pos,
      hF.w_p' 0 hF.pos, hF.w_f j₁ hF.j₁_lt, hF.w_p' j₁ hF.j₁_lt, hF.hyp⟩

private theorem lineAxis_smul_le (hs : OmegaSetting QN Qf ρ)
    {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ} (hF : IsListFrame QN e f p p' w k j₁) (i : ℕ)
    (μ : K') : movedSpace (rhoE ρ (listLine e f p p' w k i).1 (μ • (listLine e f p p' w k i).2)) ≤
      lineAxis ρ e f p p' w k i := by
  by_cases hi : i < k + 4
  · obtain ⟨ha, hd, had, hli⟩ := listLine_spec hs hF hi
    obtain ⟨b, c, hb, hc, hab, hdb, hac, hdc, hbc⟩ := listLine_wit hF hi
    unfold lineAxis
    exact hs.movedSpace_rhoE_smul_le ha hd hb hc had hab hdb hac hdc hbc hli μ
  · unfold lineAxis
    rw [listLine_ge (by omega : k + 4 ≤ i)]
    simp

omit [Finite K'] [Finite K] in
private theorem lineAxis_rank (hs : OmegaSetting QN Qf ρ) {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) {j : ℕ} (hj : j < k + 4) :
    finrank K ↥(lineAxis ρ e f p p' w k j) ≤ 2 := by
  obtain ⟨ha, hd, had, hli⟩ := listLine_spec hs hF hj
  unfold lineAxis
  exact (hs.isLongRootElement_rhoE ha hd had hli).finrank_movedSpace_le_two

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem ov_cert {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ} (hs : OmegaSetting QN Qf ρ)
    (hF : IsListFrame QN e f p p' w k j₁) {i j : ℕ} (hi : i < k) (hj : j < k)
    (hperp : polar QN (w i) (w j) = 0) (hne : w i + w j ≠ 0) :
    lineAxis ρ e f p p' w k j ⊓ lineAxis ρ e f p p' w k i ≠ ⊥ := by
  rw [lineAxis_lt hj, lineAxis_lt hi, inf_comm]
  have hfsum : polar QN f (w i + w j) = 0 := by
    rw [polar_add_right, hF.w_f i hi, hF.w_f j hj, add_zero]
  exact hs.movedSpace_rhoE_inf_ne_bot hF.e_sing (hF.w_sing i hi) (hF.w_sing j hj)
    (hF.w_e i hi) (hF.w_e j hj) hperp (li_e_of hs hF (hF.w_ne i hi) (hF.w_f i hi))
    (li_e_of hs hF (hF.w_ne j hj) (hF.w_f j hj)) (li_e_of hs hF hne hfsum)

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem ov_k {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ} (hs : OmegaSetting QN Qf ρ)
    (hF : IsListFrame QN e f p p' w k j₁) :
    lineAxis ρ e f p p' w k k ⊓ lineAxis ρ e f p p' w k 0 ≠ ⊥ := by
  rw [lineAxis_k, lineAxis_lt hF.pos, rhoE_comm hF.e_sing (hF.w_sing 0 hF.pos) (hF.w_e 0 hF.pos)]
  exact hs.movedSpace_rhoE_inf_ne_bot (hF.w_sing 0 hF.pos) hF.p_sing hF.e_sing
    ((polar_comm QN (w 0) p).trans (hF.w_p 0 hF.pos))
    ((polar_comm QN (w 0) e).trans (hF.w_e 0 hF.pos))
    ((polar_comm QN p e).trans hF.ep) (li_w0_p hF) (li_w0_e hF) (li_w0_pe hF)

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem ov_k1 {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ} (hs : OmegaSetting QN Qf ρ)
    (hF : IsListFrame QN e f p p' w k j₁) :
    lineAxis ρ e f p p' w k (k + 1) ⊓ lineAxis ρ e f p p' w k k ≠ ⊥ := by
  rw [lineAxis_k1, lineAxis_k, rhoE_comm hF.f_sing (hF.w_sing 0 hF.pos) (hF.w_f 0 hF.pos)]
  exact hs.movedSpace_rhoE_inf_ne_bot (hF.w_sing 0 hF.pos) hF.f_sing hF.p_sing
    ((polar_comm QN (w 0) f).trans (hF.w_f 0 hF.pos))
    ((polar_comm QN (w 0) p).trans (hF.w_p 0 hF.pos)) hF.fp
    (li_w0_f hF) (li_w0_p hF) (li_w0_fp hF)

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem ov_k2 {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ} (hs : OmegaSetting QN Qf ρ)
    (hF : IsListFrame QN e f p p' w k j₁) :
    lineAxis ρ e f p p' w k (k + 2) ⊓ lineAxis ρ e f p p' w k (k + 1) ≠ ⊥ := by
  rw [lineAxis_k2, lineAxis_k1, inf_comm]
  exact hs.movedSpace_rhoE_inf_ne_bot hF.f_sing (hF.w_sing 0 hF.pos) hF.p_sing
    (hF.w_f 0 hF.pos) hF.fp ((polar_comm QN (w 0) p).trans (hF.w_p 0 hF.pos))
    (li_f_w0 hF) (li_f_p hF) (li_f_w0p hF)

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem ov_k3 {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ} (hs : OmegaSetting QN Qf ρ)
    (hF : IsListFrame QN e f p p' w k j₁) :
    lineAxis ρ e f p p' w k (k + 3) ⊓ lineAxis ρ e f p p' w k (k + 1) ≠ ⊥ := by
  rw [lineAxis_k3, lineAxis_k1, inf_comm]
  exact hs.movedSpace_rhoE_inf_ne_bot hF.f_sing (hF.w_sing 0 hF.pos) hF.p'_sing
    (hF.w_f 0 hF.pos) hF.fp' ((polar_comm QN (w 0) p').trans (hF.w_p' 0 hF.pos))
    (li_f_w0 hF) (li_f_p' hF) (li_f_w0p' hF)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem eichler_mem_span {e : N} {w : ℕ → N} {k : ℕ} {Y : Subgroup (N ≃ₗ[K'] N)}
    (hwe : ∀ j < k, polar QN e (w j) = 0) (hY : ∀ j < k, ∀ c : K', eichler QN e (c • w j) ∈ Y) :
    ∀ x ∈ Submodule.span K' (w '' Set.Iio k),
      polar QN e x = 0 ∧ ∀ c : K', eichler QN e (c • x) ∈ Y := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact ⟨hwe j hj, fun c => hY j hj c⟩
  | zero =>
    refine ⟨by rw [polar_zero_right], fun c => ?_⟩
    rw [smul_zero, eichler_zero_right]
    exact Y.one_mem
  | add x y hx hy ihx ihy =>
    have h1 : ∀ c : K', polar QN e (c • x) = 0 := fun c => by
      rw [polar_smul_right_eq, ihx.1, mul_zero]
    have h2 : ∀ c : K', polar QN e (c • y) = 0 := fun c => by
      rw [polar_smul_right_eq, ihy.1, mul_zero]
    refine ⟨by rw [polar_add_right, ihx.1, ihy.1, add_zero], fun c => ?_⟩
    rw [smul_add, ← eichler_mul (h1 c) (h2 c)]
    exact Y.mul_mem (ihx.2 c) (ihy.2 c)
  | smul a x hx ih =>
    refine ⟨by rw [polar_smul_right_eq, ih.1, mul_zero], fun c => ?_⟩
    rw [← mul_smul]
    exact ih.2 (c * a)

omit [CharP K 2] [Finite K] [FiniteDimensional K V] [Finite K'] [FiniteDimensional K' N] in
private theorem elementaryGroup_le_of_lines (hs : OmegaSetting QN Qf ρ)
    {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ} (hF : IsListFrame QN e f p p' w k j₁)
    {Y : Subgroup (N ≃ₗ[K'] N)}
    (hY : ∀ i : ℕ, ∀ c : K',
      eichler QN (listLine e f p p' w k i).1 (c • (listLine e f p p' w k i).2) ∈ Y) :
    elementaryGroup QN ≤ Y := by
  have hYl : ∀ j < k, ∀ c : K', eichler QN e (c • w j) ∈ Y := by
    intro j hj c
    simpa [listLine_lt hj] using hY j c
  refine elementaryGroup_le_of_frame (fun x hx => eq_zero_of_polar_eq_zero hs.ndN hx)
    hF.e_sing hF.f_sing hF.p_sing hF.p'_sing (hF.w_sing 0 hF.pos) (hF.w_sing j₁ hF.j₁_lt)
    hF.ef hF.pp' hF.hyp hF.ep hF.ep' hF.fp hF.fp' (hF.w_e 0 hF.pos) (hF.w_f 0 hF.pos)
    (hF.w_p 0 hF.pos) (hF.w_p' 0 hF.pos) (hF.w_e j₁ hF.j₁_lt) (hF.w_f j₁ hF.j₁_lt)
    (hF.w_p j₁ hF.j₁_lt) (hF.w_p' j₁ hF.j₁_lt) ?_ ?_ ?_
  · intro x hxe hxf hxp hxp'
    simpa using (eichler_mem_span (fun j hj => hF.w_e j hj) hYl x
      (hF.span x hxe hxf hxp hxp')).2 1
  · intro c
    simpa [listLine_k2] using hY (k + 2) c
  · intro c
    simpa [listLine_k3] using hY (k + 3) c

omit [CharP K 2] [Finite K] in
private theorem cost_step {A : ℕ → Submodule K V} {k : ℕ} (C : Finset ℕ) (hk : 0 < k)
    (hrank : ∀ j < k + 4, finrank K ↥(A j) ≤ 2)
    (hbot : ∀ j, k + 4 ≤ j → A j = ⊥) (hcert : ∀ j ∈ C, ∃ i < j, A j ⊓ A i ≠ ⊥)
    (h₀ : A k ⊓ A 0 ≠ ⊥) (h₁ : A (k + 1) ⊓ A k ≠ ⊥) (h₂ : A (k + 2) ⊓ A (k + 1) ≠ ⊥)
    (h₃ : A (k + 3) ⊓ A (k + 1) ≠ ⊥) (j : ℕ) :
    finrank K ↥(A j ⊔ ⨆ i < j, A i) ≤
      finrank K ↥(⨆ i < j, A i) + (if j ∈ C ∪ Finset.Ico k (k + 4) then 1 else 2) := by
  have hle : ∀ i n : ℕ, i < n → A i ≤ ⨆ i' < n, A i' := fun i n hi =>
    le_iSup₂ (f := fun i' (_ : i' < n) => A i') i hi
  by_cases hbig : k + 4 ≤ j
  · rw [hbot j hbig, bot_sup_eq]
    exact Nat.le_add_right _ _
  rcases Nat.lt_or_ge j k with hjk | hjk
  · by_cases hjC : j ∈ C
    · obtain ⟨i, hi, hov⟩ := hcert j hjC
      rw [if_pos (Finset.mem_union_left _ hjC)]
      exact finrank_sup_le_add_one (hrank j (by omega)) (hle i j hi) hov
    · have hnot : j ∉ C ∪ Finset.Ico k (k + 4) := by
        intro h
        rcases Finset.mem_union.mp h with h | h
        · exact hjC h
        · exact absurd (Finset.mem_Ico.mp h).1 (by omega)
      rw [if_neg hnot]
      exact finrank_sup_le_add_two (hrank j (by omega))
  · rw [if_pos (Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨hjk, by omega⟩))]
    rcases (show j = k ∨ j = k + 1 ∨ j = k + 2 ∨ j = k + 3 by omega) with h | h | h | h <;>
      rw [h]
    · exact finrank_sup_le_add_one (hrank k (by omega)) (hle 0 k hk) h₀
    · exact finrank_sup_le_add_one (hrank (k + 1) (by omega)) (hle k (k + 1) (by omega)) h₁
    · exact finrank_sup_le_add_one (hrank (k + 2) (by omega)) (hle (k + 1) (k + 2) (by omega)) h₂
    · exact finrank_sup_le_add_one (hrank (k + 3) (by omega)) (hle (k + 1) (k + 3) (by omega)) h₃

private theorem sum_cost_le (k : ℕ) (C : Finset ℕ) (hC : ∀ j ∈ C, 0 < j ∧ j < k) :
    ∑ j ∈ Finset.range (k + 4), (if j ∈ C ∪ Finset.Ico k (k + 4) then 1 else 2) + C.card ≤
      2 * k + 4 := by
  have hsub : C ∪ Finset.Ico k (k + 4) ⊆ Finset.range (k + 4) := by
    intro x hx
    rw [Finset.mem_range]
    rcases Finset.mem_union.mp hx with h | h
    · have := (hC x h).2
      omega
    · exact (Finset.mem_Ico.mp h).2
  have hdisj : Disjoint C (Finset.Ico k (k + 4)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 := (hC x hx).2
    have h2 := (Finset.mem_Ico.mp hx').1
    omega
  have hcard : (C ∪ Finset.Ico k (k + 4)).card = C.card + 4 := by
    rw [Finset.card_union_of_disjoint hdisj, Nat.card_Ico]
    omega
  have hid : ∑ j ∈ Finset.range (k + 4), (if j ∈ C ∪ Finset.Ico k (k + 4) then 1 else 2) +
      ∑ j ∈ Finset.range (k + 4), (if j ∈ C ∪ Finset.Ico k (k + 4) then 1 else 0) =
      ∑ _j ∈ Finset.range (k + 4), 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> rfl
  have hone : ∑ j ∈ Finset.range (k + 4), (if j ∈ C ∪ Finset.Ico k (k + 4) then 1 else 0) =
      (C ∪ Finset.Ico k (k + 4)).card := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
    simp
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hid
  omega

theorem OmegaSetting.finrank_add_card_le (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) (C : Finset ℕ)
    (hC : ∀ j ∈ C, 0 < j ∧ j < k ∧ IsCertified QN w j) :
    finrank K V + C.card ≤ 2 * k + 4 := by
  have hk : 0 < k := hF.pos
  have hCk : ∀ j ∈ C, 0 < j ∧ j < k := fun j hj => ⟨(hC j hj).1, (hC j hj).2.1⟩
  have hcert : ∀ j ∈ C, ∃ i < j, lineAxis ρ e f p p' w k j ⊓ lineAxis ρ e f p p' w k i ≠ ⊥ := by
    intro j hj
    obtain ⟨-, hjk, i, hi, hperp, hne⟩ := hC j hj
    exact ⟨i, hi, ov_cert hs hF (hi.trans hjk) hjk hperp hne⟩
  have htopA : (⊤ : Submodule K V) ≤ ⨆ i, lineAxis ρ e f p p' w k i :=
    top_le_iSup_of_generate htop (fun i => (listLine e f p p' w k i).1)
      (fun i => (listLine e f p p' w k i).2)
      (elementaryGroup_le_of_lines hs hF (fun i c => Subgroup.subset_closure ⟨i, c, rfl⟩))
      (A := lineAxis ρ e f p p' w k) (fun i c => lineAxis_smul_le hs hF i c)
  have hsup : (⨆ i, lineAxis ρ e f p p' w k i) ≤ ⨆ i < k + 4, lineAxis ρ e f p p' w k i := by
    refine iSup_le fun i => ?_
    by_cases hi : i < k + 4
    · exact le_iSup₂ (f := fun i (_ : i < k + 4) => lineAxis ρ e f p p' w k i) i hi
    · rw [lineAxis_ge (j := i) (by omega)]
      exact bot_le
  have hb : finrank K ↥(⨆ i < k + 4, lineAxis ρ e f p p' w k i) ≤
      ∑ j ∈ Finset.range (k + 4), (if j ∈ C ∪ Finset.Ico k (k + 4) then 1 else 2) :=
    finrank_iSup_lt_le_sum (lineAxis ρ e f p p' w k)
      (fun j => if j ∈ C ∪ Finset.Ico k (k + 4) then 1 else 2)
      (fun j => cost_step (A := lineAxis ρ e f p p' w k) C hk
        (fun j hj => lineAxis_rank hs hF hj) (fun _ hj => lineAxis_ge hj) hcert
        (ov_k hs hF) (ov_k1 hs hF) (ov_k2 hs hF) (ov_k3 hs hF) j) (k + 4)
  have hmono := Submodule.finrank_mono (htopA.trans hsup)
  rw [finrank_top] at hmono
  have hsum := sum_cost_le k C hCk
  omega

theorem OmegaSetting.finrank_le_of_listFrame (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) (hC : ∀ j, 0 < j → j < k → IsCertified QN w j) :
    finrank K V ≤ k + 5 := by
  have h := hs.finrank_add_card_le htop hF (Finset.Ioo 0 k) fun j hj => by
    rw [Finset.mem_Ioo] at hj
    exact ⟨hj.1, hj.2, hC j hj.1 hj.2⟩
  rw [Nat.card_Ioo] at h
  have := hF.pos
  omega

theorem OmegaSetting.finrank_le_eight_of_listFrame (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) {e f p p' : N} {w : ℕ → N} {j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w 2 j₁) : finrank K V ≤ 8 := by
  have h := hs.finrank_add_card_le htop hF ∅ (by simp)
  rw [Finset.card_empty, add_zero] at h
  omega

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
