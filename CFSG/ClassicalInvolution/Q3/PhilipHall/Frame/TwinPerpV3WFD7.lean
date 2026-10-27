module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFD6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFD5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section D7outer




variable {n : ℕ}


section D7

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
  {M : Fin 4 → Subgroup Y} {a : Fin 4 → Y} {y : Y}

theorem WFFrame.E_basic (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) {s e : Y} (hs : s = a 0 * a 1 * a 2 * a 3)
    (he : e = x * s * x⁻¹) :
    s * s = 1 ∧ e * e = 1 ∧ t * s = s * t ∧ e * s = s * e ∧ e * t = t * e ∧
      (x * e * x⁻¹ = s * e ∨ x * e * x⁻¹ = t * (s * e)) ∧ e ≠ 1 ∧ e ≠ t ∧ e ≠ s ∧ e ≠ s * t := by
  have he' : e = x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ := by rw [he, hs]
  have hs2 : s * s = 1 := by rw [hs]; exact hfr.s_sq h
  have hts : t * s = s * t := by rw [hs]; exact hfr.s_comm_t h
  have hee : e * e = 1 := by rw [he']; exact hfr.d1_ee h x
  have hes : e * s = s * e := by rw [he', hs]; exact hfr.d1_es h hxo hxt hxM hmv
  have het : e * t = t * e := by rw [he']; exact hfr.d1_et h hxt
  obtain ⟨hne1, hnet, hnes, hnest⟩ := hfr.d1_ne h hxo hxt hxM hmv
  rw [← he'] at hne1 hnet hnes hnest
  rw [← hs] at hnes hnest
  have hcy := hfr.d1_cycle h hxo hxt hxM hmv
  rw [← he', ← hs] at hcy
  have ht := (h.q8 (hfr.mem 0)).z_sq
  have hse2 : (s * e) * (s * e) = 1 := by
    calc (s * e) * (s * e) = s * (e * s) * e := by group
      _ = s * (s * e) * e := by rw [hes]
      _ = (s * s) * (e * e) := by group
      _ = 1 := by rw [hs2, hee, one_mul]
  have hsei : (s * e)⁻¹ = s * e := inv_eq_of_mul_eq_one_right hse2
  refine ⟨hs2, hee, hts, hes, het, ?_, hne1, hnet, hnes, hnest⟩
  rcases hcy with h1 | h1
  · left
    calc x * e * x⁻¹ = (s * e)⁻¹ * (s * e * (x * e * x⁻¹)) := by group
      _ = s * e := by rw [h1, hsei, mul_one]
  · right
    have hcom : t * (s * e) = (s * e) * t := by
      calc t * (s * e) = (t * s) * e := by group
        _ = (s * t) * e := by rw [hts]
        _ = s * (t * e) := by group
        _ = s * (e * t) := by rw [het]
        _ = (s * e) * t := by group
    calc x * e * x⁻¹ = (s * e)⁻¹ * (s * e * (x * e * x⁻¹)) := by group
      _ = (s * e) * t := by rw [h1, hsei]
      _ = t * (s * e) := hcom.symm

theorem WFFrame.x_mem_N (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) {s e : Y} (hs : s = a 0 * a 1 * a 2 * a 3)
    (he : e = x * s * x⁻¹) :
    x ∈ Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y) := by
  obtain ⟨-, -, -, -, -, hcy, -⟩ := hfr.E_basic h hxo hxt hxM hmv hs he
  apply mem_normalizer_closure
  intro g hg
  have ht : t ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  have hsm : s ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  have hem : e ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · rw [hxt]; simpa using ht
  · rw [← he]; exact hem
  · rcases hcy with e1 | e1
    · rw [e1]; exact Subgroup.mul_mem _ hsm hem
    · rw [e1]; exact Subgroup.mul_mem _ ht (Subgroup.mul_mem _ hsm hem)

theorem WFFrame.P_mem_N (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) {s e : Y} (hs : s = a 0 * a 1 * a 2 * a 3)
    (he : e = x * s * x⁻¹) {p : Y} (hp : p ∈ M 0 ⊔ M 1 ⊔ M 2 ⊔ M 3) :
    p ∈ Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y) := by
  have hq : ∀ i, Q8Facts (M i) t := fun i => h.q8 (hfr.mem i)
  have hcom : ∀ i j, i ≠ j → Commutes (M i) (M j) := fun i j hij m hm m' hm' =>
    hfr.cross h hij hm hm'
  have hP : ∀ i, ∀ m ∈ M i, m ∈ M 0 ⊔ M 1 ⊔ M 2 ⊔ M 3 := fun i m hm => le_sup4 M i hm
  have hsP : s ∈ M 0 ⊔ M 1 ⊔ M 2 ⊔ M 3 := by
    rw [hs]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hP 0 _ (hfr.haM 0))
      (hP 1 _ (hfr.haM 1))) (hP 2 _ (hfr.haM 2))) (hP 3 _ (hfr.haM 3))
  have heP : e ∈ M 0 ⊔ M 1 ⊔ M 2 ⊔ M 3 := by
    have e1 : e = (x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹) := by
      rw [he, hs]; group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (hP 0 _ (hfr.act_mem hxM 0 (hfr.haM 0))) (hP 1 _ (hfr.act_mem hxM 1 (hfr.haM 1))))
      (hP 2 _ (hfr.act_mem hxM 2 (hfr.haM 2)))) (hP 3 _ (hfr.act_mem hxM 3 (hfr.haM 3)))
  have hps := P_comm_center (J := M) hq hcom hp hsP
  have hpe := P_comm_center (J := M) hq hcom hp heP
  have hpt : p * t = t * p :=
    Subgroup.mem_centralizer_singleton_iff.mp (P_le_centralizer (J := M) hq hp)
  have hti : p * t * p⁻¹ = t := mul_inv_eq_iff_eq_mul.mpr hpt
  have htm : t ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  have hsm : s ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  have hem : e ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  apply mem_normalizer_closure
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · rw [hti]; exact htm
  · rcases hps with e1 | e1
    · rw [mul_inv_eq_one.mp e1]; exact hsm
    · rw [mul_inv_eq_iff_eq_mul.mp e1]; exact Subgroup.mul_mem _ htm hsm
  · rcases hpe with e1 | e1
    · rw [mul_inv_eq_one.mp e1]; exact hem
    · rw [mul_inv_eq_iff_eq_mul.mp e1]; exact Subgroup.mul_mem _ htm hem

theorem WFFrame.exists_flip (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {k : Fin 4 → Y}
    (hk : ∀ i, k i ∈ M i ∧ k i * k i = t) (l : Fin 4) :
    ∃ m ∈ M l, m * (k 0 * k 1 * k 2 * k 3) * m⁻¹ = t * (k 0 * k 1 * k 2 * k 3) := by
  obtain ⟨Q, hQ, hQc⟩ := hfr.split_gen h (fun p => (hk p).1) l
  have hq := h.q8 (hfr.mem l)
  have ht := hq.z_sq
  have ht1 := hq.z_ne
  have hal1 : k l ≠ 1 := fun e1 => by
    have := (hk l).2
    rw [e1, one_mul] at this
    exact ht1 this.symm
  have halt : k l ≠ t := fun e1 => by
    have := (hk l).2
    rw [e1, ht] at this
    exact ht1 this.symm
  obtain ⟨m, hmM, hmnc⟩ := hq.exists_noncomm (k l) (hk l).1 hal1 halt
  have hcomm_eq := hq.comm_eq (k l) (hk l).1 m hmM hmnc
  have h3 : k l * m = t * (m * k l) := by
    calc k l * m = (k l * m * (k l)⁻¹ * m⁻¹) * (m * k l) := by group
      _ = t * (m * k l) := by rw [hcomm_eq]
  have h4 : m * k l = t * (k l * m) := by
    calc m * k l = (t * t) * (m * k l) := by rw [ht, one_mul]
      _ = t * (t * (m * k l)) := by rw [mul_assoc]
      _ = t * (k l * m) := by rw [← h3]
  have hmQ : m * Q * m⁻¹ = Q := mul_inv_eq_iff_eq_mul.mpr (hQc m hmM)
  have hma : m * k l * m⁻¹ = t * k l := by rw [h4]; group
  refine ⟨m, hmM, ?_⟩
  calc m * (k 0 * k 1 * k 2 * k 3) * m⁻¹ = (m * k l * m⁻¹) * (m * Q * m⁻¹) := by rw [hQ]; group
    _ = (t * k l) * Q := by rw [hma, hmQ]
    _ = t * (k 0 * k 1 * k 2 * k 3) := by rw [hQ]; group

theorem WFFrame.conj_s_mem_E (hB : WFB0 n) (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) {s e : Y} (hs : s = a 0 * a 1 * a 2 * a 3)
    (he : e = x * s * x⁻¹) {g : Y} (hg : g * t = t * g) :
    g * s * g⁻¹ ∈ Subgroup.closure ({t, s, e} : Set Y) := by
  have ht := (h.q8 (hfr.mem 0)).z_sq
  have ht1 := (h.q8 (hfr.mem 0)).z_ne
  obtain ⟨-, -, -, -, -, hcy, -⟩ := hfr.E_basic h hxo hxt hxM hmv hs he
  have hW' : conjSub g W ∈ WSet (CoreAssembly.conjClass (tightCore R)) :=
    WSet.conj h.hyp.conjInvariant h.hW g
  have htW' : t ∈ conjSub g W := by
    have := conj_mem_conjSub (n := g) h.t_mem
    rwa [show g * t * g⁻¹ = t from mul_inv_eq_iff_eq_mul.mpr hg] at this
  have hsF : g * s * g⁻¹ ∈ FrameInv (CoreAssembly.conjClass (tightCore R)) K (conjSub g W) := by
    refine ⟨fun i => conjSub g (M i), fun i => g * a i * g⁻¹, ?_, ?_, ?_, ?_⟩
    · intro i j hij; exact hfr.inj (conjSub_injective g hij)
    · intro i; exact h.conj_mem_twinSet hg (hfr.mem i)
    · intro i
      refine ⟨Subgroup.mem_inf.mpr ⟨conj_mem_conjSub (hfr.haM i), conj_mem_conjSub (hfr.haW i)⟩, ?_⟩
      have hsq : (g * a i * g⁻¹) * (g * a i * g⁻¹) = t := by
        calc (g * a i * g⁻¹) * (g * a i * g⁻¹) = g * (a i * a i) * g⁻¹ := by group
          _ = t := by rw [hfr.sq h i, hg]; group
      exact orderOf_four_of_sq hsq ht ht1
    · rw [hs]; group
  obtain ⟨b, hb, hbs⟩ := hfr.frameInv_canonical h hW' hsF
  have h3 := hfr.r3 hB h hxo hxt hxM hmv hW' htW' hb
  rw [← hs] at h3
  have he' : x * (x * s * x⁻¹) * x⁻¹ = (x * x) * s * (x * x)⁻¹ := by group
  rw [← he] at h3
  have e2 : (x * x) * s * (x * x)⁻¹ = x * e * x⁻¹ := by rw [he]; group
  rw [e2] at h3
  rw [hbs]
  have htm : t ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  have hsm : s ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  have hem : e ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  have he'm : x * e * x⁻¹ ∈ Subgroup.closure ({t, s, e} : Set Y) := by
    rcases hcy with e1 | e1
    · rw [e1]; exact Subgroup.mul_mem _ hsm hem
    · rw [e1]; exact Subgroup.mul_mem _ htm (Subgroup.mul_mem _ hsm hem)
  rcases h3 with (e1 | e1) | (e1 | e1) | (e1 | e1) <;> rw [e1]
  · exact hsm
  · exact Subgroup.mul_mem _ hsm htm
  · exact hem
  · exact Subgroup.mul_mem _ hem htm
  · exact he'm
  · exact Subgroup.mul_mem _ he'm htm

theorem WFFrame.ct_mem_N (hB : WFB0 n) (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) {s e : Y} (hs : s = a 0 * a 1 * a 2 * a 3)
    (he : e = x * s * x⁻¹) {c : Y} (hc : c * t = t * c) :
    c ∈ Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y) := by
  apply mem_normalizer_closure
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · rw [show c * g * c⁻¹ = g from mul_inv_eq_iff_eq_mul.mpr hc]
    exact Subgroup.subset_closure (by simp)
  · exact hfr.conj_s_mem_E hB h hxo hxt hxM hmv hs he hc
  · have hcx : (c * x) * t = t * (c * x) := by
      calc (c * x) * t = c * (x * t) := mul_assoc _ _ _
        _ = c * (t * x) := by rw [hxt]
        _ = (c * t) * x := (mul_assoc _ _ _).symm
        _ = (t * c) * x := by rw [hc]
        _ = t * (c * x) := mul_assoc _ _ _
    have := hfr.conj_s_mem_E hB h hxo hxt hxM hmv hs he hcx
    have e1 : c * g * c⁻¹ = (c * x) * s * (c * x)⁻¹ := by rw [he]; group
    rw [e1]; exact this

theorem WFFrame.r4 (hB : WFB0 n) (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) {s e : Y} (hs : s = a 0 * a 1 * a 2 * a 3)
    (he : e = x * s * x⁻¹) :
    ∀ v ∈ Subgroup.closure ({t, s, e} : Set Y), v ≠ 1 →
      ∃ n' ∈ Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y), n' * t * n'⁻¹ = v := by
  obtain ⟨hs2, hee, hts, hes, het, hcy, -⟩ := hfr.E_basic h hxo hxt hxM hmv hs he
  have ht := (h.q8 (hfr.mem 0)).z_sq
  have hxN := hfr.x_mem_N h hxo hxt hxM hmv hs he
  have hPN := fun {p : Y} (hp : p ∈ M 0 ⊔ M 1 ⊔ M 2 ⊔ M 3) => hfr.P_mem_N h hxo hxt hxM hmv hs he hp
  have hPgN : conjSub y (M 0) ⊔ conjSub y (M 1) ⊔ conjSub y (M 2) ⊔ conjSub y (M 3) ≤
      Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y) := by
    have := hfr.d5 hB h hxo hxt hxM hmv
    have he' : e = x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ := by rw [he, hs]
    rw [← he', ← hs] at this
    exact this
  obtain ⟨kk, hkk, hkprod⟩ := wfD4_proved n Y R S t K K' K₃ u₁ u₂ u₃ K₄ W h M a y hfr
  obtain ⟨m₀, hm₀M, hm₀⟩ := hfr.exists_flip h hkk 0
  have hsy : y * t * y⁻¹ = s := by rw [hs]; exact hfr.fuse
  obtain ⟨p, hpJ, hpt⟩ : ∃ p ∈ conjSub y (M 0), p * t * p⁻¹ = s * t := by
    refine ⟨y * m₀ * y⁻¹, conj_mem_conjSub hm₀M, ?_⟩
    calc y * m₀ * y⁻¹ * t * (y * m₀ * y⁻¹)⁻¹ =
        y * (m₀ * (y⁻¹ * t * y) * m₀⁻¹) * y⁻¹ := by group
      _ = y * (m₀ * (kk 0 * kk 1 * kk 2 * kk 3) * m₀⁻¹) * y⁻¹ := by rw [hkprod]
      _ = y * (t * (kk 0 * kk 1 * kk 2 * kk 3)) * y⁻¹ := by rw [hm₀]
      _ = (y * t * y⁻¹) * (y * (kk 0 * kk 1 * kk 2 * kk 3) * y⁻¹) := by group
      _ = s * t := by rw [← hkprod, hsy]; group
  have hpN : p ∈ Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y) :=
    hPgN (le_sup4 (fun i => conjSub y (M i)) 0 hpJ)
  obtain ⟨p', hp'M, hp's⟩ : ∃ p' ∈ M 0, p' * s * p'⁻¹ = t * s := by
    obtain ⟨m, hmM, hm⟩ := hfr.exists_flip h (k := a) (fun i => ⟨hfr.haM i, hfr.sq h i⟩) 0
    exact ⟨m, hmM, by rw [hs]; exact hm⟩
  have hp'N : p' ∈ Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y) :=
    hPN (le_sup4 M 0 hp'M)
  have hp't : p' * t * p'⁻¹ = t := mul_inv_eq_iff_eq_mul.mpr (hfr.t_comm h 0 hp'M).symm
  obtain ⟨m'', hm''M, hm''e⟩ : ∃ m'' ∈ M 0, m'' * e * m''⁻¹ = t * e := by
    have hku : ∀ i, x * a i * x⁻¹ ∈ M i ∧ (x * a i * x⁻¹) * (x * a i * x⁻¹) = t := fun i =>
      ⟨hfr.act_mem hxM i (hfr.haM i), hfr.act_sq h hxt i⟩
    obtain ⟨m, hmM, hm⟩ := hfr.exists_flip h (k := fun i => x * a i * x⁻¹) hku 0
    refine ⟨m, hmM, ?_⟩
    have e1 : e = (x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹) := by
      rw [he, hs]; group
    rw [e1]; exact hm
  have hm''N : m'' ∈ Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y) :=
    hPN (le_sup4 M 0 hm''M)
  have hm''t : m'' * t * m''⁻¹ = t := mul_inv_eq_iff_eq_mul.mpr (hfr.t_comm h 0 hm''M).symm
  have mulN := fun {u v : Y} (hu : u ∈ Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y))
    (hv : v ∈ Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y)) =>
    Subgroup.mul_mem _ hu hv
  have n1 : (p' * p) * t * (p' * p)⁻¹ = s := by
    calc (p' * p) * t * (p' * p)⁻¹ = p' * (p * t * p⁻¹) * p'⁻¹ := by group
      _ = p' * (s * t) * p'⁻¹ := by rw [hpt]
      _ = (p' * s * p'⁻¹) * (p' * t * p'⁻¹) := by group
      _ = s := by
          rw [hp's, hp't]
          calc t * s * t = s * t * t := by rw [hts]
            _ = s := by rw [mul_assoc, ht, mul_one]
  have n3 : (x * (p' * p)) * t * (x * (p' * p))⁻¹ = e := by
    calc (x * (p' * p)) * t * (x * (p' * p))⁻¹ = x * ((p' * p) * t * (p' * p)⁻¹) * x⁻¹ := by group
      _ = e := by rw [n1, he]
  have n4 : (m'' * (x * (p' * p))) * t * (m'' * (x * (p' * p)))⁻¹ = t * e := by
    calc (m'' * (x * (p' * p))) * t * (m'' * (x * (p' * p)))⁻¹ =
        m'' * ((x * (p' * p)) * t * (x * (p' * p))⁻¹) * m''⁻¹ := by group
      _ = t * e := by rw [n3, hm''e]
  have n5 : (x * (x * (p' * p))) * t * (x * (x * (p' * p)))⁻¹ = x * e * x⁻¹ := by
    calc (x * (x * (p' * p))) * t * (x * (x * (p' * p)))⁻¹ =
        x * ((x * (p' * p)) * t * (x * (p' * p))⁻¹) * x⁻¹ := by group
      _ = x * e * x⁻¹ := by rw [n3]
  have n6 : (x * (m'' * (x * (p' * p)))) * t * (x * (m'' * (x * (p' * p))))⁻¹ =
      t * (x * e * x⁻¹) := by
    calc (x * (m'' * (x * (p' * p)))) * t * (x * (m'' * (x * (p' * p))))⁻¹ =
        x * ((m'' * (x * (p' * p))) * t * (m'' * (x * (p' * p)))⁻¹) * x⁻¹ := by group
      _ = x * (t * e) * x⁻¹ := by rw [n4]
      _ = (x * t * x⁻¹) * (x * e * x⁻¹) := by group
      _ = t * (x * e * x⁻¹) := by rw [show x * t * x⁻¹ = t from mul_inv_eq_iff_eq_mul.mpr hxt]
  have N1 := mulN hp'N hpN
  have N3 := mulN hxN N1
  have N4 := mulN hm''N N3
  have N5 := mulN hxN N3
  have N6 := mulN hxN N4
  intro v hv hv1
  rcases e8_closure ht hs2 hee hts het.symm hes.symm v hv with e1 | e1 | e1 | e1 | e1 | e1 | e1 | e1
  · exact absurd e1 hv1
  · exact ⟨1, Subgroup.one_mem _, by rw [e1]; group⟩
  · exact ⟨_, N1, by rw [e1]; exact n1⟩
  · exact ⟨_, N3, by rw [e1]; exact n3⟩
  · exact ⟨p, hpN, by rw [e1, hpt]; exact hts.symm⟩
  · exact ⟨_, N4, by rw [e1]; exact n4⟩
  · rcases hcy with e2 | e2
    · exact ⟨_, N5, by rw [n5, e2, e1]⟩
    · refine ⟨_, N6, ?_⟩
      rw [n6, e2, ← mul_assoc, ht, one_mul, e1]
  · rcases hcy with e2 | e2
    · refine ⟨_, N6, ?_⟩
      rw [n6, e2, e1, mul_assoc]
    · exact ⟨_, N5, by rw [n5, e2, e1, mul_assoc]⟩

theorem WFFrame.exists_frame_at (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {W₁ : Subgroup Y}
    (hW₁ : W₁ ∈ WSet (CoreAssembly.conjClass (tightCore R))) (ht₁ : t ∈ W₁) :
    ∃ b : Fin 4 → Y, ∀ i, b i ∈ M i ∧ b i ∈ W₁ ∧ b i * b i = t := by
  have hMD := fun l => twin_mem_DSet h.partI h.exit.2.2.2.1 hW₁ ht₁ (hfr.mem l).1
    (h.uniqInv (hfr.mem l))
  have : ∀ i, ∃ g, g ∈ M i ∧ g ∈ W₁ ∧ g * g = t := fun i =>
    exists_gen_sq h.hyp hW₁ (hfr.mem i).1 (hMD i) (h.exit.2.2.2.1 _ (hfr.mem i).1) (h.q8 (hfr.mem i))
  choose b hb using this
  exact ⟨b, fun i => ⟨(hb i).1, (hb i).2.1, (hb i).2.2⟩⟩

theorem WFFrame.frame_mem_E (hB : WFB0 n) (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) {s e : Y} (hs : s = a 0 * a 1 * a 2 * a 3)
    (he : e = x * s * x⁻¹) {W₁ : Subgroup Y}
    (hW₁ : W₁ ∈ WSet (CoreAssembly.conjClass (tightCore R))) (ht₁ : t ∈ W₁) {b : Fin 4 → Y}
    (hb : ∀ i, b i ∈ M i ∧ b i ∈ W₁ ∧ b i * b i = t) :
    b 0 * b 1 * b 2 * b 3 ∈ Subgroup.closure ({t, s, e} : Set Y) := by
  obtain ⟨-, -, -, -, -, hcy, -⟩ := hfr.E_basic h hxo hxt hxM hmv hs he
  have h3 := hfr.r3 hB h hxo hxt hxM hmv hW₁ ht₁ hb
  rw [← hs] at h3
  rw [← he] at h3
  have e2 : (x * x) * s * (x * x)⁻¹ = x * e * x⁻¹ := by rw [he]; group
  rw [e2] at h3
  have htm : t ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  have hsm : s ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  have hem : e ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  have he'm : x * e * x⁻¹ ∈ Subgroup.closure ({t, s, e} : Set Y) := by
    rcases hcy with e1 | e1
    · rw [e1]; exact Subgroup.mul_mem _ hsm hem
    · rw [e1]; exact Subgroup.mul_mem _ htm (Subgroup.mul_mem _ hsm hem)
  rcases h3 with (e1 | e1) | (e1 | e1) | (e1 | e1) <;> rw [e1]
  · exact hsm
  · exact Subgroup.mul_mem _ hsm htm
  · exact hem
  · exact Subgroup.mul_mem _ hem htm
  · exact he'm
  · exact Subgroup.mul_mem _ he'm htm

theorem WFFrame.r5 (hB : WFB0 n) (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) {s e : Y} (hs : s = a 0 * a 1 * a 2 * a 3)
    (he : e = x * s * x⁻¹) {W' : Subgroup Y}
    (hW' : W' ∈ WSet (CoreAssembly.conjClass (tightCore R))) (htW' : t ∈ W')
    {L L' : Subgroup Y} (hL : L ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K)
    (hL' : L' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) (hne : L ≠ L') {a₁ a₂ : Y}
    (ha₁ : a₁ ∈ L ⊓ W') (ha₂ : a₂ ∈ L' ⊓ W') (oa₁ : orderOf a₁ = 4) (oa₂ : orderOf a₂ = 4) :
    Subgroup.centralizer ({a₁ * a₂} : Set Y) ≤
      Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y) := by
  obtain ⟨b', hb'⟩ := hfr.exists_frame_at h hW' htW'
  obtain ⟨-, -, -, -, hs'F⟩ := hfr.frame_basic h hb'
  have hs'E := hfr.frame_mem_E hB h hxo hxt hxM hmv hs he hW' htW' hb'
  have hN := hB Y R S t K K' K₃ u₁ u₂ u₃ K₄ W h W' hW' htW' L hL L' hL' hne a₁ ha₁ a₂ ha₂ oa₁ oa₂ _
    hs'F
  have htm : t ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  have hcl : Subgroup.closure ({t, b' 0 * b' 1 * b' 2 * b' 3} : Set Y) ≤
      Subgroup.closure ({t, s, e} : Set Y) := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact htm
    · exact hs'E
  intro c hc
  have hct : c * t * c⁻¹ ∈ Subgroup.closure ({t, s, e} : Set Y) :=
    hcl ((Subgroup.mem_normalizer_iff.mp (hN hc) t).mp (Subgroup.subset_closure (by simp)))
  have hct1 : c * t * c⁻¹ ≠ 1 := fun e1 => (h.q8 (hfr.mem 0)).z_ne (by
    have : t = c⁻¹ * (c * t * c⁻¹) * c := by group
    rw [this, e1]; group)
  obtain ⟨n', hn'N, hn'⟩ := hfr.r4 hB h hxo hxt hxM hmv hs he _ hct hct1
  have hcn : (n'⁻¹ * c) * t = t * (n'⁻¹ * c) := by
    have h1 : n'⁻¹ * (c * t * c⁻¹) * n' = t := by rw [← hn']; group
    calc (n'⁻¹ * c) * t = (n'⁻¹ * (c * t * c⁻¹) * n') * (n'⁻¹ * c) := by group
      _ = t * (n'⁻¹ * c) := by rw [h1]
  have hmem := hfr.ct_mem_N hB h hxo hxt hxM hmv hs he hcn
  have : c = n' * (n'⁻¹ * c) := by group
  rw [this]
  exact Subgroup.mul_mem _ hn'N hmem

end D7

end D7outer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
