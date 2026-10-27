module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFF4

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

section StepC




variable {n : ℕ}

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
  {M : Fin 4 → Subgroup Y} {a : Fin 4 → Y} {y : Y}

theorem WFFrame.t_e (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J) :
    t * ((x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹)) =
      ((x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹)) * t := by
  have hU : ∀ k, Commute t (x * a k * x⁻¹) := fun k =>
    hfr.t_comm h k (hfr.act_mem hxM k (hfr.haM k))
  exact ((((hU 0).mul_right (hU 1)).mul_right (hU 2)).mul_right (hU 3)).eq

theorem WFFrame.e_a (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J) {c : Fin 4 → Y}
    (hc : ∀ i, ((∀ m ∈ M i, x * m = m * x) ∧ c i = 1) ∨ (¬ (∀ m ∈ M i, x * m = m * x) ∧ c i = t))
    (j : Fin 4) :
    ((x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹)) * a j =
      c j * (a j * ((x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹))) := by
  have h1 := hfr.a_e h hxo hxt hxM hc j
  have ht2 := (h.q8 (hfr.mem 0)).z_sq
  generalize (x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹) = E at h1 ⊢
  rcases hc j with ⟨-, e⟩ | ⟨-, e⟩
  · rw [e, one_mul] at h1 ⊢
    exact h1.symm
  · rw [e] at h1 ⊢
    calc E * a j = t * (t * (E * a j)) := by rw [← mul_assoc, ht2, one_mul]
      _ = t * (a j * E) := by rw [← h1]


theorem WFFrame.e_s (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J) {c : Fin 4 → Y}
    (hc : ∀ i, ((∀ m ∈ M i, x * m = m * x) ∧ c i = 1) ∨ (¬ (∀ m ∈ M i, x * m = m * x) ∧ c i = t)) :
    ((x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹)) *
        (a 0 * a 1 * a 2 * a 3) =
      (c 0 * c 1 * c 2 * c 3) * ((a 0 * a 1 * a 2 * a 3) *
        ((x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹))) := by
  have hcA : ∀ i k, c i * a k = a k * c i := fun i k => by
    rcases hc i with ⟨-, e⟩ | ⟨-, e⟩
    · rw [e, one_mul, mul_one]
    · rw [e]; exact hfr.t_comm h k (hfr.haM k)
  exact swap_prod4 (hfr.e_a h hxo hxt hxM hc 0) (hfr.e_a h hxo hxt hxM hc 1)
    (hfr.e_a h hxo hxt hxM hc 2) (hfr.e_a h hxo hxt hxM hc 3) (hcA 1 0) (hcA 2 0) (hcA 2 1)
    (hcA 3 0) (hcA 3 1) (hcA 3 2)

theorem WFFrame.pair_e (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J) {c : Fin 4 → Y}
    (hc : ∀ i, ((∀ m ∈ M i, x * m = m * x) ∧ c i = 1) ∨ (¬ (∀ m ∈ M i, x * m = m * x) ∧ c i = t))
    (i j : Fin 4) {ε : Y} (hε : ε = 1 ∨ ε = t) :
    ((x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹)) * (a i * (ε * a j)) =
      (c i * c j) * ((a i * (ε * a j)) *
        ((x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹))) := by
  have hEi := hfr.e_a h hxo hxt hxM hc i
  have hEj := hfr.e_a h hxo hxt hxM hc j
  have hEt := hfr.t_e h hxM
  generalize (x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹) = E at hEi hEj hEt ⊢
  have hcA : ∀ k l, c k * a l = a l * c k := fun k l => by
    rcases hc k with ⟨-, e⟩ | ⟨-, e⟩
    · rw [e, one_mul, mul_one]
    · rw [e]; exact hfr.t_comm h l (hfr.haM l)
  have hc1t : ∀ k, c k = 1 ∨ c k = t := fun k => by
    rcases hc k with ⟨-, e⟩ | ⟨-, e⟩
    · exact Or.inl e
    · exact Or.inr e
  have hcε : ∀ k, c k * ε = ε * c k := fun k => by
    rcases hc1t k with e | e <;> rcases hε with f | f <;> simp [e, f]
  have hEε : E * ε = ε * E := by
    rcases hε with f | f
    · simp [f]
    · rw [f]; exact hEt.symm
  calc E * (a i * (ε * a j)) = (E * a i) * (ε * a j) := by group
    _ = (c i * (a i * E)) * (ε * a j) := by rw [hEi]
    _ = c i * a i * (E * ε) * a j := by group
    _ = c i * a i * (ε * E) * a j := by rw [hEε]
    _ = c i * a i * ε * (E * a j) := by group
    _ = c i * a i * ε * (c j * (a j * E)) := by rw [hEj]
    _ = c i * (a i * ε * c j) * (a j * E) := by group
    _ = c i * (c j * (a i * ε)) * (a j * E) := by
        rw [show a i * ε * c j = c j * (a i * ε) by
          calc a i * ε * c j = a i * (ε * c j) := mul_assoc _ _ _
            _ = a i * (c j * ε) := by rw [hcε j]
            _ = (a i * c j) * ε := (mul_assoc _ _ _).symm
            _ = (c j * a i) * ε := by rw [hcA j i]
            _ = c j * (a i * ε) := mul_assoc _ _ _]
    _ = (c i * c j) * ((a i * (ε * a j)) * E) := by group


theorem WFFrame.gt_eq (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (x : Y) :
    (x * y) * t * (x * y)⁻¹ = x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ := by
  rw [← hfr.fuse]; group

theorem WFFrame.eTwin_uniq (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (x : Y) (k : Fin 4) :
    IsUniqueInvolution (conjSub (x * y) (M k)) (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) := by
  have := (h.uniqInv (hfr.mem k)).conj (x * y)
  rwa [hfr.gt_eq x] at this

theorem WFFrame.eTwin_q8 (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (x : Y) (k : Fin 4) :
    Q8Facts (conjSub (x * y) (M k)) (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) := by
  obtain ⟨e⟩ := members_q8_of_isPGroup h.hStd.perp h.exit.2.2.2.1 _
    (h.hyp.conjInvariant (x * y) _ (hfr.mem k).1)
  exact q8Facts_of_iso (hfr.eTwin_uniq h x k) e

theorem WFFrame.eTwin_comm (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (x : Y) {i j : Fin 4}
    (hij : i ≠ j) : Commutes (conjSub (x * y) (M i)) (conjSub (x * y) (M j)) := by
  intro m hm m' hm'
  rw [mem_conjSub_iff] at hm hm'
  have := hfr.cross h hij hm hm'
  calc m * m' = (x * y) * ((x * y)⁻¹ * m * (x * y)) * ((x * y)⁻¹ * m' * (x * y)) * (x * y)⁻¹ := by
        group
    _ = (x * y) * ((x * y)⁻¹ * m' * (x * y)) * ((x * y)⁻¹ * m * (x * y)) * (x * y)⁻¹ := by
        rw [mul_assoc _ ((x * y)⁻¹ * m * (x * y)), this, ← mul_assoc _ _ ((x * y)⁻¹ * m * (x * y))]
    _ = m' * m := by group

theorem WFFrame.eTwin_perm (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (x : Y) {c : Y}
    (hc : c * (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) = (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) * c)
    (i : Fin 4) : ∃ j, conjSub c (conjSub (x * y) (M i)) = conjSub (x * y) (M j) := by
  have hd := h.hStd.datum
  set E := x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ with hE
  have hu := (hfr.eTwin_uniq h x i).conj c
  have hcE : c * E * c⁻¹ = E := mul_inv_eq_iff_eq_mul.mpr hc
  rw [hcE] at hu
  have hJ'Ω : conjSub c (conjSub (x * y) (M i)) ∈ CoreAssembly.conjClass (tightCore R) :=
    h.hyp.conjInvariant c _ (h.hyp.conjInvariant (x * y) _ (hfr.mem i).1)
  have hu' := hu.conj (x * y)⁻¹
  have e : (x * y)⁻¹ * E * (x * y)⁻¹⁻¹ = t := by
    rw [hE, ← hfr.gt_eq x]; group
  rw [e] at hu'
  have hmem : conjSub (x * y)⁻¹ (conjSub c (conjSub (x * y) (M i))) ∈
      twinSet (CoreAssembly.conjClass (tightCore R)) K :=
    ⟨h.hyp.conjInvariant _ _ hJ'Ω, t, hd.hz, hu'⟩
  obtain ⟨j, hj⟩ := hfr.surj _ hmem
  refine ⟨j, ?_⟩
  rw [hj, conjSub_conjSub_inv]


theorem orderOf_four_of_sq {z x : Y} (hx : x * x = z) (hz : z * z = 1) (hz1 : z ≠ 1) :
    orderOf x = 4 := by
  have h2 : x ^ 2 ≠ 1 := by rw [sq, hx]; exact hz1
  have h4 : x ^ 4 = 1 := by
    calc x ^ 4 = (x * x) * (x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [hx, hz]
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2) (by simpa using h4)
  simpa using this

theorem WFFrame.G1 (hB : WFB0 n) (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {E : Y}
    (hEt : E * t = t * E) (hEs : E * (a 0 * a 1 * a 2 * a 3) = t * ((a 0 * a 1 * a 2 * a 3) * E))
    {i j : Fin 4} (hij : i ≠ j) {ε : Y} (hε : ε = 1 ∨ ε = t) {d : Y} (hdE : d * E = E * d)
    (hdb : d * (a i * (ε * a j)) = (a i * (ε * a j)) * d) : d * t = t * d := by
  have hq8 := fun k => h.q8 (hfr.mem k)
  have ht := (hq8 0).z_sq
  have ht1 := (hq8 0).z_ne
  have hMne : ∀ p q : Fin 4, p ≠ q → M p ≠ M q := fun p q hpq e => hpq (hfr.inj e)
  have hsq := hfr.sq h
  have hεa : ε * a j ∈ M j ⊓ W := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rcases hε with e | e
      · rw [e, one_mul]; exact hfr.haM j
      · rw [e]; exact (M j).mul_mem (hq8 j).z_mem (hfr.haM j)
    · rcases hε with e | e
      · rw [e, one_mul]; exact hfr.haW j
      · rw [e]; exact W.mul_mem h.t_mem (hfr.haW j)
  have hεsq : (ε * a j) * (ε * a j) = t := by
    have htc : t * a j = a j * t := hfr.t_comm h j (hfr.haM j)
    rcases hε with e | e
    · rw [e, one_mul]; exact hsq j
    · rw [e]
      calc t * a j * (t * a j) = t * (a j * t) * a j := by group
        _ = t * (t * a j) * a j := by rw [← htc]
        _ = (t * t) * (a j * a j) := by group
        _ = t := by rw [ht, hsq j, one_mul]
  have hεo : orderOf (ε * a j) = 4 := orderOf_four_of_sq hεsq ht ht1
  have hsF : (a 0 * a 1 * a 2 * a 3) ∈ FrameInv (CoreAssembly.conjClass (tightCore R)) K W :=
    ⟨M, a, hfr.inj, hfr.mem, fun k => ⟨Subgroup.mem_inf.mpr ⟨hfr.haM k, hfr.haW k⟩, hfr.ha4 k⟩, rfl⟩
  have hnorm := hB Y R S t K K' K₃ u₁ u₂ u₃ K₄ W h W h.hW h.t_mem (M i) (hfr.mem i) (M j) (hfr.mem j)
    (hMne i j hij) (a i) (Subgroup.mem_inf.mpr ⟨hfr.haM i, hfr.haW i⟩) (ε * a j) hεa (hfr.ha4 i) hεo
    _ hsF (Subgroup.mem_centralizer_singleton_iff.mpr hdb)
  obtain ⟨s, hs⟩ : ∃ s, s = a 0 * a 1 * a 2 * a 3 := ⟨_, rfl⟩
  rw [← hs] at hEs hnorm hsF
  have hs2 : s * s = 1 := by
    have hcW : ∀ p q : Fin 4, Commute (a p) (a q) := fun p q => hfr.comm_a h p q
    rw [hs, prod4_sq_comm (hcW 0 1) (hcW 0 2) (hcW 0 3) (hcW 1 2) (hcW 1 3) (hcW 2 3), hfr.sq h, hfr.sq h,
      hfr.sq h, hfr.sq h, ht, one_mul, ht]
  have hts : t * s = s * t := by
    have hti : ∀ p, Commute t (a p) := fun p => hfr.t_comm h p (hfr.haM p)
    rw [hs]
    exact (((hti 0).mul_right (hti 1)).mul_right (hti 2)).mul_right (hti 3)
  have hcJ : ∀ p q : Fin 4, p ≠ q → Commutes (M p) (M q) := fun p q hpq m hm m' hm' =>
    hfr.cross h hpq hm hm'
  have hsne := frame_prod_ne (hq8 0) (hfr.haM 0) (hfr.haM 1) (hfr.haM 2) (hfr.haM 3) (hsq 0)
    (hcJ 0 1 (by decide)) (hcJ 0 2 (by decide)) (hcJ 0 3 (by decide))
  rw [← hs] at hsne
  have hs' : d * s * d⁻¹ ∈ Subgroup.closure ({t, s} : Set Y) :=
    (Subgroup.mem_normalizer_iff.mp hnorm s).mp (Subgroup.subset_closure (by simp))
  have hrel : E * (d * s * d⁻¹) = (d * t * d⁻¹) * ((d * s * d⁻¹) * E) := by
    have hdE' : d * E * d⁻¹ = E := mul_inv_eq_iff_eq_mul.mpr hdE
    calc E * (d * s * d⁻¹) = (d * E * d⁻¹) * (d * s * d⁻¹) := by rw [hdE']
      _ = d * (E * s) * d⁻¹ := by group
      _ = d * (t * (s * E)) * d⁻¹ := by rw [hEs]
      _ = (d * t * d⁻¹) * ((d * s * d⁻¹) * (d * E * d⁻¹)) := by group
      _ = (d * t * d⁻¹) * ((d * s * d⁻¹) * E) := by rw [hdE']
  have hEt' : t * E = E * t := hEt.symm
  have htt : d * t * d⁻¹ = t := by
    rcases klein_closure ht hs2 hts _ hs' with e | e | e | e
    · exact absurd (by
        have : s = d⁻¹ * (d * s * d⁻¹) * d := by group
        rw [this, e]; group) hsne.1
    · rw [e] at hrel
      have : d * t * d⁻¹ = 1 := by
        have h1 : t * E = (d * t * d⁻¹) * (t * E) := hEt.symm.trans hrel
        have h2 : (d * t * d⁻¹) * (t * E) = 1 * (t * E) := by rw [one_mul]; exact h1.symm
        exact mul_right_cancel h2
      exact absurd (by
        have h3 : t = d⁻¹ * (d * t * d⁻¹) * d := by group
        rw [h3, this]; group) ht1
    · rw [e] at hrel
      have h1 : t * (s * E) = (d * t * d⁻¹) * (s * E) := by rw [← hEs, hrel]
      exact (mul_right_cancel h1).symm
    · rw [e] at hrel
      have h1 : E * (t * s) = s * E := by
        calc E * (t * s) = (E * t) * s := (mul_assoc _ _ _).symm
          _ = (t * E) * s := by rw [hEt]
          _ = t * (E * s) := mul_assoc _ _ _
          _ = t * (t * (s * E)) := by rw [hEs]
          _ = (t * t) * (s * E) := (mul_assoc _ _ _).symm
          _ = s * E := by rw [ht, one_mul]
      have h2 : (d * t * d⁻¹ * t) * (s * E) = 1 * (s * E) := by
        calc (d * t * d⁻¹ * t) * (s * E) = (d * t * d⁻¹) * (t * s * E) := by group
          _ = E * (t * s) := hrel.symm
          _ = s * E := h1
          _ = 1 * (s * E) := (one_mul _).symm
      have h3 := mul_right_cancel h2
      calc d * t * d⁻¹ = (d * t * d⁻¹) * (t * t) := by rw [ht, mul_one]
        _ = (d * t * d⁻¹ * t) * t := (mul_assoc _ _ _).symm
        _ = t := by rw [h3, one_mul]
  have : d * t * d⁻¹ * d = t * d := by rw [htt]
  calc d * t = d * t * d⁻¹ * d := by group
    _ = t * d := this


theorem WFFrame.v_notW (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J) {i : Fin 4}
    (hmv : ¬ ∀ m ∈ M i, x * m = m * x) {ε : Y} (hε : ε = 1 ∨ ε = t) :
    ε * (x⁻¹ * a i * x) ∈ M i ∧ ε * (x⁻¹ * a i * x) ∉ W := by
  have hxM' : ∀ m ∈ M i, x⁻¹ * m * x ∈ M i := fun m hm =>
    mem_conjSub_iff.mp (by rw [hxM _ (hfr.mem i)]; exact hm)
  have hxz' : x⁻¹ * t = t * x⁻¹ := by
    calc x⁻¹ * t = x⁻¹ * (t * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * t) * x⁻¹ := by rw [hxt]
      _ = t * x⁻¹ := by group
  have hq := h.q8 (hfr.mem i)
  have hviM : x⁻¹ * a i * x ∈ M i := hxM' _ (hfr.haM i)
  have hεM : ε ∈ M i := by
    rcases hε with e | e
    · rw [e]; exact (M i).one_mem
    · rw [e]; exact hq.z_mem
  refine ⟨(M i).mul_mem hεM hviM, fun hW => ?_⟩
  have hviW : x⁻¹ * a i * x ∈ W := by
    rcases hε with e | e
    · rw [e, one_mul] at hW; exact hW
    · rw [e] at hW
      have := W.mul_mem (W.inv_mem h.t_mem) hW
      have e2 : t⁻¹ * (t * (x⁻¹ * a i * x)) = x⁻¹ * a i * x := by group
      rwa [e2] at this
  have hsq : (x⁻¹ * a i * x) * (x⁻¹ * a i * x) = t := by
    calc (x⁻¹ * a i * x) * (x⁻¹ * a i * x) = x⁻¹ * (a i * a i) * x := by group
      _ = x⁻¹ * t * x := by rw [hfr.sq h i]
      _ = t := by rw [mul_assoc, ← hxt]; group
  have hc := h.abelian _ (hfr.haW i) _ hviW
  have hxi : orderOf x⁻¹ = orderOf x := orderOf_inv x
  have hxo' : Odd (orderOf x⁻¹) := by rw [hxi]; exact hxo
  have hxM'' : ∀ m ∈ M i, x⁻¹ * m * x⁻¹⁻¹ ∈ M i := fun m hm => by simpa using hxM' m hm
  have hfix : ZFix x⁻¹ t (a i) := by
    rcases eq_or_mul_t_of_comm hq (hfr.haM i) hviM (hfr.sq h i) hsq hc with e | e
    · exact Or.inl (by simpa using e)
    · exact Or.inr (by simpa using e)
  have hcent := hq.cent_of_fix hxo' hxz' hxM'' (hfr.haM i) (hfr.sq h i) hfix
  exact hmv fun m hm => by
    have h1 := hcent m hm
    calc x * m = x * (m * x⁻¹ * x) := by group
      _ = x * (x⁻¹ * m * x) := by rw [h1]
      _ = m * x := by group


theorem WFFrame.moves_pair (hWM : WFWM n) (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J) {i j : Fin 4}
    (hij : i ≠ j) (hmi : ¬ ∀ m ∈ M i, x * m = m * x) (hmj : ¬ ∀ m ∈ M j, x * m = m * x) {ε : Y}
    (hε : ε = 1 ∨ ε = t) (k : Fin 4) :
    conjSub (a i * (ε * a j)) (conjSub (x * y) (M k)) ≠ conjSub (x * y) (M k) := by
  intro heq
  obtain ⟨hvi, hvi'⟩ := hfr.v_notW h hxo hxt hxM hmi (ε := 1) (Or.inl rfl)
  obtain ⟨hvj, hvj'⟩ := hfr.v_notW h hxo hxt hxM hmj hε
  rw [one_mul] at hvi hvi'
  have key := hWM Y R S t K K' K₃ u₁ u₂ u₃ K₄ W h M a y hfr i j hij _ hvi hvi' _ hvj hvj' k
  apply key
  have hεx : x⁻¹ * ε * x = ε := by
    rcases hε with e | e
    · rw [e]; group
    · rw [e]; calc x⁻¹ * t * x = x⁻¹ * (t * x) := mul_assoc _ _ _
        _ = x⁻¹ * (x * t) := by rw [hxt]
        _ = t := by group
  have hconj : (x⁻¹ * a i * x) * (ε * (x⁻¹ * a j * x)) = x⁻¹ * (a i * (ε * a j)) * x := by
    calc (x⁻¹ * a i * x) * (ε * (x⁻¹ * a j * x)) = (x⁻¹ * a i * x) * ((x⁻¹ * ε * x) * (x⁻¹ * a j * x)) := by
          rw [hεx]
      _ = x⁻¹ * (a i * (ε * a j)) * x := by group
  rw [hconj]
  have := congrArg (conjSub x⁻¹) heq
  rw [← conjSub_mul, ← conjSub_mul, ← conjSub_mul] at this
  rw [← conjSub_mul]
  rw [show x⁻¹ * (x * y) = y by group] at this
  rw [show x⁻¹ * (a i * (ε * a j)) * x * y = x⁻¹ * (a i * (ε * a j)) * (x * y) by group]
  exact this

end StepC

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
