module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFR0

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

section Swap

variable {Y : Type*} [Group Y]

theorem slide_left {d U R : Y} (h : d * U = U * d) : U * (d * R) = d * (U * R) := by
  rw [← mul_assoc, ← h, mul_assoc]

theorem swap_prod4 {A U₀ U₁ U₂ U₃ d₀ d₁ d₂ d₃ : Y}
    (h₀ : A * U₀ = d₀ * (U₀ * A)) (h₁ : A * U₁ = d₁ * (U₁ * A))
    (h₂ : A * U₂ = d₂ * (U₂ * A)) (h₃ : A * U₃ = d₃ * (U₃ * A))
    (c₁₀ : d₁ * U₀ = U₀ * d₁) (c₂₀ : d₂ * U₀ = U₀ * d₂) (c₂₁ : d₂ * U₁ = U₁ * d₂)
    (c₃₀ : d₃ * U₀ = U₀ * d₃) (c₃₁ : d₃ * U₁ = U₁ * d₃) (c₃₂ : d₃ * U₂ = U₂ * d₃) :
    A * (U₀ * U₁ * U₂ * U₃) = (d₀ * d₁ * d₂ * d₃) * ((U₀ * U₁ * U₂ * U₃) * A) := by
  have s : ∀ (d U R : Y), A * U = d * (U * A) → A * (U * R) = d * (U * (A * R)) := by
    intro d U R h
    calc A * (U * R) = (A * U) * R := (mul_assoc _ _ _).symm
      _ = d * (U * A) * R := by rw [h]
      _ = d * (U * (A * R)) := by group
  calc A * (U₀ * U₁ * U₂ * U₃) = A * (U₀ * (U₁ * (U₂ * U₃))) := by group
    _ = d₀ * (U₀ * (A * (U₁ * (U₂ * U₃)))) := s d₀ U₀ _ h₀
    _ = d₀ * (U₀ * (d₁ * (U₁ * (A * (U₂ * U₃))))) := by rw [s d₁ U₁ _ h₁]
    _ = d₀ * (U₀ * (d₁ * (U₁ * (d₂ * (U₂ * (A * U₃)))))) := by rw [s d₂ U₂ _ h₂]
    _ = d₀ * (U₀ * (d₁ * (U₁ * (d₂ * (U₂ * (d₃ * (U₃ * A))))))) := by rw [h₃]
    _ = d₀ * (U₀ * (d₁ * (U₁ * (d₂ * (d₃ * (U₂ * (U₃ * A))))))) := by rw [slide_left c₃₂]
    _ = d₀ * (U₀ * (d₁ * (d₂ * (U₁ * (d₃ * (U₂ * (U₃ * A))))))) := by rw [slide_left c₂₁]
    _ = d₀ * (U₀ * (d₁ * (d₂ * (d₃ * (U₁ * (U₂ * (U₃ * A))))))) := by rw [slide_left c₃₁]
    _ = d₀ * (d₁ * (U₀ * (d₂ * (d₃ * (U₁ * (U₂ * (U₃ * A))))))) := by rw [slide_left c₁₀]
    _ = d₀ * (d₁ * (d₂ * (U₀ * (d₃ * (U₁ * (U₂ * (U₃ * A))))))) := by rw [slide_left c₂₀]
    _ = d₀ * (d₁ * (d₂ * (d₃ * (U₀ * (U₁ * (U₂ * (U₃ * A))))))) := by rw [slide_left c₃₀]
    _ = (d₀ * d₁ * d₂ * d₃) * ((U₀ * U₁ * U₂ * U₃) * A) := by group


theorem prod4_mul2 {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Y}
    (c₁₀ : A₁ * B₀ = B₀ * A₁) (c₂₀ : A₂ * B₀ = B₀ * A₂) (c₂₁ : A₂ * B₁ = B₁ * A₂)
    (c₃₀ : A₃ * B₀ = B₀ * A₃) (c₃₁ : A₃ * B₁ = B₁ * A₃) (c₃₂ : A₃ * B₂ = B₂ * A₃) :
    (A₀ * A₁ * A₂ * A₃) * (B₀ * B₁ * B₂ * B₃) = (A₀ * B₀) * (A₁ * B₁) * (A₂ * B₂) * (A₃ * B₃) := by
  have sl : ∀ (U d R : Y), U * d = d * U → U * (d * R) = d * (U * R) := by
    intro U d R h
    rw [← mul_assoc, h, mul_assoc]
  calc (A₀ * A₁ * A₂ * A₃) * (B₀ * B₁ * B₂ * B₃)
      = A₀ * (A₁ * (A₂ * (A₃ * (B₀ * (B₁ * (B₂ * B₃)))))) := by group
    _ = A₀ * (A₁ * (A₂ * (B₀ * (A₃ * (B₁ * (B₂ * B₃)))))) := by rw [sl _ _ _ c₃₀]
    _ = A₀ * (A₁ * (B₀ * (A₂ * (A₃ * (B₁ * (B₂ * B₃)))))) := by rw [sl _ _ _ c₂₀]
    _ = A₀ * (B₀ * (A₁ * (A₂ * (A₃ * (B₁ * (B₂ * B₃)))))) := by rw [sl _ _ _ c₁₀]
    _ = A₀ * (B₀ * (A₁ * (A₂ * (B₁ * (A₃ * (B₂ * B₃)))))) := by rw [sl _ _ _ c₃₁]
    _ = A₀ * (B₀ * (A₁ * (B₁ * (A₂ * (A₃ * (B₂ * B₃)))))) := by rw [sl _ _ _ c₂₁]
    _ = A₀ * (B₀ * (A₁ * (B₁ * (A₂ * (B₂ * (A₃ * B₃)))))) := by rw [sl _ _ _ c₃₂]
    _ = (A₀ * B₀) * (A₁ * B₁) * (A₂ * B₂) * (A₃ * B₃) := by group

theorem comm_mid {m Pl g Pr : Y} (hl : m * Pl = Pl * m) (hr : m * Pr = Pr * m)
    (h : m * (Pl * g * Pr) = (Pl * g * Pr) * m) : m * g = g * m := by
  have e : Pl * (m * g) * Pr = Pl * (g * m) * Pr := by
    calc Pl * (m * g) * Pr = (Pl * m) * g * Pr := by group
      _ = (m * Pl) * g * Pr := by rw [← hl]
      _ = m * (Pl * g * Pr) := by group
      _ = (Pl * g * Pr) * m := h
      _ = Pl * g * (Pr * m) := by group
      _ = Pl * g * (m * Pr) := by rw [hr]
      _ = Pl * (g * m) * Pr := by group
  exact mul_left_cancel (mul_right_cancel e)

end Swap


section Toolbox




variable {n : ℕ}


variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
  {M : Fin 4 → Subgroup Y} {a : Fin 4 → Y} {y : Y}

theorem WFFrame.sq (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (i : Fin 4) :
    a i * a i = t :=
  T7A.sq_eq_of_orderOf_four (h.uniqInv (hfr.mem i)) (hfr.haM i) (hfr.ha4 i)

theorem WFFrame.cross (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {i j : Fin 4} (hij : i ≠ j)
    {m m' : Y} (hm : m ∈ M i) (hm' : m' ∈ M j) : m * m' = m' * m :=
  h.comm (hfr.mem i) (hfr.mem j) (fun e => hij (hfr.inj e)) m hm m' hm'

theorem WFFrame.comm_a (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (i j : Fin 4) :
    a i * a j = a j * a i :=
  h.abelian _ (hfr.haW i) _ (hfr.haW j)

theorem WFFrame.t_comm (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (i : Fin 4) {m : Y}
    (hm : m ∈ M i) : t * m = m * t :=
  (h.q8 (hfr.mem i)).z_central m hm

theorem WFFrame.act_mem {x : Y} (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J) (i : Fin 4)
    {m : Y} (hm : m ∈ M i) : x * m * x⁻¹ ∈ M i := by
  have := conj_mem_conjSub (n := x) hm
  rwa [hxM _ (hfr.mem i)] at this

theorem WFFrame.act_sq (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y} (hxt : x * t = t * x)
    (i : Fin 4) : (x * a i * x⁻¹) * (x * a i * x⁻¹) = t := by
  calc (x * a i * x⁻¹) * (x * a i * x⁻¹) = x * (a i * a i) * x⁻¹ := by group
    _ = x * t * x⁻¹ := by rw [hfr.sq h i]
    _ = t := by rw [hxt]; group


theorem WFFrame.act_fixed {x : Y} (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y)
    (i : Fin 4) (hc : ∀ m ∈ M i, x * m = m * x) : x * a i * x⁻¹ = a i := by
  rw [hc _ (hfr.haM i)]; group

theorem WFFrame.act_moved (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J) (i : Fin 4)
    (hmv : ¬ ∀ m ∈ M i, x * m = m * x) :
    a i * (x * a i * x⁻¹) = t * ((x * a i * x⁻¹) * a i) := by
  have hq := h.q8 (hfr.mem i)
  have hxz : x * t = t * x := hxt
  have hnz := hq.not_zfix_of_not_cent hxo hxz (fun m hm => hfr.act_mem hxM i hm) hmv (hfr.haM i)
    (hfr.sq h i)
  have hu : x * a i * x⁻¹ ∈ M i := hfr.act_mem hxM i (hfr.haM i)
  have hnc : a i * (x * a i * x⁻¹) ≠ (x * a i * x⁻¹) * a i := by
    intro hc
    rcases eq_or_mul_t_of_comm hq (hfr.haM i) hu (hfr.sq h i) (hfr.act_sq h hxt i) hc with e | e
    · exact hnz (Or.inl e)
    · exact hnz (Or.inr e)
  have := hq.comm_eq _ (hfr.haM i) _ hu hnc
  calc a i * (x * a i * x⁻¹) = (a i * (x * a i * x⁻¹) * (a i)⁻¹ * (x * a i * x⁻¹)⁻¹) *
      ((x * a i * x⁻¹) * a i) := by group
    _ = t * ((x * a i * x⁻¹) * a i) := by rw [this]

theorem WFFrame.act_cross (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J) {i j : Fin 4}
    (hij : i ≠ j) :
    a i * (x * a j * x⁻¹) = (x * a j * x⁻¹) * a i ∧
      (x * a i * x⁻¹) * (x * a j * x⁻¹) = (x * a j * x⁻¹) * (x * a i * x⁻¹) :=
  ⟨hfr.cross h hij (hfr.haM i) (hfr.act_mem hxM j (hfr.haM j)),
    hfr.cross h hij (hfr.act_mem hxM i (hfr.haM i)) (hfr.act_mem hxM j (hfr.haM j))⟩

theorem exists_comm_coeff (x : Y) (M : Fin 4 → Subgroup Y) (t : Y) :
    ∃ c : Fin 4 → Y, ∀ i, ((∀ m ∈ M i, x * m = m * x) ∧ c i = 1) ∨
      (¬ (∀ m ∈ M i, x * m = m * x) ∧ c i = t) := by
  classical
  refine ⟨fun i => if (∀ m ∈ M i, x * m = m * x) then 1 else t, fun i => ?_⟩
  by_cases hi : ∀ m ∈ M i, x * m = m * x
  · left; exact ⟨hi, if_pos hi⟩
  · right; exact ⟨hi, if_neg hi⟩

theorem WFFrame.a_e (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    {c : Fin 4 → Y}
    (hc : ∀ i, ((∀ m ∈ M i, x * m = m * x) ∧ c i = 1) ∨ (¬ (∀ m ∈ M i, x * m = m * x) ∧ c i = t))
    (j : Fin 4) :
    a j * ((x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹)) =
      c j * (((x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹)) * a j) := by
  obtain ⟨U, hUdef⟩ : ∃ U : Fin 4 → Y, ∀ k, U k = x * a k * x⁻¹ := ⟨fun k => x * a k * x⁻¹, fun _ => rfl⟩
  have hUM : ∀ k, U k ∈ M k := fun k => (hUdef k) ▸ hfr.act_mem hxM k (hfr.haM k)
  have hc1t : ∀ i, c i = 1 ∨ c i = t := fun i => by
    rcases hc i with ⟨-, e⟩ | ⟨-, e⟩
    · exact Or.inl e
    · exact Or.inr e
  have hcU : ∀ i l, c i * U l = U l * c i := fun i l => by
    rcases hc1t i with e | e
    · rw [e, one_mul, mul_one]
    · rw [e]; exact hfr.t_comm h l (hUM l)
  let d : Fin 4 → Y := fun k => if j = k then c j else 1
  have hdU : ∀ k l, d k * U l = U l * d k := fun k l => by
    by_cases hjk : j = k
    · simp only [d, if_pos hjk]; exact hcU j l
    · simp only [d, if_neg hjk, one_mul, mul_one]
  have hjk : ∀ k, a j * U k = d k * (U k * a j) := fun k => by
    by_cases hjk : j = k
    · subst hjk
      simp only [d, if_pos rfl]
      rcases hc j with ⟨hcen, e⟩ | ⟨hmv, e⟩
      · rw [e, one_mul, hUdef, hfr.act_fixed j hcen]
      · rw [e, hUdef]; exact hfr.act_moved h hxo hxt hxM j hmv
    · simp only [d, if_neg hjk, one_mul]
      rw [hUdef]
      exact (hfr.act_cross h hxM hjk).1
  have key := swap_prod4 (hjk 0) (hjk 1) (hjk 2) (hjk 3) (hdU 1 0) (hdU 2 0) (hdU 2 1) (hdU 3 0)
    (hdU 3 1) (hdU 3 2)
  have hd : d 0 * d 1 * d 2 * d 3 = c j := by
    fin_cases j <;> simp [d]
  rw [hd] at key
  rw [hUdef 0, hUdef 1, hUdef 2, hUdef 3] at key
  exact key


theorem WFFrame.indep (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {g : Fin 4 → Y}
    (hg : ∀ i, g i ∈ M i) (hp : g 0 * g 1 * g 2 * g 3 = 1 ∨ g 0 * g 1 * g 2 * g 3 = t) (i : Fin 4) :
    g i = 1 ∨ g i = t := by
  have hcen : ∀ i, ∀ m ∈ M i, m * (g 0 * g 1 * g 2 * g 3) = (g 0 * g 1 * g 2 * g 3) * m := by
    intro i m hm
    rcases hp with e | e
    · rw [e, one_mul, mul_one]
    · rw [e]; exact (hfr.t_comm h i hm).symm
  have hcr : ∀ i j, j ≠ i → ∀ m ∈ M i, m * g j = g j * m := fun i j hj m hm =>
    hfr.cross h (Ne.symm hj) hm (hg j)
  have c2 : ∀ i j k, j ≠ i → k ≠ i → ∀ m ∈ M i, m * (g j * g k) = (g j * g k) * m :=
    fun i j k hj hk m hm => by
      calc m * (g j * g k) = (m * g j) * g k := (mul_assoc _ _ _).symm
        _ = (g j * m) * g k := by rw [hcr i j hj m hm]
        _ = g j * (m * g k) := mul_assoc _ _ _
        _ = g j * (g k * m) := by rw [hcr i k hk m hm]
        _ = (g j * g k) * m := (mul_assoc _ _ _).symm
  have c3 : ∀ i j k l, j ≠ i → k ≠ i → l ≠ i → ∀ m ∈ M i,
      m * (g j * g k * g l) = (g j * g k * g l) * m := fun i j k l hj hk hl m hm => by
    calc m * (g j * g k * g l) = (m * (g j * g k)) * g l := (mul_assoc _ _ _).symm
      _ = ((g j * g k) * m) * g l := by rw [c2 i j k hj hk m hm]
      _ = (g j * g k) * (m * g l) := mul_assoc _ _ _
      _ = (g j * g k) * (g l * m) := by rw [hcr i l hl m hm]
      _ = (g j * g k * g l) * m := (mul_assoc _ _ _).symm
  have h0 : ∀ m ∈ M 0, g 0 * m = m * g 0 := fun m hm =>
    (comm_mid (m := m) (Pl := 1) (g := g 0) (Pr := g 1 * g 2 * g 3) (by simp)
      (c3 0 1 2 3 (by decide) (by decide) (by decide) m hm)
      (by rw [show 1 * g 0 * (g 1 * g 2 * g 3) = g 0 * g 1 * g 2 * g 3 by group]; exact hcen 0 m hm)).symm
  have h1 : ∀ m ∈ M 1, g 1 * m = m * g 1 := fun m hm =>
    (comm_mid (m := m) (Pl := g 0) (g := g 1) (Pr := g 2 * g 3) (hcr 1 0 (by decide) m hm)
      (c2 1 2 3 (by decide) (by decide) m hm)
      (by rw [show g 0 * g 1 * (g 2 * g 3) = g 0 * g 1 * g 2 * g 3 by group]; exact hcen 1 m hm)).symm
  have h2 : ∀ m ∈ M 2, g 2 * m = m * g 2 := fun m hm =>
    (comm_mid (m := m) (Pl := g 0 * g 1) (g := g 2) (Pr := g 3) (c2 2 0 1 (by decide) (by decide) m hm)
      (hcr 2 3 (by decide) m hm) (hcen 2 m hm)).symm
  have h3 : ∀ m ∈ M 3, g 3 * m = m * g 3 := fun m hm =>
    (comm_mid (m := m) (Pl := g 0 * g 1 * g 2) (g := g 3) (Pr := 1)
      (c3 3 0 1 2 (by decide) (by decide) (by decide) m hm) (by simp)
      (by rw [show g 0 * g 1 * g 2 * g 3 * 1 = g 0 * g 1 * g 2 * g 3 by group]; exact hcen 3 m hm)).symm
  have key : ∀ i : Fin 4, ∀ m ∈ M i, g i * m = m * g i := by
    intro i
    fin_cases i
    exacts [h0, h1, h2, h3]
  exact (h.q8 (hfr.mem i)).center _ (hg i) (key i)

end Toolbox

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
