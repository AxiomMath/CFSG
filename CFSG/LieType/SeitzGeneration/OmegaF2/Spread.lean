module

public import CFSG.LieType.SeitzGeneration.OmegaF2.Irred
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def cross3 (u w : Fin 3 → K) : Fin 3 → K :=
  ![u 1 * w 2 - u 2 * w 1, u 2 * w 0 - u 0 * w 2, u 0 * w 1 - u 1 * w 0]

structure TSFrame (Q : QuadraticForm K V) (e : Fin 3 → V) : Prop where
  Q_e : ∀ i, Q (e i) = 0
  polar_e : ∀ i j, polar Q (e i) (e j) = 0

@[expose] def frameVec (e : Fin 3 → V) (u : Fin 3 → K) : V := ∑ i, u i • e i

@[expose] noncomputable def siegel (Q : QuadraticForm K V) (e : Fin 3 → V) (ω : Fin 3 → K) :
    V ≃ₗ[K] V :=
  eichler Q (e 1) (ω 0 • e 2) * eichler Q (e 2) (ω 1 • e 0) * eichler Q (e 0) (ω 2 • e 1)

variable {e : Fin 3 → V}

private theorem polar_frameVec_left (he : TSFrame Q e) (v : Fin 3 → K) (i : Fin 3) :
    polar Q (frameVec e v) (e i) = 0 := by
  simp [frameVec, Fin.sum_univ_three, polar_add_left, polar_smul_left, he.polar_e]

private theorem polar_add_frameVec_left (he : TSFrame Q e) (x : V) (v : Fin 3 → K) (i : Fin 3) :
    polar Q (x + frameVec e v) (e i) = polar Q x (e i) := by
  rw [polar_add_left, polar_frameVec_left he, add_zero]

private theorem eichler_frame_apply (he : TSFrame Q e) (a b : Fin 3) (s : K) (x : V) :
    eichler Q (e a) (s • e b) x =
      x + (polar Q x (e a) * s) • e b - (s * polar Q x (e b)) • e a := by
  have hw : polar Q (e a) (s • e b) = 0 := by simp [polar_smul_right, he.polar_e]
  rw [eichler_apply (he.Q_e a) hw x]
  simp [polar_smul_right, QuadraticMap.map_smul, he.Q_e] <;> module

theorem siegel_zero (he : TSFrame Q e) : siegel Q e 0 = 1 := by
  simp [siegel, eichler_zero_right]

private theorem linearEquiv_mul_apply' (f g : V ≃ₗ[K] V) (x : V) : (f * g) x = f (g x) := rfl

private theorem siegel_apply (he : TSFrame Q e) (ω : Fin 3 → K) (x : V) :
    siegel Q e ω x = x + frameVec e (cross3 ω (fun i => polar Q x (e i))) := by
  simp only [siegel, linearEquiv_mul_apply', eichler_frame_apply he]
  simp [frameVec, cross3, Fin.sum_univ_three, polar_add_left, polar_sub_left, polar_smul_left,
    he.polar_e] <;> module

theorem siegel_add (he : TSFrame Q e) (ω ω' : Fin 3 → K) :
    siegel Q e (ω + ω') = siegel Q e ω * siegel Q e ω' := by
  apply LinearEquiv.ext
  intro x
  rw [linearEquiv_mul_apply']
  simp only [siegel_apply he, polar_add_frameVec_left he]
  simp [frameVec, cross3, Fin.sum_univ_three] <;> module

private theorem Q_frameVec (he : TSFrame Q e) (u : Fin 3 → K) : Q (frameVec e u) = 0 := by
  simp [frameVec, Fin.sum_univ_three, QuadraticMap.map_add, polar_add_left, polar_add_right,
    polar_smul_left, polar_smul_right, QuadraticMap.map_smul, he.Q_e, he.polar_e]

private theorem polar_frameVec_frameVec (he : TSFrame Q e) (u w : Fin 3 → K) :
    polar Q (frameVec e u) (frameVec e w) = 0 := by
  simp [frameVec, Fin.sum_univ_three, polar_add_left, polar_add_right, polar_smul_left,
    polar_smul_right, he.polar_e]

theorem eichler_frameVec (he : TSFrame Q e) (u w : Fin 3 → K) :
    eichler Q (frameVec e u) (frameVec e w) = siegel Q e (cross3 u w) := by
  apply LinearEquiv.ext
  intro x
  rw [eichler_apply (Q_frameVec he u) (polar_frameVec_frameVec he u w) x, Q_frameVec he w,
    zero_mul, add_zero, siegel_apply he]
  simp [frameVec, cross3, Fin.sum_univ_three, polar_add_left, polar_add_right, polar_smul_left,
    polar_smul_right] <;> module

private theorem polar_frameVec_dual {e' : Fin 3 → V}
    (hdual : ∀ i j, polar Q (e i) (e' j) = if i = j then 1 else 0) (v : Fin 3 → K) (j : Fin 3) :
    polar Q (frameVec e v) (e' j) = v j := by
  simp only [frameVec, Fin.sum_univ_three, polar_add_left, polar_smul_left, hdual]
  fin_cases j <;> simp

private theorem polar_e'_e {e' : Fin 3 → V}
    (hdual : ∀ i j, polar Q (e i) (e' j) = if i = j then 1 else 0) (k j : Fin 3) :
    polar Q (e' j) (e k) = if k = j then 1 else 0 := by
  rw [polar_comm, hdual]

theorem siegel_conj (he : TSFrame Q e) {e' : Fin 3 → V}
    (hdual : ∀ i j, polar Q (e i) (e' j) = if i = j then 1 else 0) {i j : Fin 3} (hij : i ≠ j)
    (ω : Fin 3 → K) :
    eichler Q (e i) (e' j) * siegel Q e ω * (eichler Q (e i) (e' j))⁻¹ =
      siegel Q e (Function.update ω j (ω j + ω i)) := by
  have hpi : polar Q (e i) (e' j) = 0 := by rw [hdual, if_neg hij]
  have hT := eichler_apply (he.Q_e i) hpi
  rw [mul_inv_eq_iff_eq_mul]
  apply LinearEquiv.ext
  intro x
  simp only [linearEquiv_mul_apply', hT]
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals
    simp only [siegel_apply he, polar_add_left, polar_sub_left, polar_smul_left, polar_add_right,
      polar_sub_right, polar_smul_right, polar_frameVec_left he, polar_add_frameVec_left he,
      polar_frameVec_dual hdual, he.polar_e, polar_e'_e hdual]
    simp [frameVec, cross3, Fin.sum_univ_three, Function.update_apply] <;> module

theorem full_line_of_spread {H : Subgroup (V ≃ₗ[K] V)} (he : TSFrame Q e) {e' : Fin 3 → V}
    (hdual : ∀ i j, polar Q (e i) (e' j) = if i = j then 1 else 0)
    (hT : ∀ i j : Fin 3, i ≠ j → eichler Q (e i) (e' j) ∈ H) (u w : Fin 3 → K)
    (hnz : cross3 u w ≠ 0)
    (hline : ∀ t : K, eichler Q (frameVec e u) (t • frameVec e w) ∈ H) :
    ∀ i j : Fin 3, i ≠ j → ∀ t : K, eichler Q (e i) (t • e j) ∈ H := by
  have frameVec_smul : ∀ (s : K) (w : Fin 3 → K), frameVec e (s • w) = s • frameVec e w := by
    intro s w
    simp [frameVec, Finset.smul_sum, smul_smul]
  have frameVec_single : ∀ (j : Fin 3) (a : K), frameVec e (Pi.single j a) = a • e j := by
    intro j a
    fin_cases j <;> simp [frameVec, Fin.sum_univ_three, Pi.single_apply]
  have cross3_smul : ∀ (s : K) (u w : Fin 3 → K), cross3 u (s • w) = s • cross3 u w := by
    intro s u w
    funext k
    fin_cases k <;> simp [cross3] <;> ring
  let Ω : Submodule K (Fin 3 → K) :=
    { carrier := {ω | ∀ s : K, siegel Q e (s • ω) ∈ H}
      add_mem' := by
        intro a b ha hb
        have ha' : ∀ s : K, siegel Q e (s • a) ∈ H := ha
        have hb' : ∀ s : K, siegel Q e (s • b) ∈ H := hb
        show ∀ s : K, siegel Q e (s • (a + b)) ∈ H
        intro s
        rw [smul_add, siegel_add he]
        exact H.mul_mem (ha' s) (hb' s)
      zero_mem' := by
        show ∀ s : K, siegel Q e (s • (0 : Fin 3 → K)) ∈ H
        intro s
        rw [smul_zero, siegel_zero he]
        exact H.one_mem
      smul_mem' := by
        intro r a ha
        have ha' : ∀ s : K, siegel Q e (s • a) ∈ H := ha
        show ∀ s : K, siegel Q e (s • (r • a)) ∈ H
        intro s
        rw [smul_smul]
        exact ha' (s * r) }
  have hΩmem : ∀ ω, ω ∈ Ω ↔ ∀ s : K, siegel Q e (s • ω) ∈ H := fun ω => Iff.rfl
  have hc : cross3 u w ∈ Ω := by
    rw [hΩmem]
    intro s
    rw [← cross3_smul, ← eichler_frameVec he, frameVec_smul]
    exact hline s
  have hΩstab : ∀ i j : Fin 3, i ≠ j → ∀ ω ∈ Ω, Function.update ω j (ω j + ω i) ∈ Ω := by
    intro i j hij ω hω
    rw [hΩmem] at hω ⊢
    intro s
    have hupd : Function.update (s • ω) j ((s • ω) j + (s • ω) i) =
        s • Function.update ω j (ω j + ω i) := by
      funext k
      by_cases hk : k = j
      · subst hk
        simp [mul_add]
      · simp [Function.update_apply, hk]
    rw [← hupd, ← siegel_conj he hdual hij]
    exact H.mul_mem (H.mul_mem (hT i j hij) (hω s)) (H.inv_mem (hT i j hij))
  have hΩtop : Ω = ⊤ := eq_top_of_stable Ω hΩstab hc hnz
  have hall : ∀ ω : Fin 3 → K, siegel Q e ω ∈ H := by
    intro ω
    have hω : ω ∈ Ω := by
      rw [hΩtop]
      exact Submodule.mem_top
    have h := (hΩmem ω).1 hω 1
    rwa [one_smul] at h
  have hfv : ∀ a b : Fin 3 → K, eichler Q (frameVec e a) (frameVec e b) ∈ H := by
    intro a b
    rw [eichler_frameVec he]
    exact hall _
  intro i j hij t
  have h1 : e i = frameVec e (Pi.single i (1 : K)) := by
    rw [frameVec_single, one_smul]
  have h2 : t • e j = frameVec e (Pi.single j t) := by
    rw [frameVec_single]
  rw [h1, h2]
  exact hfv _ _

end CFSG.LieType.SeitzGeneration.OmegaF2
