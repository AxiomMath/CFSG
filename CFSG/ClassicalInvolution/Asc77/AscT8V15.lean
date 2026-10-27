module

public import CFSG.ClassicalInvolution.Asc77.AscT8V12
import CFSG.ClassicalInvolution.Asc77.AscSu4ShapeEng
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 CFSG.ClassicalGroups.Unitary
open scoped MatrixGroups commutatorElement

namespace T8V

section SU4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su4_shape (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (α : Su K p f 4 →* Su K p f 4)
    (g : GL (Fin 4) K) (φ : K ≃+* K)
    (hα : ∀ x : Su K p f 4, suMat (α x) =
      (g : Matrix (Fin 4) (Fin 4) K) * φ.mapMatrix (suMat x) *
        ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A)
    (hfix2 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 2 (by norm_num) A) =
      blockEmb K p f 4 2 2 (by norm_num) A) :
    (φ = RingEquiv.refl K ∧ ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b]) ∨
    (φ = unitaryInvolution K p f ∧ ∃ m n : K, m ≠ 0 ∧ n ≠ 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) =
        !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0]) :=
  CFSG.ClassicalInvolution.Asc77.CX.CX4.U4.shape_gen hK hp α g φ hα hfix0 hfix2

theorem norm_neg_one_sq {c : K} (hq4 : p ^ f % 4 = 1) (hc : c * c = -1) :
    unitaryInvolution K p f c * c = -1 := by
  rw [unitaryInvolution_apply, ← pow_succ]
  obtain ⟨j, hj⟩ : ∃ j, p ^ f = 4 * j + 1 := ⟨p ^ f / 4, by omega⟩
  rw [hj, show 4 * j + 1 + 1 = 2 * (2 * j + 1) by ring, pow_mul, pow_two, hc]
  exact Odd.neg_one_pow ⟨j, by ring⟩

theorem norm_ratio_diag (α : Su K p f 4 →* Su K p f 4) {a b : K}
    (hY : suMat (α (mixSU K p f)) =
      !![0, 0, a * b⁻¹, 0; 0, 1, 0, 0; -(b * a⁻¹), 0, 0, 0; 0, 0, 0, 1]) :
    unitaryInvolution K p f (b * a⁻¹) * (b * a⁻¹) = 1 := by
  have hu : conjTr (unitaryInvolution K p f) (suMat (α (mixSU K p f))) *
      suMat (α (mixSU K p f)) = 1 := (α (mixSU K p f)).2.2
  rw [hY] at hu
  have e := congrFun (congrFun hu 0) 0
  simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four] at e
  simpa [map_mul, map_inv₀] using e

theorem norm_ratio_antidiag (α : Su K p f 4 →* Su K p f 4) {m n : K}
    (hY : suMat (α (mixSU K p f)) =
      !![1, 0, 0, 0; 0, 0, 0, m * n⁻¹; 0, 0, 1, 0; 0, -(n * m⁻¹), 0, 0]) :
    unitaryInvolution K p f (n * m⁻¹) * (n * m⁻¹) = 1 := by
  have hu : conjTr (unitaryInvolution K p f) (suMat (α (mixSU K p f))) *
      suMat (α (mixSU K p f)) = 1 := (α (mixSU K p f)).2.2
  rw [hY] at hu
  have e := congrFun (congrFun hu 1) 1
  simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four] at e
  simpa [map_mul, map_inv₀] using e

theorem sq_of_diag4_sharp (hK : Nat.card K = (p ^ f) ^ 2) (β : Su K p f 4 →* Su K p f 4)
    {s w : K} (hs : s ≠ 0) (hw : w ≠ 0)
    (hβ : ∀ x, suMat (β x) =
      !![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w] * suMat x *
        !![s⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, w⁻¹, 0; 0, 0, 0, w⁻¹])
    (hβ2 : ∀ x, β (β x) * x⁻¹ ∈ Subgroup.center (Su K p f 4)) (hne : s ≠ -w) :
    ∀ x, β x = x := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) (hβ2 (mixSU K p f))
  have e : suMat (β (β (mixSU K p f)) * (mixSU K p f)⁻¹) = Matrix.scalar (Fin 4) (c : K) := hc
  have e2 : suMat (β (β (mixSU K p f))) =
      Matrix.scalar (Fin 4) (c : K) * suMat (mixSU K p f) := by
    calc suMat (β (β (mixSU K p f))) = suMat (β (β (mixSU K p f)) * (mixSU K p f)⁻¹) *
          suMat (mixSU K p f) := by
          rw [suMat_mul, Matrix.mul_assoc, suMat_inv_mul_suMat, Matrix.mul_one]
      _ = _ := by rw [e]
  have h1 : suMat (β (β (mixSU K p f))) = (c : K) • suMat (mixSU K p f) := by
    rw [e2, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  rw [hβ (β (mixSU K p f)), hβ (mixSU K p f), suMat_mixSU] at h1
  have hss : s * s = w * w := sq_eq_of_scalar hs hw (c : K) h1
  rcases mul_self_eq_mul_self_iff.mp hss with h | h
  · subst h
    intro x
    apply suMat_injective
    rw [hβ x]
    exact conj_scalar4 hs (suMat x)
  · exact absurd h hne

omit [Finite K] in
theorem inv_of_antidiag4 {m n : K} (hm : m ≠ 0) (hn : n ≠ 0) (Gi : Matrix (Fin 4) (Fin 4) K)
    (h : Gi * !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] = 1) :
    Gi = !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0] := by
  have h2 : (!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] : Matrix (Fin 4) (Fin 4) K) *
      !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, hm, hn]
  calc Gi = Gi * (!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] *
        !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0]) := by
        rw [h2, Matrix.mul_one]
    _ = (Gi * !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0]) *
        !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0] := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h, Matrix.one_mul]

theorem sq_of_lift_sharp (hK : Nat.card K = (p ^ f) ^ 2) (α : Su K p f 4 →* Su K p f 4)
    (G Gi : Matrix (Fin 4) (Fin 4) K) (φ : K ≃+* K) (hφφ : ∀ c, φ (φ c) = c)
    (hGiG : Gi * G = 1) (hα : ∀ x, suMat (α x) = G * φ.mapMatrix (suMat x) * Gi) {s w : K}
    (hs : s ≠ 0) (hw : w ≠ 0)
    (hD : G * φ.mapMatrix G = !![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w])
    (hα4 : ∀ x, α (α (α (α x))) * x⁻¹ ∈ Subgroup.center (Su K p f 4)) (hne : s ≠ -w) :
    ∀ x, α (α x) = x := by
  have hDi : φ.mapMatrix Gi * Gi = !![s⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, w⁻¹, 0; 0, 0, 0, w⁻¹] := by
    apply inv_of_diag4 hs hw
    rw [← hD]
    exact inv_sq_matrix φ G Gi hGiG
  have hβ : ∀ x, suMat ((α.comp α) x) =
      !![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w] * suMat x *
        !![s⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, w⁻¹, 0; 0, 0, 0, w⁻¹] := by
    intro x
    show suMat (α (α x)) = _
    rw [hα (α x), hα x, alpha_sq_matrix φ hφφ, hD, hDi]
  exact sq_of_diag4_sharp hK (α.comp α) hs hw hβ hα4 hne

theorem su4_fixing_sharp (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq4 : p ^ f % 4 = 1)
    (α : Su K p f 4 →* Su K p f 4) (g : GL (Fin 4) K) (φ : K ≃+* K)
    (hα : ∀ x : Su K p f 4, suMat (α x) =
      (g : Matrix (Fin 4) (Fin 4) K) * φ.mapMatrix (suMat x) *
        ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A)
    (hfix2 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 2 (by norm_num) A) =
      blockEmb K p f 4 2 2 (by norm_num) A)
    (hα4 : ∀ x, α (α (α (α x))) * x⁻¹ ∈ Subgroup.center (Su K p f 4)) :
    ∀ x, α (α x) = x := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hσσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c :=
    unitaryInvolution_involutive hK
  set G : Matrix (Fin 4) (Fin 4) K := (g : Matrix (Fin 4) (Fin 4) K) with hG
  set Gi : Matrix (Fin 4) (Fin 4) K := ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    with hGi
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rcases su4_shape hK hp α g φ hα hfix0 hfix2 with ⟨hφ, a, b, ha, hb, hGab⟩ |
    ⟨hφ, m, n, hm, hn, hGmn⟩
  · subst hφ
    have hGi' : Gi = !![a⁻¹, 0, 0, 0; 0, a⁻¹, 0, 0; 0, 0, b⁻¹, 0; 0, 0, 0, b⁻¹] :=
      inv_of_diag4 ha hb Gi (by rw [← hGab]; exact hGiG)
    have hY : suMat (α (mixSU K p f)) =
        !![0, 0, a * b⁻¹, 0; 0, 1, 0, 0; -(b * a⁻¹), 0, 0, 0; 0, 0, 0, 1] := by
      rw [hα, hG, hGab, hGi', mapMatrix_refl_four, suMat_mixSU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp
    have hN := norm_ratio_diag α hY
    have hne : a * a ≠ -(b * b) := by
      intro h
      have hc : (b * a⁻¹) * (b * a⁻¹) = -1 := by
        field_simp
        linear_combination h
      have := norm_neg_one_sq hq4 hc
      rw [hN] at this
      apply h2
      linear_combination this
    refine sq_of_lift_sharp hK α G Gi (RingEquiv.refl K) (fun c => rfl) hGiG hα
      (mul_ne_zero ha ha) (mul_ne_zero hb hb) ?_ hα4 hne
    rw [mapMatrix_refl_four, hG, hGab]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  · subst hφ
    have hσm : unitaryInvolution K p f m ≠ 0 := (map_ne_zero _).mpr hm
    have hσn : unitaryInvolution K p f n ≠ 0 := (map_ne_zero _).mpr hn
    have hGi' : Gi = !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0] :=
      inv_of_antidiag4 hm hn Gi (by rw [← hGmn]; exact hGiG)
    have hmix : (unitaryInvolution K p f).mapMatrix (suMat (mixSU K p f)) =
        suMat (mixSU K p f) := by
      rw [suMat_mixSU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [RingEquiv.mapMatrix_apply]
    have hY : suMat (α (mixSU K p f)) =
        !![1, 0, 0, 0; 0, 0, 0, m * n⁻¹; 0, 0, 1, 0; 0, -(n * m⁻¹), 0, 0] := by
      rw [hα, hG, hGmn, hGi', hmix, suMat_mixSU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp
    have hN := norm_ratio_antidiag α hY
    have hNN : unitaryInvolution K p f n * n = unitaryInvolution K p f m * m := by
      simp only [map_mul, map_inv₀] at hN
      field_simp at hN
      linear_combination hN
    have hne : -(unitaryInvolution K p f m * m) ≠ -(-(unitaryInvolution K p f n * n)) := by
      intro h
      have h' : unitaryInvolution K p f m * m = 0 := by
        have : (2 : K) * (unitaryInvolution K p f m * m) = 0 := by
          rw [← hNN] at h ⊢
          linear_combination -h
        exact (mul_eq_zero.mp this).resolve_left h2
      exact mul_ne_zero hσm hm h'
    refine sq_of_lift_sharp hK α G Gi (unitaryInvolution K p f) hσσ hGiG hα
      (neg_ne_zero.mpr (mul_ne_zero hσm hm)) (neg_ne_zero.mpr (mul_ne_zero hσn hn)) ?_ hα4 hne
    rw [hG, hGmn]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, RingEquiv.mapMatrix_apply] <;> ring

theorem su4_aut_blocks_sharp (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq4 : p ^ f % 4 = 1) {X : Type} [Group X] (θ : Su K p f 4 →* X)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center (Su K p f 4)) (σ : MulAut X)
    (hσ4 : σ * σ * (σ * σ) = 1)
    (hfix0 : ∀ A : Su K p f 2, σ (θ (blockEmb K p f 4 2 0 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 0 (by norm_num) A))
    (hfix2 : ∀ A : Su K p f 2, σ (θ (blockEmb K p f 4 2 2 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 2 (by norm_num) A)) :
    σ * σ = 1 := by
  obtain ⟨α, g, φ, hlift, hmat, -, -⟩ :=
    unitaryAutClassification_isometry_of_card hK hp hq (d := 4) (by norm_num) X θ hθ hker σ
  have : Group.IsPerfect (Su K p f 2) := isPerfect_suTwo_of_card hK hq
  have hαfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A := fun A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed hker hlift (blockEmb K p f 4 2 0 (by norm_num))
      hfix0) A
  have hαfix2 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 2 (by norm_num) A) =
      blockEmb K p f 4 2 2 (by norm_num) A := fun A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed hker hlift (blockEmb K p f 4 2 2 (by norm_num))
      hfix2) A
  have h4 : ∀ y, σ (σ (σ (σ y))) = y := fun y => by
    have := congrArg (fun τ : MulAut X => τ y) hσ4
    simpa using this
  have hα4 : ∀ x, α (α (α (α x))) * x⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    intro x
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hlift, hlift, hlift, hlift, h4, mul_inv_cancel]
  have h := su4_fixing_sharp hK hp hq4 α g φ (fun x => hmat x) hαfix0 hαfix2 hα4
  ext y
  obtain ⟨x, rfl⟩ := hθ y
  show σ (σ (θ x)) = θ x
  rw [← hlift x, ← hlift (α x), h x]

theorem e4_su_sigma (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq4 : p ^ f % 4 = 1) {X : Type} [Group X] (θ : Su K p f 4 →* X)
    {R R' : Subgroup (Su K p f 4)} {y y' : Su K p f 4} (hP : E4Pair θ R R' y y')
    (hR : R ∈ Models.longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ Models.longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num)) :
    ∀ σ : MulAut X, (∀ r ∈ R, σ (θ r) = θ r) → (∀ r ∈ R', σ (θ r) = θ r) →
      σ * σ * (σ * σ) = 1 → σ * σ = 1 := by
  intro σ hσ hσ' hσ4
  have hc : y' * y⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    have := hP.cen
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hP.hy2
    rw [hyi, ← hP.comm y hP.hy y' hP.hy']
    exact this
  obtain ⟨g, hRg, hR'g, -⟩ := twin_std_u hK hp hR hR' hP.ne hP.hy hP.hy2 hP.hy1 hP.hy'
    hP.hy'2 hP.hy'1 hc
  set c : MulAut X := MulAut.conj (θ g) with hcdef
  have hcp : ∀ s, c (θ s) = θ (g * s * g⁻¹) := fun s => by
    rw [hcdef, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set σ' : MulAut X := c⁻¹ * σ * c with hσ'def
  have hσ'p : ∀ s, σ' (θ s) = (c⁻¹) (σ (c (θ s))) := fun s => rfl
  have hfixσ' : ∀ (S : Subgroup (Su K p f 4)),
      (∀ r ∈ S.map (MulAut.conj g).toMonoidHom, σ (θ r) = θ r) → ∀ r ∈ S, σ' (θ r) = θ r := by
    intro S hS r hr
    have hmem : g * r * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom := ⟨r, hr, rfl⟩
    rw [hσ'p, hcp, hS _ hmem, ← hcp]
    simp
  have hσ4' : σ' * σ' * (σ' * σ') = 1 := by
    calc σ' * σ' * (σ' * σ') = c⁻¹ * (σ * σ * (σ * σ)) * c := by rw [hσ'def]; group
      _ = 1 := by rw [hσ4]; group
  have hfix0 := hfixσ' ((blockEmb K p f 4 2 0 (by norm_num)).range) (hRg ▸ hσ)
  have hfix2 := hfixσ' ((blockEmb K p f 4 2 2 (by norm_num)).range) (hR'g ▸ hσ')
  have hsq : σ * σ = c * (σ' * σ') * c⁻¹ := by rw [hσ'def]; group
  rw [hsq, su4_aut_blocks_sharp hK hp hq hq4 θ hP.surj hP.ker σ' hσ4'
    (fun A => hfix0 _ ⟨A, rfl⟩) (fun A => hfix2 _ ⟨A, rfl⟩)]
  group

theorem e4_su_inner (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq4 : p ^ f % 4 = 1)
    {X : Type} [Group X] (θ : Su K p f 4 →* X) {R R' : Subgroup (Su K p f 4)}
    {y y' : Su K p f 4} (hP : E4Pair θ R R' y y')
    (hR : R ∈ Models.longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ Models.longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num)) :
    ∀ s : Su K p f 4, (∀ r ∈ R, s * r = r * s) → (∀ r ∈ R', s * r = r * s) →
      ∀ k ∈ θ.ker, s * s ≠ y * y' * k := by
  intro s hs hs' k hk hsk
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  have hc : y' * y⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    have := hP.cen
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hP.hy2
    rw [hyi, ← hP.comm y hP.hy y' hP.hy']
    exact this
  obtain ⟨g, hRg, hR'g, -⟩ := twin_std_u hK hp hR hR' hP.ne hP.hy hP.hy2 hP.hy1 hP.hy'
    hP.hy'2 hP.hy'1 hc
  have hcomm : ∀ (L S₁ : Subgroup (Su K p f 4)),
      S₁ = L.map (MulAut.conj g).toMonoidHom → (∀ r ∈ S₁, s * r = r * s) →
      ∀ r ∈ L, (g⁻¹ * s * g) * r = r * (g⁻¹ * s * g) := by
    intro L S₁ hS₁ hS r hr
    have hmem : g * r * g⁻¹ ∈ S₁ := by
      rw [hS₁]
      exact ⟨r, hr, rfl⟩
    have h := hS _ hmem
    calc (g⁻¹ * s * g) * r = g⁻¹ * (s * (g * r * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * r * g⁻¹) * s) * g := by rw [h]
      _ = r * (g⁻¹ * s * g) := by group
  have hc0 := hcomm _ R hRg hs
  have hc2 := hcomm _ R' hR'g hs'
  generalize hs₀ : g⁻¹ * s * g = s₀ at hc0 hc2
  have hαfix : ∀ r : Su K p f 4, s₀ * r = r * s₀ → (MulAut.conj s₀).toMonoidHom r = r := by
    intro r hr
    show s₀ * r * s₀⁻¹ = r
    rw [hr]
    group
  obtain ⟨t, ht, hts⟩ : ∃ t : K, unitaryInvolution K p f t * t = 1 ∧
      unitaryInvolution K p f t ≠ t := by
    obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
    exact exists_norm_one_ne_aux _ h2 hζ0 hζ
  rcases su4_shape hK hp (MulAut.conj s₀).toMonoidHom (s₀ : GL (Fin 4) K) (RingEquiv.refl K)
    (fun x => by
      show suMat (s₀ * x * s₀⁻¹) = _
      rw [suMat_mul, suMat_mul, mapMatrix_refl_four]
      rfl)
    (fun A => hαfix _ (hc0 _ ⟨A, rfl⟩)) (fun A => hαfix _ (hc2 _ ⟨A, rfl⟩)) with
    ⟨-, a, b, ha, hb, hM⟩ | ⟨hφ, -⟩
  swap
  · exact absurd (by rw [← hφ]; rfl) hts
  have hM' : suMat s₀ = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] := hM
  have hunit : conjTr (unitaryInvolution K p f) (suMat s₀) * suMat s₀ = 1 := s₀.2.2
  rw [hM'] at hunit
  have n0 := congrFun (congrFun hunit 0) 0
  simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four] at n0
  have hdet : (suMat s₀).det = 1 := s₀.2.1
  rw [hM'] at hdet
  have hdet' : a * a * (b * b) = 1 := by
    simpa [Matrix.det_succ_row_zero, Fin.sum_univ_succ, mul_assoc] using hdet
  have hcen : s * s ∈ Subgroup.center (Su K p f 4) := hsk ▸ Subgroup.mul_mem _ hP.cen (hP.ker hk)
  have hss0 : s₀ * s₀ = s * s := by
    have h1 := Subgroup.mem_center_iff.mp hcen g⁻¹
    calc s₀ * s₀ = g⁻¹ * (s * s) * g := by rw [← hs₀]; group
      _ = (s * s) * g⁻¹ * g := by rw [h1]
      _ = s * s := by group
  obtain ⟨c, hcs⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) hcen
  have hmat : suMat (s * s) =
      !![a * a, 0, 0, 0; 0, a * a, 0, 0; 0, 0, b * b, 0; 0, 0, 0, b * b] := by
    rw [← hss0, suMat_mul, hM']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  have e0 := congrFun (congrFun (hcs.symm.trans hmat) 0) 0
  have e2 := congrFun (congrFun (hcs.symm.trans hmat) 2) 2
  simp [Matrix.scalar_apply] at e0 e2
  have hcc : (c : K) * c = 1 := by
    calc (c : K) * c = (a * a) * (b * b) := congrArg₂ (· * ·) e0 e2
      _ = 1 := hdet'
  rcases mul_self_eq_one_iff.mp hcc with h1 | h1
  · have hs1 : s * s = 1 := by
      apply suMat_injective
      have hcs' : suMat (s * s) = Matrix.scalar (Fin 4) (c : K) := hcs
      rw [hcs', h1, suMat_one]
      simp [Matrix.scalar_apply]
    rw [hs1] at hsk
    exact hP.nontwin (by rw [eq_inv_of_mul_eq_one_left hsk.symm]; exact θ.ker.inv_mem hk)
  · have haa : a * a = -1 := by rw [← e0, h1]
    have hN := norm_neg_one_sq hq4 haa
    have n0' : unitaryInvolution K p f a * a = 1 := by simpa using n0
    rw [n0'] at hN
    apply h2
    linear_combination hN

end SU4

end T8V
end CFSG.ClassicalInvolution.Asc77
