module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QSpSkew
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QSpCnt

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.Burgoyne.Sp

variable {r : ℕ} {K : Type} [Field K]

theorem eq_one_or_neg_of_coe_eq_smul [NeZero r] {s : StatedSp r K} {μ : K}
    (hs : ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = μ • 1) :
    ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 ∨
      ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = -1 := by
  have hJ := mem_statedSp_iff.1 s.2
  rw [hs, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one, smul_smul] at hJ
  have hμ : μ * μ = 1 := smul_formJ_injective r (by rw [hJ, one_smul])
  rcases mul_self_eq_one_iff.1 hμ with h | h
  · left
    rw [hs, h, one_smul]
  · right
    rw [hs, h, neg_one_smul]

theorem mem_center_of_coe_eq_smul_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Subgroup (GL ι K)} {s : H} {μ : K}
    (hs : ((s : GL ι K) : Matrix ι ι K) = μ • 1) : s ∈ center H := by
  rw [mem_center_iff]
  intro t
  apply Subtype.ext
  apply Units.ext
  simp only [coe_mul, Units.val_mul, hs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]

variable [Finite K]

theorem famF_concl_sp_split (hK : ringChar K ≠ 2) (hK4 : 4 ≤ Nat.card K) (hr : 2 ≤ r) {l : K}
    (hl : l ^ 2 = -1) {X : Type} [Group X] [Finite X] (π : StatedSp r K →* X)
    (hπ : Function.Surjective π)
    (hker : ∀ s, π s = 1 → ∃ μ : K,
      ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = μ • 1)
    {a : StatedSp r K}
    (ha : ((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      l • stdSkew r K)
    (hz2 : π a * π a = 1) {P : Subgroup X} (hPC : P ≤ centralizer ({π a} : Set X))
    (h8 : Nat.card P = 8)
    (hP : ∀ L : Subgroup (centralizer ({π a} : Set X)), IsComponent L → Even (Nat.card L) →
      ∀ k ∈ L, ∀ g ∈ P, (k : X) * g = g * k) :
    ¬ ((∃ u ∈ P, ∃ v ∈ P, u * v ≠ v * u) ∧ ∀ q ∈ P, q * q = 1 → q = 1 ∨ q = π a) ∧
      ¬ ∀ q ∈ P, q * q = 1 := by
  have : NeZero r := ⟨by omega⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hl0 : l ≠ 0 := by
    rintro rfl
    have : (0 : K) = -1 := by rw [← hl]; ring
    exact one_ne_zero (neg_eq_zero.1 this.symm)
  set Ma := ((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hMa
  have haa : Ma * Ma = -1 := by
    rw [ha, Matrix.smul_mul, Matrix.mul_smul, stdSkew_mul_self, smul_smul, ← sq, hl, neg_one_smul]
  have hcomm_iff : ∀ N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K,
      N * Ma = Ma * N ↔ N * stdSkew r K = stdSkew r K * N := by
    intro N
    rw [ha, Matrix.mul_smul, Matrix.smul_mul]
    constructor
    · intro h
      exact smul_right_injective _ hl0 h
    · intro h
      rw [h]
  have hans : ∀ c : K, Ma ≠ c • 1 := by
    intro c hc
    have e1 := congrFun (congrFun hc (Sum.inl ⟨0, by omega⟩)) (Sum.inl ⟨0, by omega⟩)
    have e2 := congrFun (congrFun hc (Sum.inr ⟨0, by omega⟩)) (Sum.inr ⟨0, by omega⟩)
    rw [ha] at e1 e2
    simp [stdSkew] at e1 e2
    apply hl0
    have : (2 : K) * l = 0 := by linear_combination e1 - e2
    exact (mul_eq_zero.1 this).resolve_left h2
  have hMq : IsQuasisimple (leviSL r K).range := isQuasisimple_leviSL_range hr (Or.inr hK4)
  have hcent : ∀ g : StatedSp r K, g ∈ centralizer ({a} : Set (StatedSp r K)) ↔
      g ∈ spCent r K (stdSkewGsp r K) := by
    intro g
    rw [mem_centralizer_singleton_iff, mem_spCent, coe_stdSkewGsp]
    constructor
    · intro h
      have e := congrArg (fun x : StatedSp r K =>
        ((x : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h
      exact ((hcomm_iff _).1 e).symm
    · intro h
      exact Subtype.ext (Units.ext ((hcomm_iff _).2 h.symm))
  have hNC : (leviSL r K).range ≤ centralizer ({a} : Set (StatedSp r K)) := by
    rintro _ ⟨g, rfl⟩
    exact (hcent _).2 (leviSL_mem_spCent g)
  have hNn : ∀ x ∈ centralizer ({a} : Set (StatedSp r K)), ∀ m ∈ (leviSL r K).range,
      x * m * x⁻¹ ∈ (leviSL r K).range := fun x hx m hm =>
    conj_mem_leviSL_range h2 ((hcent x).1 hx) hm
  have hker' : ∀ s, π s = 1 → s ∈ center (StatedSp r K) := fun s hs => by
    obtain ⟨μ, hμ⟩ := hker s hs
    exact mem_center_of_coe_eq_smul_one hμ
  have hker2 : ∀ s, π s = 1 →
      ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 ∨
        ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = -1 :=
    fun s hs => by
      obtain ⟨μ, hμ⟩ := hker s hs
      exact eq_one_or_neg_of_coe_eq_smul hμ
  have hPT : ∀ g ∈ P, ∀ s, π s = g → s ∈ centralizer ((leviSL r K).range : Set (StatedSp r K)) := by
    intro g hg s hs
    have key := lift_commute_of_subnormal π hπ hker' a hMq le_rfl
      (fun x hx m hm => mul_mem (mul_mem hx hm) (inv_mem hx)) hNC hNn
      (fun L hL he k hk => hP L hL he k hk g hg) hs
    rw [mem_centralizer_iff]
    intro m hm
    exact (key m hm).symm
  have hTU : ∀ s ∈ centralizer ((leviSL r K).range : Set (StatedSp r K)),
      ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * Ma =
        Ma * ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) →
      ∃ x y : K, x ^ 2 + y ^ 2 = 1 ∧
        ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          x • 1 + y • Ma := by
    intro s hs hsa
    have hsS := (hcomm_iff _).1 hsa
    have hsL : ∀ i j : Fin r, i ≠ j →
        ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * levN i j =
          levN i j * ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
      intro i j hij
      have h1 := (mem_centralizer_iff.1 hs) _ ⟨Matrix.SpecialLinearGroup.transvection hij 1, rfl⟩
      have h1' := congrArg (fun x : StatedSp r K =>
        ((x : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h1
      simp only [Subgroup.coe_mul, Units.val_mul, coe_leviSL_transvection, one_smul] at h1'
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one] at h1'
      exact (add_left_cancel h1').symm
    obtain ⟨x, y, hxy⟩ := rot_of_commute_levN h2 (by omega) hl0 hsS hsL
    have hxy' : ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        x • 1 + y • Ma := by rw [hxy, ha]
    refine ⟨x, y, norm_eq_one_of_rot_mem (mem_statedSp_iff.1 a.2) haa ?_, hxy'⟩
    have hD := mem_statedSp_iff.1 s.2
    rwa [hxy'] at hD
  exact famF_concl_skew h2 π hπ hker2 haa hans hz2 hTU h8 hPC hPT

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
