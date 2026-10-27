module

public import CFSG.LieType.SeitzGeneration.SpFourData

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram)

section MixElt

variable {r : ℕ} {K : Type} [Field K]

theorem spTransvection_comm_of_form_eq_zero {w w' : Fin r ⊕ Fin r → K}
    (h : spForm r K w w' = 0) (t t' : K) :
    spTransvection w t * spTransvection w' t' = spTransvection w' t' * spTransvection w t := by
  refine commute_spTransvection (x := spTransvection w' t') (u := w) ?_ t
  rw [spEnd_spTransvection, h, mul_zero, zero_smul, add_zero]

@[expose] noncomputable def mixElt (z : StatedSp r K) (u : Fin r ⊕ Fin r → K) (c : K) :
    StatedSp r K :=
  spTransvection u c * spTransvection (spEnd z u) c * spTransvection (spEnd z (spEnd z u)) c

theorem mixElt_orth {z : StatedSp r K} (hz : z ^ 3 = 1) {u : Fin r ⊕ Fin r → K}
    (hu : spForm r K u (spEnd z u) = 0) :
    spForm r K u (spEnd z (spEnd z u)) = 0 ∧
      spForm r K (spEnd z u) (spEnd z (spEnd z u)) = 0 := by
  have h2 : spForm r K (spEnd z u) (spEnd z (spEnd z u)) = 0 := by
    rw [spEnd_isometry]
    exact hu
  refine ⟨?_, h2⟩
  have h3 := spEnd_isometry z u (spEnd z (spEnd z u))
  rw [spEnd_cube_apply hz] at h3
  rw [← h3, ← spForm_isAlt.neg_eq u (spEnd z u), hu, neg_zero]

theorem mixElt_comm {z : StatedSp r K} (hz : z ^ 3 = 1) {u : Fin r ⊕ Fin r → K}
    (hu : spForm r K u (spEnd z u) = 0) (c : K) : mixElt z u c * z = z * mixElt z u c := by
  obtain ⟨h02, -⟩ := mixElt_orth hz hu
  have c1 : z * spTransvection u c * z⁻¹ = spTransvection (spEnd z u) c :=
    spTransvection_conj z u c
  have c2 : z * spTransvection (spEnd z u) c * z⁻¹ = spTransvection (spEnd z (spEnd z u)) c :=
    spTransvection_conj z (spEnd z u) c
  have c3 : z * spTransvection (spEnd z (spEnd z u)) c * z⁻¹ = spTransvection u c := by
    rw [spTransvection_conj, spEnd_cube_apply hz]
  have k12 : spTransvection u c * spTransvection (spEnd z u) c =
      spTransvection (spEnd z u) c * spTransvection u c :=
    spTransvection_comm_of_form_eq_zero hu c c
  have k13 : spTransvection u c * spTransvection (spEnd z (spEnd z u)) c =
      spTransvection (spEnd z (spEnd z u)) c * spTransvection u c :=
    spTransvection_comm_of_form_eq_zero h02 c c
  have key : z * mixElt z u c * z⁻¹ = mixElt z u c := by
    calc z * mixElt z u c * z⁻¹
        = (z * spTransvection u c * z⁻¹) * (z * spTransvection (spEnd z u) c * z⁻¹) *
          (z * spTransvection (spEnd z (spEnd z u)) c * z⁻¹) := by
          unfold mixElt
          group
      _ = spTransvection (spEnd z u) c * spTransvection (spEnd z (spEnd z u)) c *
          spTransvection u c := by rw [c1, c2, c3]
      _ = mixElt z u c := by
          unfold mixElt
          rw [mul_assoc, ← k13, ← mul_assoc, ← k12]
  exact (mul_inv_eq_iff_eq_mul.mp key).symm

theorem spEnd_mixElt {z : StatedSp r K} (hz : z ^ 3 = 1) {u : Fin r ⊕ Fin r → K}
    (hu : spForm r K u (spEnd z u) = 0) (c : K) (y : Fin r ⊕ Fin r → K) :
    spEnd (mixElt z u c) y = y + (c * spForm r K y u) • u +
      (c * spForm r K y (spEnd z u)) • spEnd z u +
      (c * spForm r K y (spEnd z (spEnd z u))) • spEnd z (spEnd z u) := by
  obtain ⟨h13, h23⟩ := mixElt_orth hz hu
  have h21 : spForm r K (spEnd z u) u = 0 := by rw [← spForm_isAlt.neg_eq u, hu, neg_zero]
  have h31 : spForm r K (spEnd z (spEnd z u)) u = 0 := by
    rw [← spForm_isAlt.neg_eq u, h13, neg_zero]
  have h32 : spForm r K (spEnd z (spEnd z u)) (spEnd z u) = 0 := by
    rw [← spForm_isAlt.neg_eq (spEnd z u), h23, neg_zero]
  simp only [mixElt, spEnd_comp_apply, spEnd_spTransvection, map_add, map_smul, h21, h31, h32,
    mul_zero]
  module

end MixElt

section Mixing

variable {K : Type} [Field K]

structure MixData (H : Subgroup (StatedSp 2 K)) (z : StatedSp 2 K)
    (P₀ P₁ : Submodule K (Fin 2 ⊕ Fin 2 → K)) : Prop where
  cube : z ^ 3 = 1
  central : ∀ g : StatedSp 2 K, g * z = z * g → g ∈ H
  center₀ : ∀ v ∈ P₀, TransCenter H v
  sup : P₀ ⊔ P₁ = ⊤
  orth : ∀ u ∈ P₀, ∀ v ∈ P₁, spForm 2 K u v = 0
  nd₀ : ((spForm 2 K).restrict P₀).Nondegenerate
  nd₁ : ((spForm 2 K).restrict P₁).Nondegenerate
  rank₀ : Module.finrank K P₀ = 2
  rank₁ : Module.finrank K P₁ = 2
  stab₀ : ∀ v ∈ P₀, spEnd z v ∈ P₀
  stab₁ : ∀ v ∈ P₁, spEnd z v ∈ P₁
  norm₀ : ∀ v ∈ P₀, v + spEnd z v + spEnd z (spEnd z v) = 0
  norm₁ : ∀ v ∈ P₁, v + spEnd z v + spEnd z (spEnd z v) = 0

theorem mixed_center_of_isotropic {H : Subgroup (StatedSp 2 K)} {z : StatedSp 2 K}
    {P₀ P₁ : Submodule K (Fin 2 ⊕ Fin 2 → K)} (D : MixData H z P₀ P₁)
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) {u₀ u₁ : Fin 2 ⊕ Fin 2 → K} (hu₀ : u₀ ∈ P₀) (hu₁ : u₁ ∈ P₁)
    (hiso : spForm 2 K (u₀ + u₁) (spEnd z (u₀ + u₁)) = 0)
    (hstar : ∃ v ∈ P₀, spForm 2 K v u₀ • u₁ + spForm 2 K v (spEnd z u₀) • spEnd z u₁ +
      spForm 2 K v (spEnd z (spEnd z u₀)) • spEnd z (spEnd z u₁) ≠ 0) :
    ∃ y₀ ∈ P₀, ∃ y₁ ∈ P₁, y₀ ≠ 0 ∧ y₁ ≠ 0 ∧ TransCenter H (y₀ + y₁) := by
  obtain ⟨v, hv, hB⟩ := hstar
  obtain ⟨c₂, hc₂0, hc₂1⟩ := hK
  have hZ₀ : spEnd z u₀ ∈ P₀ := D.stab₀ u₀ hu₀
  have hZZ₀ : spEnd z (spEnd z u₀) ∈ P₀ := D.stab₀ _ hZ₀
  have hZ₁ : spEnd z u₁ ∈ P₁ := D.stab₁ u₁ hu₁
  have hZZ₁ : spEnd z (spEnd z u₁) ∈ P₁ := D.stab₁ _ hZ₁
  obtain ⟨A, hA⟩ : ∃ A : Fin 2 ⊕ Fin 2 → K, A = spForm 2 K v u₀ • u₀ +
      spForm 2 K v (spEnd z u₀) • spEnd z u₀ +
      spForm 2 K v (spEnd z (spEnd z u₀)) • spEnd z (spEnd z u₀) := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : Fin 2 ⊕ Fin 2 → K, B = spForm 2 K v u₀ • u₁ +
      spForm 2 K v (spEnd z u₀) • spEnd z u₁ +
      spForm 2 K v (spEnd z (spEnd z u₀)) • spEnd z (spEnd z u₁) := ⟨_, rfl⟩
  have hAmem : A ∈ P₀ := by
    rw [hA]
    exact P₀.add_mem (P₀.add_mem (P₀.smul_mem _ hu₀) (P₀.smul_mem _ hZ₀)) (P₀.smul_mem _ hZZ₀)
  have hBmem : B ∈ P₁ := by
    rw [hBd]
    exact P₁.add_mem (P₁.add_mem (P₁.smul_mem _ hu₁) (P₁.smul_mem _ hZ₁)) (P₁.smul_mem _ hZZ₁)
  have hB0 : B ≠ 0 := by rw [hBd]; exact hB
  have z0 : spForm 2 K v u₁ = 0 := D.orth v hv _ hu₁
  have z1 : spForm 2 K v (spEnd z u₁) = 0 := D.orth v hv _ hZ₁
  have z2 : spForm 2 K v (spEnd z (spEnd z u₁)) = 0 := D.orth v hv _ hZZ₁
  have key : ∀ c : K, spEnd (mixElt z (u₀ + u₁) c) v = (v + c • A) + c • B := by
    intro c
    rw [spEnd_mixElt D.cube hiso c v, hA, hBd]
    simp only [map_add, z0, z1, z2, add_zero]
    module
  have hy₀ : ∃ c : K, c ≠ 0 ∧ v + c • A ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : v + (1 : K) • A = 0 := hcon 1 one_ne_zero
    have h2 : v + c₂ • A = 0 := hcon c₂ hc₂0
    have h3 : (1 - c₂) • A = 0 := by linear_combination (norm := module) h1 - h2
    have hA0 : A = 0 := (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.2 (Ne.symm hc₂1))
    have hv0 : v = 0 := by
      rw [hA0, smul_zero, add_zero] at h1
      exact h1
    apply hB0
    rw [hBd, hv0]
    simp
  obtain ⟨c, hc0, hy₀⟩ := hy₀
  refine ⟨v + c • A, P₀.add_mem hv (P₀.smul_mem c hAmem), c • B, P₁.smul_mem c hBmem, hy₀,
    smul_ne_zero hc0 hB0, ?_⟩
  have := (D.center₀ v hv).map (D.central _ (mixElt_comm D.cube hiso c))
  rwa [key c] at this

omit [Field K] in
theorem other_root {l : K} [Field K] (hl : l ^ 2 + l + 1 = 0) :
    (-1 - l) ^ 2 + (-1 - l) + 1 = 0 := by
  linear_combination hl

theorem exists_eigenvector (h3 : (3 : K) ≠ 0) {z : StatedSp 2 K}
    {P : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hnd : ((spForm 2 K).restrict P).Nondegenerate)
    (hP : P ≠ ⊥) (hstab : ∀ v ∈ P, spEnd z v ∈ P)
    (hnorm : ∀ v ∈ P, v + spEnd z v + spEnd z (spEnd z v) = 0) {l : K} (hl : l ^ 2 + l + 1 = 0) :
    ∃ e ∈ P, e ≠ 0 ∧ spEnd z e = l • e := by
  have hm := other_root hl
  obtain ⟨w, hw, hwm⟩ : ∃ w ∈ P, spEnd z w - (-1 - l) • w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hwP⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    obtain ⟨w', hw'P, hww'⟩ : ∃ w' ∈ P, spForm 2 K w w' ≠ 0 := by
      by_contra h
      push Not at h
      exact hwP.2 (congrArg Subtype.val (hnd.1 ⟨w, hwP.1⟩ fun y => h y y.2))
    have e1 : spEnd z w = (-1 - l) • w := sub_eq_zero.1 (hcon w hwP.1)
    have e2 : spEnd z w' = (-1 - l) • w' := sub_eq_zero.1 (hcon w' hw'P)
    have h := spEnd_isometry z w w'
    rw [e1, e2, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h
    have hsq : (-1 - l) ^ 2 = 1 := by
      have : ((-1 - l) * (-1 - l) - 1) * spForm 2 K w w' = 0 := by linear_combination h
      have := (mul_eq_zero.mp this).resolve_right hww'
      linear_combination this
    exact h3 (by linear_combination hsq - ((-1 - l) - 2) * (hm - hsq))
  refine ⟨spEnd z w - (-1 - l) • w, P.sub_mem (hstab w hw) (P.smul_mem _ hw), hwm, ?_⟩
  have hn := hnorm w hw
  have hl' : (l ^ 2 + l + 1) • w = 0 := by rw [hl, zero_smul]
  rw [map_sub, map_smul]
  linear_combination (norm := module) hn - hl'

end Mixing

section CW

variable {K : Type} [Field K]

theorem exists_nonzero_zero_quadratic [Finite K] {σ : Type} [Fintype σ] [DecidableEq σ]
    (hσ : 3 ≤ Fintype.card σ) (M : Matrix σ σ K) :
    ∃ x : σ → K, x ≠ 0 ∧ x ⬝ᵥ (M.mulVec x) = 0 := by
  classical
  have := Fintype.ofFinite K
  have hp : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  let F : MvPolynomial σ K :=
    ∑ i, ∑ j, MvPolynomial.C (M i j) * MvPolynomial.X i * MvPolynomial.X j
  have hdeg : F.totalDegree ≤ 2 := by
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    calc (MvPolynomial.C (M i j) * MvPolynomial.X i * MvPolynomial.X j).totalDegree
        ≤ (MvPolynomial.C (M i j) * MvPolynomial.X i).totalDegree +
            (MvPolynomial.X j : MvPolynomial σ K).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ ((MvPolynomial.C (M i j) : MvPolynomial σ K).totalDegree +
            (MvPolynomial.X i : MvPolynomial σ K).totalDegree) +
            (MvPolynomial.X j : MvPolynomial σ K).totalDegree :=
          Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _
      _ ≤ 2 := by simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  have hdvd := char_dvd_card_solutions (ringChar K)
    (show F.totalDegree < Fintype.card σ by omega)
  have heval : ∀ x : σ → K, MvPolynomial.eval x F = x ⬝ᵥ (M.mulVec x) := by
    intro x
    simp only [F, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, dotProduct,
      Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  by_contra hcon
  push Not at hcon
  have hcard : ∀ [inst : Fintype {x : σ → K // MvPolynomial.eval x F = 0}],
      Fintype.card {x : σ → K // MvPolynomial.eval x F = 0} = 1 := by
    intro inst
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, by rw [heval]; simp⟩, fun ⟨x, hx⟩ => Subtype.ext ?_⟩
    by_contra hne
    exact hcon x hne (by rw [← heval]; exact hx)
  rw [@hcard _] at hdvd
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 hdvd)

end CW

section Cases

variable {K : Type} [Field K]

theorem exists_isotropic_split {H : Subgroup (StatedSp 2 K)} {z : StatedSp 2 K}
    {P₀ P₁ : Submodule K (Fin 2 ⊕ Fin 2 → K)} (h3 : (3 : K) ≠ 0) (D : MixData H z P₀ P₁) {l : K}
    (hl : l ^ 2 + l + 1 = 0) :
    ∃ u₀ ∈ P₀, ∃ u₁ ∈ P₁, spForm 2 K (u₀ + u₁) (spEnd z (u₀ + u₁)) = 0 ∧
      ∃ v ∈ P₀, spForm 2 K v u₀ • u₁ + spForm 2 K v (spEnd z u₀) • spEnd z u₁ +
        spForm 2 K v (spEnd z (spEnd z u₀)) • spEnd z (spEnd z u₁) ≠ 0 := by
  have hP₀ : P₀ ≠ ⊥ := by
    intro h
    have := D.rank₀
    rw [h] at this
    simp at this
  have hP₁ : P₁ ≠ ⊥ := by
    intro h
    have := D.rank₁
    rw [h] at this
    simp at this
  obtain ⟨e₀, he₀, he₀0, hze₀⟩ := exists_eigenvector h3 D.nd₀ hP₀ D.stab₀ D.norm₀ hl
  obtain ⟨e₁, he₁, he₁0, hze₁⟩ := exists_eigenvector h3 D.nd₁ hP₁ D.stab₁ D.norm₁ (other_root hl)
  have o01 : spForm 2 K e₀ e₁ = 0 := D.orth e₀ he₀ e₁ he₁
  have o10 : spForm 2 K e₁ e₀ = 0 := by rw [← spForm_isAlt.neg_eq e₀ e₁, o01, neg_zero]
  have a0 : spForm 2 K e₀ e₀ = 0 := spForm_isAlt e₀
  have a1 : spForm 2 K e₁ e₁ = 0 := spForm_isAlt e₁
  refine ⟨e₀, he₀, e₁, he₁, ?_, ?_⟩
  · simp only [map_add, hze₀, hze₁, map_smul, LinearMap.add_apply, o01, o10, a0, a1, smul_eq_mul,
      mul_zero, add_zero]
  · obtain ⟨y, hy, hy0⟩ : ∃ y ∈ P₀, spForm 2 K e₀ y ≠ 0 := by
      by_contra h
      push Not at h
      exact he₀0 (congrArg Subtype.val (D.nd₀.1 ⟨e₀, he₀⟩ fun y => h y y.2))
    have hyv : spForm 2 K y e₀ ≠ 0 := fun h => hy0 (by
      rw [← neg_eq_zero, spForm_isAlt.neg_eq]
      exact h)
    refine ⟨y, hy, ?_⟩
    have hlm : l * (-1 - l) = 1 := by linear_combination (-1 : K) * hl
    have hv1 : (l * (-1 - l) - 1) • e₁ = 0 := by rw [sub_eq_zero.2 hlm, zero_smul]
    have hexpr : spForm 2 K y e₀ • e₁ + spForm 2 K y (spEnd z e₀) • spEnd z e₁ +
        spForm 2 K y (spEnd z (spEnd z e₀)) • spEnd z (spEnd z e₁) =
        (3 * spForm 2 K y e₀) • e₁ := by
      simp only [hze₀, hze₁, map_smul, smul_eq_mul]
      linear_combination (norm := module) (spForm 2 K y e₀ * (l * (-1 - l) + 2)) • hv1
    rw [hexpr]
    exact smul_ne_zero (mul_ne_zero h3 hyv) he₁0

theorem linearIndependent_of_nonsplit (hns : ∀ l : K, l ^ 2 + l + 1 ≠ 0) {z : StatedSp 2 K}
    {P : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hnorm : ∀ v ∈ P, v + spEnd z v + spEnd z (spEnd z v) = 0) {w : Fin 2 ⊕ Fin 2 → K}
    (hw : w ∈ P) (hw0 : w ≠ 0) : LinearIndependent K ![w, spEnd z w] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ht : t = 0 := by
    by_contra ht
    have hzw : spEnd z w = (-s / t) • w := by
      have h1 : t • spEnd z w = (-s) • w := by linear_combination (norm := module) hst
      calc spEnd z w = t⁻¹ • (t • spEnd z w) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = (-s / t) • w := by rw [h1, smul_smul, div_eq_inv_mul]
    have hn := hnorm w hw
    rw [hzw, map_smul, hzw] at hn
    have h0 : (1 + (-s / t) + (-s / t) * (-s / t)) • w = 0 := by
      linear_combination (norm := module) hn
    refine hns (-s / t) ?_
    have := (smul_eq_zero.mp h0).resolve_right hw0
    linear_combination this
  refine ⟨?_, ht⟩
  rw [ht, zero_smul, add_zero] at hst
  exact (smul_eq_zero.mp hst).resolve_right hw0

theorem form_ne_zero_of_nonsplit (hns : ∀ l : K, l ^ 2 + l + 1 ≠ 0) {z : StatedSp 2 K}
    {P : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hnd : ((spForm 2 K).restrict P).Nondegenerate)
    (hrank : Module.finrank K P = 2) (hstab : ∀ v ∈ P, spEnd z v ∈ P)
    (hnorm : ∀ v ∈ P, v + spEnd z v + spEnd z (spEnd z v) = 0) {w : Fin 2 ⊕ Fin 2 → K}
    (hw : w ∈ P) (hw0 : w ≠ 0) : spForm 2 K w (spEnd z w) ≠ 0 := by
  intro h0
  have hli := linearIndependent_of_nonsplit hns hnorm hw hw0
  have hS := span_pair_eq_of_rank_two hrank hw (hstab w hw) hli
  refine hw0 (congrArg Subtype.val (hnd.1 ⟨w, hw⟩ fun y => ?_))
  have hy : (y : Fin 2 ⊕ Fin 2 → K) ∈ Submodule.span K {w, spEnd z w} := by
    rw [hS]
    exact y.2
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.1 hy
  change spForm 2 K w y = 0
  rw [← hst, map_add, map_smul, map_smul, spForm_isAlt w, h0, smul_zero, smul_zero, add_zero]

theorem exists_isotropic_nonsplit [Finite K] {H : Subgroup (StatedSp 2 K)} {z : StatedSp 2 K}
    {P₀ P₁ : Submodule K (Fin 2 ⊕ Fin 2 → K)} (h3 : (3 : K) ≠ 0) (D : MixData H z P₀ P₁)
    (hns : ∀ l : K, l ^ 2 + l + 1 ≠ 0) :
    ∃ u₀ ∈ P₀, ∃ u₁ ∈ P₁, spForm 2 K (u₀ + u₁) (spEnd z (u₀ + u₁)) = 0 ∧
      ∃ v ∈ P₀, spForm 2 K v u₀ • u₁ + spForm 2 K v (spEnd z u₀) • spEnd z u₁ +
        spForm 2 K v (spEnd z (spEnd z u₀)) • spEnd z (spEnd z u₁) ≠ 0 := by
  obtain ⟨x, hx0, hx⟩ := exists_nonzero_zero_quadratic (K := K) (σ := Fin 2 ⊕ Fin 2) (by simp)
    (gram K 2 * ((z : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
  have hxz : spForm 2 K x (spEnd z x) = 0 := by
    rw [spForm_apply, spEnd_apply, Matrix.mulVec_mulVec]
    exact hx
  have hxmem : x ∈ P₀ ⊔ P₁ := by rw [D.sup]; trivial
  obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Submodule.mem_sup.1 hxmem
  have c01 : spForm 2 K x₀ (spEnd z x₁) = 0 := D.orth x₀ hx₀ _ (D.stab₁ x₁ hx₁)
  have c10 : spForm 2 K x₁ (spEnd z x₀) = 0 := by
    rw [← spForm_isAlt.neg_eq (spEnd z x₀) x₁, D.orth _ (D.stab₀ x₀ hx₀) x₁ hx₁, neg_zero]
  have hsum : spForm 2 K x₀ (spEnd z x₀) + spForm 2 K x₁ (spEnd z x₁) = 0 := by
    have := hxz
    simp only [map_add, LinearMap.add_apply, c01, c10, add_zero, zero_add] at this
    exact this
  have hx₀0 : x₀ ≠ 0 := by
    intro h
    have hx₁0 : x₁ ≠ 0 := fun h1 => hx0 (by rw [h, h1, add_zero])
    refine form_ne_zero_of_nonsplit hns D.nd₁ D.rank₁ D.stab₁ D.norm₁ hx₁ hx₁0 ?_
    simpa [h] using hsum
  have hx₁0 : x₁ ≠ 0 := by
    intro h
    refine form_ne_zero_of_nonsplit hns D.nd₀ D.rank₀ D.stab₀ D.norm₀ hx₀ hx₀0 ?_
    simpa [h] using hsum
  refine ⟨x₀, hx₀, x₁, hx₁, hxz, ?_⟩
  obtain ⟨y, hy, hy0⟩ : ∃ y ∈ P₀, spForm 2 K x₀ y ≠ 0 := by
    by_contra h
    push Not at h
    exact hx₀0 (congrArg Subtype.val (D.nd₀.1 ⟨x₀, hx₀⟩ fun y => h y y.2))
  have hyv : spForm 2 K y x₀ ≠ 0 := fun h => hy0 (by
    rw [← neg_eq_zero, spForm_isAlt.neg_eq]
    exact h)
  refine ⟨y, hy, fun hcross => ?_⟩
  have hn₀ := D.norm₀ x₀ hx₀
  have hn₁ := D.norm₁ x₁ hx₁
  have hα : spForm 2 K y x₀ + spForm 2 K y (spEnd z x₀) + spForm 2 K y (spEnd z (spEnd z x₀)) =
      0 := by
    have := congrArg (spForm 2 K y) hn₀
    simpa only [map_add, map_zero] using this
  have hcr : (spForm 2 K y x₀ - spForm 2 K y (spEnd z (spEnd z x₀))) • x₁ +
      (spForm 2 K y (spEnd z x₀) - spForm 2 K y (spEnd z (spEnd z x₀))) • spEnd z x₁ = 0 := by
    linear_combination (norm := module) hcross - spForm 2 K y (spEnd z (spEnd z x₀)) • hn₁
  obtain ⟨h1, h2⟩ := (LinearIndependent.pair_iff.mp
    (linearIndependent_of_nonsplit hns D.norm₁ hx₁ hx₁0)) _ _ hcr
  have h3α : (3 : K) * spForm 2 K y x₀ = 0 := by linear_combination hα - h2 + 2 * h1
  exact hyv ((mul_eq_zero.mp h3α).resolve_left h3)

theorem exists_mixed_center [Finite K] {H : Subgroup (StatedSp 2 K)} {z : StatedSp 2 K}
    {P₀ P₁ : Submodule K (Fin 2 ⊕ Fin 2 → K)} (h3 : (3 : K) ≠ 0)
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) (D : MixData H z P₀ P₁) :
    ∃ y₀ ∈ P₀, ∃ y₁ ∈ P₁, y₀ ≠ 0 ∧ y₁ ≠ 0 ∧ TransCenter H (y₀ + y₁) := by
  by_cases hsp : ∃ l : K, l ^ 2 + l + 1 = 0
  · obtain ⟨l, hl⟩ := hsp
    obtain ⟨u₀, hu₀, u₁, hu₁, hiso, hstar⟩ := exists_isotropic_split h3 D hl
    exact mixed_center_of_isotropic D hK hu₀ hu₁ hiso hstar
  · push Not at hsp
    obtain ⟨u₀, hu₀, u₁, hu₁, hiso, hstar⟩ := exists_isotropic_nonsplit h3 D hsp
    exact mixed_center_of_isotropic D hK hu₀ hu₁ hiso hstar

end Cases



end CFSG.LieType.SeitzGeneration
