module

public import CFSG.ClassicalInvolution.Phan.PhanS8Q4Count
import CFSG.ClassicalInvolution.Phan.PhanS8Q3Ternary
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q

open CFSG.ClassicalInvolution.PhanB3.S.Std Matrix

variable {K : Type} [Field K] {M : Model K}

theorem exists_pair_ne_of_expand {G : Vec K → Vec K → K} (hG : Sesq M G) (e : Fin 3 → Vec K)
    (d d' : Fin 3 → K) (h : G (∑ i, d i • e i) (∑ i, d' i • e i) ≠ 0) :
    ∃ i j : Fin 3, G (e i) (e j) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  rw [hG.expand_three]
  simp [hcon]

theorem exists_good_conic_pt [Finite K] (hq : 3 ≤ M.q) {x : Fin 4 → Vec K} (hx : GramInj M x)
    {m : ℕ} {Φ : Fin m → Vec K → Vec K → K} (hΦ : ∀ k, Sesq M (Φ k))
    (hw : ∀ k, ∃ u ∈ orthSpan M (Set.range x), ∃ u' ∈ orthSpan M (Set.range x), Φ k u u' ≠ 0)
    (hcard : m * (2 * M.q + 2) < Nat.card K) :
    ∃ p ∈ orthSpan M (Set.range x), bf M p p = 0 ∧ ∀ k, Φ k p p ≠ 0 := by
  classical
  set Z := orthSpan M (Set.range x) with hZdef
  have hZ3 : Module.finrank K Z = 3 := hx.finrank_orth
  let b : Module.Basis (Fin 3) K Z := Module.finBasisOfFinrankEq K Z hZ3
  let emb : (Fin 3 → K) →ₗ[K] Vec K := Fintype.linearCombination K (fun i => ((b i : Z) : Vec K))
  have emb_apply : ∀ z, emb z = ∑ i, z i • ((b i : Z) : Vec K) := fun z => by
    simp [emb, Fintype.linearCombination_apply]
  have emb_mem : ∀ z, emb z ∈ Z := fun z => by
    rw [emb_apply]
    exact Z.sum_mem fun i _ => Z.smul_mem _ (b i).2
  let N : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => bf M ((b i : Z) : Vec K) (b j)
  have hNs : Nᵀ = N := by
    ext i j
    simp [N, bf_comm M]
  have bf_emb : ∀ z z', bf M (emb z) (emb z') = Bf N z z' := by
    intro z z'
    rw [emb_apply, emb_apply, bf_sum_left, Bf_def]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bf_comm, bf_sum_left, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [N, bf_comm M]
    ring
  have emb_surj : ∀ u ∈ Z, ∃ z, emb z = u := by
    intro u hu
    refine ⟨fun i => b.repr ⟨u, hu⟩ i, ?_⟩
    have h := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [emb_apply]
    exact h
  have emb_inj : ∀ z, emb z = 0 → z = 0 := by
    intro z hz
    have : ∑ i, z i • (b i) = (0 : Z) := by
      apply Subtype.ext
      rw [emb_apply] at hz
      simpa using hz
    exact funext fun i => (Fintype.linearIndependent_iff.1 b.linearIndependent) z this i
  have hN : N.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hz : emb c = 0 := by
      refine hx.eq_zero_of_orth (emb_mem c) fun z' hz' => ?_
      obtain ⟨d, rfl⟩ := emb_surj z' hz'
      rw [bf_emb, Bf_comm' N hNs]
      simp [Bf, hc]
    exact hc0 (emb_inj c hz)
  obtain ⟨y, v, a, γ, hγ, hsing, hspan⟩ :=
    exists_conic_param M.two_ne N hNs hN
  set c₀ : Vec K := emb y with hc₀
  set c₁ : Vec K := emb v with hc₁
  set c₂ : Vec K := γ • emb a with hc₂
  have hconic : ∀ μ, conicPt c₀ c₁ c₂ μ = emb (y + μ • v + (γ * μ ^ 2) • a) := by
    intro μ
    simp only [conicPt, hc₀, hc₁, hc₂, map_add, map_smul, smul_smul]
    rw [mul_comm (μ ^ 2) γ]
  have hw' : ∀ k, ∃ i j : Fin 3, Φ k (cs c₀ c₁ c₂ i) (cs c₀ c₁ c₂ j) ≠ 0 := by
    intro k
    obtain ⟨u, hu, u', hu', hne⟩ := hw k
    obtain ⟨z, rfl⟩ := emb_surj u hu
    obtain ⟨z', rfl⟩ := emb_surj u' hu'
    obtain ⟨e₁, e₂, e₃, rfl⟩ := hspan z
    obtain ⟨f₁, f₂, f₃, rfl⟩ := hspan z'
    refine exists_pair_ne_of_expand (hΦ k) (cs c₀ c₁ c₂) ![e₁, e₂, e₃ * γ⁻¹] ![f₁, f₂, f₃ * γ⁻¹] ?_
    convert hne using 2
    · simp only [Fin.sum_univ_three, cs_zero, cs_one, cs_two, hc₀, hc₁, hc₂, map_add, map_smul,
        smul_smul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [mul_assoc, inv_mul_cancel₀ hγ, mul_one]
    · simp only [Fin.sum_univ_three, cs_zero, cs_one, cs_two, hc₀, hc₁, hc₂, map_add, map_smul,
        smul_smul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [mul_assoc, inv_mul_cancel₀ hγ, mul_one]
  obtain ⟨μ, hμ⟩ := exists_good_param hq hΦ hw' hcard
  refine ⟨conicPt c₀ c₁ c₂ μ, ?_, ?_, hμ⟩
  · rw [hconic]
    exact emb_mem _
  · rw [hconic, bf_emb]
    exact hsing μ

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q
