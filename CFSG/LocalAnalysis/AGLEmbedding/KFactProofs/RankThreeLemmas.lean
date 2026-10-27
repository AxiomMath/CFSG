module

public import CFSG.LocalAnalysis.AGLEmbedding.CoverRankLift
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def alt3 {p : ℕ} (u : Fin 3 → ZMod p) : Matrix (Fin 3) (Fin 3) (ZMod p) :=
  !![0, u 0, u 1; -u 0, 0, u 2; -u 1, -u 2, 0]

theorem noAlt_three {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m : ℕ}
    (Ms : Fin m → Matrix (Fin 3) (Fin 3) (ZMod p))
    (h : ∀ u : Fin 3 → ZMod p, (∀ j, (Ms j).transpose * alt3 u * Ms j = alt3 u) → u = 0) :
    ∀ B : Matrix (Fin 3) (Fin 3) (ZMod p), B.transpose = -B →
      (∀ j, (Ms j).transpose * B * Ms j = B) → B = 0 := by
  intro B hB hinv
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have hdiag : ∀ i, B i i = 0 := by
    intro i
    have := congrFun (congrFun hB i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    have h3 : (2 : ZMod p) * B i i = 0 := by
      rw [two_mul]; nth_rewrite 2 [this]; exact add_neg_cancel _
    exact (mul_eq_zero.1 h3).resolve_left h2
  have hsymm : ∀ i j, B j i = -B i j := fun i j => by
    have := congrFun (congrFun hB i) j
    simpa using this
  have hBu : B = alt3 ![B 0 1, B 0 2, B 1 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [alt3, hdiag]
    · exact hsymm 0 1
    · exact hsymm 0 2
    · exact hsymm 1 2
  have hu : ![B 0 1, B 0 2, B 1 2] = 0 := h _ (fun j => hBu ▸ hinv j)
  rw [hBu, hu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alt3]

theorem alt3_00 {p : ℕ} (u : Fin 3 → ZMod p) : alt3 u 0 0 = 0 := by simp [alt3]

theorem alt3_01 {p : ℕ} (u : Fin 3 → ZMod p) : alt3 u 0 1 = u 0 := by simp [alt3]

theorem alt3_02 {p : ℕ} (u : Fin 3 → ZMod p) : alt3 u 0 2 = u 1 := by simp [alt3]

theorem alt3_10 {p : ℕ} (u : Fin 3 → ZMod p) : alt3 u 1 0 = -u 0 := by simp [alt3]

theorem alt3_11 {p : ℕ} (u : Fin 3 → ZMod p) : alt3 u 1 1 = 0 := by simp [alt3]

theorem alt3_12 {p : ℕ} (u : Fin 3 → ZMod p) : alt3 u 1 2 = u 2 := by simp [alt3]

theorem alt3_20 {p : ℕ} (u : Fin 3 → ZMod p) : alt3 u 2 0 = -u 1 := by simp [alt3]

theorem alt3_21 {p : ℕ} (u : Fin 3 → ZMod p) : alt3 u 2 1 = -u 2 := by simp [alt3]

theorem alt3_22 {p : ℕ} (u : Fin 3 → ZMod p) : alt3 u 2 2 = 0 := by simp [alt3]

theorem mem_normalizer_closure_of_conj {G : Type*} [Group G] {s : Set G} {g : G} {n : ℕ}
    (hn : 0 < n) (hg : g ^ n = 1) (h : ∀ x ∈ s, g * x * g⁻¹ ∈ Subgroup.closure s) :
    g ∈ Subgroup.normalizer ((Subgroup.closure s : Subgroup G) : Set G) := by
  have hconj : ∀ x ∈ Subgroup.closure s, g * x * g⁻¹ ∈ Subgroup.closure s := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact h x hx
    | one => simp
    | mul x y _ _ hx hy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]; exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]; exact Subgroup.inv_mem _ hx
  have hconjpow : ∀ (j : ℕ), ∀ x ∈ Subgroup.closure s,
      g ^ j * x * (g ^ j)⁻¹ ∈ Subgroup.closure s := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      have e : g ^ (j + 1) * x * (g ^ (j + 1))⁻¹ = g * (g ^ j * x * (g ^ j)⁻¹) * g⁻¹ := by group
      rw [e]; exact hconj _ (ih x hx)
  have hinv : g⁻¹ = g ^ (n - 1) := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← pow_succ, Nat.sub_add_cancel hn, hg]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hconj x, fun hx => ?_⟩
  have h1 := hconjpow (n - 1) _ hx
  rw [← hinv] at h1
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1

theorem isPGroup_closure_insert {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {q : G} {s : Set G}
    (hs : IsPGroup p (Subgroup.closure s)) (hpow : q ^ p ∈ Subgroup.closure s)
    (hnorm : ∀ x ∈ s, q * x * q⁻¹ ∈ Subgroup.closure s) :
    IsPGroup p (Subgroup.closure (insert q s)) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨m, hm⟩ := hs ⟨q ^ p, hpow⟩
  have hqm : q ^ (p ^ (m + 1)) = 1 := by
    have h := congrArg Subtype.val hm
    simpa [pow_succ', pow_mul] using h
  have hqn := mem_normalizer_closure_of_conj (pow_pos hp _) hqm hnorm
  have hz : IsPGroup p (Subgroup.zpowers q) := by
    intro g
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨m + 1, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hqm, one_zpow]
  have hcl : Subgroup.closure (insert q s) = Subgroup.zpowers q ⊔ Subgroup.closure s := by
    rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure]
  rw [hcl]
  exact hz.to_sup_of_normal_right' hs (Subgroup.zpowers_le.2 hqn)

theorem le_pRank_of_indep {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) {n : ℕ}
    (a : Fin n → X) (hcomm : ∀ i j, a i * a j = a j * a i) (hpow : ∀ i, a i ^ p = 1)
    (hind : ∀ c : Fin n → ZMod p,
      ((List.finRange n).map fun k => a k ^ (c k).val).prod = 1 → c = 0)
    {H : Subgroup X} (hH : ∀ i, a i ∈ H) : n ≤ Open.pRank p H := by
  let D : ModuleSpec X p :=
    { n := n, m := 0, a := a, g := fun j => j.elim0, M := fun j => j.elim0, comm := hcomm,
      pow := hpow, indep := hind, act := fun j => j.elim0 }
  have hEA : Open.IsElemAbelian p D.span :=
    ⟨inferInstance, fun x hx => D.pow_eq_one_of_mem hx⟩
  refine le_pRank_of_pow_le_card hp ?_ hEA (D.card_span hp).ge
  exact (Subgroup.closure_le H).2 (by rintro _ ⟨i, rfl⟩; exact hH i)

end CFSG.AGLEmbedding
