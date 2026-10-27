module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.RankThree.PartOne.CTP
open scoped commutatorElement

section Field

theorem mem_of_quadratic {K : Type} [Field K] [Finite K] {k : Subfield K} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p) {x α β : K}
    (hα : α ∈ k) (hβ : β ∈ k) (hx : x ^ 2 + α * x + β = 0) : x ∈ k := by
  by_contra hxk
  have hfin : Module.finrank k K = p := by
    have h := Module.natCard_eq_pow_finrank (K := k) (V := K)
    have h2 : 2 ≤ Nat.card k := Finite.one_lt_card
    rw [hK] at h
    exact (Nat.pow_right_injective h2 h).symm
  let F : IntermediateField k K := IntermediateField.adjoin k {x}
  let q : Polynomial k := Polynomial.X ^ 2 + Polynomial.C ⟨α, hα⟩ * Polynomial.X +
    Polynomial.C ⟨β, hβ⟩
  have hqm : q.Monic := by
    unfold q
    monicity!
  have hq0 : Polynomial.aeval x q = 0 := by
    simp only [q, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    exact hx
  have hint : IsIntegral k x := ⟨q, hqm, by
    rw [← Polynomial.aeval_def]; exact hq0⟩
  have hdeg : Module.finrank k F ≤ 2 := by
    rw [IntermediateField.adjoin.finrank hint]
    have h1 := minpoly.degree_le_of_ne_zero k x hqm.ne_zero hq0
    have h2 : q.natDegree = 2 := by
      unfold q
      compute_degree!
    have := Polynomial.natDegree_le_natDegree h1
    omega
  have hdvd : Module.finrank k F ∣ p := by
    have := IntermediateField.finrank_dvd_of_le_right (K := k) (L := K) (F := F) (E := ⊤) le_top
    rwa [IntermediateField.finrank_top', hfin] at this
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h2
  · have hF : F = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1
    have hxF : x ∈ F := IntermediateField.subset_adjoin k {x} rfl
    rw [hF] at hxF
    obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.mp hxF
    exact hxk y.2
  · have := hdeg
    have h3 := hp.two_le
    omega

end Field

namespace RootPair

section Basic

variable {F : Type} [Field F]

theorem u2_pow (n : ℕ) (a : F) : u2 a ^ n = u2 (n * a) := by
  induction n with
  | zero => simp [u2_zero]
  | succ n ih => rw [pow_succ, ih, ← u2_add]; congr 1; push_cast; ring

theorem l2_pow (n : ℕ) (a : F) : l2 a ^ n = l2 (n * a) := by
  induction n with
  | zero => simp [l2_zero]
  | succ n ih => rw [pow_succ, ih, ← l2_add]; congr 1; push_cast; ring

theorem u2_pow_ringChar (a : F) : u2 a ^ ringChar F = 1 := by
  rw [u2_pow, CharP.cast_eq_zero (R := F) (ringChar F), zero_mul, u2_zero]

theorem l2_pow_ringChar (a : F) : l2 a ^ ringChar F = 1 := by
  rw [l2_pow, CharP.cast_eq_zero (R := F) (ringChar F), zero_mul, l2_zero]

theorem center_offDiag {g : SpecialLinearGroup (Fin 2) F}
    (hg : g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  rw [← hr]
  simp [Matrix.scalar_apply]

theorem mkPSL_eq_one_iff (g : SpecialLinearGroup (Fin 2) F) :
    mkPSL F g = 1 ↔ g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  rw [mkPSL, QuotientGroup.mk'_apply]
  exact QuotientGroup.eq_one_iff g

theorem mkPSL_u2_injective (a : F) (ha : a ≠ 0) :
    Function.Injective fun s : F => mkPSL F (u2 (s * a)) := by
  intro s s' h
  simp only at h
  have h1 : mkPSL F (u2 (s * a) * (u2 (s' * a))⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  rw [mkPSL_eq_one_iff] at h1
  have h2 := center_offDiag h1
  have h3 : u2 (s * a) * (u2 (s' * a))⁻¹ = u2 (s * a - s' * a) := by
    have : (u2 (s' * a))⁻¹ = u2 (-(s' * a)) := by
      rw [inv_eq_iff_mul_eq_one, ← u2_add]; simp [u2_zero]
    rw [this, ← u2_add]; congr 1; ring
  rw [h3] at h2
  simp [u2_coe] at h2
  have : (s - s') * a = 0 := by linear_combination h2
  rcases mul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h ha

theorem coe_l2_mul_u2 (a b : F) :
    ((l2 b * u2 a : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, a; b, 1 + a * b] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, u2_coe, l2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem mkPSL_u2_mul_l2_ne {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    mkPSL F (u2 a) * mkPSL F (l2 b) ≠ mkPSL F (l2 b) * mkPSL F (u2 a) := by
  intro h
  rw [← map_mul, ← map_mul] at h
  have h' : (u2 a * l2 b)⁻¹ * (l2 b * u2 a) ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) :=
    QuotientGroup.eq.mp h
  obtain ⟨r, hr2, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h'
  set z := (u2 a * l2 b)⁻¹ * (l2 b * u2 a) with hzdef
  have hz : u2 a * l2 b * z = l2 b * u2 a := by rw [hzdef, mul_inv_cancel_left]
  have e : ((u2 a * l2 b * z : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((l2 b * u2 a : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by rw [hz]
  rw [Matrix.SpecialLinearGroup.coe_mul (u2 a * l2 b) z, coe_u2_mul_l2, ← hr, coe_l2_mul_u2] at e
  have e01 := congrFun (congrFun e 0) 1
  have e00 := congrFun (congrFun e 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] at e01 e00
  have hr1 : r = 1 := by
    have : a * (r - 1) = 0 := by linear_combination e01
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h ha
    · linear_combination h
  subst hr1
  exact mul_ne_zero ha hb (by linear_combination e00)

end Basic

section Group

theorem mem_of_pow_eq_one_of_coprime_sup {G : Type*} [Group G] {N C : Subgroup G} [N.Normal]
    (hdisj : Disjoint N C) (hsup : N ⊔ C = ⊤) {ℓ : ℕ} (hℓ : Nat.Coprime ℓ (Nat.card C))
    {g : G} (hg : g ^ ℓ = 1) : g ∈ N := by
  have hg' : g ∈ N ⊔ C := hsup ▸ Subgroup.mem_top g
  obtain ⟨n, hn, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg'
  have hmk : ((n * c : G) : G ⧸ N) = (c : G ⧸ N) := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  have hq : ((c ^ ℓ : G) : G ⧸ N) = 1 := by
    rw [QuotientGroup.mk_pow, ← hmk, ← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one]
  have hcN : c ^ ℓ ∈ N := (QuotientGroup.eq_one_iff _).mp hq
  have hc1 : c ^ ℓ = 1 := Subgroup.disjoint_def.mp hdisj hcN (C.pow_mem hc ℓ)
  have hord : orderOf c = 1 := by
    have h1 : orderOf c ∣ ℓ := orderOf_dvd_of_pow_eq_one hc1
    have h2 : orderOf c ∣ Nat.card C := by
      have := orderOf_dvd_natCard (⟨c, hc⟩ : C)
      rwa [Subgroup.orderOf_mk] at this
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hℓ) h2
  rw [orderOf_eq_one_iff.mp hord, mul_one]
  exact hn

private theorem commutatorElement_mul_left' {G : Type*} [Group G] {a z : G}
    (hz : z ∈ Subgroup.center G) (b : G) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hzb : z * b = b * z := (Subgroup.mem_center_iff.mp hz b).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hzb]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem commutatorElement_mul_right' {G : Type*} [Group G] (a : G) {b z : G}
    (hz : z ∈ Subgroup.center G) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have hza : z * a⁻¹ = a⁻¹ * z := (Subgroup.mem_center_iff.mp hz a⁻¹).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [hza]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem eq_top_of_central_kernel_perfect {G M : Type*} [Group G] [Group M] [Group.IsPerfect G]
    (φ : G →* M) (hker : φ.ker ≤ Subgroup.center G) {R : Subgroup G}
    (hR : φ.range ≤ R.map φ) : R = ⊤ := by
  have key : ∀ g : G, ∃ r ∈ R, ∃ z ∈ Subgroup.center G, g = r * z := by
    intro g
    obtain ⟨r, hr, hrg⟩ := Subgroup.mem_map.mp (hR (MonoidHom.mem_range.mpr ⟨g, rfl⟩))
    refine ⟨r, hr, r⁻¹ * g, hker ?_, (mul_inv_cancel_left r g).symm⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hrg, inv_mul_cancel]
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := G), commutator_def,
    Subgroup.commutator_le]
  intro g₁ _ g₂ _
  obtain ⟨r₁, hr₁, z₁, hz₁, rfl⟩ := key g₁
  obtain ⟨r₂, hr₂, z₂, hz₂, rfl⟩ := key g₂
  rw [commutatorElement_mul_left' hz₁, commutatorElement_mul_right' r₁ hz₂,
    commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hr₁ hr₂) (inv_mem hr₁)) (inv_mem hr₂)

theorem alt4_pow : ∀ g : alternatingGroup (Fin 4),
    g ^ 1 = 1 ∨ g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 4 = 1 ∨ g ^ 5 = 1 := by decide +kernel

theorem perm4_pow : ∀ g : Equiv.Perm (Fin 4),
    g ^ 1 = 1 ∨ g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 4 = 1 ∨ g ^ 5 = 1 := by decide +kernel

theorem alt5_pow : ∀ g : alternatingGroup (Fin 5),
    g ^ 1 = 1 ∨ g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 4 = 1 ∨ g ^ 5 = 1 := by decide +kernel

end Group

section Trace

variable {F : Type} [Field F]

theorem coe_pow_u2_mul_l2 (p q : F) (n : ℕ) :
    (((u2 p * l2 q) ^ n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (!![1 + p * q, p; q, 1] : Matrix (Fin 2) (Fin 2) F) ^ n := by
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_u2_mul_l2]

theorem pow_offDiag (p q : F) :
    ((!![1 + p * q, p; q, 1] : Matrix (Fin 2) (Fin 2) F) ^ 2) 0 1 = p * (2 + p * q) ∧
    ((!![1 + p * q, p; q, 1] : Matrix (Fin 2) (Fin 2) F) ^ 3) 0 1 = p * ((2 + p * q) ^ 2 - 1) ∧
    ((!![1 + p * q, p; q, 1] : Matrix (Fin 2) (Fin 2) F) ^ 4) 0 1 =
      p * ((2 + p * q) ^ 3 - 2 * (2 + p * q)) ∧
    ((!![1 + p * q, p; q, 1] : Matrix (Fin 2) (Fin 2) F) ^ 5) 0 1 =
      p * ((2 + p * q) ^ 4 - 3 * (2 + p * q) ^ 2 + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [pow_succ] <;> ring

theorem trace_quadratic_of_pow_central {p q : F} (hp : p ≠ 0) {n : ℕ} (hn1 : 1 ≤ n) (hn5 : n ≤ 5)
    (h : (u2 p * l2 q) ^ n ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) :
    (2 + p * q) ^ 2 + 0 * (2 + p * q) + 0 = 0 ∨ (2 + p * q) ^ 2 + 0 * (2 + p * q) + (-1) = 0 ∨
      (2 + p * q) ^ 2 + 0 * (2 + p * q) + (-2) = 0 ∨
      (2 + p * q) ^ 2 + (-1) * (2 + p * q) + (-1) = 0 ∨
      (2 + p * q) ^ 2 + 1 * (2 + p * q) + (-1) = 0 := by
  have h01 := center_offDiag h
  rw [coe_pow_u2_mul_l2] at h01
  obtain ⟨e2, e3, e4, e5⟩ := pow_offDiag p q
  interval_cases n
  · simp at h01
    exact absurd h01 hp
  · rw [e2] at h01
    rcases mul_eq_zero.mp h01 with h1 | h1
    · exact absurd h1 hp
    · left; rw [h1]; ring
  · rw [e3] at h01
    rcases mul_eq_zero.mp h01 with h1 | h1
    · exact absurd h1 hp
    · right; left; linear_combination h1
  · rw [e4] at h01
    rcases mul_eq_zero.mp h01 with h1 | h1
    · exact absurd h1 hp
    · have h2 : (2 + p * q) * ((2 + p * q) ^ 2 - 2) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · left; rw [h3]; ring
      · right; right; left; linear_combination h3
  · rw [e5] at h01
    rcases mul_eq_zero.mp h01 with h1 | h1
    · exact absurd h1 hp
    · have h2 : ((2 + p * q) ^ 2 - (2 + p * q) - 1) * ((2 + p * q) ^ 2 + (2 + p * q) - 1) = 0 := by
        linear_combination h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · right; right; right; left; linear_combination h3
      · right; right; right; right; linear_combination h3

theorem trace_l2 (b : F) :
    Matrix.trace ((l2 b : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 2 := by
  rw [l2_coe, Matrix.trace_fin_two]
  simp [one_add_one_eq_two]

theorem trace_u2 (a : F) :
    Matrix.trace ((u2 a : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 2 := by
  rw [u2_coe, Matrix.trace_fin_two]
  simp [one_add_one_eq_two]

theorem trace_l2_mul_u2_gen (p q : F) :
    Matrix.trace ((l2 q * u2 p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      2 + p * q := by
  rw [coe_l2_mul_u2, Matrix.trace_fin_two]
  simp
  ring

theorem trace_pair_gen (p q p' q' : F) :
    Matrix.trace ((u2 p * l2 q * (u2 p' * l2 q') : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = 2 + (p + p') * (q + q') + p * q * (p' * q') := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_u2_mul_l2, coe_u2_mul_l2, Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

end Trace

section Aux

@[expose] def uHom {F : Type} [Field F] (k : Subfield F) (a : F) :
    Multiplicative k →* SpecialLinearGroup (Fin 2) F where
  toFun s := u2 ((s.toAdd : F) * a)
  map_one' := by simp [u2_zero]
  map_mul' s s' := by
    rw [← u2_add]
    congr 1
    simp [add_mul]

theorem exists_ne_zero_one {F : Type} [Field F] [Finite F] (k : Subfield F)
    (hk3 : 3 ≤ Nat.card k) : ∃ ω ∈ k, ω ≠ 0 ∧ ω ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsub : (Set.univ : Set k) ⊆ {0, 1} := by
    intro x _
    by_cases hx : (x : F) = 0
    · left; exact Subtype.ext hx
    · right; exact Subtype.ext (hcon x x.2 hx)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ] at h1
  have h2 : ({0, 1} : Set k).ncard ≤ 2 :=
    (Set.ncard_insert_le (0 : k) {1}).trans (by simp)
  omega

theorem mul_mem_of_pow_central {F : Type} [Field F] [Finite F] {k : Subfield F} {d : ℕ}
    (hd : d.Prime) (hd2 : d ≠ 2) (hK : Nat.card F = Nat.card k ^ d) {α β : F} (hα : α ≠ 0)
    (h : ∃ n, 1 ≤ n ∧ n ≤ 5 ∧
      (u2 α * l2 β) ^ n ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) : α * β ∈ k := by
  obtain ⟨n, hn1, hn5, hn⟩ := h
  have hq := trace_quadratic_of_pow_central hα hn1 hn5 hn
  have ht : (2 + α * β) ∈ k := by
    rcases hq with h | h | h | h | h
    · exact mem_of_quadratic hd hd2 hK (α := 0) (β := 0) k.zero_mem k.zero_mem h
    · exact mem_of_quadratic hd hd2 hK (α := 0) (β := -1) k.zero_mem (k.neg_mem k.one_mem) h
    · exact mem_of_quadratic hd hd2 hK (α := 0) (β := -2) k.zero_mem
        (k.neg_mem (ofNat_mem k 2)) h
    · exact mem_of_quadratic hd hd2 hK (α := -1) (β := -1) (k.neg_mem k.one_mem)
        (k.neg_mem k.one_mem) h
    · exact mem_of_quadratic hd hd2 hK (α := 1) (β := -1) k.one_mem (k.neg_mem k.one_mem) h
  have : α * β = (2 + α * β) - 2 := by ring
  rw [this]
  exact k.sub_mem ht (ofNat_mem k 2)

theorem pow_central_of_small {F : Type} [Field F] {a b : F}
    {M : Subgroup (SpecialLinearGroup (Fin 2) F)} (hx : u2 a ∈ M) (hy : l2 b ∈ M) {G₀ : Type}
    [Group G₀] (e : M.map (mkPSL F) ≃* G₀)
    (hG : ∀ g : G₀, g ^ 1 = 1 ∨ g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 4 = 1 ∨ g ^ 5 = 1) :
    ∃ n, 1 ≤ n ∧ n ≤ 5 ∧
      (u2 a * l2 b) ^ n ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  let z : M.map (mkPSL F) := ⟨mkPSL F (u2 a * l2 b), Subgroup.mem_map_of_mem _ (M.mul_mem hx hy)⟩
  have key : ∀ n, (e z) ^ n = 1 →
      (u2 a * l2 b) ^ n ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
    intro n hn
    have h1 : z ^ n = 1 := by
      apply e.injective
      rw [map_pow, hn, map_one]
    have h2 : mkPSL F ((u2 a * l2 b) ^ n) = 1 := by
      have := congrArg Subtype.val h1
      simpa [z, map_pow] using this
    exact (mkPSL_eq_one_iff _).mp h2
  rcases hG (e z) with h | h | h | h | h
  · exact ⟨1, le_rfl, by norm_num, key 1 h⟩
  · exact ⟨2, by norm_num, by norm_num, key 2 h⟩
  · exact ⟨3, by norm_num, by norm_num, key 3 h⟩
  · exact ⟨4, by norm_num, by norm_num, key 4 h⟩
  · exact ⟨5, by norm_num, by norm_num, key 5 h⟩

end Aux

end RootPair

section Dickson

open CFSG.Glauberman.Dickson RootPair

namespace RootPair

theorem witness_eq_top_pair {F : Type} [Field F] [Finite F] {k : Subfield F} {d : ℕ}
    (hd : d.Prime) (hK : Nat.card F = Nat.card k ^ d) (hk3 : 3 ≤ Nat.card k) {α β : F}
    (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : α * β ∉ k)
    {M : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hu : ∀ t ∈ k, u2 (t * α) ∈ M) (hl : ∀ s ∈ k, l2 (s * β) ∈ M) {ℓ m : ℕ}
    (W : SubfieldConjugacyWitness ℓ m (M.map (mkPSL F))) : W.K = ⊤ := by
  have hc0 : α * β ≠ 0 := mul_ne_zero hα hβ
  suffices h : k ≤ W.K ∧ α * β ∈ W.K by
    rcases subfield_eq_or_eq_top h.1 hd hK with h1 | h1
    · exact absurd (h1 ▸ h.2) hαβ
    · exact h1
  have hxα : u2 α ∈ M := by simpa using hu 1 k.one_mem
  have hlβ : l2 β ∈ M := by simpa using hl 1 k.one_mem
  by_cases h2 : (2 : F) = 0
  ·
    have : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    have key : ∀ x y : F, u2 x ∈ M → u2 y ∈ M → x ≠ 0 → (y / x) ^ 2 ∈ W.K := by
      intro x y hx hy hx0
      have hAM : u2 x * l2 β ∈ M := M.mul_mem hx hlβ
      have hBM : u2 y * l2 β * u2 (x + y) ∈ M :=
        M.mul_mem (M.mul_mem hy hlβ) (by rw [u2_add]; exact M.mul_mem hx hy)
      have hxb : x * β ≠ 0 := mul_ne_zero hx0 hβ
      have h := normalizedTrace_mem_subfield (M.map (mkPSL F)) W
        ⟨mkPSL F (u2 x * l2 β), Subgroup.mem_map_of_mem _ hAM⟩
        ⟨mkPSL F (u2 y * l2 β * u2 (x + y)), Subgroup.mem_map_of_mem _ hBM⟩
        (u2 x * l2 β) (u2 y * l2 β * u2 (x + y)) rfl rfl
        (by rw [trace_u2_mul_l2]; exact hxb)
        (by rw [trace_u2_mul_l2_mul_u2]; exact hxb)
      rw [trace_pair, trace_u2_mul_l2, trace_u2_mul_l2_mul_u2] at h
      have : y ^ 2 * β ^ 2 / (x * β * (x * β)) = (y / x) ^ 2 := by
        field_simp
      rwa [this] at h
    have hkW : k ≤ W.K := by
      intro c hc
      by_cases hc0 : c = 0
      · rw [hc0]
        exact W.K.zero_mem
      · have h := key α (c * α) hxα (hu c hc) hα
        have hc' : c * α / α = c := by field_simp
        rw [hc'] at h
        exact mem_subfield_of_sq_mem W.K h
    refine ⟨hkW, ?_⟩
    obtain ⟨ω, hωk, hω0, hω1⟩ := exists_ne_zero_one k hk3
    have hωW : ω ∈ W.K := hkW hωk
    have hA : u2 α * l2 β ∈ M := M.mul_mem hxα hlβ
    have hB : u2 (ω * α) * l2 (ω * β) ∈ M := M.mul_mem (by simpa [mul_comm] using hu ω hωk)
      (by simpa [mul_comm] using hl ω hωk)
    have htrA : Matrix.trace ((u2 α * l2 β : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = α * β := trace_u2_mul_l2 α β
    have htrB : Matrix.trace ((u2 (ω * α) * l2 (ω * β) : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = ω ^ 2 * (α * β) := by
      rw [trace_u2_mul_l2]; ring
    have htrAB : Matrix.trace ((u2 α * l2 β * (u2 (ω * α) * l2 (ω * β)) :
        SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (1 + ω) ^ 2 * (α * β) + ω ^ 2 * (α * β) ^ 2 := by
      rw [trace_pair_gen]
      linear_combination (CharTwo.two_eq_zero : (2 : F) = 0)
    have hω1' : 1 + ω ≠ 0 := by
      intro h
      apply hω1
      have : ω = -1 := by linear_combination h
      rw [this]
      exact CharTwo.neg_eq 1
    have h := normalizedTrace_mem_subfield (M.map (mkPSL F)) W
      ⟨mkPSL F (u2 α * l2 β), Subgroup.mem_map_of_mem _ hA⟩
      ⟨mkPSL F (u2 (ω * α) * l2 (ω * β)), Subgroup.mem_map_of_mem _ hB⟩
      (u2 α * l2 β) (u2 (ω * α) * l2 (ω * β)) rfl rfl
      (by rw [htrA]; exact hc0) (by rw [htrB]; exact mul_ne_zero (pow_ne_zero 2 hω0) hc0)
    rw [htrAB, htrA, htrB] at h
    have hN : ((1 + ω) ^ 2 * (α * β) + ω ^ 2 * (α * β) ^ 2) /
        (α * β * (ω ^ 2 * (α * β))) = (1 + ω) ^ 2 / (ω ^ 2 * (α * β)) + 1 := by
      field_simp
    rw [hN] at h
    have h1 : (1 + ω) ^ 2 / (ω ^ 2 * (α * β)) ∈ W.K := by
      have := W.K.sub_mem h W.K.one_mem
      simpa using this
    have h3 : (1 + ω) ^ 2 / ω ^ 2 ∈ W.K :=
      W.K.div_mem (W.K.pow_mem (W.K.add_mem W.K.one_mem hωW) 2) (W.K.pow_mem hωW 2)
    have h4 : (1 + ω) ^ 2 / ω ^ 2 ≠ 0 :=
      div_ne_zero (pow_ne_zero 2 hω1') (pow_ne_zero 2 hω0)
    have h5 : (α * β)⁻¹ ∈ W.K := by
      have := W.K.div_mem h1 h3
      have e : (1 + ω) ^ 2 / (ω ^ 2 * (α * β)) / ((1 + ω) ^ 2 / ω ^ 2) = (α * β)⁻¹ := by
        field_simp
      rwa [e] at this
    simpa using W.K.inv_mem h5
  ·
    have h4 : (4 : F) ≠ 0 := by
      intro h4
      apply h2
      have : (2 : F) * 2 = 0 := by linear_combination h4
      exact mul_self_eq_zero.mp this
    have h2W : (2 : F) ∈ W.K := ofNat_mem W.K 2
    have hpair : ∀ s t : F, s ∈ k → t ∈ k → (t * β) * (s * α) ∈ W.K := by
      intro s t hs ht
      have hA : l2 (t * β) ∈ M := hl t ht
      have hB : u2 (s * α) ∈ M := hu s hs
      have h := normalizedTrace_mem_subfield (M.map (mkPSL F)) W
        ⟨mkPSL F (l2 (t * β)), Subgroup.mem_map_of_mem _ hA⟩
        ⟨mkPSL F (u2 (s * α)), Subgroup.mem_map_of_mem _ hB⟩
        (l2 (t * β)) (u2 (s * α)) rfl rfl (by rw [trace_l2]; exact h2)
        (by rw [trace_u2]; exact h2)
      rw [trace_l2_mul_u2_gen, trace_l2, trace_u2] at h
      have e : (t * β) * (s * α) = 4 * ((2 + s * α * (t * β)) / (2 * 2)) - 2 := by
        field_simp
        ring
      rw [e]
      exact W.K.sub_mem (W.K.mul_mem (ofNat_mem W.K 4) h) h2W
    have hc : α * β ∈ W.K := by
      have h := hpair 1 1 k.one_mem k.one_mem
      rw [one_mul, one_mul, mul_comm] at h
      exact h
    refine ⟨fun s hs => ?_, hc⟩
    have h1 := hpair s 1 hs k.one_mem
    have e : s = (1 * β * (s * α)) / (α * β) := by
      field_simp
    rw [e]
    exact W.K.div_mem h1 hc

end RootPair

theorem sl2_eq_top_of_root_pair {F : Type} [Field F] [Finite F] {k : Subfield F} {d : ℕ}
    (hd : d.Prime) (hd2 : d ≠ 2) (hK : Nat.card F = Nat.card k ^ d) (hk3 : 3 ≤ Nat.card k)
    {α β : F} (hαβ : α * β ∉ k) {M : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hu : ∀ t ∈ k, u2 (t * α) ∈ M) (hl : ∀ s ∈ k, l2 (s * β) ∈ M) : M = ⊤ := by
  classical
  have hα : α ≠ 0 := fun h => hαβ (by rw [h, zero_mul]; exact k.zero_mem)
  have hβ : β ≠ 0 := fun h => hαβ (by rw [h, mul_zero]; exact k.zero_mem)
  have hℓ : (ringChar F).Prime := CharP.prime_ringChar F
  have : Fact (ringChar F).Prime := ⟨hℓ⟩
  obtain ⟨f, hf1, hF⟩ : ∃ f, 1 ≤ f ∧ Nat.card F = ringChar F ^ f := by
    have := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
    exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩
  have hkdvd : Nat.card k ∣ ringChar F ^ f := by
    rw [← hF, hK]
    exact dvd_pow_self _ hd.ne_zero
  obtain ⟨m₀, -, hk⟩ := (Nat.dvd_prime_pow hℓ).1 hkdvd
  have hxM : u2 α ∈ M := by simpa using hu 1 k.one_mem
  have hyM : l2 β ∈ M := by simpa using hl 1 k.one_mem
  have hxy := mkPSL_u2_mul_l2_ne hα hβ
  have hFcard4 : ∃ S : Finset F, S.card = 4 := by
    have := Fintype.ofFinite F
    have h27 : 4 ≤ Fintype.card F := by
      rw [← Nat.card_eq_fintype_card, hK]
      calc 4 ≤ 3 ^ 2 := by norm_num
        _ ≤ Nat.card k ^ 2 := Nat.pow_le_pow_left hk3 2
        _ ≤ Nat.card k ^ d := Nat.pow_le_pow_right (by omega) hd.two_le
    obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq h27
    exact ⟨S, hS⟩
  let H : Subgroup (PSL2MatrixGroup F) := M.map (mkPSL F)
  let x : H := ⟨mkPSL F (u2 α), Subgroup.mem_map_of_mem _ hxM⟩
  let y : H := ⟨mkPSL F (l2 β), Subgroup.mem_map_of_mem _ hyM⟩
  have hxyH : x * y ≠ y * x := by
    intro h
    exact hxy (congrArg Subtype.val h)
  have hkH : Nat.card k ∣ Nat.card H := by
    let φ : Multiplicative k →* PSL2MatrixGroup F := (mkPSL F).comp (uHom k α)
    have hinj : Function.Injective φ := by
      intro s s' h
      have := mkPSL_u2_injective α hα h
      exact Multiplicative.toAdd.injective (Subtype.ext this)
    have hle : φ.range ≤ H := by
      rintro _ ⟨s, rfl⟩
      exact ⟨uHom k α s, hu _ s.toAdd.2, rfl⟩
    have hcard : Nat.card φ.range = Nat.card k := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
        Nat.card_congr Multiplicative.toAdd]
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hle
  have hFdvd : ringChar F ∣ Nat.card F := by
    rw [hF]
    exact dvd_pow_self _ (by omega)
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield (p := ringChar F)
      (f := f) hF H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hcard, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m', t, -, ht, N, C, hN, hNel, hNcard, hCcyc, hCcard, hdisj, hsup⟩ |
      ⟨m, hm0, hmf, ⟨eP⟩, ⟨W⟩⟩ | ⟨m, hm0, hmf, ⟨eP⟩, ⟨W⟩⟩
  · exact absurd (hEl.toIsMulCommutative.is_comm.comm x y) hxyH
  · have : IsCyclic H := hcyc
    exact absurd (IsCyclic.isMulCommutative.is_comm.comm x y) hxyH
  ·
    exfalso
    have hzcop : Nat.Coprime (ringChar F) z := by
      rw [Nat.Prime.coprime_iff_not_dvd hℓ]
      intro hdvd
      rcases hz with hz | hz
      · have h1 : z ∣ Nat.card F - 1 := hz.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
        have h2 : ringChar F ∣ Nat.card F - 1 := hdvd.trans h1
        have h3 : ringChar F ∣ 1 := by
          have := Nat.dvd_sub hFdvd h2
          have h4 : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
          rwa [Nat.sub_sub_self h4] at this
        exact hℓ.one_lt.ne' (Nat.dvd_one.mp h3)
      · have hg : Nat.gcd (Nat.card F - 1) 2 ∣ Nat.card F + 1 := by
          have h1 := Nat.gcd_dvd_left (Nat.card F - 1) 2
          have h2 := Nat.gcd_dvd_right (Nat.card F - 1) 2
          have h4 : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
          have h5 : Nat.card F + 1 = (Nat.card F - 1) + 2 := by omega
          rw [h5]
          exact Nat.dvd_add h1 h2
        have h1 : z ∣ Nat.card F + 1 := hz.trans (Nat.div_dvd_of_dvd hg)
        have h2 : ringChar F ∣ Nat.card F + 1 := hdvd.trans h1
        have h3 : ringChar F ∣ 1 := (Nat.dvd_add_right hFdvd).mp h2
        exact hℓ.one_lt.ne' (Nat.dvd_one.mp h3)
    have hkz : Nat.Coprime (Nat.card k) z := by
      rw [hk]
      exact Nat.Coprime.pow_left _ hzcop
    have h2 : Nat.card k ∣ 2 := hkz.dvd_of_dvd_mul_right (by rw [← hcard]; exact hkH)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · exfalso
    exact hαβ (mul_mem_of_pow_central hd hd2 hK hα (pow_central_of_small hxM hyM e alt4_pow))
  · exfalso
    exact hαβ (mul_mem_of_pow_central hd hd2 hK hα (pow_central_of_small hxM hyM e perm4_pow))
  · exfalso
    exact hαβ (mul_mem_of_pow_central hd hd2 hK hα (pow_central_of_small hxM hyM e alt5_pow))
  ·
    exfalso
    have := hN
    have hcop : Nat.Coprime (ringChar F) (Nat.card C) := by
      rw [hCcard, Nat.Prime.coprime_iff_not_dvd hℓ]
      intro hdvd
      have h1 : t ∣ ringChar F ^ f - 1 := ht.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
      have h2 : ringChar F ∣ ringChar F ^ f - 1 := hdvd.trans h1
      have h3 : ringChar F ∣ ringChar F ^ f := dvd_pow_self _ (by omega)
      have h4 : ringChar F ∣ 1 := by
        have := Nat.dvd_sub h3 h2
        have h5 : 1 ≤ ringChar F ^ f := Nat.one_le_pow _ _ hℓ.pos
        rwa [Nat.sub_sub_self h5] at this
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp h4)
    have hx1 : x ^ ringChar F = 1 := by
      apply Subtype.ext
      simp [x, ← map_pow, u2_pow_ringChar]
    have hy1 : y ^ ringChar F = 1 := by
      apply Subtype.ext
      simp [y, ← map_pow, l2_pow_ringChar]
    have hxN : x ∈ N := mem_of_pow_eq_one_of_coprime_sup hdisj hsup hcop hx1
    have hyN : y ∈ N := mem_of_pow_eq_one_of_coprime_sup hdisj hsup hcop hy1
    have hcomm := hNel.toIsMulCommutative.is_comm.comm (⟨x, hxN⟩ : N) ⟨y, hyN⟩
    exact hxyH (congrArg Subtype.val hcomm)
  ·
    have hWK : W.K = ⊤ := witness_eq_top_pair hd hK hk3 hα hβ hαβ hu hl W
    have hmf' : m = f := by
      have h1 : Nat.card W.K = Nat.card F := by
        rw [hWK]
        exact Nat.card_congr Subfield.topEquiv.toEquiv
      rw [W.card_eq, hF] at h1
      exact Nat.pow_right_injective hℓ.two_le h1
    have e2 : GaloisField (ringChar F) m ≃+* F := by
      have := Fintype.ofFinite (GaloisField (ringChar F) m)
      have := Fintype.ofFinite F
      exact FiniteField.ringEquivOfCardEq (by
        rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF,
          GaloisField.card (ringChar F) m hm0, hmf'])
    have hcardH : Nat.card H = Nat.card (PSL2MatrixGroup F) := by
      rw [Nat.card_congr eP.toEquiv]
      exact Nat.card_congr (h826_pslEquiv e2).toEquiv
    have hHtop : H = ⊤ := Subgroup.eq_top_of_card_eq H hcardH
    have : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) :=
      CFSG.LinearGroups.special_linear_dimension_two_perfect hFcard4
    refine eq_top_of_central_kernel_perfect (mkPSL F) ?_ ?_
    · rw [mkPSL, QuotientGroup.ker_mk']
    · intro g _
      change g ∈ H
      rw [hHtop]
      trivial
  ·
    exfalso
    have hWK : W.K = ⊤ := witness_eq_top_pair hd hK hk3 hα hβ hαβ hu hl W
    have hmf' : m = f := by
      have h1 : Nat.card W.K = Nat.card F := by
        rw [hWK]
        exact Nat.card_congr Subfield.topEquiv.toEquiv
      rw [W.card_eq, hF] at h1
      exact Nat.pow_right_injective hℓ.two_le h1
    have := Nat.le_of_dvd (by omega) hmf
    omega

end Dickson

end CFSG.LieType.SeitzGeneration
