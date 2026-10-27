module

public import CFSG.LocalAnalysis.ComponentInitial.MatrixExtensionAlternating

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix
open scoped commutatorElement

@[expose] def binarySymMatrices (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) (ZMod 2)) where
  carrier := {X | Xᵀ = X}
  add_mem' {X Y} hX hY := by
    change (X + Y)ᵀ = X + Y
    rw [transpose_add, show Xᵀ = X from hX, show Yᵀ = Y from hY]
  zero_mem' := transpose_zero
  neg_mem' {X} hX := by
    change (-X)ᵀ = -X
    rw [transpose_neg, show Xᵀ = X from hX]

theorem mem_binarySymMatrices {n : ℕ} {X : Matrix (Fin n) (Fin n) (ZMod 2)} :
    X ∈ binarySymMatrices n ↔ Xᵀ = X :=
  Iff.rfl

namespace MatrixExtension

section Sym

variable {n : ℕ}

theorem binaryOff_mem_binarySymMatrices (i j : Fin n) : binaryOff i j ∈ binarySymMatrices n :=
  (binaryOff_mem_binaryAltMatrices i j).1

theorem single_mem_binarySymMatrices (k : Fin n) :
    single k k (1 : ZMod 2) ∈ binarySymMatrices n :=
  transpose_single k k 1

theorem vecMulVec_self_mem_binarySymMatrices (v : Fin n → ZMod 2) :
    vecMulVec v v ∈ binarySymMatrices n := by
  rw [mem_binarySymMatrices, transpose_vecMulVec]

theorem binaryTransvection_congr_diag_of_ne {a b : Fin n} (h : a ≠ b) {k : Fin n} (hk : k ≠ b) :
    (binaryTransvection h : Matrix (Fin n) (Fin n) (ZMod 2)) * single k k 1 *
        (binaryTransvection h : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = single k k 1 := by
  rw [binaryTransvection_congr_diag, ite_eq_right hk, add_zero]

theorem binaryTransvection_congr_diag_self {a b : Fin n} (h : a ≠ b) :
    (binaryTransvection h : Matrix (Fin n) (Fin n) (ZMod 2)) * single b b 1 *
        (binaryTransvection h : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
      single b b 1 + (binaryOff a b + single a a 1) := by
  rw [binaryTransvection_congr_diag, ite_eq_left rfl]

theorem vecMulVec_single_add_single (i j : Fin n) :
    vecMulVec (Pi.single i (1 : ZMod 2) + Pi.single j 1) (Pi.single i 1 + Pi.single j 1) =
      single i i 1 + single j j 1 + binaryOff i j := by
  rw [add_vecMulVec, vecMulVec_add, vecMulVec_add, vecMulVec_single_single,
    vecMulVec_single_single, vecMulVec_single_single, vecMulVec_single_single, binaryOff]
  abel

end Sym

section Core

variable {n : ℕ} {M : Type*} [AddCommGroup M]
  {act : GL (Fin n) (ZMod 2) →* AddMonoid.End M} {π : M →+ Matrix (Fin n) (Fin n) (ZMod 2)}

local notation "𝕏" => binaryTransvection

theorem act_binaryTransvection_diag_eq (hn : 4 ≤ n)
    (hπact : ∀ g x, π (act g x) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * π x *
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) (hC : ∀ g, ∀ c ∈ π.ker, act g c = c)
    {a b : Fin n} (hab : a ≠ b) {k : Fin n} (hk : k ≠ b) {x : M}
    (hx : π x = single k k 1) : act (𝕏 hab) x = x := by
  obtain ⟨l, hla, hlb, hlk⟩ := exists_ne_of_four hn a b k
  rw [← commutatorElement_binaryTransvection hla.symm hlb hab]
  refine act_commutatorElement_apply_eq act hC (act_sub_mem_ker hπact ?_)
    (act_sub_mem_ker hπact ?_)
  · rw [hx, binaryTransvection_congr_diag_of_ne _ (Ne.symm hlk)]
  · rw [hx, binaryTransvection_congr_diag_of_ne _ hk]

theorem commutatorElement_mul_binaryTransvection {a i j b : Fin n} (hai : a ≠ i) (haj : a ≠ j)
    (hib : i ≠ b) (hab : a ≠ b) (hij : i ≠ j) :
    ⁅𝕏 hai * 𝕏 haj, 𝕏 hib⁆ = 𝕏 hab := by
  have hcomm : ⁅𝕏 haj, 𝕏 hib⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact binaryTransvection_commute haj hib hij.symm hab.symm
  rw [commutatorElement_mul_left_eq, hcomm, mul_one, mul_inv_cancel, one_mul,
    commutatorElement_binaryTransvection hai hib hab]

theorem mulVec_binaryTransvection_mul {a i j : Fin n} (hai : a ≠ i) (haj : a ≠ j)
    (hij : i ≠ j) :
    ((𝕏 hai * 𝕏 haj : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        (Pi.single i 1 + Pi.single j 1) = Pi.single i 1 + Pi.single j 1 := by
  rw [Units.val_mul, ← mulVec_mulVec, binaryTransvection_coe, binaryTransvection_coe,
    one_add_single_mulVec, one_add_single_mulVec]
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm,
    Pi.single_eq_of_ne (Ne.symm hai), add_zero, zero_add]
  funext k
  simp only [Pi.add_apply]
  exact (add_assoc _ _ _).trans (by rw [CharTwo.add_self_eq_zero, add_zero])

theorem sym_act_binaryTransvection_eq_of_ne (hn : 4 ≤ n)
    (hπact : ∀ g x, π (act g x) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * π x *
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) (hC : ∀ g, ∀ c ∈ π.ker, act g c = c)
    (hliftQ : ∀ v : Fin n → ZMod 2, ∃ x, π x = vecMulVec v v)
    {a b : Fin n} (hab : a ≠ b) {i j : Fin n} (hi : i ≠ b) (hj : j ≠ b) {x : M}
    (hx : π x = binaryOff i j) : act (𝕏 hab) x = x := by
  suffices h : ∃ y, π y = binaryOff i j ∧ act (𝕏 hab) y = y by
    obtain ⟨y, hy, hay⟩ := h
    have hxy : x - y ∈ π.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, hx, hy]
      exact sub_self _
    have h' := hC (𝕏 hab) _ hxy
    rw [map_sub, hay] at h'
    exact sub_left_inj.mp h'
  by_cases hij : i = j
  · subst hij
    refine ⟨0, by rw [map_zero, binaryOff_self], map_zero _⟩
  by_cases ha : a = i ∨ a = j
  · refine ⟨x, hx, ?_⟩
    obtain ⟨l, hli, hlj, hlb⟩ := exists_ne_of_four hn i j b
    have hla : l ≠ a := by
      rcases ha with rfl | rfl
      · exact hli
      · exact hlj
    rw [← commutatorElement_binaryTransvection hla.symm hlb hab]
    refine act_commutatorElement_apply_eq act hC (act_sub_mem_ker hπact ?_)
      (act_sub_mem_ker hπact ?_)
    · rw [hx, binaryTransvection_congr_binaryOff_of_ne _ (Ne.symm hli) (Ne.symm hlj)]
    · rw [hx, binaryTransvection_congr_binaryOff_of_ne _ hi hj]
  · push Not at ha
    obtain ⟨hai, haj⟩ := ha
    obtain ⟨u, hu⟩ := hliftQ (Pi.single i 1 + Pi.single j 1)
    obtain ⟨di, hdi⟩ := hliftQ (Pi.single i 1)
    obtain ⟨dj, hdj⟩ := hliftQ (Pi.single j 1)
    rw [vecMulVec_single_single] at hdi hdj
    have hu' : act (𝕏 hab) u = u := by
      rw [← commutatorElement_mul_binaryTransvection hai haj hi hab hij]
      refine act_commutatorElement_apply_eq act hC (act_sub_mem_ker hπact ?_)
        (act_sub_mem_ker hπact ?_)
      · rw [hu, mul_vecMulVec_mul_transpose, mulVec_binaryTransvection_mul hai haj hij]
      · rw [hu, mul_vecMulVec_mul_transpose, binaryTransvection_coe, one_add_single_mulVec]
        simp only [Pi.add_apply, Pi.single_eq_of_ne hi.symm, Pi.single_eq_of_ne hj.symm,
          add_zero, Pi.single_zero]
    have hdi' := act_binaryTransvection_diag_eq hn hπact hC hab hi hdi
    have hdj' := act_binaryTransvection_diag_eq hn hπact hC hab hj hdj
    refine ⟨u + di + dj, ?_, by rw [map_add, map_add, hu', hdi', hdj']⟩
    rw [map_add, map_add, hu, hdi, hdj, vecMulVec_single_add_single]
    have h2 : ∀ X : Matrix (Fin n) (Fin n) (ZMod 2), X + X = 0 := binary_add_self
    linear_combination (norm := abel) h2 (single i i 1) + h2 (single j j 1)

variable [Module (ZMod 2) M]

theorem sym_diag_defect_eq (hn : 4 ≤ n)
    (hπact : ∀ g x, π (act g x) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * π x *
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) (hC : ∀ g, ∀ c ∈ π.ker, act g c = c)
    {o : Fin n → Fin n → M} (ho : ∀ i j, π (o i j) = binaryOff i j) (hod : ∀ i, o i i = 0)
    (hoact : ∀ (a b : Fin n) (h : a ≠ b) (i j : Fin n), act (𝕏 h) (o i j) =
      o i j + (if i = b then o a j else 0) + (if j = b then o i a else 0))
    {d : Fin n → M} (hd : ∀ k, π (d k) = single k k 1) {a b c : Fin n} (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) :
    act (𝕏 hac) (d c) - d c - d a - o a c = act (𝕏 hab) (d b) - d b - d a - o a b := by
  have hdef : ∀ {x y : Fin n} (hxy : x ≠ y), act (𝕏 hxy) (d y) - d y - d x - o x y ∈ π.ker := by
    intro x y hxy
    rw [AddMonoidHom.mem_ker, map_sub, map_sub, map_sub, hπact, hd, hd, ho,
      binaryTransvection_congr_diag_self]
    abel
  obtain ⟨c₁, hc₁, e₁⟩ : ∃ z ∈ π.ker, act (𝕏 hbc) (d c) = d c + d b + o b c + z :=
    ⟨_, hdef hbc, by abel⟩
  obtain ⟨c₂, hc₂, e₂⟩ : ∃ z ∈ π.ker, act (𝕏 hab) (d b) = d b + d a + o a b + z :=
    ⟨_, hdef hab, by abel⟩
  have k₁ : ∀ g, act g c₁ = c₁ := fun g => hC g _ hc₁
  have k₂ : ∀ g, act g c₂ = c₂ := fun g => hC g _ hc₂
  have f₁ := act_binaryTransvection_diag_eq hn hπact hC hab (Ne.symm hbc) (hd c)
  have f₂ := act_binaryTransvection_diag_eq hn hπact hC hbc hbc (hd b)
  have f₃ := act_binaryTransvection_diag_eq hn hπact hC hbc hac (hd a)
  have f₄ := act_binaryTransvection_diag_eq hn hπact hC hab hab (hd a)
  have g₁ : act (𝕏 hab) (o b c) = o b c + o a c := by
    rw [hoact, ite_eq_left rfl, ite_eq_right (Ne.symm hbc), add_zero]
  have g₂ : act (𝕏 hbc) (o a b) = o a b := by
    rw [hoact, ite_eq_right hac, ite_eq_right hbc, add_zero, add_zero]
  have g₃ : act (𝕏 hbc) (o b c) = o b c := by
    rw [hoact, ite_eq_right hbc, ite_eq_left rfl, hod, add_zero, add_zero]
  have g₄ : act (𝕏 hbc) (o a c) = o a c + o a b := by
    rw [hoact, ite_eq_right hac, ite_eq_left rfl, add_zero]
  have g₅ : act (𝕏 hab) (o a c) = o a c := by
    rw [hoact, ite_eq_right hab, ite_eq_right (Ne.symm hbc), add_zero, add_zero]
  have hcomm : act (𝕏 hac) (d c) =
      act (𝕏 hab) (act (𝕏 hbc) (act (𝕏 hab) (act (𝕏 hbc) (d c)))) := by
    rw [← commutatorElement_binaryTransvection hab hbc hac, commutatorElement_def,
      binaryTransvection_inv, binaryTransvection_inv, act_mul_apply, act_mul_apply,
      act_mul_apply]
  rw [hcomm, e₁, e₂]
  simp only [map_add, f₁, e₁, e₂, f₂, f₃, f₄, g₁, g₂, g₃, g₄, g₅, k₁, k₂]
  linear_combination (norm := match_scalars <;> decide) (0 : ZMod 2) • (rfl : c₁ = c₁)

theorem exists_sym_equivariant_lifts (hn : 4 ≤ n)
    (hπact : ∀ g x, π (act g x) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * π x *
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) (hC : ∀ g, ∀ c ∈ π.ker, act g c = c)
    (hliftQ : ∀ v : Fin n → ZMod 2, ∃ x, π x = vecMulVec v v)
    (hliftO : ∀ i j : Fin n, ∃ x, π x = binaryOff i j) :
    ∃ (o : Fin n → Fin n → M) (d : Fin n → M), (∀ i j, π (o i j) = binaryOff i j) ∧
      (∀ i j, o i j = o j i) ∧ (∀ i, o i i = 0) ∧ (∀ k, π (d k) = single k k 1) ∧
      (∀ (a b : Fin n) (h : a ≠ b) (i j : Fin n), act (𝕏 h) (o i j) =
        o i j + (if i = b then o a j else 0) + (if j = b then o i a else 0)) ∧
      ∀ (a b : Fin n) (h : a ≠ b) (k : Fin n),
        act (𝕏 h) (d k) = d k + (if k = b then d a + o a k else 0) := by
  classical
  obtain ⟨o, ho, hos, hod, hoact⟩ := exists_off_equivariant_lifts hn hπact hC
    (fun hab _ _ hi hj _ hx => sym_act_binaryTransvection_eq_of_ne hn hπact hC hliftQ hab hi hj hx)
    hliftO
  have hd₀ : ∀ k : Fin n, ∃ x, π x = single k k 1 := fun k => by
    obtain ⟨x, hx⟩ := hliftQ (Pi.single k 1)
    exact ⟨x, by rw [hx, vecMulVec_single_single]⟩
  choose d₀ hd₀π using hd₀
  choose b₀ hb₀ using fun a : Fin n => exists_ne_ne_of_three_le (by omega : 3 ≤ n) a a
  set e : Fin n → M := fun a =>
    act (𝕏 (hb₀ a).1.symm) (d₀ (b₀ a)) - d₀ (b₀ a) - d₀ a - o a (b₀ a) with he
  have hemem : ∀ a, e a ∈ π.ker := fun a => by
    simp only [he]
    rw [AddMonoidHom.mem_ker, map_sub, map_sub, map_sub, hπact, hd₀π, hd₀π, ho,
      binaryTransvection_congr_diag_self]
    abel
  have hdef : ∀ (a b : Fin n) (hab : a ≠ b),
      act (𝕏 hab) (d₀ b) = d₀ b + d₀ a + o a b + e a := by
    intro a b hab
    by_cases hb : b = b₀ a
    · subst hb
      simp only [he]
      abel
    · have h := sym_diag_defect_eq hn hπact hC ho hod hoact hd₀π (hb₀ a).1.symm
        (Ne.symm hb) hab
      simp only [he]
      rw [← h]
      abel
  refine ⟨o, fun k => d₀ k + e k, ho, hos, hod, fun k => ?_, hoact, fun a b hab k => ?_⟩
  · rw [map_add, hd₀π, (AddMonoidHom.mem_ker).mp (hemem k), add_zero]
  · rw [map_add, hC _ _ (hemem k)]
    by_cases hk : k = b
    · subst hk
      rw [ite_eq_left rfl, hdef a k hab]
      have h2 := zmod_two_add_self (e k)
      linear_combination (norm := match_scalars <;> decide) (1 : ZMod 2) • h2
    · rw [ite_eq_right hk, add_zero, act_binaryTransvection_diag_eq hn hπact hC hab hk (hd₀π k)]

end Core

section SymSection

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

@[expose] def symSection (o : Fin n → Fin n → M) (d : Fin n → M) :
    Matrix (Fin n) (Fin n) (ZMod 2) →+ M :=
  altSection o + { toFun := fun X => ∑ k, X k k • d k
                   map_zero' := by simp
                   map_add' := fun X Y => by simp [add_smul, Finset.sum_add_distrib] }

theorem symSection_apply (o : Fin n → Fin n → M) (d : Fin n → M)
    (X : Matrix (Fin n) (Fin n) (ZMod 2)) :
    symSection o d X = altSection o X + ∑ k, X k k • d k :=
  rfl

theorem diag_sum_apply (X : Matrix (Fin n) (Fin n) (ZMod 2)) (a b : Fin n) :
    (∑ k, X k k • single k k (1 : ZMod 2) : Matrix (Fin n) (Fin n) (ZMod 2)) a b =
      if a = b then X a a else 0 := by
  rw [Matrix.sum_apply, Finset.sum_eq_single a]
  · rw [Matrix.smul_apply, single_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab]
  · intro k _ hka
    rw [Matrix.smul_apply, single_apply, ite_eq_right fun h => hka h.1, smul_zero]
  · simp

theorem symSection_closure_spec (o : Fin n → Fin n → M) (d : Fin n → M)
    (hsymm : ∀ i j, o i j = o j i)
    (π : M →+ Matrix (Fin n) (Fin n) (ZMod 2)) (hπo : ∀ i j, π (o i j) = binaryOff i j)
    (hπd : ∀ k, π (d k) = single k k 1) :
    (∀ x ∈ AddSubgroup.closure (Set.range fun p : Fin n × Fin n =>
        if p.1 = p.2 then d p.1 else o p.1 p.2), π x = 0 → x = 0) ∧
    ∀ X ∈ binarySymMatrices n, ∃ x ∈ AddSubgroup.closure (Set.range fun p : Fin n × Fin n =>
        if p.1 = p.2 then d p.1 else o p.1 p.2), π x = X := by
  classical
  set S := AddSubgroup.closure (Set.range fun p : Fin n × Fin n =>
    if p.1 = p.2 then d p.1 else o p.1 p.2) with hS
  have hπσ : ∀ X, π (symSection o d X) = (∑ p ∈ binaryUpperPairs n,
      X p.1 p.2 • (single p.1 p.2 (1 : ZMod 2) + single p.2 p.1 1)) +
        ∑ k, X k k • single k k (1 : ZMod 2) := by
    intro X
    rw [symSection_apply, altSection_apply, map_add, map_sum, map_sum]
    congr 1
    · exact Finset.sum_congr rfl fun p _ =>
        (map_zmod_two_smul π (X p.1 p.2) (o p.1 p.2)).trans (congrArg _ (hπo _ _))
    · exact Finset.sum_congr rfl fun k _ =>
        (map_zmod_two_smul π (X k k) (d k)).trans (congrArg _ (hπd _))
  have hπσ_apply : ∀ X a b, π (symSection o d X) a b =
      (if a < b then X a b else if b < a then X b a else 0) + if a = b then X a a else 0 := by
    intro X a b
    rw [hπσ, Matrix.add_apply]
    exact congrArg₂ (· + ·) (binaryUpperSum_apply X a b) (diag_sum_apply X a b)
  have hgen : ∀ p : Fin n × Fin n, (if p.1 = p.2 then d p.1 else o p.1 p.2) ∈ S :=
    fun p => AddSubgroup.subset_closure ⟨p, rfl⟩
  have hSσ : S ≤ (symSection o d).range := by
    rw [hS, AddSubgroup.closure_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    dsimp only
    rcases lt_trichotomy i j with h | rfl | h
    · refine ⟨single i j 1, ?_⟩
      rw [ite_eq_right h.ne, symSection_apply, altSection_single o h,
        Finset.sum_eq_zero fun k _ => by
          rw [single_apply, ite_eq_right fun h' => h.ne (h'.1.trans h'.2.symm), zero_smul],
        add_zero]
    · refine ⟨single i i 1, ?_⟩
      rw [ite_eq_left rfl, symSection_apply, altSection_apply]
      rw [Finset.sum_eq_zero fun p hp => by
        rw [single_apply, ite_eq_right fun h' =>
          (Finset.mem_filter.mp hp).2.ne (h'.1.symm.trans h'.2), zero_smul]]
      rw [Finset.sum_eq_single i (fun k _ hki => by
        rw [single_apply, ite_eq_right fun h' => hki h'.1.symm, zero_smul]) (by simp)]
      simp
    · refine ⟨single j i 1, ?_⟩
      rw [ite_eq_right h.ne', symSection_apply, altSection_single o h, hsymm,
        Finset.sum_eq_zero fun k _ => by
          rw [single_apply, ite_eq_right fun h' => h.ne (h'.1.trans h'.2.symm), zero_smul],
        add_zero]
  have hσS : ∀ X, symSection o d X ∈ S := fun X => by
    rw [symSection_apply, altSection_apply]
    refine add_mem (AddSubgroup.sum_mem _ fun p hp => zmod_two_smul_mem S _ ?_)
      (AddSubgroup.sum_mem _ fun k _ => zmod_two_smul_mem S _ ?_)
    · have := hgen p
      rwa [ite_eq_right (Finset.mem_filter.mp hp).2.ne] at this
    · have := hgen (k, k)
      rwa [ite_eq_left rfl] at this
  refine ⟨fun x hx hπx => ?_, fun X hX => ⟨symSection o d X, hσS X, ?_⟩⟩
  · obtain ⟨Y, rfl⟩ := hSσ hx
    have hent : ∀ a b, π (symSection o d Y) a b = 0 := fun a b => by rw [hπx]; rfl
    have hup : ∀ p ∈ binaryUpperPairs n, Y p.1 p.2 = 0 := by
      intro p hp
      have h := hent p.1 p.2
      rw [hπσ_apply, ite_eq_left (Finset.mem_filter.mp hp).2,
        ite_eq_right (Finset.mem_filter.mp hp).2.ne, add_zero] at h
      exact h
    have hdg : ∀ k, Y k k = 0 := by
      intro k
      have h := hent k k
      rw [hπσ_apply, ite_eq_right (lt_irrefl k), ite_eq_right (lt_irrefl k), ite_eq_left rfl,
        zero_add] at h
      exact h
    rw [symSection_apply, altSection_apply]
    rw [Finset.sum_eq_zero fun p hp => by rw [hup p hp, zero_smul],
      Finset.sum_eq_zero fun k _ => by rw [hdg k, zero_smul], add_zero]
  · ext a b
    rw [hπσ_apply]
    have hXt : Xᵀ = X := hX
    rcases lt_trichotomy a b with h | rfl | h
    · rw [ite_eq_left h, ite_eq_right h.ne, add_zero]
    · rw [ite_eq_right (lt_irrefl a), ite_eq_right (lt_irrefl a), ite_eq_left rfl, zero_add]
    · rw [ite_eq_right (lt_asymm h), ite_eq_left h, ite_eq_right h.ne', add_zero]
      exact congrFun₂ hXt a b

end SymSection

section Core

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  {act : GL (Fin n) (ZMod 2) →* AddMonoid.End M} {π : M →+ Matrix (Fin n) (Fin n) (ZMod 2)}

theorem sym_exists_invariant_complement (hn : 4 ≤ n)
    (hπact : ∀ g x, π (act g x) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * π x *
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) (hC : ∀ g, ∀ c ∈ π.ker, act g c = c)
    (hliftQ : ∀ v : Fin n → ZMod 2, ∃ x, π x = vecMulVec v v)
    (hliftO : ∀ i j : Fin n, ∃ x, π x = binaryOff i j) :
    ∃ S : AddSubgroup M, (∀ g, ∀ x ∈ S, act g x ∈ S) ∧ (∀ x ∈ S, π x = 0 → x = 0) ∧
      ∀ X ∈ binarySymMatrices n, ∃ x ∈ S, π x = X := by
  classical
  obtain ⟨o, d, ho, hos, hod, hd, hoact, hdact⟩ :=
    exists_sym_equivariant_lifts hn hπact hC hliftQ hliftO
  obtain ⟨hinj, hsurj⟩ := symSection_closure_spec o d hos π ho hd
  set S := AddSubgroup.closure (Set.range fun p : Fin n × Fin n =>
    if p.1 = p.2 then d p.1 else o p.1 p.2) with hS
  have hmemo : ∀ k l, o k l ∈ S := fun k l => by
    by_cases hkl : k = l
    · rw [hkl, hod]
      exact zero_mem _
    · have h : (if (k, l).1 = (k, l).2 then d (k, l).1 else o (k, l).1 (k, l).2) ∈ S :=
        AddSubgroup.subset_closure ⟨(k, l), rfl⟩
      rwa [ite_eq_right hkl] at h
  have hmemd : ∀ k, d k ∈ S := fun k => by
    have h : (if (k, k).1 = (k, k).2 then d (k, k).1 else o (k, k).1 (k, k).2) ∈ S :=
      AddSubgroup.subset_closure ⟨(k, k), rfl⟩
    rwa [ite_eq_left rfl] at h
  refine ⟨S, fun g => act_mem_of_closure_eq_top act closure_binaryTransvection ?_ ?_ g, hinj,
    hsurj⟩
  · rintro _ ⟨a, b, h, rfl⟩
    exact ⟨a, b, h, (binaryTransvection_inv h).symm⟩
  · rintro _ ⟨a, b, h, rfl⟩ x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨⟨i, j⟩, rfl⟩ := hy
      dsimp only
      split_ifs with hij
      · rw [hdact]
        refine add_mem (hmemd i) ?_
        split_ifs
        · exact add_mem (hmemd a) (hmemo a i)
        · exact zero_mem _
      · rw [hoact]
        refine add_mem (add_mem (hmemo i j) ?_) ?_
        · split_ifs
          · exact hmemo a j
          · exact zero_mem _
        · split_ifs
          · exact hmemo i a
          · exact zero_mem _
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy

end Core

section Group

variable {n : ℕ} {P : Type*} [Group P]

theorem binarySym_eq_sum (X : binarySymMatrices n) :
    X = ∑ p ∈ binaryUpperPairs n, ((X : Matrix (Fin n) (Fin n) (ZMod 2)) p.1 p.2).val •
        (⟨binaryOff p.1 p.2, binaryOff_mem_binarySymMatrices _ _⟩ : binarySymMatrices n) +
      ∑ k, ((X : Matrix (Fin n) (Fin n) (ZMod 2)) k k).val •
        (⟨single k k 1, single_mem_binarySymMatrices k⟩ : binarySymMatrices n) := by
  apply Subtype.ext
  refine Eq.trans ?_ (AddSubgroup.coe_add _ _ _).symm
  refine Eq.trans ?_ (congrArg₂ (· + ·) (AddSubgroup.val_finsetSum _ _ _).symm
    (AddSubgroup.val_finsetSum _ _ _).symm)
  have hs : ∀ p : Fin n × Fin n, (((((X : Matrix (Fin n) (Fin n) (ZMod 2)) p.1 p.2).val •
      (⟨binaryOff p.1 p.2, binaryOff_mem_binarySymMatrices _ _⟩ : binarySymMatrices n)) :
        binarySymMatrices n) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (X : Matrix (Fin n) (Fin n) (ZMod 2)) p.1 p.2 •
        (single p.1 p.2 (1 : ZMod 2) + single p.2 p.1 1) := fun p => by
    rw [AddSubgroup.coe_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]
    rfl
  have hd : ∀ k : Fin n, (((((X : Matrix (Fin n) (Fin n) (ZMod 2)) k k).val •
      (⟨single k k 1, single_mem_binarySymMatrices k⟩ : binarySymMatrices n)) :
        binarySymMatrices n) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (X : Matrix (Fin n) (Fin n) (ZMod 2)) k k • single k k (1 : ZMod 2) := fun k => by
    rw [AddSubgroup.coe_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]
  refine Eq.trans ?_ (congrArg₂ (· + ·) (Finset.sum_congr rfl fun p _ => (hs p).symm)
    (Finset.sum_congr rfl fun k _ => (hd k).symm))
  ext a b
  refine Eq.trans ?_ (Matrix.add_apply _ _ a b).symm
  refine Eq.trans ?_ (congrArg₂ (· + ·) (binaryUpperSum_apply _ a b).symm
    (diag_sum_apply _ a b).symm)
  have hXt : (X : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = X := X.2
  rcases lt_trichotomy a b with h | rfl | h
  · rw [ite_eq_left h, ite_eq_right h.ne, add_zero]
  · rw [ite_eq_right (lt_irrefl a), ite_eq_right (lt_irrefl a), ite_eq_left rfl, zero_add]
  · rw [ite_eq_right (lt_asymm h), ite_eq_left h, ite_eq_right h.ne', add_zero]
    exact (congrFun₂ hXt a b).symm

theorem eq_top_of_lifts_binarySym (π : P →* Multiplicative (binarySymMatrices n))
    {K : Subgroup P} (hK : π.ker ≤ K)
    (hliftO : ∀ i j, ∃ x ∈ K, ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = binaryOff i j)
    (hliftD : ∀ k, ∃ x ∈ K, ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = single k k 1) :
    K = ⊤ := by
  have hmap : ∀ v : Multiplicative (binarySymMatrices n), v ∈ K.map π := by
    intro v
    have hv : v = (∏ p ∈ binaryUpperPairs n, Multiplicative.ofAdd
        (⟨binaryOff p.1 p.2, binaryOff_mem_binarySymMatrices _ _⟩ : binarySymMatrices n) ^
          ((v.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) p.1 p.2).val) *
        ∏ k, Multiplicative.ofAdd
          (⟨single k k 1, single_mem_binarySymMatrices k⟩ : binarySymMatrices n) ^
            ((v.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) k k).val := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_prod, toAdd_prod]
      simp only [toAdd_pow, toAdd_ofAdd]
      exact binarySym_eq_sum v.toAdd
    rw [hv]
    refine mul_mem (Finset.prod_induction _ (· ∈ K.map π) (fun _ _ ha hb => mul_mem ha hb)
      (one_mem _) fun p _ => pow_mem ?_ _) (Finset.prod_induction _ (· ∈ K.map π)
      (fun _ _ ha hb => mul_mem ha hb) (one_mem _) fun k _ => pow_mem ?_ _)
    · obtain ⟨x, hxK, hx⟩ := hliftO p.1 p.2
      exact ⟨x, hxK, Multiplicative.toAdd.injective (Subtype.ext hx)⟩
    · obtain ⟨x, hxK, hx⟩ := hliftD k
      exact ⟨x, hxK, Multiplicative.toAdd.injective (Subtype.ext hx)⟩
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨k, hkK, hk⟩ := hmap (π z)
  have hker : k⁻¹ * z ∈ K := hK (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hk, inv_mul_cancel])
  simpa using K.mul_mem hkK hker

theorem binarySym_commute (hn : 4 ≤ n) (act : GL (Fin n) (ZMod 2) →* MulAut P)
    (π : P →* Multiplicative (binarySymMatrices n)) (hπ : Function.Surjective π)
    (hπact : ∀ g x, ((π (act g x)).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) * ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ)
    (hC : π.ker ≤ Subgroup.center P) (hCfix : ∀ g, ∀ c ∈ π.ker, act g c = c) :
    ∀ x y : P, x * y = y * x := by
  classical
  have hinj : ∀ {x y : P}, ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) → π x = π y := fun h =>
    Multiplicative.toAdd.injective (Subtype.ext h)
  have himul : ∀ x y : P, ((π (x * y)).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) +
        ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) :=
    fun x y => by rw [map_mul, toAdd_mul, AddSubgroup.coe_add]
  have hzero : ∀ {x : P}, ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = 0 → x ∈ π.ker :=
    fun h => by
      rw [MonoidHom.mem_ker]
      exact Multiplicative.toAdd.injective (Subtype.ext h)
  have hliftO : ∀ i j, ∃ x : P, ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      binaryOff i j := fun i j => by
    obtain ⟨x, hx⟩ := hπ (Multiplicative.ofAdd ⟨binaryOff i j,
      binaryOff_mem_binarySymMatrices i j⟩)
    exact ⟨x, by rw [hx]; rfl⟩
  have hliftD : ∀ k, ∃ x : P, ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      single k k 1 := fun k => by
    obtain ⟨x, hx⟩ := hπ (Multiplicative.ofAdd ⟨single k k 1, single_mem_binarySymMatrices k⟩)
    exact ⟨x, by rw [hx]; rfl⟩
  choose pO hpO using hliftO
  choose pD hpD using hliftD
  have hH : ∀ a b : Multiplicative (binarySymMatrices n), a * b = b * a := fun a b =>
    Multiplicative.toAdd.injective (Subtype.ext (by
      simp only [toAdd_mul, AddSubgroup.coe_add]
      exact add_comm _ _))
  have hinv : ∀ g (x y : P), ⁅act g x, act g y⁆ = ⁅x, y⁆ := fun g x y =>
    (map_commutatorElement (act g) x y).symm.trans
      (hCfix g _ (commutatorElement_mem_ker π hH x y))
  have key : ∀ (g : GL (Fin n) (ZMod 2)) (x y z : P),
      ((π (act g x)).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
        ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) →
      ((π (act g z)).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
        ((π z).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) +
          ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) → ⁅x, y⁆ = 1 := by
    intro g x y z h₁ h₂
    have h := hinv g x z
    rw [commutatorElement_eq_of_map_eq π hC (hinj h₁) (hinj (h₂.trans (himul z y).symm)),
      commutatorElement_mul_right_of_ker π hH hC] at h
    exact mul_eq_left.mp h
  have hDO₁ : ∀ (x y : P) (k l : Fin n), k ≠ l →
      ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = single k k 1 →
      ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = binaryOff k l → ⁅x, y⁆ = 1 := by
    intro x y k l hkl hx hy
    have h := key (binaryTransvection hkl) x (y * x) (pD l)
      (by rw [hπact, hx, binaryTransvection_congr_diag_of_ne _ hkl])
      (by rw [hπact, hpD, binaryTransvection_congr_diag_self, himul, hy, hx])
    rwa [commutatorElement_mul_right_of_ker π hH hC, commutatorElement_self, mul_one] at h
  have hDO₂ : ∀ (x y : P) (k j l : Fin n), j ≠ l → j ≠ k → l ≠ k →
      ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = single k k 1 →
      ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = binaryOff j l → ⁅x, y⁆ = 1 := by
    intro x y k j l _ _ _ hx hy
    obtain ⟨m, hmk, hmj, hml⟩ := exists_ne_of_four hn k j l
    exact key (binaryTransvection hmj.symm) x y (pO m l)
      (by rw [hπact, hx, binaryTransvection_congr_diag_of_ne _ (Ne.symm hmk)])
      (by rw [hπact, hpO, binaryTransvection_congr_binaryOff_left _ hml.symm, hy])
  have hDO : ∀ (x y : P) (k i j : Fin n),
      ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = single k k 1 →
      ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = binaryOff i j → ⁅x, y⁆ = 1 := by
    intro x y k i j hx hy
    by_cases hij : i = j
    · rw [hij, binaryOff_self] at hy
      exact commutatorElement_eq_one_of_mem_center_right x (hC (hzero hy))
    by_cases hik : i = k
    · subst hik
      exact hDO₁ x y i j hij hx hy
    by_cases hjk : j = k
    · subst hjk
      exact hDO₁ x y j i (Ne.symm hij) hx (hy.trans (binaryOff_comm i j))
    exact hDO₂ x y k i j hij hik hjk hx hy
  have hDD : ∀ (x y : P) (k l : Fin n),
      ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = single k k 1 →
      ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = single l l 1 → ⁅x, y⁆ = 1 := by
    intro x y k l hx hy
    by_cases hkl : k = l
    · subst hkl
      rw [commutatorElement_eq_of_map_eq π hC rfl (hinj (hy.trans hx.symm)),
        commutatorElement_self]
    obtain ⟨m, hmk, hml⟩ := exists_ne_ne_of_three_le (by omega) k l
    have h := key (binaryTransvection hml.symm) x (pO l m * y) (pD m)
      (by rw [hπact, hx, binaryTransvection_congr_diag_of_ne _ (Ne.symm hmk)])
      (by rw [hπact, hpD, binaryTransvection_congr_diag_self, himul, hpO, hy])
    rwa [commutatorElement_mul_right_of_ker π hH hC, hDO x (pO l m) k l m hx (hpO l m),
      one_mul] at h
  have hDcen : ∀ (x : P) (k : Fin n),
      ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = single k k 1 → x ∈ Subgroup.center P := by
    intro x k hx
    have htop : Subgroup.centralizer {x} = ⊤ := by
      refine eq_top_of_lifts_binarySym π (fun c hc => ?_)
        (fun i j => ⟨pO i j, ?_, hpO i j⟩) fun l => ⟨pD l, ?_, hpD l⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_center_iff.mp (hC hc) x).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (commutatorElement_eq_one_iff_mul_comm.mp (hDO x _ k i j hx (hpO i j))).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (commutatorElement_eq_one_iff_mul_comm.mp (hDD x _ k l hx (hpD l))).symm
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    have hy : y ∈ Subgroup.centralizer {x} := htop ▸ Subgroup.mem_top y
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    exact hy
  have hactcen : ∀ g, ∀ x ∈ Subgroup.center P, act g x ∈ Subgroup.center P := by
    intro g x hx
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    obtain ⟨z, rfl⟩ := (act g).surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx z]
  have hOcen : ∀ (x : P) (i j : Fin n),
      ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = binaryOff i j →
      x ∈ Subgroup.center P := by
    intro x i j hx
    by_cases hij : i = j
    · rw [hij, binaryOff_self] at hx
      exact hC (hzero hx)
    set w := act (binaryTransvection (Ne.symm hij)) (pD i) * pD i * pD j with hw
    have hwc : w ∈ Subgroup.center P := Subgroup.mul_mem _ (Subgroup.mul_mem _
      (hactcen _ _ (hDcen _ i (hpD i))) (hDcen _ i (hpD i))) (hDcen _ j (hpD j))
    have hwπ : π w = π x := hinj (by
      rw [hw, himul, himul, hπact, hpD, hpD, binaryTransvection_congr_diag_self, hx,
        binaryOff_comm j i]
      have h2 : ∀ X : Matrix (Fin n) (Fin n) (ZMod 2), X + X = 0 := binary_add_self
      linear_combination (norm := abel) h2 (single i i 1) + h2 (single j j 1))
    have hk : w⁻¹ * x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwπ, inv_mul_cancel]
    have := Subgroup.mul_mem _ hwc (hC hk)
    rwa [mul_inv_cancel_left] at this
  have htop : Subgroup.center P = ⊤ := eq_top_of_lifts_binarySym π hC
    (fun i j => ⟨pO i j, hOcen _ i j (hpO i j), hpO i j⟩)
    (fun k => ⟨pD k, hDcen _ k (hpD k), hpD k⟩)
  intro x y
  have hx : x ∈ Subgroup.center P := htop ▸ Subgroup.mem_top x
  exact (Subgroup.mem_center_iff.mp hx y).symm

theorem binarySym_sq_eq_one (hn : 3 ≤ n) (act : GL (Fin n) (ZMod 2) →* MulAut P)
    (π : P →* Multiplicative (binarySymMatrices n)) (hπ : Function.Surjective π)
    (hπact : ∀ g x, ((π (act g x)).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) * ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ)
    (hC2 : ∀ c ∈ π.ker, c ^ 2 = 1) (hCfix : ∀ g, ∀ c ∈ π.ker, act g c = c)
    (hcomm : ∀ x y : P, x * y = y * x) : ∀ x : P, x ^ 2 = 1 := by
  have hinj : ∀ {x y : P}, ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) → π x = π y := fun h =>
    Multiplicative.toAdd.injective (Subtype.ext h)
  have himul : ∀ x y : P, ((π (x * y)).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) +
        ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) :=
    fun x y => by rw [map_mul, toAdd_mul, AddSubgroup.coe_add]
  have hsqmul : ∀ x y : P, (x * y) ^ 2 = x ^ 2 * y ^ 2 := fun x y =>
    (show Commute x y from hcomm x y).mul_pow 2
  have hsqker : ∀ {y : P} {Y : Matrix (Fin n) (Fin n) (ZMod 2)},
      ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = Y → y ^ 2 ∈ π.ker := by
    intro y Y hy
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [map_pow, toAdd_pow, AddSubgroup.coe_nsmul, hy, two_nsmul]
    exact binary_add_self _
  have hliftO : ∀ i j, ∃ x : P, ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      binaryOff i j := fun i j => by
    obtain ⟨x, hx⟩ := hπ (Multiplicative.ofAdd ⟨binaryOff i j,
      binaryOff_mem_binarySymMatrices i j⟩)
    exact ⟨x, by rw [hx]; rfl⟩
  have hliftD : ∀ k, ∃ x : P, ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      single k k 1 := fun k => by
    obtain ⟨x, hx⟩ := hπ (Multiplicative.ofAdd ⟨single k k 1, single_mem_binarySymMatrices k⟩)
    exact ⟨x, by rw [hx]; rfl⟩
  have hstep : ∀ (g : GL (Fin n) (ZMod 2)) (y w : P), y ^ 2 ∈ π.ker →
      π (act g y) = π (y * w) → w ^ 2 = 1 := by
    intro g y w hy hgy
    obtain ⟨c, hc, hcy⟩ : ∃ c ∈ π.ker, act g y = y * w * c :=
      ⟨(y * w)⁻¹ * act g y, by rw [MonoidHom.mem_ker, map_mul, map_inv, hgy, inv_mul_cancel],
        by group⟩
    have h : (act g y) ^ 2 = (y * w * c) ^ 2 := by rw [hcy]
    rw [← map_pow, hCfix _ _ hy, hsqmul, hsqmul, hC2 c hc, mul_one] at h
    exact mul_eq_left.mp h.symm
  have hsqO : ∀ i j (x : P), ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = binaryOff i j →
      x ^ 2 = 1 := by
    intro i j x hx
    by_cases hij : i = j
    · subst hij
      rw [binaryOff_self] at hx
      exact hC2 x (by
        rw [MonoidHom.mem_ker]
        exact Multiplicative.toAdd.injective (Subtype.ext hx))
    obtain ⟨k, hki, hkj⟩ := exists_ne_ne_of_three_le hn i j
    obtain ⟨y, hy⟩ := hliftO i k
    refine hstep (binaryTransvection hkj.symm) y x (hsqker hy) (hinj ?_)
    rw [hπact, hy, binaryOff_comm i k, binaryTransvection_congr_binaryOff_left _ hki.symm,
      himul, hy, hx, binaryOff_comm k i, binaryOff_comm j i]
  have hsqD : ∀ a (x : P), ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = single a a 1 →
      x ^ 2 = 1 := by
    intro a x hx
    obtain ⟨b, hba, -⟩ := exists_ne_ne_of_three_le hn a a
    obtain ⟨y, hy⟩ := hliftD b
    obtain ⟨w, hw⟩ := hliftO a b
    have h := hstep (binaryTransvection hba.symm) y (w * x) (hsqker hy) (hinj (by
      rw [hπact, hy, binaryTransvection_congr_diag_self, himul, himul, hy, hw, hx]))
    rwa [hsqmul, hsqO a b w hw, one_mul] at h
  let K : Subgroup P :=
    { carrier := {z | z ^ 2 = 1}
      mul_mem' := fun {a b} ha hb => by
        change (a * b) ^ 2 = 1
        rw [hsqmul, ha, hb, one_mul]
      one_mem' := one_pow 2
      inv_mem' := fun {a} ha => by
        change a⁻¹ ^ 2 = 1
        rw [inv_pow, ha, inv_one] }
  have htop : K = ⊤ := eq_top_of_lifts_binarySym π (fun c hc => hC2 c hc)
    (fun i j => by
      obtain ⟨x, hx⟩ := hliftO i j
      exact ⟨x, hsqO i j x hx, hx⟩)
    (fun k => by
      obtain ⟨x, hx⟩ := hliftD k
      exact ⟨x, hsqD k x hx, hx⟩)
  intro x
  have hx : x ∈ K := htop ▸ Subgroup.mem_top x
  exact hx

end Group

end MatrixExtension

open Matrix MatrixExtension CFSG.Assembly in
theorem binary_symmetric_matrix_central_extension_splitting {n : ℕ} (hn : 4 ≤ n) {P : Type*}
    [Group P] [Finite P] (_hP : IsPGroup 2 P) (act : GL (Fin n) (ZMod 2) →* MulAut P)
    (π : P →* Multiplicative (binarySymMatrices n)) (hπ : Function.Surjective π)
    (hπact : ∀ g x, ((π (act g x)).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) * ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ)
    (hC : π.ker ≤ Subgroup.center P) (hC2 : ∀ c ∈ π.ker, c ^ 2 = 1)
    (hCfix : ∀ g, ∀ c ∈ π.ker, act g c = c) :
    IsElemAbelian 2 (⊤ : Subgroup P) ∧
      ∃ P₀ : Subgroup P, (∀ g, ∀ x ∈ P₀, act g x ∈ P₀) ∧ π.ker ⊓ P₀ = ⊥ ∧ π.ker ⊔ P₀ = ⊤ ∧
        Function.Bijective (π.comp P₀.subtype) := by
  have hcomm := binarySym_commute hn act π hπ hπact hC hCfix
  have hsq := binarySym_sq_eq_one (by omega) act π hπ hπact hC2 hCfix hcomm
  let _ : CommGroup P := { (inferInstance : Group P) with mul_comm := hcomm }
  let _ : Module (ZMod 2) (Additive P) := AddCommGroup.zmodModule fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hsq, ofMul_one]
  let actA : GL (Fin n) (ZMod 2) →* AddMonoid.End (Additive P) :=
    { toFun := fun g => MonoidHom.toAdditive (act g).toMonoidHom
      map_one' := by
        ext x
        rw [map_one]
        rfl
      map_mul' := fun g h => by
        ext x
        rw [map_mul]
        rfl }
  have hactA : ∀ g x, actA g x = Additive.ofMul (act g x.toMul) := fun _ _ => rfl
  let πA : Additive P →+ Matrix (Fin n) (Fin n) (ZMod 2) :=
    { toFun := fun x => ((π x.toMul).toAdd : Matrix (Fin n) (Fin n) (ZMod 2))
      map_zero' := by simp
      map_add' := fun x y => by simp }
  have hπA : ∀ x, πA x = ((π x.toMul).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) := fun _ => rfl
  have hkerA : ∀ x : Additive P, πA x = 0 → x.toMul ∈ π.ker := fun x h => by
    rw [MonoidHom.mem_ker]
    exact Multiplicative.toAdd.injective (Subtype.ext h)
  have hliftA : ∀ X ∈ binarySymMatrices n, ∃ x, πA x = X := fun X hX => by
    obtain ⟨x, hx⟩ := hπ (Multiplicative.ofAdd ⟨X, hX⟩)
    exact ⟨Additive.ofMul x, by rw [hπA, toMul_ofMul, hx]; rfl⟩
  obtain ⟨S, hSinv, hSinj, hSsurj⟩ := sym_exists_invariant_complement hn (act := actA)
    (π := πA) (fun g x => by rw [hactA, hπA, hπA, toMul_ofMul, hπact])
    (fun g c hc => by rw [hactA, hCfix g _ (hkerA c hc), ofMul_toMul])
    (fun v => hliftA _ (vecMulVec_self_mem_binarySymMatrices v))
    (fun i j => hliftA _ (binaryOff_mem_binarySymMatrices i j))
  let P₀ : Subgroup P :=
    { carrier := {x | Additive.ofMul x ∈ S}
      mul_mem' := fun {a b} ha hb => by
        change Additive.ofMul (a * b) ∈ S
        rw [ofMul_mul]
        exact S.add_mem ha hb
      one_mem' := by
        change Additive.ofMul (1 : P) ∈ S
        rw [ofMul_one]
        exact S.zero_mem
      inv_mem' := fun {a} ha => by
        change Additive.ofMul a⁻¹ ∈ S
        rw [ofMul_inv]
        exact S.neg_mem ha }
  have hP₀ : ∀ x, x ∈ P₀ ↔ Additive.ofMul x ∈ S := fun _ => Iff.rfl
  have hone : ∀ x ∈ P₀, π x = 1 → x = 1 := fun x hx h => by
    have h' := hSinj (Additive.ofMul x) hx (by
      rw [hπA, toMul_ofMul, h]
      rfl)
    rwa [← ofMul_one, Additive.ofMul.injective.eq_iff] at h'
  have hexists : ∀ v : Multiplicative (binarySymMatrices n), ∃ x ∈ P₀, π x = v := fun v => by
    obtain ⟨s, hs, hsv⟩ := hSsurj _ v.toAdd.2
    exact ⟨s.toMul, by rwa [hP₀, ofMul_toMul], Multiplicative.toAdd.injective
      (Subtype.ext (by rw [← hsv, hπA]))⟩
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩, fun x _ => hsq x⟩, P₀,
    fun g x hx => ?_, ?_, ?_, ⟨?_, fun v => ?_⟩⟩
  · rw [hP₀] at hx ⊢
    have := hSinv g _ hx
    rwa [hactA, toMul_ofMul] at this
  · refine eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hone x hx.2 hx.1)
  · refine eq_top_iff.mpr fun z _ => ?_
    obtain ⟨y, hy, hyz⟩ := hexists (π z)
    have hzy : z * y⁻¹ ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hyz, mul_inv_cancel]
    have := Subgroup.mul_mem_sup hzy hy
    rwa [inv_mul_cancel_right] at this
  · rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hone x x.2 hx)
  · obtain ⟨x, hx, hxv⟩ := hexists v
    exact ⟨⟨x, hx⟩, hxv⟩

end CFSG.LocalAnalysis.ComponentInitial
