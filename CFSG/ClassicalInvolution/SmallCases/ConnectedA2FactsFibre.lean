module

public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2FactsBasic

public section

namespace CFSG.ClassicalInvolution.ConnectedA2

open scoped IsMulCommutative MatrixGroups
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Generic.DeltaClosure

theorem exists_sq_add_sq_eq_neg_one (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ a b : F, a ^ 2 + b ^ 2 = -1 := by
  classical
  have := Fintype.ofFinite F
  have hcard : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  obtain ⟨a, b, h⟩ := FiniteField.exists_root_sum_quadratic
    (f := (Polynomial.X ^ 2 : Polynomial F))
    (g := (Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial F)) (by simp)
    (by rw [Polynomial.degree_X_pow_add_C (by norm_num)]; simp) hcard
  refine ⟨a, b, ?_⟩
  simp at h
  linear_combination h

theorem exists_sl2_quaternion (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ i j : SL(2, F), i * i = -1 ∧ j * j = -1 ∧ i * j = -1 * (j * i) := by
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq_eq_neg_one F hodd
  refine ⟨⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩,
    ⟨!![a, b; b, -a], by simp [Matrix.det_fin_two]; linear_combination -hab⟩, ?_, ?_, ?_⟩
  · refine Subtype.ext ?_
    show (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] = -1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · refine Subtype.ext ?_
    show (!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) F) * !![a, b; b, -a] = -1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination hab | linear_combination (-1 : F) * hab | ring1
  · refine Subtype.ext ?_
    show (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * !![a, b; b, -a] =
      -1 * (!![a, b; b, -a] * !![0, -1; 1, 0])
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

section ElemAbelian

variable {G : Type} [Group G]

omit [Group G] in
theorem pairwise_commute_triple {G : Type} [Group G] {a b c : G} (hab : a * b = b * a)
    (hac : a * c = c * a) (hbc : b * c = c * b) :
    ({a, b, c} : Set G).Pairwise Commute := by
  intro x hx y hy _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with h | h | h <;> rcases hy with h' | h' | h' <;> subst h h'
  all_goals first
    | exact Commute.refl _
    | exact hab
    | exact hab.symm
    | exact hac
    | exact hac.symm
    | exact hbc
    | exact hbc.symm

theorem isElemAbelian_closure_triple {a b c : G} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    IsElemAbelian 2 (Subgroup.closure ({a, b, c} : Set G)) := by
  have hcomm : IsMulCommutative (Subgroup.closure ({a, b, c} : Set G)) :=
    Subgroup.isMulCommutative_closure (pairwise_commute_triple hab hac hbc)
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> simpa [sq] using ‹_›
  | one => simp
  | mul y z hy' hz' hy hz =>
    have hc' : y * z = z * y := by
      have h := hcomm.is_comm.comm (⟨y, hy'⟩ : Subgroup.closure ({a, b, c} : Set G)) ⟨z, hz'⟩
      exact congrArg Subtype.val h
    rw [sq] at hy hz ⊢
    calc y * z * (y * z) = y * (z * y) * z := by group
      _ = y * (y * z) * z := by rw [← hc']
      _ = (y * y) * (z * z) := by group
      _ = 1 := by rw [hy, hz, one_mul]
  | inv y _ hy => rw [inv_pow, hy, inv_one]

variable [Finite G]

theorem eight_le_card_closure_triple {a b c : G} (ha : a * a = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab' : a ≠ b) (hcn : c ∉ Subgroup.closure ({a, b} : Set G)) :
    8 ≤ Nat.card (Subgroup.closure ({a, b, c} : Set G)) := by
  set E₂ := Subgroup.closure ({a, b} : Set G) with hE₂
  set E₃ := Subgroup.closure ({a, b, c} : Set G) with hE₃
  have hle : E₂ ≤ E₃ := Subgroup.closure_mono (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto)
  have hcE₃ : c ∈ E₃ := Subgroup.subset_closure (by simp)
  have h4 : 4 ≤ Nat.card E₂ := by
    have hsub : ({1, a, b, a * b} : Set G) ⊆ (E₂ : Set G) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact E₂.one_mem
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact E₂.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [ncard_klein_four ha1 hb1 hab' ha] at h1
    have h2 : Nat.card E₂ = (E₂ : Set G).ncard := Nat.card_coe_set_eq (E₂ : Set G)
    omega
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card E₃ := Nat.card_pos
  have hk1 : k ≠ 1 := by
    intro h
    rw [h, mul_one] at hk
    have heq : E₂ = E₃ := Subgroup.eq_of_le_of_card_ge hle hk.le
    exact hcn (heq ▸ hcE₃)
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, mul_zero] at hk
    omega
  have hk2 : 2 ≤ k := by omega
  calc 8 = 4 * 2 := by norm_num
    _ ≤ Nat.card E₂ * k := Nat.mul_le_mul h4 hk2
    _ = Nat.card E₃ := hk.symm

theorem exists_elemAbelian_eight {E : Subgroup G} (hE : IsElemAbelian 2 E) (h8 : 8 ≤ Nat.card E)
    {a : G} (haE : a ∈ E) (ha : a * a = 1) :
    ∃ B : Subgroup G, B ≤ E ∧ IsElemAbelian 2 B ∧ Nat.card B = 8 ∧ a ∈ B := by
  have hpg : IsPGroup 2 E := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hE.2 g g.2
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hpg
  have hn3 : 3 ≤ n := by
    by_contra h
    push Not at h
    have : Nat.card E ≤ 4 := by
      rw [hn]
      calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by norm_num
    omega
  have hdvd : 2 ^ 3 ∣ Nat.card E := by
    rw [hn]
    exact pow_dvd_pow 2 hn3
  have hwE : Subgroup.zpowers a ≤ E := (Subgroup.zpowers_le).mpr haE
  have hcarda : Nat.card (Subgroup.zpowers a) ∣ 2 ^ 3 := by
    rw [Nat.card_zpowers]
    refine (orderOf_dvd_of_pow_eq_one ?_).trans (by norm_num : 2 ∣ 2 ^ 3)
    rw [pow_two]
    exact ha
  obtain ⟨B, hBcard, haB, hBE⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two hcarda hdvd hwE
  have hcomm : IsMulCommutative B := ⟨⟨fun x y => by
    apply Subtype.ext
    have := congrArg Subtype.val (hE.1.is_comm.comm (⟨x.1, hBE x.2⟩ : E) ⟨y.1, hBE y.2⟩)
    exact this⟩⟩
  exact ⟨B, hBE, ⟨hcomm, fun x hx => hE.2 x (hBE hx)⟩, by rw [hBcard]; norm_num,
    haB (Subgroup.mem_zpowers a)⟩

end ElemAbelian

section Twins

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

omit [Finite G] in
theorem le_centralizer_closure_of {S : Set G} {M : Subgroup G}
    (h : ∀ m ∈ M, ∀ g ∈ S, m * g = g * m) :
    M ≤ Subgroup.centralizer (Subgroup.closure S : Set G) := by
  intro m hm
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hle : Subgroup.closure S ≤ Subgroup.centralizer ({m} : Set G) :=
    (Subgroup.closure_le _).mpr fun g hg => by
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (h m hm g hg).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem exists_elemAbelian_eight_of_twin_charts (hodd : Odd (Nat.card F))
    {φ₁ φ₂ : SL(2, F) →* G} (h₁ : Function.Injective φ₁)
    (hc : ∀ x y, φ₁ x * φ₂ y = φ₂ y * φ₁ x) (hw : φ₁ (-1) = φ₂ (-1)) {M : Subgroup G}
    (hM₁ : ∀ m ∈ M, ∀ x, m * φ₁ x = φ₁ x * m) (hM₂ : ∀ m ∈ M, ∀ y, m * φ₂ y = φ₂ y * m)
    {m : G} (hmM : m ∈ M) (hm : m * m = 1) (hm1 : m ≠ 1) (hmc : ∀ m' ∈ M, m' * m = m * m') :
    ∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ m ∈ E ∧
      M ≤ Subgroup.centralizer (E : Set G) := by
  obtain ⟨i, j, hii, hjj, hij⟩ := exists_sl2_quaternion F hodd
  obtain ⟨w, hwdef⟩ : ∃ w : G, w = φ₁ (-1) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : G, s = φ₁ i := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : G, t = φ₁ j := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s' : G, s' = φ₂ i := ⟨_, rfl⟩
  obtain ⟨t', ht'⟩ : ∃ t' : G, t' = φ₂ j := ⟨_, rfl⟩
  have hw1 : w ≠ 1 := by
    rw [hwdef]
    exact fun h => sl2_neg_one_ne_one hodd (h₁ (h.trans (map_one φ₁).symm))
  have hww : w * w = 1 := by
    rw [hwdef, ← map_mul]
    have : (-1 : SL(2, F)) * -1 = 1 := by
      calc (-1 : SL(2, F)) * -1 = -1 * (-1)⁻¹ := by rw [neg_one_inv]
        _ = 1 := mul_inv_cancel _
    rw [this, map_one]
  have hss : s * s = w := by rw [hs, hwdef, ← map_mul, hii]
  have htt : t * t = w := by rw [ht, hwdef, ← map_mul, hjj]
  have hss' : s' * s' = w := by rw [hs', hwdef, hw, ← map_mul, hii]
  have htt' : t' * t' = w := by rw [ht', hwdef, hw, ← map_mul, hjj]
  have hst : s * t = w * (t * s) := by
    rw [hs, ht, hwdef, ← map_mul, ← map_mul, ← map_mul, hij]
  have hnst : s * t ≠ t * s := by
    intro h
    apply hw1
    have h2 : w * (t * s) = 1 * (t * s) := by rw [← hst, h, one_mul]
    exact mul_right_cancel h2
  have hw₁ : ∀ x, w * φ₁ x = φ₁ x * w := fun x => by
    rw [hwdef, ← map_mul, ← map_mul, mul_neg_one_comm]
  have hw₂ : ∀ y, w * φ₂ y = φ₂ y * w := fun y => by
    rw [hwdef, hw, ← map_mul, ← map_mul, mul_neg_one_comm]
  have hwM : ∀ m' ∈ M, m' * w = w * m' := fun m' hm' => by
    rw [hwdef]; exact hM₁ m' hm' (-1)
  have hws : w * s = s * w := by rw [hs]; exact hw₁ i
  have hwt : w * t = t * w := by rw [ht]; exact hw₁ j
  have hwr₂ : w ∈ φ₂.range := ⟨-1, by rw [hwdef, hw]⟩
  have hs'r : s' ∈ φ₂.range := ⟨i, hs'.symm⟩
  have ht'r : t' ∈ φ₂.range := ⟨j, ht'.symm⟩
  have hcen : ∀ x, φ₁ x ∈ φ₂.range → ∀ y, φ₁ x * φ₁ y = φ₁ y * φ₁ x := by
    rintro x ⟨u, hu⟩ y
    rw [← hu]
    exact (hc y u).symm
  have hs_ne : ∀ r : G, r ∈ φ₂.range → s ≠ r := by
    intro r hr h
    apply hnst
    have hsr : φ₁ i ∈ φ₂.range := by rw [← hs, h]; exact hr
    have := hcen i hsr j
    rwa [← hs, ← ht] at this
  have ht_ne : ∀ r : G, r ∈ φ₂.range → t ≠ r := by
    intro r hr h
    apply hnst
    have htr : φ₁ j ∈ φ₂.range := by rw [← ht, h]; exact hr
    have := hcen j htr i
    rw [← hs, ← ht] at this
    exact this.symm
  have hX : ∀ r : G, r ∈ φ₂.range → s⁻¹ * t ≠ r := by
    intro r hr h
    have hmem : φ₁ (i⁻¹ * j) ∈ φ₂.range := by
      rw [map_mul, map_inv, ← hs, ← ht, h]
      exact hr
    have h1 := hcen (i⁻¹ * j) hmem i
    rw [map_mul, map_inv, ← hs, ← ht] at h1
    have h1' : s⁻¹ * t * s = t := by rw [h1]; group
    apply hnst
    calc s * t = s * (s⁻¹ * t * s) := by rw [h1']
      _ = t * s := by group
  have hsc : s * s' = s' * s := by rw [hs, hs']; exact hc i i
  have htc : t * t' = t' * t := by rw [ht, ht']; exact hc j j
  have hst' : s * t' = t' * s := by rw [hs, ht']; exact hc i j
  have hts' : t * s' = s' * t := by rw [ht, hs']; exact hc j i
  have hs't' : s' * t' = w * (t' * s') := by
    rw [hs', ht', hwdef, hw, ← map_mul, ← map_mul, ← map_mul, hij]
  obtain ⟨u₁, hu₁⟩ : ∃ u : G, u = s * s' := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u : G, u = t * t' := ⟨_, rfl⟩
  have hu₁sq : u₁ * u₁ = 1 := by
    rw [hu₁]
    calc s * s' * (s * s') = s * (s' * s) * s' := by group
      _ = s * (s * s') * s' := by rw [← hsc]
      _ = (s * s) * (s' * s') := by group
      _ = 1 := by rw [hss, hss', hww]
  have hu₂sq : u₂ * u₂ = 1 := by
    rw [hu₂]
    calc t * t' * (t * t') = t * (t' * t) * t' := by group
      _ = t * (t * t') * t' := by rw [← htc]
      _ = (t * t) * (t' * t') := by group
      _ = 1 := by rw [htt, htt', hww]
  have hwu₁ : w * u₁ = u₁ * w := by
    rw [hu₁, ← mul_assoc, hws, mul_assoc, show w * s' = s' * w by rw [hs']; exact hw₂ i,
      ← mul_assoc]
  have hwu₂ : w * u₂ = u₂ * w := by
    rw [hu₂, ← mul_assoc, hwt, mul_assoc, show w * t' = t' * w by rw [ht']; exact hw₂ j,
      ← mul_assoc]
  have hu₁₂ : u₁ * u₂ = u₂ * u₁ := by
    have e1 : s * s' * (t * t') = (s * t) * (s' * t') := by
      calc s * s' * (t * t') = s * (s' * t) * t' := by group
        _ = s * (t * s') * t' := by rw [← hts']
        _ = (s * t) * (s' * t') := by group
    have e2 : t * t' * (s * s') = (t * s) * (t' * s') := by
      calc t * t' * (s * s') = t * (t' * s) * s' := by group
        _ = t * (s * t') * s' := by rw [← hst']
        _ = (t * s) * (t' * s') := by group
    have hwc : ∀ a b : G, w * a = a * w → a * w * b = w * a * b := fun a b h => by rw [h]
    rw [hu₁, hu₂, e1, e2, hst, hs't']
    have hwts : w * (t * s) = (t * s) * w := by
      rw [mul_assoc, ← mul_assoc w t s, hwt, mul_assoc, hws, ← mul_assoc]
    calc w * (t * s) * (w * (t' * s')) = w * ((t * s) * w) * (t' * s') := by group
      _ = w * (w * (t * s)) * (t' * s') := by rw [← hwts]
      _ = (w * w) * ((t * s) * (t' * s')) := by group
      _ = (t * s) * (t' * s') := by rw [hww, one_mul]
  have hMs : ∀ m' ∈ M, m' * s = s * m' := fun m' hm' => by rw [hs]; exact hM₁ m' hm' i
  have hMt : ∀ m' ∈ M, m' * t = t * m' := fun m' hm' => by rw [ht]; exact hM₁ m' hm' j
  have hMs' : ∀ m' ∈ M, m' * s' = s' * m' := fun m' hm' => by rw [hs']; exact hM₂ m' hm' i
  have hMt' : ∀ m' ∈ M, m' * t' = t' * m' := fun m' hm' => by rw [ht']; exact hM₂ m' hm' j
  have hMu₁ : ∀ m' ∈ M, m' * u₁ = u₁ * m' := fun m' hm' => by
    rw [hu₁, ← mul_assoc, hMs m' hm', mul_assoc, hMs' m' hm', ← mul_assoc]
  have hMu₂ : ∀ m' ∈ M, m' * u₂ = u₂ * m' := fun m' hm' => by
    rw [hu₂, ← mul_assoc, hMt m' hm', mul_assoc, hMt' m' hm', ← mul_assoc]
  have hu₁t : u₁ * t ≠ t * u₁ := by
    intro h
    apply hnst
    rw [hu₁] at h
    have h2 : s * t * s' = t * s * s' := by
      calc s * t * s' = s * (t * s') := by rw [mul_assoc]
        _ = s * (s' * t) := by rw [hts']
        _ = s * s' * t := by rw [← mul_assoc]
        _ = t * (s * s') := h
        _ = t * s * s' := by rw [mul_assoc]
    exact mul_right_cancel h2
  have hu₁1 : u₁ ≠ 1 := by
    intro h
    rw [hu₁] at h
    exact hs_ne s'⁻¹ (Subgroup.inv_mem _ hs'r) (eq_inv_of_mul_eq_one_left h)
  have hu₁w : w ≠ u₁ := by
    intro h
    rw [hu₁] at h
    refine hs_ne (w * s'⁻¹) (Subgroup.mul_mem _ hwr₂ (Subgroup.inv_mem _ hs'r)) ?_
    exact eq_mul_inv_of_mul_eq h.symm
  by_cases hmw : m = w
  ·
    have hcn : u₂ ∉ Subgroup.closure ({w, u₁} : Set G) := by
      intro hmem
      rcases closure_pair_mem hww hu₁sq hwu₁ hmem with h | h | h | h
      · rw [hu₂] at h
        exact ht_ne t'⁻¹ (Subgroup.inv_mem _ ht'r) (eq_inv_of_mul_eq_one_left h)
      · rw [hu₂] at h
        exact ht_ne (w * t'⁻¹) (Subgroup.mul_mem _ hwr₂ (Subgroup.inv_mem _ ht'r))
          (eq_mul_inv_of_mul_eq h)
      · rw [hu₂, hu₁] at h
        refine hX (s' * t'⁻¹) (Subgroup.mul_mem _ hs'r (Subgroup.inv_mem _ ht'r)) ?_
        calc s⁻¹ * t = s⁻¹ * (t * t') * t'⁻¹ := by group
          _ = s⁻¹ * (s * s') * t'⁻¹ := by rw [h]
          _ = s' * t'⁻¹ := by group
      · rw [hu₂, hu₁] at h
        have hws' : w * s⁻¹ = s⁻¹ * w := (Commute.inv_right (show Commute w s from hws))
        refine hX (w * s' * t'⁻¹) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hwr₂ hs'r)
          (Subgroup.inv_mem _ ht'r)) ?_
        calc s⁻¹ * t = s⁻¹ * (t * t') * t'⁻¹ := by group
          _ = s⁻¹ * (w * (s * s')) * t'⁻¹ := by rw [h]
          _ = (s⁻¹ * w) * (s * s') * t'⁻¹ := by rw [mul_assoc s⁻¹ w]
          _ = (w * s⁻¹) * (s * s') * t'⁻¹ := by rw [← hws']
          _ = w * (s⁻¹ * (s * s')) * t'⁻¹ := by rw [mul_assoc w]
          _ = w * s' * t'⁻¹ := by rw [inv_mul_cancel_left]
    have hE' := isElemAbelian_closure_triple hww hu₁sq hu₂sq hwu₁ hwu₂ hu₁₂
    have h8 := eight_le_card_closure_triple hww hw1 hu₁1 hu₁w hcn
    obtain ⟨E, hEle, hEel, hEcard, hwE⟩ :=
      exists_elemAbelian_eight hE' h8 (Subgroup.subset_closure (by simp)) hww
    refine ⟨E, hEel, hEcard, hmw ▸ hwE, ?_⟩
    have hMc := le_centralizer_closure_of (M := M) (S := ({w, u₁, u₂} : Set G)) (by
      intro m' hm' g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact hwM m' hm'
      · exact hMu₁ m' hm'
      · exact hMu₂ m' hm')
    intro m' hm'
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp (hMc hm') x (hEle hx)
  ·
    have hmwc : m * w = w * m := hwM m hmM
    have hmu₁ : m * u₁ = u₁ * m := hMu₁ m hmM
    have hcn : u₁ ∉ Subgroup.closure ({m, w} : Set G) := by
      intro hmem
      have hle : Subgroup.closure ({m, w} : Set G) ≤ Subgroup.centralizer ({t} : Set G) :=
        (Subgroup.closure_le _).mpr (by
          intro g hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
          rcases hg with rfl | rfl
          · exact hMt g hmM
          · exact hwt)
      exact hu₁t (Subgroup.mem_centralizer_singleton_iff.mp (hle hmem))
    have hE' := isElemAbelian_closure_triple hm hww hu₁sq hmwc hmu₁ hwu₁
    have h8 := eight_le_card_closure_triple hm hm1 hw1 hmw hcn
    obtain ⟨E, hEle, hEel, hEcard, hmE⟩ :=
      exists_elemAbelian_eight hE' h8 (Subgroup.subset_closure (by simp)) hm
    refine ⟨E, hEel, hEcard, hmE, ?_⟩
    have hMc := le_centralizer_closure_of (M := M) (S := ({m, w, u₁} : Set G)) (by
      intro m' hm' g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact hmc m' hm'
      · exact hwM m' hm'
      · exact hMu₁ m' hm')
    intro m' hm'
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp (hMc hm') x (hEle hx)

end Twins

section FrameBoot

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {F : Type}
  [Field F] {A : Subgroup G} {S : Set (Subgroup G)}

theorem bootData_of_twins {K : Subgroup G} {z : G} (hb : Branch p f K z)
    (hex : ExactMembers (conjClass K)) (Fr : RankFrame F (conjClass K) A S)
    (hP1 : FrameP1 (conjClass K) A) {K₁ K₂ M : Subgroup G} (h₁ : K₁ ∈ S) (h₂ : K₂ ∈ S)
    (hM : M ∈ S) {w : G} (hw₁ : IsUniqueInvolution K₁ w) (hw₂ : IsUniqueInvolution K₂ w)
    (hne : K₁ ≠ K₂) (hc₁ : Commutes M K₁) (hc₂ : Commutes M K₂) :
    BootData p f (conjClass K) := by
  have : Finite F := Fr.finite
  have hodd := Fr.odd
  obtain ⟨φ₁, hφ₁, hD₁⟩ := Fr.inSigma h₁
  obtain ⟨φ₂, hφ₂, hD₂⟩ := Fr.inSigma h₂
  have hu₁ := hD₁.isUniqueInvolution hodd
  have hu₂ := hD₂.isUniqueInvolution hodd
  rw [hφ₁] at hu₁
  rw [hφ₂] at hu₂
  have hw₁' : w = φ₁ (-1) := hw₁.eq hu₁
  have hw₂' : w = φ₂ (-1) := hw₂.eq hu₂
  have hcom := commutes_of_same_involution hb hex Fr hP1 h₁ h₂ hw₁ hw₂ hne
  have hmem₁ : ∀ x, φ₁ x ∈ K₁ := fun x => by rw [← hφ₁]; exact ⟨x, rfl⟩
  have hmem₂ : ∀ y, φ₂ y ∈ K₂ := fun y => by rw [← hφ₂]; exact ⟨y, rfl⟩
  obtain ⟨m, hm⟩ := Fr.exists_isUniqueInvolution hM
  obtain ⟨E, hEel, hEcard, hmE, hME⟩ := exists_elemAbelian_eight_of_twin_charts hodd hD₁.inj
    (fun x y => hcom _ (hmem₁ x) _ (hmem₂ y)) (hw₁'.symm.trans hw₂')
    (M := M) (fun m' hm' x => hc₁ m' hm' _ (hmem₁ x)) (fun m' hm' y => hc₂ m' hm' _ (hmem₂ y))
    hm.mem hm.sq hm.ne_one (fun m' hm' => mul_comm_of_isUniqueInvolution hm hm')
  exact ⟨M, m, E, Fr.subset hM, isClassicalMember_of_isUniqueInvolution hb.member (Fr.subset hM) hm,
    hEel, hEcard, hmE, hME⟩

theorem fibreLE2_of_branch {K : Subgroup G} {z : G} (hb : Branch p f K z)
    (hex : ExactMembers (conjClass K)) (Fr : RankFrame F (conjClass K) A S)
    (hP1 : FrameP1 (conjClass K) A) : FibreLE2 S := by
  intro w K₁ h₁ K₂ h₂ K₃ h₃ hw₁ hw₂ hw₃
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h12, h13, h23⟩ := hcon
  exact hb.noBoot (bootData_of_twins hb hex Fr hP1 h₁ h₂ h₃ hw₁ hw₂ h12
    (commutes_of_same_involution hb hex Fr hP1 h₃ h₁ hw₃ hw₁ (Ne.symm h13))
    (commutes_of_same_involution hb hex Fr hP1 h₃ h₂ hw₃ hw₂ (Ne.symm h23)))

end FrameBoot

end CFSG.ClassicalInvolution.ConnectedA2
