module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434General

public section

open CFSG.Open

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434

structure HeisRel {G : Type*} [Group G] (a b c : G) : Prop where
  ha : a ^ 5 = 1
  hb : b ^ 5 = 1
  hc : c ^ 5 = 1
  ac : a * c = c * a
  bc : b * c = c * b
  ab : a * b = c * (b * a)

namespace HeisRel

variable {G : Type*} [Group G] {a b c : G}

theorem commute_ac (h : HeisRel a b c) : Commute a c := h.ac

theorem commute_bc (h : HeisRel a b c) : Commute b c := h.bc

theorem ba (h : HeisRel a b c) : b * a = c ^ 4 * (a * b) := by
  have h1 : c * (b * a) = a * b := h.ab.symm
  have h2 : c ^ 4 * (c * (b * a)) = b * a := by
    rw [← mul_assoc, ← pow_succ, h.hc]; simp
  rw [h1] at h2
  exact h2.symm

theorem b_mul_a_pow (h : HeisRel a b c) (i : ℕ) : b * a ^ i = c ^ (4 * i) * (a ^ i * b) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hca : Commute (a ^ i) (c ^ 4) := h.commute_ac.pow_pow i 4
    calc b * a ^ (i + 1) = (b * a ^ i) * a := by rw [pow_succ, ← mul_assoc]
      _ = c ^ (4 * i) * (a ^ i * b) * a := by rw [ih]
      _ = c ^ (4 * i) * (a ^ i * (b * a)) := by simp only [mul_assoc]
      _ = c ^ (4 * i) * (a ^ i * (c ^ 4 * (a * b))) := by rw [h.ba]
      _ = c ^ (4 * i) * (c ^ 4 * (a ^ i * (a * b))) := by rw [hca.left_comm]
      _ = c ^ (4 * i + 4) * (a ^ (i + 1) * b) := by
        rw [pow_add c, pow_succ a i]; simp only [mul_assoc]
      _ = c ^ (4 * (i + 1)) * (a ^ (i + 1) * b) := by rw [Nat.mul_succ]

theorem b_pow_mul_a_pow (h : HeisRel a b c) (i j : ℕ) :
    b ^ j * a ^ i = c ^ (4 * i * j) * (a ^ i * b ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hbc : Commute b (c ^ (4 * i * j)) := h.commute_bc.pow_right _
    calc b ^ (j + 1) * a ^ i = b * (b ^ j * a ^ i) := by rw [pow_succ', mul_assoc]
      _ = b * (c ^ (4 * i * j) * (a ^ i * b ^ j)) := by rw [ih]
      _ = c ^ (4 * i * j) * (b * (a ^ i * b ^ j)) := by rw [hbc.left_comm]
      _ = c ^ (4 * i * j) * ((b * a ^ i) * b ^ j) := by rw [← mul_assoc b]
      _ = c ^ (4 * i * j) * ((c ^ (4 * i) * (a ^ i * b)) * b ^ j) := by rw [h.b_mul_a_pow i]
      _ = c ^ (4 * i * j) * (c ^ (4 * i) * (a ^ i * (b * b ^ j))) := by simp only [mul_assoc]
      _ = c ^ (4 * i * j + 4 * i) * (a ^ i * b ^ (j + 1)) := by
        rw [pow_add c, pow_succ' b j, mul_assoc (c ^ (4 * i * j))]
      _ = c ^ (4 * i * (j + 1)) * (a ^ i * b ^ (j + 1)) := by rw [Nat.mul_succ]

theorem mul_normal (h : HeisRel a b c) (i j k i' j' k' : ℕ) :
    (a ^ i * b ^ j * c ^ k) * (a ^ i' * b ^ j' * c ^ k') =
      a ^ (i + i') * b ^ (j + j') * c ^ (k + k' + 4 * i' * j) := by
  have hCA' : Commute (c ^ k) (a ^ i') := (h.commute_ac.pow_pow i' k).symm
  have hAZ : Commute (a ^ i) (c ^ (4 * i' * j)) := h.commute_ac.pow_pow _ _
  have hBC : Commute (b ^ j) (c ^ k) := h.commute_bc.pow_pow _ _
  have hBZ : Commute (b ^ (j + j')) (c ^ (4 * i' * j)) := h.commute_bc.pow_pow _ _
  have hCB : Commute (c ^ k) (b ^ (j + j')) := (h.commute_bc.pow_pow _ _).symm
  have hZA : Commute (c ^ (4 * i' * j)) (a ^ (i + i')) := (h.commute_ac.pow_pow _ _).symm
  have hZB : Commute (c ^ (4 * i' * j)) (b ^ (j + j')) := (h.commute_bc.pow_pow _ _).symm
  have hAA : a ^ i * a ^ i' = a ^ (i + i') := (pow_add a i i').symm
  have hBB : b ^ j * b ^ j' = b ^ (j + j') := (pow_add b j j').symm
  calc (a ^ i * b ^ j * c ^ k) * (a ^ i' * b ^ j' * c ^ k')
      = a ^ i * (b ^ j * (c ^ k * (a ^ i' * (b ^ j' * c ^ k')))) := by simp only [mul_assoc]
    _ = a ^ i * (b ^ j * (a ^ i' * (c ^ k * (b ^ j' * c ^ k')))) := by rw [hCA'.left_comm]
    _ = a ^ i * ((b ^ j * a ^ i') * (c ^ k * (b ^ j' * c ^ k'))) := by simp only [mul_assoc]
    _ = a ^ i * ((c ^ (4 * i' * j) * (a ^ i' * b ^ j)) * (c ^ k * (b ^ j' * c ^ k'))) := by
        rw [h.b_pow_mul_a_pow i' j]
    _ = a ^ i * (c ^ (4 * i' * j) * (a ^ i' * (b ^ j * (c ^ k * (b ^ j' * c ^ k'))))) := by
        simp only [mul_assoc]
    _ = c ^ (4 * i' * j) * (a ^ i * (a ^ i' * (b ^ j * (c ^ k * (b ^ j' * c ^ k'))))) := by
        rw [hAZ.left_comm]
    _ = c ^ (4 * i' * j) * (a ^ i * (a ^ i' * (c ^ k * (b ^ j * (b ^ j' * c ^ k'))))) := by
        rw [hBC.left_comm]
    _ = c ^ (4 * i' * j) * ((a ^ i * a ^ i') * (c ^ k * (b ^ (j + j') * c ^ k'))) := by
        rw [← hBB, ← mul_assoc (a ^ i)]; simp only [mul_assoc]
    _ = c ^ (4 * i' * j) * ((a ^ (i + i')) * (b ^ (j + j') * (c ^ k * c ^ k'))) := by
        rw [hAA, hCB.left_comm]
    _ = a ^ (i + i') * (b ^ (j + j') * (c ^ (4 * i' * j) * (c ^ k * c ^ k'))) := by
        rw [hZA.left_comm, hZB.left_comm]
    _ = a ^ (i + i') * b ^ (j + j') * c ^ (k + k' + 4 * i' * j) := by
        rw [← mul_assoc (a ^ (i + i')), ← pow_add, ← pow_add]
        congr 2
        · omega

theorem pow_normal (h : HeisRel a b c) (i j k n : ℕ) :
    (a ^ i * b ^ j * c ^ k) ^ n =
      a ^ (n * i) * b ^ (n * j) * c ^ (n * k + 4 * i * j * n.choose 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, h.mul_normal]
    have e1 : n * i + i = (n + 1) * i := by ring
    have e2 : n * j + j = (n + 1) * j := by ring
    have e3 : n * k + 4 * i * j * n.choose 2 + k + 4 * i * (n * j) =
        (n + 1) * k + 4 * i * j * (n + 1).choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      ring
    rw [e1, e2, e3]

theorem normal_pow_five (h : HeisRel a b c) (i j k : ℕ) : (a ^ i * b ^ j * c ^ k) ^ 5 = 1 := by
  rw [h.pow_normal]
  have h1 : a ^ (5 * i) = 1 := by rw [pow_mul, h.ha, one_pow]
  have h2 : b ^ (5 * j) = 1 := by rw [pow_mul, h.hb, one_pow]
  have h3 : c ^ (5 * k + 4 * i * j * Nat.choose 5 2) = 1 := by
    have : 5 * k + 4 * i * j * Nat.choose 5 2 = 5 * (k + 8 * i * j) := by
      rw [show Nat.choose 5 2 = 10 by decide]; ring
    rw [this, pow_mul, h.hc, one_pow]
  rw [h1, h2, h3]
  simp

@[expose] def subgroup (h : HeisRel a b c) : Subgroup G where
  carrier := {g | ∃ i j k : ℕ, g = a ^ i * b ^ j * c ^ k}
  one_mem' := ⟨0, 0, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨i, j, k, rfl⟩ ⟨i', j', k', rfl⟩
    exact ⟨i + i', j + j', k + k' + 4 * i' * j, h.mul_normal i j k i' j' k'⟩
  inv_mem' := by
    rintro _ ⟨i, j, k, rfl⟩
    have h5 := h.normal_pow_five i j k
    have h4 : (a ^ i * b ^ j * c ^ k)⁻¹ = (a ^ i * b ^ j * c ^ k) ^ 4 := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ']
      exact h5
    rw [h4, h.pow_normal]
    exact ⟨4 * i, 4 * j, 4 * k + 4 * i * j * Nat.choose 4 2, rfl⟩

theorem a_mem (h : HeisRel a b c) : a ∈ h.subgroup := ⟨1, 0, 0, by simp⟩

theorem b_mem (h : HeisRel a b c) : b ∈ h.subgroup := ⟨0, 1, 0, by simp⟩

theorem isPGroup (h : HeisRel a b c) : IsPGroup 5 h.subgroup := by
  intro g
  obtain ⟨i, j, k, hg⟩ := g.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rw [pow_one, Subgroup.coe_pow, hg]
  exact h.normal_pow_five i j k

theorem not_isMulCommutative (h : HeisRel a b c) (hc1 : c ≠ 1) :
    ¬ IsMulCommutative h.subgroup := by
  intro hcomm
  have hab : a * b = b * a :=
    congrArg Subtype.val (mul_comm' (⟨a, h.a_mem⟩ : h.subgroup) ⟨b, h.b_mem⟩)
  apply hc1
  have : c * (b * a) = 1 * (b * a) := by rw [← h.ab, hab, one_mul]
  exact mul_right_cancel this

theorem exists_pGroup (h : HeisRel a b c) (hc1 : c ≠ 1) :
    ∃ P : Subgroup G, IsPGroup 5 P ∧ ¬ IsMulCommutative P :=
  ⟨h.subgroup, h.isPGroup, h.not_isMulCommutative hc1⟩

theorem map {G' : Type*} [Group G'] (h : HeisRel a b c) (f : G →* G') : HeisRel (f a) (f b) (f c) where
  ha := by rw [← map_pow, h.ha, map_one]
  hb := by rw [← map_pow, h.hb, map_one]
  hc := by rw [← map_pow, h.hc, map_one]
  ac := by rw [← map_mul, ← map_mul, h.ac]
  bc := by rw [← map_mul, ← map_mul, h.bc]
  ab := by rw [← map_mul, ← map_mul, ← map_mul, h.ab]

end HeisRel

@[expose] def HasNonabelianFiveSubgroup (G : Type*) [Group G] : Prop :=
  ∃ P : Subgroup G, IsPGroup 5 P ∧ ¬ IsMulCommutative P

namespace HasNonabelianFiveSubgroup

variable {G H : Type*} [Group G] [Group H]

theorem of_injective {f : G →* H} (hf : Function.Injective f) (h : HasNonabelianFiveSubgroup G) :
    HasNonabelianFiveSubgroup H := by
  obtain ⟨P, hP, hnc⟩ := h
  refine ⟨P.map f, hP.map f, ?_⟩
  · intro hc
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    have := mul_comm' (⟨f a, ⟨a, a.2, rfl⟩⟩ : P.map f) ⟨f b, ⟨b, b.2, rfl⟩⟩
    have h2 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul, ← map_mul] at h2
    exact Subtype.ext (hf h2)

theorem of_mulEquiv (e : G ≃* H) (h : HasNonabelianFiveSubgroup G) : HasNonabelianFiveSubgroup H :=
  of_injective (f := e.toMonoidHom) e.injective h

end HasNonabelianFiveSubgroup

theorem hasNonabelianFiveSubgroup_of_heis {G : Type*} [Group G] {a b c : G} (h : HeisRel a b c)
    (hc1 : c ≠ 1) : HasNonabelianFiveSubgroup G :=
  h.exists_pGroup hc1

theorem Data.false_of_hasNonabelianFiveSubgroup {K : Type} [Group K] [Finite K] {Q : Sylow 5 K}
    {x : K} {J₁ J₂ : Subgroup K} (hD : Data K Q x J₁ J₂) (h : HasNonabelianFiveSubgroup K) :
    False := by
  obtain ⟨P, hP, hnc⟩ := h
  exact hnc (isMulCommutative_of_isPGroup hD.abelian hP)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434
