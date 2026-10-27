module

public import CFSG.ClassicalInvolution.Q3.TL4MF164Dat

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint

section Abelian

theorem mem_of_pow_three_of_index_le_two {X : Type} [Group X] [Finite X] {N : Subgroup X}
    (hN : N.index ≤ 2) {x : X} {k : ℕ} (hx : x ^ 3 ^ k = 1) : x ∈ N := by
  obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have hx' : x ^ (2 * m + 1) = 1 := hm ▸ hx
  have hxe : x = (x ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, hx', one_mul]
  rw [hxe]
  exact N.pow_mem (MF164.sq_mem_of_index_le_two hN x) _

theorem psl2_sylow_three_comm {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ f) (h7 : 7 ≤ Nat.card K) (Q : Sylow 3 (GorensteinWalter.PSL2 K))
    {x y : GorensteinWalter.PSL2 K} (hx : x ∈ Q) (hy : y ∈ Q) : x * y = y * x := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨e⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hK Q
    have h := congrArg (fun a => ((e a : Q) : GorensteinWalter.PSL2 K))
      (mul_comm (e.symm ⟨x, hx⟩) (e.symm ⟨y, hy⟩))
    simpa using h
  · have hcop : Nat.Coprime 3 (Nat.card K) := by
      rw [hK]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
    have hcyc : IsCyclic ↥(Q : Subgroup (GorensteinWalter.PSL2 K)) :=
      GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card K hK h7 3 (by norm_num) hcop Q
    let _ : CommGroup ↥(Q : Subgroup (GorensteinWalter.PSL2 K)) := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥(Q : Subgroup _)) ⟨y, hy⟩)

theorem abelian3_of_l2 {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hi : (genFittingFStar X).index ≤ 2) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : Even f)
    (hL : LieModel (FStarQuot X) .PSL 2 p f) (P : Subgroup X) (hP : IsPGroup 3 ↥P) :
    ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := MF164.exists_fstar_equiv_psl2 hs hL
  have hF : ∀ x ∈ P, x ∈ genFittingFStar X := by
    intro x hx
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    exact mem_of_pow_three_of_index_le_two hi (k := k) (by simpa using congrArg Subtype.val hk)
  have hf1 : f ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK, pow_zero] at h1
    exact lt_irrefl 1 h1
  have h7 : 7 ≤ Nat.card K := by
    obtain ⟨g, hg⟩ := hf
    have hg1 : 1 ≤ g := by omega
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    rw [hK, hg, ← two_mul, pow_mul]
    calc 7 ≤ 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ (p ^ 2) ^ g := Nat.le_self_pow (by omega) _
  have hP3 : IsPGroup 3 ↥((P.subgroupOf (genFittingFStar X)).map e.toMonoidHom) := by
    refine IsPGroup.map (fun g => ?_) e.toMonoidHom
    obtain ⟨k, hk⟩ := hP ⟨((g : ↥(genFittingFStar X)) : X), Subgroup.mem_subgroupOf.mp g.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  obtain ⟨Q, hQ⟩ := hP3.exists_le_sylow
  intro x hx y hy
  have hx' : e ⟨x, hF x hx⟩ ∈ Q := hQ ⟨⟨x, hF x hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hy' : e ⟨y, hF y hy⟩ ∈ Q := hQ ⟨⟨y, hF y hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have h := psl2_sylow_three_comm hp hK h7 Q hx' hy'
  rw [← map_mul, ← map_mul] at h
  exact congrArg Subtype.val (e.injective h)

theorem abelian3_of_m11 {X : Type} [Group X] [Finite X]
    (h : NativeSporadic.IsSporadic X .M11) (P : Subgroup X) (hP : IsPGroup 3 ↥P) :
    ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  obtain ⟨e⟩ := h
  have hX : Nat.card X = 7920 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M11
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : 3 ^ k ∣ 7920 := hk ▸ hX ▸ Subgroup.card_subgroup_dvd_card P
  have hk2 : k ≤ 2 := by
    by_contra hlt
    have : 3 ^ 3 ∣ 7920 := (Nat.pow_dvd_pow 3 (by omega)).trans hdvd
    norm_num at this
  have hc : ∀ a b : ↥P, a * b = b * a := by
    interval_cases k
    · have : Subsingleton ↥P := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
      exact fun a b => Subsingleton.elim _ _
    · have : IsCyclic ↥P := isCyclic_of_prime_card (p := 3) (by simpa using hk)
      let _ : CommGroup ↥P := IsCyclic.commGroup
      exact mul_comm
    · exact fun a b => (IsPGroup.isMulCommutative_of_card_eq_prime_sq hk).is_comm.comm a b
  intro x hx y hy
  exact congrArg Subtype.val (hc ⟨x, hx⟩ ⟨y, hy⟩)

theorem abelian3_of_m11_or_l2 {X : Type} [Group X] [Finite X]
    (h : NativeSporadic.IsSporadic X .M11 ∨ (IsSimpleGroup ↥(genFittingFStar X) ∧
      (genFittingFStar X).index ≤ 2 ∧ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧
        LieModel (FStarQuot X) .PSL 2 p f)) :
    ∀ P : Subgroup X, IsPGroup 3 ↥P → ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  rcases h with h | ⟨hs, hi, p, f, hp, hp2, hf, hL⟩
  · exact abelian3_of_m11 h
  · exact abelian3_of_l2 hs hi hp hp2 hf hL

end Abelian

section PSL33

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

def IsUnitri3 {K : Type} [Field K] (M : Matrix (Fin 3) (Fin 3) K) : Prop :=
  M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 0 0 = 1 ∧ M 1 1 = 1 ∧ M 2 2 = 1

def unitri3 (K : Type) [Field K] : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {g | IsUnitri3 (g : Matrix (Fin 3) (Fin 3) K)}
  mul_mem' := by
    rintro a b ⟨a10, a20, a21, a00, a11, a22⟩ ⟨b10, b20, b21, b00, b11, b22⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, a00, a11, a22, b10, b20, b21,
        b00, b11, b22]
  one_mem' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  inv_mem' := by
    rintro a ⟨a10, a20, a21, a00, a11, a22⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Matrix.adjugate_fin_three, a10, a20, a21, a00, a11, a22]

theorem pow_three_eq_one_of_mem_unitri3 {K : Type} [Field K] (h3 : (3 : K) = 0)
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ unitri3 K) : g ^ 3 = 1 := by
  obtain ⟨g10, g20, g21, g00, g11, g22⟩ := hg
  apply Subtype.ext
  show (g : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, g10, g20, g21, g00, g11, g22] <;>
    ring_nf <;> simp [h3]

theorem exists_nonabelian_three_of_lieModel_psl33 {H : Type} [Group H]
    (h : LieModel H .PSL 3 3 1) :
    ∃ P : Subgroup H, IsPGroup 3 ↥P ∧ ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime_pow (p := 3) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  let x : SpecialLinearGroup (Fin 3) K :=
    ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩
  let y : SpecialLinearGroup (Fin 3) K :=
    ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩
  have hx : x ∈ unitri3 K := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [x]
  have hy : y ∈ unitri3 K := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [y]
  have hU : IsPGroup 3 ↥(unitri3 K) := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one]; exact pow_three_eq_one_of_mem_unitri3 h3 g.2)⟩
  refine ⟨((unitri3 K).map (proj 3 K)).map e.symm.toMonoidHom, (hU.map _).map _,
    e.symm (proj 3 K x), ⟨proj 3 K x, ⟨x, hx, rfl⟩, rfl⟩,
    e.symm (proj 3 K y), ⟨proj 3 K y, ⟨y, hy, rfl⟩, rfl⟩, ?_⟩
  intro hxy
  simp only [← map_mul] at hxy
  have hxy' := e.symm.injective hxy
  have hmem : (x * y)⁻¹ * (y * x) ∈ scalars 3 K := QuotientGroup.eq.mp hxy'
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hmem
  have key : (!![1, 0, 0; 0, 1, 1; 0, 0, 1] * !![1, 1, 0; 0, 1, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) K) =
      (!![1, 1, 0; 0, 1, 0; 0, 0, 1] * !![1, 0, 0; 0, 1, 1; 0, 0, 1]) * scalar (Fin 3) (c : K) := by
    have hs : y * x = (x * y) * ((x * y)⁻¹ * (y * x)) := (mul_inv_cancel_left _ _).symm
    have h1 := congrArg (fun A : SpecialLinearGroup (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) hs
    rw [← hc]
    exact h1
  have h00 := congrFun (congrFun key 0) 0
  have h02 := congrFun (congrFun key 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h00 h02
  rw [← h00] at h02
  exact one_ne_zero h02.symm

end PSL33

end CFSG.ClassicalInvolution.Q3.TL4
