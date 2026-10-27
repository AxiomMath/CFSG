module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallMain

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open CFSG.CGT.PushingUpLit.SolKNA.R4
open Equiv Equiv.Perm
open scoped MatrixGroups

theorem sixteen_le_card_of_q16Pair {α : Type} [Fintype α] [DecidableEq α] {x y : Perm α}
    (h : Q16Pair x y) : 16 ≤ Fintype.card α := by
  obtain ⟨h4, h8, hy2, hyx⟩ := h
  obtain ⟨p, hp⟩ : ∃ p, (x ^ 4) p ≠ p := by
    by_contra hcon
    push Not at hcon
    exact h4 (Equiv.ext hcon)
  have hmod : ∀ m : ℕ, x ^ m = x ^ (m % 8) := fun m => by
    conv_lhs => rw [← Nat.div_add_mod m 8, pow_add, pow_mul, h8, one_pow, one_mul]
  have hA : ∀ m : ℕ, 0 < m → m < 8 → (x ^ m) p = p → False := by
    intro m hm0 hm8 hfix
    have hk : ∃ k : ℕ, (m * k) % 8 = 4 := by
      have key : ∀ m : Fin 8, m.val ≠ 0 → ∃ k : Fin 8, (m.val * k.val) % 8 = 4 := by decide
      obtain ⟨k, hk⟩ := key ⟨m, hm8⟩ (by simpa using hm0.ne')
      exact ⟨k.val, hk⟩
    obtain ⟨k, hk⟩ := hk
    apply hp
    have h1 : x ^ 4 = (x ^ m) ^ k := by rw [← pow_mul, hmod (m * k), hk]
    rw [h1]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hfix k
  have hinj0 : Set.InjOn (fun i : ℕ => (x ^ i) p) (Finset.range 8 : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    simp only at hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · apply hA (j - i) (by omega) (by omega)
      have hx : x ^ j = x ^ i * x ^ (j - i) := by rw [← pow_add]; congr 1; omega
      rw [hx, Perm.mul_apply] at hij
      exact (x ^ i).injective hij.symm
    · apply hA (i - j) (by omega) (by omega)
      have hx : x ^ i = x ^ j * x ^ (i - j) := by rw [← pow_add]; congr 1; omega
      rw [hx, Perm.mul_apply] at hij
      exact (x ^ j).injective hij
  have hinv : ∀ (f : Perm α) (q : α), f (f⁻¹ q) = q := fun f q => f.apply_symm_apply q
  have hinv' : ∀ (f : Perm α) (q : α), f⁻¹ (f q) = q := fun f q => f.symm_apply_apply q
  have hyxi : ∀ i : ℕ, y * x ^ i = (x ^ i)⁻¹ * y := fun i => by
    have h1 : y * x ^ i * y⁻¹ = (x ^ i)⁻¹ := by
      have := map_pow (MulAut.conj y) x i
      simpa only [MulAut.conj_apply, hyx, inv_pow] using this
    rw [← h1]
    group
  have hC : ∀ i j : ℕ, y ((x ^ i) p) ≠ (x ^ j) p := by
    intro i j hij
    have e1 : y ((x ^ i) p) = (x ^ i)⁻¹ (y p) := by
      rw [← Perm.mul_apply, hyxi, Perm.mul_apply]
    rw [e1] at hij
    have e2 : y p = (x ^ (i + j)) p := by
      have := congrArg (fun q => (x ^ i) q) hij
      rw [hinv] at this
      rw [pow_add, Perm.mul_apply]
      exact this
    have e3 : y (y p) = p := by
      rw [e2]
      have : y ((x ^ (i + j)) p) = ((x ^ (i + j))⁻¹) (y p) := by
        rw [← Perm.mul_apply, hyxi, Perm.mul_apply]
      rw [this, e2, hinv']
    apply hp
    rw [← hy2, pow_two, Perm.mul_apply]
    exact e3
  set S₀ : Finset α := (Finset.range 8).image fun i => (x ^ i) p with hS₀
  set S₁ : Finset α := (Finset.range 8).image fun i => y ((x ^ i) p) with hS₁
  have hc₀ : S₀.card = 8 := by rw [hS₀, Finset.card_image_of_injOn hinj0]; simp
  have hc₁ : S₁.card = 8 := by
    rw [hS₁, Finset.card_image_of_injOn]
    · simp
    · intro i hi j hj hij
      exact hinj0 hi hj (y.injective hij)
  have hdisj : Disjoint S₀ S₁ := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 ha'
    exact hC j i hj
  have := Finset.card_union_of_disjoint hdisj
  have := Finset.card_le_univ (S₀ ∪ S₁)
  omega

theorem noQ16_perm {α : Type} [Fintype α] [DecidableEq α] (h : Fintype.card α < 16) :
    NoQ16 (Perm α) := fun _ _ hxy => absurd (sixteen_le_card_of_q16Pair hxy) (by omega)

theorem embedsAut_alternating {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    EmbedsAut (alternatingGroup (Fin n)) (Perm (Fin n)) := by
  intro Y _ N _ ⟨eK⟩ hC
  have hbij : Function.Bijective (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
      Perm (Fin n) →* MulAut (alternatingGroup (Fin n))) :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  let c : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) := MulEquiv.ofBijective _ hbij
  let g : Y →* MulAut ↥N := MulAut.conjNormal
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : y ∈ Subgroup.centralizer (N : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have := congrArg (fun α : MulAut ↥N => ((α ⟨m, hm⟩ : ↥N) : Y)) hy
      simp only [g, MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc m * y = (y * m * y⁻¹) * y := by rw [this]
        _ = y * m := by group
    rw [hC, Subgroup.mem_bot] at h1
    exact h1
  exact ⟨c.symm.toMonoidHom.comp ((MulAut.congr eK).toMonoidHom.comp g),
    c.symm.injective.comp ((MulAut.congr eK).injective.comp hg)⟩

@[expose] def ExAlt (F : Type) [Group F] : Prop :=
  ∃ n : ℕ, 7 ≤ n ∧ n ≤ 11 ∧ Nonempty (F ≃* alternatingGroup (Fin n))


theorem twinLeafR_exAlt {r n : ℕ} (hr : 4 ≤ r) : TwinLeafR r n ExAlt :=
  twinLeafR_of_noQ16 hr fun F _ ⟨m, hm7, hm11, ⟨e⟩⟩ =>
    ⟨Perm (Fin m), inferInstance, fun Y _ N _ ⟨eN⟩ hC =>
      embedsAut_alternating (by omega) (by omega) Y N ⟨eN.trans e⟩ hC,
      noQ16_perm (by simp; omega)⟩

theorem twinCyc4_of_forall_sq {F : Type} [Group F]
    (h : ∀ z : F, orderOf z = 2 → ∀ u : F, u * z = z * u → u * u = 1) : TwinCyc4 F := by
  intro z hz
  refine ⟨⊥, inferInstance, ?_⟩
  intro X _ hX u huX hu4
  exfalso
  have hu : u * z = z * u := Subgroup.mem_centralizer_singleton_iff.mp (hX.le huX)
  have h2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h z hz u hu)
  rw [hu4] at h2
  omega

theorem twinCyc4_psl2Even {F : Type} [Group F] {f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel F .PSL 2 2 f) :
    TwinCyc4 F ∧ Nobq.OutTwoCyclic F := by
  obtain ⟨-, K, hK, hfin, hcard, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hcp : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    rw [← Nat.card_eq_fintype_card]
    exact hcard)
  let e1 : F ≃* CFSG.GorensteinWalter.PSL2 K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  let e2 : F ≃* Matrix.SpecialLinearGroup (Fin 2) K := e1.trans (Nobq.psl2MulEquivSL2 K)
  refine ⟨twinCyc4_of_forall_sq fun z hz u huz => ?_,
    Nobq.OutTwoCyclic.of_mulEquiv e1 (Nobq.outTwoCyclic_psl2_of_charTwo K)⟩
  have hz2 : orderOf (e2 z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz
  have htt : e2 z * e2 z = 1 := by
    have := pow_orderOf_eq_one (e2 z)
    rwa [hz2, pow_two] at this
  have ht1 : e2 z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz2
    omega
  have hsC : e2 u * e2 z = e2 z * e2 u := by rw [← map_mul, ← map_mul, huz]
  have hss : e2 u * e2 u = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    refine Nobq.sq_eq_one_of_commute (T := (e2 z : Matrix (Fin 2) (Fin 2) K)) ?_ ?_
      (Matrix.SpecialLinearGroup.det_coe (e2 u)) ?_
    · rw [← Matrix.SpecialLinearGroup.coe_mul, htt, Matrix.SpecialLinearGroup.coe_one]
    · intro h1
      exact ht1 (Subtype.ext (by rw [h1, Matrix.SpecialLinearGroup.coe_one]))
    · rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hsC]
  exact e2.injective (by rw [map_mul, hss, map_one])

theorem false_of_psl2Even {r n : ℕ} (hr : 4 ≤ r) {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t) {f : ℕ}
    (hF : LieModel ↥(genFittingFStar Y) .PSL 2 2 f) : False := by
  haveI := h.core.simple
  rcases hF with ⟨-, hF⟩ | ⟨hF, -⟩ | ⟨hF, -⟩ | ⟨hF, -⟩
  · obtain ⟨hcyc, hout⟩ := twinCyc4_psl2Even hF
    exact false_of_twinCyc4 hr h (socleComm2_of_outTwoCyclic hout) hcyc
  all_goals exact absurd hF (by norm_num)

@[expose] def ExL2Even (F : Type) [Group F] : Prop :=
  LieModel F .PSL 2 2 3 ∨ LieModel F .PSL 2 2 4

theorem twinLeafR_exL2Even {r n : ℕ} (hr : 4 ≤ r) : TwinLeafR r n ExL2Even :=
  fun _ _ _ _ _ _ hP _ hF => hF.elim (false_of_psl2Even hr hP) (false_of_psl2Even hr hP)

@[expose] def ExcludedRest (F : Type) [Group F] : Prop :=
  CFSG.Assembly.LowTwoRank.StatedClassicalModel F .PSU 3 2 2 ∨ LieModel F .PSL 3 2 2 ∨
    LieModel F .twistedB2 0 2 3 ∨ NativeSporadic.IsSporadic F .M22 ∨
    NativeSporadic.IsSporadic F .M23 ∨ NativeSporadic.IsSporadic F .J1 ∨
    NativeSporadic.IsSporadic F .J2 ∨ NativeSporadic.IsSporadic F .J3 ∨
    NativeSporadic.IsSporadic F .McL ∨ NativeSporadic.IsSporadic F .Ly

theorem excludedSmall_split {F : Type} [Group F] (h : Nobq.ExcludedSmall F) :
    ExAlt F ∨ ExL2Even F ∨ ExcludedRest F := by
  rcases h with ⟨⟨e⟩⟩ | h | h | h | h | h | ⟨n, hn8, hn11, he⟩ | h | h | h | h | h | h | h
  · exact Or.inl ⟨7, le_rfl, by norm_num, ⟨e⟩⟩
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl ⟨n, by omega, hn11, he⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr h))))))))))

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
