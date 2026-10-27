module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSource

public noncomputable section

namespace CFSG.ComponentClassification.SymmetricLocal

open Matrix CFSG.Assembly.LowTwoRank

variable (r : ℕ) (k : Type) [Field k]

@[expose] def symmetricMatrices : AddSubgroup (Matrix (Fin r) (Fin r) k) where
  carrier := {C | Cᵀ = C}
  zero_mem' := transpose_zero
  add_mem' := by
    intro a b ha hb
    change (a + b)ᵀ = a + b
    rw [transpose_add, show aᵀ = a from ha, show bᵀ = b from hb]
  neg_mem' := by
    intro a ha
    change (-a)ᵀ = -a
    rw [transpose_neg, show aᵀ = a from ha]

@[expose] def symUnipotentHom : Multiplicative (symmetricMatrices r k) →* StatedSp r k where
  toFun C := LocalAnalysis.ComponentInitial.SymplecticFlag.upperUnipotentSp r k
    (show ((Multiplicative.toAdd C : symmetricMatrices r k) : Matrix (Fin r) (Fin r) k)ᵀ =
      (Multiplicative.toAdd C : symmetricMatrices r k) from (Multiplicative.toAdd C).2)
  map_one' := by
    refine Subtype.ext (Units.ext ?_)
    rw [LocalAnalysis.ComponentInitial.SymplecticFlag.coe_upperUnipotentSp]
    simp [fromBlocks_one]
  map_mul' := by
    intro C D
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_mul, Units.val_mul,
      LocalAnalysis.ComponentInitial.SymplecticFlag.coe_upperUnipotentSp,
      LocalAnalysis.ComponentInitial.SymplecticFlag.coe_upperUnipotentSp,
      LocalAnalysis.ComponentInitial.SymplecticFlag.coe_upperUnipotentSp, fromBlocks_multiply]
    simp only [toAdd_mul, AddSubgroup.coe_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add]
    rw [add_comm]

variable {r k}

theorem coe_symUnipotentHom (C : Multiplicative (symmetricMatrices r k)) :
    (((symUnipotentHom r k C : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
        fromBlocks 1 ((Multiplicative.toAdd C : symmetricMatrices r k) :
          Matrix (Fin r) (Fin r) k) 0 1 :=
  LocalAnalysis.ComponentInitial.SymplecticFlag.coe_upperUnipotentSp _

theorem symUnipotentHom_injective : Function.Injective (symUnipotentHom r k) := by
  intro C D h
  have h' := congrArg (fun g : StatedSp r k =>
    ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)) h
  simp only [coe_symUnipotentHom] at h'
  have hC := (Matrix.fromBlocks_inj.mp h').2.1
  exact Multiplicative.toAdd.injective (Subtype.ext hC)

theorem isElementaryAbelian_range_symUnipotentHom [CharP k 2] :
    CFSG.IsElementaryAbelian 2 (symUnipotentHom r k).range := by
  refine { toIsMulCommutative := isMulCommutative_iff.mpr ?_, exponent_dvd_p := ?_ }
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    change symUnipotentHom r k a * symUnipotentHom r k b =
      symUnipotentHom r k b * symUnipotentHom r k a
    rw [← map_mul, ← map_mul, mul_comm a b]
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    obtain ⟨_, a, rfl⟩ := x
    apply Subtype.ext
    change symUnipotentHom r k a ^ 2 = 1
    have ha : a * a = 1 := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      ext i j
      simp only [toAdd_mul, AddSubgroup.coe_add, Matrix.add_apply, toAdd_one,
        ZeroMemClass.coe_zero, Matrix.zero_apply]
      exact CharTwo.add_self_eq_zero _
    rw [← map_pow, pow_two, ha, map_one]

theorem smul_one_mem_symmetricMatrices (t : k) :
    t • (1 : Matrix (Fin r) (Fin r) k) ∈ symmetricMatrices r k := by
  change (t • (1 : Matrix (Fin r) (Fin r) k))ᵀ = t • 1
  rw [transpose_smul, transpose_one]

theorem card_le_card_symmetricMatrices [Finite k] (hr : 1 ≤ r) :
    Nat.card k ≤ Nat.card (symmetricMatrices r k) := by
  have : Finite (symmetricMatrices r k) := inferInstance
  refine Nat.card_le_card_of_injective (fun t => ⟨t • 1, smul_one_mem_symmetricMatrices t⟩) ?_
  intro s t h
  have h' := congrArg (fun C : symmetricMatrices r k =>
    (C : Matrix (Fin r) (Fin r) k) ⟨0, hr⟩ ⟨0, hr⟩) h
  simpa using h'

@[expose] def threeSym (hr : 2 ≤ r) (v : k × k × k) : Matrix (Fin r) (Fin r) k :=
  single ⟨0, by omega⟩ ⟨0, by omega⟩ v.1 + single ⟨1, hr⟩ ⟨1, hr⟩ v.2.1 +
    single ⟨0, by omega⟩ ⟨1, hr⟩ v.2.2 + single ⟨1, hr⟩ ⟨0, by omega⟩ v.2.2

theorem threeSym_mem (hr : 2 ≤ r) (v : k × k × k) : threeSym hr v ∈ symmetricMatrices r k := by
  change (threeSym hr v)ᵀ = threeSym hr v
  simp only [threeSym, transpose_add, transpose_single]
  abel

theorem card_cube_le_card_symmetricMatrices [Finite k] (hr : 2 ≤ r) :
    Nat.card k ^ 3 ≤ Nat.card (symmetricMatrices r k) := by
  have h3 : Nat.card (k × k × k) = Nat.card k ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod]
    ring
  rw [← h3]
  refine Nat.card_le_card_of_injective (fun v => ⟨threeSym hr v, threeSym_mem hr v⟩) ?_
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h' := congrArg (fun C : symmetricMatrices r k => (C : Matrix (Fin r) (Fin r) k)) h
  simp only at h'
  have hne : (⟨0, by omega⟩ : Fin r) ≠ ⟨1, hr⟩ := by simp [Fin.ext_iff]
  have h00 := congrFun (congrFun h' ⟨0, by omega⟩) ⟨0, by omega⟩
  have h11 := congrFun (congrFun h' ⟨1, hr⟩) ⟨1, hr⟩
  have h01 := congrFun (congrFun h' ⟨0, by omega⟩) ⟨1, hr⟩
  simp only [threeSym, Matrix.add_apply, Matrix.single_apply, hne, hne.symm, and_self,
    and_true, and_false, ite_true, ite_false, add_zero, zero_add] at h00 h11 h01
  rw [h00, h11, h01]

theorem eq_of_two_pow_mul_odd {a b m m' : ℕ} (hm : Odd m) (hm' : Odd m')
    (h : 2 ^ a * m = 2 ^ b * m') : a = b := by
  have h1 : a ≤ b := UnbalancingLocal.two_pow_dvd_of_dvd_mul_odd hm' (h ▸ dvd_mul_right _ _)
  have h2 : b ≤ a := UnbalancingLocal.two_pow_dvd_of_dvd_mul_odd hm (h.symm ▸ dvd_mul_right _ _)
  omega

theorem card_statedSp_eq_two_pow_mul_odd [Finite k] {g : ℕ} (hk : Nat.card k = 2 ^ g)
    (hg : 1 ≤ g) (hr : 1 ≤ r) :
    ∃ m, Odd m ∧ Nat.card (StatedSp r k) = 2 ^ (g * r ^ 2) * m := by
  have := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := g)
    (by rw [← Nat.card_eq_fintype_card, hk])
  have hcard := (LocalAnalysis.ComponentInitial.SymplecticFlag.symplectic_higher_order_and_Sylow
    (K := k) 2 (2 ^ g) hk hr).1
  refine ⟨∏ j ∈ Finset.Icc 1 r, ((2 ^ g) ^ (2 * j) - 1), ?_, ?_⟩
  · refine Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have heven : Even ((2 ^ g) ^ (2 * j)) := by
      rw [← pow_mul]
      exact (Nat.even_pow' (by positivity)).mpr even_two
    have hpos : 1 ≤ (2 ^ g) ^ (2 * j) := Nat.one_le_pow _ _ (by positivity)
    exact Nat.Even.sub_odd hpos heven odd_one
  · rw [hcard, ← pow_mul]

variable (r k) in
theorem statedScalars_subgroupOf_statedSp_eq_bot [CharP k 2] (hr : 1 ≤ r) :
    (StatedScalars (Fin r ⊕ Fin r) k).subgroupOf (StatedSp r k) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hx
  have hsp := LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp x.2
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar,
    CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup,
    CFSG.ClassicalGroups.Symplectic.scalar_mem_symplecticGroup_iff hr] at hsp
  have hc1 : (c : k) = 1 := by
    have h0 : ((c : k) + 1) ^ 2 = 0 := by
      rw [add_sq, hsp, one_pow, mul_one, two_mul, CharTwo.add_self_eq_zero, add_zero,
        CharTwo.add_self_eq_zero]
    have h1 : (c : k) + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h0
    rwa [CharTwo.add_eq_zero] at h1
  apply Subtype.ext
  rw [OneMemClass.coe_one, ← hc]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one, hc1, Matrix.scalar_apply,
    Matrix.diagonal_one]

theorem small_standard_source_even_simple_symplectic_parameters_stated {X : Type} [Group X]
    {k : Type} [Field k] [Finite k] {g r : ℕ} (hk : Nat.card k = 2 ^ g) (hr : 1 ≤ r)
    (hX : Nonempty (X ≃* StatedSp r k)) :
    (∀ p f : ℕ, p ≠ 2 → StatedClassicalModel X .PSL 2 p f → r = 1 ∧ g = 2 ∧ p = 5 ∧ f = 1) ∧
      IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧ ¬ StatedClassicalModel X .PSL 3 2 2 ∧
      (StatedScalars (Fin r ⊕ Fin r) k).subgroupOf (StatedSp r k) = ⊥ ∧
      Nonempty (StatedProj (StatedSp r k) ≃* StatedSp r k) := by
  obtain ⟨e⟩ := hX
  have := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := g)
    (by rw [← Nat.card_eq_fintype_card, hk])
  have hk2 : 2 ≤ Nat.card k := Finite.one_lt_card
  have hg : 1 ≤ g := by
    by_contra h
    have h0 : g = 0 := by omega
    rw [h0, pow_zero] at hk
    omega
  obtain ⟨m, hmodd, hcardSp⟩ := card_statedSp_eq_two_pow_mul_odd hk hg hr
  have hXcard : Nat.card X = 2 ^ (g * r ^ 2) * m := (Nat.card_congr e.toEquiv).trans hcardSp
  have hS1 : r = 1 → Nat.card X = 2 ^ g * ((2 ^ g) ^ 2 - 1) := by
    intro hr1
    subst hr1
    rw [Nat.card_congr e.toEquiv,
      (LocalAnalysis.ComponentInitial.SymplecticFlag.symplectic_higher_order_and_Sylow
        (K := k) 2 (2 ^ g) hk le_rfl).1]
    simp
  have : CFSG.IsElementaryAbelian 2 (symUnipotentHom r k).range :=
    isElementaryAbelian_range_symUnipotentHom
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : CFSG.IsElementaryAbelian 2 ((symUnipotentHom r k).range.map e.symm.toMonoidHom) :=
    CFSG.IsElementaryAbelian.map _
  have hEcard : Nat.card ((symUnipotentHom r k).range.map e.symm.toMonoidHom) =
      Nat.card (symmetricMatrices r k) := by
    rw [Subgroup.card_map_of_injective e.symm.injective, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective symUnipotentHom_injective, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd]
  have hbot := statedScalars_subgroupOf_statedSp_eq_bot r k hr
  refine ⟨fun p f hp2 hmodel => ?_, ⟨fun e7 => ?_⟩, fun h322 => ?_, hbot,
    ⟨(QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot⟩⟩
  · obtain ⟨⟨hp, hf, -⟩, K', _, _, hK', ⟨ψ⟩⟩ := hmodel
    have hq : Odd (Nat.card K') := by
      rw [hK']
      exact (hp.odd_of_ne_two hp2).pow
    have h4 := UnbalancingLocal.card_le_four_of_odd_psl_two hq ψ
      ((symUnipotentHom r k).range.map e.symm.toMonoidHom)
    rw [hEcard] at h4
    have hr1 : r = 1 := by
      by_contra hr1
      have h8 := card_cube_le_card_symmetricMatrices (k := k) (show 2 ≤ r by omega)
      have h8' : 2 ^ 3 ≤ Nat.card k ^ 3 := Nat.pow_le_pow_left hk2 3
      omega
    subst hr1
    have hqk := card_le_card_symmetricMatrices (k := k) (r := 1) le_rfl
    rw [hk] at hqk
    have hg2 : g ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by omega)
    have hXq : Nat.card X * 2 = Nat.card K' * (Nat.card K' ^ 2 - 1) := by
      rw [Nat.card_congr ψ.toEquiv]
      exact UnbalancingLocal.two_mul_card_psl_two_of_odd K' hq
    rw [hS1 rfl] at hXq
    interval_cases g
    · exfalso
      norm_num at hXq
      exact UnbalancingLocal.cubeSub_ne_of_between (a := 2) (N := 12) (by norm_num) (by norm_num)
        (by norm_num) _ hXq.symm
    · norm_num at hXq
      have h5 := UnbalancingLocal.eq_of_cubeSub_eq (b := 5) Nat.card_pos (by norm_num)
        (by rw [← hXq]; norm_num)
      rw [hK'] at h5
      obtain ⟨hp5, hf1⟩ := UnbalancingLocal.prime_pow_inj hp Nat.prime_five hf le_rfl
        (h5.trans (pow_one 5).symm)
      exact ⟨rfl, rfl, hp5, hf1⟩
  · have h7 : Nat.card X = 2520 :=
      (Nat.card_congr e7.toEquiv).trans UnbalancingLocal.card_alternating_seven
    have h3 : g * r ^ 2 = 3 := eq_of_two_pow_mul_odd hmodd (by decide : Odd 315)
      (by rw [← hXcard, h7]; norm_num)
    have hr1 : r = 1 := by
      by_contra hr1
      have hr2 : 2 ≤ r := by omega
      have h4 : 4 ≤ r ^ 2 := by nlinarith
      have h4' : 1 * 4 ≤ g * r ^ 2 := Nat.mul_le_mul hg h4
      omega
    subst hr1
    have hg3 : g = 3 := by simpa using h3
    subst hg3
    have h504 := hS1 rfl
    rw [h7] at h504
    norm_num at h504
  · obtain ⟨-, K₃, _, _, hK₃, ⟨χ⟩⟩ := h322
    have h20160 : Nat.card X = 20160 := (Nat.card_congr χ.toEquiv).trans
      (UnbalancingLocal.card_psl_three_four K₃ (by rw [hK₃]; norm_num))
    have h6 : g * r ^ 2 = 6 := eq_of_two_pow_mul_odd hmodd (by decide : Odd 315)
      (by rw [← hXcard, h20160]; norm_num)
    have hr1 : r = 1 := by
      rcases (show r = 1 ∨ r = 2 ∨ 3 ≤ r by omega) with h | h | h
      · exact h
      · subst h
        omega
      · have h9 : 9 ≤ r ^ 2 := by nlinarith
        have h9' : 1 * 9 ≤ g * r ^ 2 := Nat.mul_le_mul hg h9
        omega
    subst hr1
    have hg6 : g = 6 := by simpa using h6
    subst hg6
    have h262080 := hS1 rfl
    rw [h20160] at h262080
    norm_num at h262080

theorem small_standard_source_even_simple_symplectic_parameters {X : Type} [Group X]
    {k : Type} [Field k] [Finite k] {g r : ℕ} (hk : Nat.card k = 2 ^ g) (hr : 1 ≤ r)
    (hX : Nonempty (X ≃* StatedSp r k)) :
    (∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → Assembly.ComponentType.ClassicalModel X .PSL 2 p f →
      r = 1 ∧ g = 2 ∧ p = 5 ∧ f = 1) ∧
      IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧
      ¬ Assembly.ComponentType.ClassicalModel X .PSL 3 2 2 ∧
      (StatedScalars (Fin r ⊕ Fin r) k).subgroupOf (StatedSp r k) = ⊥ ∧
      Nonempty (StatedProj (StatedSp r k) ≃* StatedSp r k) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    small_standard_source_even_simple_symplectic_parameters_stated hk hr hX
  exact ⟨fun p f _ hp2 hY => h1 p f hp2
      (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSL 2 p f hY), h2,
    fun hZ => h3 (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSL 3 2 2 hZ),
    h4, h5⟩

end CFSG.ComponentClassification.SymmetricLocal
