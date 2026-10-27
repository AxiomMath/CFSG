module

public import CFSG.Quasithin.Background.HA7DataInputs
public import CFSG.Quasithin.Background.HSp4A
public import CFSG.Quasithin.Background.FixVZPowersMem
import CFSG.Certificates.Kernel.Misc.RankOneSq

public section

namespace CFSG.KC.Misc.A7GL42

section Perm

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.A7 Equiv Equiv.Perm
open scoped Matrix

theorem cycleType_of_inv (σ : alternatingGroup (Fin 7)) (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    (σ : Perm (Fin 7)).cycleType = Multiset.replicate 2 2 := by
  have h2' : (σ : Perm (Fin 7)) ^ 2 = 1 := by
    rw [sq, ← Subgroup.coe_mul, h2, Subgroup.coe_one]
  have h1' : (σ : Perm (Fin 7)) ≠ 1 := fun h => h1 (Subtype.ext h)
  have hord : orderOf (σ : Perm (Fin 7)) = 2 := orderOf_eq_prime h2' h1'
  obtain ⟨n, hn⟩ := cycleType_prime_order (hord ▸ Nat.prime_two)
  rw [hord] at hn
  have hsign : sign (σ : Perm (Fin 7)) = 1 := σ.2
  rw [sign_of_cycleType, hn, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul,
    neg_one_pow_eq_one_iff_even (by decide)] at hsign
  have hsum : (σ : Perm (Fin 7)).cycleType.sum ≤ 7 := by
    rw [sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [hn]
  have hn2 : n ≤ 2 := by omega
  interval_cases n
  · exact absurd hsign (by decide)
  · rfl
  · exact absurd hsign (by decide)

theorem exists_conj_inv7 : ∀ σ : alternatingGroup (Fin 7), σ * σ = 1 → σ ≠ 1 →
    ∃ g : alternatingGroup (Fin 7), g * σ * g⁻¹ = inv7 := by
  intro σ h2 h1
  have hc : IsConj (σ : Perm (Fin 7)) (inv7 : Perm (Fin 7)) := by
    rw [isConj_iff_cycleType_eq, cycleType_of_inv σ h2 h1,
      cycleType_of_inv inv7 (by decide) (by decide)]
  have hsupp : (σ : Perm (Fin 7)).support.card + 2 ≤ Fintype.card (Fin 7) := by
    rw [← sum_cycleType, cycleType_of_inv σ h2 h1, Multiset.sum_replicate, smul_eq_mul,
      Fintype.card_fin]
    norm_num
  exact isConj_iff.mp (alternatingGroup.isConj_of hc hsupp)

theorem cycleType_inv8 : (inv8 : Perm (Fin 8)).cycleType = {2, 2} := by
  change (swap (0 : Fin 8) 1 * swap 2 3).cycleType = {2, 2}
  have hd : Disjoint (swap (0 : Fin 8) 1) (swap 2 3) := fun x => by fin_cases x <;> decide
  rw [hd.cycleType_mul, (isCycle_swap (by decide)).cycleType,
    (isCycle_swap (by decide)).cycleType, card_support_swap (by decide),
    card_support_swap (by decide)]
  rfl

theorem card_centralizer_perm :
    Nat.card (Subgroup.centralizer {(inv8 : Perm (Fin 8))}) = 192 := by
  rw [nat_card_centralizer, cycleType_inv8]
  rfl

theorem card_centralizer_inv8 :
    (Finset.univ.filter fun π : alternatingGroup (Fin 8) => π * inv8 = inv8 * π).card = 96 := by
  classical
  let C := Subgroup.centralizer {(inv8 : Perm (Fin 8))}
  let f : C →* ℤˣ := sign.comp C.subtype
  have hsw : swap (4 : Fin 8) 5 ∈ C := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    change swap (4 : Fin 8) 5 * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * swap 4 5
    decide
  have hsurj : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨⟨_, hsw⟩, sign_swap (by decide : (4 : Fin 8) ≠ 5)⟩
  have hker : Nat.card f.ker * 2 = 192 := by
    rw [← card_centralizer_perm, ← f.ker.card_mul_index, Subgroup.index_ker,
      MonoidHom.range_eq_top_of_surjective f hsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int]
  have e : {π : alternatingGroup (Fin 8) // π * inv8 = inv8 * π} ≃ f.ker :=
    { toFun := fun π => ⟨⟨π.1.1,
          Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val π.2)⟩,
          MonoidHom.mem_ker.mpr π.1.2⟩
      invFun := fun x => ⟨⟨x.1.1, MonoidHom.mem_ker.mp x.2⟩,
          Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.1.2)⟩
      left_inv := fun π => rfl
      right_inv := fun x => rfl }
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_congr e]
  omega

theorem fixV_five {V : Type*} [CommGroup V] [Finite V] (x : MulAut V) (hx5 : x ^ 5 = 1)
    (h16 : Nat.card V = 16) :
    fixV (Subgroup.zpowers x) = ⊥ ∨ fixV (Subgroup.zpowers x) = ⊤ := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : IsPGroup 5 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := if x = 1 then 0 else 1) ?_
    rw [Nat.card_zpowers]
    split_ifs with h
    · rw [h, orderOf_one, pow_zero]
    · rw [pow_one]
      exact orderOf_eq_prime hx5 h
  have hmod := Sp4.card_modEq_card_inf_fixV hP (W := ⊤) fun _ _ _ _ => Subgroup.mem_top _
  rw [top_inf_eq, Subgroup.card_top, h16] at hmod
  have hdvd := Subgroup.card_subgroup_dvd_card (fixV (Subgroup.zpowers x))
  rw [h16, (by norm_num : (16 : ℕ) = 2 ^ 4)] at hdvd
  obtain ⟨k, hk, hFk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hFk] at hmod
  interval_cases k
  · exact Or.inl (Subgroup.card_eq_one.mp hFk)
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  · exact Or.inr ((Subgroup.card_eq_iff_eq_top _).mp (by rw [hFk, h16]; norm_num))

theorem fix_eq_zero_of_pow_five :
    ∀ M : Matrix (Fin 4) (Fin 4) (ZMod 2), M ^ 5 = 1 → M ≠ 1 →
      ∀ v : Fin 4 → ZMod 2, M *ᵥ v = v → v = 0 := by
  classical
  intro M h5 h1 v hv
  let g : GL (Fin 4) (ZMod 2) := ⟨M, M ^ 4, by rw [← pow_succ', h5], by rw [← pow_succ, h5]⟩
  have hg5 : g ^ 5 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h5)
  have hx5 : matAut g ^ 5 = 1 := by
    rw [← matHom_apply, ← map_pow, hg5, map_one]
  have h16 : Nat.card (StdMod (Fin 4) (ZMod 2)) = 16 := by
    rw [card_stdMod]
    simp
  rcases fixV_five (matAut g) hx5 h16 with hbot | htop
  · have hfx : matAut g (Multiplicative.ofAdd v) = Multiplicative.ofAdd v := by
      change Multiplicative.ofAdd (M *ᵥ v) = _
      rw [hv]
    have hmem := mem_fixV_zpowers_iff_apply.mpr hfx
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Multiplicative.ofAdd.injective (hmem.trans ofAdd_zero.symm)
  · exfalso
    apply h1
    refine Matrix.ext_iff_mulVec.mpr fun w => ?_
    rw [Matrix.one_mulVec]
    have hw : Multiplicative.ofAdd w ∈ fixV (Subgroup.zpowers (matAut g)) :=
      htop ▸ Subgroup.mem_top _
    exact congrArg Multiplicative.toAdd (mem_fixV_zpowers_iff_apply.mp hw)

end Perm

section Transvection

open Matrix
open scoped Matrix

abbrev V4 := Fin 4 → ZMod 2

@[expose] def fT (p : V4 × V4) : Matrix (Fin 4) (Fin 4) (ZMod 2) := 1 + vecMulVec p.1 p.2

@[expose] def QT (p : V4 × V4) : Prop :=
  fT p * fT p = 1 ∧ (Finset.univ.filter fun v : V4 => fT p *ᵥ v = v).card = 8

instance : DecidablePred QT := fun p => by unfold QT; infer_instance

theorem c7022_card_ker_dot : ∀ φ : V4, φ ≠ 0 →
    (Finset.univ.filter fun v : V4 => φ ⬝ᵥ v = 0).card = 8 := by
  decide +kernel

theorem c7022_zmod2_eq_one : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

theorem c7022_zmod2_mul_eq_one : ∀ x y : ZMod 2, x * y = 1 → x = 1 ∧ y = 1 := by decide

theorem c7022_zmod2_add_self : ∀ x : ZMod 2, x + x = 0 := by decide

theorem exists_vecMulVec {K : Type*} [Field K] (N : Matrix (Fin 4) (Fin 4) K) (h : N.rank ≤ 1) :
    ∃ a φ : Fin 4 → K, N = vecMulVec a φ := by
  change Module.finrank K (LinearMap.range N.mulVecLin) ≤ 1 at h
  obtain ⟨u, hu⟩ := (finrank_le_one_iff (K := K) (V := LinearMap.range N.mulVecLin)).1 h
  choose c hc using fun j : Fin 4 =>
    hu ⟨N.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩
  refine ⟨u, c, ?_⟩
  ext i j
  have h1 := congrFun (congrArg (fun w : LinearMap.range N.mulVecLin => (w : Fin 4 → K)) (hc j)) i
  simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
  rw [vecMulVec_apply, mul_comm, h1]
  rfl

theorem vecMulVec_inj {a φ b ψ : V4} (ha : a ≠ 0) (hφ : φ ≠ 0)
    (h : vecMulVec a φ = vecMulVec b ψ) : a = b ∧ φ = ψ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hφ
  have hi1 := c7022_zmod2_eq_one _ hi
  have hj1 := c7022_zmod2_eq_one _ hj
  have hij := congrFun (congrFun h i) j
  rw [vecMulVec_apply, vecMulVec_apply, hi1, hj1, one_mul] at hij
  obtain ⟨hbi, hψj⟩ := c7022_zmod2_mul_eq_one _ _ hij.symm
  refine ⟨funext fun k => ?_, funext fun k => ?_⟩
  · have := congrFun (congrFun h k) j
    rwa [vecMulVec_apply, vecMulVec_apply, hj1, hψj, mul_one, mul_one] at this
  · have := congrFun (congrFun h i) k
    rwa [vecMulVec_apply, vecMulVec_apply, hi1, hbi, one_mul, one_mul] at this

theorem QT_ne {p : V4 × V4} (hp : QT p) : p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  obtain ⟨-, h8⟩ := hp
  have h1 : (p.1 = 0 ∨ p.2 = 0) → fT p = 1 := by
    rintro (h | h) <;> ext i j <;> simp [fT, vecMulVec_apply, h]
  by_contra hc
  rw [not_and_or, not_not, not_not] at hc
  rw [h1 hc] at h8
  rw [Finset.filter_true_of_mem fun v _ => Matrix.one_mulVec v, Finset.card_univ,
    Fintype.card_fun, ZMod.card, Fintype.card_fin] at h8
  norm_num at h8

theorem fT_mulVec (p : V4 × V4) (v : V4) : fT p *ᵥ v = v + (p.2 ⬝ᵥ v) • p.1 := by
  rw [fT, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem fT_fix_iff {p : V4 × V4} (ha : p.1 ≠ 0) (v : V4) : fT p *ᵥ v = v ↔ p.2 ⬝ᵥ v = 0 := by
  rw [fT_mulVec, add_eq_left, smul_eq_zero]
  exact or_iff_left ha

theorem fT_sq (p : V4 × V4) : fT p * fT p = 1 + vecMulVec p.1 ((p.2 ⬝ᵥ p.1) • p.2) := by
  have h2 : vecMulVec p.1 p.2 + vecMulVec p.1 p.2 = 0 := by
    ext i j
    exact c7022_zmod2_add_self _
  rw [fT, add_mul, one_mul, mul_add, mul_one, vecMulVec_mul_vecMulVec, add_assoc,
    ← add_assoc (vecMulVec p.1 p.2), h2, zero_add]

theorem vecMulVec_eq_zero {a w : V4} : vecMulVec a w = 0 ↔ a = 0 ∨ w = 0 := by
  constructor
  · intro h
    by_contra hc
    rw [not_or] at hc
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hc.1
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc.2
    have := congrFun (congrFun h i) j
    rw [vecMulVec_apply] at this
    exact mul_ne_zero hi hj this
  · rintro (rfl | rfl) <;> ext i j <;> simp [vecMulVec_apply]

theorem QT_iff {a φ : V4} (ha : a ≠ 0) : QT (a, φ) ↔ φ ≠ 0 ∧ φ ⬝ᵥ a = 0 := by
  have hfix : (Finset.univ.filter fun v : V4 => fT (a, φ) *ᵥ v = v) =
      Finset.univ.filter fun v : V4 => φ ⬝ᵥ v = 0 :=
    Finset.filter_congr fun v _ => fT_fix_iff ha v
  rw [QT, fT_sq, add_eq_left, vecMulVec_eq_zero, smul_eq_zero, hfix]
  by_cases hφ : φ = 0
  · subst hφ
    rw [Finset.filter_true_of_mem fun v _ => zero_dotProduct v, Finset.card_univ,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
    simp
  · rw [c7022_card_ker_dot φ hφ]
    simp [ha, hφ]

theorem card_QT : (Finset.univ.filter QT).card = 105 := by
  classical
  have hrow : ∀ a : V4, (Finset.univ.filter fun φ : V4 => QT (a, φ)).card =
      if a = 0 then 0 else 7 := by
    intro a
    split_ifs with ha
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro φ _ hq
      exact (QT_ne hq).1 ha
    · have he : (Finset.univ.filter fun φ : V4 => QT (a, φ)) =
          (Finset.univ.filter fun φ : V4 => a ⬝ᵥ φ = 0).erase 0 := by
        ext φ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
          QT_iff ha, dotProduct_comm φ a]
      rw [he, Finset.card_erase_of_mem (by simp), c7022_card_ker_dot a ha]
  rw [Finset.card_filter, Fintype.sum_prod_type]
  simp only [← Finset.card_filter, hrow]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul,
    Finset.filter_ne' Finset.univ (0 : V4), Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

theorem card_transvections :
    (Finset.univ.filter fun M : Matrix (Fin 4) (Fin 4) (ZMod 2) => M * M = 1 ∧
      (Finset.univ.filter fun v : Fin 4 → ZMod 2 => M *ᵥ v = v).card = 8).card = 105 := by
  classical
  have himg : (Finset.univ.filter fun M : Matrix (Fin 4) (Fin 4) (ZMod 2) => M * M = 1 ∧
      (Finset.univ.filter fun v : Fin 4 → ZMod 2 => M *ᵥ v = v).card = 8) =
      (Finset.univ.filter QT).image fT := by
    ext M
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h2, h8⟩
      have hr := CFSG.KC.Misc.RankOne.rank_le_one_of_card_fix (ZMod.card 2) M h8.ge
      obtain ⟨a, φ, h⟩ := exists_vecMulVec _ hr
      have hM : fT (a, φ) = M := by
        rw [fT, ← h]
        abel
      exact ⟨(a, φ), by rw [QT, hM]; exact ⟨h2, h8⟩, hM⟩
    · rintro ⟨p, hp, rfl⟩
      exact hp
  rw [himg, Finset.card_image_of_injOn, card_QT]
  intro p hp q hq hpq
  have hp' := QT_ne (Finset.mem_filter.mp hp).2
  have hpq' : vecMulVec p.1 p.2 = vecMulVec q.1 q.2 := add_left_cancel hpq
  obtain ⟨h1, h2⟩ := vecMulVec_inj hp'.1 hp'.2 hpq'
  exact Prod.ext h1 h2

end Transvection

end CFSG.KC.Misc.A7GL42
