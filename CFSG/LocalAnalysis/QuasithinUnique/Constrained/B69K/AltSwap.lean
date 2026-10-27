module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltNatData

public section

namespace CFSG.Quasithin.B69K

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open CFSG.HardMathSupport.Cooperstein.Coordinator

section SwapHelpers

open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

theorem sp_zmod2_sub_eq_one : ∀ u w : ZMod 2, u ≠ w → w - u = 1 := by decide

theorem sp_evenWeightPerm_sub {m : ℕ} (a c : Fin m) (hac : a ≠ c) (x : evenWeight m) :
    evenWeightPerm (Equiv.swap a c) x - x = 0 ∨
      evenWeightPerm (Equiv.swap a c) x - x = pairEW a c := by
  by_cases h : (x : Fin m → ZMod 2) a = (x : Fin m → ZMod 2) c
  · left
    apply Subtype.ext
    funext i
    simp only [AddSubgroup.coe_sub, Pi.sub_apply, evenWeightPerm_apply, Equiv.swap_inv,
      AddSubgroup.coe_zero, Pi.zero_apply]
    by_cases hia : i = a
    · simp [hia, Equiv.swap_apply_left, h]
    · by_cases hic : i = c
      · simp [hic, Equiv.swap_apply_right, h]
      · simp [Equiv.swap_apply_of_ne_of_ne hia hic]
  · right
    apply Subtype.ext
    funext i
    simp only [AddSubgroup.coe_sub, Pi.sub_apply, evenWeightPerm_apply, Equiv.swap_inv,
      pairEW_apply]
    by_cases hia : i = a
    · have h' : (x : Fin m → ZMod 2) c - (x : Fin m → ZMod 2) a = 1 :=
        sp_zmod2_sub_eq_one _ _ h
      simp [hia, hac, Equiv.swap_apply_left, h']
    · by_cases hic : i = c
      · have h' : (x : Fin m → ZMod 2) a - (x : Fin m → ZMod 2) c = 1 :=
          sp_zmod2_sub_eq_one _ _ (Ne.symm h)
        simp [hic, Ne.symm hac, Equiv.swap_apply_right, h']
      · simp [hia, hic, Equiv.swap_apply_of_ne_of_ne hia hic]

theorem sp_altAct_sub {m : ℕ} (a c : Fin m) (hac : a ≠ c) (v : altHeart m) :
    altAct (Equiv.swap a c) v - v = 0 ∨
      altAct (Equiv.swap a c) v - v = ((pairEW a c : evenWeight m) : altHeart m) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  rw [altAct_mk, ← QuotientAddGroup.mk_sub]
  rcases sp_evenWeightPerm_sub a c hac x with h | h
  · left
    rw [h, QuotientAddGroup.mk_zero]
  · right
    rw [h]

theorem sp_altAct_pairEW {m : ℕ} (a c : Fin m) :
    altAct (Equiv.swap a c) ((pairEW a c : evenWeight m) : altHeart m) =
      ((pairEW a c : evenWeight m) : altHeart m) := by
  rw [altAct_mk, evenWeightPerm_pairEW, Equiv.swap_apply_left, Equiv.swap_apply_right,
    pairEW_comm]

end SwapHelpers

section Stmts

variable {S : Type} [CommGroup S] [Finite S] {G Lt : Subgroup (MulAut S)} {hLG : Lt ≤ G} {m : ℕ}

open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

theorem swap_properties (D : AltNatData G Lt hLG m) (hm : 9 ≤ m) (hodd : Odd m)
    {b : MulAut S} (hb : b ∈ G) (hsw : (D.θ ⟨b, hb⟩).IsSwap) :
    b ^ 2 = 1 ∧ IsQuadratic (Subgroup.zpowers b) ∧ b ≠ 1 ∧
      Nat.card S = 2 * Nat.card (fixV (Subgroup.zpowers b)) := by
  obtain ⟨a, c, hac, ht⟩ := hsw
  have hsq : D.θ ((⟨b, hb⟩ : ↥G) ^ 2) = 1 := by
    rw [map_pow, ht, sq, Equiv.swap_mul_self]
  have hb2 : (⟨b, hb⟩ : ↥G) ^ 2 = 1 := D.inj (hsq.trans (map_one D.θ).symm)
  have hsq1 : b ^ 2 = 1 := by
    have h := congrArg Subtype.val hb2
    simpa using h
  have hb1 : b ≠ 1 := by
    intro h
    have h1 : (⟨b, hb⟩ : ↥G) = 1 := Subtype.ext h
    have hs : Equiv.Perm.sign (D.θ ⟨b, hb⟩) = 1 := by
      rw [h1, map_one, map_one]
    rw [ht, Equiv.Perm.sign_swap hac] at hs
    have h2 := congrArg Units.val hs
    norm_num at h2
  have hord : orderOf b = 2 := orderOf_eq_prime hsq1 hb1
  have hzp : ∀ k : ℤ, b ^ k = 1 ∨ b ^ k = b := by
    intro k
    have h : b ^ (k % 2) = b ^ k := by
      have h0 := zpow_mod_orderOf b k
      rw [hord] at h0
      simpa using h0
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [← h, hk, zpow_zero]
    · right
      rw [← h, hk, zpow_one]
  have hfixzp : ∀ v : S, (∀ x ∈ Subgroup.zpowers b, x v = v) ↔ b v = v := by
    intro v
    constructor
    · intro h
      exact h b (Subgroup.mem_zpowers b)
    · intro h x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rcases hzp k with hk | hk
      · simp [hk]
      · rw [hk]
        exact h
  let δ : S →* S :=
    { toFun := fun s => b s * s⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        show b (x * y) * (x * y)⁻¹ = b x * x⁻¹ * (b y * y⁻¹)
        rw [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hδ : ∀ s : S, δ s = b s * s⁻¹ := fun s => rfl
  have hequiv : ∀ s : S, Multiplicative.toAdd (D.π (b s)) =
      altAct (Equiv.swap a c) (Multiplicative.toAdd (D.π s)) := by
    intro s
    have h := D.equiv ⟨b, hb⟩ s
    rw [ht] at h
    exact h
  have hval_eq : ∀ s : S, Multiplicative.toAdd (D.π (δ s)) =
      altAct (Equiv.swap a c) (Multiplicative.toAdd (D.π s)) - Multiplicative.toAdd (D.π s) := by
    intro s
    rw [hδ s, map_mul, map_inv, toAdd_mul, toAdd_inv, hequiv s, sub_eq_add_neg]
  have hval : ∀ s : S, Multiplicative.toAdd (D.π (δ s)) = 0 ∨
      Multiplicative.toAdd (D.π (δ s)) = ((pairEW a c : evenWeight m) : altHeart m) := by
    intro s
    rw [hval_eq s]
    exact sp_altAct_sub a c hac _
  obtain ⟨s₀, hs₀⟩ : ∃ s : S, b s ≠ s := by
    by_contra hcon
    push Not at hcon
    exact hb1 (MulEquiv.ext fun x => by simp [hcon x])
  have hne : δ s₀ ≠ 1 := by
    intro h
    apply hs₀
    rw [hδ s₀] at h
    exact mul_inv_eq_one.mp h
  have hc0 : Multiplicative.toAdd (D.π (δ s₀)) = ((pairEW a c : evenWeight m) : altHeart m) := by
    rcases hval s₀ with h | h
    · exfalso
      apply hne
      apply D.π.injective
      apply Multiplicative.toAdd.injective
      rw [h, map_one, toAdd_one]
    · exact h
  have hdichot : ∀ s : S, δ s = 1 ∨ δ s = δ s₀ := by
    intro s
    rcases hval s with h | h
    · left
      apply D.π.injective
      apply Multiplicative.toAdd.injective
      rw [h, map_one, toAdd_one]
    · right
      apply D.π.injective
      apply Multiplicative.toAdd.injective
      rw [h, hc0]
  have hfixc0 : b (δ s₀) = δ s₀ := by
    apply D.π.injective
    apply Multiplicative.toAdd.injective
    rw [hequiv (δ s₀), hc0, sp_altAct_pairEW a c]
  have hgen : ∀ y : S, (y = 1 ∨ y = δ s₀) → b y = y := by
    rintro y (rfl | rfl)
    · exact map_one b
    · exact hfixc0
  have hFeq : fixV (Subgroup.zpowers b) = δ.ker := by
    ext v
    rw [CFSG.Quasithin.mem_fixV, MonoidHom.mem_ker, hfixzp v, hδ v, mul_inv_eq_one]
  have hgen_val : ∀ x ∈ Subgroup.zpowers b, ∀ v : S, x v * v⁻¹ = 1 ∨ x v * v⁻¹ = δ s₀ := by
    intro x hx v
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases hzp k with hk | hk
    · left
      rw [hk]
      simp
    · rw [hk]
      rcases hdichot v with h | h
      · left
        rw [hδ v] at h
        exact h
      · right
        rw [hδ v] at h
        exact h
  have hc_le : commV (Subgroup.zpowers b) ≤ fixV (Subgroup.zpowers b) := by
    show Subgroup.closure _ ≤ fixV (Subgroup.zpowers b)
    rw [Subgroup.closure_le]
    rintro w ⟨x, hx, v, rfl⟩
    show x v * v⁻¹ ∈ fixV (Subgroup.zpowers b)
    rw [CFSG.Quasithin.mem_fixV]
    exact (hfixzp _).mpr (hgen _ (hgen_val x hx v))
  have hIsQ : IsQuadratic (Subgroup.zpowers b) := hc_le
  have hrange2 : Nat.card δ.range = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨1, one_mem _⟩, ⟨δ s₀, MonoidHom.mem_range.mpr ⟨s₀, rfl⟩⟩, ?_, ?_⟩
    · intro h
      exact hne (congrArg Subtype.val h).symm
    · apply Set.eq_univ_of_forall
      rintro ⟨z, hz⟩
      obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hz
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hdichot s with h | h
      · left
        exact Subtype.ext h
      · right
        exact Subtype.ext h
  have hcard : Nat.card δ.ker * δ.ker.index = Nat.card S := Subgroup.card_mul_index δ.ker
  rw [Subgroup.index_ker, hrange2] at hcard
  refine ⟨hsq1, hIsQ, hb1, ?_⟩
  rw [hFeq, ← hcard, Nat.mul_comm]

theorem range_eq_top_of_swap (D : AltNatData G Lt hLG m) {b : MulAut S} (hb : b ∈ G)
    (hsw : (D.θ ⟨b, hb⟩).IsSwap) : D.θ.range = ⊤ := by
  obtain ⟨a, c, hac, ht⟩ := hsw
  have hsub : alternatingGroup (Fin m) ≤ D.θ.range := by
    refine le_trans D.alt_le ?_
    intro σ hσ
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hσ
    exact MonoidHom.mem_range.mpr ⟨Subgroup.inclusion hLG x, rfl⟩
  have hT : Equiv.swap a c ∈ D.θ.range := MonoidHom.mem_range.mpr ⟨⟨b, hb⟩, ht⟩
  rw [eq_top_iff]
  intro σ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · exact hsub (Equiv.Perm.mem_alternatingGroup.mpr h)
  · have hσt : σ * Equiv.swap a c ∈ alternatingGroup (Fin m) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, h, Equiv.Perm.sign_swap hac]
      all_goals rfl
    have h2 := mul_mem (hsub hσt) hT
    rwa [mul_assoc, Equiv.swap_mul_self, mul_one] at h2

end Stmts

section Glue

variable {S : Type} [CommGroup S] [Finite S] {G Lt : Subgroup (MulAut S)} {hLG : Lt ≤ G} {m : ℕ}

theorem theta_mem_alt (D : AltNatData G Lt hLG m) (hperf : Group.IsPerfect ↥Lt) (x : ↥Lt) :
    D.θ (Subgroup.inclusion hLG x) ∈ alternatingGroup (Fin m) := by
  haveI := hperf
  let φ : ↥Lt →* ℤˣ := Equiv.Perm.sign.comp (D.θ.comp (Subgroup.inclusion hLG))
  haveI : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
  haveI : Subsingleton ↥φ.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  have hx : φ x = 1 := by
    have h1 : (⟨φ x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ : ↥φ.range) = 1 :=
      Subsingleton.elim _ _
    exact congrArg Subtype.val h1
  rw [Equiv.Perm.mem_alternatingGroup]
  exact hx

end Glue

end CFSG.Quasithin.B69K
