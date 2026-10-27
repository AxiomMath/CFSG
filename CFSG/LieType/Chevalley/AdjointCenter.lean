module

public import CFSG.LieType.Simplicity.Torus
public import CFSG.LieType.Chevalley.Refined
public import CFSG.LieType.Chevalley.RootOps.Comm
public import CFSG.LieType.BorelTits.TitsClause

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Simplicity CFSG.LieType.BorelTits

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem nativeData_U_inf_X_of_not_pos
    (α : Root τ) (hα : ¬ (rootCombinatorics τ).pos α) :
    (nativeData τ K).U ⊓ (nativeData τ K).X α = ⊥ := by
  rw [rootCombinatorics_pos] at hα
  have hneg : height α.1 < 0 := (IsRoot.height_pos_or_neg α.2).resolve_left hα
  rw [eq_bot_iff, ← nativeData_B_inf_Uneg τ K]
  exact inf_le_inf RootGroupData.U_le_B
    (le_iSup₂_of_le (f := fun (β : Root τ) (_ : height β.1 < 0) => (nativeRootSubgroups τ K).X β)
      α hneg le_rfl)

theorem nativeData_normalizer_U_le_B :
    Subgroup.normalizer ((nativeData τ K).U : Set (adjointGroup τ K)) ≤ (nativeData τ K).B :=
  (nativeData τ K).normalizer_le (nativeRootSubgroups τ K).simple_le_normalizer_Ui
    (nativeRootSubgroups τ K).rankOne (nativeRootSubgroups τ K).closure_B_union_n
    nativeData_U_inf_X_of_not_pos (nativeRootSubgroups τ K).X_ne_bot
    fun _ hw => rootCombinatorics_eq_one hw

theorem mem_H_of_mem_center
    {z : adjointGroup τ K} (hz : z ∈ Subgroup.center (adjointGroup τ K)) :
    z ∈ (nativeData τ K).H := by
  obtain ⟨p, hpK⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have hzB : z ∈ (nativeData τ K).B := nativeData_normalizer_U_le_B
    (Subgroup.mem_normalizer_iff.2 fun x => by
      rw [← Subgroup.mem_center_iff.1 hz x, mul_inv_cancel_right])
  obtain ⟨u, hu, h, hh, rfl⟩ := exists_mul_of_mem_B hzB
  have hcomm : u * h = h * u := by
    have h1 := Subgroup.mem_center_iff.1 hz h
    have h2 : h * u * h = u * h * h := by rw [mul_assoc, h1]
    exact (mul_right_cancel h2).symm
  have hcop : Nat.Coprime (orderOf (u * h)) p := by
    have hc := Holds.coprime_card_center (holds_adjointGroup_tag τ K p)
    exact Nat.Coprime.coprime_dvd_left
      (by rw [← Subgroup.orderOf_mk (u * h) hz]; exact orderOf_dvd_natCard _) hc
  obtain ⟨a, ha⟩ := ((nativeRootSubgroups τ K).isPGroup_U p) ⟨u, hu⟩
  have hua : u ^ p ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  set m := orderOf (u * h)
  have hm : Nat.Coprime (p ^ a) m := (Nat.Coprime.pow_left a hcop.symm)
  set n := (p ^ a) ^ Nat.totient m
  have hn : n % m = 1 % m := Nat.ModEq.pow_totient hm
  have hzn : (u * h) ^ n = u * h := by
    rw [← pow_mod_orderOf, show n % orderOf (u * h) = 1 % orderOf (u * h) from hn,
      pow_mod_orderOf, pow_one]
  have hpow : (u * h) ^ n = h ^ n := by
    have hc : Commute u h := hcomm
    rw [hc.mul_pow]
    have hdvd : p ^ a ∣ n := by
      have htot : 0 < Nat.totient m := Nat.totient_pos.2 (orderOf_pos _)
      exact dvd_pow_self _ htot.ne'
    rw [orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one hua).trans hdvd), one_mul]
  rw [← hzn, hpow]
  exact pow_mem hh n

theorem eq_one_of_mem_H_of_commute_xOp
    {h : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    (i : Fin τ.rank) (hc : ((h : ModGL τ K) : Module.End K (RootModule τ K)) * xOp τ K i 1 =
      xOp τ K i 1 * ((h : ModGL τ K) : Module.End K (RootModule τ K))) {μ : K}
    (h₁ : ((h : ModGL τ K) : Module.End K (RootModule τ K))
      (Finsupp.single (.inr (simpleRoot τ i)) 1) = μ • Finsupp.single (.inr (simpleRoot τ i)) 1) :
    μ = 1 := by
  classical
  obtain ⟨μ', h₂⟩ := exists_apply_single_eq_smul_of_mem_H hh (.inr (-simpleRoot τ i))
  have e₁ : rootVec τ K (Pi.single i 1) = Finsupp.single (.inr (simpleRoot τ i)) 1 :=
    rootVec_eq_single (isRoot_single τ i)
  have e₂ : rootVec τ K (-Pi.single i 1) = Finsupp.single (.inr (-simpleRoot τ i)) 1 :=
    rootVec_eq_single (isRoot_neg_single τ i)
  rw [← e₁] at h₁
  rw [← e₂] at h₂
  have key := congrArg (fun f : Module.End K (RootModule τ K) =>
    f (rootVec τ K (-Pi.single i 1))) hc
  simp only [Module.End.mul_apply] at key
  rw [xOp_rootVec_neg_single', h₂, map_smul, xOp_rootVec_neg_single', map_add, map_add,
    map_smul, map_smul, apply_hVec_of_mem_H hh i, h₁, h₂, one_smul, one_pow, one_smul] at key
  have hne : (-simpleRoot τ i : Root τ) ≠ simpleRoot τ i := fun h => by
    have := congrArg (fun α : Root τ => α.1 i) h
    simp [simpleRoot] at this
  have hk₁ := congrArg (fun x : RootModule τ K => x (Sum.inl i)) key
  have hk₂ := congrArg (fun x : RootModule τ K => x (Sum.inr (simpleRoot τ i))) key
  simp only [e₁, e₂, hVec_eq_single, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply, reduceCtorEq, ite_false, ite_true, Sum.inr.injEq, hne, mul_zero,
    mul_one, zero_add, add_zero] at hk₁ hk₂
  linear_combination hk₂ - hk₁

theorem center_adjointGroup_eq_bot :
    Subgroup.center (adjointGroup τ K) = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzH := mem_H_of_mem_center hz
  set zl : Module.End K (RootModule τ K) := ((z : ModGL τ K) : Module.End K (RootModule τ K))
    with hzl
  have hxc : ∀ i, zl * xOp τ K i 1 = xOp τ K i 1 * zl := fun i => by
    have h := Subgroup.mem_center_iff.1 hz ⟨xUnit τ K i 1, xUnit_mem_adjointGroup i 1⟩
    have h' := congrArg (fun g : adjointGroup τ K => ((g : ModGL τ K) : Module.End K
      (RootModule τ K))) h
    simpa only [Subgroup.coe_mul, Units.val_mul, coe_xUnit] using h'.symm
  have hroot : ∀ α : Root τ, zl (Finsupp.single (.inr α) 1) = Finsupp.single (.inr α) 1 := by
    intro α
    obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.1 α.2
    obtain ⟨m, rfl⟩ := weylHom_surjective (τ := τ) (K := K) w
    have hα : α = weylHom τ K m • simpleRoot τ j := Subtype.ext hwj.symm
    obtain ⟨μ, hμ⟩ := exists_apply_single_eq_smul_of_mem_H hzH (.inr α)
    have hconj := conj_apply_single_inr m z (simpleRoot τ j) (μ := μ) (by rw [← hα]; exact hμ)
    have hzm : (m : adjointGroup τ K)⁻¹ * z * m = z := by
      rw [mul_assoc, ← Subgroup.mem_center_iff.1 hz, inv_mul_cancel_left]
    rw [hzm] at hconj
    have h1 := eq_one_of_mem_H_of_commute_xOp hzH j (hxc j) hconj
    rw [hμ, h1, one_smul]
  refine Subtype.ext (Units.ext (Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_))
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Subgroup.coe_one, Units.val_one,
    Module.End.one_apply]
  rcases b with i | α
  · rw [← hVec_eq_single]
    exact apply_hVec_of_mem_H hzH i
  · exact hroot α

end CFSG.LieType.Chevalley
