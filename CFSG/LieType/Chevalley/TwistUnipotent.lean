module

public import CFSG.LieType.Chevalley.TwistMap
public import CFSG.LieType.Chevalley.Refined
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

section Native

variable {τ : Tag} {K : Type} [Field K]

theorem simpleRoot_injective : Function.Injective (simpleRoot τ) := by
  intro i j h
  by_contra hij
  have h1 := congrFun (congrArg Subtype.val h) i
  simp [simpleRoot, Ne.symm hij] at h1

theorem height_simpleRoot_pos (j : Fin τ.rank) : 0 < height (simpleRoot τ j).1 :=
  (rootCombinatorics τ).pos_simple j

theorem xElement_ne_one {j : Fin τ.rank} {c : K} (hc : c ≠ 0) : xElement j c ≠ 1 := by
  intro h
  have h1 : xOp τ K j c = xOp τ K j 0 := by
    rw [xOp_zero]
    exact congrArg (fun g : adjointGroup τ K =>
      ((g : ModGL τ K) : Module.End K (RootModule τ K))) h
  exact hc (xOp_injective j h1)

theorem xElement_mem_X (j : Fin τ.rank) (c : K) :
    xElement j c ∈ (nativeRootSubgroups τ K).X (simpleRoot τ j) :=
  ((nativeRootSubgroups τ K).mem_simple j _).2 ⟨c, rfl⟩

theorem mem_Uminus_of_mem_X {w : WeylGroup τ} {α : Root τ} (hα : 0 < height α.1)
    (hwα : height (w • α).1 < 0) {x : adjointGroup τ K}
    (hx : x ∈ (nativeRootSubgroups τ K).X α) : x ∈ Uminus τ K w :=
  le_iSup₂_of_le (f := fun (β : Root τ) (_ : 0 < height β.1 ∧ height (w • β).1 < 0) =>
    (nativeRootSubgroups τ K).X β) α ⟨hα, hwα⟩ le_rfl hx

theorem mem_Uplus_of_mem_X {w : WeylGroup τ} {α : Root τ} (hα : 0 < height α.1)
    (hwα : 0 < height (w • α).1) {x : adjointGroup τ K}
    (hx : x ∈ (nativeRootSubgroups τ K).X α) : x ∈ Uplus τ K w :=
  le_iSup₂_of_le (f := fun (β : Root τ) (_ : 0 < height β.1 ∧ 0 < height (w • β).1) =>
    (nativeRootSubgroups τ K).X β) α ⟨hα, hwα⟩ le_rfl hx

theorem not_isRoot_nsmul_single_add_nsmul_single {j k : Fin τ.rank} (hjk : j ≠ k)
    (hc : τ.cartan j k = 0) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬IsRoot τ (a • (Pi.single j 1 : Fin τ.rank → ℤ) + b • Pi.single k 1) := by
  set v : Fin τ.rank → ℤ := a • Pi.single j 1 + b • Pi.single k 1 with hv
  intro h
  have hr := IsRoot.reflect j h
  have hvl : ∀ l, v l = (if l = j then (a : ℤ) else 0) + if l = k then (b : ℤ) else 0 :=
    fun l => by simp [hv, Pi.single_apply]
  have hsum : ∑ l, τ.cartan j l * v l = 2 * a := by
    simp [hvl, mul_add, Finset.sum_add_distrib, τ.cartan_self, hc]
  have hvj : v j = a := by simp [hvl, hjk]
  have hvk : v k = b := by simp [hvl, hjk.symm]
  have hj : reflect τ j v j = -a := by
    have h1 : reflect τ j v j = v j - ∑ l, τ.cartan j l * v l := by simp [reflect]
    rw [h1, hsum, hvj]
    ring
  have hk : reflect τ j v k = b := by rw [reflect_apply_of_ne j hjk.symm, hvk]
  rcases hr.nonneg_or_nonpos with h1 | h1
  · have := h1 j
    omega
  · have := h1 k
    omega

theorem commute_of_mem_simple {j k : Fin τ.rank} (hjk : j ≠ k) (hc : τ.cartan j k = 0)
    {x y : adjointGroup τ K} (hx : x ∈ (nativeRootSubgroups τ K).X (simpleRoot τ j))
    (hy : y ∈ (nativeRootSubgroups τ K).X (simpleRoot τ k)) : Commute x y := by
  have h := (nativeRootSubgroups τ K).comm j (simpleRoot τ k) (height_simpleRoot_pos k)
    (fun h => hjk (simpleRoot_injective h).symm) x hx y hy
  have hbot : (⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
      γ.1 = a • (simpleRoot τ j).1 + b • (simpleRoot τ k).1),
      (nativeRootSubgroups τ K).X γ) = ⊥ := by
    refine iSup_eq_bot.2 fun γ => iSup_eq_bot.2 fun ⟨a, b, ha, hb, hγ⟩ => ?_
    exact absurd (hγ ▸ γ.2) (not_isRoot_nsmul_single_add_nsmul_single hjk hc ha hb)
  rw [hbot, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_commute.1 (by rw [commutatorElement_def]; exact h)

variable [Finite K]

theorem eq_one_of_mem_Uminus_of_nrep_conj_mem_U {w : WeylGroup τ} {x : adjointGroup τ K}
    (hx : x ∈ Uminus τ K w) (hU : nrep τ K w * x * (nrep τ K w)⁻¹ ∈ (nativeData τ K).U) :
    x = 1 := by
  have h : nrep τ K w * x * (nrep τ K w)⁻¹ ∈ (nativeData τ K).B ⊓ Uneg τ K :=
    Subgroup.mem_inf.2 ⟨(nativeData τ K).U_le_B hU, nrep_conj_mem_Uneg hx⟩
  rw [nativeData_B_inf_Uneg, Subgroup.mem_bot, conj_eq_one_iff] at h
  exact h

variable (τ K) in
theorem Uplus_inf_Uminus (w : WeylGroup τ) : Uplus τ K w ⊓ Uminus τ K w = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hp, hm⟩
  exact (Subgroup.mem_bot).2 (eq_one_of_mem_Uminus_of_nrep_conj_mem_U hm (nrep_conj_mem_U hp))

end Native

section Twist

variable (t : TwistTag)

theorem height_smul_single_perm {w : WeylGroup t.tag} (hw : weylTwist t w = w)
    (j : Fin t.tag.rank) :
    height (w • (Pi.single (t.perm j) 1 : Fin t.tag.rank → ℤ)) =
      height (w • (Pi.single j 1 : Fin t.tag.rank → ℤ)) := by
  have h := congrArg (fun α : Root t.tag => height α.1)
    (weylTwist_smul_rootTwist t w (simpleRoot t.tag j))
  simp only [hw, rootTwist_simpleRoot, height_rootTwist] at h
  exact h

def twistOrbitTail : (t : TwistTag) → Fin t.tag.rank → List (Fin t.tag.rank)
  | .E6 => (![[5], [], [4], [], [2], [0]] : Fin 6 → List (Fin 6))
  | .D4 => (![[1, 3], [3, 0], [], [0, 1]] : Fin 4 → List (Fin 4))

theorem twistOrbitTail_spec (i : Fin t.tag.rank) :
    (i :: twistOrbitTail t i).Nodup ∧
      ((i :: twistOrbitTail t i).map t.perm).Perm (i :: twistOrbitTail t i) ∧
      (∀ j ∈ i :: twistOrbitTail t i, ∀ k ∈ i :: twistOrbitTail t i, j ≠ k →
        t.tag.cartan j k = 0) ∧
      ∀ j ∈ i :: twistOrbitTail t i, j = i ∨ j = t.perm i ∨ j = t.perm (t.perm i) := by
  have horth : ∀ i : Fin t.tag.rank, ∀ j ∈ i :: twistOrbitTail t i,
      ∀ k ∈ i :: twistOrbitTail t i, (j == k || t.tag.cartan j k == 0) = true := by
    cases t <;> decide
  refine ⟨?_, ?_, fun j hj k hk hjk => by simpa [hjk] using horth i j hj k hk, ?_⟩ <;>
    revert i <;> cases t <;> decide

variable {K : Type} [Field K] [Finite K]

theorem exists_twistEquiv_fixed_conj_not_mem_U_of_orbit (σ : K →+* K)
    (hσ : Function.Surjective σ) {w : WeylGroup t.tag} (hw : weylTwist t w = w)
    {i : Fin t.tag.rank} (hi : height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0)
    (l : List (Fin t.tag.rank)) (hnd : (i :: l).Nodup)
    (hperm : ((i :: l).map t.perm).Perm (i :: l))
    (horth : ∀ j ∈ i :: l, ∀ k ∈ i :: l, j ≠ k → t.tag.cartan j k = 0)
    (horbit : ∀ j ∈ i :: l, j = i ∨ j = t.perm i ∨ j = t.perm (t.perm i)) :
    ∃ u ∈ (nativeData t.tag K).U, twistEquiv t K σ hσ u = u ∧
      nrep t.tag K w * u * (nrep t.tag K w)⁻¹ ∉ (nativeData t.tag K).U := by
  set f : Fin t.tag.rank → adjointGroup t.tag K := fun j => xElement j 1 with hf
  have hneg : ∀ j ∈ i :: l, height (w • (Pi.single j 1 : Fin t.tag.rank → ℤ)) < 0 := by
    intro j hj
    rcases horbit j hj with rfl | rfl | rfl
    · exact hi
    · rwa [height_smul_single_perm t hw]
    · rwa [height_smul_single_perm t hw, height_smul_single_perm t hw]
  have hcomm : ((i :: l).map f).Pairwise Commute := by
    rw [List.pairwise_map]
    exact hnd.imp_of_mem fun hj hk hjk =>
      commute_of_mem_simple hjk (horth _ hj _ hk hjk) (xElement_mem_X _ _) (xElement_mem_X _ _)
  have hUm : ((i :: l).map f).prod ∈ Uminus t.tag K w := by
    refine list_prod_mem fun x hx => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    exact mem_Uminus_of_mem_X (height_simpleRoot_pos j) (hneg j hj) (xElement_mem_X j 1)
  refine ⟨((i :: l).map f).prod, ?_, ?_, fun hU => ?_⟩
  ·
    refine list_prod_mem fun x hx => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact (nativeData t.tag K).simple_le_U j (xElement_mem_X j 1)
  ·
    have hFf : twistC t K σ ∘ f = f ∘ t.perm := funext fun j => by
      simp only [Function.comp_apply, hf, twistC_xElement, map_one]
    rw [twistEquiv_apply, map_list_prod, List.map_map, hFf, ← List.map_map]
    exact ((hperm.map f).symm.prod_eq' hcomm).symm
  ·
    have hu := eq_one_of_mem_Uminus_of_nrep_conj_mem_U hUm hU
    rw [List.map_cons, List.prod_cons] at hu
    have hil : i ∉ l := (List.nodup_cons.1 hnd).1
    have hy : (l.map f).prod ∈ Uplus t.tag K (simple t.tag i) := by
      refine list_prod_mem fun x hx => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      have hji : simpleRoot t.tag j ≠ simpleRoot t.tag i := fun h =>
        hil (simpleRoot_injective h ▸ hj)
      exact mem_Uplus_of_mem_X (height_simpleRoot_pos j)
        ((rootCombinatorics t.tag).pos_refl i _ (height_simpleRoot_pos j) hji)
        (xElement_mem_X j 1)
    have hxi : f i ∈ Uminus t.tag K (simple t.tag i) := by
      have hs : simple t.tag i • simpleRoot t.tag i = -simpleRoot t.tag i :=
        (rootCombinatorics t.tag).refl_simple i
      refine mem_Uminus_of_mem_X (height_simpleRoot_pos i) ?_ (xElement_mem_X i 1)
      rw [hs, coe_neg_root, height_neg]
      exact neg_neg_of_pos (height_simpleRoot_pos i)
    have hxi' : f i ∈ Uplus t.tag K (simple t.tag i) := by
      rw [eq_inv_of_mul_eq_one_left hu]
      exact inv_mem hy
    have h1 : f i ∈ Uplus t.tag K (simple t.tag i) ⊓ Uminus t.tag K (simple t.tag i) :=
      Subgroup.mem_inf.2 ⟨hxi', hxi⟩
    rw [Uplus_inf_Uminus, Subgroup.mem_bot] at h1
    exact xElement_ne_one one_ne_zero h1

end Twist

theorem exists_twistEquiv_fixed_conj_not_mem_U (t : TwistTag) (K : Type) [Field K] [Finite K]
    (σ : K →+* K) (hσ : Function.Surjective σ) {w : WeylGroup t.tag}
    (hw : weylTwist t w = w) (hw1 : w ≠ 1) :
    ∃ u ∈ (nativeData t.tag K).U, twistEquiv t K σ hσ u = u ∧
      nrep t.tag K w * u * (nrep t.tag K w)⁻¹ ∉ (nativeData t.tag K).U := by
  obtain ⟨i, hi⟩ := exists_height_neg_of_ne_one hw1
  obtain ⟨hnd, hperm, horth, horbit⟩ := twistOrbitTail_spec t i
  exact exists_twistEquiv_fixed_conj_not_mem_U_of_orbit t σ hσ hw hi _ hnd hperm horth horbit

end CFSG.LieType.Chevalley
