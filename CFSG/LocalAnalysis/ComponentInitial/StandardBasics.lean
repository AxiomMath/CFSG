module

public import CFSG.Assembly.ComponentTypeDefs
import CFSG.GroupTheory.OddOverlap

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Assembly CFSG.Assembly.ComponentType Polynomial
open scoped commutatorElement

theorem finite_odd_field_two_squares {k : Type*} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    (c : k) : ∃ a b : k, a ^ 2 + b ^ 2 = c := by
  have := Fintype.ofFinite k
  have hodd : Fintype.card k % 2 = 1 :=
    Nat.mod_two_ne_zero.1 fun h => hk (FiniteField.even_card_iff_char_two.2 h)
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (f := (X ^ 2 : k[X]))
    (g := X ^ 2 - C c) (degree_X_pow 2) (degree_X_pow_sub_C (by decide) _) hodd
  refine ⟨a, b, ?_⟩
  rw [← sub_eq_zero]
  simpa only [eval_C, eval_X, eval_pow, eval_sub, ← add_sub_assoc] using hab

section FusedLift

variable {E J : Type*} [Group E] [Group J]

theorem mul_sq_of_commutator_mem_center {x y : E} (hc : ⁅x, y⁆ ∈ Subgroup.center E)
    (hc2 : ⁅x, y⁆ ^ 2 = 1) : (x * y) ^ 2 = ⁅x, y⁆ * x ^ 2 * y ^ 2 := by
  have hz := Subgroup.mem_center_iff.1 hc
  have hxy : x * y = ⁅x, y⁆ * (y * x) := by rw [commutatorElement_def]; group
  generalize ⁅x, y⁆ = c at hz hc2 hxy ⊢
  have hyx : y * x = c * (x * y) := by
    rw [hxy, ← mul_assoc, ← sq, hc2, one_mul]
  calc (x * y) ^ 2 = x * (y * x) * y := by simp only [sq, mul_assoc]
    _ = x * (c * (x * y)) * y := by rw [hyx]
    _ = (x * c) * (x * y) * y := by simp only [mul_assoc]
    _ = c * x * (x * y) * y := by rw [hz x]
    _ = c * x ^ 2 * y ^ 2 := by simp only [sq, mul_assoc]

theorem commutatorElement_mul_right_of_mem_center {x y z : E}
    (hz : ⁅x, z⁆ ∈ Subgroup.center E) : ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have h := Subgroup.mem_center_iff.1 hz
  have : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [this, h y, mul_assoc ⁅x, z⁆, mul_inv_cancel, mul_one]

theorem exists_mem_ne_of_four_lt_card {V : Subgroup J} (h : 4 < Nat.card V) (a b c d : J) :
    ∃ x ∈ V, x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := by
  by_contra hcon
  push Not at hcon
  have hsub : (V : Set J) ⊆ {a, b, c, d} := fun x hx => by
    by_cases ha : x = a
    · simp [ha]
    by_cases hb : x = b
    · simp [hb]
    by_cases hc : x = c
    · simp [hc]
    simp [hcon x hx ha hb hc]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h4 : ({a, b, c, d} : Set J).ncard ≤ 4 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    refine (Nat.succ_le_succ (Set.ncard_insert_le _ _)).trans ?_
    refine (Nat.succ_le_succ (Nat.succ_le_succ (Set.ncard_insert_le _ _))).trans ?_
    simp
  rw [← Nat.card_coe_set_eq] at hle
  change Nat.card V ≤ _ at hle
  omega

variable {η : E →* J}

theorem isElemAbelian_comap_of_fused (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (hCe : IsElemAbelian 2 η.ker) {V : Subgroup J} {r : ℕ}
    (hV : IsElemAbelian 2 V) (hr : 3 ≤ r) (hcard : Nat.card V = 2 ^ r)
    (hfus : ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → w ≠ 1 → ∃ g : J, g * v * g⁻¹ = w) :
    IsElemAbelian 2 (V.comap η) := by
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := hV.2
  have hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw => by
    have := hV.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩
    exact congrArg Subtype.val this
  have hker2 : ∀ c ∈ η.ker, c ^ 2 = 1 := hCe.2
  have hsqk : ∀ x, η x ∈ V → x ^ 2 ∈ η.ker := fun x hx => by
    rw [MonoidHom.mem_ker, map_pow, hV2 _ hx]
  have hcomk : ∀ x y, η x ∈ V → η y ∈ V → ⁅x, y⁆ ∈ η.ker := fun x y hx hy => by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hVc _ hx _ hy
  have hsq_eq : ∀ x y, η x = η y → x ^ 2 = y ^ 2 := fun x y hxy => by
    have hc : x⁻¹ * y ∈ η.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    obtain ⟨c, hc', rfl⟩ : ∃ c ∈ η.ker, y = x * c := ⟨x⁻¹ * y, hc, by group⟩
    have hz := Subgroup.mem_center_iff.1 (hC hc')
    rw [sq, sq, ← mul_assoc, mul_assoc x c x, ← hz x, ← mul_assoc, mul_assoc, ← sq c,
      hker2 c hc', mul_one]
  have hsq_fus : ∀ x y, η x ∈ V → η y ∈ V → η x ≠ 1 → η y ≠ 1 → x ^ 2 = y ^ 2 :=
    fun x y hx hy hx1 hy1 => by
      obtain ⟨g, hg⟩ := hfus _ hx _ hy hx1 hy1
      obtain ⟨e, rfl⟩ := hη g
      have hconj : η (e * x * e⁻¹) = η y := by rw [map_mul, map_mul, map_inv, hg]
      rw [← hsq_eq _ _ hconj, conj_pow, Subgroup.mem_center_iff.1 (hC (hsqk x hx)) e,
        mul_inv_cancel_right]
  have h4 : 4 < Nat.card V := by
    rw [hcard]
    calc 4 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have hinv : ∀ a ∈ V, a⁻¹ = a := fun a ha =>
    inv_eq_of_mul_eq_one_right (by rw [← sq, hV2 a ha])
  have hne1 : ∀ a ∈ V, ∀ b ∈ V, a ≠ b → a * b ≠ 1 := fun a ha b hb hab h =>
    hab ((hinv a ha).symm.trans (inv_eq_of_mul_eq_one_right h))
  obtain ⟨v, hv, hv1, -, -, -⟩ := exists_mem_ne_of_four_lt_card h4 1 1 1 1
  obtain ⟨w, hw, hw1, hwv, -, -⟩ := exists_mem_ne_of_four_lt_card h4 1 v 1 1
  obtain ⟨u, hu, hu1, huv, huw, huvw⟩ := exists_mem_ne_of_four_lt_card h4 1 v w (v * w)
  have hwu1 : w * u ≠ 1 := hne1 w hw u hu (Ne.symm huw)
  have hvwu : v ≠ w * u := fun h => huvw (by
    rw [eq_inv_mul_of_mul_eq h.symm, hinv w hw, hVc w hw v hv])
  obtain ⟨x, rfl⟩ := hη v
  obtain ⟨y, rfl⟩ := hη w
  obtain ⟨z, rfl⟩ := hη u
  have hs2 : (x ^ 2) ^ 2 = 1 := hker2 _ (hsqk x hv)
  have hcom_s : ∀ a b, η a ∈ V → η b ∈ V → η a ≠ 1 → η b ≠ 1 → η a ≠ η b →
      ⁅a, b⁆ = x ^ 2 := fun a b ha hb ha1 hb1 hab => by
    have hk := hcomk a b ha hb
    have hab1 : η (a * b) ≠ 1 := by rw [map_mul]; exact hne1 _ ha _ hb hab
    have habV : η (a * b) ∈ V := by rw [map_mul]; exact V.mul_mem ha hb
    have h1 := mul_sq_of_commutator_mem_center (hC hk) (hker2 _ hk)
    rw [hsq_fus (a * b) x habV hv hab1 hv1, hsq_fus a x ha hv ha1 hv1,
      hsq_fus b x hb hv hb1 hv1, mul_assoc, ← sq, hs2, mul_one] at h1
    exact h1.symm
  have hyzV : η (y * z) ∈ V := by rw [map_mul]; exact V.mul_mem hw hu
  have hs : x ^ 2 = 1 := by
    have h1 := hcom_s x (y * z) hv hyzV hv1 (by rwa [map_mul]) (by rwa [map_mul])
    rw [commutatorElement_mul_right_of_mem_center (hC (hcomk x z hv hu)),
      hcom_s x y hv hw hv1 hw1 (Ne.symm hwv), hcom_s x z hv hu hv1 hu1 (Ne.symm huv)] at h1
    exact mul_eq_left.1 h1
  have hsq1 : ∀ a, η a ∈ V → a ^ 2 = 1 := fun a ha => by
    by_cases ha1 : η a = 1
    · exact hker2 a ha1
    · rw [hsq_fus a x ha hv ha1 hv1, hs]
  have hcomm1 : ∀ a b, η a ∈ V → η b ∈ V → a * b = b * a := fun a b ha hb => by
    by_cases ha1 : η a = 1
    · exact Subgroup.mem_center_iff.1 (hC ha1) b |>.symm
    by_cases hb1 : η b = 1
    · exact Subgroup.mem_center_iff.1 (hC hb1) a
    by_cases hab : η a = η b
    · have hc : a⁻¹ * b ∈ η.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
      obtain ⟨c, hc', rfl⟩ : ∃ c ∈ η.ker, b = a * c := ⟨a⁻¹ * b, hc, by group⟩
      rw [← mul_assoc, mul_assoc a c a, ← Subgroup.mem_center_iff.1 (hC hc') a, mul_assoc]
    · rw [← commutatorElement_eq_one_iff_mul_comm, hcom_s a b ha hb ha1 hb1 hab, hs]
  exact ⟨⟨⟨fun a b => Subtype.ext (hcomm1 a b a.2 b.2)⟩⟩, fun a ha => hsq1 a ha⟩

theorem fused_rank_three_elementary_two_subgroup_central_lift [Finite E] [Finite J]
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (hCe : IsElemAbelian 2 η.ker)
    {V : Subgroup J} {r : ℕ} (hV : IsElemAbelian 2 V) (hr : 3 ≤ r) (hcard : Nat.card V = 2 ^ r)
    (hfus : ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → w ≠ 1 → ∃ g : J, g * v * g⁻¹ = w) :
    IsElemAbelian 2 (V.comap η) :=
  isElemAbelian_comap_of_fused hη hC hCe hV hr hcard hfus

end FusedLift

section Standard

variable {G : Type*} [Group G]

theorem standard_involution_centralizer_normality [Finite G] {L : Subgroup G}
    (hL : IsStandardSubgroup L) {t : G} (ht : t ∈ Subgroup.centralizer (L : Set G))
    (ht2 : orderOf t = 2) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G) ∧
      L ≤ Subgroup.centralizer ({t} : Set G) ∧
      (L.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal ∧
      IsComponentOf L (Subgroup.centralizer ({t} : Set G)) ∧
      ((Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf
        (Subgroup.centralizer ({t} : Set G))).Normal := by
  obtain ⟨hq, -, hodd, hnorm, -⟩ := hL
  set C := Subgroup.centralizer (L : Set G)
  set T := Subgroup.centralizer ({t} : Set G)
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    StandardSubgroupAPI.mem_of_odd_inf_map_conj_of_commute hodd ht ht2
      (Subgroup.mem_centralizer_singleton_iff.1 hg)
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hnorm ▸ hTC
  have hLT : L ≤ T := fun l hl => Subgroup.mem_centralizer_iff.2 fun h hh => by
    rw [Set.mem_singleton_iff.1 hh]
    exact (Subgroup.mem_centralizer_iff.1 ht l hl).symm
  have hLn : (L.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLT).2 hTL
  refine ⟨hTL, hLT, hLn, ⟨hLT, IsSubnormal.step hLT hLn (IsSubnormal.refl T), hq⟩, ?_⟩
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 ?_
  exact (le_inf hTC (Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf

end Standard

end CFSG.LocalAnalysis.ComponentInitial
