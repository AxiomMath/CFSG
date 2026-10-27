module

public import CFSG.LocalAnalysis.EvenSmallLie.Setup
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusionZStar

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

theorem exists_mem_ne_one_of_relIndex_lt_card [Finite G] {M W X : Subgroup G} (hWX : W ≤ X)
    (hlt : M.relIndex X < Nat.card W) : ∃ w ∈ W, w ∈ M ∧ w ≠ 1 := by
  by_contra! h
  have hbot : M ⊓ W = ⊥ := eq_bot_iff.mpr fun w hw => mem_bot.mpr (h w hw.2 hw.1)
  have hcard := relIndex_mul_card M W
  rw [hbot, card_bot, mul_one] at hcard
  have hle := relIndex_le_of_le_right (H := M) hWX index_ne_zero_of_finite
  omega

theorem eq_of_isConj_of_relIndex_lt_card [Finite G] {d : G} {M : Subgroup G} (hdM : d ∈ M)
    (hM : ∀ y ∈ M, IsConj d y → y = d)
    (hV : ∀ y ∈ centralizer ({d} : Set G), y ∉ M → IsConj d y → ∃ V : Subgroup G,
      M.relIndex (centralizer ({d} : Set G)) < Nat.card V ∧ V ≤ centralizer ({y} : Set G) ∧
        ∀ v ∈ V, v ≠ 1 → IsConj (v * y) y) :
    ∀ y ∈ centralizer ({d} : Set G), IsConj d y → y = d := by
  intro y hyX hy
  by_contra hyd
  obtain ⟨V, hlt, hVy, hVconj⟩ := hV y hyX (fun hyM => hyd (hM y hyM hy)) hy
  obtain ⟨c, rfl⟩ := isConj_iff.mp hy
  have hWX : V.map (MulAut.conj c⁻¹).toMonoidHom ≤ centralizer ({d} : Set G) := by
    rintro _ ⟨v, hv, rfl⟩
    have hcomm := mem_centralizer_singleton_iff.mp (hVy hv)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc c⁻¹ * v * c * d = c⁻¹ * (v * (c * d * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * d * c⁻¹ * v) * c := by rw [hcomm]
      _ = d * (c⁻¹ * v * c) := by group
  have hcard : Nat.card (V.map (MulAut.conj c⁻¹).toMonoidHom) = Nat.card V :=
    card_map_of_injective (MulAut.conj c⁻¹).injective
  obtain ⟨w, ⟨v, hv, rfl⟩, hwM, hw1⟩ :=
    exists_mem_ne_one_of_relIndex_lt_card hWX (hcard ▸ hlt)
  have hv1 : v ≠ 1 := by
    rintro rfl
    exact hw1 (map_one _)
  have hconj : IsConj d ((MulAut.conj c⁻¹).toMonoidHom v * d) := by
    refine hy.trans ((hVconj v hv hv1).symm.trans (isConj_iff.mpr ⟨c⁻¹, ?_⟩))
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  exact hw1 (by simpa using hM _ (mul_mem hwM hdM) hconj)

theorem fours_group_excludes_external_fusion [Finite G] {d : G} {M : Subgroup G} (hdM : d ∈ M)
    (hindex : M.relIndex (centralizer ({d} : Set G)) ≤ 2) (hM : ∀ y ∈ M, IsConj d y → y = d)
    (hV : ∀ y ∈ centralizer ({d} : Set G), y ∉ M → IsConj d y → ∃ V : Subgroup G,
      Nat.card V = 4 ∧ V ≤ centralizer ({y} : Set G) ∧ ∀ v ∈ V, v ≠ 1 → IsConj (v * y) y) :
    ∀ y ∈ centralizer ({d} : Set G), IsConj d y → y = d :=
  eq_of_isConj_of_relIndex_lt_card hdM hM fun y hyX hyM hy => by
    obtain ⟨V, hV4, hVy, hVconj⟩ := hV y hyX hyM hy
    exact ⟨V, by omega, hVy, hVconj⟩

theorem exists_four_of_pair {N : Subgroup G} {y a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b)
    (hw : ∀ w ∈ ({a, b, a * b} : Set G), w ∈ N ∧ Commute w y ∧ IsConj (w * y) y) :
    ∃ V : Subgroup G, V ≤ N ∧ Nat.card V = 4 ∧ V ≤ centralizer ({y} : Set G) ∧
      ∀ v ∈ V, v ≠ 1 → IsConj (v * y) y := by
  have e1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have e2 : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
  have e3 : a * b * a = b := by rw [hab, mul_assoc, ha, mul_one]
  have e4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have e5 : a * b * (a * b) = 1 := by rw [← mul_assoc, e3, hb]
  have hab1 : a * b ≠ 1 := fun h => hne (by rw [← e4, h, one_mul])
  have haab : a ≠ a * b := fun h => hb1 (mul_eq_left.mp h.symm)
  have hbab : b ≠ a * b := fun h => ha1 (mul_eq_right.mp h.symm)
  have hwa := hw a (by simp)
  have hwb := hw b (by simp)
  have hwab := hw (a * b) (by simp)
  refine ⟨{ carrier := {1, a, b, a * b}
            mul_mem' := ?_
            one_mem' := Set.mem_insert _ _
            inv_mem' := ?_ }, ?_, ?_, ?_, ?_⟩
  · intro x z hx hz
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, one_mul, mul_one, ha, hb, e1, e2, e3,
        e4, e5, ← hab, true_or, or_true]
  · intro x hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, inv_one, inv_eq_of_mul_eq_one_right ha,
        inv_eq_of_mul_eq_one_right hb, inv_eq_of_mul_eq_one_right e5, true_or, or_true]
  · rintro x (rfl | rfl | rfl | rfl)
    exacts [N.one_mem, hwa.1, hwb.1, hwab.1]
  · change Nat.card (({1, a, b, a * b} : Set G)) = 4
    rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_pair hbab]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, haab⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
  · rintro x (rfl | rfl | rfl | rfl)
    exacts [one_mem _, mem_centralizer_singleton_iff.mpr hwa.2.1,
      mem_centralizer_singleton_iff.mpr hwb.2.1, mem_centralizer_singleton_iff.mpr hwab.2.1]
  · rintro v (rfl | rfl | rfl | rfl) hv
    exacts [absurd rfl hv, hwa.2.2, hwb.2.2, hwab.2.2]

theorem exists_four_of_isConj {N : Subgroup G} [N.Normal] {y₀ y : G} (hc : IsConj y₀ y)
    (h : ∃ V : Subgroup G, V ≤ N ∧ Nat.card V = 4 ∧ V ≤ centralizer ({y₀} : Set G) ∧
      ∀ v ∈ V, v ≠ 1 → IsConj (v * y₀) y₀) :
    ∃ V : Subgroup G, V ≤ N ∧ Nat.card V = 4 ∧ V ≤ centralizer ({y} : Set G) ∧
      ∀ v ∈ V, v ≠ 1 → IsConj (v * y) y := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hc
  obtain ⟨V, hVN, hV4, hVc, hVconj⟩ := h
  refine ⟨V.map (MulAut.conj c).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact ‹N.Normal›.conj_mem v (hVN hv) c
  · rw [card_map_of_injective (MulAut.conj c).injective, hV4]
  · rintro _ ⟨v, hv, rfl⟩
    have hcomm := mem_centralizer_singleton_iff.mp (hVc hv)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * v * c⁻¹ * (c * y₀ * c⁻¹) = c * (v * y₀) * c⁻¹ := by group
      _ = c * (y₀ * v) * c⁻¹ := by rw [hcomm]
      _ = c * y₀ * c⁻¹ * (c * v * c⁻¹) := by group
  · rintro _ ⟨v, hv, rfl⟩ hv1
    have hv1' : v ≠ 1 := by
      rintro rfl
      exact hv1 (map_one _)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (isConj_iff.mpr ⟨c⁻¹, by group⟩).trans
      ((hVconj v hv hv1').trans (isConj_iff.mpr ⟨c, rfl⟩))

theorem exists_four_map {H : Type*} [Group H] (φ : G →* H) (hφ : Function.Injective φ)
    {N : Subgroup G} {M : Subgroup H} (hNM : N.map φ ≤ M) {y : G}
    (h : ∃ V : Subgroup G, V ≤ N ∧ Nat.card V = 4 ∧ V ≤ centralizer ({y} : Set G) ∧
      ∀ v ∈ V, v ≠ 1 → IsConj (v * y) y) :
    ∃ V : Subgroup H, V ≤ M ∧ Nat.card V = 4 ∧ V ≤ centralizer ({φ y} : Set H) ∧
      ∀ v ∈ V, v ≠ 1 → IsConj (v * φ y) (φ y) := by
  obtain ⟨V, hVN, hV4, hVc, hVconj⟩ := h
  refine ⟨V.map φ, (map_mono hVN).trans hNM, by rw [card_map_of_injective hφ, hV4], ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp (hVc hv)]
  · rintro _ ⟨v, hv, rfl⟩ hv1
    rw [← map_mul]
    exact φ.map_isConj (hVconj v hv fun h1 => hv1 (by rw [h1, map_one]))

open CFSG.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusion in
theorem false_of_isolated_involution [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {d : G} (hd : orderOf d = 2)
    (hiso : ∀ y ∈ centralizer ({d} : Set G), IsConj d y → y = d) : False :=
  not_isolated_involution_of_nonabelian_simple hnonab hd fun g hg =>
    hiso _ (mem_centralizer_singleton_iff.mpr hg.eq) (isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩)

theorem false_of_fours_group [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {d : G} (hd : orderOf d = 2) {M : Subgroup G} (hdM : d ∈ M)
    (hindex : M.relIndex (centralizer ({d} : Set G)) ≤ 2) (hM : ∀ y ∈ M, IsConj d y → y = d)
    (hV : ∀ y ∈ centralizer ({d} : Set G), y ∉ M → IsConj d y → ∃ V : Subgroup G,
      Nat.card V = 4 ∧ V ≤ centralizer ({y} : Set G) ∧ ∀ v ∈ V, v ≠ 1 → IsConj (v * y) y) :
    False :=
  false_of_isolated_involution hnonab hd (fours_group_excludes_external_fusion hdM hindex hM hV)

theorem normalizer_le_centralizer_of_card_center_eq_two {L : Subgroup G}
    (hZ : Nat.card (center L) = 2) {z : L} (hzZ : z ∈ center L) (hz : z ≠ 1) :
    normalizer (L : Set G) ≤ centralizer ({(z : G)} : Set G) := by
  intro h hh
  have hw : h * z * h⁻¹ ∈ L := (mem_normalizer_iff.mp hh z).mp z.2
  have hwZ : (⟨h * z * h⁻¹, hw⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro l
    apply Subtype.ext
    have hl : h⁻¹ * l * h ∈ L := (mem_normalizer_iff''.mp hh l).mp l.2
    have hc := congrArg Subtype.val ((mem_center_iff.mp hzZ) ⟨_, hl⟩)
    simp only [coe_mul] at hc ⊢
    calc (l : G) * (h * z * h⁻¹) = h * (h⁻¹ * l * h * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * l * h)) * h⁻¹ := by rw [hc]
      _ = h * z * h⁻¹ * l := by group
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : center L)).mp hZ
  have hzy : (⟨z, hzZ⟩ : center L) = y := hy _ fun h1 => hz (congrArg Subtype.val h1)
  have hwy : (⟨⟨h * z * h⁻¹, hw⟩, hwZ⟩ : center L) = y := hy _ fun h1 => hz (by
    have h2 : h * z * h⁻¹ = 1 := congrArg (fun x : center L => ((x : L) : G)) h1
    exact Subtype.ext (by simpa using h2))
  have heq : h * z * h⁻¹ = z := congrArg (fun x : center L => ((x : L) : G)) (hwy.trans hzy.symm)
  rw [mem_centralizer_singleton_iff]
  calc h * z = h * z * h⁻¹ * h := by group
    _ = z * h := by rw [heq]

theorem centralizer_eq_normalizer_of_standard [Finite G] {L : Subgroup G}
    (hL : standardComponentIsStandard L) (hZ : Nat.card (center L) = 2) {z : L}
    (hzZ : z ∈ center L) (hz : orderOf (z : G) = 2) :
    centralizer ({(z : G)} : Set G) = normalizer (L : Set G) :=
  le_antisymm (centralizer_le_normalizer_of_standard hL (mem_centralizer_of_mem_center hzZ) hz)
    (normalizer_le_centralizer_of_card_center_eq_two hZ hzZ fun h => by simp [h] at hz)

theorem mem_of_sq_eq_one_of_mem_sup_centralizer [Finite G] {L : Subgroup G}
    (hK : IsCyclic (centralizer (L : Set G))) (hZ : Even (Nat.card (center L)))
    (hsq : ∀ a : L, a ^ 2 ∈ center L → a ^ 2 = 1) {x : G}
    (hx : x ∈ L ⊔ centralizer (L : Set G)) (hx2 : x ^ 2 = 1) : x ∈ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left L _
    (centralizer_le_normalizer _)] at hx
  obtain ⟨a, ha, k, hk, rfl⟩ := hx
  have hak : Commute a k := mem_centralizer_iff.mp hk a ha
  have hprod : a ^ 2 * k ^ 2 = 1 := by rwa [← hak.mul_pow]
  have ha2 : a ^ 2 = 1 := by
    have hmem : a ^ 2 ∈ centralizer (L : Set G) := by
      rw [eq_inv_of_mul_eq_one_left hprod]
      exact inv_mem (pow_mem hk 2)
    have hcen : (⟨a, ha⟩ : L) ^ 2 ∈ center L := by
      rw [mem_center_iff]
      intro l
      exact Subtype.ext (by simpa using mem_centralizer_iff.mp hmem l l.2)
    simpa using congrArg Subtype.val (hsq ⟨a, ha⟩ hcen)
  have hk2 : k ^ 2 = 1 := by rwa [ha2, one_mul] at hprod
  refine mul_mem ha ?_
  by_cases hk1 : k = 1
  · exact hk1 ▸ one_mem L
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hZ)
  have hzK : ((z : L) : G) ∈ centralizer (L : Set G) := mem_centralizer_of_mem_center z.2
  have hzpow : zpowers (⟨k, hk⟩ : centralizer (L : Set G)) = zpowers ⟨_, hzK⟩ := by
    refine IsCyclic.subgroup_eq_iff_card_eq.mpr ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_mk, orderOf_mk, orderOf_coe, orderOf_coe, hz,
      orderOf_eq_prime hk2 hk1]
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hzpow ▸ mem_zpowers (⟨k, hk⟩ : centralizer (L : Set G)))
  have hkn : ((z : L) : G) ^ n = k := congrArg Subtype.val hn
  exact hkn ▸ zpow_mem (z : L).2 n

end CFSG.EvenSmallLie
