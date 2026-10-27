module

public import CFSG.LargeExtraspecial.AS62Conf2
public import CFSG.LargeExtraspecial.AS62Sem

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Asc77 CFSG.RankThree.OrthogonalInvolutions
open scoped IsMulCommutative

namespace AS62

section Klein

variable {K : Type*} [Group K]

theorem mul_mul_self_of_commute {a b : K} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : a * b * (a * b) = 1 := by
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * a * (b * b) := by rw [← hab]; group
    _ = 1 := by rw [ha, hb, one_mul]

@[expose] def kleinSub (a b : K) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    Subgroup K where
  carrier := {1, a, b, a * b}
  one_mem' := Set.mem_insert _ _
  mul_mem' := by
    have h_aab : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have h_bab : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
    have h_aba : a * b * a = b := by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul]
    have h_abb : a * b * b = a := by rw [mul_assoc, hb, mul_one]
    have h_abab : a * b * (a * b) = 1 := mul_mul_self_of_commute ha hb hab
    rintro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [one_mul, mul_one, ha, hb, h_aab, h_bab, h_aba, h_abb, h_abab, ← hab,
        true_or, or_true]
  inv_mem' := by
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · simp [hai]
    · simp [hbi]
    · rw [mul_inv_rev, hai, hbi, ← hab]
      simp

theorem mem_kleinSub {a b : K} {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a} {x : K} :
    x ∈ kleinSub a b ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := Iff.rfl

theorem card_kleinSub {a b : K} {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a}
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : Nat.card (kleinSub a b ha hb hab) = 4 := by
  have hab1 : a * b ≠ 1 := fun h => hne (by
    calc a = a * (b * b) := by rw [hb, mul_one]
      _ = b := by rw [← mul_assoc, h, one_mul])
  have haba : a * b ≠ a := fun h => hb1 (by
    calc b = a⁻¹ * (a * b) := by group
      _ = 1 := by rw [h, inv_mul_cancel])
  have habb : a * b ≠ b := fun h => ha1 (by
    calc a = a * b * b⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel])
  change Nat.card (({1, a, b, a * b} : Set K) : Type _) = 4
  rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hb1, Ne.symm hab1⟩),
    Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, Ne.symm haba⟩),
    Set.ncard_pair (Ne.symm habb)]

end Klein

@[expose] def kleinLabels : Subgroup (Equiv.Perm (Fin 5)) :=
  kleinSub (Equiv.swap 1 2 * Equiv.swap 3 4) (Equiv.swap 1 3 * Equiv.swap 2 4) (by decide)
    (by decide) (by decide)

theorem card_kleinLabels : Nat.card kleinLabels = 4 :=
  card_kleinSub (by decide) (by decide) (by decide)

theorem kleinLabels_le : kleinLabels ≤ alternatingGroup (Fin 5) := by
  intro p hp
  rw [Equiv.Perm.mem_alternatingGroup]
  rcases mem_kleinSub.mp hp with rfl | rfl | rfl | rfl <;> decide

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_self_of_conj (S : Setting G) {q b : G} (hq : q ∈ S.QG) (hb : b ∈ S.QG)
    (hbb : b * b = 1) (hqb : q * b * q⁻¹ = S.z * b) :
    ∃ c : G, (c = 1 ∨ c = b) ∧ q * c * (q * c) = 1 := by
  rcases S.sq_eq_one_or_z hq with h | h <;> rw [pow_two] at h
  · exact ⟨1, Or.inl rfl, by rw [mul_one, h]⟩
  · refine ⟨b, Or.inr rfl, ?_⟩
    have hbz : b * S.z = S.z * b := S.z_comm_QG hb
    calc q * b * (q * b) = q * b * q⁻¹ * (q * q) * b := by group
      _ = S.z * b * S.z * b := by rw [hqb, h]
      _ = S.z * S.z * (b * b) := by rw [mul_assoc S.z b S.z, hbz]; group
      _ = 1 := by rw [S.z_mul_z, hbb, one_mul]

omit [Finite G] in
theorem exists_commute_of_conj (S : Setting G) {e₁ e₂ b : G} (h₁ : e₁ ∈ S.QG) (h₂ : e₂ ∈ S.QG)
    (h₁₁ : e₁ * e₁ = 1) (hbb : b * b = 1) (h₁b : e₁ * b = b * e₁)
    (h₂b : e₂ * b * e₂⁻¹ = S.z * b) :
    ∃ c : G, (c = 1 ∨ c = b) ∧ e₁ * c * (e₁ * c) = 1 ∧ e₁ * c * e₂ = e₂ * (e₁ * c) := by
  rcases S.mul_comm_or h₁ h₂ with h | h
  · exact ⟨1, Or.inl rfl, by rw [mul_one, h₁₁], by rw [mul_one, h]⟩
  · refine ⟨b, Or.inr rfl, mul_mul_self_of_commute h₁₁ hbb h₁b, ?_⟩
    have hzb : e₂ * b = S.z * b * e₂ := by
      calc e₂ * b = e₂ * b * e₂⁻¹ * e₂ := by group
        _ = S.z * b * e₂ := by rw [h₂b]
    have hbe : b * e₂ = S.z * (e₂ * b) := by
      calc b * e₂ = S.z * S.z * b * e₂ := by rw [S.z_mul_z, one_mul]
        _ = S.z * (S.z * b * e₂) := by group
        _ = S.z * (e₂ * b) := by rw [hzb]
    have hz₁ : e₁ * S.z = S.z * e₁ := S.z_comm_QG h₁
    calc e₁ * b * e₂ = e₁ * (b * e₂) := mul_assoc _ _ _
      _ = e₁ * (S.z * (e₂ * b)) := by rw [hbe]
      _ = e₁ * S.z * e₂ * b := by group
      _ = S.z * (e₁ * e₂) * b := by rw [hz₁]; group
      _ = S.z * (S.z * (e₂ * e₁)) * b := by rw [h]
      _ = S.z * S.z * (e₂ * (e₁ * b)) := by group
      _ = e₂ * (e₁ * b) := by rw [S.z_mul_z, one_mul]

namespace Label

variable {S : Setting G} {H : Subgroup G} (L : Label S H)

theorem zz_two_mul_zz_four (hc : ConfHyp S H) : L.zz 2 * L.zz 4 = S.z * (L.zz 1 * L.zz 3) := by
  have : IsMulCommutative (closure (S.zConj H)) :=
    isMulCommutative_closure fun x hx y hy _ => hc.commute_zConj hx hy
  let f : Fin 5 → closure (S.zConj H) := fun i => ⟨L.zz i, subset_closure (L.zz_mem i)⟩
  have hsq : ∀ i, f i * f i = 1 := fun i => Subtype.ext (L.zz_mul_self i)
  have hp : f 0 * f 1 * f 2 * f 3 * f 4 = 1 := Subtype.ext (L.prod_zz hc)
  have hY : f 2 * f 4 * (f 2 * f 4) = 1 := by rw [mul_mul_mul_comm, hsq, hsq, one_mul]
  have hXY : f 0 * (f 1 * f 3) * (f 2 * f 4) = 1 := by rw [← hp]; ac_rfl
  have key : f 2 * f 4 = f 0 * (f 1 * f 3) := by
    calc f 2 * f 4 = 1 * (f 2 * f 4) := (one_mul _).symm
      _ = f 0 * (f 1 * f 3) * (f 2 * f 4) * (f 2 * f 4) := by rw [hXY]
      _ = f 0 * (f 1 * f 3) := by rw [mul_assoc (f 0 * (f 1 * f 3)), hY, mul_one]
  rw [← L.zz_zero]
  exact congrArg Subtype.val key

theorem zz_three_mul_zz_four (hc : ConfHyp S H) :
    L.zz 3 * L.zz 4 = S.z * (L.zz 1 * L.zz 2) := by
  have : IsMulCommutative (closure (S.zConj H)) :=
    isMulCommutative_closure fun x hx y hy _ => hc.commute_zConj hx hy
  let f : Fin 5 → closure (S.zConj H) := fun i => ⟨L.zz i, subset_closure (L.zz_mem i)⟩
  have hsq : ∀ i, f i * f i = 1 := fun i => Subtype.ext (L.zz_mul_self i)
  have hp : f 0 * f 1 * f 2 * f 3 * f 4 = 1 := Subtype.ext (L.prod_zz hc)
  have hY : f 3 * f 4 * (f 3 * f 4) = 1 := by rw [mul_mul_mul_comm, hsq, hsq, one_mul]
  have hXY : f 0 * (f 1 * f 2) * (f 3 * f 4) = 1 := by rw [← hp]; ac_rfl
  have key : f 3 * f 4 = f 0 * (f 1 * f 2) := by
    calc f 3 * f 4 = 1 * (f 3 * f 4) := (one_mul _).symm
      _ = f 0 * (f 1 * f 2) * (f 3 * f 4) * (f 3 * f 4) := by rw [hXY]
      _ = f 0 * (f 1 * f 2) := by rw [mul_assoc (f 0 * (f 1 * f 2)), hY, mul_one]
  rw [← L.zz_zero]
  exact congrArg Subtype.val key

omit [Finite G] in
theorem conj_zz_mul (h : H) (i j : Fin 5) :
    (h : G) * (L.zz i * L.zz j) * (h : G)⁻¹ = L.zz (L.σ h i) * L.zz (L.σ h j) := by
  rw [← L.conj_zz, ← L.conj_zz]
  group

theorem exists_klein_pair (hc : ConfHyp S H) :
    ∃ e₁ e₂ : H, (e₁ : G) ∈ S.QG ∧ (e₂ : G) ∈ S.QG ∧
      L.σ e₁ = Equiv.swap 1 2 * Equiv.swap 3 4 ∧ L.σ e₂ = Equiv.swap 1 3 * Equiv.swap 2 4 ∧
      (e₁ : G) * e₁ = 1 ∧ (e₂ : G) * e₂ = 1 ∧ (e₁ : G) * e₂ = e₂ * e₁ := by
  have hV : ∀ i : Fin 5, L.zz i ∈ closure (S.zConj H) := fun i => subset_closure (L.zz_mem i)
  have hσV : ∀ (c : G) (hcV : c ∈ closure (S.zConj H)), L.σ ⟨c, hc.V_le hcV⟩ = 1 :=
    fun c hcV => (L.σ_eq_one_iff hc _).mpr hcV
  have hzz : ∀ i j : Fin 5, L.zz i * L.zz j * (L.zz i * L.zz j) = 1 := fun i j =>
    mul_mul_self_of_commute (L.zz_mul_self i) (L.zz_mul_self j)
      (hc.commute_zConj (L.zz_mem i) (L.zz_mem j))
  have hQ : ∀ i j : Fin 5, i ≠ 0 → j ≠ 0 → L.zz i * L.zz j ∈ S.QG := fun i j hi hj =>
    hc.mul_mem_QG (L.zz_mem i) (L.zz_ne_z hi) (L.zz_mem j) (L.zz_ne_z hj)
  have hb₁Q := hQ 1 3 (by decide) (by decide)
  have hb₂Q := hQ 1 2 (by decide) (by decide)
  have hcorr : ∀ (i j : Fin 5) (c : G), i ≠ 0 → j ≠ 0 → (c = 1 ∨ c = L.zz i * L.zz j) →
      c ∈ S.QG ∧ c ∈ closure (S.zConj H) := by
    rintro i j c hi hj (rfl | rfl)
    · exact ⟨one_mem _, one_mem _⟩
    · exact ⟨hQ i j hi hj, mul_mem (hV i) (hV j)⟩
  obtain ⟨q₁, hq₁, hσ₁⟩ := L.exists_σ_eq_klein₁ hc
  obtain ⟨q₂, hq₂, hσ₂⟩ := L.exists_σ_eq_klein₂ hc
  have h₁ : (q₁ : G) * (L.zz 1 * L.zz 3) * (q₁ : G)⁻¹ = S.z * (L.zz 1 * L.zz 3) := by
    rw [L.conj_zz_mul, hσ₁, ← L.zz_two_mul_zz_four hc]
    rfl
  have h₂ : (q₂ : G) * (L.zz 1 * L.zz 2) * (q₂ : G)⁻¹ = S.z * (L.zz 1 * L.zz 2) := by
    rw [L.conj_zz_mul, hσ₂, ← L.zz_three_mul_zz_four hc]
    rfl
  obtain ⟨c₁, hc₁, hc₁sq⟩ := exists_mul_self_of_conj S hq₁ hb₁Q (hzz 1 3) h₁
  obtain ⟨c₂, hc₂, hc₂sq⟩ := exists_mul_self_of_conj S hq₂ hb₂Q (hzz 1 2) h₂
  obtain ⟨hc₁Q, hc₁V⟩ := hcorr 1 3 c₁ (by decide) (by decide) hc₁
  obtain ⟨hc₂Q, hc₂V⟩ := hcorr 1 2 c₂ (by decide) (by decide) hc₂
  set f₁ : H := q₁ * ⟨c₁, hc.V_le hc₁V⟩
  set f₂ : H := q₂ * ⟨c₂, hc.V_le hc₂V⟩
  have hσf₁ : L.σ f₁ = Equiv.swap 1 2 * Equiv.swap 3 4 := by
    rw [map_mul, hσ₁, hσV c₁ hc₁V, mul_one]
  have hσf₂ : L.σ f₂ = Equiv.swap 1 3 * Equiv.swap 2 4 := by
    rw [map_mul, hσ₂, hσV c₂ hc₂V, mul_one]
  have hf₁Q : (f₁ : G) ∈ S.QG := S.QG.mul_mem hq₁ hc₁Q
  have hf₂Q : (f₂ : G) ∈ S.QG := S.QG.mul_mem hq₂ hc₂Q
  have hf₁b : (f₁ : G) * (L.zz 1 * L.zz 2) = L.zz 1 * L.zz 2 * f₁ := by
    have e := L.conj_zz_mul f₁ 1 2
    rw [hσf₁] at e
    change (f₁ : G) * (L.zz 1 * L.zz 2) * (f₁ : G)⁻¹ = L.zz 2 * L.zz 1 at e
    rw [← hc.commute_zConj (L.zz_mem 1) (L.zz_mem 2)] at e
    calc (f₁ : G) * (L.zz 1 * L.zz 2) = f₁ * (L.zz 1 * L.zz 2) * (f₁ : G)⁻¹ * f₁ := by group
      _ = L.zz 1 * L.zz 2 * f₁ := by rw [e]
  have hf₂b : (f₂ : G) * (L.zz 1 * L.zz 2) * (f₂ : G)⁻¹ = S.z * (L.zz 1 * L.zz 2) := by
    rw [L.conj_zz_mul, hσf₂, ← L.zz_three_mul_zz_four hc]
    rfl
  obtain ⟨c₃, hc₃, hc₃sq, hc₃comm⟩ :=
    exists_commute_of_conj S hf₁Q hf₂Q hc₁sq (hzz 1 2) hf₁b hf₂b
  obtain ⟨hc₃Q, hc₃V⟩ := hcorr 1 2 c₃ (by decide) (by decide) hc₃
  refine ⟨f₁ * ⟨c₃, hc.V_le hc₃V⟩, f₂, S.QG.mul_mem hf₁Q hc₃Q, hf₂Q, ?_, hσf₂, hc₃sq, hc₂sq,
    hc₃comm⟩
  rw [map_mul, hσf₁, hσV c₃ hc₃V, mul_one]

end Label

namespace ConfHyp

variable {S : Setting G} {H : Subgroup G}

theorem exists_complement (hc : ConfHyp S H) :
    ∃ A : Subgroup G, A ≤ H ∧ closure (S.zConj H) ⊓ A = ⊥ ∧ closure (S.zConj H) ⊔ A = H := by
  obtain ⟨p, hp, hpz⟩ :=
    Set.exists_ne_of_one_lt_ncard (by rw [hc.ncard_zConj]; norm_num) S.z
  obtain ⟨L, -⟩ := hc.exists_label hp hpz
  obtain ⟨e₁, e₂, -, -, hσ₁, hσ₂, h₁₁, h₂₂, h₁₂⟩ := L.exists_klein_pair hc
  have h₁₁' : e₁ * e₁ = 1 := Subtype.ext h₁₁
  have h₂₂' : e₂ * e₂ = 1 := Subtype.ext h₂₂
  have h₁₂' : e₁ * e₂ = e₂ * e₁ := Subtype.ext h₁₂
  set E := kleinSub e₁ e₂ h₁₁' h₂₂' h₁₂' with hE
  set T := kleinLabels.comap L.σ with hT
  have : IsMulCommutative L.σ.ker := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (hc.commute_V ((L.σ_eq_one_iff hc a).mp a.2) ((L.σ_eq_one_iff hc b).mp b.2)))⟩⟩
  have hσE : ∀ x ∈ E, L.σ x ∈ kleinLabels := by
    intro x hx
    refine mem_kleinSub.mpr ?_
    rcases mem_kleinSub.mp hx with rfl | rfl | rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr (Or.inl hσ₁)
    · exact Or.inr (Or.inr (Or.inl hσ₂))
    · exact Or.inr (Or.inr (Or.inr (by rw [map_mul, hσ₁, hσ₂])))
  have hNE : L.σ.ker ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxN, hxE⟩ := mem_inf.mp hx
    rw [MonoidHom.mem_ker] at hxN
    rw [mem_bot]
    rcases mem_kleinSub.mp hxE with h | h | h | h
    · exact h
    · rw [h, hσ₁] at hxN
      exact absurd hxN (by decide)
    · rw [h, hσ₂] at hxN
      exact absurd hxN (by decide)
    · rw [h, map_mul, hσ₁, hσ₂] at hxN
      exact absurd hxN (by decide)
  have hsup : L.σ.ker ⊔ E = T := by
    apply le_antisymm
    · refine sup_le (fun x hx => ?_) (fun x hx => mem_comap.mpr (hσE x hx))
      rw [mem_comap, MonoidHom.mem_ker.mp hx]
      exact one_mem _
    · intro h hh
      obtain ⟨e, heE, he⟩ : ∃ e ∈ E, L.σ e = L.σ h := by
        rcases mem_kleinSub.mp (mem_comap.mp hh) with h' | h' | h' | h'
        · exact ⟨1, one_mem _, by rw [map_one, h']⟩
        · exact ⟨e₁, mem_kleinSub.mpr (Or.inr (Or.inl rfl)), by rw [hσ₁, h']⟩
        · exact ⟨e₂, mem_kleinSub.mpr (Or.inr (Or.inr (Or.inl rfl))), by rw [hσ₂, h']⟩
        · exact ⟨e₁ * e₂, mem_kleinSub.mpr (Or.inr (Or.inr (Or.inr rfl))),
            by rw [map_mul, hσ₁, hσ₂, h']⟩
      have hN : h * e⁻¹ ∈ L.σ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
      rw [show h = h * e⁻¹ * e by group]
      exact mul_mem (mem_sup_left hN) (mem_sup_right heE)
  have hcard : Nat.card L.σ.ker = 16 := by
    rw [L.ker_σ hc, Nat.card_congr (subgroupOfEquivOfLe hc.V_le).toEquiv, hc.card_V]
  have hindex : T.index = 15 := by
    rw [hT, Subgroup.index_comap, L.range_σ hc.isAFive]
    have h := Subgroup.relIndex_mul_relIndex ⊥ kleinLabels (alternatingGroup (Fin 5)) bot_le
      kleinLabels_le
    rw [relIndex_bot_left, relIndex_bot_left, card_kleinLabels, card_alternatingGroup_five] at h
    omega
  have hcop : Nat.Coprime T.index (Nat.card L.σ.ker) := by
    rw [hindex, hcard]
    norm_num
  obtain ⟨D, -, hND, hNDtop⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting L.σ.ker T E hcop hNE hsup
  have hNV : L.σ.ker.map H.subtype = closure (S.zConj H) := by
    rw [L.ker_σ hc, subgroupOf_map_subtype, inf_eq_left.mpr hc.V_le]
  refine ⟨D.map H.subtype, map_subtype_le D, ?_, ?_⟩
  · rw [← hNV, ← map_inf_eq _ _ _ H.subtype_injective, hND, Subgroup.map_bot]
  · rw [← hNV, ← Subgroup.map_sup, hNDtop, ← MonoidHom.range_eq_map, range_subtype]


theorem exists_frame (hc : ConfHyp S H) (L : Label S H) :
    ∃ F : Frame G, F.H = H ∧ F.V = closure (S.zConj H) ∧ F.zz = L.zz := by
  obtain ⟨A, hAH, hVA, hVAH⟩ := hc.exists_complement
  have hrange : Set.range L.zz = S.zConj H := by
    ext x
    exact ⟨fun ⟨i, hi⟩ => hi ▸ L.zz_mem i, fun hx => L.exists_zz_eq hx⟩
  have hNV : L.σ.ker.map H.subtype = closure (S.zConj H) := by
    rw [L.ker_σ hc, subgroupOf_map_subtype, inf_eq_left.mpr hc.V_le]
  have htop : L.σ.ker ⊔ A.subgroupOf H = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, hNV, subgroupOf_map_subtype, inf_eq_left.mpr hAH, hVAH,
      ← MonoidHom.range_eq_map, range_subtype]
  refine ⟨⟨H, closure (S.zConj H), A, L.zz, ?_, L.zz_mul_self,
    fun i j => hc.commute_zConj (L.zz_mem i) (L.zz_mem j), L.prod_zz hc, hc.card_V, hVA, hVAH,
    L.σ.comp (inclusion hAH), fun a i => L.conj_zz (inclusion hAH a) i, ?_, ?_⟩, rfl, rfl, rfl⟩
  · rw [hrange]
  · refine (injective_iff_map_eq_one _).mpr fun a ha => Subtype.ext ?_
    have h1 : (a : G) ∈ closure (S.zConj H) := (L.σ_eq_one_iff hc (inclusion hAH a)).mp ha
    have h2 : (a : G) ∈ closure (S.zConj H) ⊓ A := mem_inf.mpr ⟨h1, a.2⟩
    rw [hVA, mem_bot] at h2
    exact h2
  · ext p
    rw [Equiv.Perm.mem_alternatingGroup]
    constructor
    · rintro ⟨a, rfl⟩
      exact L.sign_σ hc.isAFive _
    · intro hp
      obtain ⟨h, rfl⟩ := L.exists_σ_eq hc.isAFive hp
      have hh : h ∈ ((L.σ.ker ⊔ A.subgroupOf H : Subgroup H) : Set H) := by
        rw [htop]
        exact mem_top h
      rw [normal_mul] at hh
      obtain ⟨n, hn, y, hy, rfl⟩ := Set.mem_mul.mp hh
      refine ⟨⟨y, mem_subgroupOf.mp hy⟩, ?_⟩
      change L.σ (inclusion hAH ⟨y, mem_subgroupOf.mp hy⟩) = L.σ (n * y)
      rw [map_mul, MonoidHom.mem_ker.mp hn, one_mul]
      rfl

end ConfHyp

end AS62

end CFSG.LargeExtraspecial
