module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterCount
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterTwoGroup
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter

namespace OuterSetting

variable {X : Type*} [Group X] {J P : Subgroup X} [J.Normal] {zb : X} {q : ℕ}
  (hS : OuterSetting X J P zb q)
@[expose] def cosetSubgroup (T : Subgroup X) (w₁ : X) (hn : ∀ t ∈ T, w₁ * t * w₁⁻¹ ∈ T)
    (hn' : ∀ t ∈ T, w₁⁻¹ * t * w₁ ∈ T) (hsq : w₁ ^ 2 ∈ T) : Subgroup X where
  carrier := {g | g ∈ T ∨ g * w₁⁻¹ ∈ T}
  one_mem' := Or.inl T.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (T.mul_mem ha hb)
    · exact Or.inr (by simpa [mul_assoc] using T.mul_mem ha hb)
    · refine Or.inr ?_
      have h := T.mul_mem ha (hn b hb)
      simpa [mul_assoc] using h
    · refine Or.inl ?_
      have h := T.mul_mem (T.mul_mem ha (hn _ hb)) hsq
      have heq : a * w₁⁻¹ * (w₁ * (b * w₁⁻¹) * w₁⁻¹) * w₁ ^ 2 = a * b := by
        rw [pow_two]; group
      rwa [heq] at h
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (T.inv_mem ha)
    · refine Or.inr ?_
      have h := T.mul_mem (hn' _ (T.inv_mem ha)) (T.inv_mem hsq)
      have heq : w₁⁻¹ * (a * w₁⁻¹)⁻¹ * w₁ * (w₁ ^ 2)⁻¹ = a⁻¹ * w₁⁻¹ := by
        rw [pow_two]; group
      rwa [heq] at h

include hS in
theorem torus_root_counts_ne [Finite X] {w₁ : X} (hw₁ : w₁ ∈ P) (hw₁RT : ¬ InRT P J w₁)
    (hw₁2 : w₁ ^ 2 ∈ torusT P J) {q' : ℕ} (hq' : 0 < q') :
    Nat.card {t : X // t ∈ torusT P J ∧ t ^ 2 = zb} ≠
        Nat.card {t : X // t ∈ torusT P J ∧ (t * w₁) ^ 2 = zb} ∧
      Nat.card {t : X // t ∈ torusT P J ∧ t ^ 2 = zb} +
          q' * Nat.card {t : X // t ∈ torusT P J ∧ (t * w₁) ^ 2 = zb} ≠ 2 * q' + 2 := by
  set T := torusT P J with hTdef
  have hzbT : zb ∈ T := ⟨hS.zb_mem, hS.zb_mem_centralizer⟩
  have hn : ∀ t ∈ T, w₁ * t * w₁⁻¹ ∈ T := fun t ht =>
    ⟨P.mul_mem (P.mul_mem hw₁ ht.1) (P.inv_mem hw₁), conj_mem_centralizer w₁ ht.2⟩
  have hn' : ∀ t ∈ T, w₁⁻¹ * t * w₁ ∈ T := fun t ht => by
    have h := conj_mem_centralizer w₁⁻¹ ht.2
    rw [inv_inv] at h
    exact ⟨P.mul_mem (P.mul_mem (P.inv_mem hw₁) ht.1) hw₁, h⟩
  set Qs := cosetSubgroup T w₁ hn hn' hw₁2 with hQs
  have hw₁T : w₁ ∉ T := fun h => hw₁RT ⟨1, Subgroup.one_mem _, w₁, h, by rw [one_mul]⟩
  have hQP : Qs ≤ P := by
    rintro g (hg | hg)
    · exact hg.1
    · simpa using P.mul_mem hg.1 hw₁
  have hQ : IsPGroup 2 Qs := hS.isPGroup.to_le hQP
  set z' : Qs := ⟨zb, Or.inl hzbT⟩
  have hzb1 : zb ≠ 1 := fun h => hS.zb_not_mem (h ▸ J.one_mem)
  have hz' : orderOf z' = 2 := by
    refine orderOf_eq_prime (Subtype.ext hS.zb_sq) (fun h => hzb1 (congrArg Subtype.val h))
  have hout : ∀ g : X, g * w₁⁻¹ ∈ T → g ^ 2 = 1 → g ≠ 1 → False := by
    intro g hg hg2 hg1
    have hgP : g ∈ P := by simpa using P.mul_mem hg.1 hw₁
    have hc : ∀ y ∈ J, y * (g * w₁⁻¹)⁻¹ = (g * w₁⁻¹)⁻¹ * y := fun y hy =>
      commute_root_torus hy (Subgroup.inv_mem _ hg)
    rcases hS.involution g hg2 hg1 with hgJ | hgJ
    · refine hw₁RT ⟨g, ⟨hgP, hgJ⟩, (g * w₁⁻¹)⁻¹, Subgroup.inv_mem _ hg, ?_⟩
      rw [hc g hgJ]
      group
    · refine hw₁RT ⟨zb * g, ⟨P.mul_mem hS.zb_mem hgP, hgJ⟩, (g * w₁⁻¹)⁻¹ * zb,
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hzbT, ?_⟩
      have hzz : zb * zb = 1 := by rw [← pow_two]; exact hS.zb_sq
      calc w₁ = (g * w₁⁻¹)⁻¹ * g := by group
        _ = (g * w₁⁻¹)⁻¹ * (zb * zb) * g := by rw [hzz, mul_one]
        _ = (g * w₁⁻¹)⁻¹ * zb * (zb * g) := by group
        _ = zb * ((g * w₁⁻¹)⁻¹ * (zb * g)) := by rw [hS.zb_central, mul_assoc]
        _ = zb * ((zb * g) * (g * w₁⁻¹)⁻¹) := by rw [hc _ hgJ]
        _ = zb * g * ((g * w₁⁻¹)⁻¹ * zb) := by rw [← hS.zb_central]; group
  have huniq : ∀ g : Qs, g ^ 2 = 1 → g = 1 ∨ g = z' := by
    intro g hg
    have hg2 : (g : X) ^ 2 = 1 := by simpa using congrArg Subtype.val hg
    by_cases hg1 : (g : X) = 1
    · exact Or.inl (Subtype.ext hg1)
    rcases g.2 with hgT | hgT
    · rcases hS.eq_one_or_eq_zb hgT hg2 with h | h
      · exact absurd h hg1
      · exact Or.inr (Subtype.ext h)
    · exact (hout _ hgT hg2 hg1).elim
  set T' := T.subgroupOf Qs
  have hT' : T'.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨w₁, Or.inr (by rw [mul_inv_cancel]; exact T.one_mem)⟩,
      fun h => hw₁T (Subgroup.mem_subgroupOf.mp h), fun b => ?_⟩
    rcases b.2 with hb | hb
    · exact Or.inr (Subgroup.mem_subgroupOf.mpr hb)
    · refine Or.inl (Subgroup.mem_subgroupOf.mpr ?_)
      have h := T.mul_mem hb hw₁2
      have heq : (b : X) * w₁⁻¹ * w₁ ^ 2 = b * w₁ := by rw [pow_two]; group
      rwa [heq] at h
  obtain ⟨h₁, h₂⟩ := root_counts_ne hQ hz' huniq hT' (Subgroup.mem_subgroupOf.mpr hzbT) hq'
  have e₀ : Nat.card {t : Qs // t ∈ T' ∧ t ^ 2 = z'} =
      Nat.card {t : X // t ∈ T ∧ t ^ 2 = zb} :=
    Nat.card_congr
      { toFun := fun t => ⟨t.1, Subgroup.mem_subgroupOf.mp t.2.1, by
          simpa using congrArg Subtype.val t.2.2⟩
        invFun := fun t => ⟨⟨t.1, Or.inl t.2.1⟩, Subgroup.mem_subgroupOf.mpr t.2.1,
          Subtype.ext (by simpa using t.2.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have e₁ : Nat.card {w : Qs // w ∉ T' ∧ w ^ 2 = z'} =
      Nat.card {t : X // t ∈ T ∧ (t * w₁) ^ 2 = zb} :=
    Nat.card_congr
      { toFun := fun w => ⟨w.1.1 * w₁⁻¹,
          (w.1.2.resolve_left fun h => w.2.1 (Subgroup.mem_subgroupOf.mpr h)), by
          rw [inv_mul_cancel_right]
          simpa using congrArg Subtype.val w.2.2⟩
        invFun := fun t => ⟨⟨t.1 * w₁, Or.inr (by rw [mul_inv_cancel_right]; exact t.2.1)⟩,
          fun h => hw₁T (by
            have h' := T.mul_mem (T.inv_mem t.2.1) (Subgroup.mem_subgroupOf.mp h)
            rwa [inv_mul_cancel_left] at h'),
          Subtype.ext (by simpa using t.2.2)⟩
        left_inv := fun w => Subtype.ext (Subtype.ext (by simp))
        right_inv := fun t => Subtype.ext (by simp) }
  rw [e₀, e₁] at h₁ h₂
  exact ⟨h₁, h₂⟩

include hS in
theorem false_of_card_sq [Finite X] {s : X} (hs : s ∈ P) (hsRT : ¬ InRT P J s) {u : X}
    (hu : u ∈ P ⊓ J) (hu1 : u ≠ 1) (hu2 : u ^ 2 = 1)
    (hcount : Nat.card {w : X // w ∈ P ∧ w ^ 2 = zb} = Nat.card {w : X // w ∈ P ∧ w ^ 2 = u} ∨
      Nat.card {w : X // w ∈ P ∧ w ^ 2 = zb} =
        Nat.card {w : X // w ∈ P ∧ w ^ 2 = u * zb}) : False := by
  obtain ⟨w₁, hw₁, hw₁RT, hw₁2⟩ := hS.exists_outer_sq_mem_torus hs hsRT
  have hq : 0 < q := by have := hS.model.four_le; omega
  have hzbT : zb ∈ torusT P J := ⟨hS.zb_mem, hS.zb_mem_centralizer⟩
  obtain ⟨h₁, h₂⟩ := hS.torus_root_counts_ne hw₁ hw₁RT hw₁2 hq
  have hout0 : ∀ y, (y = u ∨ y = u * zb) →
      Nat.card {w : X // w ∈ P ∧ ¬ InRT P J w ∧ w ^ 2 = y} = 0 := by
    intro y hy
    rw [Nat.card_eq_zero]
    left
    exact ⟨fun w => hS.false_of_sq_eq w.2.1 w.2.2.1 hu hu1 hu2
      (by rcases hy with rfl | rfl <;> simp [w.2.2.2])⟩
  have hnz : Nat.card {w : X // w ∈ P ∧ w ^ 2 = zb} =
      q * Nat.card {t : X // t ∈ torusT P J ∧ t ^ 2 = zb} +
        q ^ 2 * Nat.card {t : X // t ∈ torusT P J ∧ (t * w₁) ^ 2 = zb} := by
    have hin := hS.card_inRT_sq (a := 1) (b := zb) (Subgroup.one_mem _) hzbT
    rw [one_mul, hS.card_sq_one_root] at hin
    rw [card_sq_split, hin, hS.card_outer_sq_zb hw₁ hw₁RT hw₁2,
      hS.card_twist_root hw₁ hw₁RT hw₁2]
  have hnu : Nat.card {w : X // w ∈ P ∧ w ^ 2 = u} = q * (q + 1) * 2 := by
    have hin := hS.card_inRT_sq (a := u) (b := 1) hu (Subgroup.one_mem _)
    rw [mul_one, hS.card_sq_root hu hu1 hu2, hS.card_torus_sq_one] at hin
    rw [card_sq_split, hin, hout0 u (Or.inl rfl), add_zero]
  have hnuz : Nat.card {w : X // w ∈ P ∧ w ^ 2 = u * zb} =
      q * (q + 1) * Nat.card {t : X // t ∈ torusT P J ∧ t ^ 2 = zb} := by
    have hin := hS.card_inRT_sq (a := u) (b := zb) hu hzbT
    rw [hS.card_sq_root hu hu1 hu2] at hin
    rw [card_sq_split, hin, hout0 (u * zb) (Or.inr rfl), add_zero]
  set N₀ := Nat.card {t : X // t ∈ torusT P J ∧ t ^ 2 = zb}
  set N₁ := Nat.card {t : X // t ∈ torusT P J ∧ (t * w₁) ^ 2 = zb}
  rcases hcount with h | h
  · rw [hnz, hnu] at h
    apply h₂
    have h' : q * (N₀ + q * N₁) = q * (2 * q + 2) := by
      calc q * (N₀ + q * N₁) = q * N₀ + q ^ 2 * N₁ := by ring
        _ = q * (q + 1) * 2 := h
        _ = q * (2 * q + 2) := by ring
    exact Nat.eq_of_mul_eq_mul_left hq h'
  · rw [hnz, hnuz] at h
    apply h₁
    have h' : q * N₀ + q ^ 2 * N₁ = q * N₀ + q ^ 2 * N₀ := by rw [h]; ring
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) (Nat.add_left_cancel h')).symm

end OuterSetting

end CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter
