module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup

variable {G : Type*} [Group G]

theorem exists_comm_mem_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {P U V : Subgroup G}
    (hP : IsPGroup p P) (hVP : V ≤ P) (hU : ∀ x ∈ P, ∀ u ∈ U, x * u * x⁻¹ ∈ U)
    (hV : ∀ x ∈ P, ∀ v ∈ V, x * v * x⁻¹ ∈ V)
    (hne : ¬ V ≤ U) : ∃ v ∈ V, v ∉ U ∧ ∀ x ∈ P, x * v * x⁻¹ * v⁻¹ ∈ U := by
  have hU'n : (U.subgroupOf P).Normal := ⟨fun a ha g => by
    rw [mem_subgroupOf] at ha ⊢
    simpa using hU g g.2 a ha⟩
  have hV'n : (V.subgroupOf P).Normal := ⟨fun a ha g => by
    rw [mem_subgroupOf] at ha ⊢
    simpa using hV g g.2 a ha⟩
  have hnil : Group.IsNilpotent (P ⧸ U.subgroupOf P) := (hP.to_quotient _).isNilpotent
  have hWn : ((V.subgroupOf P).map (QuotientGroup.mk' (U.subgroupOf P))).Normal :=
    hV'n.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨v₀, hv₀V, hv₀U⟩ := Set.not_subset.1 hne
  have hWne : (V.subgroupOf P).map (QuotientGroup.mk' (U.subgroupOf P)) ≠ ⊥ := by
    intro h
    have hmem : QuotientGroup.mk' (U.subgroupOf P) ⟨v₀, hVP hv₀V⟩ ∈
        (V.subgroupOf P).map (QuotientGroup.mk' (U.subgroupOf P)) :=
      mem_map_of_mem _ (mem_subgroupOf.2 hv₀V)
    rw [h, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hmem
    exact hv₀U hmem
  obtain ⟨⟨w, hwW, hwc⟩, hw1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hWne)
  obtain ⟨v', hv'V, rfl⟩ := hwW
  refine ⟨v', mem_subgroupOf.1 hv'V, fun hvU => hw1 ?_, fun x hx => ?_⟩
  · apply Subtype.ext
    change QuotientGroup.mk' (U.subgroupOf P) v' = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact mem_subgroupOf.2 hvU
  · have hc := Subgroup.mem_center_iff.1 hwc (QuotientGroup.mk' (U.subgroupOf P) ⟨x, hx⟩)
    have h1 : QuotientGroup.mk' (U.subgroupOf P) (⟨x, hx⟩ * v' * ⟨x, hx⟩⁻¹ * v'⁻¹) = 1 := by
      simp only [map_mul, map_inv, hc, mul_inv_cancel_right, mul_inv_cancel]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    simpa using h1

theorem mem_normalizer_of_conj_mem [Finite G] {X : Subgroup G} {g : G}
    (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : g ∈ normalizer (X : Set G) := by
  have hle : X.map (MulAut.conj g).toMonoidHom ≤ X := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : X.map (MulAut.conj g).toMonoidHom = X :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq

theorem le_of_isPGroup_of_conj [Finite G] {p : ℕ} [Fact p.Prime] {H Q X : Subgroup G}
    (hQH : Q ≤ H) (hXH : X ≤ H) (hQ : IsPGroup p Q) (hX : IsPGroup p X) {m : ℕ}
    (hcard : Nat.card H = Nat.card Q * m) (hm : ¬ p ∣ m)
    (hconj : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) : X ≤ Q := by
  have hN : Q ≤ normalizer (X : Set G) := fun q hq =>
    mem_normalizer_of_conj_mem (hconj q (hQH hq))
  have hXQ : IsPGroup p (X ⊔ Q : Subgroup G) := hX.to_sup_of_normal_left' hQ hN
  have hle : X ⊔ Q ≤ H := sup_le hXH hQH
  obtain ⟨a, ha⟩ := hXQ.exists_card_eq
  obtain ⟨b, hb⟩ := hQ.exists_card_eq
  have hdvd : p ^ a ∣ p ^ b * m := by
    rw [← ha, ← hb, ← hcard]
    exact Subgroup.card_dvd_of_le hle
  have hcop : Nat.Coprime (p ^ a) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)
  have h1 : Nat.card (X ⊔ Q : Subgroup G) ≤ Nat.card Q := by
    rw [ha, hb]
    exact Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos _) (hcop.dvd_of_dvd_mul_right hdvd)
  have heq : Q = X ⊔ Q := Subgroup.eq_of_le_of_card_ge le_sup_right h1
  exact heq ▸ le_sup_left

theorem mul_inv_mem_of_card_eq_two_mul [Finite G] {U W : Subgroup G} (hUW : U ≤ W)
    (hcard : Nat.card W = 2 * Nat.card U) {a b : G} (ha : a ∈ W) (hb : b ∈ W) (haU : a ∉ U)
    (hbU : b ∉ U) : a * b⁻¹ ∈ U := by
  have hidx : (U.subgroupOf W).index = 2 := by
    have h := (U.subgroupOf W).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hUW).toEquiv, hcard] at h
    have hpos : 0 < Nat.card U := Nat.card_pos
    nlinarith
  have ha' : (⟨a, ha⟩ : W) ∉ U.subgroupOf W := fun h => haU (mem_subgroupOf.1 h)
  have hb' : (⟨b, hb⟩ : W) ∉ U.subgroupOf W := fun h => hbU (mem_subgroupOf.1 h)
  have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := (⟨b, hb⟩ : W)⁻¹)).2
    (by simp [ha', hb'])
  exact mem_subgroupOf.1 h

@[expose] def commSub (P U V : Subgroup G) (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hUV : U ≤ V) : Subgroup G where
  carrier := {v | v ∈ V ∧ ∀ x ∈ P, x * v * x⁻¹ * v⁻¹ ∈ U}
  mul_mem' := by
    rintro f g ⟨hf, hfU⟩ ⟨hg, hgU⟩
    refine ⟨mul_mem hf hg, fun x hx => ?_⟩
    have e : x * (f * g) * x⁻¹ * (f * g)⁻¹ =
        (x * f * x⁻¹ * f⁻¹) * (f * (x * g * x⁻¹ * g⁻¹) * f⁻¹) := by group
    have hc : f * (x * g * x⁻¹ * g⁻¹) = (x * g * x⁻¹ * g⁻¹) * f :=
      hV _ hf _ (hUV (hgU x hx))
    rw [e, hc, mul_inv_cancel_right]
    exact mul_mem (hfU x hx) (hgU x hx)
  one_mem' := ⟨one_mem _, fun x _ => by simp⟩
  inv_mem' := by
    rintro f ⟨hf, hfU⟩
    refine ⟨inv_mem hf, fun x hx => ?_⟩
    have e : x * f⁻¹ * x⁻¹ * f⁻¹⁻¹ = f⁻¹ * (x * f * x⁻¹ * f⁻¹)⁻¹ * f := by group
    have hc : f⁻¹ * (x * f * x⁻¹ * f⁻¹)⁻¹ = (x * f * x⁻¹ * f⁻¹)⁻¹ * f⁻¹ :=
      hV _ (inv_mem hf) _ (hUV (inv_mem (hfU x hx)))
    rw [e, hc, inv_mul_cancel_right]
    exact inv_mem (hfU x hx)

variable {P U V : Subgroup G} {hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a} {hUV : U ≤ V}

end CFSG.LocalAnalysis.EvenBN.Tits
