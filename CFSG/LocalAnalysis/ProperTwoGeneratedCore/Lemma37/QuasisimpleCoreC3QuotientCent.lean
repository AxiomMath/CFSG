module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Quotient

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G}

namespace PartC

theorem eq_of_mul_eq_mul (hc : PartC T Q P₁ e u) {q p q' p' ε : G} (hq : q ∈ Q) (hp : p ∈ P₁)
    (hq' : q' ∈ Q) (hp' : p' ∈ P₁) (hε : ε = 1 ∨ ε = e) (h : q' * p' = q * p * ε) :
    (q' = q ∨ q' = q * e) ∧ (p' = p ∨ p' = p * e) := by
  have hεP : ε ∈ P₁ := by
    rcases hε with rfl | rfl
    exacts [P₁.one_mem, hc.mem_right]
  have hδ : q⁻¹ * q' = p * ε * p'⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, h]
    group
  have hδZ := hc.mem_inf _ (Q.mul_mem (Q.inv_mem hq) hq')
    (hδ ▸ P₁.mul_mem (P₁.mul_mem hp hεP) (P₁.inv_mem hp'))
  have hee := hc.centralElt_mul_self
  rcases hδZ with h0 | h0
  · rw [inv_mul_eq_one] at h0
    subst h0
    have hp'p : p' = p * ε := mul_left_cancel (h.trans (mul_assoc _ _ _))
    refine ⟨Or.inl rfl, ?_⟩
    rcases hε with rfl | rfl
    · left
      rw [hp'p, mul_one]
    · exact Or.inr hp'p
  · rw [inv_mul_eq_iff_eq_mul] at h0
    subst h0
    refine ⟨Or.inr rfl, ?_⟩
    have h2 : e * p' = p * ε := by
      simp only [mul_assoc] at h
      exact mul_left_cancel h
    have hp'e : p' = p * ε * e := by
      calc p' = e * (e * p') := by rw [← mul_assoc, hee, one_mul]
        _ = e * (p * ε) := by rw [h2]
        _ = p * ε * e := (hc.commute_centralElt (p * ε)).symm
    rcases hε with rfl | rfl
    · right
      rw [hp'e, mul_one]
    · left
      rw [hp'e, mul_assoc, hee, mul_one]

end PartC

namespace CaseC3

variable (Z : Subgroup G) [Z.Normal]

theorem mk_facts (h : CaseC3 T Q P₁ e u y) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) :
    (y : G ⧸ Z) ∈ T.map (QuotientGroup.mk' Z) ∧
      (y : G ⧸ Z) ∉ (Q ⊔ P₁).map (QuotientGroup.mk' Z) ∧ (y : G ⧸ Z) ^ 2 = 1 := by
  refine ⟨Subgroup.mem_map_of_mem _ h.mem, ?_, ?_⟩
  · rw [PartC.mk_mem_map_iff_of_le Z (h.partC.le_sup_of_mem_iff Z hZ)]
    exact h.not_mem
  · rw [← QuotientGroup.mk_pow, pow_two, h.mul_self, QuotientGroup.eq_one_iff, hZ]
    exact Or.inr rfl

theorem mk_commute_of_conj (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) {w : G}
    (hw : y * w * y⁻¹ = w ∨ y * w * y⁻¹ = w * e) :
    (w : G ⧸ Z) * (y : G ⧸ Z) = (y : G ⧸ Z) * (w : G ⧸ Z) := by
  have he1 : ((e : G) : G ⧸ Z) = 1 := (QuotientGroup.eq_one_iff e).mpr ((hZ e).mpr (Or.inr rfl))
  have hw' : ((y * w * y⁻¹ : G) : G ⧸ Z) = (w : G ⧸ Z) := by
    rcases hw with hw | hw
    · rw [hw]
    · rw [hw, QuotientGroup.mk_mul, he1, mul_one]
  calc (w : G ⧸ Z) * (y : G ⧸ Z) = ((y * w * y⁻¹ : G) : G ⧸ Z) * (y : G ⧸ Z) := by rw [hw']
    _ = (y : G ⧸ Z) * (w : G ⧸ Z) := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      group

theorem mem_map_sup_inf_centralizer_iff (h : CaseC3 T Q P₁ e u y)
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) {v : G} (hvQ : v ∈ Q) (hvv : v * v = e)
    (hyv : y * v * y⁻¹ = v⁻¹)
    (hvfix : ∀ w ∈ Q, (y * w * y⁻¹ = w ∨ y * w * y⁻¹ = w * e) →
      w = 1 ∨ w = e ∨ w = v ∨ w = v * e) (x : G ⧸ Z) :
    x ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) ⊓ Subgroup.centralizer {(y : G ⧸ Z)} ↔
      x = 1 ∨ x = (u : G ⧸ Z) ∨ x = (v : G ⧸ Z) ∨ x = (u : G ⧸ Z) * (v : G ⧸ Z) := by
  have hc := h.partC
  have he1 : ((e : G) : G ⧸ Z) = 1 := (QuotientGroup.eq_one_iff e).mpr ((hZ e).mpr (Or.inr rfl))
  constructor
  · intro hx
    obtain ⟨hxW, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hxW
    obtain ⟨q, hq, p, hp, rfl⟩ := hc.mem_sup_iff.mp hw
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC
    simp only [QuotientGroup.mk'_apply] at hxC ⊢
    have key : ((y * (q * p) * y⁻¹ : G) : G ⧸ Z) = ((q * p : G) : G ⧸ Z) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hxC,
        mul_inv_cancel_right]
    have hconj := QuotientGroup.eq.mp key.symm
    have hε := (hZ _).mp hconj
    have hsplit : (y * q * y⁻¹) * (y * p * y⁻¹) =
        q * p * ((q * p)⁻¹ * (y * (q * p) * y⁻¹)) := by group
    obtain ⟨hqf, hpf⟩ := hc.eq_of_mul_eq_mul hq hp (hc.normal_left y h.mem q hq)
      (hc.normal_right y h.mem p hp) hε hsplit
    have hqi : (q : G ⧸ Z) = 1 ∨ (q : G ⧸ Z) = (v : G ⧸ Z) := by
      rcases hvfix q hq hqf with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inl he1
      · exact Or.inr rfl
      · exact Or.inr (by rw [QuotientGroup.mk_mul, he1, mul_one])
    have hpi : (p : G ⧸ Z) = 1 ∨ (p : G ⧸ Z) = (u : G ⧸ Z) := by
      rcases h.mem_of_conj_right hp hpf with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inl he1
      · exact Or.inr rfl
      · exact Or.inr (by rw [QuotientGroup.mk_mul, he1, mul_one])
    have huv : (v : G ⧸ Z) * (u : G ⧸ Z) = (u : G ⧸ Z) * (v : G ⧸ Z) := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc.commute v hvQ u hc.self_mem]
    rw [QuotientGroup.mk_mul]
    rcases hqi with hqi | hqi <;> rcases hpi with hpi | hpi <;> rw [hqi, hpi]
    · exact Or.inl (mul_one 1)
    · exact Or.inr (Or.inl (one_mul _))
    · exact Or.inr (Or.inr (Or.inl (mul_one _)))
    · exact Or.inr (Or.inr (Or.inr huv))
  · have hW : ∀ {w : G}, w ∈ Q ⊔ P₁ → (w : G ⧸ Z) ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) :=
      fun hw => Subgroup.mem_map_of_mem _ hw
    have hu : (u : G ⧸ Z) ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) ⊓
        Subgroup.centralizer {(y : G ⧸ Z)} :=
      ⟨hW (Subgroup.mem_sup_right hc.self_mem), Subgroup.mem_centralizer_singleton_iff.mpr
        (mk_commute_of_conj Z hZ h.conj_self)⟩
    have hv : (v : G ⧸ Z) ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) ⊓
        Subgroup.centralizer {(y : G ⧸ Z)} :=
      ⟨hW (Subgroup.mem_sup_left hvQ), Subgroup.mem_centralizer_singleton_iff.mpr
        (mk_commute_of_conj Z hZ (Or.inr (by rw [hyv, hc.inv_eq_mul_centralElt hvv])))⟩
    rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact hu
    · exact hv
    · exact Subgroup.mul_mem _ hu hv

theorem card_map_sup_inf_centralizer (h : CaseC3 T Q P₁ e u y)
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) :
    Nat.card ((Q ⊔ P₁).map (QuotientGroup.mk' Z) ⊓ Subgroup.centralizer {(y : G ⧸ Z)} :
      Subgroup (G ⧸ Z)) = 4 := by
  have hc := h.partC
  obtain ⟨v, hvQ, hvv, hyv, hvfix⟩ := h.exists_inv_conj_left
  set H := (Q ⊔ P₁).map (QuotientGroup.mk' Z) ⊓ Subgroup.centralizer {(y : G ⧸ Z)} with hH
  have hset : (H : Set (G ⧸ Z)) =
      {1, (u : G ⧸ Z), (v : G ⧸ Z), (u : G ⧸ Z) * (v : G ⧸ Z)} := by
    ext x
    rw [SetLike.mem_coe, h.mem_map_sup_inf_centralizer_iff Z hZ hvQ hvv hyv hvfix]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hmk1 : ∀ {g : G}, (g : G ⧸ Z) = 1 ↔ g = 1 ∨ g = e := fun {g} => by
    rw [QuotientGroup.eq_one_iff, hZ]
  have hv1 : v ≠ 1 := fun h1 => hc.centralElt_ne_one (by rw [← hvv, h1, mul_one])
  have hve : v ≠ e := fun h1 => hc.centralElt_ne_one (by
    rw [← hvv, h1, hc.centralElt_mul_self])
  have hvP : v ∉ P₁ := fun hvP => by
    rcases hc.mem_inf v hvQ hvP with h1 | h1
    exacts [hv1 h1, hve h1]
  have hu1 : (u : G ⧸ Z) ≠ 1 := fun h1 => by
    rcases hmk1.mp h1 with h1 | h1
    exacts [hc.self_ne.1 h1, hc.self_ne.2 h1]
  have hv1' : (v : G ⧸ Z) ≠ 1 := fun h1 => by
    rcases hmk1.mp h1 with h1 | h1
    exacts [hv1 h1, hve h1]
  have huv1 : (u : G ⧸ Z) * (v : G ⧸ Z) ≠ 1 := fun h1 => by
    rw [← QuotientGroup.mk_mul] at h1
    apply hvP
    rcases hmk1.mp h1 with h1 | h1
    · rw [eq_inv_of_mul_eq_one_right h1]
      exact P₁.inv_mem hc.self_mem
    · rw [show v = u⁻¹ * e by rw [← h1]; group]
      exact P₁.mul_mem (P₁.inv_mem hc.self_mem) hc.mem_right
  have huv : (u : G ⧸ Z) ≠ (v : G ⧸ Z) := fun h1 => by
    apply hvP
    rcases (hZ _).mp (QuotientGroup.eq.mp h1) with h1 | h1
    · rw [show v = u * (u⁻¹ * v) by group, h1, mul_one]
      exact hc.self_mem
    · rw [show v = u * (u⁻¹ * v) by group, h1]
      exact P₁.mul_mem hc.self_mem hc.mem_right
  rw [show Nat.card H = (H : Set (G ⧸ Z)).ncard from Nat.card_coe_set_eq _, hset,
    Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_pair]
  · exact fun h1 => hu1 (by simpa using congrArg (fun g => (u : G ⧸ Z)⁻¹ * g) h1.symm)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨huv, fun h1 => hv1' ?_⟩
    simpa using congrArg (fun g => (u : G ⧸ Z)⁻¹ * g) h1.symm
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hu1.symm, hv1'.symm, huv1.symm⟩

end CaseC3

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
