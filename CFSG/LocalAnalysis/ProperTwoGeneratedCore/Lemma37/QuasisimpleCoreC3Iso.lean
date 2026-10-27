module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Model
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3TypeA

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {G : Type} [Group G] [Finite G] {T Q P₁ S : Subgroup G} {e u y x m : G}

structure CaseC3BCD (T Q P₁ S : Subgroup G) (e u y x m : G) (Z : Subgroup G) [Z.Normal] : Prop
    extends CaseC3Top T Q P₁ S e u y x where
  mem_iff : ∀ g, g ∈ Z ↔ g = 1 ∨ g = e
  mk_mul_self : ((x * x : G) : G ⧸ Z) = 1
  mk_comm : (x : G ⧸ Z) * (y : G ⧸ Z) = (y : G ⧸ Z) * (x : G ⧸ Z)
  m_mem : m ∈ P₁
  m_moved : y * m * y⁻¹ ≠ m
  m_moved' : y * m * y⁻¹ ≠ m * e

namespace CaseC3BCD

variable {Z : Subgroup G} [Z.Normal] (hb : CaseC3BCD T Q P₁ S e u y x m Z)
include hb

omit [Finite G] in
theorem mk_centralElt : ((e : G) : G ⧸ Z) = 1 :=
  (QuotientGroup.eq_one_iff e).mpr ((hb.mem_iff e).mpr (Or.inr rfl))

omit [Finite G] in
theorem le_sup : Z ≤ Q ⊔ P₁ := hb.partC.le_sup_of_mem_iff Z hb.mem_iff

omit [Finite G] in
theorem le_bot : Z ≤ T := hb.le_sup.trans hb.partC.sup_le

theorem c3Relations :
    C3Relations (u : G ⧸ Z) (m : G ⧸ Z) ((x : G ⧸ Z) * (u : G ⧸ Z) * (x : G ⧸ Z)⁻¹)
      ((x : G ⧸ Z) * (m : G ⧸ Z) * (x : G ⧸ Z)⁻¹) (y : G ⧸ Z) (x : G ⧸ Z) := by
  have hc := hb.partC
  obtain ⟨φ⟩ := hb.quaternion_right
  have hZ := hb.mem_iff
  have he1 := hb.mk_centralElt
  refine c3Relations_of (W := (Q ⊔ P₁).map (QuotientGroup.mk' Z))
    (fun g hg g' hg' => hc.mul_comm_of_mem_map_sup Z φ hZ hg hg') (fun g hg => ?_)
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_right hc.self_mem))
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_right hb.m_mem)) ?_ ?_ ?_ hb.mk_comm.symm ?_ ?_
  · have := hc.pow_two_eq_one_of_mem_map_sup Z φ hZ hg
    rwa [pow_two] at this
  · rintro _ ⟨w, hw, rfl⟩
    have := hb.mk_conj_mem Z hw
    simpa only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv] using this
  · rw [← QuotientGroup.mk_mul, hb.mul_self, he1]
  · rw [← QuotientGroup.mk_mul]
    exact hb.mk_mul_self
  · rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rcases hb.conj_self with h1 | h1 <;> rw [h1]
    rw [QuotientGroup.mk_mul, he1, mul_one]
  · rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rcases hb.toCaseC3.conj_moved hb.m_mem hb.m_moved hb.m_moved' with h1 | h1 <;> rw [h1]
    · rw [QuotientGroup.mk_mul]
    · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, he1, mul_one]

omit [Finite G] in
theorem mk_not_mem_bot : (x : G ⧸ Z) ∉ T.map (QuotientGroup.mk' Z) := by
  rw [PartC.mk_mem_map_iff_of_le Z hb.le_bot]
  exact hb.not_mem_bot

omit [Finite G] in
theorem mk_ne_one : (u : G ⧸ Z) ≠ 1 ∧ (m : G ⧸ Z) ≠ 1 ∧ (u : G ⧸ Z) * (m : G ⧸ Z) ≠ 1 := by
  have hc := hb.partC
  have hmk1 : ∀ {g : G}, (g : G ⧸ Z) = 1 ↔ g = 1 ∨ g = e := fun {g} => by
    rw [QuotientGroup.eq_one_iff, hb.mem_iff]
  have hfix : ∀ g : G, (g = 1 ∨ g = e ∨ g = u ∨ g = u * e) →
      y * g * y⁻¹ = g ∨ y * g * y⁻¹ = g * e := by
    rintro g (rfl | rfl | rfl | rfl)
    · left
      group
    · exact Or.inl (hc.conj_centralElt y)
    · exact hb.conj_self
    · exact conj_mul_mod_central hc.center hc.centralElt_mul_self hb.conj_self
        (Or.inl (hc.conj_centralElt y))
  have hmU : ¬ (m = 1 ∨ m = e ∨ m = u ∨ m = u * e) := fun h' => by
    rcases hfix m h' with h1 | h1
    exacts [hb.m_moved h1, hb.m_moved' h1]
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · rcases hmk1.mp h1 with h2 | h2
    exacts [hc.self_ne.1 h2, hc.self_ne.2 h2]
  · rcases hmk1.mp h1 with h2 | h2
    · exact hmU (Or.inl h2)
    · exact hmU (Or.inr (Or.inl h2))
  · rw [← QuotientGroup.mk_mul] at h1
    rcases hmk1.mp h1 with h2 | h2
    · apply hmU
      right; right; right
      rw [eq_inv_of_mul_eq_one_right h2, hc.inv_eq_mul_centralElt hc.sq]
    · apply hmU
      right; right; left
      rw [show m = u⁻¹ * e by rw [← h2]; group, hc.inv_eq_mul_centralElt hc.sq,
        hc.mul_centralElt_mul_centralElt]

omit [Finite G] in
theorem c3Word_eq_one (v : Fin 64)
    (hv : c3Word (u : G ⧸ Z) (m : G ⧸ Z) ((x : G ⧸ Z) * (u : G ⧸ Z) * (x : G ⧸ Z)⁻¹)
      ((x : G ⧸ Z) * (m : G ⧸ Z) * (x : G ⧸ Z)⁻¹) (y : G ⧸ Z) (x : G ⧸ Z) v = 1) : v = 0 := by
  have hc := hb.partC
  obtain ⟨hu1, hm1, hum1⟩ := hb.mk_ne_one
  obtain ⟨-, hyW, -⟩ := hb.toCaseC3.mk_facts Z hb.mem_iff
  refine QuasisimpleCore.c3Word_eq_one (W := (Q ⊔ P₁).map (QuotientGroup.mk' Z))
    (T₀ := T.map (QuotientGroup.mk' Z)) (P := P₁.map (QuotientGroup.mk' Z))
    (Q := Q.map (QuotientGroup.mk' Z)) (Subgroup.map_mono hc.sup_le)
    (Subgroup.map_mono le_sup_right) (Subgroup.map_mono le_sup_left) ?_
    (Subgroup.mem_map_of_mem _ hc.self_mem) (Subgroup.mem_map_of_mem _ hb.m_mem) hu1 hm1 hum1
    ?_ (Subgroup.mem_map_of_mem _ hb.mem) hyW hb.mk_not_mem_bot v hv
  · rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hqp⟩
    simp only [QuotientGroup.mk'_apply] at hqp ⊢
    rcases (hb.mem_iff _).mp (QuotientGroup.eq.mp hqp.symm) with h1 | h1
    · rw [inv_mul_eq_one] at h1
      subst h1
      rcases hc.mem_inf _ hq hp with h2 | h2 <;> rw [h2]
      · rfl
      · exact hb.mk_centralElt
    · rw [inv_mul_eq_iff_eq_mul] at h1
      have hpQ : p ∈ Q := by
        rw [show p = q * e⁻¹ by rw [h1]; group]
        exact Q.mul_mem hq (Q.inv_mem hc.mem_left)
      rcases hc.mem_inf p hpQ hp with h2 | h2 <;> rw [h2]
      · rfl
      · exact hb.mk_centralElt
  · rintro _ ⟨p, hp, rfl⟩
    have := Subgroup.mem_map_of_mem (QuotientGroup.mk' Z) (hb.swap_right p hp)
    simpa only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv] using this

omit [Finite G] in
theorem card_map_top : Nat.card (S.map (QuotientGroup.mk' Z)) = 64 := by
  have hc := hb.partC
  obtain ⟨φ⟩ := hb.quaternion_right
  have h1 := Subgroup.relIndex_mul_card ((Q ⊔ P₁).map (QuotientGroup.mk' Z))
    (T.map (QuotientGroup.mk' Z))
  rw [hc.relIndex_map_sup Z hb.mem_iff hb.mem hb.not_mem,
    inf_eq_left.mpr (Subgroup.map_mono hc.sup_le), hc.card_map_sup Z φ hb.mem_iff] at h1
  have h2 := Subgroup.relIndex_mul_card (T.map (QuotientGroup.mk' Z))
    (S.map (QuotientGroup.mk' Z))
  rw [PartC.relIndex_map_eq_two Z hb.le_bot hb.mem_top hb.not_mem_bot hb.mul_mem,
    inf_eq_left.mpr (Subgroup.map_mono hb.le_top), ← h1] at h2
  omega

theorem c3Word_bijective :
    Function.Injective (c3Word (u : G ⧸ Z) (m : G ⧸ Z)
      ((x : G ⧸ Z) * (u : G ⧸ Z) * (x : G ⧸ Z)⁻¹) ((x : G ⧸ Z) * (m : G ⧸ Z) * (x : G ⧸ Z)⁻¹)
      (y : G ⧸ Z) (x : G ⧸ Z)) ∧
    (∀ v, c3Word (u : G ⧸ Z) (m : G ⧸ Z) ((x : G ⧸ Z) * (u : G ⧸ Z) * (x : G ⧸ Z)⁻¹)
      ((x : G ⧸ Z) * (m : G ⧸ Z) * (x : G ⧸ Z)⁻¹) (y : G ⧸ Z) (x : G ⧸ Z) v ∈
        S.map (QuotientGroup.mk' Z)) ∧
    ∀ s ∈ S.map (QuotientGroup.mk' Z), ∃ v, c3Word (u : G ⧸ Z) (m : G ⧸ Z)
      ((x : G ⧸ Z) * (u : G ⧸ Z) * (x : G ⧸ Z)⁻¹) ((x : G ⧸ Z) * (m : G ⧸ Z) * (x : G ⧸ Z)⁻¹)
      (y : G ⧸ Z) (x : G ⧸ Z) v = s := by
  have hc := hb.partC
  have hS : ∀ {g : G}, g ∈ S → (g : G ⧸ Z) ∈ S.map (QuotientGroup.mk' Z) :=
    fun hg => Subgroup.mem_map_of_mem _ hg
  have hxS := hS hb.mem_top
  have hconj : ∀ {g : G}, g ∈ S → (x : G ⧸ Z) * (g : G ⧸ Z) * (x : G ⧸ Z)⁻¹ ∈
      S.map (QuotientGroup.mk' Z) := fun hg =>
    (S.map (QuotientGroup.mk' Z)).mul_mem ((S.map (QuotientGroup.mk' Z)).mul_mem hxS (hS hg))
      ((S.map (QuotientGroup.mk' Z)).inv_mem hxS)
  have huS : u ∈ S := hb.le_top (hc.right_le hc.self_mem)
  have hmS : m ∈ S := hb.le_top (hc.right_le hb.m_mem)
  exact c3Word_bijective_onto hb.c3Relations hb.c3Word_eq_one hb.card_map_top (hS huS) (hS hmS)
    (hconj huS) (hconj hmS) (hS (hb.le_top hb.mem)) hxS

end CaseC3BCD

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
