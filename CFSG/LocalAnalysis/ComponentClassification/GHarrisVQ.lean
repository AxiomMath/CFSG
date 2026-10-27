module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisEFCertInputs
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL32e

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

namespace SCert.SE

theorem mul_of_d_zero (a b : SE) (ha : a.d = 0) :
    a * b = ⟨b.d, a.v0 + b.v0, a.v1 + b.v1, a.v2 + b.v2⟩ := by
  show mul a b = _
  simp only [mul, act, ha, me_zero, dmul_zero_left]
  congr 1 <;> simp

theorem inv_of_d_zero (a : SE) (ha : a.d = 0) : a⁻¹ = ⟨0, -a.v0, -a.v1, -a.v2⟩ := by
  show inv a = _
  simp only [inv, act, ha, show dinv 0 = 0 from rfl, me_zero]
  congr 1 <;> simp

@[expose] def Qsub : Subgroup SE where
  carrier := {s | s.d = 0}
  mul_mem' {a b} ha hb := by
    change (a * b).d = 0
    rw [mul_of_d_zero a b ha]
    exact hb
  one_mem' := rfl
  inv_mem' {a} ha := by
    change a⁻¹.d = 0
    rw [inv_of_d_zero a ha]

theorem Qsub_comm {a b : SE} (ha : a ∈ Qsub) (hb : b ∈ Qsub) : a * b = b * a := by
  rw [mul_of_d_zero a b ha, mul_of_d_zero b a hb, show a.d = b.d from ha.trans hb.symm]
  congr 1 <;> ring

@[expose] def predV (s : SE) : Prop :=
  s.d = 0 ∧ s.v0.val % 2 = 0 ∧ s.v1.val % 2 = 0 ∧ s.v2.val % 2 = 0

instance : DecidablePred predV := fun s => by unfold predV; infer_instance

theorem zmod4_even_add : ∀ x y : ZMod 4, x.val % 2 = 0 → y.val % 2 = 0 → (x + y).val % 2 = 0 := by
  decide

theorem zmod4_even_neg : ∀ x : ZMod 4, x.val % 2 = 0 → (-x).val % 2 = 0 := by decide

@[expose] def Vsub : Subgroup SE where
  carrier := {s | predV s}
  mul_mem' {a b} ha hb := by
    change predV (a * b)
    rw [mul_of_d_zero a b ha.1]
    exact ⟨hb.1, zmod4_even_add _ _ ha.2.1 hb.2.1, zmod4_even_add _ _ ha.2.2.1 hb.2.2.1,
      zmod4_even_add _ _ ha.2.2.2 hb.2.2.2⟩
  one_mem' := by decide
  inv_mem' {a} ha := by
    change predV a⁻¹
    rw [inv_of_d_zero a ha.1]
    exact ⟨rfl, zmod4_even_neg _ ha.2.1, zmod4_even_neg _ ha.2.2.1, zmod4_even_neg _ ha.2.2.2⟩

theorem Vsub_le_Qsub : Vsub ≤ Qsub := fun _ h => h.1

@[expose] def Vlist : List SE :=
  [⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 2, 0⟩, ⟨0, 0, 2, 2⟩, ⟨0, 2, 0, 0⟩, ⟨0, 2, 0, 2⟩,
    ⟨0, 2, 2, 0⟩, ⟨0, 2, 2, 2⟩]

theorem mem_Vlist_of_predV : ∀ s : SE, predV s → s ∈ Vlist := by decide +kernel

theorem predV_of_mem_Vlist : ∀ s ∈ Vlist, predV s := by decide +kernel

theorem predV_conj : ∀ s ∈ Vlist, ∀ c : SE, predV (c⁻¹ * s * c) := by decide +kernel

theorem sq_of_mem_Vlist : ∀ s ∈ Vlist, s * s = 1 := by decide +kernel

theorem conj_rep_of_mem_Vlist : ∀ s ∈ Vlist, s ≠ 1 → ∃ c : SE,
    c⁻¹ * s * c = gen 0 ∨ c⁻¹ * s * c = invRep 1 ∨ c⁻¹ * s * c = invRep 2 := by
  decide +kernel

theorem invRep_mem_V : predV (gen 0) ∧ predV (invRep 1) ∧ predV (invRep 2) := by decide

theorem centralizer_nonabelian : ∀ i : Fin 9, (i = 3 ∨ i = 5) → ∃ p q : SE,
    p * invRep i = invRep i * p ∧ q * invRep i = invRep i * q ∧ p * q ≠ q * p := by
  intro i hi
  rcases hi with rfl | rfl
  · exact ⟨⟨0, 0, 2, 0⟩, ⟨2, 0, 0, 0⟩, by decide⟩
  · exact ⟨⟨0, 0, 2, 0⟩, ⟨2, 0, 1, 3⟩, by decide⟩

theorem t_not_central : (⟨2, 0, 0, 0⟩ : SE) * invRep 1 ≠ invRep 1 * ⟨2, 0, 0, 0⟩ := by decide

theorem partner_V : ∀ e : SE, predE e → e * e = 1 → e ≠ 1 → e ≠ gen 0 → predV e ∨
    ∃ w ∈ Vlist, w ≠ 1 ∧ w ≠ gen 0 ∧ e * w = w * e ∧ e ≠ w ∧ e ≠ gen 0 * w := by
  decide +kernel

theorem predV_of_E_F : ∀ s : SE, predE s → predF s → s * s = 1 → predV s := by decide +kernel

theorem card_filter_predV : (Finset.univ.filter predV).card = 8 := by decide +kernel

theorem card_Vsub : Nat.card Vsub = 8 := by
  rw [← card_filter_predV, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

theorem card_filter_Q : (Finset.univ.filter fun s : SE => s.d = 0).card = 64 := by decide +kernel

theorem card_Qsub : Nat.card Qsub = 64 := by
  rw [← card_filter_Q, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

end SCert.SE

variable {G : Type} [Group G]

namespace GHSylow

variable (D : GHSylow G)

abbrev Q : Subgroup G := SE.Qsub.map D.toG

abbrev V : Subgroup G := SE.Vsub.map D.toG

theorem toG_mem_V_iff {s : SE} : D.toG s ∈ D.V ↔ SE.predV s := D.mem_map_toG

theorem toG_mem_Q_iff {s : SE} : D.toG s ∈ D.Q ↔ s.d = 0 := D.mem_map_toG

theorem V_le_Q : D.V ≤ D.Q := map_mono SE.Vsub_le_Qsub

theorem Q_le_S : D.Q ≤ (D.S : Subgroup G) := by
  rintro _ ⟨s, -, rfl⟩
  exact D.toG_mem s

theorem V_le_S : D.V ≤ (D.S : Subgroup G) := D.V_le_Q.trans D.Q_le_S

theorem card_V : Nat.card D.V = 8 := by
  rw [card_map_of_injective D.toG_injective, SE.card_Vsub]

theorem card_Q : Nat.card D.Q = 64 := by
  rw [card_map_of_injective D.toG_injective, SE.card_Qsub]

theorem Q_comm {a b : G} (ha : a ∈ D.Q) (hb : b ∈ D.Q) : a * b = b * a := by
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  rw [← map_mul, ← map_mul, SE.Qsub_comm ha₀ hb₀]

theorem exists_Vlist {v : G} (hv : v ∈ D.V) : ∃ s ∈ SE.Vlist, D.toG s = v := by
  obtain ⟨s, hs, rfl⟩ := hv
  exact ⟨s, SE.mem_Vlist_of_predV s hs, rfl⟩

theorem isElemAbelian_V : CFSG.Open.IsElemAbelian 2 D.V := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun v hv => ?_⟩
  · exact D.Q_comm (D.V_le_Q a.2) (D.V_le_Q b.2)
  · obtain ⟨s, hs, rfl⟩ := D.exists_Vlist hv
    rw [← map_pow, pow_two, SE.sq_of_mem_Vlist s hs, map_one]

theorem conj_mem_V {c v : G} (hc : c ∈ (D.S : Subgroup G)) (hv : v ∈ D.V) : c⁻¹ * v * c ∈ D.V := by
  obtain ⟨s, hs, rfl⟩ := D.exists_Vlist hv
  obtain ⟨c₀, rfl⟩ := D.exists_toG hc
  rw [← map_inv, ← map_mul, ← map_mul, D.toG_mem_V_iff]
  exact SE.predV_conj s hs c₀

theorem exists_conj_rep_of_mem_V {v : G} (hv : v ∈ D.V) (hv1 : v ≠ 1) :
    ∃ c ∈ (D.S : Subgroup G), c⁻¹ * v * c = D.z ∨ c⁻¹ * v * c = D.t ∨ c⁻¹ * v * c = D.a1l := by
  obtain ⟨s, hs, rfl⟩ := D.exists_Vlist hv
  have hs1 : s ≠ 1 := fun h => hv1 (by rw [h, map_one])
  obtain ⟨c, hc⟩ := SE.conj_rep_of_mem_Vlist s hs hs1
  refine ⟨D.toG c, D.toG_mem c, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  rcases hc with h | h | h <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem z_mem_V : D.z ∈ D.V := (D.toG_mem_V_iff).mpr SE.invRep_mem_V.1

theorem t_mem_V : D.t ∈ D.V := (D.toG_mem_V_iff).mpr SE.invRep_mem_V.2.1

theorem a1l_mem_V : D.a1l ∈ D.V := (D.toG_mem_V_iff).mpr SE.invRep_mem_V.2.2

end GHSylow

end CFSG.ComponentClassification.GHarris
