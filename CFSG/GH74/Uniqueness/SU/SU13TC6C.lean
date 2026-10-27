module

public import CFSG.GH74.Uniqueness.SU.SU13TC6B

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem conj_mem_commutator {Y Y₂ : Subgroup G} {g : G} (h : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y₂) {n : G}
    (hn : n ∈ ⁅Y, Y⁆) : g * n * g⁻¹ ∈ ⁅Y₂, Y₂⁆ := by
  have h1 : Y.map (MulAut.conj g).toMonoidHom ≤ Y₂ := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have h2 := Subgroup.commutator_mono h1 h1
  rw [← Subgroup.map_commutator] at h2
  exact h2 ⟨n, hn, by simp [MulAut.conj_apply]⟩

namespace Ctx9

variable (X : Ctx9 G z)

theorem Zy_comm {n : G} (hn : n ∈ X.Zy) {y : G} (hy : y ∈ X.Y) : y * n = n * y :=
  mem_centralizer_iff.mp (mem_inf.mp hn).2 y hy

def Z2 : Subgroup G where
  carrier := {y | y ∈ X.Y ∧ ∀ y' ∈ X.Y, y * y' * y⁻¹ * y'⁻¹ ∈ X.Zy}
  one_mem' := ⟨X.Y.one_mem, fun y' _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haY, ha⟩ ⟨hbY, hb⟩
    refine ⟨X.Y.mul_mem haY hbY, fun y' hy' => ?_⟩
    have h1 := hb y' hy'
    have h2 := ha y' hy'
    have hc : a * (b * y' * b⁻¹ * y'⁻¹) * a⁻¹ = b * y' * b⁻¹ * y'⁻¹ := by
      have := X.Zy_comm h1 haY
      calc a * (b * y' * b⁻¹ * y'⁻¹) * a⁻¹ = (a * (b * y' * b⁻¹ * y'⁻¹)) * a⁻¹ := by group
        _ = ((b * y' * b⁻¹ * y'⁻¹) * a) * a⁻¹ := by rw [this]
        _ = b * y' * b⁻¹ * y'⁻¹ := by group
    have : a * b * y' * (a * b)⁻¹ * y'⁻¹ =
        (a * (b * y' * b⁻¹ * y'⁻¹) * a⁻¹) * (a * y' * a⁻¹ * y'⁻¹) := by group
    rw [this, hc]
    exact X.Zy.mul_mem h1 h2
  inv_mem' := by
    rintro a ⟨haY, ha⟩
    refine ⟨X.Y.inv_mem haY, fun y' hy' => ?_⟩
    have h2 := ha y' hy'
    have h3 := X.Zy.inv_mem h2
    have h4 : (a * y' * a⁻¹ * y'⁻¹)⁻¹ = y' * a * y'⁻¹ * a⁻¹ := by group
    rw [h4] at h3
    have h5 := X.Zy_comm h3 (X.Y.inv_mem haY)
    have hc : a⁻¹ * (y' * a * y'⁻¹ * a⁻¹) * a = y' * a * y'⁻¹ * a⁻¹ := by
      calc a⁻¹ * (y' * a * y'⁻¹ * a⁻¹) * a = (a⁻¹ * (y' * a * y'⁻¹ * a⁻¹)) * a := by group
        _ = ((y' * a * y'⁻¹ * a⁻¹) * a⁻¹) * a := by rw [h5]
        _ = y' * a * y'⁻¹ * a⁻¹ := by group
    have : a⁻¹ * y' * a⁻¹⁻¹ * y'⁻¹ = a⁻¹ * (y' * a * y'⁻¹ * a⁻¹) * a := by group
    rw [this, hc]
    exact h3

theorem Zy_le_Z2 : X.Zy ≤ X.Z2 := fun n hn => ⟨(mem_inf.mp hn).1, fun y' hy' => by
  have := X.Zy_comm hn hy'
  have h : n * y' * n⁻¹ * y'⁻¹ = 1 := by
    calc n * y' * n⁻¹ * y'⁻¹ = (n * y') * n⁻¹ * y'⁻¹ := rfl
      _ = (y' * n) * n⁻¹ * y'⁻¹ := by rw [← this]
      _ = 1 := by group
  rw [h]
  exact X.Zy.one_mem⟩

theorem Z2_le_Y : X.Z2 ≤ X.Y := fun _ hy => hy.1

theorem conj_Z2 {c y : G} (hc : c ∈ X.C) (hy : y ∈ X.Z2) : c * y * c⁻¹ ∈ X.Z2 := by
  obtain ⟨hyY, hy⟩ := hy
  refine ⟨X.conj_Y hc hyY, fun y' hy' => ?_⟩
  have hy'' : c⁻¹ * y' * c ∈ X.Y := by simpa using X.conj_Y (X.C.inv_mem hc) hy'
  have h := X.conj_Zy hc (hy _ hy'')
  have : c * (y * (c⁻¹ * y' * c) * y⁻¹ * (c⁻¹ * y' * c)⁻¹) * c⁻¹ =
      c * y * c⁻¹ * y' * (c * y * c⁻¹)⁻¹ * y'⁻¹ := by group
  rw [← this]
  exact h

theorem Z2_eq_Y : X.Z2 = X.Y := by
  have hlt : X.Zy < X.Y := lt_of_le_of_ne inf_le_left (fun h => by
    have := X.card_Zy
    rw [h, X.Y_card] at this
    norm_num at this)
  have hP : IsPGroup 3 X.Y := IsPGroup.of_card (n := 7) X.Y_card
  obtain ⟨v, hvY, hvZ, hvc⟩ := exists_central_mod (p := 3) (by norm_num) (P := X.Y) (N := X.Y)
    (Z := X.Zy) hP le_rfl (fun g hg u hu => X.Y.mul_mem (X.Y.mul_mem hg hu) (X.Y.inv_mem hg)) inf_le_left
    (fun g hg u hu => by
      have := X.Zy_comm hu hg
      have h : g * u * g⁻¹ = u := by rw [this]; group
      rw [h]; exact hu) hlt
  have hvZ2 : v ∈ X.Z2 := ⟨hvY, fun y' hy' => by
    have h := X.Zy.inv_mem (hvc y' hy')
    have e : (y' * v * y'⁻¹ * v⁻¹)⁻¹ = v * y' * v⁻¹ * y'⁻¹ := by group
    rwa [e] at h⟩
  have hs : X.L.e.s₂ ∈ X.Z2 := X.Zy_le_Z2 X.s₂_mem_Zy
  have hord := (lattice_orders X (N := X.Z2) X.Z2_le_Y (fun c hc n hn => X.conj_Z2 hc hn)).1 hs
  have hge : Nat.card X.Zy < Nat.card X.Z2 := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le X.Zy_le_Z2) (fun h => ?_)
    have heq : X.Zy = X.Z2 := Subgroup.eq_of_le_of_card_ge X.Zy_le_Z2 (by rw [h])
    rw [← heq] at hvZ2
    exact hvZ hvZ2
  rw [X.card_Zy] at hge
  have h7 : Nat.card X.Z2 = 3 ^ 7 := by
    rcases hord with h | h | h
    · rw [h] at hge; norm_num at hge
    · rw [h] at hge; norm_num at hge
    · exact h
  exact Subgroup.eq_of_le_of_card_ge X.Z2_le_Y (by rw [h7, X.Y_card])

theorem class_two {a b : G} (ha : a ∈ X.Y) (hb : b ∈ X.Y) : a * b * a⁻¹ * b⁻¹ ∈ X.Zy := by
  have : a ∈ X.Z2 := by rw [X.Z2_eq_Y]; exact ha
  exact this.2 b hb

theorem Y'_le_Zy : ⁅X.Y, X.Y⁆ ≤ X.Zy := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact X.class_two ha hb

theorem Y'_le_Y : ⁅X.Y, X.Y⁆ ≤ X.Y := X.Y'_le_Zy.trans inf_le_left

theorem conj_Y' {c n : G} (hc : c ∈ X.C) (hn : n ∈ ⁅X.Y, X.Y⁆) : c * n * c⁻¹ ∈ ⁅X.Y, X.Y⁆ :=
  conj_mem_commutator (fun _ hy => X.conj_Y hc hy) hn

theorem Y'_comm {n : G} (hn : n ∈ ⁅X.Y, X.Y⁆) {y : G} (hy : y ∈ X.Y) : y * n = n * y :=
  X.Zy_comm (X.Y'_le_Zy hn) hy

theorem Y'_ne_bot : ⁅X.Y, X.Y⁆ ≠ ⊥ := by
  intro h
  have hY : X.Y ≤ X.Zy := fun y hy => mem_inf.mpr ⟨hy, mem_centralizer_iff.mpr fun y' hy' => by
    have := Subgroup.commutator_mem_commutator hy' hy
    rw [h, mem_bot, commutatorElement_def] at this
    calc y' * y = (y' * y * y'⁻¹ * y⁻¹) * y * y' := by group
      _ = y * y' := by rw [this, one_mul]⟩
  have := Subgroup.card_le_of_le hY
  rw [X.Y_card, X.card_Zy] at this
  norm_num at this

theorem exists_conj_z {r : G} (hr : r ∈ kfour X.hz X.L.e) (hr1 : r ≠ 1) :
    ∃ c ∈ X.C, c * z * c⁻¹ = r := by
  rcases kfour_mem X.hz X.L.e hr with h | h | h | h
  · obtain ⟨k, hk, hkz⟩ := X.l.k₂
    exact ⟨k, mem_centralizer_singleton_iff.mpr hk, by rw [h]; exact hkz⟩
  · obtain ⟨k, hk, hkz⟩ := X.l.k₁
    exact ⟨k, mem_centralizer_singleton_iff.mpr hk, by rw [h]; exact hkz⟩
  · exact ⟨1, X.C.one_mem, by rw [h]; group⟩
  · exact absurd h hr1

theorem cent_Y_abelian {r : G} (hr : r ∈ kfour X.hz X.L.e) (hr1 : r ≠ 1) {a b : G} (ha : a ∈ X.Y)
    (hb : b ∈ X.Y) (har : a * r = r * a) (hbr : b * r = r * b) : a * b = b * a := by
  obtain ⟨c, hc, hcr⟩ := X.exists_conj_z hr hr1
  have hconj : ∀ w : G, w ∈ X.Y → w * r = r * w → c⁻¹ * w * c ∈ X.E := by
    intro w hw hwr
    have hwY : c⁻¹ * w * c ∈ X.Y := by simpa using X.conj_Y (X.C.inv_mem hc) hw
    have hcomm : (c⁻¹ * w * c) * z = z * (c⁻¹ * w * c) := by
      calc (c⁻¹ * w * c) * z = c⁻¹ * w * (c * z * c⁻¹) * c := by group
        _ = c⁻¹ * (w * r) * c := by rw [hcr]; group
        _ = c⁻¹ * (r * w) * c := by rw [hwr]
        _ = c⁻¹ * ((c * z * c⁻¹) * w) * c := by rw [hcr]
        _ = z * (c⁻¹ * w * c) := by group
    have hmem : c⁻¹ * w * c ∈ oc X.C ⊓ centralizer ({z} : Set G) :=
      mem_inf.mpr ⟨hwY, mem_centralizer_singleton_iff.mpr hcomm⟩
    rw [X.l3.Y_cent] at hmem
    exact hmem
  have hab := X.L.E.E_abel _ (hconj a ha har) _ (hconj b hb hbr)
  calc a * b = c * ((c⁻¹ * a * c) * (c⁻¹ * b * c)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * b * c) * (c⁻¹ * a * c)) * c⁻¹ := by rw [hab]
    _ = b * a := by group

theorem cent_Y_R_central {a : G} (ha : a ∈ X.Y) (hat : a * X.L.e.t = X.L.e.t * a) (haz : a * z = z * a)
    {b : G} (hb : b ∈ X.Y) : a * b = b * a := by
  have haE : a ∈ X.E := by
    have hmem : a ∈ oc X.C ⊓ centralizer ({z} : Set G) :=
      mem_inf.mpr ⟨ha, mem_centralizer_singleton_iff.mpr haz⟩
    rw [X.l3.Y_cent] at hmem
    exact hmem
  have hs : a ∈ zpowers X.L.e.s₂ := X.L.m.cent_t a haE hat.symm
  exact zpowers_comm_of_mem_centralizer (X.Y_le_C hb) hs

end Ctx9

end CFSG.GH74.Uniqueness.SU.SU13
