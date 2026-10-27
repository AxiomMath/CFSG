module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117cCtx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117cX

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

namespace Sec11cCnt

variable {z : G} {R T C D Q1 Q2 : Subgroup G} {a x : G}

theorem card_le_of_le_DQ [Finite G] (h : Sec11cCnt G z R T C D Q1 Q2 a x) {Y : Subgroup G}
    (hY : IsCyclic Y) (hYD : Y ≤ D) (hYi : Y.relIndex D = 2) {V : Subgroup G}
    (hVDQ : V ≤ D ⊔ (Q1 ⊔ Q2)) (hV : IsElemAbelianMod z V) : Nat.card V ≤ 128 := by
  have hVR : V ≤ R := hVDQ.trans (sup_le h.D_le (h.Q_le_T.trans h.T_le))
  have hP : Sec11cProj G z D (Q1 ⊔ Q2) V := h.proj hVR hV
  have hcount := hP.card_le_of_le h.cnt.z_sq h.cnt.z_ne hVDQ
  have hle8 : Nat.card ↥(D ⊓ (V ⊔ (Q1 ⊔ Q2))) ≤ 8 :=
    sec11c_card_le_eight hY hYD hYi h.cnt.z_sq inf_le_left hP.elemAb
  have hQ : Nat.card ↥(Q1 ⊔ Q2) = 32 := h.card_Q
  have h2 : 2 * Nat.card V ≤ 8 * 32 := by
    calc 2 * Nat.card V
        ≤ Nat.card ↥(D ⊓ (V ⊔ (Q1 ⊔ Q2))) * Nat.card ↥(Q1 ⊔ Q2) := hcount
      _ ≤ 8 * 32 := by rw [hQ]; exact Nat.mul_le_mul_right _ hle8
  omega

theorem exists_U [Finite G] (h : Sec11cCnt G z R T C D Q1 Q2 a x) {Y : Subgroup G}
    (hY : IsCyclic Y) (hYD : Y ≤ D) (hYi : Y.relIndex D = 2)
    (hY4 : ∀ u ∈ D, u ∉ Y → u ^ 4 = 1) (hnab : ∃ u ∈ D, ∃ v ∈ D, u * v ≠ v * u) {u : G}
    (hu : u ∈ D) (huY : u ∉ Y) :
    ∃ U : Subgroup G, U ≤ D ⊔ (Q1 ⊔ Q2) ∧ z ∈ U ∧ IsElemAbelianMod z U ∧ Nat.card U = 128 ∧
      u ∈ U ∧ Q1 ⊔ Q2 ≤ U := by
  have hzc : ∀ x ∈ D, x * z = z * x := fun x hx => h.R_z x (h.D_le hx)
  obtain ⟨X, hXD, huX, hzX, hXel, hX8⟩ :=
    sec11c_exists_X_of_cyclic (h.R_two.to_le h.D_le) hYD hY hYi h.z_memD h.cnt.z_sq
      h.cnt.z_ne hzc hnab hu huY (hY4 u hu huY)
  have hXle8 : Nat.card X ≤ 8 := sec11c_card_le_eight hY hYD hYi h.cnt.z_sq hXD hXel
  have hXcard : Nat.card X = 8 := le_antisymm hXle8 hX8
  have hcomm : ∀ a ∈ X, ∀ b ∈ Q1 ⊔ Q2, a * b = b * a :=
    fun a ha b hb => h.D_Q a (hXD ha) b hb
  have hUel : IsElemAbelianMod z (X ⊔ (Q1 ⊔ Q2)) :=
    sec11_isElemAbelianMod_sup hcomm (fun a ha => hzc a (hXD ha))
      (fun b hb => h.cnt.z_cent b (h.Q_le_T hb)) hXel h.Q_el
  have hInf : X ⊓ (Q1 ⊔ Q2) = zpowers z := by
    apply le_antisymm
    · calc X ⊓ (Q1 ⊔ Q2) ≤ D ⊓ (Q1 ⊔ Q2) := inf_le_inf_right _ hXD
        _ = zpowers z := h.D_inf
    · exact Subgroup.zpowers_le.mpr ⟨hzX, h.z_memQ⟩
  have hzcard : Nat.card ↥(zpowers z) = 2 := by
    rw [Nat.card_zpowers,
      orderOf_eq_prime (p := 2) (by rw [pow_two]; exact h.cnt.z_sq) h.cnt.z_ne]
  have hcard_sup := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute X (Q1 ⊔ Q2) hcomm).1
  have hUcard : Nat.card ↥(X ⊔ (Q1 ⊔ Q2)) = 128 := by
    rw [hInf, hzcard, hXcard, h.card_Q] at hcard_sup
    omega
  exact ⟨X ⊔ (Q1 ⊔ Q2), sup_le (hXD.trans le_sup_left) le_sup_right, Subgroup.mem_sup_left hzX,
    hUel, hUcard, Subgroup.mem_sup_left huX, le_sup_right⟩

end Sec11cCnt

end CFSG.OddStandard.SmallF3.Omega
