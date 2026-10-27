module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx4

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

theorem equiv_of_card_eq_quaternion {X Y : Type} [Group X] [Group Y] {n m : ℕ}
    (hX : IVK.IsQuaternionTwoGroup X n) (hY : IVK.IsQuaternionTwoGroup Y m)
    (h : Nat.card X = Nat.card Y) : Nonempty (X ≃* Y) := by
  obtain ⟨hn, ⟨eX⟩⟩ := hX
  obtain ⟨hm, ⟨eY⟩⟩ := hY
  haveI : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  haveI : NeZero (2 ^ (m - 2)) := ⟨by positivity⟩
  have h1 : Nat.card X = 4 * 2 ^ (n - 2) := by rw [Nat.card_congr eX.toEquiv, Basic.card_quat]
  have h2 : Nat.card Y = 4 * 2 ^ (m - 2) := by rw [Nat.card_congr eY.toEquiv, Basic.card_quat]
  have h3 : 2 ^ (n - 2) = 2 ^ (m - 2) := by omega
  have h4 : n - 2 = m - 2 := Nat.pow_right_injective (le_refl 2) h3
  have : n = m := by omega
  subst this
  exact ⟨eX.trans eY.symm⟩

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem quatP (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) : ∃ n, IVK.IsQuaternionTwoGroup ↥(Pof S K) n := by
  have hstd := hs.fused.std
  exact hq G hstd.simple z hstd.orderOf_z S K hstd.sylow (hstd.comp_isPCompIn hK)
    (hstd.comp_pRank hK)

theorem V₁_cyclic (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : IsCyclic ↥(Vof S K₁ W₂) :=
  Basic.isCyclic_of_le inf_le_left hs.W₂_max.2.1

theorem V₁h_cyclic (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    IsCyclic ↥(conjugate (Vof S K₁ W₂) h) := by
  rw [conjugate_eq_comap]
  exact Basic.cyclic_comap_conj _ hs.V₁_cyclic h

theorem V₁h_card (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    2 * Nat.card ↥(conjugate (Vof S K₁ W₂) h) = Nat.card ↥(Pof S K₁) := by
  rw [conjugate_eq_comap, Basic.card_comap_conj]
  exact hs.card_V₁ hII hq

theorem V₁h_inf_Q (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) : conjugate (Vof S K₁ W₂) h ⊓ Qof S K = ⊥ := by
  have hQ : Basic.GQ (Qof S K) z := by
    rcases hK with rfl | rfl
    · exact hs.gq_Q₁ hII
    · exact hs.gq_Q₂ hII
  refine Basic.conj_inf_bot (P := Pof S K₁) (Q := Qof S K) (V₁ := Vof S K₁ W₂) ?_ hQ.uniq
    inf_le_right hs.h_move (fun x => mem_conjugate_iff) ?_
  · exact (hs.gq_P hII hq (Or.inl rfl)).uniq
  · exact (hs.S_pgroup hII).to_le ((inf_le_right : conjugate (Vof S K₁ W₂) h ⊓ Qof S K ≤ Qof S K).trans
      inf_le_left)

theorem embed_Q₂ (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Nat.card ↥(Pof S K₁) * Nat.card ↥(Qof S K₂) ≤ Nat.card ↥(S1 S K₁) := by
  obtain ⟨hN, hnc⟩ := hs.nc_quot (K := K₂) (Or.inr rfl)
  have := @Basic.two_mul_card_mul_card_le G _ _ (S1 S K₁) (Qof S K₂) (conjugate (Vof S K₁ W₂) h)
    hN (hs.S1_pgroup hII) (hs.Q₂_le_S1 hII) hnc hs.V₁h_cyclic (hs.V₁h_le_S1 hII hq hrec)
    (hs.V₁h_inf_Q hII hq (Or.inr rfl))
  rw [hs.V₁h_card hII hq] at this
  exact this

theorem e_of_a4 (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    {e₁ e₂ : ℕ} (he₁ : e₁ = 1 ∨ e₁ = 2) (he₂ : e₂ = 1 ∨ e₂ = 2)
    (hq₁ : Nat.card ↥(Qof S K₁) = e₁ * Nat.card ↥(Pof S K₂))
    (hq₂ : Nat.card ↥(Qof S K₂) = e₂ * Nat.card ↥(Pof S K₁))
    (h4 : (Pz S z).relIndex (S1 S K₁) = 4) : e₁ = 2 ∧ e₂ = 2 := by
  have h1 := hs.two_mul_card_S1_of_four hII h4
  obtain ⟨-, hcard⟩ := hs.card_S1 hII
  rw [h4] at hcard
  have hP := hs.card_P hII
  rw [hq₁, hq₂] at h1
  have hpos : 0 < Nat.card ↥(Pof S K₁) * Nat.card ↥(Pof S K₂) := by
    have : 0 < Nat.card ↥(Pof S K₁) := Nat.card_pos
    have : 0 < Nat.card ↥(Pof S K₂) := Nat.card_pos
    positivity
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl <;> constructor <;> first | rfl | (exfalso; nlinarith)

theorem lemma82_core (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ (Pz S z).relIndex (S1 S K₁) = 2 * e ∧
      Nat.card ↥(Pof S K₁) = Nat.card ↥(Pof S K₂) ∧
      Nat.card ↥(Qof S K₁) = e * Nat.card ↥(Pof S K₂) ∧
      Nat.card ↥(Qof S K₂) = e * Nat.card ↥(Pof S K₁) := by
  obtain ⟨e₂, he₂, hq₂⟩ := hs.card_Q₂ hII
  obtain ⟨e₁, he₁, hq₁⟩ := hs.card_Q₁ hII
  obtain ⟨ha, hcard⟩ := hs.card_S1 hII
  have hemb := hs.embed_Q₂ hII hq hrec
  have hP := hs.card_P hII
  have hN₂ : 0 < Nat.card ↥(Pof S K₂) := Nat.card_pos
  have hord := hs.fused.ord₁
  have ha4 : (Pz S z).relIndex (S1 S K₁) = 4 → e₂ = 2 := fun h4 =>
    (hs.e_of_a4 hII he₁ he₂ hq₁ hq₂ h4).2
  obtain ⟨hae, hNN⟩ := Basic.numeric82 (N₁ := Nat.card ↥(Pof S K₁)) (N₂ := Nat.card ↥(Pof S K₂))
    (q₂ := Nat.card ↥(Qof S K₂)) (s₁ := Nat.card ↥(S1 S K₁)) (p := Nat.card ↥(Pz S z))
    (e₂ := e₂) (a := (Pz S z).relIndex (S1 S K₁)) hord hN₂ (by omega) hq₂ hcard he₂ ha ha4 hemb
  have hiso : Nonempty (↥(Pof S K₁) ≃* ↥(Pof S K₂)) := by
    obtain ⟨n₁, hn₁⟩ := hs.quatP hq (Or.inl rfl)
    obtain ⟨n₂, hn₂⟩ := hs.quatP hq (Or.inr rfl)
    exact equiv_of_card_eq_quaternion hn₁ hn₂ hNN
  have hQle := hs.fused.ord₂ hiso
  rw [hq₁, hq₂, ← hNN] at hQle
  have hN₁ : 0 < Nat.card ↥(Pof S K₁) := by rw [hNN]; exact hN₂
  have he₁₂ : e₁ ≤ e₂ := Nat.le_of_mul_le_mul_right hQle hN₁
  have hee : e₁ = e₂ := by
    rcases he₂ with rfl | rfl
    · omega
    · have h4 : (Pz S z).relIndex (S1 S K₁) = 4 := by omega
      exact (hs.e_of_a4 hII he₁ (Or.inr rfl) hq₁ hq₂ h4).1
  refine ⟨e₂, he₂, hae, hNN, ?_, hq₂⟩
  rw [hq₁, hee]

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
