module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ConeData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Cases
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Lin

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem commutator_mem_of_relIndex_le_two {M : Type*} [Group M] {H K : Subgroup M}
    (h : H.relIndex K ≤ 2) (h0 : H.relIndex K ≠ 0) {x y : M} (hx : x ∈ K)
    (hy : y ∈ K) : x * y * x⁻¹ * y⁻¹ ∈ H := by
  have hcases : H.relIndex K = 1 ∨ H.relIndex K = 2 := by omega
  rcases hcases with h1 | h2
  · have hKH := relIndex_eq_one.1 h1
    exact hKH (mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy))
  · have hi : (H.subgroupOf K).index = 2 := h2
    have key := (Subgroup.mul_mem_iff_of_index_two hi (a := ⟨x, hx⟩ * ⟨y, hy⟩)
      (b := (⟨x, hx⟩ : K)⁻¹ * (⟨y, hy⟩ : K)⁻¹)).2 (by
        rw [Subgroup.mul_mem_iff_of_index_two hi, Subgroup.mul_mem_iff_of_index_two hi,
          inv_mem_iff, inv_mem_iff])
    have : (⟨x, hx⟩ * ⟨y, hy⟩ * ((⟨x, hx⟩ : K)⁻¹ * (⟨y, hy⟩ : K)⁻¹) : K) ∈ H.subgroupOf K := key
    rw [mem_subgroupOf] at this
    simpa [mul_assoc] using this

theorem sum_zeroSet (ε : Eps) (w : V6) : ∃ v, qfV ε v = 0 ∧ qfV ε (v + w) = 0 := by
  have h : ∀ x < 64, ∃ y < 64, qfB ε y = false ∧ qfB ε (y ^^^ x) = false := by
    have hb : ((List.range 64).all fun x => (List.range 64).any fun y =>
        !qfB ε y && !qfB ε (y ^^^ x)) = true := by
      cases ε <;> decide
    simp only [List.all_eq_true, List.mem_range, List.any_eq_true, Bool.and_eq_true,
      Bool.not_eq_true'] at hb
    intro x hx
    obtain ⟨y, hy, h1, h2⟩ := hb x hx
    exact ⟨y, hy, h1, h2⟩
  obtain ⟨y, hy, h1, h2⟩ := h (vecBits w) (vecBits_lt w)
  refine ⟨toVec 6 y, ?_, ?_⟩
  · rw [qfV_eq_zero_iff, vecBits_toVec hy, h1]
  · rw [qfV_eq_zero_iff, ← toVec_vecBits w, ← toVec_xor, vecBits_toVec
      (Nat.xor_lt_two_pow (n := 6) hy (vecBits_lt w))]
    exact h2

theorem oBound_even (ε : Eps) : 2 * (oBound ε / 2) = oBound ε := by cases ε <;> rfl

variable {G : Type*} [Group G]

namespace Setup

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hS : Setup ε t L U Q P a ψ p)
include hS

theorem false_of_cone [Finite G] (hcone : ∀ v, v ∈ Zset t Q ψ ↔ qfV ε v = 0) : False := by
  classical
  set E : Subgroup G := Q ⊔ zpowers t
  have hsum : ∀ w, ∃ v ∈ Zset t Q ψ, ∃ v' ∈ Zset t Q ψ, v + v' = w := by
    intro w
    obtain ⟨v, hv, hvw⟩ := sum_zeroSet ε w
    refine ⟨v, (hcone v).2 hv, v + w, (hcone _).2 hvw, ?_⟩
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hNQ := hS.normalizer_E_le hsum
  set Φ := hS.affHom hNQ
  have hΦmem : Φ.range ≤ affGroup ε := by
    rintro _ ⟨g, rfl⟩
    refine ⟨fun v => ?_, fun x y z => ?_⟩
    · have h := hS.affF_mem_Zset_iff hNQ g.2 v
      rw [hcone, hcone] at h
      rcases qfV_cases ε v with h0 | h0
      · rw [h0]; exact h.2 h0
      · rw [h0]
        rcases qfV_cases ε (affF t ψ g v) with h1 | h1
        · exact absurd (h.1 h1) (by rw [h0]; exact one_ne_zero)
        · exact h1
    · change affF t ψ g (x + y + z) = affF t ψ g x + affF t ψ g y + affF t ψ g z
      rw [hS.affF_eq_add hNQ g.2 (x + y + z), hS.affF_eq_add hNQ g.2 x,
        hS.affF_eq_add hNQ g.2 y, hS.affF_eq_add hNQ g.2 z,
        hS.rad.lin_add (hNQ g.2), hS.rad.lin_add (hNQ g.2)]
      have key : ∀ a b c w : V6, w + (a + b + c) = w + a + (w + b) + (w + c) := by
        intro a b c w
        ext i
        simp only [Pi.add_apply]
        exact (by decide : ∀ a b c e : ZMod 2, e + (a + b + c) = e + a + (e + b) + (e + c)) _ _ _ _
      exact key _ _ _ _
  have hZcard : Nat.card (Zset t Q ψ) = (zeroSet ε).card := by
    have hset : Zset t Q ψ = ↑(zeroSet ε) := by
      ext v
      simp [zeroSet, hcone]
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hcardΦ : 2 * Nat.card Φ.range = (zeroSet ε).card * oBound ε := by
    have h1 := hS.card_range_affHom hNQ
    rw [hS.card_E, hS.card_normalizer_E, hZcard, hS.rad.card_P] at h1
    have h2 := oBound_even ε
    nlinarith
  have hidx : Φ.range.relIndex (affGroup ε) ≤ 2 := by
    have h := Subgroup.relIndex_mul_card (H := Φ.range) (K := affGroup ε)
    rw [inf_of_le_left hΦmem] at h
    have h3 := card_affGroup_le ε
    have hpos : 0 < Nat.card Φ.range := Nat.card_pos
    nlinarith
  have hidx0 : Φ.range.relIndex (affGroup ε) ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card (H := Φ.range) (K := affGroup ε)
    rw [h0, zero_mul] at h
    exact (Nat.card_pos (α := affGroup ε)).ne' h.symm
  obtain ⟨g, hg⟩ := commutator_mem_of_relIndex_le_two hidx hidx0 (coneXP_mem ε) (coneYP_mem ε)
  have hgc : ∀ v, affF t ψ g v = coneCommP ε v := fun v => by
    rw [← hS.affHom_apply hNQ, hg]
    rfl
  have hg0 : affF t ψ g 0 = 0 := by rw [hgc, coneComm_zero]
  have hgt : (g : G) * t = t * g := by
    have h := hS.t_affF hNQ g.2 0
    rw [hg0, hS.rad.ψ_zero, mul_one] at h
    calc (g : G) * t = g * t * (g : G)⁻¹ * g := by group
      _ = t * g := by rw [← h]
  have hgP : (g : G) ∈ P ⊔ zpowers t := by
    rw [← hS.shape.normalizer_eq]
    exact ⟨mem_centralizer_singleton_iff.2 hgt, g.2⟩
  obtain ⟨q, hqP, hgq⟩ := (hS.shape.mem_sup_iff hS.rad.P_le_L).1 hgP
  have htQ : t ∈ normalizer (Q : Set G) := hNQ (le_normalizer (t_mem_sup (X := Q)))
  have hlin : ∀ v, lin ψ g v = lin ψ q v := by
    intro v
    rcases hgq with h | h <;> rw [h]
    rw [hS.rad.lin_mul (hS.rad.P_le_normalizer hqP) htQ]
    congr 1
    rw [hS.rad.lin_eq_iff htQ, ← hS.commute_ψ v, mul_inv_cancel_right]
  have hfun : (coneCommP ε : V6 → V6) = lin ψ q := funext fun v => by
    rw [← hgc, hS.affF_eq_add hNQ g.2, hg0, zero_add, hlin]
  have hd := hS.rad.dickC_colsF_lin hqP
  rw [← hfun, colsF_coneComm, (coneCheck_spec ε).2.2.2] at hd
  exact Bool.noConfusion hd

theorem mem_Zset [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (v : V6) :
    v ∈ Zset t Q ψ :=
  (hS.Zset_cases hG hnab).elim (fun h => h v) fun h => (hS.false_of_cone h).elim

end Setup

end CFSG.EvenSmallLie.OmegaEight.Stage1
