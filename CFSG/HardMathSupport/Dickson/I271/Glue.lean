module

public import CFSG.HardMathSupport.Dickson.I271.Support.CenterLift
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_PartIIExists
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open scoped commutatorElement

section Perfect

theorem commutatorElement_mul_central {G : Type*} [Group G] {a b z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hc : ∀ g : G, z * g * z⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hz g]; group
  have hc' : ∀ g : G, w * g * w⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hw g]; group
  calc ⁅a * z, b * w⁆ = a * (z * (b * w) * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = a * (b * w) * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hc]
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hc' a⁻¹]
    _ = ⁅a, b⁆ := by simp only [commutatorElement_def]

theorem eq_top_of_sup_center_eq_top {G : Type*} [Group G] {H : Subgroup G}
    (hperf : commutator G = ⊤) (h : H ⊔ Subgroup.center G = ⊤) : H = ⊤ := by
  rw [eq_top_iff, ← hperf]
  show ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ H
  rw [Subgroup.commutator_le]
  have hmem : ∀ g : G, g ∈ H ⊔ Subgroup.center G := fun g => by
    rw [h]; exact Subgroup.mem_top g
  intro g₁ _ g₂ _
  obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (hmem g₁)
  obtain ⟨a₂, ha₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (hmem g₂)
  rw [commutatorElement_mul_central hz₁ hz₂, commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha₁ ha₂) (H.inv_mem ha₁)) (H.inv_mem ha₂)

end Perfect

section Closure

variable {X : Type} [Group X] [Finite X]

theorem le_coreIn_of_fixed {p : ℕ} {B K : Subgroup X} (hperf : commutator ↥K = ⊤)
    (hlift : CenterLift B K) (Fam : Set (Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))))
    (hrank : ∀ P ∈ Fam, 3 ≤ CFSG.Open.pRank p (actPre B K P))
    (hgen : Subgroup.closure
      {s : ↥K ⧸ Subgroup.center ↥K | ∃ P ∈ Fam, ∀ e ∈ P, e s = s} = ⊤) :
    K ≤ coreIn p 3 B K := by
  set Γ : Subgroup X := coreIn p 3 B K with hΓ
  set Γ₀ : Subgroup ↥K := Γ.subgroupOf K with hΓ₀
  set S : Set (↥K ⧸ Subgroup.center ↥K) := {s | ∃ P ∈ Fam, ∀ e ∈ P, e s = s} with hS
  have hlift' : ∀ s ∈ S, ∃ k ∈ Γ₀, (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) = s := by
    rintro s ⟨P, hP, hs⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨k, ?_, rfl⟩
    have hnorm := mem_normalizer_actPre hlift hs
    show (k : X) ∈ Γ
    have hle : K ⊓ Subgroup.normalizer (actPre B K P : Set X) ≤ Γ :=
      le_iSup₂_of_le (f := fun (Q : Subgroup X) (_ : Q ≤ B ∧ 3 ≤ CFSG.Open.pRank p Q) =>
        K ⊓ Subgroup.normalizer (Q : Set X)) (actPre B K P) ⟨actPre_le_left, hrank P hP⟩ le_rfl
    exact hle ⟨k.2, hnorm⟩
  have hle : Subgroup.closure S ≤ Γ₀.map (QuotientGroup.mk' (Subgroup.center ↥K)) := by
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨k, hk, rfl⟩ := hlift' s hs
    exact ⟨k, hk, rfl⟩
  have hsup : Γ₀ ⊔ Subgroup.center ↥K = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : (QuotientGroup.mk g : ↥K ⧸ Subgroup.center ↥K) ∈ Subgroup.closure S := by
      rw [hgen]; exact Subgroup.mem_top _
    obtain ⟨γ, hγ, hγg⟩ := hle hg
    have hz : γ⁻¹ * g ∈ Subgroup.center ↥K := QuotientGroup.eq.1 hγg
    have : g = γ * (γ⁻¹ * g) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hγ hz
  have htop : Γ₀ = ⊤ := eq_top_of_sup_center_eq_top hperf hsup
  intro x hx
  have : (⟨x, hx⟩ : ↥K) ∈ Γ₀ := by rw [htop]; exact Subgroup.mem_top _
  exact this

theorem pRank_actPre {p : ℕ} (hp : p.Prime) {B K : Subgroup X} (hBel : IsElemAbelian p B)
    (hperf : commutator ↥K = ⊤) {P : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))}
    (hP : P ≤ autImage B K) {r : ℕ} (hr : Nat.card P = p ^ r) :
    CFSG.Open.pRank p (actPre B K P) =
      CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (K : Set X)) + r := by
  have hCel : IsElemAbelian p (B ⊓ Subgroup.centralizer (K : Set X)) :=
    i271_isElemAbelian_of_le hBel inf_le_left
  obtain ⟨c, hc⟩ := i271_exists_card_eq hp hCel
  have hcard : Nat.card (actPre B K P) = p ^ (c + r) := by
    rw [card_actPre hperf hP, hc, hr, pow_add]
  rw [i271_pRank_eq hp (isElemAbelian_actPre P hBel) hcard, i271_pRank_eq hp hCel hc]

theorem one_le_pRank_centralizer {p : ℕ} (hp : p.Prime) {B K : Subgroup X}
    (hBel : IsElemAbelian p B) (h : B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥) :
    1 ≤ CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (K : Set X)) := by
  have hCel : IsElemAbelian p (B ⊓ Subgroup.centralizer (K : Set X)) :=
    i271_isElemAbelian_of_le hBel inf_le_left
  obtain ⟨c, hc⟩ := i271_exists_card_eq hp hCel
  rw [i271_pRank_eq hp hCel hc]
  by_contra h0
  have : c = 0 := by omega
  rw [this, pow_zero] at hc
  exact h (Subgroup.eq_bot_of_card_eq _ hc)

theorem centerLift_of_hyp {p : ℕ} {K B : Subgroup X} (hH : I271Hyp p K B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hZ : CFSG.Open.pRank p (Subgroup.center ↥K) ≤ 1) : CenterLift B K :=
  centerLift_of_pRank_le_one hH.prime hH.odd hH.scp hBN
    (i271h_center_isPGroup hH.prime (i271h_primeCore_eq_bot hH.core hH.comp)) hZ

end Closure

section GOne

variable {X : Type} [Group X] [Finite X]

theorem caseA_of_planeGen {p : ℕ} {K B : Subgroup X} (hH : I271Hyp p K B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hc : 2 ≤ CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (K : Set X)))
    (hZ : CFSG.Open.pRank p (Subgroup.center ↥K) ≤ 1)
    (E : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))) (hE : E ≤ autImage B K)
    (hEel : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hgen : Subgroup.closure {s : ↥K ⧸ Subgroup.center ↥K | ∃ e ∈ E, e ≠ 1 ∧ e s = s} = ⊤) :
    I271CaseA p K B := by
  haveI : Fact p.Prime := ⟨hH.prime⟩
  have hperf : commutator ↥K = ⊤ := (i116e_isQuasisimple hH.core hH.comp).1
  have hlift := centerLift_of_hyp hH hBN hZ
  have hBel : IsElemAbelian p B := hH.scp.2.1
  refine ⟨hH.rank_four, i271h_isInGOne_of_le hBN ?_⟩
  refine le_coreIn_of_fixed hperf hlift {P | ∃ e ∈ E, e ≠ 1 ∧ P = Subgroup.zpowers e} ?_ ?_
  · rintro P ⟨e, he, hne, rfl⟩
    have hP : Subgroup.zpowers e ≤ autImage B K := (Subgroup.zpowers_le).2 (hE he)
    have hcard : Nat.card (Subgroup.zpowers e) = p ^ 1 := by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (hEel.2 e he) hne
    rw [pRank_actPre hH.prime hBel hperf hP hcard]
    omega
  · rw [eq_top_iff, ← hgen]
    apply Subgroup.closure_mono
    rintro s ⟨e, he, hne, hs⟩
    refine ⟨Subgroup.zpowers e, ⟨e, he, hne, rfl⟩, ?_⟩
    intro e' he'
    have : Subgroup.zpowers e ≤ MulAction.stabilizer (MulAut (↥K ⧸ Subgroup.center ↥K)) s :=
      (Subgroup.zpowers_le).2 (by rw [MulAction.mem_stabilizer_iff]; exact hs)
    exact MulAction.mem_stabilizer_iff.1 (this he')

theorem caseA_of_hyperGen3 {p : ℕ} {K B : Subgroup X} (hH : I271Hyp p K B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hZ : CFSG.Open.pRank p (Subgroup.center ↥K) ≤ 1)
    (E : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))) (hE : E ≤ autImage B K)
    (hEcard : Nat.card E = p ^ 3)
    (hgen : Subgroup.closure {s : ↥K ⧸ Subgroup.center ↥K |
      ∃ F ≤ E, F.relIndex E = p ∧ ∀ f ∈ F, f s = s} = ⊤) :
    I271CaseA p K B := by
  haveI : Fact p.Prime := ⟨hH.prime⟩
  have hperf : commutator ↥K = ⊤ := (i116e_isQuasisimple hH.core hH.comp).1
  have hlift := centerLift_of_hyp hH hBN hZ
  have hBel : IsElemAbelian p B := hH.scp.2.1
  refine ⟨hH.rank_four, i271h_isInGOne_of_le hBN ?_⟩
  refine le_coreIn_of_fixed hperf hlift {F | F ≤ E ∧ F.relIndex E = p} ?_ ?_
  · rintro F ⟨hFE, hFi⟩
    have hFcard : Nat.card F = p ^ 2 := by
      have h := Subgroup.relIndex_mul_card F E
      rw [inf_of_le_left hFE, hFi, hEcard] at h
      have hp0 : 0 < p := hH.prime.pos
      have : p * Nat.card F = p * p ^ 2 := by rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_left hp0 this
    rw [pRank_actPre hH.prime hBel hperf (hFE.trans hE) hFcard]
    have := one_le_pRank_centralizer hH.prime hBel hH.centralized
    omega
  · have hset : {s : ↥K ⧸ Subgroup.center ↥K | ∃ P ∈ {F : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)) |
        F ≤ E ∧ F.relIndex E = p}, ∀ e ∈ P, e s = s} =
        {s : ↥K ⧸ Subgroup.center ↥K | ∃ F ≤ E, F.relIndex E = p ∧ ∀ f ∈ F, f s = s} := by
      ext s
      constructor
      · rintro ⟨F, ⟨h1, h2⟩, h3⟩
        exact ⟨F, h1, h2, h3⟩
      · rintro ⟨F, h1, h2, h3⟩
        exact ⟨F, ⟨h1, h2⟩, h3⟩
    rw [hset]
    exact hgen

end GOne

end CFSG.HardMathSupport.Dickson.I271
