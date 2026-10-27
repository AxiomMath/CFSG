module

public import CFSG.ClassicalInvolution.WeakCT.DLWeakAgree
public import CFSG.ClassicalInvolution.Asc77.AscSix63
public import CFSG.ClassicalInvolution.Asc77.WP2Stand

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Blueprint

variable (p f : ℕ) [Fact p.Prime]

@[expose] def LinearChain3 {G : Type} [Group G] (U : Fin 3 → Subgroup G) : Prop :=
  Commutes (U 0) (U 2) ∧ (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
    (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤

@[expose] def PhanChain3 {G : Type} [Group G] (U : Fin 3 → Subgroup G) : Prop :=
  ∃ V : Fin 3 → Fin 3 → Subgroup G, WeakPhanA (GaloisField p (2 * f)) p f 3 U V

variable {p f}

namespace T7C

theorem center_eq_bot_of_exists_not_commute {G : Type} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

noncomputable def centerQuotientEquivOfCenterEqBot {G : Type} [Group G]
    (h : Subgroup.center G = ⊥) : G ⧸ Subgroup.center G ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

theorem exists_not_commute_of_stand {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} (hs : AscStand p f Ω K) : ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  obtain ⟨x, -, y, -, hxy⟩ :=
    (hs.hyp.isQuatSub_of_mem_RSet hs.odd (mem_RSet_of_isSylow2In hs.mem hV)).exists_not_commute
  exact ⟨x, y, hxy⟩

end T7C

variable {G : Type} [Group G] [IsSimpleGroup G]

theorem oddLieType_of_linearChain3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hnab : ∃ a b : G, a * b ≠ b * a) {U : Fin 3 → Subgroup G} (h : LinearChain3 p f U) :
    OddLieType G := by
  obtain ⟨h02, h01, h12, hgen⟩ := h
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hcomm : ∀ i j : Fin 3, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x := by
    have key : ∀ i j : Fin 3, (i : ℕ) + 1 < j → i = 0 ∧ j = 2 := by decide
    intro i j hij
    obtain ⟨rfl, rfl⟩ := key i j hij
    exact h02
  have hpair : ∀ i j : Fin 3, (j : ℕ) = i + 1 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j) := by
    have key : ∀ i j : Fin 3, (j : ℕ) = i + 1 → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) := by decide
    intro i j hij
    rcases key i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h01
    · exact h12
  obtain ⟨-, -, -, -, hmodel⟩ := weakCT_recognition_of_pairs (GaloisField p f) p f Fact.out hK
    (by omega) (n := 3) (by norm_num) hcomm hpair hgen
  have hmodel' : LieModel G .PSL 4 p f :=
    lieModel_of_mulEquiv (T7C.centerQuotientEquivOfCenterEqBot
      (T7C.center_eq_bot_of_exists_not_commute hnab)) hmodel
  exact ⟨.PSL, 4, p, f, Fact.out, hp2, ⟨Fact.out, by omega, by norm_num, by simp [Prod.ext_iff],
    by simp [Prod.ext_iff]⟩, hmodel'⟩

theorem oddLieType_of_phanChain3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hnab : ∃ a b : G, a * b ≠ b * a) {U : Fin 3 → Subgroup G} (h : PhanChain3 p f U) :
    OddLieType G := by
  obtain ⟨V, hV⟩ := h
  have hf : 2 * f ≠ 0 := by
    rintro h0
    have : f = 0 := by omega
    subst this
    simp at hq
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) hf, ← pow_mul, mul_comm]
  exact (weakPhan_simple_native_recognition (GaloisField p (2 * f)) p f hK hp2 hq (n := 3)
    (by norm_num) hnab hV).2

theorem oddLieType_of_symplecticPair (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hnab : ∃ a b : G, a * b ≠ b * a) {W U V : Subgroup G}
    (h : SymplecticBlockPair (GaloisField p f) W U V) (hgen : U ⊔ V = ⊤) : OddLieType G := by
  obtain ⟨θ, c, hrange, hker, -, hU, hV⟩ := h
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hUle : U ≤ θ.range := hU ▸ Subgroup.map_le_range θ _
  have hVle : V ≤ θ.range := hV ▸ Subgroup.map_le_range θ _
  have hsurj : Function.Surjective θ :=
    MonoidHom.range_eq_top.mp (eq_top_iff.mpr (hgen ▸ sup_le hUle hVle))
  have hcen : Subgroup.center G = ⊥ := T7C.center_eq_bot_of_exists_not_commute hnab
  have hkerc : θ.ker = Subgroup.center (StatedSp 2 (GaloisField p f)) := by
    refine le_antisymm hker fun x hx => ?_
    rw [MonoidHom.mem_ker]
    have : θ x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := hsurj g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
    rwa [hcen, Subgroup.mem_bot] at this
  have hadm : StatedLieAdmissible .PSp 2 p f := by
    refine ⟨Fact.out, by omega, by norm_num, ?_⟩
    simp [Prod.ext_iff]
    omega
  have e : StatedSp 2 (GaloisField p f) ⧸ Subgroup.center (StatedSp 2 (GaloisField p f)) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hkerc.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hsurj)
  have hmodel := statedClassicalModel_of_mulEquiv e
    (CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient 2 (GaloisField p f)
      hadm hF)
  exact ⟨.PSp, 2, p, f, Fact.out, hp2, hadm, Or.inl ⟨by decide, hmodel⟩⟩

end CFSG.ClassicalInvolution.Asc77
