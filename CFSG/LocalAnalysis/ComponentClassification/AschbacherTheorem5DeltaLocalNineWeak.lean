module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalNineTwo
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeaklyClosed
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalEightThree

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal.Nine

open SectionSix SectionSix.BarTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem isSylowOf_sup_sylow {N X S : Subgroup G} (hX2 : IsPGroup 2 X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hNX : N ⊓ X = ⊥) (hS : IsSylowOf 2 S N)
    (hXS : S ≤ Subgroup.normalizer (X : Set G)) : IsSylowOf 2 (X ⊔ S) (N ⊔ X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXSbot : X ⊓ S = ⊥ :=
    le_bot_iff.mp (by rw [inf_comm]; exact (inf_le_inf_right X hS.le).trans hNX.le)
  have hle : X ⊔ S ≤ N ⊔ X := sup_le le_sup_right (hS.le.trans le_sup_left)
  rw [isSylowOf_iff]
  refine ⟨hle, IsPGroup.to_sup_of_normal_left' hX2 hS.isPGroup hXS, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (X ⊔ S) (N ⊔ X)
  rw [inf_eq_left.mpr hle, AschbacherTheorem3.card_sup_of_le_normalizer hXS hXSbot,
    AschbacherTheorem3.card_sup_of_le_normalizer hXN hNX] at h1
  have h2 := Subgroup.relIndex_mul_card S N
  rw [inf_eq_left.mpr hS.le] at h2
  have h3 : (X ⊔ S).relIndex (N ⊔ X) = S.relIndex N := by
    have hpos : 0 < Nat.card X * Nat.card S := Nat.mul_pos Nat.card_pos Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc (X ⊔ S).relIndex (N ⊔ X) * (Nat.card X * Nat.card S) = Nat.card N * Nat.card X := h1
      _ = S.relIndex N * Nat.card S * Nat.card X := by rw [h2]
      _ = S.relIndex N * (Nat.card X * Nat.card S) := by ring
  rw [h3]
  exact (isSylowOf_iff.mp hS).2.2

theorem exists_weak (hC : Counterexample G D r Abar) {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) {a m : Fin r} {X S : Subgroup G}
    (hX2 : IsPGroup 2 X) (hXH : X ≤ Subgroup.normalizer (D : Set G)) (hX1 : X ≠ ⊥)
    (hXm : X ≤ orbitProduct (rightConjugate D g) (conjFactors D Abar g) {j | j ≠ m})
    (hXA : X ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
    (hS : IsSylowOf 2 S (aschbacherThm5Preimage D (Abar a)))
    (hXS : ∀ x ∈ X, ∀ s ∈ S, x * s = s * x) :
    ∃ y ∈ aschbacherThm5Preimage D (Abar a), rightConjugate X y ≤ X ⊔ S ∧
      rightConjugate X y ≠ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  have hAD : A ≤ D := preimage_le D _
  have hAH : A ≤ Subgroup.normalizer (D : Set G) := hAD.trans Subgroup.le_normalizer
  have hOA : aschbacherThm5Core D ≤ A := core_le_preimage D _
  have hSH : S ≤ Subgroup.normalizer (D : Set G) := hS.le.trans hAH
  have hXAbot : X ⊓ A = ⊥ := inf_orbitProduct_eq_bot hC hg hX2 hXm
  have hSX : S ≤ Subgroup.normalizer (X : Set G) := by
    refine le_trans (fun s hs => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    exact fun x hx => hXS x hx s hs
  have hsyl := isSylowOf_sup_sylow hX2 hXA (by rw [inf_comm]; exact hXAbot) hS hSX
  have hsylb := isSylowOf_bar hsyl (sup_le hAH hXH)
  rw [bar_sup hXH hSH, bar_sup hAH hXH] at hsylb
  have hF : AschbacherTheorem3.Frame (bar D A) (bar D X) :=
    ⟨bar_le_normalizer hXA hAH, by
      rw [← bar_inf_of_core_le hOA, hXAbot, bar, Subgroup.bot_subgroupOf, Subgroup.map_bot],
      isPGroup_bar hX2⟩
  have hXSN : bar D X ⊔ bar D S ≤ Subgroup.normalizer (bar D X : Set (Bar D)) :=
    sup_le Subgroup.le_normalizer (bar_le_normalizer hSX hXH)
  have hSF : AschbacherTheorem3.SylowFrame (bar D A) (bar D X) (bar D X ⊔ bar D S) :=
    { toFrame := hF
      sylow := hsylb
      sylow_normalizer := by
        rw [inf_eq_left.mpr hXSN]
        exact hsylb.of_le (le_inf hsylb.le hXSN) inf_le_left }
  have hO := oddCore_bar_eq_bot hAD (Eight.le_normalizer_factor hC a)
  by_contra hno
  push Not at hno
  have hwc : ∀ yb ∈ bar D A, rightConjugate (bar D X) yb ≤ bar D X ⊔ bar D S →
      rightConjugate (bar D X) yb = bar D X := by
    intro yb hyb hle
    obtain ⟨y₀, hy₀A, rfl⟩ := (mem_bar_iff D A yb).mp hyb
    rw [← bar_rightConjugate] at hle ⊢
    have hle' := le_sup_core_of_bar_le (rightConjugate_le_normalizer hXH y₀)
      (hle.trans (le_of_eq (bar_sup hXH hSH).symm))
    obtain ⟨o, ho, hRo⟩ := le_rightConjugate_of_le_sup_core (sup_le hXH hSH)
      (AschbacherTheorem3.isPGroup_rightConjugate hX2 y₀) hle'
    have hoH : o ∈ Subgroup.normalizer (D : Set G) := core_le_normalizer D ho
    have hy : (y₀ : G) * o⁻¹ ∈ A := A.mul_mem hy₀A (A.inv_mem (hOA ho))
    have hXy : rightConjugate X ((y₀ : G) * o⁻¹) ≤ X ⊔ S := by
      have := AschbacherTheorem3.rightConjugate_le_rightConjugate hRo o⁻¹
      rwa [rightConjugate_mul, rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this
    have heq := hno _ hy hXy
    have hsplit : rightConjugate X (y₀ : G) =
        rightConjugate (rightConjugate X ((y₀ : G) * o⁻¹)) o := by
      rw [rightConjugate_mul, inv_mul_cancel_right]
    rw [hsplit, heq]
    have h1 := bar_rightConjugate X ⟨o, hoH⟩
    rw [show toBar D ⟨o, hoH⟩ = 1 from (toBar_eq_one_iff D _).mpr ho, rightConjugate_one] at h1
    exact h1
  have hcomm := AschbacherTheorem3.lemma_4_2 hSF hwc hO
  apply hX1
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨n, hn⟩ := hX2 ⟨x, hx⟩
  have hxC : toBar D ⟨x, hXH hx⟩ ∈ Subgroup.centralizer (bar D A : Set (Bar D)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 := Subgroup.commutator_mem_commutator hz (toBar_mem_bar D (h := ⟨x, hXH hx⟩) hx)
    rw [hcomm, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1)
  have hC' := hC.conj g
  apply hg
  exact SixTools.mem_normalizer_of_fusion_conj hC (g := g) (y := x)
    ⟨n, by simpa using congrArg Subtype.val hn⟩ hx1
    ((centralizes_iff_mem_centralizer D A hAD ⟨x, hXH hx⟩).mpr hxC)
    (centralizes_of_mem_centralizing ((orbitProduct_le_centralizing hC'.hyp.hcomm
      (j := m) (by simp)) (hXm hx)))

end DeltaLocal.Nine

end CFSG.ComponentClassification.AschbacherTheorem5
