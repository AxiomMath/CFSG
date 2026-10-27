module

public import Mathlib.GroupTheory.PGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.MinimalInvariantCommutator

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup
open scoped commutatorElement

structure HHMinimal {K : Type*} [Group K] (B Q : Subgroup K) : Prop where
  normalizes : B ≤ normalizer (Q : Set K)
  nontrivial : ⁅Q, B⁆ ≠ ⊥
  minimal : ∀ R : Subgroup K, R ≤ Q → B ≤ normalizer (R : Set K) → ⁅R, B⁆ ≠ ⊥ → Q ≤ R

theorem exists_hhMinimal {K : Type*} [Group K] [Finite K] {A B : Subgroup K}
    (hBA : B ≤ normalizer (A : Set K)) (hne : ⁅A, B⁆ ≠ ⊥) :
    ∃ Q : Subgroup K, Q ≤ A ∧ HHMinimal B Q := by
  let S : Set (Subgroup K) := {R | R ≤ A ∧ B ≤ normalizer (R : Set K) ∧ ⁅R, B⁆ ≠ ⊥}
  have hSne : S.Nonempty := ⟨A, le_rfl, hBA, hne⟩
  obtain ⟨Q, hQ⟩ := S.toFinite.exists_minimalFor id S hSne
  refine ⟨Q, hQ.1.1, hQ.1.2.1, hQ.1.2.2, fun R hRQ hBR hRne => ?_⟩
  exact hQ.2 ⟨hRQ.trans hQ.1.1, hBR, hRne⟩ hRQ

namespace HHMinimal

variable {K : Type*} [Group K] [Finite K] {B Q : Subgroup K} {d : ℕ}

theorem commutator_eq (h : HHMinimal B Q) (hd : d.Prime) (hd3 : d ≠ 3) (hQ : IsPGroup 3 Q)
    (hB : IsPGroup d B) : ⁅Q, B⁆ = Q := by
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime (Nat.card B) (Nat.card Q) :=
    IsPGroup.coprime_card_of_ne d 3 hd3 B Q hB hQ
  exact GorensteinWalter.commutator_eq_self_of_minimal_invariant_coprime B Q B
    h.normalizes le_normalizer h.normalizes hcop h.nontrivial h.minimal

theorem commutator_self_le_centralizer (h : HHMinimal B Q) (hQ : IsPGroup 3 Q) :
    ⁅Q, Q⁆ ≤ centralizer (B : Set K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRQ : ⁅Q, Q⁆ ≤ Q := Subgroup.commutator_le_self Q
  have hBR : B ≤ normalizer ((⁅Q, Q⁆ : Subgroup K) : Set K) :=
    GorensteinWalter.le_normalizer_commutator_of_le_normalizer B Q Q h.normalizes h.normalizes
  have hQne : Q ≠ ⊥ := by
    intro hbot
    exact h.nontrivial (by rw [hbot, Subgroup.commutator_bot_left])
  haveI : Group.IsNilpotent ↥Q := hQ.isNilpotent
  haveI : Group.IsSolvable ↥Q := inferInstance
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  have hlt : ⁅Q, Q⁆ < Q := by
    have hcom : _root_.commutator ↥Q < ⊤ :=
      Group.IsSolvable.commutator_lt_top_of_nontrivial ↥Q
    have hmap := (Subgroup.map_subtype_lt_map_subtype (G' := Q)
      (H := _root_.commutator ↥Q) (K := ⊤)).mpr hcom
    rwa [Subgroup.map_subtype_commutator, Subgroup.map_top, Subgroup.range_subtype] at hmap
  have hbot : ⁅⁅Q, Q⁆, B⁆ = ⊥ := by
    by_contra hne'
    exact (lt_iff_le_not_ge.mp hlt).2 (h.minimal ⁅Q, Q⁆ hRQ hBR hne')
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot

theorem commutator_self_le_centralizer_self (h : HHMinimal B Q) (hd : d.Prime) (hd3 : d ≠ 3)
    (hQ : IsPGroup 3 Q) (hB : IsPGroup d B) : ⁅Q, Q⁆ ≤ centralizer (Q : Set K) := by
  have hcomm : ⁅Q, B⁆ = Q := h.commutator_eq hd hd3 hQ hB
  have hB' : ⁅Q, Q⁆ ≤ centralizer (B : Set K) := h.commutator_self_le_centralizer hQ
  have h1le : ⁅Q, ⁅Q, Q⁆⁆ ≤ ⁅Q, Q⁆ :=
    (Subgroup.le_normalizer_iff_commutator_le_right).mp (Subgroup.normalizer_commutator_ge_left Q Q)
  have h1 : ⁅⁅Q, ⁅Q, Q⁆⁆, B⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (h1le.trans hB')
  have hP'A : ⁅⁅Q, Q⁆, B⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hB'
  have h2 : ⁅⁅⁅Q, Q⁆, B⁆, Q⁆ = ⊥ := by rw [hP'A, Subgroup.commutator_bot_left]
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := B) (H₂ := Q)
    (H₃ := ⁅Q, Q⁆) h1 h2
  rw [Subgroup.commutator_comm B Q, hcomm] at h3
  rw [Subgroup.commutator_comm Q ⁅Q, Q⁆] at h3
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3

theorem pow_three_mem_centralizer (h : HHMinimal B Q) (hQ : IsPGroup 3 Q) :
    ∀ x ∈ Q, x ^ 3 ∈ centralizer (B : Set K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQne : Q ≠ ⊥ := by
    intro hbot
    exact h.nontrivial (by rw [hbot, Subgroup.commutator_bot_left])
  haveI : Group.IsNilpotent ↥Q := hQ.isNilpotent
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  let S : Set K := {y | ∃ x ∈ Q, y = x ^ 3}
  let R : Subgroup K := Subgroup.closure S
  have hRQ : R ≤ Q := by
    show Subgroup.closure S ≤ Q
    rw [Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    exact Q.pow_mem hx 3
  have hBR : B ≤ normalizer (R : Set K) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show (Subgroup.closure S).map (MulAut.conj b) = Subgroup.closure S
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hz
      refine ⟨b * x * b⁻¹, (Subgroup.mem_normalizer_iff.mp (h.normalizes hb) x).1 hx, ?_⟩
      rw [map_pow]
      show (b * x * b⁻¹) ^ 3 = (b * x * b⁻¹) ^ 3
      rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(MulAut.conj b)⁻¹ (x ^ 3), ⟨(MulAut.conj b)⁻¹ x, ?_, map_pow _ x 3⟩, ?_⟩
      · rw [MulAut.conj_inv_apply]
        simpa using (Subgroup.mem_normalizer_iff.mp (h.normalizes (inv_mem hb)) x).1 hx
      · show b * (b⁻¹ * x ^ 3 * b) * b⁻¹ = x ^ 3
        group
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (α := Subgroup ↥Q)
  have hNnormal : N.Normal :=
    NormalizerCondition.normal_of_coatom N
      (Group.normalizerCondition_of_isNilpotent (G := ↥Q)) hN
  haveI : N.Normal := hNnormal
  have hNindex : N.index = 3 :=
    (IsPGroup.isCoatom_iff_index_eq_prime (p := 3) hQ).mp hN
  have hsub : R ≤ N.map (Subgroup.subtype Q) := by
    show Subgroup.closure S ≤ N.map (Subgroup.subtype Q)
    rw [Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    refine ⟨(⟨x, hx⟩ : ↥Q) ^ 3, ?_, by simp⟩
    have hxN := N.pow_index_mem (⟨x, hx⟩ : ↥Q)
    rwa [hNindex] at hxN
  have hNlt : N.map (Subgroup.subtype Q) < Q := by
    have hmap := (Subgroup.map_subtype_lt_map_subtype (G' := Q) (H := N) (K := ⊤)).mpr hN.lt_top
    rwa [Subgroup.map_top, Subgroup.range_subtype] at hmap
  have hRlt : R < Q := lt_of_le_of_lt hsub hNlt
  have hne : ⁅R, B⁆ = ⊥ := by
    by_contra hne'
    exact (lt_iff_le_not_ge.mp hRlt).2 (h.minimal R hRQ hBR hne')
  have hcent : R ≤ centralizer (B : Set K) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hne
  intro x hx
  exact hcent (Subgroup.subset_closure ⟨x, hx, rfl⟩)

theorem inf_centralizer_le_of_not_comm (h : HHMinimal B Q)
    (hnc : ¬ ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) :
    Q ⊓ centralizer (Q : Set K) ≤ centralizer (B : Set K) := by
  let R : Subgroup K := Q ⊓ centralizer (Q : Set K)
  have hconj : ∀ b ∈ B, ∀ z ∈ R, b * z * b⁻¹ ∈ R := by
    intro b hb z hz
    obtain ⟨hzQ, hzC⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (h.normalizes hb) z).1 hzQ
    · rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hc' : b⁻¹ * c * b ∈ Q := by
        simpa using (Subgroup.mem_normalizer_iff.mp (h.normalizes (inv_mem hb)) c).1 hc
      have hcomm := (Subgroup.mem_centralizer_iff.mp hzC) (b⁻¹ * c * b) hc'
      calc c * (b * z * b⁻¹) = b * ((b⁻¹ * c * b) * z) * b⁻¹ := by group
        _ = b * (z * (b⁻¹ * c * b)) * b⁻¹ := by rw [hcomm]
        _ = b * z * b⁻¹ * c := by group
  have hBR : B ≤ normalizer (R : Set K) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro z
    exact ⟨hconj b hb z, fun hz => by
      have hz' := hconj b⁻¹ (inv_mem hb) (b * z * b⁻¹) hz
      have heq : b⁻¹ * (b * z * b⁻¹) * (b⁻¹)⁻¹ = z := by group
      rwa [heq] at hz'⟩
  change R ≤ centralizer (B : Set K)
  have hbot : ⁅R, B⁆ = ⊥ := by
    by_contra hne
    have hQR : Q ≤ R := h.minimal R inf_le_left hBR hne
    apply hnc
    intro x hx y hy
    have hxcent : x ∈ centralizer (Q : Set K) := (Subgroup.mem_inf.mp (hQR hx)).2
    exact ((Subgroup.mem_centralizer_iff.mp hxcent) y hy).symm
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot

end HHMinimal

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
