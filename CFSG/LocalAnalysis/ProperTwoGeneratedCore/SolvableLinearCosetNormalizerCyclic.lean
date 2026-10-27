module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.CharacterTheory.TwoRankLowerBound.AbelianRankOne

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups

variable {G : Type*} [Group G]

theorem commute_of_isCyclic_outer {L P : Subgroup G}
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) [IsCyclic (Outer L)]
    (hinner : ∀ p ∈ P, ∀ l ∈ L, (∀ y ∈ L, p * y * p⁻¹ = l * y * l⁻¹) →
      ∀ x ∈ P, p * x = x * p) :
    ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  let φ : P →* Outer L :=
    (QuotientGroup.mk' (inner L)).comp ((L.normalizerMonoidHom).comp (Subgroup.inclusion hPL))
  have hker : φ.ker ≤ Subgroup.center P := by
    intro p hp
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hp
    obtain ⟨l, hl⟩ := hp
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    refine (hinner p p.2 l l.2 (fun y hy => ?_) x x.2).symm
    have h := congrArg (fun σ : MulAut L => ((σ ⟨y, hy⟩ : L) : G)) hl
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.comp_apply,
      Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion] at h
    exact h.symm
  have hcomm := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center φ hker
  intro x hx y hy
  exact congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem isCyclic_of_commute_of_twoRank_le_one [Finite G] {P D : Subgroup G} (hPD : P ≤ D)
    (hP : IsPGroup 2 P) (hrank : CFSG.Open.twoRank D ≤ 1)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) : IsCyclic P := by
  let _ : CommGroup P :=
    { (inferInstance : Group P) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  apply CFSG.TwoRankLowerBound.Helpers.abelian_two_group_cyclic_of_unique_involution_of_card_eq_pow
    n P hP hn
  intro a b ha hb
  have hD := CFSG.TwoRankLowerBound.Helpers.commuting_involutions_eq_of_twoRank_le_one D hrank
    ⟨a, hPD a.2⟩ ⟨b, hPD b.2⟩
    (by rw [← Subgroup.orderOf_coe, ← ha, ← Subgroup.orderOf_coe a])
    (by rw [← Subgroup.orderOf_coe, ← hb, ← Subgroup.orderOf_coe b])
    (Subtype.ext (hcomm a a.2 b b.2))
  have h := congrArg (fun x : D => (x : G)) hD
  exact Subtype.ext h

theorem isCyclic_of_sl2_hull_action [Finite G] {L M D P : Subgroup G} {u : G}
    (hLM : L ≤ M) (hLn : (L.subgroupOf M).Normal) {F : Type*} [Field F] {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f) (e : L ≃* SL(2, F))
    (hK : M ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.zpowers u)
    (hPM : P ≤ M) (hPu : P ≤ Subgroup.centralizer ({u} : Set G)) (huP : u ∈ P)
    (hLP : L ⊓ P = ⊥) (hP : IsPGroup 2 P) (hPD : P ≤ D) (hrank : CFSG.Open.twoRank D ≤ 1) :
    IsCyclic P := by
  have hPL : P ≤ Subgroup.normalizer (L : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h := hLn.conj_mem ⟨y, hLM hy⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨p, hPM hp⟩
      exact Subgroup.mem_subgroupOf.mp h
    · intro hy
      have h := hLn.conj_mem ⟨p * y * p⁻¹, hLM hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
        ⟨p⁻¹, M.inv_mem (hPM hp)⟩
      have h2 := Subgroup.mem_subgroupOf.mp h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at h2
      have h3 : p⁻¹ * (p * y * p⁻¹) * p = y := by group
      rwa [h3] at h2
  have hcyc : IsCyclic (Outer L) :=
    (equivalence e).isCyclic.mpr (even_SL2_full_automorphism_semilinear_model hf hF).2.2.1
  have hinner : ∀ p ∈ P, ∀ l ∈ L, (∀ y ∈ L, p * y * p⁻¹ = l * y * l⁻¹) →
      ∀ x ∈ P, p * x = x * p := by
    intro p hp l hl hpl x hx
    have hk : l⁻¹ * p ∈ M ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨M.mul_mem (M.inv_mem (hLM hl)) (hPM hp), Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy
      have h := hpl y hy
      calc y * (l⁻¹ * p) = l⁻¹ * (l * y * l⁻¹) * p := by group
        _ = l⁻¹ * (p * y * p⁻¹) * p := by rw [h]
        _ = l⁻¹ * p * y := by group
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hK hk)
    have hlP : l ∈ P := by
      have h : l = p * (u ^ k)⁻¹ := by rw [hk]; group
      rw [h]
      exact P.mul_mem hp (P.inv_mem (P.zpow_mem huP k))
    have hl1 : l = 1 := by
      have h : l ∈ L ⊓ P := ⟨hl, hlP⟩
      rwa [hLP, Subgroup.mem_bot] at h
    have hpu : p = u ^ k := by rw [hk, hl1, inv_one, one_mul]
    rw [hpu]
    exact ((show Commute x u from
      Subgroup.mem_centralizer_singleton_iff.mp (hPu hx)).symm.zpow_left k).eq
  exact isCyclic_of_commute_of_twoRank_le_one hPD hP hrank
    (commute_of_isCyclic_outer hPL hinner)

end CFSG.ProperTwoGeneratedCore.HighRankPair
