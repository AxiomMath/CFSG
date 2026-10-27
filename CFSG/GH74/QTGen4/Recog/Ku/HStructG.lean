module

public import CFSG.GH74.QTGen4.Recog.Ku.HStruct

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem card_P_eq (h : KuHyp G T M H P z) : Nat.card P = 32 := by
  have hP := h.pExtra.2.1
  rw [hP]
  norm_num

theorem card_pCore_sub_P (h : KuHyp G T M H P z) :
    Nat.card {g : ↥(pCoreOf 2 H) // (g : G) ∉ P} = 32 := by
  classical
  have hPQ : P ≤ pCoreOf 2 H := h.P_le_pCore_H
  have hsum : Nat.card ↥(pCoreOf 2 H) =
      Nat.card {g : ↥(pCoreOf 2 H) // (g : G) ∈ P} +
        Nat.card {g : ↥(pCoreOf 2 H) // (g : G) ∉ P} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun g : ↥(pCoreOf 2 H) => (g : G) ∈ P)).symm
  have hin : Nat.card {g : ↥(pCoreOf 2 H) // (g : G) ∈ P} = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPQ).toEquiv
  have hQ : Nat.card ↥(pCoreOf 2 H) = 64 := card_pCore_H h
  have hP := card_P_eq h
  omega

theorem conj_mem_pCore_of_mem (h : KuHyp G T M H P z) {k : G} (hk : k ∈ H)
    {g : G} (hg : g ∈ pCoreOf 2 H) : k * g * k⁻¹ ∈ pCoreOf 2 H :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf_self H hk) g).mp hg

theorem conj_mem_P_iff (h : KuHyp G T M H P z) {k : G} (hk : k ∈ H) {g : G} :
    k * g * k⁻¹ ∈ P ↔ g ∈ P :=
  (Subgroup.mem_normalizer_iff.mp (h.hNormP hk) g).symm

theorem exists_fixed_coset (h : KuHyp G T M H P z) {x : G} (hxH : x ∈ H)
    (hx3 : orderOf x = 3) :
    ∃ u ∈ pCoreOf 2 H, u ∉ P ∧ x * u * x⁻¹ = u := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hKH : ∀ k ∈ Subgroup.zpowers x, k ∈ H := fun k hk => Subgroup.zpowers_le.mpr hxH hk
  letI : MulAction (Subgroup.zpowers x) {g : ↥(pCoreOf 2 H) // (g : G) ∉ P} :=
    { smul := fun k a =>
        ⟨⟨(k : G) * (a.1 : G) * (k : G)⁻¹,
            h.conj_mem_pCore_of_mem (hKH k.1 k.2) a.1.2⟩,
          fun hc => a.2 ((h.conj_mem_P_iff (hKH k.1 k.2)).mp hc)⟩
      one_smul := fun a => Subtype.ext (Subtype.ext (by
        show (1 : G) * (a.1 : G) * (1 : G)⁻¹ = a.1
        simp))
      mul_smul := fun k l a => Subtype.ext (Subtype.ext (by
        show ((k : G) * (l : G)) * (a.1 : G) * ((k : G) * (l : G))⁻¹ =
          (k : G) * ((l : G) * (a.1 : G) * (l : G)⁻¹) * (k : G)⁻¹
        group)) }
  have hG : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3]; norm_num)
  have hmod := IsPGroup.card_modEq_card_fixedPoints hG
    {g : ↥(pCoreOf 2 H) // (g : G) ∉ P}
  rw [h.card_pCore_sub_P] at hmod
  have hne : (MulAction.fixedPoints (Subgroup.zpowers x)
      {g : ↥(pCoreOf 2 H) // (g : G) ∉ P}).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    have h0 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers x)
        {g : ↥(pCoreOf 2 H) // (g : G) ∉ P}) = 0 := by
      rw [hc]
      simp
    rw [h0] at hmod
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨a, ha⟩ := hne
  have hfix := (MulAction.mem_fixedPoints).mp ha ⟨x, Subgroup.mem_zpowers x⟩
  have hxa : x * (a.1 : G) * x⁻¹ = (a.1 : G) := congrArg (fun b => (b.1 : G)) hfix
  exact ⟨(a.1 : G), a.1.2, a.2, hxa⟩

end KuHyp

end CFSG.GH74.QTGen4.Ku
