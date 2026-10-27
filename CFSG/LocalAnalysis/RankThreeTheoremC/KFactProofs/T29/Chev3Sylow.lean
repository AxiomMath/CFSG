module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Step0
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3

open CFSG.Open Subgroup
open scoped Pointwise

section Sylow

variable {X : Type} [Group X] [Finite X]

theorem three_le_pRank_centralizer_of_mem {L E : Subgroup X} (h4 : ¬ 3 ^ 4 ∣ Nat.card L)
    (hEL : E ≤ L) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3) {x : X}
    (hx : orderOf x = 3) (hxL : x ∈ L) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h27 : 3 ^ 3 ∣ Nat.card L := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hEL
  have hfac : (Nat.card L).factorization 3 = 3 := by
    have h1 : 3 ≤ (Nat.card L).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp h27
    have h2 : ¬ 4 ≤ (Nat.card L).factorization 3 := fun h =>
      h4 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mpr h)
    omega
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 E L :=
    CFSG.ABGLocalTools.isSylowOf_of_card hEL (by rw [hcard, hfac])
  obtain ⟨P, hP⟩ := hSyl
  have hxp : IsPGroup 3 (zpowers (⟨x, hxL⟩ : L)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
      simpa using hx)
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L P Q
  have hxQ : (⟨x, hxL⟩ : L) ∈ (Q : Subgroup L) := hQ (Subgroup.mem_zpowers _)
  rw [← hg] at hxQ
  have hxQ' : ∃ s ∈ (P : Subgroup L), g * s * g⁻¹ = (⟨x, hxL⟩ : L) := by
    have h2 : (⟨x, hxL⟩ : L) ∈ MulAut.conj g • (P : Subgroup L) := hxQ
    have := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp h2
    simpa using this
  obtain ⟨s, hsP, hs⟩ := hxQ'
  have hsE : (s : X) ∈ E := by
    rw [← hP]
    exact ⟨s, hsP, rfl⟩
  set F : Subgroup X := E.map (MulAut.conj (g : X)).toMonoidHom with hF
  have hFab : IsElemAbelian 3 F := CFSG.Open.IsElemAbelian.map hE _
  have hFcard : Nat.card F = 3 ^ 3 := by
    rw [hF, Subgroup.card_map_of_injective (MulAut.conj (g : X)).injective, hcard]
  have hxF : x ∈ F := by
    refine ⟨(s : X), hsE, ?_⟩
    have := congrArg Subtype.val hs
    simpa using this
  have hFle : F ≤ centralizer ({x} : Set X) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (hFab.1.is_comm.comm (⟨z, hz⟩ : F) ⟨y, hxF⟩ |> congrArg Subtype.val).symm
  exact le_pRank_of_isElemAbelian_card Nat.prime_three hFle hFab (by rw [hFcard])

theorem three_le_pRank_centralizer_of_sylow {L : Subgroup X} (h4 : ¬ 3 ^ 4 ∣ Nat.card L)
    (hall : ∀ g : X, g ^ 3 = 1 → g ∈ L) (hr : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) {x : X}
    (hx : orderOf x = 3) : 3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, -, hE, hcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (H := (⊤ : Subgroup X)) hr
  have hx3 : x ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  exact three_le_pRank_centralizer_of_mem h4 (fun g hg => hall g (hE.2 g hg)) hE hcard hx
    (hall x hx3)

@[expose] noncomputable def mulEquivQuotientCenter {L : Subgroup X}
    (hZ : center ↥L = ⊥) : ↥L ≃* (↥L ⧸ center ↥L) :=
  (QuotientGroup.quotientBot (G := ↥L)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)

end Sylow

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3
