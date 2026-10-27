module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootS2
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootS3
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootConj

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal CFSG.ComponentClassification.RestrictedStd.Spor Equiv

section S4

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

omit [Finite G] in
theorem mem_centralizer_rootGroup_of_fix (e : L ≃* alternatingGroup (Fin n)) {y : G} (hy : y ∈ L)
    {S : Finset (Fin n)}
    (hS : ∀ i ∈ S, ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) i = i) :
    y ∈ centralizer (rootGroup (G := G) e S : Set G) := by
  rw [mem_centralizer_iff]
  intro r hr
  exact comm_of_mem_corr_of_fix e hy hS hr

theorem nearGives_of_ne_six (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hFour : FourExactOuterInput) (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (e : L ≃* alternatingGroup (Fin n)) (hn : 12 ≤ n)
    {k : ℕ} (hk3 : 3 ≤ k) (hk4 : k ≤ 4) (hm : 9 ≤ n - k) {y : G} (hy : y ∈ FusionSet L z)
    (hf4 : 4 ≤ (fixFin ((e ⟨y, hy.1⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card)
    (hf6 : (fixFin ((e ⟨y, hy.1⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card ≠ 6) :
    ∃ S : Finset (Fin n), S.card = k ∧ ∀ b ∈ L, b ∈ centralizer (rootGroup e S : Set G) →
      orderOf b = 2 → ∃ h' ∈ centralizer (rootGroup e S : Set G), h' * z * h'⁻¹ = z * b := by
  obtain ⟨hyL, hy2, g, hg⟩ := hy
  set F : Finset (Fin n) :=
    fixFin ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) with hF
  have hf4' : 4 ≤ F.card := hf4
  have hf6' : F.card ≠ 6 := hf6
  obtain ⟨S, hSF, hSk⟩ := Finset.exists_subset_card_eq (by omega : k ≤ F.card)
  refine ⟨S, hSk, ?_⟩
  rcases zstar_or_fusion hlookup hHN hFour h d hQ2 hE e hk3 hk4 hm S hSk with hz | hfus
  · exfalso
    have hid : NormalAltIdent n F.card := by
      rcases Nat.lt_or_ge F.card 5 with h5 | h5
      · have : F.card = 4 := by omega
        rw [this]
        exact normalAltIdent_four hn
      · exact normalAltIdent_of_five_le h5
    have hfS : ∀ i ∈ S, ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) i = i :=
      fun i hi => mem_fixFin.1 (hSF hi)
    have hfF : (5 ≤ F.card ∧ F.card ≠ 6) ∨ F.card = 4 := by omega
    obtain ⟨S₁, hS₁c, hS₁⟩ := exists_common_root_of_fix h d hQ2 hE e hyL hy2 hg hfF hid hfS
    have hS' : S.card = 3 ∨ S.card = 4 := by omega
    have hz₁ : IsZStar (rootGroup e S₁) z :=
      (isZStar_rootGroup_iff h d e hS₁c.symm (by omega)).1 hz
    exact false_of_zstar_common_root h d hQ2 e hn ⟨hyL, hy2, g, hg⟩ hg hS'
      (mem_centralizer_rootGroup_of_fix e hyL hfS) hS₁ hz hz₁
  · exact hfus

end S4

end CFSG.OddStandard.AltStdSec
