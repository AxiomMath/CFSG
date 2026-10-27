module

public import CFSG.ClassicalInvolution.Q3.Sec13L711Base
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen610
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen611
public import CFSG.ClassicalInvolution.Asc77.AscE187Conj
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

namespace Q8Omega

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem conjSub_eq_of_le {A : Subgroup G} {g : G} (h : conjSub g A ≤ A) : conjSub g A = A :=
  Subgroup.eq_of_le_of_card_ge h (by rw [AscL62.natCard_conjSub])

theorem mem_normalizer_of_perm {η : Set (Subgroup G)} {g : G} (hg : ∀ V ∈ η, conjSub g V ∈ η) :
    g ∈ Subgroup.normalizer ((⨆ V ∈ η, V : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq]
  refine conjSub_eq_of_le ?_
  rw [conjSub_iSup₂]
  exact iSup₂_le fun V hV => le_biSup (fun V => V) (hg V hV)

variable (hΩ : Q8Omega Ω)
include hΩ

section Eta

variable {η : Set (Subgroup G)} (hη : η ∈ etaG Ω)
include hη

theorem W_isPGroup : IsPGroup 2 (⨆ V ∈ η, V : Subgroup G) := by
  obtain ⟨S, hS, -⟩ := hη
  exact S.isPGroup'.to_le (iSup₂_le fun V hV => (hS.1 hV).2)

theorem W_comm : ∀ x ∈ (⨆ V ∈ η, V : Subgroup G), ∀ y ∈ (⨆ V ∈ η, V : Subgroup G),
    x * y = y * x := by
  obtain ⟨S, hS, hinv⟩ := hη
  exact (Sec6Gen.eta_abelian_of_cyc66 hΩ.hyp (Sec6Gen.cyc66 hΩ.hyp) hS hinv).1

omit hΩ hη in
theorem le_W {V : Subgroup G} (hV : V ∈ η) : V ≤ (⨆ V ∈ η, V : Subgroup G) :=
  le_biSup (fun V => V) hV

theorem mem_eta_iff {V : Subgroup G} : V ∈ η ↔ V ∈ USet Ω ∧ V ≤ (⨆ V ∈ η, V : Subgroup G) := by
  obtain ⟨S, hS, hinv⟩ := hη
  have h := (Sec6Gen.eta_abelian_of_cyc66 hΩ.hyp (Sec6Gen.cyc66 hΩ.hyp) hS hinv).2
  constructor
  · intro hV
    exact ⟨(hS.1 hV).1, le_W hV⟩
  · intro hV
    rw [← h]
    exact hV

theorem mem_USet_of_mem_eta {V : Subgroup G} (hV : V ∈ η) : V ∈ USet Ω :=
  ((hΩ.mem_eta_iff hη).mp hV).1

theorem inf_mem_eta {P K : Subgroup G} (hP : IsPGroup 2 P)
    (hWP : (⨆ V ∈ η, V : Subgroup G) ≤ P) (hK : K ∈ Ω) (h2 : 2 < Nat.card ↥(K ⊓ P)) :
    K ⊓ (⨆ V ∈ η, V : Subgroup G) ∈ η := by
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hP
  have h2' : 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) :=
    lt_of_lt_of_le h2 (Subgroup.card_le_of_le (inf_le_inf_left K hS))
  exact Sec6Gen.l6_11Gen G Ω hΩ.hyp S η hη (fun V hV => (le_W hV).trans (hWP.trans hS)) K hK h2'

theorem inf_mem_eta_of_le_normalizer {K : Subgroup G} (hK : K ∈ Ω)
    (hKW : K ≤ Subgroup.normalizer ((⨆ V ∈ η, V : Subgroup G) : Set G)) :
    K ⊓ (⨆ V ∈ η, V : Subgroup G) ∈ η := by
  have hP : IsPGroup 2 ↥(K ⊔ (⨆ V ∈ η, V : Subgroup G)) :=
    (hΩ.two K hK).to_sup_of_normal_right' (hΩ.W_isPGroup hη) hKW
  refine hΩ.inf_mem_eta hη hP le_sup_right hK ?_
  rw [inf_eq_left.mpr le_sup_left, hΩ.card K hK]
  norm_num

theorem le_normalizer_W_of_le {P R : Subgroup G} (hP : IsPGroup 2 P)
    (hWP : (⨆ V ∈ η, V : Subgroup G) ≤ P) (hR : R ∈ Ω) (hRP : R ≤ P) :
    R ≤ Subgroup.normalizer ((⨆ V ∈ η, V : Subgroup G) : Set G) := by
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hP
  have h := (Sec6Gen.l6_10Gen G Ω hΩ.hyp S η hη
    (fun V hV => (le_W hV).trans (hWP.trans hS))).1 R ((hΩ.mem_RSet_iff).mpr hR) (hRP.trans hS)
  exact fun r hr => mem_normalizer_of_perm (h r hr)

end Eta

end Q8Omega

end CFSG.ClassicalInvolution.Q3.Sec13
