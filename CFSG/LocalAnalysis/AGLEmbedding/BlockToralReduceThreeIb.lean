module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceGlue
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceTypes
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceCover
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceCycle

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial LinearFlag

namespace ToralReduce

theorem isElemAbelian_subgroupOf {Y : Type*} [Group Y] {p : ℕ} {E : Subgroup Y}
    (h : IsElemAbelian p E) (K : Subgroup Y) : IsElemAbelian p (E.subgroupOf K) :=
  CFSG.Open.IsElemAbelian.subgroupOf h K

variable {G : Type} [Group G] [Finite G]

theorem false_of_toral_three_two
    (hC : KFactFixCensusThree) (hG : GlueVhyp) {M S L : Subgroup G} (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (h2 : NineThreeTwo M S L)
    (hcyc : CycPerfect 3 (blockPL M S L)) {u : ↥M ⧸ CFSG.pCore 2 ↥M} (hu : u ∈ barM M L)
    (hu3 : u ^ 3 = 1) (huC : u ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hV : ∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V, V⁆ = V ∧
      V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      V ≤ Subgroup.normalizer (barM M (S ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ u ∈ V)
    (hfix : ∀ l ∈ barM M L, u * l * u⁻¹ = l → l ∈ blockPL M S L)
    {E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hEL : E ≤ barM M L) (hEel : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) : False := by
  obtain ⟨hCP, hjoin, e, he, ⟨φ⟩⟩ :=
    exists_census_of_nineThreeTwo hC hG hA hL hS h2 hcyc hu hu3 huC hV hfix
  have hK4 := four_le_card_galoisField he
  have hE'el := isElemAbelian_subgroupOf hEel (barM M L)
  have hE'c : Nat.card (E.subgroupOf (barM M L)) = 3 ^ 3 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  by_cases hZ3 : 3 ∣ Nat.card (Subgroup.center ↥(barM M L))
  · exact false_of_card_eq_of_three_dvd hL.component.2.2.1 hK4 φ hCP.odd hZ3 hE'el hE'c
  · by_cases hK3 : 3 ∣ Nat.card (GaloisField 2 e) - 1
    · obtain ⟨ω, hω1, hω3⟩ := exists_cube_root_of_dvd hK3
      exact false_of_fix_of_cube_root hCP φ hω1 hω3 hZ3 hu hu3 huC hjoin hfix
    · have h3 : Nat.Coprime 3 (Nat.card (Subgroup.center ↥(barM M L))) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ3
      let f := (censusHom φ).comp (E.subgroupOf (barM M L)).subtype
      have hf : Function.Injective f := fun a b hab =>
        Subtype.ext (eq_of_censusHom_eq_of_pow φ h3 (hE'el.2 _ a.2) (hE'el.2 _ b.2) hab)
      have hle := card_le_nine_of_not_dvd hK3 (Eb := f.range)
        (by
          rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
          rw [← map_mul, ← map_mul, hE'el.1.is_comm.comm a b])
        (by
          rintro _ ⟨a, rfl⟩
          rw [← map_pow, show a ^ 3 = 1 from Subtype.ext (hE'el.2 _ a.2), map_one])
      rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, hE'c] at hle
      norm_num at hle

end ToralReduce

open ToralReduce in
theorem citedBlockToralThreeIb_of_census
    (hC : KFactFixCensusThree) (hG : GlueVhyp)
    (hTPLT : CitedBlockTransvectionPLType) : CitedBlockToralThreeIb := by
  intro G _ _ M S L hK hA hL h93 hX hS hIb u hu hu3 huC hV hfix E hEL hEC hEel hEc
  have hTPL := citedBlockTransvectionPL_of_type hTPLT
  have hEP : E ≤ blockPL M S L := fun e he => hfix e (hEL he) (by
    rw [Subgroup.mem_centralizer_iff.mp (hEC he) u rfl, mul_inv_cancel_right])
  have h27 : 3 ^ 3 ∣ Nat.card (blockPL M S L) := hEc ▸ Subgroup.card_dvd_of_le hEP
  have h9 : 9 ∣ Nat.card (blockPL M S L) := (show 9 ∣ 3 ^ 3 by norm_num).trans h27
  rcases h93 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact hX h1
  · exact false_of_toral_three_two hC hG hA hL hS h2 (cycPerfect_of_ib Nat.prime_three hIb) hu
      hu3 huC hV hfix hEL hEel hEc
  · exact not_dvd_card_blockPL_of_ib_rest hTPL hK hA hL hX hS (Or.inl h3) hIb h9
  · have h72 := h27.trans (card_blockPL_dvd_of_nineThreeFour h4)
    norm_num at h72
  · obtain ⟨-, ⟨e⟩, -⟩ := h5
    have hcard : Nat.card (barM M L) = 2520 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    have h := hEc ▸ Subgroup.card_dvd_of_le hEL
    rw [hcard] at h
    norm_num at h
  · exact not_dvd_card_blockPL_of_ib_rest hTPL hK hA hL hX hS (Or.inr (Or.inl h6)) hIb h9
  · exact not_dvd_card_blockPL_of_ib_rest hTPL hK hA hL hX hS (Or.inr (Or.inr (Or.inl h7))) hIb
      h9
  · exact not_dvd_card_blockPL_of_ib_rest hTPL hK hA hL hX hS (Or.inr (Or.inr (Or.inr h8))) hIb
      h9

end CFSG.AGLEmbedding
