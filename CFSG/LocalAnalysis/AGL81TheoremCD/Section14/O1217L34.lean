module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Inputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34AutModel
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K4143Reduce
import CFSG.Models.PGL

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open

private theorem isPSL_of_isLinThreeFour {K : Type} [Group K]
    (hL : CFSG.AGLEmbedding.IsLinThreeFour K) : CFSG.Quasithin.IsPSL 3 2 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.AGLEmbedding.KFactProofs.UPrimeExcL34.nonempty_equiv_projSL hL
  exact CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL
    ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩ e

private theorem isElemAbelian_sylow_three_of_isLinThreeFour {K : Type} [Group K] [Finite K]
    (hL : CFSG.AGLEmbedding.IsLinThreeFour K) (T : Sylow 3 K) :
    CFSG.Open.IsElemAbelian 3 (T : Subgroup K) := by
  classical
  obtain ⟨ε₀⟩ := CFSG.AGLEmbedding.KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour hL
  have hcard : Nat.card ((T : Subgroup K).map ε₀.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ε₀.injective]
    exact CFSG.AGLEmbedding.KFactProofs.UPrimeExcL34.card_sylow_three_of_isLinThreeFour hL T
  have hmap : CFSG.Open.IsElemAbelian 3 ((T : Subgroup K).map ε₀.toMonoidHom) :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
      (CFSG.RankThree.PartTwo.KFacts.L34.isElementaryAbelian_of_card_eq_nine
        CFSG.AGLEmbedding.KFactProofs.UPrimeExcL34.card_galoisField_two_two hcard)
  have h := hmap.map ε₀.symm.toMonoidHom
  rwa [Subgroup.map_map,
    show ε₀.symm.toMonoidHom.comp ε₀.toMonoidHom = MonoidHom.id K from
      MonoidHom.ext fun x => by simp,
    Subgroup.map_id] at h

theorem kFactL34InvTwo_holds : KFactL34InvTwo := by
  intro X _ _ K hKnorm hL T S hS2 hnorm
  classical
  letI : K.Normal := hKnorm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let c : X →* MulAut ↥K := MulAut.conjNormal (H := K)
  let B : Subgroup (MulAut ↥K) := S.map c
  have hker : c.ker = Subgroup.centralizer (K : Set X) := by
    ext z
    rw [MonoidHom.mem_ker,
      CFSG.LocalAnalysis.RankThreeUC.S15.K4143K2.conjNormal_eq_one_iff_mem_centralizer K]
  have hcardB : Nat.card ↥B = (Subgroup.centralizer (K : Set X)).relIndex S := by
    rw [← hker, ← Subgroup.relIndex_ker c (K := S)]
  have hB2 : IsPGroup 2 ↥B := hS2.map c
  have hKpsl : CFSG.Quasithin.IsPSL 3 2 2 ↥K := isPSL_of_isLinThreeFour hL
  have hTcard : Nat.card (T : Subgroup ↥K) = 9 :=
    CFSG.AGLEmbedding.KFactProofs.UPrimeExcL34.card_sylow_three_of_isLinThreeFour hL T
  have hTe : CFSG.Open.IsElemAbelian 3 (T : Subgroup ↥K) :=
    isElemAbelian_sylow_three_of_isLinThreeFour hL T
  have hnormAut : ∀ s ∈ (T : Subgroup ↥K), ∀ b ∈ B,
      MulAut.conj s * b * (MulAut.conj s)⁻¹ ∈ B := by
    intro s hs b hb
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hb
    have hsN : (s : X) ∈ Subgroup.normalizer (S : Set X) :=
      hnorm (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
    have hrS : (s : X) * r * (s : X)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp hsN r).mp hr
    have hconj : MulAut.conj s * c r * (MulAut.conj s)⁻¹ =
        c ((s : X) * r * (s : X)⁻¹) := by
      rw [show MulAut.conj s = c (s : X) from (MulAut.conjNormal_val (h := s)).symm,
        ← map_mul, ← map_inv, ← map_mul]
    rw [hconj]
    exact Subgroup.mem_map_of_mem c hrS
  have hle := (l34_aut_two_subgroup hKpsl hB2 hTcard hTe hnormAut).1
  rwa [← hcardB]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
