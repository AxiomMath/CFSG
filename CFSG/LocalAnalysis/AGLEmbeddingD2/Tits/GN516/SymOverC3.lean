module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenExtract
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenFamMain

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B2F CFSG.Quasithin.E2
  CFSG.AGLEmbeddingD2.GN

theorem exists_symOver_lift {G : Type} [Group G] [Finite G] {K S T M V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hmin : MinParabolic K S M) (hred : IsTwoReducedIn K V)
    (hbS : baum T ≤ S) (hST : S ≤ T)
    (hJ : ¬ thompsonJ S ≤ Subgroup.centralizer (V : Set G)) (hSym : SymCaseGen K S V hV) :
    ∃ (C : Subgroup (MulAut (IntMod V hV))) (Y₀ : Subgroup G), Y₀ ≤ K ∧ Nat.card C = 3 ∧
      autI hV Y₀ = C ∧ pCoreOf 2 K ⊔ baum T ≤ Subgroup.normalizer (Y₀ : Set G) ∧
      ∀ Y : Subgroup G, Y ≤ K → autI hV Y = C → Y ⊔ S = K := by
  obtain ⟨m, -, ⟨F⟩⟩ := exists_genFamData hV hmin hred hJ hSym
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hSK : S ≤ K := hmin.isSylow.1
  have hKJ : twoResidual K ≤ thompsonJ K := hSym.1
  have hHV : ¬ K ≤ Subgroup.centralizer (V : Set G) := fun hle =>
    hJ ((thompsonJ_le_self S).trans (hSK.trans hle))
  have hQC : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) :=
    MinParabolic.pCoreOf_le_centralizer hred
  have hCK : F.C ≤ autI hV K := by
    intro φ hφ
    exact autI_mono hV (thompsonJ_le_self K) (F.L_J (F.C_le hφ))
  have hYC : autI hV (preI hV K hKN F.C) = F.C := by
    refine le_antisymm ?_ ?_
    · intro φ hφ
      obtain ⟨g, hgY, rfl⟩ := (mem_autI hV).1 hφ
      exact ((mem_preI hV).1 hgY).2
    · intro φ hφ
      obtain ⟨g, hgK, rfl⟩ := (mem_autI hV).1 (hCK hφ)
      exact (mem_autI hV).2 ⟨g, (mem_preI hV).2 ⟨hgK, hφ⟩, rfl⟩
  have hnormY : ∀ g : ↥K,
      convHom hV K hKN g ∈ Subgroup.normalizer (F.C : Set (MulAut (IntMod V hV))) →
      (g : G) ∈ Subgroup.normalizer ((preI hV K hKN F.C : Subgroup G) : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨hnK, hnC⟩ := (mem_preI hV).1 hn
    have hgn : (g : G) * n * (g : G)⁻¹ ∈ K := K.mul_mem (K.mul_mem g.2 hnK) (K.inv_mem g.2)
    refine (mem_preI hV).2 ⟨hgn, ?_⟩
    show convHom hV K hKN (g * ⟨n, hnK⟩ * g⁻¹) ∈ F.C
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hg _).1 hnC
  have hQnorm : pCoreOf 2 K ≤ Subgroup.normalizer ((preI hV K hKN F.C : Subgroup G) : Set G) := by
    intro q hq
    have hqK : q ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hq
    have h1 : convHom hV K hKN ⟨q, hqK⟩ = 1 :=
      (convI_eq_one_iff hV ⟨q, hKN hqK⟩).2 (hQC hq)
    exact hnormY ⟨q, hqK⟩ (by rw [h1]; exact one_mem _)
  have hbaum : baum T = baum S := baum_eq_of_le hbS hST
  have hTnorm : baum T ≤ Subgroup.normalizer ((preI hV K hKN F.C : Subgroup G) : Set G) := by
    intro s hs
    have hsK : s ∈ K := hSK (hbS hs)
    have hsbS : s ∈ baum S := by
      rw [← hbaum]
      exact hs
    exact hnormY ⟨s, hsK⟩ (F.baum_C (convI_mem_autI hV hsbS (hKN hsK)))
  refine ⟨F.C, preI hV K hKN F.C, preI_le hV, F.C_card, hYC, sup_le hQnorm hTnorm, ?_⟩
  intro Y hYK hYCY
  refine hmin.eq_of_not_le le_sup_right (sup_le hYK hSK) fun hM => ?_
  have hCM : F.C ≤ autI hV M := by
    rw [← hYCY]
    exact autI_mono hV (le_sup_left.trans hM)
  have hTM : autI hV S ≤ autI hV M := autI_mono hV hmin.le
  have hJM := F.gen_J _ hTM (F.gen_L _ hTM hCM)
  have hC : K ⊓ Subgroup.centralizer (V : Set G) ≤ M :=
    (hmin.inf_centralizer_le_kerIn hred hHV).trans kerIn_le
  have hKM : twoResidual K ≤ M := fun x hx =>
    mem_of_convI_mem_autI_gen hV hKN hmin.maximal.1.le hC (twoResidual_le K hx)
      (hJM (convI_mem_autI hV (hKJ hx) (hKN (twoResidual_le K hx))))
  have hKM' : K ≤ M := by
    rw [← sup_twoResidual_eq hmin.isSylow]
    exact sup_le hmin.le hKM
  exact absurd (lt_of_le_of_lt hKM' hmin.maximal.1) (lt_irrefl _)

end CFSG.AGLEmbeddingD2.Tits.GN516
