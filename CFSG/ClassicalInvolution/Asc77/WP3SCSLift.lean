module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinSide
public import CFSG.ClassicalInvolution.Asc77.WP3ChainVGen3
public import CFSG.ClassicalInvolution.Asc77.WP3ChainVToral

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem mem_modOdd_of_commutes_frame {B : Subgroup G}
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ x ∈ B, x * x = 1) (hzB : z ∈ B)
    (hz1 : z ≠ 1) (hBz : B ≤ Subgroup.centralizer ({z} : Set G)) (hBY : B ≤ exactLayer Ω z)
    {e : G} (heB : e ∈ B) (he1 : e ≠ 1) (hez : e ≠ z) {q : OddQuot z}
    (hq : q ∈ memberJoin (exactFamily Ω z) z)
    (hcomm : ∀ he : e ∈ Subgroup.centralizer ({z} : Set G),
      oddQuotMk z ⟨e, he⟩ * q = q * oddQuotMk z ⟨e, he⟩) :
    q ∈ modOdd z (⨆ F ∈ signalizerFunctorEk 2 2 B,
      (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z)) := by
  have hz2 : z * z = 1 := hB2 z hzB
  have he2 : e * e = 1 := hB2 e heB
  have hze : z * e = e * z := hBc z hzB e heB
  set F : Subgroup G := Subgroup.closure ({z, e} : Set G) with hF
  have hFB : F ≤ B := by
    rw [hF, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hzB
    · exact heB
  have hcard : Nat.card F = 4 :=
    card_closure_pair_eq_four hz2 he2 hz1 he1 (fun h => hez h.symm) hze
  have hFE : F ∈ signalizerFunctorEk 2 2 B := ⟨hFB, by rw [hcard]; norm_num⟩
  have hFY : F ≤ exactLayer Ω z := hFB.trans hBY
  have hF2 : ∀ x ∈ F, x * x = 1 := fun x hx => hB2 x (hFB hx)
  have hcent : ∀ (x : G) (_ : x ∈ F) (hC : x ∈ Subgroup.centralizer ({z} : Set G)),
      oddQuotMk z ⟨x, hC⟩ * q = q * oddQuotMk z ⟨x, hC⟩ := by
    refine ChainFrame.commutes_of_closure (oddQuotMk z) q (S := ({z, e} : Set G)) ?_ ?_
    · rintro s (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      · exact hBz heB
    · rintro s (rfl | rfl) hs
      · exact oddQuotMk_central (Subgroup.mem_centralizer_singleton_iff.mpr rfl) q
      · exact hcomm hs
  obtain ⟨y, hyC, hyY, hyF, hyq⟩ := exists_lift_centralizer (a := z) hF2 hFY hq hcent
  have hle : (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) ≤
      ⨆ F ∈ signalizerFunctorEk 2 2 B, (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) :=
    le_iSup₂ (f := fun F (_ : F ∈ signalizerFunctorEk 2 2 B) =>
      Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) F hFE
  exact ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.mpr (hle ⟨hyF, hyY⟩), hyq⟩

theorem exactLayer_le_of_images {H : Subgroup G} (hnorm : NormalizesLayer (exactFamily Ω z) z)
    (hHY : H ≤ exactLayer Ω z)
    (himg : ∀ N ∈ tqMembers Ω z, ∀ y ∈ exactCore z N,
      ∀ hy : y ∈ Subgroup.centralizer ({z} : Set G), oddQuotMk z ⟨y, hy⟩ ∈ modOdd z H) :
    exactLayer Ω z ≤ oddCoreIn (exactLayer Ω z) ⊔ H := by
  refine (exactLayer_eq_iSup Ω z).le.trans (iSup₂_le fun K' hK' => ?_)
  obtain ⟨N, hN, rfl⟩ := hK'
  intro y hy
  have hyY : y ∈ exactLayer Ω z := exactCore_le_exactLayer hN hy
  have hyC : y ∈ Subgroup.centralizer ({z} : Set G) := exactCore_le_centralizer z N hy
  obtain ⟨c, hcH, hc⟩ := (mem_modOdd_iff).mp (himg N hN y hy hyC)
  have hcH' : (c : G) ∈ H := hcH
  have hcY : (c : G) ∈ exactLayer Ω z := hHY hcH'
  have heq : oddQuotMk z ⟨y, hyC⟩ = oddQuotMk z ⟨c, exactLayer_le_centralizer Ω z hcY⟩ := by
    rw [← hc]
  have hker : (⟨y, hyY⟩ : ↥(exactLayer Ω z)) * ⟨c, hcY⟩⁻¹ ∈
      (layerToOddQuot (exactFamily Ω z) z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, layerToOddQuot_apply, layerToOddQuot_apply]
    exact mul_inv_eq_one.mpr heq
  rw [ker_layerToOddQuot_of_normalizes hnorm] at hker
  have hmem := mem_oddCoreIn_of_mem_classicalInvolutionOddCore hker
  have hmem' : y * (c : G)⁻¹ ∈ oddCoreIn (exactLayer Ω z) := by
    have : ((⟨y, hyY⟩ * ⟨c, hcY⟩⁻¹ : ↥(exactLayer Ω z)) : G) = y * (c : G)⁻¹ := by simp
    rwa [this] at hmem
  have e : y = (y * (c : G)⁻¹) * c := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hmem') (Subgroup.mem_sup_right hcH')

theorem centralizerGenerationStar_of_images (hnorm : NormalizesLayer (exactFamily Ω z) z)
    {B : Subgroup G}
    (himg : ∀ N ∈ tqMembers Ω z, ∀ y ∈ exactCore z N,
      ∀ hy : y ∈ Subgroup.centralizer ({z} : Set G),
      oddQuotMk z ⟨y, hy⟩ ∈ modOdd z (⨆ F ∈ signalizerFunctorEk 2 2 B,
        (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z))) :
    CentralizerGenerationStar Ω B z :=
  exactLayer_le_of_images hnorm (iSup₂_le fun _ _ => inf_le_right) himg

end Lift

end CFSG.ClassicalInvolution.Asc77
