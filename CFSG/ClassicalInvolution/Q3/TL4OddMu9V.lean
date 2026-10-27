module

public import CFSG.ClassicalInvolution.Q3.TL4VtxMain
public import CFSG.ClassicalInvolution.Q3.TL4OddMu9
public import CFSG.ClassicalInvolution.Q3.TL4OddZT

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Edge

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)}

theorem xMem_of_mem_omegaNbr_nbr (h : TypeRFam r Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJK : J ∈ omegaNbr Ω K) {t u : G} (ht : IsUniqueInvolution K t)
    (hu : IsUniqueInvolution J u) : XMem Ω u K := by
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr h.hyp ht hJK hu
  obtain ⟨-, -, T₀, hT₀, hT₀K, hT₀N⟩ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen h.hyp hK hJK.1 hJK
  refine ⟨hK, h.tight K hK t ht (Subgroup.mem_centralizer_singleton_iff.mpr ctu.symm), T₀,
    Q3CL.T3.isSylow2In_of_mem_RSet_of_le h.hyp hK hT₀ hT₀K, fun x hx => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (S1916.normalizer_le_centralizer_of_isUniqueInvolution hu (hT₀N hx))

end Edge

section Vertex

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {n : ℕ}


theorem hyp51At_of_member (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hOm : OmegaAutOddFreeR)
    (hA : CIT3Below n) (hZ : Subgroup.center G = ⊥) (hGn : Nat.card G ≤ n)
    (hΩ : TypeRFam 3 Ω) {B : Subgroup G} (hB : IsElemAbelian 2 B) {a c : G} (haB : a ∈ B)
    (hcB : c ∈ B) (hc1 : c ≠ 1) (ha1 : a ≠ 1) (hac : a ≠ c) {Ma : Subgroup G}
    (hMa : XMem Ω c Ma) (ha : IsUniqueInvolution Ma a)
    (haC : a ∈ Subgroup.centralizer ({c} : Set G))
    (hfree : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L →
      Vtx.TwinFreeAt (vtxFam Ω c) (modOdd c (coreAt c Ma)) (oddQuotMk c ⟨a, haC⟩) L →
        alphaOf (inducedImage L (modOdd c B)) = ⊥) : Hyp51At B c := by
  have hsq : ∀ x ∈ B, x * x = 1 := fun x hx => (sq x).symm.trans (hB.2 x hx)
  have hΦ : TypeRFam 3 (vtxFam Ω c) := hΩ.vtxFam
  have hO := oddQuot_oddCore_eq_bot c
  have hQn : Nat.card (OddQuot c) < n := lt_of_lt_of_le (natCard_oddQuot_lt hZ hc1) hGn
  have hKa := modOdd_coreAt_mem_vtxFam hMa
  have haz := isUniqueInvolution_modOdd_coreAt hΩ hMa ha haC
  have haB' := oddQuotMk_mem_modOdd haB haC
  have haZ := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 haB ha1 hac haC
  have hsq' : ∀ x ∈ modOdd c B, x * x = 1 := by
    rintro _ ⟨k, hk, rfl⟩
    have hkk : k * k = 1 := Subtype.ext (hsq _ (Subgroup.mem_subgroupOf.mp hk))
    rw [← map_mul, hkk, map_one]
  refine ⟨fun L₁ L₂ hL₁ hL₂ hm₁ hm₂ => Vtx.moves_atMostOne h4 hΦ hO hQn hKa haz hL₁ hL₂
    (hm₁ _ haB' haZ) (hm₂ _ haB' haZ), fun L hL hm => ?_⟩
  by_cases htf : Vtx.TwinFreeAt (vtxFam Ω c) (modOdd c (coreAt c Ma)) (oddQuotMk c ⟨a, haC⟩) L
  · exact hfree L hL hm htf
  · have hma := hm _ haB' haZ
    have hAOF := autOddFree_of_not_twinFree h4 htw hA hOm hΦ hO hQn hKa haz hL hma htf
    have haN := Vtx.orbGrp_le_normalizer h4 hΦ hO hQn hKa haz hL hma (Vtx.le_orbGrp _ haz.mem)
    obtain ⟨y, hy, hne⟩ := hma
    exact Vtx.alphaOf_inducedImage_eq_bot_of_autOddFree hAOF hsq' haB' haN
      (Lemma52Proof.toInducedAutOn_ne_one_of_moved L haN hy hne)

end Vertex

section Cit3


@[expose] def TightStar289ZFreeR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkS3S4 R t → ∀ (J K'' : Subgroup Y) (u w : Y),
        StarFrameAt R t J K'' u w →
        ∀ (hut : u ∈ Subgroup.centralizer ({t} : Set Y)) (L : Subgroup (OddQuot t)),
          CFSG.IsComponent L → MovedByAll (Subgroup.closure ({t, u, w} : Set Y)) t L →
          Vtx.TwinFreeAt (vtxFam (CoreAssembly.conjClass (tightCore R)) t)
            (modOdd t (coreAt t J)) (oddQuotMk t ⟨u, hut⟩) L →
          alphaOf (inducedImage L (modOdd t (Subgroup.closure ({t, u, w} : Set Y)))) = ⊥

@[expose] def TightStar289TFreeR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkS3S4 R t → ∀ (J K'' : Subgroup Y) (u w : Y),
        StarFrameAt R t J K'' u w →
        ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y)) (L : Subgroup (OddQuot u)),
          CFSG.IsComponent L → MovedByAll (Subgroup.closure ({t, u, w} : Set Y)) u L →
          Vtx.TwinFreeAt (vtxFam (CoreAssembly.conjClass (tightCore R)) u)
            (modOdd u (coreAt u (tightCore R))) (oddQuotMk u ⟨t, htu⟩) L →
          alphaOf (inducedImage L (modOdd u (Subgroup.closure ({t, u, w} : Set Y)))) = ⊥


variable {n : ℕ}

theorem tightStar289ZR_of (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hOm : OmegaAutOddFreeR)
    (hfree : TightStar289ZFreeR 3 n) : TightStar289ZR 3 n := by
  intro Y _ _ R S t hL hc hA hcase J K'' u w hF
  have h := TightLargeHypR.typeRFam hL
  have ht := hL.datum.isUniqueInvolution_core
  have hut : u ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hF.comm_tu hL).symm
  have htu : t ≠ u := fun e =>
    hF.memJ.2.1 (eq_core_of_isUniqueInvolution hL hF.memJ.1 (e ▸ hF.invJ))
  exact hyp51At_of_member h4 htw hOm hL.below hL.center hL.card.le h (hF.isElemAbelian hL)
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) ht.ne_one
    hF.invJ.ne_one htu.symm (xMem_of_mem_omegaNbr_core hL hF.memJ) hF.invJ hut
    (hfree Y R S t hL hc hA hcase J K'' u w hF hut)

theorem tightStar289TR_of (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hOm : OmegaAutOddFreeR)
    (hfree : TightStar289TFreeR 3 n) : TightStar289TR 3 n := by
  intro Y _ _ R S t hL hc hA hcase J K'' u w hF
  have h := TightLargeHypR.typeRFam hL
  have ht := hL.datum.isUniqueInvolution_core
  have hK₀ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have htu' : t ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hF.comm_tu hL)
  have htu : t ≠ u := fun e =>
    hF.memJ.2.1 (eq_core_of_isUniqueInvolution hL hF.memJ.1 (e ▸ hF.invJ))
  exact hyp51At_of_member h4 htw hOm hL.below hL.center hL.card.le h (hF.isElemAbelian hL)
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hF.invJ.ne_one
    ht.ne_one htu (xMem_of_mem_omegaNbr_nbr h hK₀ hF.memJ ht hF.invJ) ht htu'
    (hfree Y R S t hL hc hA hcase J K'' u w hF htu')

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
