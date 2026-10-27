module

public import CFSG.ClassicalInvolution.Q3.TL4S289Brg
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4W

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Disconnected.AschTight

namespace S289

theorem commute_of_map {Q Z : Type} [Group Q] [Group Z] {N L : Subgroup Q} (e : ↥N ≃* Z)
    (hLN : L ≤ N) {x : Q} (hx : x ∈ N)
    (h : ∀ c ∈ (L.subgroupOf N).map e.toMonoidHom, e ⟨x, hx⟩ * c = c * e ⟨x, hx⟩) :
    ∀ y ∈ L, x * y = y * x := by
  intro y hy
  have h1 := h (e ⟨y, hLN hy⟩) ⟨⟨y, hLN hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  rw [← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val (e.injective h1)

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J K'' : Subgroup Y} {u w : Y}

@[expose] noncomputable def linkVtxEquiv (hL : TightLargeHypR r n Y R S t) :
    ↥(modOdd t (linkLayer R t)) ≃* ↥(linkGrp R t) :=
  (vtxEquiv linkLayerAt_le_centralizer fun _ hc _ hy => conj_mem_linkLayer hL hc hy).symm.trans
    (linkLayerEquiv hL)

theorem linkVtxEquiv_mk (hL : TightLargeHypR r n Y R S t) {y : Y} (hy : y ∈ linkLayer R t) :
    ((linkVtxEquiv hL ⟨oddQuotMk t ⟨y, linkLayerAt_le_centralizer hy⟩,
      oddQuotMk_mem_modOdd hy (linkLayerAt_le_centralizer hy)⟩ : ↥(linkGrp R t)) :
        SecQuot (CoreAssembly.conjClass (tightCore R)) t) =
      QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) ⟨y, linkLayer_le_layerY hL hy⟩ := by
  have e : (⟨oddQuotMk t ⟨y, linkLayerAt_le_centralizer hy⟩,
      oddQuotMk_mem_modOdd hy (linkLayerAt_le_centralizer hy)⟩ :
        ↥(modOdd t (linkLayer R t))) =
      vtxEquiv linkLayerAt_le_centralizer (fun _ hc _ hy => conj_mem_linkLayer hL hc hy)
        (QuotientGroup.mk ⟨y, hy⟩) :=
    Subtype.ext (vtxEquiv_mk _ _ ⟨y, hy⟩).symm
  rw [linkVtxEquiv, MulEquiv.trans_apply, e, MulEquiv.symm_apply_apply]
  exact linkLayerEquiv_mk hL ⟨y, hy⟩

theorem u_mem_linkLayer (hL : TightLargeHypR r n Y R S t) (hF : StarFrameAt R t J K'' u w) :
    u ∈ linkLayer R t :=
  coreAt_le_linkLayerAt hF.memJ (mem_coreAt_of_sq_sq hF.invJ.mem
    (by rw [hF.invJ.sq, one_mul]) (hF.comm_tu hL).symm)

theorem w_mem_linkLayer (hL : TightLargeHypR r n Y R S t) (hF : StarFrameAt R t J K'' u w) :
    w ∈ linkLayer R t :=
  coreAt_le_linkLayerAt hF.memK (mem_coreAt_of_sq_sq hF.invK.mem
    (by rw [hF.invK.sq, one_mul]) (hF.comm_tw hL).symm)

theorem isUniqueInvolution_link_u (hL : TightLargeHypR r n Y R S t)
    (hF : StarFrameAt R t J K'' u w) :
    IsUniqueInvolution
      ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t))
      (linkVtxEquiv hL ⟨oddQuotMk t ⟨u, linkLayerAt_le_centralizer (u_mem_linkLayer hL hF)⟩,
        oddQuotMk_mem_modOdd (u_mem_linkLayer hL hF)
          (linkLayerAt_le_centralizer (u_mem_linkLayer hL hF))⟩) := by
  have h := isUniqueInvolution_subgroupOf (isUniqueInvolution_secImg
    (TightLargeHypR.typeRFam hL) (xMem_of_mem_omegaNbr_core hL hF.memJ) hF.invJ)
    (le_linkGrp (t := t) hF.memJ)
  convert h using 1
  exact Subtype.ext (linkVtxEquiv_mk hL (u_mem_linkLayer hL hF))

theorem isUniqueInvolution_link_w (hL : TightLargeHypR r n Y R S t)
    (hF : StarFrameAt R t J K'' u w) :
    IsUniqueInvolution
      ((secImg (CoreAssembly.conjClass (tightCore R)) t K'').subgroupOf (linkGrp R t))
      (linkVtxEquiv hL ⟨oddQuotMk t ⟨w, linkLayerAt_le_centralizer (w_mem_linkLayer hL hF)⟩,
        oddQuotMk_mem_modOdd (w_mem_linkLayer hL hF)
          (linkLayerAt_le_centralizer (w_mem_linkLayer hL hF))⟩) := by
  have h := isUniqueInvolution_subgroupOf (isUniqueInvolution_secImg
    (TightLargeHypR.typeRFam hL) (xMem_of_mem_omegaNbr_core hL hF.memK) hF.invK)
    (le_linkGrp (t := t) hF.memK)
  convert h using 1
  exact Subtype.ext (linkVtxEquiv_mk hL (w_mem_linkLayer hL hF))

theorem le_modOdd_of_frame (hL : TightLargeHypR r n Y R S t) (hF : StarFrameAt R t J K'' u w)
    {L : Subgroup (OddQuot t)} (hLc : IsComponent L)
    (hm : MovedByAll (Subgroup.closure ({t, u, w} : Set Y)) t L) :
    L ≤ modOdd t (linkLayer R t) := by
  have ht := hL.datum.isUniqueInvolution_core
  have huΛ := u_mem_linkLayer hL hF
  have hutC := linkLayerAt_le_centralizer huΛ
  have hm3 := mem_closure_three_left t u w
  have htu : u ≠ t := fun e =>
    hF.memJ.2.1 (eq_core_of_isUniqueInvolution hL hF.memJ.1 (e ▸ hF.invJ))
  have huZ := Lemma52Proof.oddQuotMk_not_mem_zpowers (hF.isElemAbelian hL) hm3.1 ht.ne_one
    hm3.2.1 hF.invJ.ne_one htu hutC
  exact le_of_moved (modOdd_normal fun _ hc _ hy => conj_mem_linkLayer hL hc hy) hLc
    (oddQuotMk_mem_modOdd huΛ hutC) (hm _ (oddQuotMk_mem_modOdd hm3.2.1 hutC) huZ)

end Cit3

end S289

end CFSG.ClassicalInvolution.Q3.TL4
