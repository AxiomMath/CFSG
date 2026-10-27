module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigX3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigPi
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big15
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big18
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big4

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Gen

variable {G : Type} [Group G] [Finite G]

theorem cent_a_two_of_concl {r : ℕ} (hr : 4 ≤ r) {Λ Q : Subgroup G} (hQΛ : Q ≤ Λ)
    (hQ2 : IsPGroup 2 ↥Q) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2)))
    (hC : CentAConcl r (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)) {x : G} (hxΛ : x ∈ Λ)
    (hxQ : ∀ y ∈ Q, x * y = y * x) (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1) :
    x = 1 ∨ x = quatInvolution r e := by
  obtain ⟨k, hk⟩ := hx2
  have hzQ : quatInvolution r e ∈ Q := quatInvolution_mem hr e
  have hzz : quatInvolution r e * quatInvolution r e = 1 := quatInvolution_sq hr e
  rcases cent_a_of_concl hQΛ hQ2 e hC hxΛ hxQ ⟨k, hk⟩ with h | h
  · exact Or.inl (eq_one_of_mem_oddCoreOf h hk)
  · right
    have hzinv : (quatInvolution r e)⁻¹ = quatInvolution r e := inv_eq_of_mul_eq_one_right hzz
    rw [hzinv] at h
    have hc : Commute x (quatInvolution r e) := hxQ _ hzQ
    have hxp : x ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ, pow_mul, hk, one_pow]
    have hzp : quatInvolution r e ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ', pow_mul, pow_two, hzz, one_pow]
    have hpow : (x * quatInvolution r e) ^ 2 ^ (k + 1) = 1 := by
      rw [hc.mul_pow, hxp, hzp, one_mul]
    have hx1 : x * quatInvolution r e = 1 := eq_one_of_mem_oddCoreOf h hpow
    rw [eq_inv_of_mul_eq_one_left hx1, hzinv]

end Gen

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.t_mem_linkLayerAt (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    t ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u := by
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  have hKJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hs.large.datum.hypOmegaGen hK hs.hJ.1 hs.hJ
  exact coreAt_le_linkLayerAt hKJ (Subgroup.subset_closure
    ⟨⟨hs.large.datum.isUniqueInvolution_core.mem,
      Subgroup.mem_centralizer_singleton_iff.mpr hs.tu_comm⟩,
      Balance.isPGroup_zpowers_of_mul_self_eq_one hs.t2⟩)

theorem Z2SetR.centAConcl_t (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r) :
    CentAConcl r (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)) := by
  obtain ⟨p, f, hm⟩ := hs.exists_linkModel hr (z2BigModelArith_holds r)
  exact centAConcl_congr (linkLayerEquiv hs.large) (centAConcl_of_model (z2BigModelCent_holds r) hr hm)

theorem Z2SetR.centBConcl_t (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r) :
    CentBConcl r (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)) := by
  obtain ⟨p, f, hm⟩ := hs.exists_linkModel hr (z2BigModelArith_holds r)
  exact centBConcl_congr (linkLayerEquiv hs.large) (centBConcl_of_model (z2BigModelCent_holds r) hr hm)

theorem Z2SetR.centAConcl_u (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r) :
    CentAConcl r (↥(linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) ⧸
      classicalInvolutionOddCore ↥(linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)) := by
  obtain ⟨g, -, -, hΛ⟩ := hs.exists_linkLayerAt_eq
  rw [hΛ]
  exact centAConcl_congr (conjQuotEquiv g (linkLayer R t)) (hs.centAConcl_t hr)

theorem Z2SetR.centBConcl_u (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r) :
    CentBConcl r (↥(linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) ⧸
      classicalInvolutionOddCore ↥(linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)) := by
  obtain ⟨g, -, -, hΛ⟩ := hs.exists_linkLayerAt_eq
  rw [hΛ]
  exact centBConcl_congr (conjQuotEquiv g (linkLayer R t)) (hs.centBConcl_t hr)

theorem Z2SetR.innerModOdd_t_of_cent_T₀ (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r) {x : Y}
    (hxt : x ∈ Subgroup.centralizer ({t} : Set Y)) (hx2 : x * x = 1)
    (hxT : ∀ q ∈ T₀, x * q = q * x) : InnerModOdd (linkLayer R t) x := by
  obtain ⟨e, -⟩ := hs.exists_quat_T₀ hr
  exact cent_b_of_concl hs.T₀_le_linkLayer hs.hT₀.2.1 e (hs.centBConcl_t hr)
    (hs.mem_normalizer_linkLayer hxt) hx2 hxT

theorem Z2SetR.innerModOdd_u_of_cent_R₀ (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r) {x : Y}
    (hxu : x ∈ Subgroup.centralizer ({u} : Set Y)) (hx2 : x * x = 1)
    (hxR : ∀ q ∈ R₀, x * q = q * x) :
    InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) x := by
  obtain ⟨e, -⟩ := hs.exists_quat_R₀ hr
  exact cent_b_of_concl hs.R₀_le_linkLayerAt hs.hR₀.2.1 e (hs.centBConcl_u hr)
    (hs.mem_normalizer_linkLayerAt hxu) hx2 hxR

theorem Z2SetR.mem_omegaNbr_J_of_isSylow2In (hs : Z2SetR r n R S t J u R₀ T₀ P) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) (hLJ : L ≠ J) {W : Subgroup Y}
    (hW : IsSylow2In W L) (hWu : W ≤ Subgroup.centralizer ({u} : Set Y)) :
    L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J :=
  ⟨hL, hLJ, W, mem_RSet_of_isSylow2In hL hW, hW.1, fun x hx =>
    (TightLargeHypR.typeRFam hs.large).tight J hs.hJ.1 u hs.hu (hWu hx)⟩

theorem Z2SetR.le_linkLayerAt_of_le (hs : Z2SetR r n R S t J u R₀ T₀ P) {L : Subgroup Y}
    (hL : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) {W : Subgroup Y}
    (hW2 : IsPGroup 2 ↥W) (hWL : W ≤ L) (hWu : W ≤ Subgroup.centralizer ({u} : Set Y)) :
    W ≤ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u :=
  (le_coreAt u hW2 hWL hWu).trans (coreAt_le_linkLayerAt hL)

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
