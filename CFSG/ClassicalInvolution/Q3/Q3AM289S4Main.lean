module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4Vtx
public import CFSG.ClassicalInvolution.Q3.Q3AM289VtxZ
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4Axis
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4Stmt
public import CFSG.ClassicalInvolution.Q3.Q3AMTri

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3CH
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.Q3NM
open scoped MatrixGroups commutatorElement

section Main

variable {G : Type} [Group G] [Finite G]

theorem pspS4Leaf_of_leaves (hV : S4VertexModelLeaf) (hL : S4LinkModelLeaf) : PspS4Leaf := by
  intro _hIH G _ _ _ Ω K J S R T W z t K' _hCIT h hS4
  classical
  have hbad := h.bad
  have hstd := hbad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hK : K ∈ Ω := hstd.stand.mem
  have hz := hstd.hz
  have ht := hstd.ht
  have hJ : J ∈ omegaNbr Ω K := hstd.hJ
  have hz2 : z * z = 1 := hz.sq
  have ht2 : t * t = 1 := ht.sq
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hJ ht
  have huK' : IsUniqueInvolution K' (z * t) := h.uniq_K'
  have hKJ : K ∈ omegaNbr Ω J := Q3CL.T3.omegaNbr_symm l6_2 hΩ hK hJ.1 hJ
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (isUniqueInvolution_comm hz hu)
  have hYC : nbrLayer Ω K z ≤ Subgroup.centralizer ({z} : Set G) := nbrLayer_le_centralizer Ω K z
  obtain ⟨hzY, J₁, J₂, hJ₁, hJ₂, -, hcomm₁₂, a₁, b₂, ha₁, hb₂, hab₁₂, hzne, -⟩ :=
    h.exists_layerPair
  obtain ⟨hzY', hSL, hcard⟩ : ∃ hz' : z ∈ nbrLayer Ω K z,
      S4Layer (layerFam Ω K z)
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z, hz'⟩) ∧
        ∀ N ∈ omegaNbr Ω K, Nat.card ↥(layerImage Ω K z N) = 24 := by
    rcases hS4 with ⟨ι, hι, D, ha, hS⟩ | ⟨ι, hι, D, ha, hS⟩ | ⟨ι, hι, D, ha, hS⟩
    · exact ⟨ha, Or.inl ⟨ι, hι, D, hS⟩, fun N hN => nbrExact_of_lieSystem D hN⟩
    · exact ⟨ha, Or.inr (Or.inl ⟨ι, hι, D, hS⟩), fun N hN => nbrExact_of_lieSystem D hN⟩
    · exact ⟨ha, Or.inr (Or.inr ⟨ι, hι, D, hS⟩), fun N hN => nbrExact_of_lieSystem D hN⟩
  have hzb := hSL.zb_mem_center
  have hConj : ConjInvariant (layerFam Ω K z) := layerFam_conjInvariant hbad
  have hPair : S4Pair (layerFam Ω K z)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z, hzY'⟩) :=
    ⟨hzne, J₁, hJ₁, J₂, hJ₂, a₁, b₂, ha₁, hb₂, hcomm₁₂, hab₁₂.symm⟩
  obtain ⟨hqs, hrow, htrans⟩ : CFSG.IsQuasisimple
      (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ∧
      AutOddFreeOn (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z))
        (fun f => ∃ A ∈ layerFam Ω K z, ∀ a ∈ A, f a = a) ∧
      ∀ A ∈ layerFam Ω K z, ∀ B ∈ layerFam Ω K z,
        ∃ g : ↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z),
          conjSub g A = B := by
    rcases hSL with h1 | h1 | h1
    · exact hV.1 _ _ _ hConj h1 hPair
    · exact hV.2.1 _ _ _ hConj h1 hPair
    · exact hV.2.2 _ _ _ hConj h1 hPair
  have hnc : ∀ N ∈ omegaNbr Ω K, ∀ r : G, IsUniqueInvolution N r → ∀ hrY : r ∈ nbrLayer Ω K z,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨r, hrY⟩ ∉
        Subgroup.center (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) := by
    intro N hN r hr hrY
    obtain ⟨hrY', hu⟩ := isUniqueInvolution_layerImage hbad hN hr
    exact classical_involution_not_central htrans hPair (modOddIn_mem_layerFam hN) hu
  obtain ⟨htY, hat⟩ := isUniqueInvolution_layerImage hbad hJ ht
  have hfr : S4Frame (layerFam Ω K z)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z, hzY'⟩)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨t, htY⟩) := by
    rcases hSL with h1 | h1 | h1
    · exact hL.1 _ _ _ hConj h1 hPair _ (modOddIn_mem_layerFam hJ) _ hat
    · exact hL.2.1 _ _ _ hConj h1 hPair _ (modOddIn_mem_layerFam hJ) _ hat
    · exact hL.2.2 _ _ _ hConj h1 hPair _ (modOddIn_mem_layerFam hJ) _ hat
  obtain ⟨Mb, hMb, b₁, u₁, hb₁, hba, hbz, hab₁, hu₁M, hu₁4, hu₁sq, hau₁, ⟨Cb, hCb, hCbu⟩, hgen⟩ :=
    hfr
  obtain ⟨N, hN, rfl⟩ := exists_of_mem_layerFam hMb
  obtain ⟨x', hx', hxu⟩ := hu₁M
  have hker : Odd (Nat.card (QuotientGroup.mk'
      (classicalInvolutionOddCore ↥(nbrLayer Ω K z))).ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.ComponentClassification.OddCore.odd_card _
  obtain ⟨k, hk⟩ := Q3T8.Asc77.exists_pow_orderOf_four_lift (QuotientGroup.mk'
    (classicalInvolutionOddCore ↥(nbrLayer Ω K z))) hker (x := x') (by rw [hxu]; exact hu₁4)
  have huN : ((x' ^ k : ↥(nbrLayer Ω K z)) : G) ∈ exactCore3 z N := by
    rw [Subgroup.coe_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_subgroupOf.mp hx') k
  have hu4 : orderOf ((x' ^ k : ↥(nbrLayer Ω K z)) : G) = 4 := by
    rw [Subgroup.orderOf_coe]
    exact hk
  have huY : ((x' ^ k : ↥(nbrLayer Ω K z)) : G) ∈ nbrLayer Ω K z := (x' ^ k).2
  have hcomm : ⁅t, ((x' ^ k : ↥(nbrLayer Ω K z)) : G)⁆ ∈ oddCoreOf (nbrLayer Ω K z) := by
    have hmk : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z))
        ⟨((x' ^ k : ↥(nbrLayer Ω K z)) : G), huY⟩ =
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) x') ^ k := by
      rw [← map_pow]
    have himgs : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨t, htY⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z))
          ⟨((x' ^ k : ↥(nbrLayer Ω K z)) : G), huY⟩ =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z))
          ⟨((x' ^ k : ↥(nbrLayer Ω K z)) : G), huY⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨t, htY⟩ := by
      rw [hmk, hxu]
      exact (Commute.pow_right hau₁ k).eq
    exact (mk_comm_eq_iff htY huY).mp himgs
  have hK'u := isUniqueInvolution_layerImage hbad h.nbrK huK'
  obtain ⟨hztY, hK'u⟩ := hK'u
  have hπzt : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z * t, hztY⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z, hzY'⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨t, htY⟩ := by
    rw [← map_mul]
    rfl
  have himgJ : layerImage Ω K z N ≠ layerImage Ω K z J := by
    intro heq
    have h1 : IsUniqueInvolution (layerImage Ω K z N)
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨t, htY⟩) := by
      rw [heq]
      exact hat
    exact hba (hb₁.eq h1)
  have himgK' : layerImage Ω K z N ≠ layerImage Ω K z K' := by
    intro heq
    have h1 : IsUniqueInvolution (layerImage Ω K z N)
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z * t, hztY⟩) := by
      rw [heq]
      exact hK'u
    exact hbz ((hb₁.eq h1).trans hπzt)
  obtain ⟨s, p, b₀, hp, hb₀, hub, hs, hax⟩ :=
    exists_s4Axis h hN huN hu4 hcomm himgJ himgK'
  obtain ⟨hb₀Y, hb₀u⟩ := isUniqueInvolution_layerImage hbad hN hb₀
  have hb₀b₁ : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨b₀, hb₀Y⟩ = b₁ :=
    hb₀u.eq hb₁
  have hpY : p ∈ nbrLayer Ω K z := oddCoreOf_le_self _ hp
  have hsY : s ∈ nbrLayer Ω K z := by
    rw [hs]
    exact (nbrLayer Ω K z).mul_mem ((nbrLayer Ω K z).mul_mem hpY hb₀Y)
      ((nbrLayer Ω K z).inv_mem hpY)
  have hπp : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨p, hpY⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (mem_oddCoreOf_iff.mp hp).2
  have hπs : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨s, hsY⟩ = b₁ := by
    have e : (⟨s, hsY⟩ : ↥(nbrLayer Ω K z)) = ⟨p, hpY⟩ * ⟨b₀, hb₀Y⟩ * ⟨p, hpY⟩⁻¹ :=
      Subtype.ext hs
    rw [e, map_mul, map_mul, map_inv, hπp, ← hb₀b₁]
    simp
  have hs2 : s * s = 1 := hax.sq
  have hzs : z * s = s * z := hax.comm_z
  have hst : t * s = s * t := hax.comm_t
  have hzcl : z ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have htcl : t ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have hne : z ≠ t := fun e => by
    have : IsUniqueInvolution J z := e ▸ ht
    exact hJ.2.1 (hnt K hK J ⟨hJ.1, z, hz, this⟩)
  have hts : t ≠ s := fun e => hax.indep (e ▸ htcl)
  have hzs' : z ≠ s := fun e => hax.indep (e ▸ hzcl)
  have hts2 : (t * s) * (t * s) = 1 := by
    calc t * s * (t * s) = t * (s * t) * s := by group
      _ = t * (t * s) * s := by rw [← hst]
      _ = (t * t) * (s * s) := by group
      _ = 1 := by rw [ht2, hs2, one_mul]
  have hzts : z * (t * s) = (t * s) * z := by
    calc z * (t * s) = (z * t) * s := by group
      _ = (t * z) * s := by rw [hzt]
      _ = t * (z * s) := by group
      _ = t * (s * z) := by rw [hzs]
      _ = (t * s) * z := by group
  have hts1 : t * s ≠ 1 := fun e => hts (by
    have h1 : s = t⁻¹ := eq_inv_of_mul_eq_one_right e
    rw [h1, inv_eq_of_mul_eq_one_right ht2])
  have hztsne : z ≠ t * s := fun e => hax.indep (by
    have h1 : s = t * z := by
      calc s = t * (t * s) := by rw [← mul_assoc, ht2, one_mul]
        _ = t * z := by rw [← e]
    rw [h1]
    exact Subgroup.mul_mem _ htcl hzcl)
  have hzs2 : (z * s) * (z * s) = 1 := by
    calc z * s * (z * s) = z * (s * z) * s := by group
      _ = z * (z * s) * s := by rw [← hzs]
      _ = (z * z) * (s * s) := by group
      _ = 1 := by rw [hz2, hs2, one_mul]
  have hzts2' : (z * t * s) * (z * t * s) = 1 := by
    have hzt2 : (z * t) * (z * t) = 1 := by
      calc z * t * (z * t) = z * (t * z) * t := by group
        _ = z * (z * t) * t := by rw [← hzt]
        _ = (z * z) * (t * t) := by group
        _ = 1 := by rw [hz2, ht2, one_mul]
    have hzts' : (z * t) * s = s * (z * t) := by
      calc (z * t) * s = z * (t * s) := by group
        _ = z * (s * t) := by rw [hst]
        _ = (z * s) * t := by group
        _ = (s * z) * t := by rw [hzs]
        _ = s * (z * t) := by group
    calc z * t * s * (z * t * s) = (z * t) * (s * (z * t)) * s := by group
      _ = (z * t) * ((z * t) * s) * s := by rw [← hzts']
      _ = ((z * t) * (z * t)) * (s * s) := by group
      _ = 1 := by rw [hzt2, hs2, one_mul]
  have htsY : t * s ∈ nbrLayer Ω K z := (nbrLayer Ω K z).mul_mem htY hsY
  have hzsY : z * s ∈ nbrLayer Ω K z := (nbrLayer Ω K z).mul_mem hzY' hsY
  have hztsY : z * t * s ∈ nbrLayer Ω K z := (nbrLayer Ω K z).mul_mem hztY hsY
  have hπts : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨t * s, htsY⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨t, htY⟩ * b₁ := by
    rw [← hπs, ← map_mul]
    rfl
  have hπzs : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z * s, hzsY⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z, hzY'⟩ * b₁ := by
    rw [← hπs, ← map_mul]
    rfl
  have hπzts : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z))
      ⟨z * t * s, hztsY⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z, hzY'⟩ *
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨t, htY⟩ * b₁) := by
    rw [← hπs, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mul_assoc z t s)
  have hCbu' : IsUniqueInvolution Cb (QuotientGroup.mk'
      (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨t * s, htsY⟩) := by
    rw [hπts]
    exact hCbu
  obtain ⟨N₂, hN₂, hN₂u⟩ := exists_nbr_of_image_involution hbad htsY hts2 hCb hCbu'
  have hK'u' : IsUniqueInvolution (layerImage Ω K z K')
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨z, hzY'⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨t, htY⟩) := by
    rw [← hπzt]
    exact hK'u
  obtain ⟨D, hD, hDu⟩ := exists_partner_member hzb hConj htrans (modOddIn_mem_layerFam hJ)
    (modOddIn_mem_layerFam h.nbrK) hat hK'u' (modOddIn_mem_layerFam hN) hb₁
  obtain ⟨D', hD', hD'u⟩ := exists_partner_member hzb hConj htrans (modOddIn_mem_layerFam hJ)
    (modOddIn_mem_layerFam h.nbrK) hat hK'u' hCb hCbu
  obtain ⟨N₃, hN₃, hN₃u⟩ := exists_nbr_of_image_involution hbad hzsY hzs2 hD
    (by rw [hπzs]; exact hDu)
  obtain ⟨N₄, hN₄, hN₄u⟩ := exists_nbr_of_image_involution hbad hztsY hzts2' hD'
    (by rw [hπzts]; exact hD'u)
  obtain ⟨L, hL, hLs, -, -⟩ := hax.nbr
  have hB : IsElemAbelian 2 (Subgroup.closure ({z, t, s} : Set G)) :=
    T8T.isElemAbelian_closure_three hz2 ht2 hs2 hzt hzs hst
  have hBtq : Subgroup.closure ({z, t, s} : Set G) ≤ trivialOnQuot K := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ExactLayer.mem_trivialOnQuot_of_le_centralizer hKz
    · exact (xMem_of_omegaNbr hΩ hnt ht hKJ hz).trivialOnQuot3 hΩ ht2
    · have hKL : K ∈ omegaNbr Ω L := Q3CL.T3.omegaNbr_symm l6_2 hΩ hK hL.1 hL
      exact (xMem_of_omegaNbr hΩ hnt hLs hKL hz).trivialOnQuot3 hΩ hs2
  have hzB : z ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.subset_closure (by simp)
  have hsB : s ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.subset_closure (by simp)
  have hvtx : ∀ {M : Subgroup G} {c : G}, M ∈ omegaNbr Ω K → IsUniqueInvolution M c →
      c ∈ Subgroup.closure ({z, t, s} : Set G) → z ≠ c →
        Hyp51At (Subgroup.closure ({z, t, s} : Set G)) c := fun hM hc hcB hzc =>
    hyp51At_of_nbr_vertex hbad hqs hrow hnc hcard hM hc hB hcB hzB hzc (fun b hb => hBtq hb)
  have hz1 := hz.ne_one
  have ht1 := ht.ne_one
  have hs1 := hax.ne_one
  have hztne : z ≠ z * t := fun e => ht1 (mul_left_cancel (a := z) (by rw [mul_one]; exact e)).symm
  have hzsne : z ≠ z * s := fun e => hs1 (mul_left_cancel (a := z) (by rw [mul_one]; exact e)).symm
  have hztsne' : z ≠ z * t * s := fun e => by
    have h1 : t * s = 1 := by
      have : z * (t * s) = z * 1 := by rw [mul_one, ← mul_assoc]; exact e.symm
      exact mul_left_cancel this
    exact hts1 h1
  have htsB : t * s ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.mul_mem _ htB hsB
  have hztB : z * t ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.mul_mem _ hzB htB
  have hzsB : z * s ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.mul_mem _ hzB hsB
  have hztsB : z * t * s ∈ Subgroup.closure ({z, t, s} : Set G) :=
    Subgroup.mul_mem _ hztB hsB
  have vz : Hyp51At (Subgroup.closure ({z, t, s} : Set G)) z :=
    hyp51At_z_of_three_members hbad hL hLs hN₂ hN₂u hzs hst hax.indep
  have vt : Hyp51At (Subgroup.closure ({z, t, s} : Set G)) t ∧
      Hyp51At (Subgroup.closure ({z, t, s} : Set G)) s ∧
        Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (t * s) :=
    ⟨hvtx hJ ht htB hne, hvtx hL hLs hsB hzs', hvtx hN₂ hN₂u htsB hztsne⟩
  have va : Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (z * t) ∧
      Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (z * s) ∧
        Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (z * t * s) :=
    ⟨hvtx h.nbrK huK' hztB hztne, hvtx hN₃ hN₃u hzsB hzsne, hvtx hN₄ hN₄u hztsB hztsne'⟩
  have hlink : ∀ J' ∈ omegaNbr Ω K, ∀ t' : G, IsUniqueInvolution J' t' →
      ∃ y ∈ rankTwoSpan (Subgroup.closure ({z, t, s} : Set G)),
        y * z * y⁻¹ = z ∧ y * t * y⁻¹ = t' := by
    intro J' hJ' t' ht'
    have hzt' : z * t' = t' * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hJ' ht'
    have ht'Y : t' ∈ nbrLayer Ω K z := mem_nbrLayer_of_mem hJ' ht'.mem hzt'.symm
    have hzΛ : z ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hΛN := hbad.centralizer_le_normalizer_nbrLayer hK hz
    have hzX := commutator_self_mem_oddCoreOf_nbrLayer Ω K z
    have hBcard : Nat.card ↥(Subgroup.closure ({z, t, s} : Set G)) = 8 :=
      T8T.natCard_closure_three hz2 ht2 hs2 hzt hzs hst hz1 ht1 hne hs1 hax.indep
    have hBN : Subgroup.closure ({z, t, s} : Set G) ≤
        Subgroup.normalizer ((oddCoreOf (nbrLayer Ω K z) : Subgroup G) : Set G) := by
      rw [Subgroup.closure_le]
      intro g hg
      have hgN : g ∈ Subgroup.normalizer ((nbrLayer Ω K z : Subgroup G) : Set G) := by
        rcases hg with rfl | rfl | rfl
        · exact hΛN hzΛ
        · exact Subgroup.le_normalizer htY
        · exact Subgroup.le_normalizer hsY
      exact mem_normalizer_oddCore_of_mem_normalizer hgN
    have hOH : oddCoreOf (nbrLayer Ω K z) ≤
        rankTwoSpan (Subgroup.closure ({z, t, s} : Set G)) := by
      have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
        Nat.prime_two (Subgroup.closure ({z, t, s} : Set G)) (oddCoreOf (nbrLayer Ω K z)) hB
        (by norm_num [hBcard]) hBN (Nat.coprime_two_left.mpr (oddCoreOf_odd_natCard _))
      conv_lhs => rw [← hgen]
      exact iSup₂_le fun F hF => le_rankTwoSpan_of_le_centralizer hF inf_le_right
    have hHc : ∀ c : G, c ∈ Subgroup.closure ({z, t, s} : Set G) → c * c = 1 → c ≠ 1 → z ≠ c →
        z * c = c * z → Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) ≤
          rankTwoSpan (Subgroup.closure ({z, t, s} : Set G)) := by
      intro c hcB hc2 hc1 hzc hzc'
      have hD := T7A.isElemAbelian2_closure_pair hz2 hc2 hz1 hc1 hzc hzc'
      have hFB : Subgroup.closure ({z, c} : Set G) ∈
          signalizerFunctorEk 2 2 (Subgroup.closure ({z, t, s} : Set G)) := by
        refine ⟨?_, by simpa using hD.1⟩
        rw [Subgroup.closure_le]
        rintro y (rfl | rfl)
        · exact Subgroup.subset_closure (by simp)
        · exact hcB
      refine le_rankTwoSpan_of_le_centralizer hFB ?_
      intro g hg
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      rintro y (rfl | rfl)
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hg.1).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hg.2).symm
    obtain ⟨ht'Y', hu'⟩ := isUniqueInvolution_layerImage hbad hJ' ht'
    obtain ⟨g, hg⟩ := htrans _ (modOddIn_mem_layerFam hJ) _ (modOddIn_mem_layerFam hJ')
    have hq1 : IsUniqueInvolution (layerImage Ω K z J')
        (g * QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨t, htY⟩ * g⁻¹) := by
      have hg' : conjSub g (layerImage Ω K z J) = layerImage Ω K z J' := hg
      have h1 := hat.conj g
      rw [hg'] at h1
      exact h1
    have hgen' := hgen
    rw [← hπs] at hgen'
    exact link_conj_of_frame (X := nbrLayer Ω K z) (Λ := Subgroup.centralizer ({z} : Set G))
      (H := rankTwoSpan (Subgroup.closure ({z, t, s} : Set G))) hYC hΛN hzΛ hz2 hzX htY hsY ht'Y
      ht2 hs2 ht'.sq hts hzt hzs hzt' hst hOH
      (hHc t htB ht2 ht1 hne hzt) (hHc s hsB hs2 hs1 hzs' hzs)
      (hHc (t * s) htsB hts2 hts1 hztsne hzts) ⟨g, (hu'.eq hq1).symm⟩ hgen'
  exact s3_false_of_frame hbad hax vz vt va hlink

end Main

end CFSG.ClassicalInvolution.Q3.Q3AM
