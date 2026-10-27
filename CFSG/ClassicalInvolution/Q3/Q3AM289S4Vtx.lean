module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4Lay

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

section Vtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
  {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem commutator_mem_oddCoreOf_layer_of_trivialOnQuot {K₀ Y : Subgroup G} {c z₀ b k : G}
    (hK₀ : IsClassicalMember3 K₀ z₀) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hcK : c ∈ trivialOnQuot K₀) (hLY : exactCore3 c K₀ ≤ Y)
    (hcard : Nat.card ↥(Subgroup.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y))
      ((exactCore3 c K₀).subgroupOf Y)) = 24)
    (hb : b ∈ trivialOnQuot K₀) (hbc : b ∈ Subgroup.centralizer ({c} : Set G))
    (hk : k ∈ exactCore3 c K₀) : ⁅b, k⁆ ∈ oddCoreOf Y := by
  have hcomm : ⁅b, k⁆ ∈ oddCoreOf K₀ := hb.2 k hk.1
  have hbK : conjSub b K₀ = K₀ := mem_normalizer_iff_conjSub_eq.mp hb.1
  have hmem : ⁅b, k⁆ ∈ exactCore3 c K₀ := by
    have e : ⁅b, k⁆ = (b * k * b⁻¹) * k⁻¹ := by rw [commutatorElement_def]
    rw [e]
    have h1 : b * k * b⁻¹ ∈ K₀ := mem_of_conjSub_eq hbK hk.1
    have h2 : b * k * b⁻¹ ∈ Subgroup.centralizer ({c} : Set G) :=
      (Subgroup.centralizer ({c} : Set G)).mul_mem
        ((Subgroup.centralizer ({c} : Set G)).mul_mem hbc hk.2)
        ((Subgroup.centralizer ({c} : Set G)).inv_mem hbc)
    exact ⟨K₀.mul_mem h1 (K₀.inv_mem hk.1), (Subgroup.centralizer ({c} : Set G)).mul_mem h2
      ((Subgroup.centralizer ({c} : Set G)).inv_mem hk.2)⟩
  have hO : ⁅b, k⁆ ∈ oddCoreOf (exactCore3 c K₀) := by
    have h1 : Balance.oddCoreIn (exactCore3 c K₀) = exactCore3 c K₀ ⊓ Balance.oddCoreIn K₀ :=
      oddCoreIn_exactCore3 hK₀ hc2 hcK
    have h2 : ⁅b, k⁆ ∈ Balance.oddCoreIn (exactCore3 c K₀) := by
      rw [h1]
      exact ⟨hmem, hcomm⟩
    exact h2
  exact oddCoreOf_le_of_card_image hLY hcard
    (isSectionMember3_exactCore3 hK₀ hc2 hcK).nonempty_equiv hO

theorem oddQuot_conj_eq_of_commutator {c b k : G} (hbC : b ∈ Subgroup.centralizer ({c} : Set G))
    (hkC : k ∈ Subgroup.centralizer ({c} : Set G))
    (h : ⁅b, k⁆ ∈ oddCoreOf (Subgroup.centralizer ({c} : Set G))) :
    oddQuotMk c ⟨b, hbC⟩ * oddQuotMk c ⟨k, hkC⟩ * (oddQuotMk c ⟨b, hbC⟩)⁻¹ =
      oddQuotMk c ⟨k, hkC⟩ := by
  have hcomm : (⁅(⟨b, hbC⟩ : ↥(Subgroup.centralizer ({c} : Set G))), ⟨k, hkC⟩⁆ :
      ↥(Subgroup.centralizer ({c} : Set G))) ∈
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G)) := by
    obtain ⟨hx, h3⟩ := mem_oddCoreOf_iff.mp h
    exact h3
  have h4 := (QuotientGroup.eq_one_iff _).mpr hcomm
  have h5 : (oddQuotMk c) (⁅(⟨b, hbC⟩ : ↥(Subgroup.centralizer ({c} : Set G))), ⟨k, hkC⟩⁆ :
      ↥(Subgroup.centralizer ({c} : Set G))) = 1 := h4
  rw [map_commutatorElement] at h5
  have := commutatorElement_eq_one_iff_mul_comm.mp h5
  rw [mul_inv_eq_iff_eq_mul]
  exact this

theorem hyp51At_of_nbr_vertex [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    (hq : CFSG.IsQuasisimple
      (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)))
    (hrow : AutOddFreeOn (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z))
      (fun f => ∃ A ∈ layerFam Ω K z, ∀ a ∈ A, f a = a))
    (hnc : ∀ N ∈ omegaNbr Ω K, ∀ r : G, IsUniqueInvolution N r → ∀ hrY : r ∈ nbrLayer Ω K z,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨r, hrY⟩ ∉
        Subgroup.center (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)))
    (hcard : ∀ N ∈ omegaNbr Ω K, Nat.card ↥(layerImage Ω K z N) = 24)
    {M : Subgroup G} (hM : M ∈ omegaNbr Ω K) {c : G} (hc : IsUniqueInvolution M c)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hcB : c ∈ B) (hzB : z ∈ B) (hzc : z ≠ c)
    (hBtq : ∀ b ∈ B, b ∈ trivialOnQuot K) : Hyp51At B c := by
  classical
  have hstd := h.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hz := hstd.hz
  have hK : K ∈ Ω := hstd.stand.mem
  have hKM : K ∈ omegaNbr Ω M := Q3CL.T3.omegaNbr_symm l6_2 hΩ hK hM.1 hM
  have hzc' : z * c = c * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hM hc
  obtain ⟨g, hg⟩ := hstd.stand.trans M hM.1
  have hz' : IsUniqueInvolution M (g * z * g⁻¹) := hg ▸ hz.conj g
  have hcg : c = g * z * g⁻¹ := hc.eq hz'
  obtain ⟨Y', hY'⟩ : ∃ Y' : Subgroup G, Y' = nbrLayer Ω M c := ⟨_, rfl⟩
  have hYC : Y' ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [hY']
    exact nbrLayer_le_centralizer Ω M c
  have hCY : ∀ y ∈ Subgroup.centralizer ({c} : Set G), conjSub y Y' = Y' := by
    intro y hy
    rw [hY']
    exact mem_normalizer_iff_conjSub_eq.mp (h.centralizer_le_normalizer_nbrLayer hM.1 hc hy)
  have hY'conj : Y' = conjSub g (nbrLayer Ω K z) := by
    rw [hY', ← hg, hcg]
    exact nbrLayer_conj hΩ.conjInvariant g K z
  have hzY' : z ∈ Y' := by
    rw [hY']
    exact mem_nbrLayer_of_mem hKM hz.mem hzc'
  have hLY : exactCore3 c K ≤ Y' := by
    rw [hY']
    exact exactCore3_le_nbrLayer hKM
  subst hY'conj
  have hq' : CFSG.IsQuasisimple (↥(conjSub g (nbrLayer Ω K z)) ⧸
      classicalInvolutionOddCore ↥(conjSub g (nbrLayer Ω K z))) :=
    CFSG.ClassicalInvolution.Asc77.AscFusion.isQuasisimple_of_mulEquiv
      (Q3AM289.conjSect (nbrLayer Ω K z) g).symm hq
  have hN₀ : conjSub g⁻¹ K ∈ omegaNbr Ω K := by
    have := omegaNbr_conj hΩ.conjInvariant hKM g⁻¹
    rwa [← hg, conjSub_inv_conjSub] at this
  have hw₀ : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
    have := hz.conj g⁻¹
    rwa [inv_inv] at this
  obtain ⟨hw₀Y, -⟩ := isUniqueInvolution_layerImage h hN₀ hw₀
  have hnc₀ := hnc _ hN₀ _ hw₀ hw₀Y
  set e := Q3AM289.conjSect (nbrLayer Ω K z) g with he
  set e2 := layerQuotEquiv hYC hCY with he2
  have hwnc : QuotientGroup.mk' (classicalInvolutionOddCore ↥(conjSub g (nbrLayer Ω K z)))
      ⟨z, hzY'⟩ ∉ Subgroup.center (↥(conjSub g (nbrLayer Ω K z)) ⧸
        classicalInvolutionOddCore ↥(conjSub g (nbrLayer Ω K z))) := by
    intro hcen
    apply hnc₀
    have hmk : e (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z))
        ⟨g⁻¹ * z * g, hw₀Y⟩) =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(conjSub g (nbrLayer Ω K z)))
          ⟨z, hzY'⟩ := by
      have := congrArg (fun F => F ⟨g⁻¹ * z * g, hw₀Y⟩)
        (Q3AM289.conjSect_comp_mk (nbrLayer Ω K z) g)
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
      rw [he, this]
      congr 1
      apply Subtype.ext
      show g * (g⁻¹ * z * g) * g⁻¹ = z
      group
    rw [Subgroup.mem_center_iff]
    intro x
    apply e.injective
    rw [map_mul, map_mul, hmk]
    exact Subgroup.mem_center_iff.mp hcen (e x)
  have hrow' := autOddFreeOn_of_mulEquiv (e.trans e2) _ hrow
  refine hyp51At_of_layer hB hcB hc.ne_one hzB hz.ne_one hzc hYC hCY hq' hzY' hwnc _ hrow' ?_
  intro x hx
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨b', hb', hb'n⟩ := Subgroup.mem_subgroupOf.mp hn
  have hbB : (b' : G) ∈ B := Subgroup.mem_subgroupOf.mp hb'
  have hb'C : (b' : G) ∈ Subgroup.centralizer ({c} : Set G) := b'.2
  refine ⟨layerImage Ω K z (conjSub g⁻¹ K), modOddIn_mem_layerFam hN₀, ?_⟩
  intro a ha
  obtain ⟨k', hk', rfl⟩ := ha
  have hk : (k' : G) ∈ exactCore3 z (conjSub g⁻¹ K) := Subgroup.mem_subgroupOf.mp hk'
  have hexact : exactCore3 c K = conjSub g (exactCore3 z (conjSub g⁻¹ K)) := by
    have h1 := exactCore3_conjSub g z (conjSub g⁻¹ K)
    rw [conjSub_conjSub_inv, ← hcg] at h1
    exact h1
  have hkk : g * (k' : G) * g⁻¹ ∈ exactCore3 c K := by
    rw [hexact]
    exact Subgroup.mem_map.mpr ⟨k', hk, rfl⟩
  have hkkC : g * (k' : G) * g⁻¹ ∈ Subgroup.centralizer ({c} : Set G) :=
    exactCore3_le_centralizer c K hkk
  have hcard_c : Nat.card ↥(Subgroup.map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(conjSub g (nbrLayer Ω K z))))
      ((exactCore3 c K).subgroupOf (conjSub g (nbrLayer Ω K z)))) = 24 := by
    have hL₀Y : exactCore3 z (conjSub g⁻¹ K) ≤ nbrLayer Ω K z := exactCore3_le_nbrLayer hN₀
    have h1 := Q3AM289.modOddIn_map_conjSect hL₀Y g
    have h2 : modOddIn (conjSub g (nbrLayer Ω K z)) (exactCore3 c K) =
        (modOddIn (nbrLayer Ω K z) (exactCore3 z (conjSub g⁻¹ K))).map
          (Q3AM289.conjSect (nbrLayer Ω K z) g).toMonoidHom := by
      rw [h1, hexact]
    have h3 : Nat.card ↥(modOddIn (conjSub g (nbrLayer Ω K z)) (exactCore3 c K)) = 24 := by
      rw [h2, Subgroup.card_map_of_injective
        (f := (Q3AM289.conjSect (nbrLayer Ω K z) g).toMonoidHom)
        (Q3AM289.conjSect (nbrLayer Ω K z) g).injective]
      exact hcard _ hN₀
    exact h3
  have hK₀ : IsClassicalMember3 K z :=
    isClassicalMember3_of_uniqueInvolution hstd.stand.modU hK hz
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) :=
    isPGroup_zpowers_of_mul_self_eq_one hc.sq hc.ne_one
  have hcK : c ∈ trivialOnQuot K :=
    (xMem_of_omegaNbr hΩ hnt hc hKM hz).trivialOnQuot3 hΩ hc.sq
  have hcomm := commutator_mem_oddCoreOf_layer_of_trivialOnQuot hK₀ hc2 hcK hLY hcard_c
    (hBtq _ hbB) hb'C hkk
  have hcommC : ⁅(b' : G), g * (k' : G) * g⁻¹⁆ ∈
      oddCoreOf (Subgroup.centralizer ({c} : Set G)) := by
    refine oddCoreOf_inf_le hCY ⟨hcomm, ?_⟩
    have e : ⁅(b' : G), g * (k' : G) * g⁻¹⁆ =
        ((b' : G) * (g * (k' : G) * g⁻¹) * (b' : G)⁻¹) * (g * (k' : G) * g⁻¹)⁻¹ := by
      rw [commutatorElement_def]
    rw [e]
    exact (Subgroup.centralizer ({c} : Set G)).mul_mem
      ((Subgroup.centralizer ({c} : Set G)).mul_mem
        ((Subgroup.centralizer ({c} : Set G)).mul_mem hb'C hkkC)
        ((Subgroup.centralizer ({c} : Set G)).inv_mem hb'C))
      ((Subgroup.centralizer ({c} : Set G)).inv_mem hkkC)
  have hfix := oddQuot_conj_eq_of_commutator hb'C hkkC hcommC
  have hetot : ((((e.trans e2) (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z))
      k')) : ↥(modOdd c (conjSub g (nbrLayer Ω K z)))) : OddQuot c) =
      oddQuotMk c ⟨g * (k' : G) * g⁻¹, hkkC⟩ := by
    have h1 := congrArg (fun F => F k') (Q3AM289.conjSect_comp_mk (nbrLayer Ω K z) g)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
    show ((e2 (e (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) k')) :
      ↥(modOdd c (conjSub g (nbrLayer Ω K z)))) : OddQuot c) = _
    rw [he, h1]
    exact layerQuotEquiv_mk hYC hCY _
  have hxfix : ((toInducedAutOn (modOdd c (conjSub g (nbrLayer Ω K z))) n :
      MulAut ↥(modOdd c (conjSub g (nbrLayer Ω K z)))) ((e.trans e2)
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) k')) :
        ↥(modOdd c (conjSub g (nbrLayer Ω K z)))) =
      (e.trans e2) (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) k') := by
    apply Subtype.ext
    show (n : OddQuot c) * (((e.trans e2) (QuotientGroup.mk'
      (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) k') : ↥(modOdd c (conjSub g
        (nbrLayer Ω K z)))) : OddQuot c) * (n : OddQuot c)⁻¹ = _
    rw [hetot, ← hb'n]
    exact hfix
  show (e.trans e2).symm ((toInducedAutOn (modOdd c (conjSub g (nbrLayer Ω K z))) n :
      MulAut ↥(modOdd c (conjSub g (nbrLayer Ω K z)))) ((e.trans e2)
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) k'))) =
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) k'
  rw [hxfix]
  exact (e.trans e2).symm_apply_apply _

end Vtx

end CFSG.ClassicalInvolution.Q3.Q3AM
