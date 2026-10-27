module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3NC
public import CFSG.ClassicalInvolution.Q3.TL4E3C269GB
public import CFSG.ClassicalInvolution.Q3.TL4E3C17
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMaxOrb

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

theorem E3.image_conjSub_omegaNbr {G : Type} [Group G] {Ω : Set (Subgroup G)}
    (hc : ConjInvariant Ω) (K : Subgroup G) (g : G) :
    conjSub g '' omegaNbr Ω K = omegaNbr Ω (conjSub g K) := by
  ext M
  constructor
  · rintro ⟨M', hM', rfl⟩
    exact omegaNbr_conj hc hM' g
  · intro hM
    refine ⟨conjSub g⁻¹ M, ?_, conjSub_conjSub_inv g M⟩
    have h1 := omegaNbr_conj hc hM g⁻¹
    rwa [conjSub_inv_conjSub] at h1

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.oddCoreOf_orbGen_J_le_centralizer (hF : E3Frame n R S t J u) :
    oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)) ≤
      Subgroup.centralizer ({t} : Set Y) := by
  have hle := hF.orbGen_J_le_centralizer
  have hn : ((E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)).subgroupOf
      (Subgroup.centralizer ({u} : Set Y))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr fun c hc =>
      Generic.mem_normalizer_of_conjSub_eq (hF.conjSub_orbGen_J hc)
  have h1 : oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)) ≤
      oddCoreOf (Subgroup.centralizer ({u} : Set Y)) :=
    Balance.oddCoreIn_le_of_isSubnormal (isSubnormal_of_normal_subgroupOf hle hn)
  have hα := hF.alpha J hF.maxAdj.1.2 u hF.inv
  rw [Set.pair_comm] at hα
  exact h1.trans (E3.oddCore_le_centralizer_of_alpha hα hF.inv.ne_one)

theorem E3Frame.nbrGen_eq_orbGen_J (hF : E3Frame n R S t J u)
    (hO : omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)) :
    nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J =
      E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩG := hF.large.datum.hypOmegaGen
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  have hK₀J : tightCore R ∈ omegaNbr Ω J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩG hF.maxAdj.1.1 hJn.1 hJn
  apply le_antisymm
  · refine iSup₂_le fun M hM => ?_
    exact le_iSup₂ (f := fun N (_ : N ∈ orbOf (TC.nbrAdj Ω) J (tightCore R)) => N) M (hO hM.2)
  · refine iSup₂_le fun M hM => ?_
    obtain ⟨l, hl, rfl⟩ := hM
    have hK : tightCore R ≤ nbrGen (TC.nbrAdj Ω) J :=
      le_iSup₂ (f := fun N (_ : N ∈ {N : Subgroup Y | TC.nbrAdj Ω J N}) => N) (tightCore R)
        ⟨hJn.1, hK₀J⟩
    calc conjSub l (tightCore R) ≤ conjSub l (nbrGen (TC.nbrAdj Ω) J) := conjSub_mono hK
      _ = nbrGen (TC.nbrAdj Ω) J := conjSub_eq_self_of_mem hl

@[expose] def TightSecGenS3 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)), TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht) →
      TightEdgeless (secR R u) → ¬ TightInO2 (E3.secT htu ht) →
        ∀ s : SecQ R u, E3.secT htu ht * s = s * E3.secT htu ht → s ≠ E3.secT htu ht →
          (∃ g : SecQ R u, s = g * E3.secT htu ht * g⁻¹) →
            Subgroup.centralizer ({E3.secT htu ht} : Set (SecQ R u)) ⊔
              Subgroup.centralizer ({s} : Set (SecQ R u)) = ⊤

theorem tightE3S3NotBeta_of_gen (hG : TightSecGenS3 n) : TightE3S3NotBeta n := by
  intro Y _ _ R S t J u hF htu ht Sb hex hedge _ hnE2 h163 L hLπ hLs _ heq
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set Φ := omegaNbr Ω (tightCore R) with hΦdef
  have hd := hF.large.datum
  have hΩG := hd.hypOmegaGen
  have hc : ConjInvariant Ω := hΩG.conjInvariant
  have h := TightLargeHypR.typeRFam hF.large
  have hJn : J ∈ Φ := hF.maxAdj.1.2
  have hK₀Ω : tightCore R ∈ Ω := CoreAssembly.mem_conjClass_self _
  have hCt : Subgroup.centralizer ({t} : Set Y) ≤
      Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) :=
    h.tight _ hK₀Ω t hd.isUniqueInvolution_core
  have hO := hF.omegaNbr_subset_orbOf htu ht h163
  obtain ⟨x, hxN, hxK⟩ := hLπ
  have hsL : IsUniqueInvolution L (x * t * x⁻¹) := hxK ▸ hd.isUniqueInvolution_core.conj x
  obtain ⟨-, -, U, hU, hUK, hUN⟩ := Q3T6.Mu.omegaStarNbr_symm hΩG hK₀Ω hLs.1 hLs
  obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := Sec6Gen.exists_data_of_mem_USet hΩG hU
  have htU : t ∈ U := T3.mem_of_isPGroup hd.isUniqueInvolution_core hUK
    (Sec6Gen.isPGroup_of_mem_USet hΩG hU) (le_trans (by norm_num) hU4)
  have htL : conjSub t L = L := mem_normalizer_iff_conjSub_eq.mp (hUN htU)
  have hts : t * (x * t * x⁻¹) * t⁻¹ = x * t * x⁻¹ := hsL.conj_eq htL
  have hcomm : x * t * x⁻¹ * t = t * (x * t * x⁻¹) := by
    calc x * t * x⁻¹ * t = t * (x * t * x⁻¹) * t⁻¹ * t := by rw [hts]
      _ = t * (x * t * x⁻¹) := by group
  have hxt : x * t * x⁻¹ ≠ t := by
    intro hst
    apply hLs.2.1
    rw [← hxK]
    refine mem_normalizer_iff_conjSub_eq.mp (hCt ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [hst]
  have hX := hF.le_sup_of_secGen hO htu ht (hG Y R S t J u hF htu ht Sb hex hedge hnE2) hxN hxt
    hcomm
  set P := piGen Φ with hPdef
  have hnormΦ : ∀ c : Y, conjSub c '' Φ = Φ → c ∈ Subgroup.normalizer (P : Set Y) := by
    intro c hcΦ
    refine Generic.mem_normalizer_of_conjSub_eq ?_
    rw [hPdef, ← piGen_conj, hcΦ]
  have hCtP : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (P : Set Y) := by
    intro c hc'
    refine hnormΦ c ?_
    rw [hΦdef, E3.image_conjSub_omegaNbr hc, mem_normalizer_iff_conjSub_eq.mp (hCt hc')]
  have hxP : x ∈ Subgroup.normalizer (P : Set Y) := by
    refine hnormΦ x ?_
    rw [hΦdef, E3.image_conjSub_omegaNbr hc, hxK, heq]
  have hXeq := hF.nbrGen_eq_orbGen_J hO
  have hOX : oddCoreOf (nbrGen (TC.nbrAdj Ω) J) ≤ Subgroup.centralizer ({t} : Set Y) := by
    rw [hXeq]
    exact hF.oddCoreOf_orbGen_J_le_centralizer
  have hXP : nbrGen (TC.nbrAdj Ω) J ≤ Subgroup.normalizer (P : Set Y) :=
    hX.trans (sup_le (sup_le (inf_le_right.trans hCtP) (Subgroup.zpowers_le.mpr hxP))
      (hOX.trans hCtP))
  have hNt : nbrGen (TC.nbrAdj Ω) (tightCore R) ≤ Subgroup.centralizer ({t} : Set Y) :=
    iSup₂_le fun M hM => hF.le_centralizer_of_mem_omegaNbr hK₀Ω hM.2 hd.isUniqueInvolution_core
  have hXgP : E3.orbGen Ω (tightCore R) J ≤ P := by
    refine iSup₂_le fun M hM => ?_
    obtain ⟨l, hl, rfl⟩ := hM
    refine le_piGen ?_
    have h1 := omegaNbr_conj hc hJn l
    rwa [mem_normalizer_iff_conjSub_eq.mp (hCt (hNt hl))] at h1
  have htop := hF.eq_top_of_orbGen_le (H := Subgroup.normalizer (P : Set Y))
    (hXgP.trans Subgroup.le_normalizer) (hXeq.symm.le.trans hXP)
  have hPn : P.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  obtain ⟨g, hg'⟩ := hJn.1
  have hgJ : conjSub g (tightCore R) = J := hg'
  have hJP : J ≤ P := le_piGen hJn
  have hPtop : (⊤ : Subgroup Y) ≤ P := by
    have hgen : (⨆ M ∈ Ω, M) = ⊤ := by
      rw [iSup_conjClass_eq]
      exact hF.large.cls.2.1
    rw [← hgen]
    refine iSup₂_le fun M hM => ?_
    obtain ⟨y, hy'⟩ := hM
    have hy : conjSub y (tightCore R) = M := hy'
    have hyJ : M = conjSub (y * g⁻¹) J := by rw [← hy, ← hgJ, conjSub_mul, conjSub_inv_conjSub]
    rw [hyJ]
    intro z hz
    rw [mem_conjSub_iff] at hz
    have h1 := hPn.conj_mem _ (hJP hz) (y * g⁻¹)
    rwa [show y * g⁻¹ * ((y * g⁻¹)⁻¹ * z * (y * g⁻¹)) * (y * g⁻¹)⁻¹ = z by group] at h1
  have hPt : P ≤ Subgroup.centralizer ({t} : Set Y) :=
    piGen_le fun M hM => hF.le_centralizer_of_mem_omegaNbr hK₀Ω hM hd.isUniqueInvolution_core
  have htZ : t ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPt (hPtop (Subgroup.mem_top y)))
  rw [hF.large.center, Subgroup.mem_bot] at htZ
  exact hd.isUniqueInvolution_core.ne_one htZ

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
