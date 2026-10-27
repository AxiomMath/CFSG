module

public import CFSG.ClassicalInvolution.SmallCases.NDBE4C
import CFSG.ClassicalInvolution.SmallCases.NDB5Layer
import CFSG.ClassicalInvolution.Asc77.WP3SCUGenA
import CFSG.ClassicalInvolution.Asc77.WP3ChainVGen3
import CFSG.ClassicalInvolution.Asc77.WP3FrameLieE
import CFSG.ClassicalInvolution.Asc77.AscT3UG2D4
import CFSG.ClassicalInvolution.Asc77.WP3LayerHyp
import CFSG.ClassicalInvolution.Asc77.WP3L52Main
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
import CFSG.Timmesfeld.ARS.CaseEFrame
import CFSG.Timmesfeld.ARS.CaseMLevi
import CFSG.Timmesfeld.ARS.Sec12Center
import CFSG.Timmesfeld.ARS.Sec13Closed
import CFSG.Timmesfeld.ARS.Sec13Maximal
import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G}

namespace ExoticLift

variable {C : ExoticCtx p f K z} (L : ExoticLift C)

theorem tbar_ne_zbar : oddQuotMk z ⟨L.t, L.ht⟩ ≠ oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ := by
  intro h
  apply L.ne₁
  apply C.eq_one_of_comm
  intro y
  rw [← L.htbar, h]
  exact oddQuotMk_central (Asc77.XCtx.hzC z) _

include L in
theorem Q_conj (c : OddQuot z) :
    (C.psi C.i₁).range.map (MulAut.conj c).toMonoidHom = (C.psi C.i₁).range := by
  have hK : modOdd z C.X.K = (C.X.psi C.i₀).range := by
    rw [← C.X.exactCore_K]
    exact C.K₀
  refine Layer.conj_range_eq C.X C.card_eq C.ne hK ⟨L.τ₁, L.htbar.symm⟩ ?_ ?_ L.tbar_ne_zbar c
  · exact fun h => L.ne₁ (C.psi_injective (L.htbar.symm.trans (h.trans (map_one _).symm)))
  · rw [← map_mul]
    have e : (⟨L.t, L.ht⟩ * ⟨L.t, L.ht⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 :=
      Subtype.ext L.uJ.sq
    rw [e, map_one]

include L in
theorem mem_normalizer_Q (c : OddQuot z) :
    c ∈ Subgroup.normalizer ((C.psi C.i₁).range : Set (OddQuot z)) := by
  rw [mem_normalizer_iff_conjSub_eq]
  exact L.Q_conj c

theorem swap_dichotomy {a b : G} (hbB : b ∈ L.B) {M : Subgroup G}
    (hM : M ∈ tqMembers (𝒞 K) z) (hMa : IsClassicalMember p f M a)
    {Ra : Subgroup (compModel C.D C.i₁).K}
    (hRa : Ra ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D)
    (hRaM : Ra.map (C.psi C.i₁) = modOdd z (exactCore z M))
    {xa : (compModel C.D C.i₁).K} (hUa : IsUniqueInvolution Ra xa) {s : G}
    (hsa : s * a * s⁻¹ = z) (hb'C : s⁻¹ * b * s ∈ Subgroup.centralizer ({z} : Set G)) :
    (∀ y ∈ (C.psi C.i₁).range,
        oddQuotMk z ⟨s⁻¹ * b * s, hb'C⟩ * y = y * oddQuotMk z ⟨s⁻¹ * b * s, hb'C⟩) ∨
      (∀ y ∈ (C.psi C.i₁).range, (oddQuotMk z ⟨s⁻¹ * b * s, hb'C⟩ * C.psi C.i₁ xa) * y =
        y * (oddQuotMk z ⟨s⁻¹ * b * s, hb'C⟩ * C.psi C.i₁ xa)) := by
  have hp2 := C.hS.odd
  have hq := C.hS.five
  have hΩ := C.X.hΩ
  have has : a = s⁻¹ * z * s := by
    calc a = s⁻¹ * (s * a * s⁻¹) * s := by group
      _ = s⁻¹ * z * s := by rw [hsa]
  have hv2 : oddQuotMk z ⟨s⁻¹ * b * s, hb'C⟩ * oddQuotMk z ⟨s⁻¹ * b * s, hb'C⟩ = 1 := by
    rw [← map_mul]
    have hb2 : b * b = 1 := Lemma52Proof.mul_self_eq_one_of_mem L.B_elem hbB
    have e : (⟨s⁻¹ * b * s, hb'C⟩ * ⟨s⁻¹ * b * s, hb'C⟩ :
        ↥(Subgroup.centralizer ({z} : Set G))) = 1 := Subtype.ext (by
      show s⁻¹ * b * s * (s⁻¹ * b * s) = 1
      rw [show s⁻¹ * b * s * (s⁻¹ * b * s) = s⁻¹ * (b * b) * s by group, hb2]
      group)
    rw [e, map_one]
  have hKM : conjSub s⁻¹ K = M := by
    have h1 : IsUniqueInvolution (conjSub s⁻¹ K) a := by
      have h2 := C.X.hKz.conj s⁻¹
      rwa [show s⁻¹ * z * s⁻¹⁻¹ = a by rw [inv_inv, ← has]] at h2
    exact C.noTwins M hM.1 _ ⟨hΩ.conjInvariant s⁻¹ K C.X.hK, a,
      ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hMa, h1⟩
  have hb'tq : s⁻¹ * b * s ∈ trivialOnQuot M := by
    have h := trivialOnQuot_conjSub (L.frameData₁.tq_B hp2 hq hΩ hbB) s⁻¹
    rwa [hKM, inv_inv] at h
  have hqM := Q27.isQuasisimple_modOdd_free C.X.hs C.D hp2 hq (exactCore_mem_exactFamily hM)
  have hcen := oddQuotMk_centralizes_modOdd_exactCore hMa C.X.hc2 hM.2 hb'tq hb'C hqM
  exact ExoticModel.involution_fund hp2 C.tag₁ (C.D.admissible C.i₁) (C.psi C.i₁)
    C.psi_injective hRa hUa (L.mem_normalizer_Q _) hv2
    (fun r hr => hcen _ (hRaM ▸ ⟨r, hr, rfl⟩))

theorem generation_z : CentralizerGenerationStar (𝒞 K) L.B z := by
  have hΩ := C.X.hΩ
  refine centralizerGenerationStar_of_components C.X.hs C.D (fun j k => ?_)
  have hJk := C.X.psi_mem_memberJoin j k
  rcases C.eq_or_eq j with rfl | rfl
  · refine mem_modOdd_of_commutes_gen hΩ.conjInvariant L.B_elem L.z_mem_B C.X.hKz.ne_one L.t_mem_B
      L.uJ.ne_one L.t_ne_z hJk (fun he => ?_)
    rw [show oddQuotMk z ⟨L.t, he⟩ = C.psi C.i₁ L.τ₁ from L.htbar]
    exact (C.X.psi_commute C.ne k L.τ₁).symm
  · have hcomm : ∀ {e : G} (heB : e ∈ L.B) (he1 : e ≠ 1) (hez : e ≠ z)
        {x : (compModel C.D C.i₁).K} (hex : ∀ he, oddQuotMk z ⟨e, he⟩ = C.psi C.i₁ x),
        Subgroup.centralizer ({x} : Set (compModel C.D C.i₁).K) ≤
          (modOdd z (⨆ F ∈ signalizerFunctorEk 2 2 L.B,
            (Subgroup.centralizer (F : Set G) ⊓ exactLayer (𝒞 K) z))).comap (C.psi C.i₁) := by
      intro e heB he1 hez x hex y hy
      refine mem_modOdd_of_commutes_gen hΩ.conjInvariant L.B_elem L.z_mem_B C.X.hKz.ne_one heB he1
        hez (C.X.psi_mem_memberJoin C.i₁ y) (fun he => ?_)
      rw [hex he, ← map_mul, ← map_mul, (Subgroup.mem_centralizer_singleton_iff.mp hy).symm]
    obtain ⟨-, -, -, hgen⟩ := T3CII.T3U.g2d4_model_facts C.hS.odd C.hS.five C.tag₁
      (C.D.isFundTag C.i₁) (C.D.admissible C.i₁) (C.D.exp_eq C.i₁)
    have htop := hgen L.τ₁ L.τ₂ L.sq₁ L.sq₂ L.ne₁ L.ne₂ L.ne₁₂ L.comm
    have hk : k ∈ Subgroup.centralizer ({L.τ₁} : Set (compModel C.D C.i₁).K) ⊔
        Subgroup.centralizer ({L.τ₂} : Set (compModel C.D C.i₁).K) ⊔
        Subgroup.centralizer ({L.τ₁ * L.τ₂} : Set (compModel C.D C.i₁).K) := by
      rw [htop]
      exact Subgroup.mem_top k
    exact (sup_le (sup_le (hcomm L.t_mem_B L.uJ.ne_one L.t_ne_z (fun _ => L.htbar))
      (hcomm L.z'_mem_B L.uK'.ne_one L.z'_ne_z (fun _ => L.hz'bar)))
      (hcomm (mul_mem L.t_mem_B L.z'_mem_B) L.uK''.ne_one L.tz'_ne_z (fun _ => L.htz'bar))) hk

theorem generation_t : CentralizerGenerationStar (𝒞 K) L.B L.t := by
  have hΩ := C.X.hΩ
  have hz1 : z ≠ 1 := C.X.hKz.ne_one
  obtain ⟨Ra, hRa, hRaJ, hUa⟩ := C.exists_fund_of_bar L.hJ L.hJt L.htbar L.ne₁
  obtain ⟨s, hsz, hst⟩ := C.exists_swap L.hJ L.hJt L.t_ne_z hRa hUa L.htbar
  have hts : L.t = s⁻¹ * z * s := by
    calc L.t = s⁻¹ * (s * L.t * s⁻¹) * s := by group
      _ = s⁻¹ * z * s := by rw [hst]
  have hzs : z = s⁻¹ * L.t * s := by
    calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
      _ = s⁻¹ * L.t * s := by rw [hsz]
  set B' := conjSub s⁻¹ L.B with hB'
  have hB'e : IsElemAbelian 2 B' := isElemAbelian_conjSub L.B_elem s⁻¹
  have hmem : ∀ {x : G}, x ∈ L.B → s⁻¹ * x * s ∈ B' := fun {x} hx => by
    rw [hB', mem_conjSub_iff]
    convert hx using 1
    group
  have hzB' : z ∈ B' := hzs ▸ hmem L.t_mem_B
  have htB' : L.t ∈ B' := hts ▸ hmem L.z_mem_B
  have hb'B' := hmem L.z'_mem_B
  have hb'tB' : s⁻¹ * L.z' * s * L.t ∈ B' := mul_mem hb'B' htB'
  have hb'C := Lemma52Proof.le_centralizer_of_mem hB'e hzB' hb'B'
  have hbz : ∀ c : G, s⁻¹ * L.z' * s * L.t = c → L.z' * z = s * c * s⁻¹ := fun c h => by
    rw [← h, hts]
    group
  have hb'1 : s⁻¹ * L.z' * s ≠ 1 := fun h => L.uK'.ne_one (by
    calc L.z' = s * (s⁻¹ * L.z' * s) * s⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have hb'z : s⁻¹ * L.z' * s ≠ z := fun h => L.t_ne_z'.symm (by
    calc L.z' = s * (s⁻¹ * L.z' * s) * s⁻¹ := by group
      _ = s * z * s⁻¹ := by rw [h]
      _ = L.t := hsz)
  have hb't1 : s⁻¹ * L.z' * s * L.t ≠ 1 := fun h => L.z'_ne_z (by
    have h1 : L.z' * z = 1 := by rw [hbz 1 h]; group
    calc L.z' = L.z' * z * z := by rw [mul_assoc, C.X.hz2, mul_one]
      _ = z := by rw [h1, one_mul])
  have hb'tz : s⁻¹ * L.z' * s * L.t ≠ z := fun h => L.frameData₁.z'_ne_zt C.hS.odd C.hS.five
    hΩ (by
      have h1 : L.z' * z = L.t := by rw [hbz z h, hsz]
      calc L.z' = L.z' * z * z := by rw [mul_assoc, C.X.hz2, mul_one]
        _ = L.t * z := by rw [h1]
        _ = z * L.t := (L.frameData₁.comm_zt C.hS.odd hΩ).symm)
  have hgen : CentralizerGenerationStar (𝒞 K) B' z := by
    refine centralizerGenerationStar_of_components C.X.hs C.D (fun j k => ?_)
    have hJk := C.X.psi_mem_memberJoin j k
    rcases C.eq_or_eq j with rfl | rfl
    · refine mem_modOdd_of_commutes_gen hΩ.conjInvariant hB'e hzB' hz1 htB' L.uJ.ne_one
        L.t_ne_z hJk (fun he => ?_)
      rw [show oddQuotMk z ⟨L.t, he⟩ = C.psi C.i₁ L.τ₁ from L.htbar]
      exact (C.X.psi_commute C.ne k L.τ₁).symm
    · rcases L.swap_dichotomy L.z'_mem_B L.hJ L.hJt hRa hRaJ hUa hst hb'C with hc | hc
      · exact mem_modOdd_of_commutes_gen hΩ.conjInvariant hB'e hzB' hz1 hb'B' hb'1 hb'z hJk
          (fun he => hc _ ⟨k, rfl⟩)
      · refine mem_modOdd_of_commutes_gen hΩ.conjInvariant hB'e hzB' hz1 hb'tB' hb't1 hb'tz hJk
          (fun he => ?_)
        have hve : oddQuotMk z ⟨s⁻¹ * L.z' * s * L.t, he⟩ =
            oddQuotMk z ⟨s⁻¹ * L.z' * s, hb'C⟩ * C.psi C.i₁ L.τ₁ := by
          rw [← L.htbar, ← map_mul]
          rfl
        rw [hve]
        exact hc _ ⟨k, rfl⟩
  have h := centralizerGenerationStar_conj hΩ.conjInvariant s hgen
  rwa [hB', conjSub_conjSub_inv, hsz] at h

theorem link_z_star : InvolutionLinkStar p f (𝒞 K) L.B {K, L.J} z := by
  have hΩ := C.X.hΩ
  obtain ⟨Ra, hRa, -, hUa⟩ := C.exists_fund_of_bar L.hJ L.hJt L.htbar L.ne₁
  have htY : L.t ∈ exactLayer (𝒞 K) z :=
    exactCore_le_exactLayer L.hJ (C.X.involution_mem_exactCore L.hJ L.hJt)
  intro N hN w hw hdisj
  have key : ActsTrivOnQuot N z ∨ w = z := by
    rcases hdisj with h | ⟨L', hL', hL'z, hL'w⟩
    · exact Or.inl h
    · rcases actsTriv_or_eq C.hS.odd C.hS.five hΩ hN hL' hw hL'z hL'w with h | h
      · exact Or.inr h
      · exact Or.inl h
  rcases key with htq | hwz
  · have hNtq : N ∈ tqMembers (𝒞 K) z := ⟨hN, mem_trivialOnQuot_iff_actsTrivOnQuot.mpr htq⟩
    obtain ⟨h, hh, hcase⟩ := C.link_z htY L.uJ.sq hRa hUa L.htbar hNtq hw
    rcases hcase with hc | hc
    · exact ⟨K, Set.mem_insert _ _, z, L.z_mem_B, C.X.K_cl, h, hh, hc⟩
    · exact ⟨L.J, Set.mem_insert_of_mem _ rfl, L.t, L.t_mem_B, L.hJt, h, hh, hc⟩
  · exact ⟨K, Set.mem_insert _ _, z, L.z_mem_B, C.X.K_cl, 1, one_mem _, by rw [hwz]; group⟩

theorem link_t_star : InvolutionLinkStar p f (𝒞 K) L.B {K, L.J} L.t := by
  have hΩ := C.X.hΩ
  obtain ⟨Ra, hRa, -, hUa⟩ := C.exists_fund_of_bar L.hJ L.hJt L.htbar L.ne₁
  obtain ⟨s, hsz, hst⟩ := C.exists_swap L.hJ L.hJt L.t_ne_z hRa hUa L.htbar
  have htY : L.t ∈ exactLayer (𝒞 K) z :=
    exactCore_le_exactLayer L.hJ (C.X.involution_mem_exactCore L.hJ L.hJt)
  have hYt : exactLayer (𝒞 K) L.t = conjSub s (exactLayer (𝒞 K) z) := by
    rw [← hsz]
    exact exactLayer_conj hΩ.conjInvariant s z
  have hstz : s⁻¹ * L.t * s = z := by rw [← hsz]; group
  intro N hN w hw hdisj
  have key : ActsTrivOnQuot N L.t ∨ w = L.t := by
    rcases hdisj with h | ⟨L', hL', hL'z, hL'w⟩
    · exact Or.inl h
    · rcases actsTriv_or_eq C.hS.odd C.hS.five hΩ hN hL' hw hL'z hL'w with h | h
      · exact Or.inr h
      · exact Or.inl h
  rcases key with htq | hwt
  · have hN'tq : conjSub s⁻¹ N ∈ tqMembers (𝒞 K) z := by
      refine ⟨hΩ.conjInvariant s⁻¹ N hN, ?_⟩
      have h := trivialOnQuot_conjSub (mem_trivialOnQuot_iff_actsTrivOnQuot.mpr htq) s⁻¹
      rwa [show s⁻¹ * L.t * s⁻¹⁻¹ = z by rw [inv_inv]; exact hstz] at h
    obtain ⟨h, hh, hcase⟩ := C.link_z htY L.uJ.sq hRa hUa L.htbar hN'tq (hw.conj s⁻¹)
    have hh' : s * h * s⁻¹ ∈ exactLayer (𝒞 K) L.t := by
      rw [hYt, mem_conjSub_iff]
      convert hh using 1
      group
    have hwe : w = s * (s⁻¹ * w * s⁻¹⁻¹) * s⁻¹ := by group
    rcases hcase with hc | hc
    · refine ⟨L.J, Set.mem_insert_of_mem _ rfl, L.t, L.t_mem_B, L.hJt, s * h * s⁻¹, hh', ?_⟩
      rw [hwe, hc]
      calc s * (h * z * h⁻¹) * s⁻¹ = (s * h * s⁻¹) * (s * z * s⁻¹) * (s * h * s⁻¹)⁻¹ := by group
        _ = (s * h * s⁻¹) * L.t * (s * h * s⁻¹)⁻¹ := by rw [hsz]
    · refine ⟨K, Set.mem_insert _ _, z, L.z_mem_B, C.X.K_cl, s * h * s⁻¹, hh', ?_⟩
      rw [hwe, hc]
      calc s * (h * L.t * h⁻¹) * s⁻¹ =
          (s * h * s⁻¹) * (s * L.t * s⁻¹) * (s * h * s⁻¹)⁻¹ := by group
        _ = (s * h * s⁻¹) * z * (s * h * s⁻¹)⁻¹ := by rw [hst]
  · exact ⟨L.J, Set.mem_insert_of_mem _ rfl, L.t, L.t_mem_B, L.hJt, 1, one_mem _,
      by rw [hwt]; group⟩

theorem cover_z {M : Subgroup G} (hM : M ∈ centMembers (𝒞 K) z) :
    ∃ g : G, z ∈ conjSub g L.B ∧ InCommonComponent z M (exactCore z (conjSub g K)) := by
  have hΩ := C.X.hΩ
  have hMtq : M ∈ tqMembers (𝒞 K) z := centMembers_subset_tqMembers hM
  have hMeq : exactCore z M = M := exactCore_eq_self_of_mem_centMembers hΩ.classical hM
  obtain ⟨j, R, -, hmod⟩ := C.X.exists_fund_of_mem hMtq
  rw [hMeq] at hmod
  rcases C.eq_or_eq j with rfl | rfl
  · refine ⟨1, ?_, (C.psi C.i₀).range, C.X.isComponent_range C.i₀, ?_, ?_⟩
    · rw [conjSub_one]
      exact L.z_mem_B
    · rw [← hmod]
      exact Subgroup.map_le_range _ _
    · rw [conjSub_one, C.K₀]
      exact le_rfl
  · obtain ⟨Ra, hRa, -, hUa⟩ := C.exists_fund_of_bar L.hJ L.hJt L.htbar L.ne₁
    obtain ⟨s, hsz, hst⟩ := C.exists_swap L.hJ L.hJt L.t_ne_z hRa hUa L.htbar
    have hKJ : conjSub s K = L.J := by
      have h1 : IsUniqueInvolution (conjSub s K) L.t := by
        have h2 := C.X.hKz.conj s
        rwa [hsz] at h2
      exact C.noTwins L.J L.hJ.1 _ ⟨hΩ.conjInvariant s K C.X.hK, L.t, L.uJ, h1⟩
    refine ⟨s, ?_, (C.psi C.i₁).range, C.X.isComponent_range C.i₁, ?_, ?_⟩
    · rw [mem_conjSub_iff, show s⁻¹ * z * s = L.t by
        calc s⁻¹ * z * s = s⁻¹ * (s * L.t * s⁻¹) * s := by rw [hst]
          _ = L.t := by group]
      exact L.t_mem_B
    · rw [← hmod]
      exact Subgroup.map_le_range _ _
    · rw [hKJ]
      exact L.J_le_Q

theorem frameSide : FrameSideTwoStar p f (𝒞 K) L.B {K, L.J} where
  elem := L.B_elem
  card := L.B_card.ge
  subset := by
    rintro M (rfl | rfl)
    · exact CoreAssembly.mem_conjClass_self _
    · exact L.hJ.1
  nonempty := ⟨K, Set.mem_insert _ _⟩
  involution := by
    rintro M (rfl | rfl)
    · exact ⟨z, L.z_mem_B, C.X.K_cl⟩
    · exact ⟨L.t, L.t_mem_B, L.hJt⟩
  generation := by
    rintro a - ⟨M, (rfl | rfl), hMa⟩
    · rw [(ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hS.odd C.hS.five hMa).eq
        C.X.hKz]
      exact L.generation_z
    · rw [(ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hS.odd C.hS.five hMa).eq L.uJ]
      exact L.generation_t
  link := by
    rintro a - ⟨M, (rfl | rfl), hMa⟩
    · rw [(ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hS.odd C.hS.five hMa).eq
        C.X.hKz]
      exact L.link_z_star
    · rw [(ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hS.odd C.hS.five hMa).eq L.uJ]
      exact L.link_t_star

end ExoticLift

end CFSG.ClassicalInvolution.NDB
