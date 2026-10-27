module

public import CFSG.ClassicalInvolution.SmallCases.NDBE3Z
public import CFSG.ClassicalInvolution.SmallCases.NDBE4Fix
import CFSG.ClassicalInvolution.Asc77.WP3FrameVertex
import CFSG.ClassicalInvolution.Asc77.WP3L52Main
import CFSG.ClassicalInvolution.Asc77.AscT8Basic
import CFSG.ClassicalInvolution.Asc77.WP3LayerHyp
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.SmallCases.NDB5Sec
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
public import CFSG.ClassicalInvolution.AschTight.S1911P3a
public import CFSG.ClassicalInvolution.AschTight.S1911P3b
public import CFSG.ClassicalInvolution.AschTight.S1911P3d
public import CFSG.ClassicalInvolution.AschTight.S1911SecG
public import CFSG.ClassicalInvolution.AschTight.S1916FusStmt
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Edge
public import CFSG.ClassicalInvolution.RouteD.MultiModelFactsFinal
import CFSG.ClassicalInvolution.Asc77.AscT8Setup
import CFSG.ClassicalInvolution.Asc77.AscThmABasic
import CFSG.ClassicalInvolution.Asc77.WP2Thm7c
import CFSG.ClassicalInvolution.SmallCases.NDB5Layer
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

namespace ExoticCtx

variable (C : ExoticCtx p f K z)

include C in
theorem noTwins : ∀ M ∈ 𝒞 K, ∀ M' ∈ twinSet (𝒞 K) M, M' = M := by
  intro M hM
  refine T8.noTwins_of_mem C.X.hΩ.conjInvariant (fun M hM => hM) (fun K' hK' => ?_) hM
  obtain ⟨hK'Ω, w, hKw, hK'w⟩ := hK'
  have hwz : w = z := hKw.eq C.X.hKz
  subst hwz
  by_contra hne
  exact C.hnoT ⟨K', hK'Ω, hne, isClassicalMember_of_twin C.X.hΩ hK'Ω hK'w⟩

theorem exists_fund_of_bar {N : Subgroup G} (hN : N ∈ tqMembers (𝒞 K) z) {w : G}
    (hw : IsClassicalMember p f N w) {x : (compModel C.D C.i₁).K}
    (hx : oddQuotMk z ⟨w, C.X.involution_mem_centralizer hN hw⟩ = C.psi C.i₁ x) (hx1 : x ≠ 1) :
    ∃ R ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D,
      R.map (C.psi C.i₁) = modOdd z (exactCore z N) ∧ IsUniqueInvolution R x := by
  have hU := C.X.isUniqueInvolution_modOdd hN hw
  obtain ⟨j, R, hR, hRN⟩ := C.X.exists_fund_of_mem hN
  rcases C.eq_or_eq j with rfl | rfl
  · exfalso
    have hwN := hU.mem
    rw [← hRN] at hwN
    obtain ⟨r, -, hr⟩ := hwN
    apply hx1
    apply C.eq_one_of_comm
    intro y
    rw [← hx, ← hr]
    exact C.X.psi_commute C.ne r y
  · refine ⟨R, hR, hRN, ?_, ?_, ?_, ?_⟩
    · have hwm := hU.mem
      rw [← hRN, hx] at hwm
      obtain ⟨r, hr, hrx⟩ := hwm
      rwa [← C.psi_injective hrx]
    · exact hx1
    · apply C.psi_injective
      rw [map_mul, map_one, ← hx]
      exact hU.sq
    · intro y hy hy2
      have hym : C.psi C.i₁ y ∈ modOdd z (exactCore z N) := by
        rw [← hRN]
        exact ⟨y, hy, rfl⟩
      rcases hU.unique _ hym (by rw [← map_mul, hy2, map_one]) with h | h
      · exact Or.inl (C.psi_injective (h.trans (map_one _).symm))
      · exact Or.inr (C.psi_injective (h.trans hx))

theorem link_z {a : G} (haY : a ∈ exactLayer (𝒞 K) z) (ha2 : a * a = 1)
    {Ra : Subgroup (compModel C.D C.i₁).K}
    (hRa : Ra ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D)
    {xa : (compModel C.D C.i₁).K} (hxa : IsUniqueInvolution Ra xa)
    (habar : oddQuotMk z ⟨a, exactLayer_le_centralizer (𝒞 K) z haY⟩ = C.psi C.i₁ xa)
    {N : Subgroup G} (hN : N ∈ tqMembers (𝒞 K) z) {w : G} (hw : IsClassicalMember p f N w) :
    ∃ h ∈ exactLayer (𝒞 K) z, w = h * z * h⁻¹ ∨ w = h * a * h⁻¹ := by
  have hwY : w ∈ exactLayer (𝒞 K) z :=
    exactCore_le_exactLayer hN (C.X.involution_mem_exactCore hN hw)
  have hw2 : w * w = 1 := (isCentralInvolution_of_isClassicalMember hw).sq
  have hU := C.X.isUniqueInvolution_modOdd hN hw
  obtain ⟨j, R, hR, hRN⟩ := C.X.exists_fund_of_mem hN
  rcases C.eq_or_eq j with rfl | rfl
  · have hR1 := C.X.fund_eq_top C.i₀ ⟨C.tag₀, C.rank₀⟩ hR
    rw [hR1, Subgroup.map_top, ← C.K₀] at hRN
    have hUK : IsUniqueInvolution (modOdd z (exactCore z K))
        (oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩) := C.X.isUniqueInvolution_modOdd C.X.K_tq C.X.K_cl
    rw [hRN] at hUK
    have heq := hU.eq hUK
    obtain ⟨o, ho, hwo⟩ := C.X.exists_conj_of_oddQuotMk_eq hwY C.X.z_mem_exactLayer hw2
      C.X.hz2 heq
    exact ⟨o, oddCoreIn_le _ ho, Or.inl hwo⟩
  · have hwm := hU.mem
    rw [← hRN] at hwm
    obtain ⟨x, hxR, hx⟩ := hwm
    obtain ⟨R', hR', -, hUR⟩ := C.exists_fund_of_bar hN hw hx.symm (fun h1 => hU.ne_one (by
      rw [← hx, h1]
      exact map_one _))
    obtain ⟨g, hg⟩ := Bootstrap.twoClassInvolutionsConj p (C.D.tag C.i₁) (C.D.rank C.i₁)
      (C.D.exp C.i₁) C.hS.odd C.tag₁ (C.D.admissible C.i₁) Ra hRa R' hR' xa hxa.mem x hUR.mem
      hxa.sq hUR.sq hxa.ne_one hUR.ne_one (Exotic.comm_of_isUniqueInvolution hxa)
      (Exotic.comm_of_isUniqueInvolution hUR)
    obtain ⟨y, hy, hyg⟩ : ∃ (y : G) (hy : y ∈ exactLayer (𝒞 K) z),
        oddQuotMk z ⟨y, exactLayer_le_centralizer (𝒞 K) z hy⟩ = C.psi C.i₁ g :=
      C.X.exists_lift_psi C.i₁ g
    have hyaY : y * a * y⁻¹ ∈ exactLayer (𝒞 K) z := mul_mem (mul_mem hy haY) (inv_mem hy)
    have hya2 : y * a * y⁻¹ * (y * a * y⁻¹) = 1 := by
      rw [show y * a * y⁻¹ * (y * a * y⁻¹) = y * (a * a) * y⁻¹ by group, ha2]
      group
    have hbar : oddQuotMk z ⟨w, exactLayer_le_centralizer (𝒞 K) z hwY⟩ =
        oddQuotMk z ⟨y * a * y⁻¹, exactLayer_le_centralizer (𝒞 K) z hyaY⟩ := by
      rw [Exotic.oddQuotMk_conj' (exactLayer_le_centralizer (𝒞 K) z hy)
        (exactLayer_le_centralizer (𝒞 K) z haY), hyg, habar, ← map_inv, ← map_mul, ← map_mul,
        hg]
      exact hx.symm
    obtain ⟨o, ho, hwo⟩ := C.X.exists_conj_of_oddQuotMk_eq hwY hyaY hw2 hya2 hbar
    refine ⟨o * y, mul_mem (oddCoreIn_le _ ho) hy, Or.inr ?_⟩
    rw [hwo]
    group

theorem exists_swap {M : Subgroup G} (hM : M ∈ tqMembers (𝒞 K) z) {a : G}
    (hMa : IsClassicalMember p f M a) (haz : a ≠ z) {Ra : Subgroup (compModel C.D C.i₁).K}
    (hRa : Ra ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D)
    {xa : (compModel C.D C.i₁).K} (hxa : IsUniqueInvolution Ra xa)
    (habar : oddQuotMk z ⟨a, C.X.involution_mem_centralizer hM hMa⟩ = C.psi C.i₁ xa) :
    ∃ s : G, s * z * s⁻¹ = a ∧ s * a * s⁻¹ = z := by
  have hp2 := C.hS.odd
  have hq := C.hS.five
  have hΩ := C.X.hΩ
  have haY : a ∈ exactLayer (𝒞 K) z :=
    exactCore_le_exactLayer hM (C.X.involution_mem_exactCore hM hMa)
  have ha2 : a * a = 1 := (isCentralInvolution_of_isClassicalMember hMa).sq
  obtain ⟨g₀, hg₀⟩ := hM.1
  have hg₀' : conjSub g₀ K = M := hg₀
  have hUa := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hMa
  have hgz : g₀ * z * g₀⁻¹ = a := by
    have h1 : IsUniqueInvolution (conjSub g₀ K) (g₀ * z * g₀⁻¹) := C.X.hKz.conj g₀
    rw [hg₀'] at h1
    exact h1.eq hUa
  have hMK : M ≠ K := fun h => haz (hUa.eq (h ▸ C.X.hKz))
  have haK : a ∈ trivialOnQuot K := Cover.mem_trivialOnQuot_K C.X hM hMa hMK
  have hK'tq : conjSub g₀⁻¹ K ∈ tqMembers (𝒞 K) z := by
    refine ⟨hΩ.conjInvariant g₀⁻¹ K C.X.hK, ?_⟩
    have h := trivialOnQuot_conjSub haK g₀⁻¹
    have e : g₀⁻¹ * a * g₀⁻¹⁻¹ = z := by rw [← hgz]; group
    rwa [e] at h
  obtain ⟨h, hh, hcase⟩ := C.link_z haY ha2 hRa hxa habar hK'tq (C.X.K_cl.conj g₀⁻¹)
  have hhz : h * z * h⁻¹ = z :=
    conj_eq_of_mem_centralizer_singleton (exactLayer_le_centralizer (𝒞 K) z hh)
  rcases hcase with hc | hc
  · exfalso
    have h2 : g₀⁻¹ * z * g₀⁻¹⁻¹ = z := hc.trans hhz
    apply haz
    rw [← hgz]
    calc g₀ * z * g₀⁻¹ = g₀ * (g₀⁻¹ * z * g₀⁻¹⁻¹) * g₀⁻¹ := by rw [h2]
      _ = z := by group
  · refine ⟨g₀ * h, ?_, ?_⟩
    · calc g₀ * h * z * (g₀ * h)⁻¹ = g₀ * (h * z * h⁻¹) * g₀⁻¹ := by group
        _ = a := by rw [hhz, hgz]
    · calc g₀ * h * a * (g₀ * h)⁻¹ = g₀ * (h * a * h⁻¹) * g₀⁻¹ := by group
        _ = g₀ * (g₀⁻¹ * z * g₀⁻¹⁻¹) * g₀⁻¹ := by rw [hc]
        _ = z := by group

end ExoticCtx

namespace ExoticLift

variable {C : ExoticCtx p f K z} (L : ExoticLift C)

theorem hyp51At_of_witness {a b : G} (haB : a ∈ L.B) (hbB : b ∈ L.B) (ha1 : a ≠ 1)
    (haz : a ≠ z) (hb1 : b ≠ 1) (hbz : b ≠ z) (hba : b ≠ a) (hbaz : b ≠ a * z)
    {M : Subgroup G} (hM : M ∈ tqMembers (𝒞 K) z) (hMa : IsClassicalMember p f M a)
    {xa : (compModel C.D C.i₁).K}
    (habar : oddQuotMk z ⟨a, C.X.involution_mem_centralizer hM hMa⟩ = C.psi C.i₁ xa)
    (hxa1 : xa ≠ 1) : Hyp51At L.B a := by
  have hp2 := C.hS.odd
  have hq := C.hS.five
  have hΩ := C.X.hΩ
  have hz1 : z ≠ 1 := C.X.hKz.ne_one
  obtain ⟨Ra, hRa, hRaM, hUa⟩ := C.exists_fund_of_bar hM hMa habar hxa1
  obtain ⟨s, hsz, hsa⟩ := C.exists_swap hM hMa haz hRa hUa habar
  have has : a = s⁻¹ * z * s := by
    calc a = s⁻¹ * (s * a * s⁻¹) * s := by group
      _ = s⁻¹ * z * s := by rw [hsa]
  have hzs : z = s⁻¹ * a * s := by
    calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
      _ = s⁻¹ * a * s := by rw [hsz]
  rw [← hyp51At_conj s⁻¹ a L.B, show s⁻¹ * a * s⁻¹⁻¹ = z by rw [inv_inv, ← hzs]]
  set B' := conjSub s⁻¹ L.B with hB'
  have hB'e : IsElemAbelian 2 B' := isElemAbelian_conjSub L.B_elem s⁻¹
  have hmem : ∀ {x : G}, x ∈ L.B → s⁻¹ * x * s ∈ B' := fun {x} hx => by
    rw [hB', mem_conjSub_iff]
    convert hx using 1
    group
  have hzB' : z ∈ B' := hzs ▸ hmem haB
  have haB' : a ∈ B' := has ▸ hmem L.z_mem_B
  have hb'B' := hmem hbB
  have hb'aB' : s⁻¹ * b * s * a ∈ B' := mul_mem hb'B' haB'
  have hb'C := Lemma52Proof.le_centralizer_of_mem hB'e hzB' hb'B'
  have hb'aC := Lemma52Proof.le_centralizer_of_mem hB'e hzB' hb'aB'
  have hmovQ : ∀ M' : Subgroup (OddQuot z), CFSG.IsComponent M' → MovedByAll B' z M' →
      M' = (C.psi C.i₁).range := fun M' hM' hm =>
    S.moved_eq_range hp2 hq C.X.hs C.D hB'e hzB' hz1 haB' ha1 haz
      (fun _ => ⟨xa, habar.symm⟩) hM' hm
  refine ⟨fun M₁ M₂ h₁ h₂ m₁ m₂ => (hmovQ M₁ h₁ m₁).trans (hmovQ M₂ h₂ m₂).symm,
    fun M' hM' hm => ?_⟩
  exfalso
  rw [hmovQ M' hM' hm] at hm
  have hnorm := FrameVertex.modOdd_le_normalizer hp2 hq hΩ.conjInvariant hΩ.classical
    C.hS.below C.X.hc2 (CoreAssembly.singleton_not_subset_center C.hS.nonabelian hz1) hB'e hzB'
    hz1 haB' ha1 haz hM hMa (C.X.isComponent_range C.i₁) hm
  set v := oddQuotMk z ⟨s⁻¹ * b * s, hb'C⟩ with hv
  have hvN : v ∈ Subgroup.normalizer ((C.psi C.i₁).range : Set (OddQuot z)) :=
    hnorm (oddQuotMk_mem_modOdd hb'B' hb'C)
  have hv2 : v * v = 1 := by
    rw [hv, ← map_mul]
    have e : (⟨s⁻¹ * b * s, hb'C⟩ * ⟨s⁻¹ * b * s, hb'C⟩ :
        ↥(Subgroup.centralizer ({z} : Set G))) = 1 :=
      Subtype.ext (Lemma52Proof.mul_self_eq_one_of_mem hB'e hb'B')
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
  have hvR : ∀ r ∈ Ra, v * C.psi C.i₁ r = C.psi C.i₁ r * v := fun r hr =>
    hcen _ (hRaM ▸ ⟨r, hr, rfl⟩)
  have hb'1 : s⁻¹ * b * s ≠ 1 := fun h => hb1 (by
    calc b = s * (s⁻¹ * b * s) * s⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have hb'z : s⁻¹ * b * s ≠ z := fun h => hba (by
    calc b = s * (s⁻¹ * b * s) * s⁻¹ := by group
      _ = s * z * s⁻¹ := by rw [h]
      _ = a := hsz)
  have hbz' : ∀ c : G, s⁻¹ * b * s * a = c → b * z = s * c * s⁻¹ := fun c h => by
    rw [← h, has]
    group
  have hb'a1 : s⁻¹ * b * s * a ≠ 1 := fun h => hbz (by
    have h1 : b * z = 1 := by rw [hbz' 1 h]; group
    calc b = b * z * z := by rw [mul_assoc, C.X.hz2, mul_one]
      _ = z := by rw [h1, one_mul])
  have hb'az : s⁻¹ * b * s * a ≠ z := fun h => hbaz (by
    have h1 : b * z = a := by rw [hbz' z h, hsz]
    calc b = b * z * z := by rw [mul_assoc, C.X.hz2, mul_one]
      _ = a * z := by rw [h1])
  rcases ExoticModel.involution_fund hp2 C.tag₁ (C.D.admissible C.i₁) (C.psi C.i₁)
    C.psi_injective hRa hUa hvN hv2 hvR with hc | hc
  · obtain ⟨y, hy, hne⟩ := hm v (oddQuotMk_mem_modOdd hb'B' hb'C)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB'e hzB' hz1 hb'B' hb'1 hb'z hb'C)
    exact hne (hc y hy)
  · have hva : v * C.psi C.i₁ xa = oddQuotMk z ⟨s⁻¹ * b * s * a, hb'aC⟩ := by
      rw [hv, ← habar, ← map_mul]
      rfl
    obtain ⟨y, hy, hne⟩ := hm _ (oddQuotMk_mem_modOdd hb'aB' hb'aC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB'e hzB' hz1 hb'aB' hb'a1 hb'az hb'aC)
    rw [← hva] at hne
    exact hne (hc y hy)

theorem hyp51At_t : Hyp51At L.B L.t :=
  L.hyp51At_of_witness L.t_mem_B L.z'_mem_B L.uJ.ne_one L.t_ne_z L.uK'.ne_one L.z'_ne_z
    L.t_ne_z'.symm (fun h => L.frameData₁.z'_ne_zt C.hS.odd C.hS.five C.X.hΩ
      (h.trans (L.frameData₁.comm_zt C.hS.odd C.X.hΩ).symm)) L.hJ L.hJt L.htbar L.ne₁

theorem hyp51At_z' : Hyp51At L.B L.z' :=
  L.hyp51At_of_witness L.z'_mem_B L.t_mem_B L.uK'.ne_one L.z'_ne_z L.uJ.ne_one L.t_ne_z
    L.t_ne_z' (fun h => L.frameData₂.z'_ne_zt C.hS.odd C.hS.five C.X.hΩ
      (h.trans (L.frameData₁.comm_zz' C.hS.odd C.X.hΩ).symm)) L.hK' L.hK'z' L.hz'bar L.ne₂

theorem hyp51At_tz' : Hyp51At L.B (L.t * L.z') :=
  L.hyp51At_of_witness (mul_mem L.t_mem_B L.z'_mem_B) L.t_mem_B L.uK''.ne_one L.tz'_ne_z
    L.uJ.ne_one L.t_ne_z (fun h => L.uK'.ne_one (mul_left_cancel (h.symm.trans (mul_one _).symm)))
    (fun h => L.z'_ne_z (by
      have h1 : L.z' * z = 1 := by
        have h2 : L.t * (L.z' * z) = L.t * 1 := by rw [mul_one, ← mul_assoc]; exact h.symm
        exact mul_left_cancel h2
      calc L.z' = L.z' * z * z := by rw [mul_assoc, C.X.hz2, mul_one]
        _ = z := by rw [h1, one_mul]))
    L.hK'' L.hK''tz' L.htz'bar L.ne₃

end ExoticLift

end CFSG.ClassicalInvolution.NDB
