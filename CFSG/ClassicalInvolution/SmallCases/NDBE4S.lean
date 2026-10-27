module

public import CFSG.ClassicalInvolution.SmallCases.NDBE3S
public import CFSG.ClassicalInvolution.SmallCases.NDBE4SModel
public import CFSG.ClassicalInvolution.SmallCases.NDBE4C
import CFSG.ClassicalInvolution.Asc77.WP3FrameVertex
import CFSG.ClassicalInvolution.Asc77.WP3L52Main
import CFSG.ClassicalInvolution.Asc77.AscT8Basic
import CFSG.ClassicalInvolution.Asc77.WP3LayerHyp
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.SmallCases.NDB5Sec
import CFSG.ClassicalInvolution.SmallCases.NDB5Layer
import CFSG.ClassicalInvolution.Balance.Q27FuzzyBalance
import CFSG.ClassicalInvolution.SmallCases.NDBE5ZT
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
import CFSG.ClassicalInvolution.Asc77.AscT8Setup
import CFSG.ClassicalInvolution.Asc77.AscThmABasic
import CFSG.ClassicalInvolution.Asc77.WP2Thm7c
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

namespace ExoticCtxS


variable (C : ExoticCtxS p f K z)

include C in
theorem noTwins : ∀ M ∈ 𝒞 K, ∀ M' ∈ twinSet (𝒞 K) M, M' = M :=
  Exotic.noTwins C.X.hΩ C.X.hKz C.hnoT

theorem exists_fund_of_bar {N : Subgroup G} (hN : N ∈ tqMembers (𝒞 K) z) {w : G}
    (hw : IsClassicalMember p f N w) {x : (compModel C.D C.i₁).K}
    (hx : oddQuotMk z ⟨w, C.X.involution_mem_centralizer hN hw⟩ = C.psi C.i₁ x)
    (hx1 : x ∉ Subgroup.center (compModel C.D C.i₁).K) :
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
    apply C.mem_center_of_comm
    intro y
    rw [← hx, ← hr]
    exact C.X.psi_commute C.ne r y
  · refine ⟨R, hR, hRN, ?_, ?_, ?_, ?_⟩
    · have hwm := hU.mem
      rw [← hRN, hx] at hwm
      obtain ⟨r, hr, hrx⟩ := hwm
      rwa [← C.psi_injective hrx]
    · exact fun h => hx1 (h ▸ Subgroup.one_mem _)
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

theorem conj_of_fund {Ra R' : Subgroup (compModel C.D C.i₁).K}
    (hRa : Ra ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D)
    (hR' : R' ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D)
    {xa x : (compModel C.D C.i₁).K} (hxa : IsUniqueInvolution Ra xa)
    (hx : IsUniqueInvolution R' x) : ∃ g, g * xa * g⁻¹ = x := by
  have hsc := ModelFacts.fundamentalSingleClass (C.D.tag C.i₁) (C.D.rank C.i₁) p (C.D.exp C.i₁)
    Fact.out C.tag₁.isFundTag (C.D.admissible C.i₁)
    (by rcases C.tag₁ with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide)
    (by rcases C.tag₁ with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide)
  obtain ⟨g, hg⟩ : ∃ g : (compModel C.D C.i₁).K, R' = conjSub g Ra := hsc Ra hRa R' hR'
  refine ⟨g, ?_⟩
  have h1 : g * xa * g⁻¹ ∈ R' := by
    rw [hg]
    exact conj_mem_conjSub hxa.mem
  rcases hx.unique _ h1 (by
    rw [show g * xa * g⁻¹ * (g * xa * g⁻¹) = g * (xa * xa) * g⁻¹ by group, hxa.sq]
    group) with h | h
  · exfalso
    apply hxa.ne_one
    calc xa = g⁻¹ * (g * xa * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · exact h

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
      rw [← hx, ExoticModel.spin_fund_noncentral C.tag₁ (C.D.admissible C.i₁) R hR x hxR h1]
      exact map_one (C.psi C.i₁)))
    obtain ⟨g, hg⟩ := C.conj_of_fund hRa hR' hxa hUR
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
  have haK : a ∈ trivialOnQuot K := Cover.mem_trivialOnQuot_K C.X hM hMa (fun h =>
    haz (hUa.eq (h ▸ C.X.hKz)))
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

end ExoticCtxS

namespace ExoticLiftS


variable {C : ExoticCtxS p f K z} (L : ExoticLiftS C)

theorem tbar_ne_zbar : oddQuotMk z ⟨L.t, L.ht⟩ ≠ oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ := by
  intro h
  apply L.nz₁
  apply C.mem_center_of_comm
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

theorem swap_trichotomy (hres : SpinOuterKleinAlpha p) {a b : G} (hbB : b ∈ L.B)
    {M : Subgroup G} (hM : M ∈ tqMembers (𝒞 K) z) (hMa : IsClassicalMember p f M a)
    {Ra : Subgroup (compModel C.D C.i₁).K}
    (hRa : Ra ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D)
    (hRaM : Ra.map (C.psi C.i₁) = modOdd z (exactCore z M))
    {xa : (compModel C.D C.i₁).K} (hUa : IsUniqueInvolution Ra xa) {s : G}
    (hsa : s * a * s⁻¹ = z) (hb'C : s⁻¹ * b * s ∈ Subgroup.centralizer ({z} : Set G)) :
    (∀ y ∈ (C.psi C.i₁).range,
        oddQuotMk z ⟨s⁻¹ * b * s, hb'C⟩ * y = y * oddQuotMk z ⟨s⁻¹ * b * s, hb'C⟩) ∨
      (∀ y ∈ (C.psi C.i₁).range, (oddQuotMk z ⟨s⁻¹ * b * s, hb'C⟩ * C.psi C.i₁ xa) * y =
        y * (oddQuotMk z ⟨s⁻¹ * b * s, hb'C⟩ * C.psi C.i₁ xa)) ∨
      (alphaOf (Subgroup.closure ({toInducedAutOn (C.psi C.i₁).range ⟨C.psi C.i₁ xa,
            ModelFacts.Orth15.mem_normalizer_range (C.psi C.i₁) xa⟩,
          toInducedAutOn (C.psi C.i₁).range ⟨oddQuotMk z ⟨s⁻¹ * b * s, hb'C⟩,
            L.mem_normalizer_Q _⟩} : Set ↥(inducedAutOn (C.psi C.i₁).range))) = ⊥ ∧
        (Subgroup.centralizer ({oddQuotMk z ⟨s⁻¹ * b * s, hb'C⟩} : Set (OddQuot z))).comap
            (C.psi C.i₁) ⊔
          (Subgroup.centralizer ({oddQuotMk z ⟨s⁻¹ * b * s, hb'C⟩ * C.psi C.i₁ xa} :
            Set (OddQuot z))).comap (C.psi C.i₁) = ⊤) := by
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
  have hcen := C.centralizes_of_tq hM hMa hb'C hb'tq
  exact ExoticModel.spin_vertex hres hp2 C.five C.tag₁ (C.D.admissible C.i₁) (C.psi C.i₁)
    (C.X.psi_ker C.i₁) hRa hUa (L.mem_normalizer_Q _) hv2
    (fun r hr => hcen _ (hRaM ▸ ⟨r, hr, rfl⟩))

end ExoticLiftS

end CFSG.ClassicalInvolution.NDB
