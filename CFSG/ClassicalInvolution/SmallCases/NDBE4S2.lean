module

public import CFSG.ClassicalInvolution.SmallCases.NDBE4S
import CFSG.ClassicalInvolution.Asc77.WP3FrameVertex
import CFSG.ClassicalInvolution.Asc77.WP3L52Main
import CFSG.ClassicalInvolution.Asc77.AscT8Basic
import CFSG.ClassicalInvolution.Asc77.WP3LayerHyp
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
import CFSG.ClassicalInvolution.Asc77.AscT8Setup
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

namespace ExoticLiftS


variable {C : ExoticCtxS p f K z} (L : ExoticLiftS C)

theorem hyp51At_of_witness (hres : SpinOuterKleinAlpha p) {a b : G} (haB : a ∈ L.B)
    (hbB : b ∈ L.B) (hgenB : Subgroup.closure ({z, a, b} : Set G) = L.B) (ha1 : a ≠ 1)
    (haz : a ≠ z) (hb1 : b ≠ 1) (hbz : b ≠ z) (hba : b ≠ a) (hbaz : b ≠ a * z)
    {M : Subgroup G} (hM : M ∈ tqMembers (𝒞 K) z) (hMa : IsClassicalMember p f M a)
    {xa : (compModel C.D C.i₁).K}
    (habar : oddQuotMk z ⟨a, C.X.involution_mem_centralizer hM hMa⟩ = C.psi C.i₁ xa)
    (hxa1 : xa ∉ Subgroup.center (compModel C.D C.i₁).K) : Hyp51At L.B a := by
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
  have haC := Lemma52Proof.le_centralizer_of_mem hB'e hzB' haB'
  have hmovQ : ∀ M' : Subgroup (OddQuot z), CFSG.IsComponent M' → MovedByAll B' z M' →
      M' = (C.psi C.i₁).range := fun M' hM' hm =>
    S.moved_eq_range hp2 hq C.X.hs C.D hB'e hzB' hz1 haB' ha1 haz
      (fun _ => ⟨xa, habar.symm⟩) hM' hm
  refine ⟨fun M₁ M₂ h₁ h₂ m₁ m₂ => (hmovQ M₁ h₁ m₁).trans (hmovQ M₂ h₂ m₂).symm,
    fun M' hM' hm => ?_⟩
  have hMQ := hmovQ M' hM' hm
  rw [hMQ] at hm ⊢
  set v := oddQuotMk z ⟨s⁻¹ * b * s, hb'C⟩ with hv
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
  rcases L.swap_trichotomy hres hbB hM hMa hRa hRaM hUa hsa hb'C with hc | hc | ⟨hα, -⟩
  · exfalso
    obtain ⟨y, hy, hne⟩ := hm v (oddQuotMk_mem_modOdd hb'B' hb'C)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB'e hzB' hz1 hb'B' hb'1 hb'z hb'C)
    exact hne (hc y hy)
  · exfalso
    have hva : v * C.psi C.i₁ xa = oddQuotMk z ⟨s⁻¹ * b * s * a, hb'aC⟩ := by
      rw [hv, ← habar, ← map_mul]
      rfl
    obtain ⟨y, hy, hne⟩ := hm _ (oddQuotMk_mem_modOdd hb'aB' hb'aC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB'e hzB' hz1 hb'aB' hb'a1 hb'az hb'aC)
    rw [← hva] at hne
    exact hne (hc y hy)
  ·
    have hB'eq : B' = Subgroup.closure ({a, s⁻¹ * b * s, z} : Set G) := by
      rw [hB', ← hgenB, conjSub, MonoidHom.map_closure]
      congr 1
      simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv]
      rw [← has, ← hzs]
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hA : IsElemAbelian 2 (Subgroup.closure ({a, s⁻¹ * b * s, z} : Set G)) := by
      rw [← hB'eq]
      exact hB'e
    have hn₁ : oddQuotMk z ⟨a, haC⟩ ∈
        Subgroup.normalizer ((C.psi C.i₁).range : Set (OddQuot z)) := L.mem_normalizer_Q _
    rw [hB'eq, Exotic.inducedImage_closure_eq hA _ haC hb'C hn₁ (L.mem_normalizer_Q _)]
    have e₁ : toInducedAutOn (C.psi C.i₁).range ⟨oddQuotMk z ⟨a, haC⟩, hn₁⟩ =
        toInducedAutOn (C.psi C.i₁).range
          ⟨C.psi C.i₁ xa, ModelFacts.Orth15.mem_normalizer_range (C.psi C.i₁) xa⟩ :=
      congrArg _ (Subtype.ext habar)
    rw [e₁]
    exact hα

theorem hyp51At_t (hres : SpinOuterKleinAlpha p) : Hyp51At L.B L.t :=
  L.hyp51At_of_witness hres L.t_mem_B L.z'_mem_B rfl L.uJ.ne_one L.t_ne_z L.uK'.ne_one
    L.z'_ne_z L.t_ne_z'.symm (fun h => L.frameData₁.z'_ne_zt C.hS.odd C.hS.five C.X.hΩ
      (h.trans (L.frameData₁.comm_zt C.hS.odd C.X.hΩ).symm)) L.hJ L.hJt L.htbar L.nz₁

theorem hyp51At_z' (hres : SpinOuterKleinAlpha p) : Hyp51At L.B L.z' :=
  L.hyp51At_of_witness hres L.z'_mem_B L.t_mem_B
    (by
      rw [show ({z, L.z', L.t} : Set G) = {z, L.t, L.z'} by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto])
    L.uK'.ne_one L.z'_ne_z L.uJ.ne_one L.t_ne_z L.t_ne_z'
    (fun h => L.frameData₂.z'_ne_zt C.hS.odd C.hS.five C.X.hΩ
      (h.trans (L.frameData₁.comm_zz' C.hS.odd C.X.hΩ).symm)) L.hK' L.hK'z' L.hz'bar L.nz₂

theorem hyp51At_tz' (hres : SpinOuterKleinAlpha p) : Hyp51At L.B (L.t * L.z') := by
  have hgen : Subgroup.closure ({z, L.t * L.z', L.t} : Set G) = L.B := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl | rfl)
      · exact L.z_mem_B
      · exact mul_mem L.t_mem_B L.z'_mem_B
      · exact L.t_mem_B
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl | rfl)
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
      · have h1 : L.t * L.z' ∈ Subgroup.closure ({z, L.t * L.z', L.t} : Set G) :=
          Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        have h2 : L.t ∈ Subgroup.closure ({z, L.t * L.z', L.t} : Set G) :=
          Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
        have := mul_mem (inv_mem h2) h1
        rwa [inv_mul_cancel_left] at this
  exact L.hyp51At_of_witness hres (mul_mem L.t_mem_B L.z'_mem_B) L.t_mem_B hgen L.uK''.ne_one
    L.tz'_ne_z L.uJ.ne_one L.t_ne_z
    (fun h => L.uK'.ne_one (mul_left_cancel (h.symm.trans (mul_one _).symm)))
    (fun h => L.z'_ne_z (by
      have h1 : L.z' * z = 1 := by
        have h2 : L.t * (L.z' * z) = L.t * 1 := by rw [mul_one, ← mul_assoc]; exact h.symm
        exact mul_left_cancel h2
      calc L.z' = L.z' * z * z := by rw [mul_assoc, C.X.hz2, mul_one]
        _ = z := by rw [h1, one_mul]))
    L.hK'' L.hK''tz' L.htz'bar L.nz₃

end ExoticLiftS

end CFSG.ClassicalInvolution.NDB
