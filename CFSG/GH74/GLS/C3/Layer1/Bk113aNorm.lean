module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.Back91Setup
public import CFSG.GH74.GLS.C3.Layer1.BackBasic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back
  CFSG.GH74.GLS.C3.Layer1.U1a
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K L M T Q : Subgroup G}

theorem pPrimeCoreOf_K_le_L (hh : Hyp9A x K L M T Q) : pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 L := by
  intro z hz
  obtain ⟨hzK, hz'⟩ := Setup91.mem_pPrimeCoreOf_iff.1 hz
  have h1 : (⟨z, hzK⟩ : ↥K) ∈ (Setup91.toLBar hh.K_le_L).ker := by
    rw [Setup91.ker_toLBar hh]
    exact hz'
  have h2 := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 h1)
  exact Setup91.mem_pPrimeCoreOf_iff.2 ⟨hh.K_le_L hzK, h2⟩

theorem CxK_le_CMK (hh : Hyp9A x K L M T Q) : CxK x K ≤ CMK M L := by
  intro c hc
  obtain ⟨hcC, hcS⟩ := hc
  have hcM : c ∈ M := hh.centralizer_le hcC
  refine mem_CMK_iff.2 ⟨hcM, mem_normalizer_of_norm hh.L_normal.2 hcM,
    mem_normalizer_pPrimeCoreOf hh.L_normal.2 hcM, fun l hl => ?_⟩
  obtain ⟨o, ho, k, hk, rfl⟩ := Setup91.exists_mul_of_mem_L hh hl
  have hkc : ⁅k, c⁆ ∈ pPrimeCoreOf 2 L := pPrimeCoreOf_K_le_L hh (hcS.2.2 k hk)
  have hoc : ⁅o, c⁆ ∈ pPrimeCoreOf 2 L := by
    have e : ⁅o, c⁆ = o * (c * o⁻¹ * c⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (pPrimeCoreOf 2 L).mul_mem ho
      (pPrimeCoreOf_norm hh.L_normal.2 hcM ((pPrimeCoreOf 2 L).inv_mem ho))
  have e : ⁅o * k, c⁆ = (o * ⁅k, c⁆ * o⁻¹) * ⁅o, c⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (pPrimeCoreOf 2 L).mul_mem
    ((pPrimeCoreOf 2 L).mul_mem ((pPrimeCoreOf 2 L).mul_mem ho hkc) ((pPrimeCoreOf 2 L).inv_mem ho))
    hoc

omit [Finite G] in
theorem map_conj_eq_self_of_mem' {C : Subgroup G} {c : G} (hc : c ∈ C) :
    C.map (MulAut.conj c).toMonoidHom = C := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    have : (MulAut.conj c).toMonoidHom w = c * w * c⁻¹ := by simp [MulAut.conj_apply]
    rw [this]
    exact C.mul_mem (C.mul_mem hc hw) (C.inv_mem hc)
  · intro hy
    refine ⟨c⁻¹ * y * c, C.mul_mem (C.mul_mem (C.inv_mem hc) hy) hc, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem _root_.CFSG.GH74.GLS.Hyp9A.K_normal (hh : Hyp9A x K L M T Q) (hs : IsSimpleGroup (kBar L))
    (hn : ∃ a b : kBar L, a * b ≠ b * a) (heven : 2 ∣ Nat.card ↥K) :
    ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
  intro c hc k hk
  by_contra hkc
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hh.twoTerminal.1.2.2
  have hK' : IsPCompIn 2 (centralizer ({x} : Set G)) (K.map (MulAut.conj c).toMonoidHom) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hK c
    rwa [map_conj_eq_self_of_mem' hc] at this
  have hne : K.map (MulAut.conj c).toMonoidHom ≠ K := by
    intro h
    apply hkc
    have hmem : c * k * c⁻¹ ∈ K.map (MulAut.conj c).toMonoidHom :=
      ⟨k, hk, by simp [MulAut.conj_apply]⟩
    rwa [h] at hmem
  have hle : K.map (MulAut.conj c).toMonoidHom ≤ CxK x K :=
    le_inf hK'.1 (Stage1.Thm2.Recip.le_cSec_of_ne hK' hK hne)
  have hcM : c ∈ M := hh.centralizer_le hc
  have hLc : K.map (MulAut.conj c).toMonoidHom ≤ L := by
    rintro _ ⟨k', hk', rfl⟩
    have : (MulAut.conj c).toMonoidHom k' = c * k' * c⁻¹ := by simp [MulAut.conj_apply]
    rw [this]
    exact hh.L_normal.2 c hcM k' (hh.K_le_L hk')
  have hO : K.map (MulAut.conj c).toMonoidHom ≤ pPrimeCoreOf 2 L := fun y hy =>
    Setup91.inf_CMK_le hs hn ⟨hLc hy, CxK_le_CMK hh (hle hy)⟩
  have hodd : Odd (Nat.card ↥(K.map (MulAut.conj c).toMonoidHom)) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd L) (Subgroup.card_dvd_of_le hO)
  rw [Subgroup.card_map_of_injective (MulAut.conj c).injective] at hodd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 heven)

end CFSG.GH74.GLS.C3.Layer1.Bk
