module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CMain
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CCase
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CLay
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Stage12.McLCover
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalInvolutionOddCore
public import CFSG.LocalAnalysis.OddStandard.Solomon75Inputs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Defs

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CatLeafProof

theorem gs81Step10CDiagInput_of (I : In81)
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog) :
    GS81Step10CDiagInput := by
  intro H _ _ h H₁ d v hst p f hp hp2 hf hJ hK hq h9 K _ _ hKc J₁ J₂ hne hJ₁ hJ₂ hL34
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  set F := centralizer ({h.a * d.z} : Set H) with hF
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥F) with hπ
  set s' : ↥F := ⟨h.a * d.sigma, Hyp59.L81Hyp.Data.asigma_mem_F⟩ with hs'
  have hs2 : s' * s' = 1 := Subtype.ext Hyp59.L81Hyp.Data.asigma_involution
  have hs2' : ∃ n : ℕ, s' ^ 2 ^ n = 1 := ⟨1, by rw [pow_one, pow_two]; exact hs2⟩
  have ht : π s' * π s' = 1 := by rw [← map_mul, hs2, map_one]
  set z' : ↥F := ⟨h.a * d.z, mem_centralizer_singleton_iff.mpr rfl⟩ with hz'
  have haa := Six.a_mul_a_self h.toHyp52
  have hza := d.z_comm_a
  have haz2 : h.a * d.z * (h.a * d.z) = 1 := by
    calc h.a * d.z * (h.a * d.z) = h.a * (d.z * h.a) * d.z := by group
      _ = h.a * (h.a * d.z) * d.z := by rw [hza]
      _ = 1 := by rw [← mul_assoc, haa, one_mul, d.z_mul_self]
  have haz1 : h.a * d.z ≠ 1 := by
    intro h1
    apply d.z_ne_a
    rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right haa]
  have hz'2 : orderOf z' = 2 := by
    rw [hz', Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact haz2) haz1
  have hzZ : π z' ∈ center (↥F ⧸ pPrimeCore 2 ↥F) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥F) y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.2)
  have hz1 : π z' ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := orderOf_dvd_natCard (⟨z', h1⟩ : ↥(pPrimeCore 2 ↥F))
    rw [Subgroup.orderOf_mk, hz'2] at h2
    exact Nat.not_even_iff_odd.mpr OddQuot.odd_card_pPrimeCore (even_iff_two_dvd.mpr h2)
  have hJF : ∀ {J : Subgroup H}, X10.AzComp K d J → J ≤ F := fun hJc =>
    hJc.1.trans inf_le_right
  obtain ⟨hC₁, hP₁, hE₁⟩ := Hyp59.L81Hyp.Data.azComp_facts hS hJ₁
  obtain ⟨hC₂, hP₂, hE₂⟩ := Hyp59.L81Hyp.Data.azComp_facts hS hJ₂
  obtain ⟨hM₁C, hM₁⟩ := Pump516.isPComponent_map_centralizer hs2' hC₁ hP₁
  obtain ⟨hM₂C, hM₂⟩ := Pump516.isPComponent_map_centralizer hs2' hC₂ hP₂
  have hne' : J₁.subgroupOf F ≠ J₂.subgroupOf F := by
    intro h1
    rw [subgroupOf_inj, inf_of_le_left (hJF hJ₁), inf_of_le_left (hJF hJ₂)] at h1
    exact hne h1
  have hMne := X10CP.map_ne_of_isPComponent_centralizer hs2 hC₁ hC₂ hP₁ hP₂ hne'
  have hE : ∀ {J : Subgroup H}, J.subgroupOf F ≤ pLayer ↥F 2 →
      (J.subgroupOf F).map π ≤ layer (↥F ⧸ pPrimeCore 2 ↥F) := fun h1 =>
    (map_mono h1).trans Pump516.map_pLayer_le_layer
  have hzM : ∀ {J : Subgroup H}, X10.AzComp K d J → π z' ∈ (J.subgroupOf F).map π :=
    fun {J} hJc => mem_map_of_mem π (show z' ∈ J.subgroupOf F from hJc.2.2.1)
  have hSL : ∀ {J : Subgroup H}, X10.AzComp K d J →
      Nonempty (↥((J.subgroupOf F).map π) ⧸ pPrimeCore 2 ↥((J.subgroupOf F).map π) ≃*
        Matrix.SpecialLinearGroup (Fin 2) K) := by
    intro J hJc
    obtain ⟨hJLC, -, -, ⟨eJ⟩⟩ := hJc
    let eJ' : ↥(J.subgroupOf F) ≃* ↥J := subgroupOfEquivOfLe (hJLC.trans inf_le_right)
    have q₀ : ↥(J.subgroupOf F) ⧸ pPrimeCore 2 ↥(J.subgroupOf F) ≃* ↥J ⧸ pPrimeCore 2 ↥J :=
      QuotientGroup.congr _ _ eJ' (pPrimeCore_map_iso 2 eJ')
    obtain ⟨q₁⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π OddQuot.not_two_dvd_card_ker
      (J.subgroupOf F)
    exact ⟨(q₁.symm.trans q₀).trans eJ⟩
  obtain ⟨e₁⟩ := hSL hJ₁
  obtain ⟨e₂⟩ := hSL hJ₂
  have hbound : padicValNat 2 (Nat.card (↥F ⧸ pPrimeCore 2 ↥F)) ≤
      2 * padicValNat 2 (p ^ (2 * f) - 1) + padicValNat 2 f + 3 := by
    have h1 := Hyp59.L81Hyp.Data.nu_card_H_le' I hst hp hp2 hf hJ
    have h2 := X10CV.padicValNat_le_of_dvd' 2 Nat.card_pos.ne'
      (card_quotient_dvd_card (pPrimeCore 2 ↥F))
    have h3 := X10CC.nu_le_card 2 F
    omega
  exact X10CF.false_of_config (pPrimeCore_quotient_pPrimeCore_eq_bot 2) ht hzZ hz1 hp2 hf hq hKc
    hMne hM₁C hM₁ (hE hE₁) (hzM hJ₁) e₁ hM₂C hM₂ (hE hE₂) (hzM hJ₂) e₂ hbound hL34

theorem gs81Step10CInput_of_N (I : In81)
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog) (hN : CFTwoNilpSL2) :
    GS81Step10CInput :=
  gs81Step10CInput_of_diag hN (gs81Step10CDiagInput_of I hS)

end CFSG.ComponentClassification.GSThmB
