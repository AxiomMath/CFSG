module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClL4
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamCl5
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamL3
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowS
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.C3.Layer1.BkIvk73Q
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClL5
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Fixed
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Kill
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Leaf2
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.KFacts
public import CFSG.GH74.Generic.S3.V1InnerEps
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.Sporadic.Th.Max3.Packet

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

namespace Lem711Cfg

variable {X : Type} [Group X] [Finite X] {L K : Subgroup X} {x y : X}

theorem l4_rowS {k : Type} [Field k] [Finite k] {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = ℓ ^ e) (h : Lem711Cfg X L K x y) (eL : ↥L ≃* projectiveSL 4 k) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = Nat.card k ^ 2 ∧
      Nonempty (↥K ≃* projectiveSL 2 E) := by
  classical
  have := h.normal
  have hZ : center (projectiveSL 4 k) = ⊥ := by
    rw [← Subgroup.map_center_eq eL, h.center_L_eq_bot, Subgroup.map_bot]
  obtain ⟨ρ, hinj, hρW, -, -⟩ := CFSG.ComponentClassification.OutcomeLocal.socle_extension
    (W := L) h.centralizer_eq_bot eL hZ
  obtain ⟨hW, hCA, hCW, hL₁⟩ := CFSG.ComponentClassification.OddSelector.socle_images eL hinj hρW
    h.K_le h.isComponentOf_centralizer
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.hx, pow_two] at this
  have hD : ρ x ∈ linearAutGroup 4 k := by
    have h1 : ρ x ∈ (⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆).map ρ := ⟨x, h.x_mem_commutator, rfl⟩
    rw [Subgroup.map_commutator] at h1
    have hle : ⁅(⊤ : Subgroup (MulAut (projectiveSL 4 k))), (⊤ : Subgroup (MulAut (projectiveSL 4 k)))⁆ ≤
        linearAutGroup 4 k := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [commutatorElement_def]
      exact L3Aut.commutator_mem_linearAutGroup (by norm_num) hℓ hk a b
    exact hle (Subgroup.commutator_mono le_top le_top h1)
  obtain ⟨p', f', hp', hp2', hf', -, hmodel⟩ := h.exists_hsrc
  have hsrc : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ center ↥K) .PSL 2 p' f' :=
    Generic.S45.LQ.stated_of_lieModel_PSL hmodel
  rcases IVK.l4_type hℓ hℓ2 he hk hp2' (Or.inl hsrc) h.odd_card_center hinj h.hx hL₁ with
    ⟨B, μ, hρB, hμ, hsq⟩ | ⟨B, hρB, -⟩
  · have htwo : (2 : k) ≠ 0 := by
      have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
      exact Ring.two_ne_zero (by rw [ringChar.eq k ℓ]; exact hℓ2)
    obtain ⟨-, E, hE, hEf, hEc, hKE⟩ := CFSG.ComponentClassification.OddSelector.selectorRowS_of_inner
      htwo hinj hCA hCW hL₁ hρB hμ hsq
    exact ⟨E, hE, hEf, hEc, hKE⟩
  · exfalso
    obtain ⟨C, hC⟩ := mem_linearAutGroup_iff.1 hD
    have hδ : dualAut 4 k ∈ linearAutGroup 4 k := by
      have h2 : dualAut 4 k = conjAut 4 k (B⁻¹ * C) := by
        rw [map_mul, map_inv, hC, hρB]
        group
      rw [h2]
      exact conjAut_mem_linearAutGroup _
    exact ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := k) (by norm_num)
      (linearAutGroup_le_semilinearAutGroup hδ)

end Lem711Cfg


theorem lem711_l4_of_three (h43 : Lem711Empty (fun X _ => LieModel X .PSL 4 3 1))
    (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Lem711Empty (fun X _ => LieModel X .PSL 4 p f) := by
  intro X _ _ L K x y h hL
  obtain ⟨k, _, _, hk, ⟨eL⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  obtain ⟨E, _, _, hE, ⟨eK⟩⟩ := h.l4_rowS hp hp2 hf hk eL
  have hEq : Nat.card E = (p ^ f) ^ 2 := by rw [hE, hk]
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hKP : Nat.card ↥K = Nat.card E * (Nat.card E ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eK.toEquiv,
      ← Nat.card_congr (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 E).toEquiv]
    exact CFSG.GorensteinWalter.psl2_card_formula E
      ⟨p, 2 * f, hp, hodd, by omega, by rw [hEq, ← pow_mul, mul_comm]⟩
  have hsimple : IsSimpleGroup ↥K := by
    have h4 : ∃ s : Finset E, s.card = 4 := by
      classical
      have : Fintype E := Fintype.ofFinite E
      have hpf : 3 ≤ p ^ f := by
        have : 3 ≤ p := by
          have := hp.two_le
          obtain ⟨t, ht⟩ := hodd
          omega
        exact this.trans (Nat.le_self_pow (by omega) p)
      have hcard : 4 ≤ Fintype.card E := by
        rw [← Nat.card_eq_fintype_card, hEq]
        nlinarith
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset E)) (n := 4) hcard
      exact ⟨s, hs⟩
    have h0 := (CFSG.LinearGroups.linear_projective_simple (K := E) (n := 2) le_rfl (Or.inr h4)).2.1
    have h1 : IsSimpleGroup (projectiveSL 2 E) :=
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 E).symm.isSimpleGroup
    exact eK.isSimpleGroup
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := h.K_quasi
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun hc => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc])⟩
  have hO : pPrimeCore 2 ↥K = ⊥ := by
    rw [h.pPrimeCore_eq_center]
    exact LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hnab
  have hKc : Nat.card ↥K = 360 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
    have h2 : Nat.card ↥(pPrimeCore 2 ↥K) = 1 := by rw [hO]; exact Subgroup.card_bot
    rw [h2, mul_one, h.card_K_bar] at h1
    exact h1
  have hn : Nat.card E = 9 := by
    have h1 := hKP
    rw [hKc] at h1
    set n := Nat.card E with hn
    have hn2 : 2 ≤ n := by
      rw [hEq]
      have : 3 ≤ p ^ f := by
        have : 3 ≤ p := by
          have := hp.two_le
          obtain ⟨t, ht⟩ := hodd
          omega
        exact this.trans (Nat.le_self_pow (by omega) p)
      nlinarith
    have h2 : n * (n ^ 2 - 1) = 720 := by
      have hev : Even (n * (n ^ 2 - 1)) := by
        rcases Nat.even_or_odd n with he | ho
        · exact he.mul_right _
        · have : Even (n ^ 2 - 1) := Nat.Odd.sub_odd ho.pow odd_one
          exact this.mul_left n
      have := Nat.div_mul_cancel hev.two_dvd
      omega
    have hle : n ≤ 9 := by
      by_contra hlt
      push Not at hlt
      have : 10 * (10 ^ 2 - 1) ≤ n * (n ^ 2 - 1) := Nat.mul_le_mul (by omega) (by
        have := Nat.pow_le_pow_left (show 10 ≤ n by omega) 2
        omega)
      omega
    interval_cases n <;> omega
  have hq3 : p ^ f = 3 := by
    rw [hEq] at hn
    have : (p ^ f) ^ 2 = 3 ^ 2 := by rw [hn]; norm_num
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) this
  rcases L3Aut.odd_prime_pow_eq_three_or_five_le hp hp2 hf with ⟨rfl, rfl⟩ | h5
  · exact h43 X L K x y h hL
  · omega

end CFSG.GH74.GLS
