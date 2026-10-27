module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainCases

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open Involution SectionSix AschbacherToolkit CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G}
  {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem le_centralizer_of_pRank_le_one {P : Subgroup G} (hP : IsPGroup 2 P)
    (hr : CFSG.Open.pRank 2 P ≤ 1) {c : G} (hcP : c ∈ P) (hc2 : orderOf c = 2) :
    P ≤ Subgroup.centralizer ({c} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : x * c * x⁻¹ ∈ P := P.mul_mem (P.mul_mem hx hcP) (P.inv_mem hx)
  have h2 : orderOf (x * c * x⁻¹) = 2 := by
    rw [← hc2]
    exact MulEquiv.orderOf_eq (MulAut.conj x) c
  have h3 := eq_of_pRank_le_one hP hr h1 hcP h2 hc2
  calc x * c = (x * c * x⁻¹) * x := by group
    _ = c * x := by rw [h3]

namespace FieldHyps

variable {t g : G}

theorem pRank_factor_inf_centralizer_le_one (hin : SectionSevenBase)
    (hC : Counterexample G D 2 Abar) (hF : FieldHyps D Abar t g) (i : Fin 2) :
    CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar i) ⊓
      Subgroup.centralizer ({t} : Set G)) ≤ 1 :=
  pRank_le_one_of_conjugate hin hC hF.not_mem
    (fun _ hx => (hF.hyp71 hC).centralizer_le hx.2)
    (fun _ hx hx1 hx2 => centralizer_le_of_mem_factor hC hx.1 hx2 hx1)

theorem not_mem_D (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) {i i' : Fin 2} (hii' : i ≠ i')
    (hnd : ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar i)) : t ∉ D := by
  intro htD
  obtain ⟨a, ha, b, hb, hab⟩ :=
    canonical_two_factor_product D Abar hC.hyp.hcomm hC.hyp.hgen i i' hii' t htD
  apply hF.false_of_centralizes_inv_mul hin hC hii' hnd ha
  have h1 : a⁻¹ * t = b := by rw [hab, inv_mul_cancel_left]
  rw [h1]
  exact cross_factor_centralizes D Abar hC.hyp.hcomm i i' hii' b hb

theorem isSylowOf_inf_factor (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) {i : Fin 2} {c : G}
    (hcA : c ∈ aschbacherThm5Preimage D (Abar i)) (hc2 : orderOf c = 2) (hct : c * t = t * c)
    {S : Subgroup G} (hS : IsSylowOf 2 S (Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer ({t} : Set G))) :
    c ∈ S ∧ IsSylowOf 2 (S ⊓ aschbacherThm5Preimage D (Abar i))
      (aschbacherThm5Preimage D (Abar i) ⊓ Subgroup.centralizer ({t} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar i) with hAdef
  set CE := Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) with hCE
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    omega
  have hCc : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (D : Set G) :=
    centralizer_le_of_mem_factor hC hcA (two_power_of_orderOf hc2) hc1
  have hCEH : CE ≤ Subgroup.normalizer (D : Set G) := inf_le_left.trans hCc
  have hcCE : c ∈ CE := ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl,
    Subgroup.mem_centralizer_singleton_iff.mpr hct⟩
  have hcS : c ∈ S := by
    obtain ⟨P, rfl⟩ := hS
    have hcen : Subgroup.zpowers (⟨c, hcCE⟩ : CE) ≤ Subgroup.center CE := by
      rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2.1)
    have : (Subgroup.zpowers (⟨c, hcCE⟩ : CE)).Normal := Subgroup.normal_of_le_center hcen
    have h2 : IsPGroup 2 (Subgroup.zpowers (⟨c, hcCE⟩ : CE)) :=
      isPGroup_zpowers_two (k := 1) (Subtype.ext (by
        change c ^ 2 ^ 1 = 1
        rw [pow_one, ← hc2]
        exact pow_orderOf_eq_one c))
    exact ⟨⟨c, hcCE⟩, h2.le_sylow_of_normal P (Subgroup.mem_zpowers _), rfl⟩
  set N₁ := CE ⊓ Subgroup.normalizer (A : Set G) with hN₁def
  have hN₁ : CE ≤ Subgroup.normalizer (N₁ : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyCE, hyA⟩
      exact ⟨CE.mul_mem (CE.mul_mem hx hyCE) (CE.inv_mem hx),
        conj_mem_normalizer_factor hC.hyp (hCEH hx) (hCEH hyCE) hyA⟩
    · rintro ⟨hyCE, hyA⟩
      have hy : y = x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ := by group
      refine ⟨?_, ?_⟩
      · rw [hy]
        exact CE.mul_mem (CE.mul_mem (CE.inv_mem hx) hyCE) (CE.inv_mem (CE.inv_mem hx))
      · rw [hy]
        exact conj_mem_normalizer_factor hC.hyp (hCEH (CE.inv_mem hx)) (hCEH hyCE) hyA
  have hS₁ := hS.inf_of_le_normalizer (inf_le_left : N₁ ≤ CE) hN₁
  have hYN₁ : CE ⊓ A ≤ N₁ := fun x hx => ⟨hx.1, Subgroup.le_normalizer hx.2⟩
  have hN₁Y : N₁ ≤ Subgroup.normalizer ((CE ⊓ A : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx.1, hx.2⟩
  have hS₂ := hS₁.inf_of_le_normalizer hYN₁ hN₁Y
  have heq : S ⊓ N₁ ⊓ (CE ⊓ A) = S ⊓ A := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
    · intro x hx
      have hxCE := hS.le hx.1
      exact ⟨⟨hx.1, hxCE, Subgroup.le_normalizer hx.2⟩, hxCE, hx.2⟩
  rw [heq] at hS₂
  have hSA : S ⊓ A ≤ A ⊓ Subgroup.centralizer ({t} : Set G) := fun x hx => ⟨hx.2, (hS.le hx.1).2⟩
  obtain ⟨P, hP, hSP⟩ := exists_isSylowOf_le hSA (hS.isPGroup.to_le inf_le_left)
  have hcP : c ∈ P := hSP ⟨hcS, hcA⟩
  have hPr : CFSG.Open.pRank 2 P ≤ 1 :=
    (CFSG.SectionRank.pRank_mono one_lt_two hP.le).trans
      (hF.pRank_factor_inf_centralizer_le_one hin hC i)
  have hPc := le_centralizer_of_pRank_le_one hP.isPGroup hPr hcP hc2
  have hPY : P ≤ CE ⊓ A := fun x hx => ⟨⟨hPc hx, (hP.le hx).2⟩, (hP.le hx).1⟩
  have hcard := IsSylowOf.card_le_of_le hS₂ hPY hP.isPGroup
  have hPeq : S ⊓ A = P := Subgroup.eq_of_le_of_card_ge hSP hcard
  exact ⟨hcS, hPeq ▸ hP⟩

end FieldHyps

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
