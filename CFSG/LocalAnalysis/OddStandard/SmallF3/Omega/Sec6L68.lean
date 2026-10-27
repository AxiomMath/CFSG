module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec68_closure [Finite G] (h34c : Asc82Lemma34c) (h36 : Asc82Lemma36) (hM : Asc82Tab6M)
    (hF : Asc82AutFacts) {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L)
    (hL6 : IsOmega6Minus L) {B : Subgroup G} (hB : IsElemAb2 B 4) (hBL : B ≤ L) {g : G}
    (hgt : g⁻¹ * t * g ≠ t) (hgB : g⁻¹ * t * g ∈ cosetSet t B)
    (hBLg : B ≤ CFSG.conjugate L g) :
    ∀ n ∈ normalizer ((zpowers t ⊔ B : Subgroup G) : Set G), ∀ a ∈ cosetSet t B,
      n * a * n⁻¹ ∈ cosetSet t B := by
  intro n hn a ha
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hS.involution, pow_orderOf_eq_one]
  have hcommB : ∀ b ∈ B, b * t = t * b := fun b hb =>
    Subgroup.mem_centralizer_iff.mp (sec68_t_mem_centralizer hS) b (hBL hb)
  obtain ⟨h₁, h₂, h3⟩ := sec68_stabilizers h36 hM hS hL6 hB hBL hgt hgB hBLg
  have htT : t ∈ cosetSet t B := ⟨1, B.one_mem, (mul_one t).symm⟩
  have htrans := sec68_trans (N := normalizer ((zpowers t ⊔ B : Subgroup G) : Set G))
    (T := cosetSet t B) htT hgB hgt.symm h3 h₁ h₂
  obtain ⟨m, hm, hma⟩ := htrans a ha
  obtain ⟨b₁, hb₁, hab⟩ := ha
  have haA : a ∈ (zpowers t ⊔ B : Subgroup G) := by
    rw [hab]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_right hb₁)
  have hnA : n * a * n⁻¹ ∈ (zpowers t ⊔ B : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp hn a).mp haA
  rcases sec68_mem_sup ht2 hcommB hnA with hyB | ⟨b, hb, hyb⟩
  · exfalso
    have hyeq : n * a * n⁻¹ = (n * m) * t * (n * m)⁻¹ := by
      rw [← hma]
      group
    have hvL : (n * m) * t * (n * m)⁻¹ ∈ L := by
      rw [← hyeq]
      exact hBL hyB
    have hv2 : orderOf ((n * m) * t * (n * m)⁻¹) = 2 := by
      simpa only [inv_inv, hS.involution] using orderOf_conjugate_eq t ((n * m)⁻¹)
    exact sec66_not_mem h34c h36 hM hF hS hL6 (g := (n * m)⁻¹)
      (by simpa only [inv_inv] using hvL) (by simpa only [inv_inv] using hv2)
  · exact ⟨b, hb, hyb⟩

theorem asc82Lemma68_of (h34c : Asc82Lemma34c) (h36 : Asc82Lemma36) (h82 : Asc82Lemma82)
    (hM : Asc82Tab6M) (hF : Asc82AutFacts) : Asc82Lemma68 := by
  intro G _ _ t L hS hL6 B hB hBL g hgt hgB hBLg
  obtain ⟨h₁, h₂, h3⟩ := sec68_stabilizers h36 hM hS hL6 hB hBL hgt hgB hBLg
  refine ⟨sec68_sylow h36 h82 hM hS hL6 hB hBL hgt hgB hBLg, ?_⟩
  have htT : t ∈ cosetSet t B := ⟨1, B.one_mem, (mul_one t).symm⟩
  exact sec68_conjTwoTrans (sec68_closure h34c h36 hM hF hS hL6 hB hBL hgt hgB hBLg) htT hgB
    hgt.symm h3 h₁ h₂

end CFSG.OddStandard.SmallF3.Omega
