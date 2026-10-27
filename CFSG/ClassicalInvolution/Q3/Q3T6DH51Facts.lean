module

public import CFSG.ClassicalInvolution.Q3.Q3CHHyp51

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Asc77

section Images

variable {G : Type} [Group G] [Finite G]

theorem isUniqueInvolution_modOdd3 {c w : G} {M : Subgroup G}
    (hw : IsUniqueInvolution M w) (hwC : w ∈ Subgroup.centralizer ({c} : Set G)) :
    IsUniqueInvolution (modOdd c M) (oddQuotMk c ⟨w, hwC⟩) := by
  have hz : IsUniqueInvolution (M.subgroupOf (Subgroup.centralizer ({c} : Set G))) ⟨w, hwC⟩ := by
    refine ⟨hw.mem, fun h => hw.ne_one (congrArg Subtype.val h), Subtype.ext hw.sq, ?_⟩
    intro y hy hy2
    rcases hw.unique (y : G) hy (congrArg Subtype.val hy2) with h | h
    · left
      exact Subtype.ext h
    · right
      exact Subtype.ext h
  exact isUniqueInvolution_map_mk_of_odd
    (odd_natCard_inf (OddCore.odd_card ↥(Subgroup.centralizer ({c} : Set G))) _) hz

omit [Finite G] in
theorem oddQuotMk_mem_sup3 {c : G} {A A' : Subgroup G}
    (hA : A ≤ Subgroup.centralizer ({c} : Set G)) (hA' : A' ≤ Subgroup.centralizer ({c} : Set G))
    {x : G} (hx : x ∈ A ⊔ A') (hxC : x ∈ Subgroup.centralizer ({c} : Set G)) :
    oddQuotMk c ⟨x, hxC⟩ ∈ modOdd c A ⊔ modOdd c A' := by
  have h1 : (⟨x, hxC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
      A.subgroupOf (Subgroup.centralizer ({c} : Set G)) ⊔
        A'.subgroupOf (Subgroup.centralizer ({c} : Set G)) := by
    rw [← Subgroup.subgroupOf_sup hA hA']
    exact hx
  have h2 := Subgroup.mem_map_of_mem (oddQuotMk c) h1
  rwa [Subgroup.map_sup] at h2

theorem eq_of_oddQuotMk_eq3 {c : G} {B : Subgroup G} (hB : CFSG.Open.IsElemAbelian 2 B)
    {d₁ d₂ : G} (hd₁ : d₁ ∈ B) (hd₂ : d₂ ∈ B) (h₁ : d₁ ∈ Subgroup.centralizer ({c} : Set G))
    (h₂ : d₂ ∈ Subgroup.centralizer ({c} : Set G))
    (h : oddQuotMk c ⟨d₁, h₁⟩ = oddQuotMk c ⟨d₂, h₂⟩) : d₁ = d₂ := by
  have hsq : (⟨d₁, h₁⟩ * ⟨d₂, h₂⟩ : ↥(Subgroup.centralizer ({c} : Set G))) *
      (⟨d₁, h₁⟩ * ⟨d₂, h₂⟩) = 1 :=
    Subtype.ext (Lemma52Proof.mul_self_eq_one_of_mem hB (B.mul_mem hd₁ hd₂))
  have hd2 : d₂ * d₂ = 1 := Lemma52Proof.mul_self_eq_one_of_mem hB hd₂
  have h1 : oddQuotMk c (⟨d₁, h₁⟩ * ⟨d₂, h₂⟩) = 1 := by
    rw [map_mul, h, ← map_mul]
    have : (⟨d₂, h₂⟩ * ⟨d₂, h₂⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 := Subtype.ext hd2
    rw [this, map_one]
  have h3 : d₁ * d₂ = 1 := congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h1)
  rw [eq_inv_of_mul_eq_one_left h3]
  exact inv_eq_of_mul_eq_one_right hd2

end Images

section Induced


variable {G : Type} [Group G] [Finite G]

theorem inducedImage_facts {A : Subgroup G} {s z₁ z₂ : G}
    (hA : CFSG.Open.IsElemAbelian 2 A) (hAgen : A = Subgroup.closure {z₁, z₂, s})
    {L : Subgroup (OddQuot s)}
    (hL : ∀ d ∈ ({z₁, z₂, z₁ * z₂} : Set G), ∀ hdC : d ∈ Subgroup.centralizer ({s} : Set G),
      oddQuotMk s ⟨d, hdC⟩ ∈ L)
    (hz₁C : z₁ ∈ Subgroup.centralizer ({s} : Set G))
    (hmov : ∃ y ∈ L, oddQuotMk s ⟨z₁, hz₁C⟩ * y ≠ y * oddQuotMk s ⟨z₁, hz₁C⟩) :
    (∀ x ∈ inducedImage L (modOdd s A), x * x = 1) ∧
      (∃ x ∈ inducedImage L (modOdd s A), x ≠ 1) ∧
      ∀ x ∈ inducedImage L (modOdd s A),
        ((x : ↥(inducedAutOn L)) : MulAut ↥L) ∈ innSubgroup ↥L := by
  have hz₁A : z₁ ∈ A := hAgen ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hz₁L : oddQuotMk s ⟨z₁, hz₁C⟩ ∈ L := hL z₁ (Set.mem_insert _ _) hz₁C
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    have hww : w * w = 1 := by
      apply Subtype.ext
      obtain ⟨k, hkA, hk⟩ := hw
      have hk' : oddQuotMk s k = (w : OddQuot s) := hk
      have hkk : k * k = 1 := Subtype.ext (Lemma52Proof.mul_self_eq_one_of_mem hA hkA)
      show (w : OddQuot s) * w = 1
      rw [← hk', ← map_mul, hkk, map_one]
    rw [← map_mul, hww, map_one]
  · refine ⟨toInducedAutOn L ⟨oddQuotMk s ⟨z₁, hz₁C⟩, Subgroup.le_normalizer hz₁L⟩,
      ⟨_, oddQuotMk_mem_modOdd hz₁A hz₁C, rfl⟩, fun h1 => ?_⟩
    obtain ⟨y, hyL, hy⟩ := hmov
    apply hy
    have h2 : conjOnNormalizer L ⟨oddQuotMk s ⟨z₁, hz₁C⟩, Subgroup.le_normalizer hz₁L⟩ = 1 :=
      congrArg Subtype.val h1
    have h3 := congrArg (fun τ : MulAut ↥L => ((τ ⟨y, hyL⟩ : ↥L) : OddQuot s)) h2
    change oddQuotMk s ⟨z₁, hz₁C⟩ * y * (oddQuotMk s ⟨z₁, hz₁C⟩)⁻¹ = y at h3
    calc oddQuotMk s ⟨z₁, hz₁C⟩ * y
        = oddQuotMk s ⟨z₁, hz₁C⟩ * y * (oddQuotMk s ⟨z₁, hz₁C⟩)⁻¹ * oddQuotMk s ⟨z₁, hz₁C⟩ := by
          group
      _ = y * oddQuotMk s ⟨z₁, hz₁C⟩ := by rw [h3]
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : (w : OddQuot s) ∈ modOdd s A := hw
    obtain ⟨d, hd, hdC, e, he, hwe⟩ := exists_mul_central_of_mem_modOdd hA hAgen hw'
    rcases hd with rfl | hd
    · have h1 := conjOnNormalizer_eq_conj w L.one_mem he
        (by rw [hwe, show oddQuotMk s ⟨1, hdC⟩ = 1 from map_one _])
      exact ⟨⟨1, L.one_mem⟩, h1.symm⟩
    · exact ⟨⟨_, hL d hd hdC⟩, (conjOnNormalizer_eq_conj w (hL d hd hdC) he hwe).symm⟩

theorem inducedAut_ne_one {s z₁ : G} {L : Subgroup (OddQuot s)}
    (hz₁C : z₁ ∈ Subgroup.centralizer ({s} : Set G)) (hz₁L : oddQuotMk s ⟨z₁, hz₁C⟩ ∈ L)
    (hmov : ∃ y ∈ L, oddQuotMk s ⟨z₁, hz₁C⟩ * y ≠ y * oddQuotMk s ⟨z₁, hz₁C⟩) :
    toInducedAutOn L ⟨oddQuotMk s ⟨z₁, hz₁C⟩, Subgroup.le_normalizer hz₁L⟩ ≠ 1 := by
  intro h1
  obtain ⟨y, hyL, hy⟩ := hmov
  apply hy
  have h2 : conjOnNormalizer L ⟨oddQuotMk s ⟨z₁, hz₁C⟩, Subgroup.le_normalizer hz₁L⟩ = 1 :=
    congrArg Subtype.val h1
  have h3 := congrArg (fun τ : MulAut ↥L => ((τ ⟨y, hyL⟩ : ↥L) : OddQuot s)) h2
  change oddQuotMk s ⟨z₁, hz₁C⟩ * y * (oddQuotMk s ⟨z₁, hz₁C⟩)⁻¹ = y at h3
  calc oddQuotMk s ⟨z₁, hz₁C⟩ * y
      = oddQuotMk s ⟨z₁, hz₁C⟩ * y * (oddQuotMk s ⟨z₁, hz₁C⟩)⁻¹ * oddQuotMk s ⟨z₁, hz₁C⟩ := by
        group
    _ = y * oddQuotMk s ⟨z₁, hz₁C⟩ := by rw [h3]

theorem exists_classical_inner_image {A : Subgroup G} {s z₁ : G} (hz₁A : z₁ ∈ A)
    {L : Subgroup (OddQuot s)} (hz₁C : z₁ ∈ Subgroup.centralizer ({s} : Set G))
    (hz₁L : oddQuotMk s ⟨z₁, hz₁C⟩ ∈ L)
    (hmov : ∃ y ∈ L, oddQuotMk s ⟨z₁, hz₁C⟩ * y ≠ y * oddQuotMk s ⟨z₁, hz₁C⟩)
    (hK : ∃ K : Subgroup (↥L ⧸ Subgroup.center ↥L),
      IsClassicalMember3 K (QuotientGroup.mk ⟨oddQuotMk s ⟨z₁, hz₁C⟩, hz₁L⟩)) :
    ∃ x ∈ inducedImage L (modOdd s A), x ≠ 1 ∧
      ClassicalInner ↥L ((x : ↥(inducedAutOn L)) : MulAut ↥L) := by
  refine ⟨toInducedAutOn L ⟨oddQuotMk s ⟨z₁, hz₁C⟩, Subgroup.le_normalizer hz₁L⟩,
    ⟨_, oddQuotMk_mem_modOdd hz₁A hz₁C, rfl⟩, inducedAut_ne_one hz₁C hz₁L hmov, ?_⟩
  have h1 := conjOnNormalizer_eq_conj
    (⟨oddQuotMk s ⟨z₁, hz₁C⟩, Subgroup.le_normalizer hz₁L⟩ :
      ↥(Subgroup.normalizer (L : Set (OddQuot s)))) hz₁L (Subgroup.center _).one_mem
    (by rw [mul_one])
  exact ⟨⟨_, hz₁L⟩, h1.symm, hK⟩

end Induced

end CFSG.ClassicalInvolution.Q3.Q3T6D
