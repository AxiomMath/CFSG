module

public import CFSG.ClassicalInvolution.Q3.Q3T6DH51Facts
public import CFSG.ClassicalInvolution.Q3.Q3T6DH51M11
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FrameSimple

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Asc77

section Rows

theorem isUniqueInvolution_of_le' {G : Type} [Group G] {N K : Subgroup G} {b : G}
    (hU : IsUniqueInvolution K b) (hbN : b ∈ N) (hNK : N ≤ K) : IsUniqueInvolution N b :=
  ⟨hbN, hU.ne_one, hU.sq, fun y hy hy2 => hU.unique y (hNK hy) hy2⟩

end Rows

section Core


@[expose] def D4InnerAlphaThree : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L : Subgroup H)
    (ψ : (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K →* H), ψ.range = L →
      ψ.ker ≤ Subgroup.center _ → ∀ A : Subgroup ↥(inducedAutOn L), (∀ x ∈ A, x * x = 1) →
        (∀ x ∈ A, ((x : ↥(inducedAutOn L)) : MulAut ↥L) ∈ innSubgroup ↥L) →
          (∃ x ∈ A, x ≠ 1 ∧ ClassicalInner ↥L ((x : ↥(inducedAutOn L)) : MulAut ↥L)) →
            alphaOf A = ⊥

theorem alphaOf_inducedImage_eq_bot_of_kind (hD4 : D4InnerAlphaThree) {c : CompData}
    (hc : ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t ∧
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 ∧ c = CompData.model t n)
    {H : Type} [Group H] [Finite H] (ψ : c.G →* H) (hker : ψ.ker ≤ Subgroup.center c.G)
    (B : Subgroup H) (h2 : ∀ x ∈ inducedImage ψ.range B, x * x = 1)
    (hne : ∃ x ∈ inducedImage ψ.range B, x ≠ 1)
    (hinn : ∀ x ∈ inducedImage ψ.range B,
      ((x : ↥(inducedAutOn ψ.range)) : MulAut ↥ψ.range) ∈ innSubgroup ↥ψ.range)
    (hcl : ∃ x ∈ inducedImage ψ.range B, x ≠ 1 ∧
      ClassicalInner ↥ψ.range ((x : ↥(inducedAutOn ψ.range)) : MulAut ↥ψ.range)) :
    alphaOf (inducedImage ψ.range B) = ⊥ := by
  obtain ⟨t, n, ht, hadm, rfl⟩ := hc
  by_cases hd4 : t = .POmegaPlus ∧ n = 4
  · obtain ⟨rfl, rfl⟩ := hd4
    exact hD4 H ψ.range ψ rfl hker _ h2 hinn hcl
  · exact alphaOf_inducedImage_eq_bot_of_inner ψ.range B
      (autOddFreeInner_range_of_model_ne_D4 ht hadm hd4 rfl ψ hker) h2 hne hinn

theorem hyp51At_of_twin_layer3_core (hD4 : D4InnerAlphaThree) {G : Type} [Group G] [Finite G]
    (hBelow : CIT3Below (Nat.card G)) {Φ : Set (Subgroup G)} {c b d : G} {M M' B : Subgroup G}
    (hΦ : SecData3 c Φ) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G) (hM : M ∈ Φ) (hM' : M' ∈ Φ)
    (hMb : IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M b)
    (hM'b : IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M' b)
    (hbU : IsUniqueInvolution M b) (hbU' : IsUniqueInvolution M' b)
    (hB : CFSG.Open.IsElemAbelian 2 B) (hbB : b ∈ B) (hdB : d ∈ B) (hcB : c ∈ B)
    (hBgen : B = Subgroup.closure ({b, d, c} : Set G)) (hc1 : c ≠ 1) (hbc : b ≠ c)
    (hd1 : d ≠ 1) (hdb : d ≠ b) (hdsup : d ∈ M ⊔ M') : Asc77.Hyp51At B c := by
  classical
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_of_secData3 hΦ hBelow hnc
  have hb1 : b ≠ 1 := fun h => by
    have := hMb.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hbC : b ∈ Subgroup.centralizer ({c} : Set G) := hMb.le hMb.mem
  have hdC : d ∈ Subgroup.centralizer ({c} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hB hcB hdB
  have hMC : M ≤ Subgroup.centralizer ({c} : Set G) := hMb.le
  have hM'C : M' ≤ Subgroup.centralizer ({c} : Set G) := hM'b.le
  obtain ⟨j₁, hj₁⟩ := exists_modOdd_le_secComp hΦ D hM
  obtain ⟨j₂, hj₂⟩ := exists_modOdd_le_secComp hΦ D hM'
  have hb₁ : oddQuotMk c ⟨b, hbC⟩ ∈ modOdd c M := oddQuotMk_mem_modOdd hbU.mem hbC
  have hb₂ : oddQuotMk c ⟨b, hbC⟩ ∈ modOdd c M' := oddQuotMk_mem_modOdd hbU'.mem hbC
  have hm₁ : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L →
      L = secComp hΦ D j₁ := fun L hL hm =>
    eq_secComp_of_movedByAll hΦ D hB hcB hc1 hbB hb1 hbc hbC (hj₁ hb₁) hL hm
  have hm₂ : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L →
      L = secComp hΦ D j₂ := fun L hL hm =>
    eq_secComp_of_movedByAll hΦ D hB hcB hc1 hbB hb1 hbc hbC (hj₂ hb₂) hL hm
  refine ⟨fun L L' hL hL' hm hm' => (hm₁ L hL hm).trans (hm₁ L' hL' hm').symm,
    fun L hL hm => ?_⟩
  have hLj₁ := hm₁ L hL hm
  have hLj₂ := hm₂ L hL hm
  have hle₁ : modOdd c M ≤ L := hLj₁ ▸ hj₁
  have hle₂ : modOdd c M' ≤ L := hLj₂ ▸ hj₂
  have hmovb : ∃ y ∈ L, oddQuotMk c ⟨b, hbC⟩ * y ≠ y * oddQuotMk c ⟨b, hbC⟩ :=
    hm _ (oddQuotMk_mem_modOdd hbB hbC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hbB hb1 hbc hbC)
  have hbL : oddQuotMk c ⟨b, hbC⟩ ∈ L := hle₁ hb₁
  have hdL : oddQuotMk c ⟨d, hdC⟩ ∈ L :=
    (sup_le hle₁ hle₂) (oddQuotMk_mem_sup3 hMC hM'C hdsup hdC)
  have hL3 : ∀ x ∈ ({b, d, b * d} : Set G), ∀ hxC : x ∈ Subgroup.centralizer ({c} : Set G),
      oddQuotMk c ⟨x, hxC⟩ ∈ L := by
    rintro x (rfl | rfl | rfl) hxC
    · exact hbL
    · exact hdL
    · have : oddQuotMk c ⟨b * d, hxC⟩ = oddQuotMk c ⟨b, hbC⟩ * oddQuotMk c ⟨d, hdC⟩ := by
        rw [← map_mul]
        rfl
      rw [this]
      exact L.mul_mem hbL hdL
  obtain ⟨hsq, hne, hinn⟩ := inducedImage_facts hB hBgen hL3 hbC hmovb
  obtain ⟨hbL', K₀, hK₀⟩ := exists_classical_center hMb hbC hle₁ hmovb
  have hcl := exists_classical_inner_image hbB hbC hbL' hmovb ⟨K₀, hK₀⟩
  have hk := kind_of_isComponent_secComp hΦ D (hLj₁ ▸ hL)
  subst hLj₁
  rcases hk with ⟨t, n, ht, hadm, hc⟩ | hc
  · exact alphaOf_inducedImage_eq_bot_of_kind hD4 ⟨t, n, ht, hadm, hc⟩
      ((sectionQuotientHom (normalizesLayer_of_secData3 hΦ)).comp (D.hom j₁))
      (Q3CH.ker_comp_le_center D _ (sectionQuotientHom_injective _) j₁) (modOdd c B) hsq hne hinn
      hcl
  · exfalso
    have hcoll := m11_twin_glue hΦ D hc hM hM' hle₁ hle₂ hbU hbU'
    have hdmem : oddQuotMk c ⟨d, hdC⟩ ∈ modOdd c M := by
      have h1 := oddQuotMk_mem_sup3 hMC hM'C hdsup hdC
      rwa [← hcoll, sup_idem] at h1
    have hd2 : oddQuotMk c ⟨d, hdC⟩ * oddQuotMk c ⟨d, hdC⟩ = 1 := by
      rw [← map_mul]
      have : (⟨d, hdC⟩ * ⟨d, hdC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 :=
        Subtype.ext (Lemma52Proof.mul_self_eq_one_of_mem hB hdB)
      rw [this, map_one]
    rcases (isUniqueInvolution_modOdd3 hbU hbC).unique _ hdmem hd2 with h | h
    · refine hd1 (eq_of_oddQuotMk_eq3 hB hdB B.one_mem hdC (Subgroup.one_mem _) ?_)
      rw [h]
      exact (map_one _).symm
    · exact hdb (eq_of_oddQuotMk_eq3 hB hdB hbB hdC hbC h)

theorem hyp51At_of_twin_layer3 (hD4 : D4InnerAlphaThree) {G : Type} [Group G] [Finite G]
    [FrameSimple G] {Ω : Set (Subgroup G)} {c b d : G} {K K' B : Subgroup G} (hΩ : InClass3 Ω)
    (hBelow : CIT3Below (Nat.card G)) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hbK : IsClassicalMember3 K b) (hbK' : IsClassicalMember3 K' b)
    (hbU : IsUniqueInvolution K b) (hbU' : IsUniqueInvolution K' b)
    (hMK : K ∈ tqMembers3 Ω c) (hMK' : K' ∈ tqMembers3 Ω c)
    (hB : CFSG.Open.IsElemAbelian 2 B) (hbB : b ∈ B) (hdB : d ∈ B) (hcB : c ∈ B)
    (hBgen : B = Subgroup.closure ({b, d, c} : Set G)) (hc1 : c ≠ 1) (hbc : b ≠ c)
    (hd1 : d ≠ 1) (hdb : d ≠ b) (hdsup : d ∈ exactCore3 c K ⊔ exactCore3 c K') :
    Asc77.Hyp51At B c := by
  classical
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) :=
    ExactLayer.isPGroup_zpowers_of_sq_eq_one (Lemma52Proof.mul_self_eq_one_of_mem hB hcB)
  have hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    have hc : c ∈ Subgroup.center G := hsub (Set.mem_singleton c)
    rw [FrameSimple.center hnab, Subgroup.mem_bot] at hc
    exact hc1 hc
  have hΦ := secData3_exactFamily hΩ hc2 ⟨K, hMK⟩
  exact hyp51At_of_twin_layer3_core hD4 hBelow hΦ hnc (exactCore3_mem_exactFamily3 hMK)
    (exactCore3_mem_exactFamily3 hMK') (isSectionMember3_exactCore3 hbK hc2 hMK.2)
    (isSectionMember3_exactCore3 hbK' hc2 hMK'.2)
    (isUniqueInvolution_of_le' hbU (mem_exactCore3 hbK hc2 hMK.2) (exactCore3_le_left c K))
    (isUniqueInvolution_of_le' hbU' (mem_exactCore3 hbK' hc2 hMK'.2) (exactCore3_le_left c K'))
    hB hbB hdB hcB hBgen hc1 hbc hd1 hdb hdsup

end Core

end CFSG.ClassicalInvolution.Q3.Q3T6D
