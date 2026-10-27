module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAltReduce

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup Assembly.LowTwoRank RowAlt
open scoped MatrixGroups

@[expose] def PerfType3 (L : Type) [Group L] : Prop :=
  InductionTypeField 3 L ∨ ∃ (τ : StatedLieTag) (n : ℕ),
    Blueprint.LieModel (L ⧸ Open.fusionZStar L) τ n 3 1

@[expose] def RowCore3 (C : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) → C S →
    ∀ t : S, orderOf t = 2 → ∀ J : Subgroup S, J ≤ centralizer {t} →
    (J.subgroupOf (centralizer {t})).IsSubnormal → t ∈ J → IsTwoQuasisimple ↥J →
    ∀ (L : Type) [Group L] [Finite L], PerfType3 L →
      Nonempty (L ⧸ Open.fusionZStar L ≃* ↥J ⧸ Open.fusionZStar ↥J) → False

theorem PerfType3.isSimpleChevalleyOver {L : Type} [Group L] [Finite L] (h : PerfType3 L) :
    IsSimpleChevalleyOver 3 (L ⧸ Open.fusionZStar L) := by
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv L
  rcases h with ⟨f, hf, h⟩ | ⟨τ, n, hm⟩
  · rcases h with ⟨-, -, hm⟩ | ⟨-, -, hm⟩ | ⟨-, -, hm⟩ | ⟨-, -, hm⟩ | ⟨hev, hsl⟩
    · exact ⟨_, _, _, GSThmB.OddQuot.lieModel_of_equiv eZ.symm hm⟩
    · exact ⟨_, _, _, GSThmB.OddQuot.lieModel_of_equiv eZ.symm hm⟩
    · exact ⟨_, _, _, GSThmB.OddQuot.lieModel_of_equiv eZ.symm hm⟩
    · exact ⟨_, _, _, GSThmB.OddQuot.lieModel_of_equiv eZ.symm hm⟩
    · have hf2 : 2 ≤ f := by
        obtain ⟨k, hk⟩ := hev
        omega
      have h5 : 5 ≤ 3 ^ f :=
        le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) hf2)
      obtain ⟨-, -, hQm, -⟩ := Lemma47.sl2_facts Nat.prime_three (by norm_num) hf h5 hsl
      exact ⟨_, _, _, GSThmB.OddQuot.lieModel_of_equiv eZ.symm hQm⟩
  · exact ⟨τ, n, 1, hm⟩

theorem PerfType3.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : PerfType3 A) : PerfType3 B := by
  rcases h with h | ⟨τ, n, hm⟩
  · exact .inl (inductionTypeField_of_bar_equiv
      (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)) h)
  · obtain ⟨eZ⟩ := FooteLit.nonempty_quotient_fusionZStar_equiv e
    exact .inr ⟨τ, n, GSThmB.OddQuot.lieModel_of_equiv eZ hm⟩

variable {G : Type} [Group G] [Finite G]

theorem chevalleyOver_of_central3 (hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G))
    (htop : (GH74.GLS.oPrimeResidual 2 G).map (QuotientGroup.mk' (pPrimeCore 2 G)) = ⊤)
    {z : G} (hz : orderOf z = 2) {L : Subgroup G} (hLC : L ≤ centralizer {z})
    (hLs : (L.subgroupOf (centralizer {z})).IsSubnormal) (hzL : z ∈ L)
    (hLq : IsTwoQuasisimple ↥L) (hch : IsSimpleChevalleyOver 3 (↥L ⧸ Open.fusionZStar ↥L))
    (hc : tildeHom G z = 1) :
    IsChevalleyOver 3 (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
      pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := GH74.GLS.oPrimeResidual 2 G with hYdef
  set ρ := QuotientGroup.mk' (pPrimeCore 2 G) with hρ
  have htt : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hz2 : orderOf (ρ z) = 2 :=
    UnbalancedLayer.orderOf_mk_eq_two (odd_card_pPrimeCore_two G) hz
  have hcen := (tildeHom_eq_one_iff z).mp hc
  have hsub := isSubnormal_map_bar htt hLC hLs hcen
  obtain ⟨e₁⟩ := nonempty_bar_equiv htop
  have hGq : IsQuasisimple (G ⧸ pPrimeCore 2 G) :=
    LocalCores.isQuasisimple_of_mulEquiv e₁.symm hY.2
  have hGO : pPrimeCore 2 (G ⧸ pPrimeCore 2 G) ≠ ⊤ := by
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot 2]
    intro h
    have h1 : ρ z ∈ (⊥ : Subgroup (G ⧸ pPrimeCore 2 G)) := h ▸ mem_top _
    rw [mem_bot] at h1
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hGq hsub with hL1 | hL1
  ·
    have hsurj : ∀ {H : Subgroup G}, H.map ρ = ⊤ → Function.Surjective (ρ.comp H.subtype) := by
      intro H hH g
      obtain ⟨x, hx, rfl⟩ : g ∈ H.map ρ := hH ▸ mem_top g
      exact ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨-, ⟨eLG⟩⟩ := Q81.isTwoQuasisimple_of_surjective hLq _ (hsurj hL1) hGO
    obtain ⟨-, ⟨eYG⟩⟩ := Q81.isTwoQuasisimple_of_surjective hY _ (hsurj htop) hGO
    obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥Y
    obtain ⟨τ, n, f, hm⟩ := hch
    exact .inl ⟨hY.2, τ, n, f,
      GSThmB.OddQuot.lieModel_of_equiv ((eLG.trans eYG.symm).trans eZ) hm⟩
  ·
    exfalso
    have : Group.IsPerfect ↥L := hLq.1
    have hLbp : Group.IsPerfect ↥(L.map ρ) :=
      Group.IsPerfect.ofSurjective (f := ρ.subgroupMap L) (MonoidHom.subgroupMap_surjective _ _)
    have hcomm : ∀ x y : ↥(L.map ρ), x * y = y * x := fun x y =>
      Subtype.ext (mem_center_iff.mp (hL1 y.2) x)
    have := ProperComplete.subsingleton_of_isPerfect_of_comm hLbp hcomm
    have h1 : (⟨ρ z, mem_map_of_mem ρ hzL⟩ : ↥(L.map ρ)) = 1 := Subsingleton.elim _ _
    have h2 : ρ z = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)

theorem chevalleyOver_of_top3 {C : (S : Type) → [Group S] → Prop}
    (hiso : ∀ (S S' : Type) [Group S] [Group S'], (S ≃* S') → C S → C S')
    (hcore : RowCore3 C) (hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G))
    (htop : (GH74.GLS.oPrimeResidual 2 G).map (QuotientGroup.mk' (pPrimeCore 2 G)) = ⊤)
    {z : G} (hz : orderOf z = 2) {L : Subgroup G} (hLC : L ≤ centralizer {z})
    (hLs : (L.subgroupOf (centralizer {z})).IsSubnormal) (hzL : z ∈ L)
    (hLq : IsTwoQuasisimple ↥L) (hT : PerfType3 ↥L)
    (hC : C (↥(GH74.GLS.oPrimeResidual 2 G) ⧸ Open.fusionZStar ↥(GH74.GLS.oPrimeResidual 2 G))) :
    IsChevalleyOver 3 (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
      pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := GH74.GLS.oPrimeResidual 2 G with hYdef
  by_cases hc : tildeHom G z = 1
  · exact chevalleyOver_of_central3 hY htop hz hLC hLs hzL hLq hT.isSimpleChevalleyOver hc
  exfalso
  obtain ⟨e₁⟩ := nonempty_bar_equiv htop
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥Y
  set Gb := G ⧸ pPrimeCore 2 G
  set Q := ↥Y ⧸ pPrimeCore 2 ↥Y
  let e₂ : Gb ⧸ center Gb ≃* Q ⧸ center Q :=
    QuotientGroup.congr _ _ e₁ (OuterAutomorphisms.center_map_equiv e₁)
  have hC₀ : C (Gb ⧸ center Gb) := hiso _ _ (e₂.trans eZ.symm).symm hC
  have hQq : IsQuasisimple Q := hY.2
  have : IsSimpleGroup (Q ⧸ center Q) := hQq.2.1
  have : IsSimpleGroup (Gb ⧸ center Gb) := e₂.isSimpleGroup
  have hnonab : ∃ a b : Gb ⧸ center Gb, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hQq.2.2
    refine ⟨e₂.symm a, e₂.symm b, fun h => hab (e₂.symm.injective ?_)⟩
    rw [map_mul, map_mul, h]
  set t := tildeHom G z with htdef
  have htt : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [← map_pow, sq, htt, map_one]) hc
  obtain ⟨hJC, hJs⟩ := isSubnormal_map_tilde htt hLC hLs
  have htJ : t ∈ L.map (tildeHom G) := mem_map_of_mem _ hzL
  have hJO : pPrimeCore 2 ↥(L.map (tildeHom G)) ≠ ⊤ := by
    intro h
    have hmem : (⟨t, htJ⟩ : ↥(L.map (tildeHom G))) ∈ pPrimeCore 2 ↥(L.map (tildeHom G)) :=
      h ▸ mem_top _
    have h1 := Subgroup.orderOf_dvd_natCard _ hmem
    rw [Subgroup.orderOf_mk, ht2] at h1
    exact (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore_two _)) (even_iff_two_dvd.mpr h1)
  obtain ⟨hJq, ⟨eLJ⟩⟩ := Q81.isTwoQuasisimple_of_surjective hLq
    ((tildeHom G).subgroupMap L) (MonoidHom.subgroupMap_surjective _ _) hJO
  exact hcore (Gb ⧸ center Gb) hnonab hC₀ t ht2 (L.map (tildeHom G)) hJC hJs htJ hJq ↥L hT
    ⟨eLJ⟩

theorem chevalleyOver_of_corePerfect3 {C : (S : Type) → [Group S] → Prop}
    (hiso : ∀ (S S' : Type) [Group S] [Group S'], (S ≃* S') → C S → C S')
    (hcore : RowCore3 C) (hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G))
    {z : G} (hz : orderOf z = 2) {L : Subgroup G} (hLC : L ≤ centralizer {z})
    (hLs : (L.subgroupOf (centralizer {z})).IsSubnormal) (hzL : z ∈ L)
    (hLq : IsTwoQuasisimple ↥L) (hT : PerfType3 ↥L)
    (hC : C (↥(GH74.GLS.oPrimeResidual 2 G) ⧸ Open.fusionZStar ↥(GH74.GLS.oPrimeResidual 2 G))) :
    IsChevalleyOver 3 (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
      pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)) := by
  set Y := GH74.GLS.oPrimeResidual 2 G with hYdef
  have hLY : L ≤ Y := le_oPrimeResidual_of_isPerfect hLq.1
  have hzY : z ∈ Y := hLY hzL
  have hJ : IsTwoComponentIn L (Y ⊓ centralizer {z}) :=
    ⟨le_inf hLY hLC, L219.isSubnormal_subgroupOf_of_le inf_le_right hLs, hLq⟩
  have hJ' := isTwoComponentIn_subgroupOf_inf hzY hJ
  have htopY : GH74.GLS.oPrimeResidual 2 ↥Y = ⊤ := T23.oPrimeResidual_two_eq_top hY.1
  let e : ↥(GH74.GLS.oPrimeResidual 2 ↥Y) ≃* ↥Y :=
    (MulEquiv.subgroupCongr htopY).trans Subgroup.topEquiv
  have hY' : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 ↥Y) :=
    isTwoQuasisimple_of_mulEquiv e.symm hY
  have htop' : (GH74.GLS.oPrimeResidual 2 ↥Y).map (QuotientGroup.mk' (pPrimeCore 2 ↥Y)) = ⊤ := by
    rw [htopY]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  obtain ⟨eZ⟩ := FooteLit.nonempty_quotient_fusionZStar_equiv e
  have hC' := hiso _ _ eZ.symm hC
  let eL : ↥(L.subgroupOf Y) ≃* ↥L := subgroupOfEquivOfLe hLY
  have hz' : orderOf (⟨z, hzY⟩ : ↥Y) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have h := chevalleyOver_of_top3 hiso hcore hY' htop' hz' hJ'.1 hJ'.2.1 hzL hJ'.2.2
    (hT.of_mulEquiv eL.symm) hC'
  exact T23.isChevalleyOver_of_mulEquiv (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)) h

theorem rowFor3_of_core {C : (S : Type) → [Group S] → Prop}
    (hiso : ∀ (S S' : Type) [Group S] [Group S'], (S ≃* S') → C S → C S')
    (hcore : RowCore3 C) :
    ∀ (G : Type) [Group G] [Finite G], IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G) →
      ∀ z : G, orderOf z = 2 → ∀ L : Subgroup G, IsTwoComponentIn L (centralizer {z}) →
        z ∈ L → PerfType3 ↥L →
        C (↥(GH74.GLS.oPrimeResidual 2 G) ⧸ Open.fusionZStar ↥(GH74.GLS.oPrimeResidual 2 G)) →
          IsChevalleyOver 3 (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
              pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)) := by
  intro G _ _ hY z hz L hL hzL hT hC
  exact chevalleyOver_of_corePerfect3 hiso hcore hY hz hL.1 hL.2.1 hzL hL.2.2 hT hC

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
