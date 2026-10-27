module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAltDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAltBar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAltImage
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step7a
public import CFSG.LocalAnalysis.ComponentClassification.TBLitSwap
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Tools

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.RowAlt

open CFSG Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem chevalleyOver_of_central (hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G))
    (htop : (GH74.GLS.oPrimeResidual 2 G).map (QuotientGroup.mk' (pPrimeCore 2 G)) = ⊤)
    {z : G} (hz : orderOf z = 2) {L : Subgroup G} (hLC : L ≤ centralizer {z})
    (hLs : (L.subgroupOf (centralizer {z})).IsSubnormal) (hzL : z ∈ L) {p : ℕ}
    (hM : IsMTypeSchur p ↥L) (hc : tildeHom G z = 1) :
    IsChevalleyOver p (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
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
  have hGq : IsQuasisimple (G ⧸ pPrimeCore 2 G) := LocalCores.isQuasisimple_of_mulEquiv e₁.symm hY.2
  have hGO : pPrimeCore 2 (G ⧸ pPrimeCore 2 G) ≠ ⊤ := by
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot 2]
    intro h
    have h1 : ρ z ∈ (⊥ : Subgroup (G ⧸ pPrimeCore 2 G)) := h ▸ mem_top _
    rw [mem_bot] at h1
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  rcases hM with ⟨hLq, hch, -, -⟩ | ⟨-, ⟨eL⟩⟩
  · rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hGq hsub with hL1 | hL1
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
  ·
    exfalso
    obtain ⟨eLb⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective (ρ.subgroupMap L)
      (MonoidHom.subgroupMap_surjective _ _) (not_two_dvd_card_ker_bar L)
    set e := eLb.symm.trans eL
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hGq hsub with hL1 | hL1
    · have : Group.IsPerfect (G ⧸ pPrimeCore 2 G) := hGq.1
      have : Group.IsPerfect ↥(L.map ρ) := Group.IsPerfect.ofSurjective
        (f := ((MulEquiv.subgroupCongr hL1).trans Subgroup.topEquiv).symm.toMonoidHom)
        (MulEquiv.surjective _)
      exact TBLit.not_isPerfect_sl2Three
        (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
    · obtain ⟨g, q, -, hq1, -⟩ := exists_slTwoThree_pair
      have hcomm : ∀ a b : ↥(L.map ρ) ⧸ pPrimeCore 2 ↥(L.map ρ), a * b = b * a := by
        intro a b
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (mem_center_iff.mp (hL1 b.2) a)
      have hqg : q * g = g * q := by
        obtain ⟨a, rfl⟩ := e.surjective q
        obtain ⟨b, rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, hcomm]
      rw [(commutatorElement_eq_one_iff_mul_comm).mpr hqg, one_pow] at hq1
      exact absurd hq1 (by decide)

theorem le_oPrimeResidual_of_isPerfect {L : Subgroup G} (hL : Group.IsPerfect ↥L) :
    L ≤ GH74.GLS.oPrimeResidual 2 G := by
  have htop := T23.oPrimeResidual_two_eq_top hL
  have hle : (GH74.GLS.oPrimeResidual 2 ↥L).map L.subtype ≤ GH74.GLS.oPrimeResidual 2 G := by
    unfold GH74.GLS.oPrimeResidual
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨y, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥L) ∈ GH74.GLS.oPrimeResidual 2 ↥L := htop ▸ mem_top _
  exact hle ⟨_, hmem, rfl⟩

theorem chevalleyOver_of_top {C : ℕ → (S : Type) → [Group S] → Prop}
    (hiso : ∀ (p : ℕ) (S S' : Type) [Group S] [Group S'], (S ≃* S') → C p S → C p S')
    (hcore : RowCore C) (hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G))
    (htop : (GH74.GLS.oPrimeResidual 2 G).map (QuotientGroup.mk' (pPrimeCore 2 G)) = ⊤)
    {z : G} (hz : orderOf z = 2) {L : Subgroup G} (hLC : L ≤ centralizer {z})
    (hLs : (L.subgroupOf (centralizer {z})).IsSubnormal) (hzL : z ∈ L) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hLq : IsTwoQuasisimple ↥L) (hM : IsMTypeSchur p ↥L)
    (hI : InductionTypeField p ↥L)
    (hC : C p (↥(GH74.GLS.oPrimeResidual 2 G) ⧸ Open.fusionZStar ↥(GH74.GLS.oPrimeResidual 2 G))) :
    IsChevalleyOver p (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
      pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := GH74.GLS.oPrimeResidual 2 G with hYdef
  by_cases hc : tildeHom G z = 1
  · exact chevalleyOver_of_central hY htop hz hLC hLs hzL hM hc
  exfalso
  obtain ⟨e₁⟩ := nonempty_bar_equiv htop
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥Y
  set Gb := G ⧸ pPrimeCore 2 G
  set Q := ↥Y ⧸ pPrimeCore 2 ↥Y
  let e₂ : Gb ⧸ center Gb ≃* Q ⧸ center Q :=
    QuotientGroup.congr _ _ e₁ (OuterAutomorphisms.center_map_equiv e₁)
  have hC₀ : C p (Gb ⧸ center Gb) := hiso p _ _ (e₂.trans eZ.symm).symm hC
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
  exact hcore (Gb ⧸ center Gb) hnonab p hp hp2 hC₀ t ht2 (L.map (tildeHom G)) hJC hJs htJ hJq
    ↥L hM hI ⟨eLJ⟩

theorem chevalleyOver_of_corePerfect {C : ℕ → (S : Type) → [Group S] → Prop}
    (hiso : ∀ (p : ℕ) (S S' : Type) [Group S] [Group S'], (S ≃* S') → C p S → C p S')
    (hcore : RowCore C) (hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G))
    {z : G} (hz : orderOf z = 2) {L : Subgroup G} (hLC : L ≤ centralizer {z})
    (hLs : (L.subgroupOf (centralizer {z})).IsSubnormal) (hzL : z ∈ L) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hLq : IsTwoQuasisimple ↥L) (hM : IsMTypeSchur p ↥L)
    (hI : InductionTypeField p ↥L)
    (hC : C p (↥(GH74.GLS.oPrimeResidual 2 G) ⧸ Open.fusionZStar ↥(GH74.GLS.oPrimeResidual 2 G))) :
    IsChevalleyOver p (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
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
  have hC' := hiso p _ _ eZ.symm hC
  let eL : ↥(L.subgroupOf Y) ≃* ↥L := subgroupOfEquivOfLe hLY
  have hM' : IsMTypeSchur p ↥(L.subgroupOf Y) := T23.isMTypeSchur_of_mulEquiv eL.symm hM
  have hI' : InductionTypeField p ↥(L.subgroupOf Y) := inductionTypeField_of_bar_equiv
    (QuotientGroup.congr _ _ eL.symm (pPrimeCore_map_iso 2 eL.symm)) hI
  have hz' : orderOf (⟨z, hzY⟩ : ↥Y) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have h := chevalleyOver_of_top hiso hcore hY' htop' hz' hJ'.1 hJ'.2.1 hzL hp hp2 hJ'.2.2 hM' hI'
    hC'
  exact T23.isChevalleyOver_of_mulEquiv (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)) h

theorem rowFor_of_core {C : ℕ → (S : Type) → [Group S] → Prop}
    (hiso : ∀ (p : ℕ) (S S' : Type) [Group S] [Group S'], (S ≃* S') → C p S → C p S')
    (hcore : RowCore C) : RowFor C := by
  intro G _ _ hY z hz L hL hzL p hp hp2 hM hI hC
  rcases hM with hM1 | ⟨-, ⟨eL⟩⟩
  · exact .inl (chevalleyOver_of_corePerfect hiso hcore hY hz hL.1 hL.2.1 hzL hp hp2 hM1.1
      (.inl hM1) hI hC)
  ·
    exfalso
    have : Group.IsPerfect ↥L := hL.2.2.1
    exact TBLit.not_isPerfect_sl2Three
      (Group.IsPerfect.ofSurjective (f := eL.toMonoidHom.comp (QuotientGroup.mk' _))
        (eL.surjective.comp (QuotientGroup.mk'_surjective _)))

theorem spor_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : Blueprint.NativeSporadic.SporadicRep S ∧
      ¬ Nonempty (S ≃* ↥Blueprint.NativeSporadic.M11)) :
    Blueprint.NativeSporadic.SporadicRep S' ∧
      ¬ Nonempty (S' ≃* ↥Blueprint.NativeSporadic.M11) := by
  obtain ⟨⟨s, ⟨eS⟩⟩, hM⟩ := h
  exact ⟨⟨s, ⟨e.symm.trans eS⟩⟩, fun ⟨eM⟩ => hM ⟨e.trans eM⟩⟩

theorem rowSpor_of_core
    (hcore : RowCore (fun _ S => Blueprint.NativeSporadic.SporadicRep S ∧
      ¬ Nonempty (S ≃* ↥Blueprint.NativeSporadic.M11))) : RowSpor :=
  rowFor_of_core (fun _ _ _ _ _ e h => spor_of_mulEquiv e h) hcore

end CFSG.ComponentClassification.HarrisLit.T1.RowAlt
