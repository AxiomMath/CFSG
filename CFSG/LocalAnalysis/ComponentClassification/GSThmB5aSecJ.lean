module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecImg
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalTools
import CFSG.Adapters.StatedPSLTwo

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace B5a

theorem center_eq_bot_of_equiv_alternating {G : Type*} [Group G] {n : ℕ} (hn : 4 ≤ n)
    (e : G ≃* alternatingGroup (Fin n)) : center G = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hcen : e y ∈ center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hy w]
  rw [alternatingGroup.center_eq_bot (by simpa using hn)] at hcen
  have : e y = e 1 := by rw [map_one]; exact mem_bot.mp hcen
  exact mem_bot.mpr (e.injective this)

theorem isSimpleGroup_of_lieModel_psl2 {X : Type} [Group X] {p f : ℕ}
    (hL : Blueprint.LieModel X .PSL 2 p f) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL

theorem center_eq_bot_of_isSimpleGroup' {G : Type*} [Group G] [IsSimpleGroup G]
    (hq : IsQuasisimple G) : center G = ⊥ := by
  rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hq
    apply hab
    have : Subsingleton (G ⧸ center G) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    exact Subsingleton.elim _ _

theorem center_eq_bot_of_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (hG : center G = ⊥) : center G' = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hcen : e.symm y ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hy (e z)
  rw [hG, mem_bot] at hcen
  rw [mem_bot, ← e.apply_symm_apply y, hcen, map_one]

end B5a

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

theorem secB0_le_P : h.secB0 y ≤ h.S ⊓ coreActionKernel h.J := (h.secB0_le_B y).trans h.B_le

theorem secJ0_sup_core :
    h.secJ0 y ⊔ oddCoreIn h.J = h.J ∧ oddCoreIn (h.secJ0 y) = h.secJ0 y ⊓ oddCoreIn h.J :=
  GSLit.fixedLayer_sup_pPrimeCore (B5a.isQuasisimple_J h) (secB0_le_P.trans inf_le_right)
    (h.isPGroup_secB0 y)

theorem nonempty_secJ0_equiv :
    Nonempty (↥(h.secJ0 y) ⧸ pPrimeCore 2 ↥(h.secJ0 y) ≃* ↥h.J ⧸ pPrimeCore 2 ↥h.J) := by
  obtain ⟨e, -⟩ := UnbalancedCorr.exists_quotient_equiv_of_sup
    ((GSLit.fixedLayer_le_inf h.J (h.secB0 y)).trans inf_le_left) secJ0_sup_core.1
    secJ0_sup_core.2
  exact ⟨e⟩

theorem isQuasisimple_secJ0 : IsQuasisimple (↥(h.secJ0 y) ⧸ pPrimeCore 2 ↥(h.secJ0 y)) := by
  obtain ⟨e⟩ := nonempty_secJ0_equiv (h := h) (y := y)
  exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 (B5a.isQuasisimple_J h)

theorem isPComponent_secJ0 : IsPComponent 2 ((h.secJ0 y).subgroupOf
    (centralizer ({h.a} : Set X) ⊓ centralizer (h.secB0 y : Set X))) := by
  obtain ⟨-, -, hs, -, -⟩ := id h.isPComponent_J
  exact GSLit.fixedLayer_isPComponent h.J_le hs
    (secB0_le_P.trans (inf_le_left.trans (h.S_le.trans inf_le_left)))
    (secB0_le_P.trans inf_le_right) (h.isPGroup_secB0 y) (B5a.isQuasisimple_J h)

theorem mem_coreActionKernel_secJ0 {g : X} (hgG : g ∈ h.secG0 y) (hgJ : g ∈ coreActionKernel h.J) :
    g ∈ coreActionKernel (h.secJ0 y) := by
  have hgN : g ∈ normalizer (h.J : Set X) := (mem_coreActionKernel.mp hgJ).1
  have hconj : conjugate (h.secJ0 y) g = h.secJ0 y := by
    change (GSLit.fixedLayer h.J (h.secB0 y)).map (MulAut.conj g⁻¹).toMonoidHom = _
    rw [GSLit.map_fixedLayer]
    change GSLit.fixedLayer (conjugate h.J g) (conjugate (h.secB0 y) g) = _
    rw [conjugate_eq_of_mem_normalizer hgN, conjugate_eq_of_mem_normalizer hgG]
  have hgN0 := mem_normalizer_of_conjugate_eq hconj
  refine mem_coreActionKernel.mpr ⟨hgN0, fun j hj => ?_⟩
  have hjJ : j ∈ h.J := ((GSLit.fixedLayer_le_inf h.J (h.secB0 y)).trans inf_le_left) hj
  have h1 : j⁻¹ * g⁻¹ * j * g ∈ oddCoreIn h.J := (mem_coreActionKernel.mp hgJ).2 j hjJ
  have h2 : j⁻¹ * g⁻¹ * j * g ∈ h.secJ0 y := by
    have h3 := (mem_normalizer_iff.mp (inv_mem hgN0) j).mp hj
    rw [inv_inv] at h3
    rw [show j⁻¹ * g⁻¹ * j * g = j⁻¹ * (g⁻¹ * j * g) by group]
    exact mul_mem (inv_mem hj) h3
  have h4 : j⁻¹ * g⁻¹ * j * g ∈ oddCoreIn (h.secJ0 y) := by
    rw [secJ0_sup_core.2]
    exact mem_inf.mpr ⟨h2, h1⟩
  exact h4

theorem nonempty_secJ_pPrimeCore_equiv (hZ : center (↥h.J ⧸ pPrimeCore 2 ↥h.J) = ⊥) :
    Nonempty (↥(h.secImage y (h.secJ0 y)) ⧸ pPrimeCore 2 ↥(h.secImage y (h.secJ0 y)) ≃*
      ↥h.J ⧸ pPrimeCore 2 ↥h.J) := by
  obtain ⟨e₀⟩ := nonempty_secJ0_equiv (h := h) (y := y)
  let e₁ : ↥((h.secJ0 y).subgroupOf (h.secG0 y)) ≃* ↥(h.secJ0 y) :=
    subgroupOfEquivOfLe (h.secJ0_le_G0 y)
  let e₂ := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₁
  have hZ' : center (↥((h.secJ0 y).subgroupOf (h.secG0 y)) ⧸
      pPrimeCore 2 ↥((h.secJ0 y).subgroupOf (h.secG0 y))) = ⊥ :=
    B5a.center_eq_bot_of_equiv (e₂.trans e₀).symm hZ
  obtain ⟨e₃⟩ := TwoQuot.nonempty_pPrimeCore_equiv_map (h.secMk y)
    (h.subgroupOf_le_centralizer_ker y ((h.secJ0_le y).trans inf_le_right))
    (h.isPGroup_ker_secMk y) hZ'
  exact ⟨e₃.symm.trans (e₂.trans e₀)⟩

theorem nonempty_secJ_fusionZStar_equiv :
    Nonempty (↥(h.secImage y (h.secJ0 y)) ⧸ Open.fusionZStar ↥(h.secImage y (h.secJ0 y)) ≃*
      ↥h.J ⧸ Open.fusionZStar ↥h.J) := by
  obtain ⟨e₀⟩ := nonempty_secJ0_equiv (h := h) (y := y)
  let e₁ : ↥((h.secJ0 y).subgroupOf (h.secG0 y)) ≃* ↥(h.secJ0 y) :=
    subgroupOfEquivOfLe (h.secJ0_le_G0 y)
  let e₂ := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₁
  have hq : IsQuasisimple (↥((h.secJ0 y).subgroupOf (h.secG0 y)) ⧸
      pPrimeCore 2 ↥((h.secJ0 y).subgroupOf (h.secG0 y))) :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr e₂).2 isQuasisimple_secJ0
  obtain ⟨e₃⟩ := TwoQuot.nonempty_fusionZStar_equiv_map (h.secMk y)
    (h.subgroupOf_le_centralizer_ker y ((h.secJ0_le y).trans inf_le_right)) hq
  obtain ⟨e₄⟩ := TwoQuot.nonempty_fusionZStar_equiv_of_pPrimeCore_equiv (e₂.trans e₀)
  exact ⟨e₃.symm.trans e₄⟩

theorem secMk_mem_normalizer {Y : Subgroup X} {g : X} (hg : g ∈ h.secG0 y)
    (hgN : g ∈ normalizer (Y : Set X)) :
    h.secMk y ⟨g, hg⟩ ∈ normalizer (h.secImage y Y : Set (h.secBar y)) := by
  apply mem_normalizer_of_conjugate_eq
  rw [← secImage_conjugate Y hg, conjugate_eq_of_mem_normalizer hgN]

theorem secMk_mem_centralizer {Y : Subgroup X} {g : X} (hg : g ∈ h.secG0 y)
    (hgC : g ∈ centralizer (Y : Set X)) :
    h.secMk y ⟨g, hg⟩ ∈ centralizer (h.secImage y Y : Set (h.secBar y)) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_iff.mp hgC z hz)

namespace SecCond

variable (hc : h.SecCond y)
include hc

abbrev secA : h.secBar y := h.secMk y ⟨h.a, hc.a_mem_G0⟩

abbrev secX : h.secBar y := h.secMk y ⟨y, hc.y_mem_G0⟩

theorem orderOf_secA : orderOf hc.secA = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [← map_pow]
    have h1 : (⟨h.a, hc.a_mem_G0⟩ : ↥(h.secG0 y)) ^ 2 = 1 := by
      apply Subtype.ext
      rw [coe_pow, ← h.orderOf_a, pow_orderOf_eq_one]
      rfl
    rw [h1, map_one]
  · intro h1
    apply h.a_not_mem_secB0 y
    have h2 : (⟨h.a, hc.a_mem_G0⟩ : ↥(h.secG0 y)) ∈ (h.secMk y).ker := h1
    rw [ker_secMk] at h2
    exact h2

theorem secJ_le : h.secImage y (h.secJ0 y) ≤ centralizer ({hc.secA} : Set (h.secBar y)) := by
  rintro _ ⟨j, hj, rfl⟩
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp ((mem_inf.mp (h.secJ0_le y hj)).1))

abbrev secYa : Subgroup X :=
  ((centralizer ({hc.secA} : Set (h.secBar y))).comap (h.secMk y)).map (h.secG0 y).subtype

theorem secImage_secYa : h.secImage y hc.secYa = centralizer ({hc.secA} : Set (h.secBar y)) := by
  show ((hc.secYa).subgroupOf (h.secG0 y)).map (h.secMk y) = _
  rw [show (hc.secYa).subgroupOf (h.secG0 y) =
      (centralizer ({hc.secA} : Set (h.secBar y))).comap (h.secMk y) from
    comap_map_eq_self_of_injective (h.secG0 y).subtype_injective _,
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

theorem secYa_le_G0 : hc.secYa ≤ h.secG0 y := map_subtype_le _

theorem centralizer_le_secYa :
    centralizer ({h.a} : Set X) ⊓ centralizer (h.secB0 y : Set X) ≤ hc.secYa := by
  intro g hg
  have hgG : g ∈ h.secG0 y := h.centralizer_le_G0 y (mem_inf.mp hg).2
  refine ⟨⟨g, hgG⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_comap, mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp hg).1)

theorem secYa_le_normalizer : hc.secYa ≤
    normalizer ((centralizer ({h.a} : Set X) ⊓ centralizer (h.secB0 y : Set X) :
      Subgroup X) : Set X) := by
  have key : ∀ g ∈ hc.secYa, ∀ c ∈ centralizer ({h.a} : Set X) ⊓
      centralizer (h.secB0 y : Set X), g * c * g⁻¹ ∈
        centralizer ({h.a} : Set X) ⊓ centralizer (h.secB0 y : Set X) := by
    intro g hg c hc'
    obtain ⟨g', hg', rfl⟩ := mem_map.mp hg
    obtain ⟨hca, hcB⟩ := mem_inf.mp hc'
    have hgB : (g' : X) ∈ normalizer (h.secB0 y : Set X) := g'.2
    refine mem_inf.mpr ⟨?_, ?_⟩
    ·
      have h1 : h.secMk y g'⁻¹ ∈ centralizer ({hc.secA} : Set (h.secBar y)) :=
        inv_mem (show h.secMk y g' ∈ centralizer ({hc.secA} : Set (h.secBar y)) from hg')
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at h1
      have h1' : h.secMk y (g'⁻¹ * ⟨h.a, hc.a_mem_G0⟩ * g') = h.secMk y ⟨h.a, hc.a_mem_G0⟩ := by
        rw [map_mul, h1, ← map_mul, inv_mul_cancel_right]
      have h2 : (h.a)⁻¹ * ((g' : X)⁻¹ * h.a * g') ∈ h.secB0 y := by
        have h3 : (⟨h.a, hc.a_mem_G0⟩ : ↥(h.secG0 y))⁻¹ * (g'⁻¹ * ⟨h.a, hc.a_mem_G0⟩ * g') ∈
            (h.secMk y).ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, h1', inv_mul_cancel]
        rw [ker_secMk, mem_subgroupOf] at h3
        simpa only [coe_mul, coe_inv] using h3
      have hcb : c * ((h.a)⁻¹ * ((g' : X)⁻¹ * h.a * g')) =
          ((h.a)⁻¹ * ((g' : X)⁻¹ * h.a * g')) * c :=
        (mem_centralizer_iff.mp hcB _ h2).symm
      have hca' : c * h.a = h.a * c := mem_centralizer_singleton_iff.mp hca
      rw [mem_centralizer_singleton_iff]
      have hcc : c * ((g' : X)⁻¹ * h.a * g') = ((g' : X)⁻¹ * h.a * g') * c := by
        have e1 : (g' : X)⁻¹ * h.a * g' = h.a * ((h.a)⁻¹ * ((g' : X)⁻¹ * h.a * g')) := by group
        rw [e1, ← mul_assoc, hca', mul_assoc, hcb, ← mul_assoc]
      calc (g' : X) * c * (g' : X)⁻¹ * h.a
          = (g' : X) * (c * ((g' : X)⁻¹ * h.a * g')) * (g' : X)⁻¹ := by group
        _ = (g' : X) * (((g' : X)⁻¹ * h.a * g') * c) * (g' : X)⁻¹ := by rw [hcc]
        _ = h.a * ((g' : X) * c * (g' : X)⁻¹) := by group
    · exact (B5a.mem_normalizer_centralizer hgB |> fun hN =>
        (mem_normalizer_iff.mp hN c).mp hcB)
  intro g hg
  rw [mem_normalizer_iff]
  intro c
  constructor
  · exact key g hg c
  · intro hc'
    have h1 := key g⁻¹ (inv_mem hg) _ hc'
    rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at h1

theorem isPComponent_secJ : IsPComponent 2 ((h.secImage y (h.secJ0 y)).subgroupOf
    (centralizer ({hc.secA} : Set (h.secBar y)))) := by
  set C₂ := centralizer ({h.a} : Set X) ⊓ centralizer (h.secB0 y : Set X) with hC₂
  have hC₂Y : C₂ ≤ hc.secYa := hc.centralizer_le_secYa
  have hn : (C₂.subgroupOf hc.secYa).Normal :=
    (normal_subgroupOf_iff_le_normalizer hC₂Y).mpr hc.secYa_le_normalizer
  have h1 := UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal (h.secJ0_le y) hC₂Y
    hn.isSubnormal isPComponent_secJ0
  have h2 := secImage_isPComponent ((h.secJ0_le y).trans hC₂Y) hc.secYa_le_G0
    ((h.secJ0_le y).trans inf_le_right) h1
  rwa [hc.secImage_secYa] at h2

omit hc in
theorem smallType_secJ : SmallType (h.secImage y (h.secJ0 y)) := by
  obtain ⟨e₂⟩ := nonempty_secJ_fusionZStar_equiv (h := h) (y := y)
  have hq := B5a.isQuasisimple_J h
  rcases h.smallType with ⟨⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, hpf, hm⟩ | hm
  · obtain ⟨e₁⟩ := nonempty_secJ_pPrimeCore_equiv (h := h) (y := y)
      (B5a.center_eq_bot_of_equiv_alternating (by norm_num) e)
    exact Or.inl ⟨e₁.trans e⟩
  · have : IsSimpleGroup (↥h.J ⧸ pPrimeCore 2 ↥h.J) := B5a.isSimpleGroup_of_lieModel_psl2 hm
    obtain ⟨e₁⟩ := nonempty_secJ_pPrimeCore_equiv (h := h) (y := y)
      (B5a.center_eq_bot_of_isSimpleGroup' hq)
    exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hpf, OddQuot.lieModel_of_equiv e₁.symm hm⟩)
  · exact Or.inr (Or.inr (OddQuot.lieModel_of_equiv e₂.symm hm))

theorem secS_le : h.secImage y h.S ≤ centralizer ({hc.secA} : Set (h.secBar y)) ⊓
    normalizer (h.secImage y (h.secJ0 y) : Set (h.secBar y)) := by
  rintro _ ⟨s, hs, rfl⟩
  have hs' : (s : X) ∈ h.S := hs
  obtain ⟨hsa, hsJ⟩ := mem_inf.mp (h.S_le hs')
  refine mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hsa)
  · have hconj : conjugate (h.secJ0 y) s = h.secJ0 y := by
      change (GSLit.fixedLayer h.J (h.secB0 y)).map (MulAut.conj (s : X)⁻¹).toMonoidHom = _
      rw [GSLit.map_fixedLayer]
      change GSLit.fixedLayer (conjugate h.J s) (conjugate (h.secB0 y) s) = _
      rw [conjugate_eq_of_mem_normalizer hsJ, conjugate_eq_of_mem_normalizer s.2]
    exact secMk_mem_normalizer s.2 (mem_normalizer_of_conjugate_eq hconj)

omit hc in
theorem secB_le : h.secImage y h.B ≤ h.secImage y h.S ⊓
    coreActionKernel (h.secImage y (h.secJ0 y)) := by
  refine le_inf (secImage_mono (h.B_le.trans inf_le_left)) ?_
  rintro _ ⟨b, hb, rfl⟩
  have hb' : (b : X) ∈ h.B := hb
  exact secMk_mem_coreActionKernel (h.secJ0_le_G0 y) b.2
    (mem_coreActionKernel_secJ0 b.2 (mem_inf.mp (h.B_le hb')).2)

theorem secB_ne_bot : h.secImage y h.B ≠ ⊥ := by
  intro hbot
  apply hc.secB0_ne_B
  apply le_antisymm (h.secB0_le_B y)
  intro b hb
  have h1 : h.secMk y ⟨b, hc.B_le_G0 hb⟩ ∈ h.secImage y h.B :=
    mem_map_of_mem _ (show (⟨b, hc.B_le_G0 hb⟩ : ↥(h.secG0 y)) ∈ h.B.subgroupOf (h.secG0 y)
      from hb)
  rw [hbot, mem_bot] at h1
  have h2 : (⟨b, hc.B_le_G0 hb⟩ : ↥(h.secG0 y)) ∈ (h.secMk y).ker := h1
  rw [ker_secMk] at h2
  exact h2

theorem secA_mem_normalizer : hc.secA ∈ normalizer (h.secImage y h.B : Set (h.secBar y)) :=
  secMk_mem_normalizer hc.a_mem_G0 h.a_mem_normalizer

theorem secX_mem : hc.secX ∈ h.secImage y h.S :=
  mem_map_of_mem _ (show (⟨y, hc.y_mem_G0⟩ : ↥(h.secG0 y)) ∈ h.S.subgroupOf (h.secG0 y) from
    hc.mem_S)

theorem secB_inf_conjugate : h.secImage y h.B ⊓ conjugate (h.secImage y h.B) hc.secX = ⊥ := by
  rw [← secImage_conjugate h.B hc.y_mem_G0, ← secImage_inf (le_refl _ |>.trans' (h.secB0_le_B y))]
  rw [eq_bot_iff]
  rintro _ ⟨b, hb, rfl⟩
  have h2 : b ∈ (h.secMk y).ker := by
    rw [ker_secMk]
    exact hb
  exact h2

theorem secX_sq_mem : hc.secX ^ 2 ∈ h.secImage y h.S ⊓
    coreActionKernel (h.secImage y (h.secJ0 y)) ⊓ normalizer (h.secImage y h.B : Set (h.secBar y))
    := by
  have hT := hc.sq_mem_T
  obtain ⟨⟨hS, hN⟩, ⟨-, hC⟩⟩ :=
    And.intro (mem_inf.mp (mem_inf.mp hT).1) (mem_inf.mp (mem_inf.mp hT).2)
  have hyG : y ^ 2 ∈ h.secG0 y := pow_mem hc.y_mem_G0 2
  have h1 : hc.secX ^ 2 = h.secMk y ⟨y ^ 2, hyG⟩ := by
    rw [← map_pow]
    rfl
  rw [h1]
  refine mem_inf.mpr ⟨mem_inf.mpr ⟨mem_map_of_mem _ (show (⟨y ^ 2, hyG⟩ : ↥(h.secG0 y)) ∈
    h.S.subgroupOf (h.secG0 y) from hS), secMk_mem_coreActionKernel (h.secJ0_le_G0 y) hyG
      (mem_coreActionKernel_secJ0 hyG hC)⟩, secMk_mem_normalizer hyG hN⟩

omit hc in
theorem kProper_secBar : Assembly.KProper Blueprint.Catalog (h.secBar y) :=
  CatalogueKProperOver.kProper_quotient (fun e h => SectionRank.catalog_of_mulEquiv e h)
    (LocalAnalysis.ComponentInitial.kProper_subgroup
      (fun e h => SectionRank.catalog_of_mulEquiv e h) h.kProper (h.secG0 y)) _

theorem normalizer_secB : normalizer (h.secImage y h.B : Set (h.secBar y)) =
    h.secImage y (normalizer (h.B : Set X)) :=
  normalizer_secImage (h.secB0_le_B y) hc.B_le_G0

theorem kGroup_normalizer_secB :
    SectionRank.IsKGroupCat ↥(normalizer (h.secImage y h.B : Set (h.secBar y))) := by
  let e : ↥((normalizer (h.B : Set X)).subgroupOf (h.secG0 y)) ≃*
      ↥((h.secG0 y).subgroupOf (normalizer (h.B : Set X))) :=
    { toFun := fun g => ⟨⟨g.1.1, g.2⟩, g.1.2⟩
      invFun := fun g => ⟨⟨g.1.1, g.2⟩, g.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have h1 : SectionRank.IsKGroupCat ↥((normalizer (h.B : Set X)).subgroupOf (h.secG0 y)) :=
    (h.kGroup_normalizer.subgroup _).of_mulEquiv e
  have h2 := OddQuot.isKGroupCat_of_surjective h1
    ((h.secMk y).subgroupMap ((normalizer (h.B : Set X)).subgroupOf (h.secG0 y)))
    ((h.secMk y).subgroupMap_surjective _)
  exact h2.of_mulEquiv (MulEquiv.subgroupCongr hc.normalizer_secB)

theorem normalizer_secB_ne_top : normalizer (h.secImage y h.B : Set (h.secBar y)) ≠ ⊤ := by
  intro htop
  have h1 : hc.secX ∈ normalizer (h.secImage y h.B : Set (h.secBar y)) := htop ▸ mem_top _
  rw [hc.normalizer_secB, secMk_mem_secImage_iff ((h.secB0_le_B y).trans le_normalizer)] at h1
  exact hc.y_not_mem_normalizer h1

end SecCond

end Hyp52

end CFSG.ComponentClassification.GSThmB
