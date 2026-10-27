module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalQuot
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalLevi
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LocalAnalysis.ComponentInitial.KProperSubgroup
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

@[expose] def Asc08Lemma310 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
    standardComponentOddCore G = ⊥ → Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin 5)) →
    Odd (Nat.card (center ↥A)) → ∀ R : Subgroup G, IsSylowOf 2 R (centralizer (A : Set G)) →
    (∀ x : G, ¬ rightConjugate R x ≤ A) →
      NativeSporadic.IsSporadic (rankTwoX A) .J2 ∨
        (NativeSporadic.IsSporadic (rankTwoX A) .M12 ∧
          ∃ t : G, t ^ 2 = 1 ∧ t ∈ normalizer (A : Set G) ∧ t ∈ normalizer (R : Set G) ∧
            ¬ ∃ a ∈ A, ∀ y ∈ A, t * y * t⁻¹ = a * y * a⁻¹)

section Abstract

variable {Q : Type} [Group Q] [Finite Q]

local notation "O" => standardComponentOddCore Q
local notation "π" => QuotientGroup.mk' (standardComponentOddCore Q)

theorem isSporadic_j2_of_standard (h5 : Asc08Lemma310) {M R : Subgroup Q} (hH : RankTwoHyp Q M)
    (hA5 : Nonempty (rankTwoQuot M ≃* alternatingGroup (Fin 5)))
    (hZ : Odd (Nat.card (center ↥M))) (hR : IsSylowOf 2 R (centralizer (M : Set Q)))
    (hno : ∀ x : Q, ¬ rightConjugate R x ≤ M)
    (hinner : ∀ b : Q, b ^ 2 = 1 → b ∈ normalizer (M : Set Q) → b ∈ normalizer (R : Set Q) →
      ∃ m ∈ M, ∀ y ∈ M, b * y * b⁻¹ = m * y * m⁻¹) :
    NativeSporadic.IsSporadic (rankTwoX (M.map π)) .J2 := by
  obtain ⟨e⟩ := hA5
  rcases h5 (Q ⧸ O) (M.map π) (rankTwoHyp_map hH) standardComponentOddCore_quotient_eq_bot
      ⟨(quotCenterMap hH).symm.trans e⟩ (odd_card_center_map hH hZ) (R.map π)
      (isSylowOf_map hH hR) (not_conj_le_map hH hR.isPGroup hno) with
    hJ | ⟨-, t, ht, htM, htR, hout⟩
  · exact hJ
  · exfalso
    obtain ⟨b, hb2, hbt, hbM, hbR⟩ := exists_lift hH hR.isPGroup ht htM htR
    obtain ⟨m, hm, hmb⟩ := hinner b hb2 hbM hbR
    apply hout
    refine ⟨π m, mem_map_of_mem _ hm, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [← hbt, ← map_inv, ← map_mul, ← map_mul, hmb y hy, map_mul, map_mul, map_inv]

end Abstract

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def conjAut {A : Subgroup G} {s : G} (hs : s ∈ normalizer (A : Set G)) :
    MulAut ↥A :=
  ((MulAut.conj s).subgroupMap A).trans
    (MulEquiv.subgroupCongr (mem_normalizer_iff_map_conj_eq.mp hs))

omit [Finite G] in
theorem conjAut_apply {A : Subgroup G} {s : G} (hs : s ∈ normalizer (A : Set G)) (x : ↥A) :
    ((conjAut hs x : ↥A) : G) = s * x * s⁻¹ :=
  rfl

omit [Finite G] in
theorem two_le_pRank_centralizer_subgroupOf' [Finite G] {A W L : Subgroup G} (hWA : W ≤ A)
    (hLA : L ≤ A) (hrank : 2 ≤ Open.pRank 2 (centralizer (A : Set G))) :
    2 ≤ Open.pRank 2 (centralizer ((L.subgroupOf (centralizer (W : Set G)) :
      Subgroup ↥(centralizer (W : Set G))) : Set ↥(centralizer (W : Set G)))) := by
  obtain ⟨U, hUK, hU, hU4⟩ := exists_four_le_of_two_le_pRank hrank
  have hUW : U ≤ centralizer (W : Set G) := hUK.trans (centralizer_le hWA)
  refine CFSG.SectionRank.le_pRank one_lt_two (E := U.subgroupOf (centralizer (W : Set G)))
    ?_ ?_ ?_
  · intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (mem_centralizer_iff.1 (hUK (mem_subgroupOf.1 hx)) y
      (hLA (mem_subgroupOf.1 hy)))
  · refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have h := congrArg Subtype.val (hU.1.is_comm.comm ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩)
      simpa using h
    · simpa using hU.2 _ hx
  · rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hU4]
    exact Nat.card_congr (subgroupOfEquivOfLe hUW).toEquiv

structure Cfg76 (A R Y L : Subgroup G) : Prop where
  hyp : AS76b.Hyp31 A
  kProper : Assembly.KProper Catalog G
  sylowR : IsSylowOf 2 R (centralizer (A : Set G))
  not_le : ∀ x : G, ¬ rightConjugate R x ≤ A
  Y_le : Y ≤ A
  L_le : L ≤ A ⊓ centralizer (Y : Set G)
  a5 : Nonempty (rankTwoQuot L ≃* alternatingGroup (Fin 5))
  oddCenter : Odd (Nat.card (center ↥L))
  standard : standardComponentIsStandard (L.subgroupOf (centralizer (Y : Set G)))
  not_normal : ¬ (L.subgroupOf (centralizer (Y : Set G))).Normal
  noInv : NoInvolutoryCentralizing A (Y ⊔ L)
  outerFree : ∀ σ : MulAut ↥A, σ * σ = 1 → (∀ y : ↥A, (y : G) ∈ Y → σ y = y) →
    ∃ l ∈ L, ∀ z : ↥A, (z : G) ∈ L → ((σ z : ↥A) : G) = l * z * l⁻¹

namespace Cfg76

variable {A R Y L : Subgroup G} (hc : Cfg76 A R Y L)
include hc

theorem L_le_A : L ≤ A := hc.L_le.trans inf_le_left

theorem L_le_centralizer : L ≤ centralizer (Y : Set G) := hc.L_le.trans inf_le_right

theorem R_le_centralizer_Y : R ≤ centralizer (Y : Set G) :=
  hc.sylowR.le.trans (centralizer_le hc.Y_le)

theorem R_le_centralizer_L : R ≤ centralizer (L : Set G) :=
  hc.sylowR.le.trans (centralizer_le hc.L_le_A)

theorem isSylowOf_inf : IsSylowOf 2 R (centralizer (Y : Set G) ⊓ centralizer (L : Set G)) := by
  refine Lemma37.isSylowOf_of_isSylowOf_inf_normalizer ?_
  refine isSylowOf_of_noInvolutory hc.hyp hc.sylowR hc.noInv
    (le_inf (le_inf hc.R_le_centralizer_Y hc.R_le_centralizer_L) le_normalizer) ?_ inf_le_right
  intro x hx
  obtain ⟨⟨hxY, hxL⟩, -⟩ := mem_inf.mp hx
  exact mem_centralizer_sup hxY hxL

theorem rank : 2 ≤ Open.pRank 2 (centralizer (A : Set G)) := hc.hyp.rank

theorem rankTwoHyp :
    RankTwoHyp ↥(centralizer (Y : Set G)) (L.subgroupOf (centralizer (Y : Set G))) :=
  ⟨LocalAnalysis.ComponentInitial.kProper_subgroup
      (fun e h => SectionRank.catalog_of_mulEquiv e h) hc.kProper _, hc.standard,
    hc.not_normal,
    two_le_pRank_centralizer_subgroupOf' hc.Y_le hc.L_le_A hc.rank⟩

theorem isSporadic_j2 (h5 : Asc08Lemma310) :
    NativeSporadic.IsSporadic (rankTwoX ((L.subgroupOf (centralizer (Y : Set G))).map
      (QuotientGroup.mk' (standardComponentOddCore ↥(centralizer (Y : Set G)))))) .J2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (Y : Set G) with hC
  have hLC : L ≤ C := hc.L_le_centralizer
  have hRC : R ≤ C := hc.R_le_centralizer_Y
  set e := subgroupOfEquivOfLe hLC
  obtain ⟨f⟩ := hc.a5
  refine isSporadic_j2_of_standard h5 (R := R.subgroupOf C) hc.rankTwoHyp
    ⟨(QuotientGroup.congr (center _) (center _) e (Subgroup.map_center_eq e)).trans f⟩ ?_ ?_ ?_ ?_
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hc.oddCenter
  · rw [Lemma37.centralizer_subgroupOf hLC,
      ← Subgroup.inf_subgroupOf_left (centralizer (L : Set G)) C,
      Lemma37.isSylowOf_subgroupOf_iff hRC inf_le_left]
    exact hc.isSylowOf_inf
  · intro x hle
    apply hc.not_le (x : G)
    intro r hr
    rw [mem_rightConjugate_iff] at hr
    have hrC : r ∈ C := by
      have h1 : (x : G) * r * (x : G)⁻¹ ∈ C := hRC hr
      have h2 : r = (x : G)⁻¹ * ((x : G) * r * (x : G)⁻¹) * (x : G) := by group
      rw [h2]
      exact mul_mem (mul_mem (inv_mem x.2) h1) x.2
    have h2 : (⟨r, hrC⟩ : ↥C) ∈ rightConjugate (R.subgroupOf C) x := by
      rw [mem_rightConjugate_iff, mem_subgroupOf]
      simpa using hr
    exact hc.L_le_A (mem_subgroupOf.mp (hle h2))
  · intro b hb2 _ hbR
    have hbR' : (b : G) ∈ normalizer (R : Set G) := by
      rw [← subgroupOf_normalizer_eq hRC] at hbR
      exact hbR
    have hbA : (b : G) ∈ normalizer (A : Set G) := by
      have h := Lemma36.normalizer_le hc.hyp hc.sylowR 1
      rw [rightConjugate_one, rightConjugate_one] at h
      exact h hbR'
    have h2 : (b : G) ^ 2 = 1 := by simpa using congrArg Subtype.val hb2
    have hσσ : conjAut hbA * conjAut hbA = 1 := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [MulAut.mul_apply, conjAut_apply, conjAut_apply, MulAut.one_apply]
      calc (b : G) * ((b : G) * x * (b : G)⁻¹) * (b : G)⁻¹ =
          (b : G) ^ 2 * x * ((b : G) ^ 2)⁻¹ := by rw [sq]; group
        _ = x := by rw [h2]; group
    obtain ⟨l, hl, hlσ⟩ := hc.outerFree _ hσσ fun y hy => Subtype.ext (by
      rw [conjAut_apply, ← mem_centralizer_iff.mp b.2 y hy, mul_inv_cancel_right])
    refine ⟨⟨l, hLC hl⟩, hl, fun y hy => Subtype.ext ?_⟩
    have h3 := hlσ ⟨y, hc.L_le_A (mem_subgroupOf.mp hy)⟩ (mem_subgroupOf.mp hy)
    rw [conjAut_apply] at h3
    simpa using h3

omit hc [Finite G] in
theorem conjAut_mul_conjAut {s : G} (hs : s ∈ normalizer (A : Set G)) :
    conjAut hs * conjAut (inv_mem hs) = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [MulAut.mul_apply, conjAut_apply, conjAut_apply, MulAut.one_apply]
  group

omit hc [Finite G] in
theorem conjAut_inv_mul_conjAut {s : G} (hs : s ∈ normalizer (A : Set G)) :
    conjAut (inv_mem hs) * conjAut hs = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [MulAut.mul_apply, conjAut_apply, conjAut_apply, MulAut.one_apply]
  group

theorem conj {s : G} (hs : s ∈ A) : Cfg76 A R (rightConjugate Y s) (rightConjugate L s) := by
  have hsN : s ∈ normalizer (A : Set G) := le_normalizer hs
  have hAs : rightConjugate A s = A := (rightConjugate_eq_self_iff A s).mpr hsN
  set e : ↥L ≃* ↥(rightConjugate L s) := (MulAut.conj s⁻¹).subgroupMap L
  have hCY : (centralizer (Y : Set G)).map (MulAut.conj s⁻¹).toMonoidHom =
      centralizer (rightConjugate Y s : Set G) := (AS76b.centralizer_rightConjugate Y s).symm
  set ψ : ↥(centralizer (Y : Set G)) ≃* ↥(centralizer (rightConjugate Y s : Set G)) :=
    ((MulAut.conj s⁻¹).subgroupMap _).trans (MulEquiv.subgroupCongr hCY)
  have hψ : ∀ x, ((ψ x : ↥(centralizer (rightConjugate Y s : Set G))) : G) = s⁻¹ * x * s := by
    intro x
    change MulAut.conj s⁻¹ (x : G) = _
    rw [MulAut.conj_apply, inv_inv]
  have hmap : (L.subgroupOf (centralizer (Y : Set G))).map ψ.toMonoidHom =
      (rightConjugate L s).subgroupOf (centralizer (rightConjugate Y s : Set G)) := by
    ext y
    rw [mem_subgroupOf, mem_rightConjugate_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hψ]
      simpa [mul_assoc] using mem_subgroupOf.mp hx
    · intro hy
      have hyC : s * (y : G) * s⁻¹ ∈ centralizer (Y : Set G) := by
        have h1 : (y : G) ∈ rightConjugate (centralizer (Y : Set G)) s := by
          rw [← AS76b.centralizer_rightConjugate]
          exact y.2
        exact (mem_rightConjugate_iff _ s y).mp h1
      refine ⟨⟨s * y * s⁻¹, hyC⟩, mem_subgroupOf.mpr hy, Subtype.ext ?_⟩
      rw [MulEquiv.coe_toMonoidHom, hψ]
      group
  set τ := conjAut (inv_mem hsN) with hτ
  set τ' := conjAut hsN with hτ'
  have hτx : ∀ x : ↥A, ((τ x : ↥A) : G) = s⁻¹ * x * s := by
    intro x
    rw [hτ, conjAut_apply, inv_inv]
  have hτ'x : ∀ x : ↥A, ((τ' x : ↥A) : G) = s * x * s⁻¹ := fun x => conjAut_apply hsN x
  have hτ'τ : τ' * τ = 1 := conjAut_mul_conjAut hsN
  have hττ' : τ * τ' = 1 := conjAut_inv_mul_conjAut hsN
  have hmemY : ∀ y : G, y ∈ Y → s⁻¹ * y * s ∈ rightConjugate Y s := fun y hy => by
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hy
  refine ⟨hc.hyp, hc.kProper, hc.sylowR, hc.not_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hAs]
    exact map_mono hc.Y_le
  · rw [AS76b.centralizer_rightConjugate]
    calc rightConjugate L s ≤ rightConjugate (A ⊓ centralizer (Y : Set G)) s := map_mono hc.L_le
      _ = rightConjugate A s ⊓ rightConjugate (centralizer (Y : Set G)) s :=
          map_inf_eq _ _ _ (MulAut.conj s⁻¹).injective
      _ = A ⊓ rightConjugate (centralizer (Y : Set G)) s := by rw [hAs]
  · obtain ⟨f⟩ := hc.a5
    exact ⟨(QuotientGroup.congr (center _) (center _) e (Subgroup.map_center_eq e)).symm.trans f⟩
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hc.oddCenter
  · rw [← hmap]
    exact standardComponentIsStandard_map_equiv ψ hc.standard
  · intro hn
    apply hc.not_normal
    have h1 := hn.comap ψ.toMonoidHom
    rwa [← hmap, comap_map_eq_self_of_injective ψ.injective] at h1
  · intro σ' hσ' hfix
    have hσ : τ' * σ' * τ * (τ' * σ' * τ) = 1 := by
      rw [show τ' * σ' * τ * (τ' * σ' * τ) = τ' * σ' * (τ * τ') * σ' * τ by group, hττ',
        mul_one, mul_assoc τ', hσ', mul_one, hτ'τ]
    have h1 := hc.noInv (τ' * σ' * τ) hσ fun x hx => by
      have hτx' : (τ x : G) ∈ rightConjugate Y s ⊔ rightConjugate L s := by
        have hsup : rightConjugate (Y ⊔ L) s = rightConjugate Y s ⊔ rightConjugate L s :=
          Subgroup.map_sup _ _ _
        rw [hτx, ← hsup, mem_rightConjugate_iff]
        simpa [mul_assoc] using hx
      rw [MulAut.mul_apply, MulAut.mul_apply, hfix _ hτx', ← MulAut.mul_apply, hτ'τ,
        MulAut.one_apply]
    calc σ' = τ * (τ' * σ' * τ) * τ' := by
          rw [show τ * (τ' * σ' * τ) * τ' = (τ * τ') * σ' * (τ * τ') by group, hττ', one_mul,
            mul_one]
      _ = 1 := by rw [h1, mul_one, hττ']
  · intro σ' hσ' hfix
    have hσ : τ' * σ' * τ * (τ' * σ' * τ) = 1 := by
      rw [show τ' * σ' * τ * (τ' * σ' * τ) = τ' * σ' * (τ * τ') * σ' * τ by group, hττ',
        mul_one, mul_assoc τ', hσ', mul_one, hτ'τ]
    obtain ⟨l, hl, hlσ⟩ := hc.outerFree (τ' * σ' * τ) hσ fun y hy => by
      rw [MulAut.mul_apply, MulAut.mul_apply, hfix _ (by rw [hτx]; exact hmemY y hy),
        ← MulAut.mul_apply, hτ'τ, MulAut.one_apply]
    refine ⟨s⁻¹ * l * s, by rw [mem_rightConjugate_iff]; simpa [mul_assoc] using hl, ?_⟩
    intro z hz
    have hz' : ((τ' z : ↥A) : G) ∈ L := by
      rw [hτ'x]
      exact (mem_rightConjugate_iff L s z).mp hz
    have h1 := hlσ (τ' z) hz'
    have hττ'z : ∀ w : ↥A, τ (τ' w) = w := fun w => by
      rw [← MulAut.mul_apply, hττ', MulAut.one_apply]
    have h2 : σ' z = τ ((τ' * σ' * τ) (τ' z)) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, hττ'z, hττ'z]
    rw [h2, hτx, h1, hτ'x]
    group

end Cfg76

theorem nonempty_equiv_a5_of_psl {X : Type} [Group X]
    (h : Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 2 2) :
    Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨f⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inl (by rw [hK]; norm_num))
  exact ⟨e.trans f⟩

end CFSG.ComponentClassification.RankTwoClassical
