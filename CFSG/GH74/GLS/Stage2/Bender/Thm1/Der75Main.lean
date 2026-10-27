module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der7
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der75Swap
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der75V7

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section MemOf

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

theorem mem_of_conj_of_commute (h72 : Lemma7_2) (h73 : Lemma7_3) (hC : Ctx6 G z k S M p)
    {Q V : Subgroup G} (hQ : QP z p (Op p M) Q) (hV : V7 z S V) {z' g : G}
    (hg : g * z * g⁻¹ = z') (hcomm : ∀ v ∈ V, z' * v = v * z') : g ∈ M := by
  have hCv : ∀ w ∈ V, w ≠ 1 → centralizer ({w} : Set G) ≤ M := h72 G z k S M p hC Q V hQ hV
  have hVle : V ≤ conjugate M g⁻¹ := by
    intro w hw
    rw [mem_conjugate_iff]
    have hwz : z' * w = w * z' := hcomm w hw
    have hz' : z = g⁻¹ * z' * g := by rw [← hg]; group
    refine hC.cen_le ?_
    rw [Subgroup.mem_centralizer_singleton_iff, hz']
    have e1 : g⁻¹ * z' * g * (g⁻¹ * w * g⁻¹⁻¹) = g⁻¹ * (z' * w) * g := by group
    have e2 : g⁻¹ * w * g⁻¹⁻¹ * (g⁻¹ * z' * g) = g⁻¹ * (w * z') * g := by group
    rw [e1, e2, hwz]
  have hgM : g⁻¹ ∈ M := h73 G z k S M p hC V hV.four hCv g⁻¹ hVle
  exact (Subgroup.inv_mem_iff M).mp hgM

theorem caseC_of_ne_m12 (h74 : Lemma7_4) (hC : Ctx6 G z k S M p) {Q V : Subgroup G}
    (hQ : QP z p (Op p M) Q) (hV : V7 z S V) (hk : k ≠ Kind.m12) : CaseC z S := by
  have hnc := lemma7_4_classes h74 hC hQ hV
  have hd := hC.ctx.data
  clear hC hQ hV
  cases hd with
  | g2 h => exact absurd h.one_class hnc
  | m12 h => exact absurd rfl hk
  | psp4 h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    obtain ⟨x, hx⟩ := h.two
    exact ⟨q, L₁, L₂, x, h.pair, hx⟩
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    rcases h.fusion with ⟨-, h1⟩ | ⟨-, x, hx, -⟩
    · exact absurd h1 hnc
    · exact ⟨q, L₁, L₂, x, h.pair, hx⟩
  | mcl h =>
    obtain ⟨n, -, h⟩ := h
    exact absurd h.one_class hnc
  | ly h =>
    obtain ⟨n, -, h⟩ := h
    exact absurd h.one_class hnc

end MemOf

section Pre

variable {G : Type} [Group G]

@[expose] def FstarPre (M : Subgroup G) : Subgroup G :=
  ((generalizedFitting (HBar M)).comap (QuotientGroup.mk' (pPrimeCore 2 ↥M))).map M.subtype

theorem FstarPre_le (M : Subgroup G) : FstarPre M ≤ M := Subgroup.map_subtype_le _

theorem mem_FstarPre {M : Subgroup G} {g : G} (hg : g ∈ M) :
    g ∈ FstarPre M ↔ QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨g, hg⟩ ∈ generalizedFitting (HBar M) := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact hm
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem FstarPre_conj {M : Subgroup G} {m g : G} (hm : m ∈ M) (hg : g ∈ FstarPre M) :
    m * g * m⁻¹ ∈ FstarPre M := by
  have hgM : g ∈ M := FstarPre_le M hg
  have hmgM : m * g * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hgM) (M.inv_mem hm)
  rw [mem_FstarPre hmgM]
  rw [mem_FstarPre hgM] at hg
  have hn : (generalizedFitting (HBar M)).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic).2
  have h1 := hn.conj_mem _ hg (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨m, hm⟩)
  have e : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨m * g * m⁻¹, hmgM⟩ =
      QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨m, hm⟩ * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨g, hgM⟩ *
        (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨m, hm⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e]
  exact h1

theorem le_FstarPre_of_barIn {M X : Subgroup G} (hX : X ≤ M)
    (h : barIn M X ≤ generalizedFitting (HBar M)) : X ≤ FstarPre M := by
  intro x hx
  have hxM : x ∈ M := hX hx
  rw [mem_FstarPre hxM]
  exact h ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem exists_not_mem_FstarPre {M X : Subgroup G}
    (h : ¬ barIn M X ≤ generalizedFitting (HBar M)) : ∃ x ∈ X, x ∉ FstarPre M := by
  by_contra hno
  push Not at hno
  apply h
  rintro _ ⟨⟨a, haM⟩, ha, rfl⟩
  exact (mem_FstarPre haM).mp (hno a (Subgroup.mem_subgroupOf.mp ha))

end Pre

section Pair

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem z_mem_LC_of_pair (hpair : Stage1Pair G z S q L₁ L₂) (hz : orderOf z = 2) : z ∈ LC z := by
  have hc := toBar_z_mem_center z
  have h1 : toBar z ⟨z, mem_Cen_self z⟩ ∈ generalizedFitting (CentralizerBar z) := by
    refine CFSG.centralizer_generalizedFitting_le (CentralizerBar z) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro f _
    exact Subgroup.mem_center_iff.mp hc f
  rw [hpair.fitting] at h1
  exact mem_LC_of_toBar_mem z (mem_Cen_self z) ⟨1, by simpa using hz⟩ h1

theorem exists_conj_mem_S {S : Subgroup G} (hSsyl : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z)) {w : G}
    (hwC : w ∈ Cen z) (hw2 : orderOf w = 2) : ∃ kk ∈ Cen z, kk⁻¹ * w * kk ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : IsPGroup 2 ↥(zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw2]; norm_num)
  have hW' : IsPGroup 2 ↥((zpowers w).subgroupOf (Cen z)) := hW2.comap_subtype
  obtain ⟨Q, hWQ⟩ := hW'.exists_le_sylow
  have hP' : CFSG.ABGLocalTools.IsSylowOf 2 ((Q : Subgroup ↥(Cen z)).map (Cen z).subtype) (Cen z) :=
    ⟨Q, rfl⟩
  obtain ⟨kk, hkk, hconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hSsyl hP'
  exact ⟨kk, hkk, (hconj w).mp ⟨⟨w, hwC⟩, hWQ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers w)), rfl⟩⟩

omit [Finite G] in
theorem orderOf_conj_eq (c w : G) : orderOf (c * w * c⁻¹) = orderOf w := by
  have h1 := MulEquiv.orderOf_eq (MulAut.conj c) w
  rwa [MulAut.conj_apply] at h1

end Pair

section CaseCEnd

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

theorem no_case_c (h72 : Lemma7_2) (h73 : Lemma7_3) (hC : Ctx6 G z k S M p) {Q : Subgroup G}
    (hQ : QP z p (Op p M) Q) (hcase : CaseC z S)
    (hM1 : barIn M (LC z) ≤ generalizedFitting (HBar M))
    (hM2 : ¬ barIn M S ≤ generalizedFitting (HBar M)) : False := by
  obtain ⟨q, L₁, L₂, x, hpair, htwo⟩ := hcase
  have ctx := hC.ctx
  have hSC : S ≤ Cen z := ctx.S_le_Cen
  have hCM : Cen z ≤ M := hC.cen_le
  have hLK : LC z ≤ FstarPre M := le_FstarPre_of_barIn ((LC_le_Cen z).trans hCM) hM1
  have hzK : z ∈ FstarPre M := hLK (z_mem_LC_of_pair hpair hC.orderOf_z)
  obtain ⟨a, haS, haK⟩ := exists_not_mem_FstarPre hM2
  obtain ⟨t₀, ht₀S, -, ht₀sw⟩ := htwo.swap_exists
  obtain ⟨s, hsS, hsK, hssw⟩ := exists_swapper_not_mem hpair hSC haS haK ht₀S ht₀sw
  obtain ⟨l, hl, hsl⟩ := htwo.coset s (Subgroup.mem_sup_right hsS)
  have hlK : l ∈ FstarPre M := hLK hl
  have hwC : s * l ∈ Cen z := Subgroup.mul_mem _ (hSC hsS) (LC_le_Cen z hl)
  have hwsw : Swaps z (s * l) L₁ L₂ := swaps_mul_LC hpair hssw hl
  have hwK : s * l ∉ FstarPre M := fun h => hsK (by
    have := (FstarPre M).mul_mem h ((FstarPre M).inv_mem hlK)
    simpa using this)
  have hw2 : orderOf (s * l) = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hsl
    rw [← hc, orderOf_conj_eq]
    exact hC.orderOf_z
  obtain ⟨kk, hkk, hyS⟩ := exists_conj_mem_S ctx.sylow hwC hw2
  have hyc : IsConj z (kk⁻¹ * (s * l) * kk) :=
    hsl.trans (isConj_iff.2 ⟨kk⁻¹, by group⟩)
  have hysw : Swaps z (kk⁻¹ * (s * l) * kk) L₁ L₂ := by
    have := swaps_conj hpair (Subgroup.inv_mem _ hkk) hwsw
    rwa [inv_inv] at this
  have hyK : kk⁻¹ * (s * l) * kk ∉ FstarPre M := fun h => hwK (by
    have := FstarPre_conj (hCM hkk) h
    have e : kk * (kk⁻¹ * (s * l) * kk) * kk⁻¹ = s * l := by group
    rwa [e] at this)
  obtain ⟨V, kk₂, hV, hkk₂, hy₂S, hy₂comm⟩ := v7_of_swap ctx hpair htwo hyS hyc hysw
  have hy₂c : IsConj z (kk₂⁻¹ * (kk⁻¹ * (s * l) * kk) * kk₂) :=
    hyc.trans (isConj_iff.2 ⟨kk₂⁻¹, by group⟩)
  have hy₂K : kk₂⁻¹ * (kk⁻¹ * (s * l) * kk) * kk₂ ∉ FstarPre M := fun h => hyK (by
    have := FstarPre_conj (hCM hkk₂) h
    have e : kk₂ * (kk₂⁻¹ * (kk⁻¹ * (s * l) * kk) * kk₂) * kk₂⁻¹ = kk⁻¹ * (s * l) * kk := by group
    rwa [e] at this)
  obtain ⟨g, hg⟩ := isConj_iff.1 hy₂c
  have hgM : g ∈ M := mem_of_conj_of_commute h72 h73 hC hQ hV hg hy₂comm
  apply hy₂K
  rw [← hg]
  exact FstarPre_conj hgM hzK

end CaseCEnd

section Lemma75

theorem lemma7_5_of (h72 : Lemma7_2) (h73 : Lemma7_3) (h34 : Leaf_Prop34) : Lemma7_5 := by
  have h74 : Lemma7_4 := lemma7_4_of h72 h73 h34
  intro G _ _ z k S M p hC Q V hQ hV
  by_contra hk
  have hcase : CaseC z S := caseC_of_ne_m12 h74 hC hQ hV hk
  obtain ⟨-, z', hz'S, hz'c, hz'ne, hz'V⟩ := hV.caseC hcase
  obtain ⟨g, hg⟩ := isConj_iff.mp hz'c
  have hgM : g ∈ M := mem_of_conj_of_commute h72 h73 hC hQ hV hg hz'V
  have hz'C : z' ∈ Cen z := hC.ctx.S_le_Cen hz'S
  have hz'2 : orderOf z' = 2 := by
    rw [← hg, orderOf_conj_eq]
    exact hC.orderOf_z
  rcases h34 G z k S hC.ctx M hC.cen_le hC.coatom.1 with
    hcov | hd | ⟨ε, q, L₁, L₂, hk', hL4, -, -, -, -, hM1, hM2, -⟩
  · exact not_cover_of_conj hC.orderOf_z hC.cen_le hz'C hz'2 hz'ne hg hgM hcov
  · exact CFSG.GH74.GLS.Stage2.Final.Thm4.not_isDihedral_S hC.ctx hd
  · exact no_case_c h72 h73 hC hQ hcase hM1 hM2

end Lemma75

end CFSG.GH74.GLS.Stage2.Bender.Thm1
