module

public import CFSG.ClassicalInvolution.Q3.Q3NHD4
public import CFSG.ClassicalInvolution.Q3.Q3NHDec
public import CFSG.ClassicalInvolution.Q3.Q3NMInner
public import CFSG.ClassicalInvolution.Q3.Q3NMAlpha
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwE6
public import CFSG.ClassicalInvolution.Q3.Q3NFMain
public import CFSG.ClassicalInvolution.Q3.Q3TIRed

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NH

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.Q3NF
  CFSG.ClassicalInvolution.Q3.Q3NM
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open scoped MatrixGroups commutatorElement


section Abstract

variable {X : Type} [Group X] {ι : Type} {Φ : Set (Subgroup X)}

theorem le_range_of_not_centralizes' (D : LieSystemData3 ι X Φ) {k : ι} {M : Subgroup X}
    (hM : M ∈ Φ) {m : X} (hm : m ∈ M) (hnc : ¬ ∀ q ∈ (D.hom k).range, m * q = q * m) :
    M ≤ (D.hom k).range := by
  obtain ⟨i, R, -, hMR⟩ := D.fundamental M hM
  have hik : i = k := by
    by_contra h
    refine hnc fun q hq => ?_
    rw [hMR] at hm
    obtain ⟨x, -, rfl⟩ := hm
    obtain ⟨y, rfl⟩ := hq
    exact D.commute i k h x y
  subst hik
  rw [hMR]
  exact Subgroup.map_le_range _ _

theorem exists_fund_of_le_range (D : LieSystemData3 ι X Φ) {k : ι} {M : Subgroup X} (hM : M ∈ Φ)
    (hMk : M ≤ (D.hom k).range) (hnc : ¬ M ≤ Subgroup.center X) :
    ∃ R ∈ (D.kind k).fund, M = R.map (D.hom k) := by
  obtain ⟨j, R, hR, hMR⟩ := D.fundamental M hM
  by_cases hjk : j = k
  · subst hjk
    exact ⟨R, hR, hMR⟩
  · exfalso
    apply hnc
    have h1 : M ≤ (D.hom j).range := hMR ▸ Subgroup.map_le_range _ _
    exact (le_inf hMk h1).trans (range_inf_range_le_center3 D (Ne.symm hjk))

end Abstract

section Normalizer

variable {X Yb : Type} [Group X] [Group Yb] {Φ : Set (Subgroup Yb)} {ι : Type}

theorem mem_normalizer_of_mem_range (D : LieSystemData3 ι Yb Φ) (θ : Yb →* X) (i : ι) {x : X}
    (hx : x ∈ θ.range) :
    x ∈ Subgroup.normalizer (((θ.comp (D.hom i)).range : Subgroup X) : Set X) := by
  obtain ⟨l, hl, hxl⟩ := exists_inner_of_mem_range D θ i hx
  obtain ⟨l', hl', hxl'⟩ := exists_inner_of_mem_range D θ i (inv_mem hx)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [hxl y hy]
    exact mul_mem (mul_mem hl hy) (inv_mem hl)
  · intro hy
    have h := hxl' _ hy
    have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rw [e] at h
    rw [h]
    exact mul_mem (mul_mem hl' hy) (inv_mem hl')

end Normalizer

section Rows

theorem autOddFreeInner_of_comp {t : StatedLieTag} {n : ℕ} (hrow : AutOddFreeInnerTag t n)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1) {c : CompData}
    (hc : c = CompData.model t n) {X : Type} [Group X] [Finite X] (ψ : c.G →* X)
    (hsurj : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center c.G) : AutOddFreeInner X := by
  subst hc
  exact hrow Nat.prime_three hfund hadm X ψ hsurj hker

theorem autOddFreeInnerTag_of_ne_D4 {t : StatedLieTag} {n : ℕ}
    (h4 : ¬ (t = .POmegaPlus ∧ n = 4)) (hadm : StatedLieAdmissible t n 3 1) :
    AutOddFreeInnerTag t n := by
  by_cases hT : t = .trialityD4
  · subst hT
    have hn : n = 0 := hadm.2.2
    subst hn
    exact autOddFreeInnerTag_trialityD4
  · exact autOddFreeInnerTag_of_not_D4 h4 hT

end Rows

section Vertex

variable {G : Type} [Group G] [Finite G]

structure VertexFrame3 (Φ : Set (Subgroup G)) (A : Subgroup G) (c : G) (K : Fin 3 → Subgroup G)
    (w : Fin 3 → G) : Prop where
  elem : IsElemAbelian 2 A
  cA : c ∈ A
  c1 : c ≠ 1
  AY : A ≤ centralizingLayer Φ {c}
  memA : ∀ i, w i ∈ A
  pair : ∀ p q : Fin 3, p ≠ q → PairData3 Φ A c (K p) (K q) (w p) (w q)
  indep : w 0 * w 1 ≠ w 2

theorem exists_two_ne {w : Fin 3 → G} {c : G} (hdist : ∀ i j : Fin 3, i ≠ j → w i ≠ w j) :
    ∃ p q : Fin 3, p ≠ q ∧ w p ≠ c ∧ w q ≠ c := by
  by_cases h0 : w 0 = c
  · exact ⟨1, 2, by decide, fun h => hdist 0 1 (by decide) (h0.trans h.symm),
      fun h => hdist 0 2 (by decide) (h0.trans h.symm)⟩
  by_cases h1 : w 1 = c
  · exact ⟨0, 2, by decide, h0, fun h => hdist 1 2 (by decide) (h1.trans h.symm)⟩
  · exact ⟨0, 1, by decide, h0, h1⟩

theorem exists_pair_prod_ne {w : Fin 3 → G} {c : G} (hdist : ∀ i j : Fin 3, i ≠ j → w i ≠ w j)
    (hsq : ∀ i, w i * w i = 1) (hcomm : ∀ i j, w i * w j = w j * w i)
    (hind : w 0 * w 1 ≠ w 2) :
    ∃ p r : Fin 3, p ≠ r ∧ w p ≠ c ∧ w r ≠ c ∧ w p * w r ≠ c := by
  have e02 : w 0 * w 2 ≠ w 1 := by
    intro h
    apply hind
    calc w 0 * w 1 = w 0 * (w 0 * w 2) := by rw [h]
      _ = w 2 := by rw [← mul_assoc, hsq 0, one_mul]
  have e12 : w 1 * w 2 ≠ w 0 := by
    intro h
    apply hind
    calc w 0 * w 1 = (w 1 * w 2) * w 1 := by rw [h]
      _ = w 2 := by rw [mul_assoc, hcomm 2 1, ← mul_assoc, hsq 1, one_mul]
  by_cases h0 : w 0 = c
  · exact ⟨1, 2, by decide, fun h => hdist 0 1 (by decide) (h0.trans h.symm),
      fun h => hdist 0 2 (by decide) (h0.trans h.symm), fun h => e12 (h.trans h0.symm)⟩
  by_cases h1 : w 1 = c
  · exact ⟨0, 2, by decide, h0, fun h => hdist 1 2 (by decide) (h1.trans h.symm),
      fun h => e02 (h.trans h1.symm)⟩
  by_cases h2 : w 2 = c
  · exact ⟨0, 1, by decide, h0, h1, fun h => hind (h.trans h2.symm)⟩
  by_cases h01 : w 0 * w 1 = c
  · refine ⟨0, 2, by decide, h0, h2, fun h => ?_⟩
    exact hdist 1 2 (by decide) (mul_left_cancel (h01.trans h.symm))
  · exact ⟨0, 1, by decide, h0, h1, h01⟩

theorem oddQuotMk_notMem_modOdd_zpowers {c w : G} (hc2 : c * c = 1) (hw2 : w * w = 1)
    (hw1 : w ≠ 1) (hwc : w ≠ c) (hcw : c * w = w * c)
    (hwC : w ∈ Subgroup.centralizer ({c} : Set G)) :
    oddQuotMk c ⟨w, hwC⟩ ∉ modOdd c (Subgroup.zpowers c) := by
  rintro ⟨k, hk, hkx⟩
  have hcC : c ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  rcases mem_zpowers_involution hc2 hk with h1 | h1
  · have hk1 : k = 1 := Subtype.ext h1
    rw [hk1, map_one] at hkx
    have := eq_one_of_oddQuotMk_eq_one (a := c) (x := ⟨w, hwC⟩)
      (Subtype.ext hw2) hkx.symm
    exact hw1 (congrArg Subtype.val this)
  · have hkc : k = ⟨c, hcC⟩ := Subtype.ext h1
    rw [hkc] at hkx
    have hprod : (⟨c, hcC⟩⁻¹ * ⟨w, hwC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) *
        (⟨c, hcC⟩⁻¹ * ⟨w, hwC⟩) = 1 := by
      apply Subtype.ext
      show (c⁻¹ * w) * (c⁻¹ * w) = 1
      have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
      rw [hci]
      calc c * w * (c * w) = c * (w * c) * w := by group
        _ = c * (c * w) * w := by rw [← hcw]
        _ = (c * c) * (w * w) := by group
        _ = 1 := by rw [hc2, hw2, one_mul]
    have h1' : oddQuotMk c (⟨c, hcC⟩⁻¹ * ⟨w, hwC⟩) = 1 := by
      rw [map_mul, map_inv, hkx, inv_mul_cancel]
    have := eq_one_of_oddQuotMk_eq_one (a := c) hprod h1'
    have h2 : (⟨c, hcC⟩⁻¹ * ⟨w, hwC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 := this
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h3
    have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
    rw [hci] at h3
    apply hwc
    calc w = c * (c * w) := by rw [← mul_assoc, hc2, one_mul]
      _ = c * 1 := by rw [h3]
      _ = c := mul_one c

end Vertex

section PairImages

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {A : Subgroup G} {a : G}
  {K K' : Subgroup G} {w w' : G}

theorem pairData3_mem_left (P : PairData3 Φ A a K K' w w') : w ∈ K := by
  obtain ⟨hz, hc⟩ := P.clsK
  exact Subgroup.mem_subgroupOf.mp hc.mem

theorem pairData3_mk_mem (P : PairData3 Φ A a K K' w w') :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {a})) ⟨w, P.clsK.1⟩ ∈
      modOddIn (centralizingLayer Φ {a}) K :=
  ⟨⟨w, P.clsK.1⟩, Subgroup.mem_subgroupOf.mpr (pairData3_mem_left P), rfl⟩

theorem pairData3_central_image (P : PairData3 Φ A a K K' w w') :
    ∀ y ∈ modOddIn (centralizingLayer Φ {a}) K,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {a})) ⟨w, P.clsK.1⟩ * y =
        y * QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {a}))
          ⟨w, P.clsK.1⟩ := by
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (P.central x (Subgroup.mem_subgroupOf.mp hx))

theorem pairData3_cross_image (P : PairData3 Φ A a K K' w w') :
    ∀ y ∈ modOddIn (centralizingLayer Φ {a}) K',
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {a})) ⟨w, P.clsK.1⟩ * y =
        y * QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {a}))
          ⟨w, P.clsK.1⟩ := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' := Subgroup.mem_subgroupOf.mp hx
  have h := (mk_comm_eq_iff P.clsK.1 x.2).mpr (by simpa [commutatorElement_def] using P.cross _ hx')
  exact h

theorem pairData3_image_sq (P : PairData3 Φ A a K K' w w') :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {a})) ⟨w, P.clsK.1⟩ *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {a}))
        ⟨w, P.clsK.1⟩ = 1 := by
  rw [← map_mul]
  have : (⟨w, P.clsK.1⟩ : ↥(centralizingLayer Φ {a})) * ⟨w, P.clsK.1⟩ = 1 := Subtype.ext P.sq
  rw [this, map_one]

theorem pairData3_image_ne_one (P : PairData3 Φ A a K K' w w') :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {a})) ⟨w, P.clsK.1⟩ ≠ 1 :=
  Q3Y.mk_ne_one_of_involution _ P.clsK.1 P.sq P.ne_one

theorem pairData3_image_ne (P : PairData3 Φ A a K K' w w') :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {a})) ⟨w, P.clsK.1⟩ ≠
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {a}))
        ⟨w', P.clsK'.1⟩ := by
  intro h
  have hwwY : w * w' ∈ centralizingLayer Φ {a} :=
    (centralizingLayer Φ {a}).mul_mem P.clsK.1 P.clsK'.1
  have hsqww : (w * w') * (w * w') = 1 := by
    calc (w * w') * (w * w') = w * (w' * w) * w' := by group
      _ = w * (w * w') * w' := by rw [← P.comm]
      _ = (w * w) * (w' * w') := by group
      _ = 1 := by rw [P.sq, P.sq', one_mul]
  have hww1 : w * w' ≠ 1 := fun h1 => P.ne (by
    have h' : w' = w⁻¹ := eq_inv_of_mul_eq_one_right h1
    exact (h'.trans (inv_eq_of_mul_eq_one_right P.sq)).symm)
  apply Q3Y.mk_ne_one_of_involution _ hwwY hsqww hww1
  have hmul : QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {a}))
      ⟨w * w', hwwY⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {a})) ⟨w, P.clsK.1⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {a}))
          ⟨w', P.clsK'.1⟩ := by
    rw [← map_mul]
    rfl
  rw [hmul, ← h, pairData3_image_sq P]

end PairImages

section Main

variable {G : Type} [Group G] [Finite G]

theorem hyp51At_of_vertexFrame {Φ : Set (Subgroup G)} {A : Subgroup G} {c : G}
    {K : Fin 3 → Subgroup G} {w : Fin 3 → G} (hΦ : SecData3 c Φ) {ι : Type}
    (D : LieSystemData3 ι (LocalQuot Φ c) (localFamily Φ c)) (V : VertexFrame3 Φ A c K w) :
    Asc77.Hyp51At A c := by
  classical
  have hN : NormalizesLayer Φ c := fun _ hn => mem_normalizer_centralizingLayer_of_secData hΦ hn
  have hθ : Function.Injective (sectionQuotientHom hN) := sectionQuotientHom_injective hN
  set θ := sectionQuotientHom hN with hθdef
  have partner : ∀ p : Fin 3, ∃ q : Fin 3, p ≠ q := by
    intro p
    fin_cases p
    exacts [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]
  have hdist : ∀ i j : Fin 3, i ≠ j → w i ≠ w j := fun i j h => (V.pair i j h).ne
  have hc2 : c * c = 1 := Q3C.elem_sq V.elem V.cA
  have hwC : ∀ i, w i ∈ Subgroup.centralizer ({c} : Set G) := fun i =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Q3C.elem_comm V.elem (V.memA i) V.cA)
  have hwY : ∀ i, w i ∈ centralizingLayer Φ {c} := fun i => V.AY (V.memA i)
  have hKΦ : ∀ p, K p ∈ centralizingMembers Φ {c} := fun p => by
    obtain ⟨q, hq⟩ := partner p
    exact (V.pair p q hq).memK
  have hKfam : ∀ p, modOddIn (centralizingLayer Φ {c}) (K p) ∈ localFamily Φ c := fun p =>
    ⟨(K p).subgroupOf _, ⟨K p, hKΦ p, le_centralizingLayer (hKΦ p), rfl⟩, rfl⟩
  have hw1 : ∀ i, w i ≠ 1 := fun i => by
    obtain ⟨q, hq⟩ := partner i
    exact (V.pair i q hq).ne_one
  have hwsq : ∀ i, w i * w i = 1 := fun i => by
    obtain ⟨q, hq⟩ := partner i
    exact (V.pair i q hq).sq
  let π := QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Φ {c}))
  let ζ : Fin 3 → OddQuot c := fun i => oddQuotMk c ⟨w i, hwC i⟩
  have hζθ : ∀ i, ζ i = θ (π ⟨w i, hwY i⟩) := fun i => rfl
  have hζmem : ∀ i, ζ i ∈ modOdd c A := fun i => oddQuotMk_mem_modOdd (V.memA i) (hwC i)
  have hζrange : ∀ i, ζ i ∈ θ.range := fun i => ⟨π ⟨w i, hwY i⟩, rfl⟩
  have hζnot : ∀ i, w i ≠ c → ζ i ∉ modOdd c (Subgroup.zpowers c) := fun i hi =>
    oddQuotMk_notMem_modOdd_zpowers hc2 (hwsq i) (hw1 i) hi
      (Q3C.elem_comm V.elem V.cA (V.memA i)) (hwC i)
  have claim : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → Asc77.MovedByAll A c L →
      ∃ k, L = (θ.comp (D.hom k)).range ∧ D.kind k ≠ CompData.sl23 ∧
        ∀ p, w p ≠ c → modOddIn (centralizingLayer Φ {c}) (K p) ≤ (D.hom k).range := by
    intro L hL hmov
    obtain ⟨p₀, -, -, hp₀, -⟩ := exists_two_ne (c := c) hdist
    obtain ⟨y₀, hy₀, hne₀⟩ := hmov (ζ p₀) (hζmem p₀) (hζnot p₀ hp₀)
    obtain ⟨k, hLk, hk⟩ := component_cases_exact hΦ hN D hL (hζrange p₀) hy₀ hne₀
    refine ⟨k, hLk, hk, fun p hp => ?_⟩
    obtain ⟨y, hy, hne⟩ := hmov (ζ p) (hζmem p) (hζnot p hp)
    rw [hLk] at hy
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨q, hq⟩ := partner p
    refine le_range_of_not_centralizes' D (hKfam p) (pairData3_mk_mem (V.pair p q hq)) ?_
    intro hall
    apply hne
    have h2 : θ (π ⟨w p, hwY p⟩) * θ (D.hom k a) = θ (D.hom k a) * θ (π ⟨w p, hwY p⟩) :=
      (map_mul θ _ _).symm.trans
        ((congrArg θ (hall (D.hom k a) ⟨a, rfl⟩)).trans (map_mul θ _ _))
    rw [hζθ p]
    exact h2
  refine ⟨fun L₁ L₂ h₁ h₂ m₁ m₂ => ?_, fun L hL hmL => ?_⟩
  ·
    obtain ⟨p, -, -, hp, -⟩ := exists_two_ne (c := c) hdist
    obtain ⟨k₁, e₁, -, s₁⟩ := claim L₁ h₁ m₁
    obtain ⟨k₂, e₂, -, s₂⟩ := claim L₂ h₂ m₂
    have hk : k₁ = k₂ := by
      by_contra hne
      exact localFamily_not_le_center hΦ (hKΦ p).1
        ((le_inf (s₁ p hp) (s₂ p hp)).trans (range_inf_range_le_center3 D hne))
    rw [e₁, e₂, hk]
  ·
    obtain ⟨k, hLk, hksl, hs⟩ := claim L hL hmL
    subst hLk
    rcases D.valid k with ⟨t, n, hfund, hadm, hc⟩ | hc | hc
    · by_cases hd4 : t = .POmegaPlus ∧ n = 4
      ·
        exfalso
        obtain ⟨rfl, rfl⟩ := hd4
        have hwcomm : ∀ i j, w i * w j = w j * w i := fun i j =>
          Q3C.elem_comm V.elem (V.memA i) (V.memA j)
        have hcw : ∀ i, c * w i = w i * c := fun i => Q3C.elem_comm V.elem V.cA (V.memA i)
        obtain ⟨p, r, hpr, hp, hr, hprc⟩ := exists_pair_prod_ne hdist hwsq hwcomm V.indep
        obtain ⟨R₁, hR₁, hK₁⟩ := exists_fund_of_le_range D (hKfam p) (hs p hp)
          (localFamily_not_le_center hΦ (hKΦ p).1)
        obtain ⟨R₂, hR₂, hK₂⟩ := exists_fund_of_le_range D (hKfam r) (hs r hr)
          (localFamily_not_le_center hΦ (hKΦ r).1)
        have P := V.pair p r hpr
        have P' := V.pair r p hpr.symm
        have hker : (θ.comp (D.hom k)).ker ≤ Subgroup.center (D.kind k).G := fun x hx => by
          apply D.ker_le_center k
          rw [MonoidHom.mem_ker] at hx ⊢
          exact hθ (hx.trans (map_one θ).symm)
        have hmap₁ : R₁.map (θ.comp (D.hom k)) =
            (modOddIn (centralizingLayer Φ {c}) (K p)).map θ := by
          rw [hK₁]
          exact (Subgroup.map_map _ _ _).symm
        have hmap₂ : R₂.map (θ.comp (D.hom k)) =
            (modOddIn (centralizingLayer Φ {c}) (K r)).map θ := by
          rw [hK₂]
          exact (Subgroup.map_map _ _ _).symm
        have hmem₁ : ζ p ∈ R₁.map (θ.comp (D.hom k)) := by
          rw [hmap₁, hζθ p]
          exact Subgroup.mem_map_of_mem θ (pairData3_mk_mem P)
        have hmem₂ : ζ r ∈ R₂.map (θ.comp (D.hom k)) := by
          rw [hmap₂, hζθ r]
          exact Subgroup.mem_map_of_mem θ (pairData3_mk_mem P')
        have hne₁ : ζ p ≠ 1 := fun h =>
          pairData3_image_ne_one P (hθ ((hζθ p).symm.trans (h.trans (map_one θ).symm)))
        have hne₂ : ζ r ≠ 1 := fun h =>
          pairData3_image_ne_one P' (hθ ((hζθ r).symm.trans (h.trans (map_one θ).symm)))
        have hz₁ : ∀ y ∈ R₁.map (θ.comp (D.hom k)), ζ p * y = y * ζ p := by
          rw [hmap₁]
          rintro _ ⟨y', hy', rfl⟩
          rw [hζθ p]
          exact (map_mul θ _ _).symm.trans
            ((congrArg θ (pairData3_central_image P y' hy')).trans (map_mul θ _ _))
        have hz₂ : ∀ y ∈ R₂.map (θ.comp (D.hom k)), ζ r * y = y * ζ r := by
          rw [hmap₂]
          rintro _ ⟨y', hy', rfl⟩
          rw [hζθ r]
          exact (map_mul θ _ _).symm.trans
            ((congrArg θ (pairData3_central_image P' y' hy')).trans (map_mul θ _ _))
        have hx : ∀ y ∈ R₁.map (θ.comp (D.hom k)), ζ r * y = y * ζ r := by
          rw [hmap₁]
          rintro _ ⟨y', hy', rfl⟩
          rw [hζθ r]
          exact (map_mul θ _ _).symm.trans
            ((congrArg θ (pairData3_cross_image P' y' hy')).trans (map_mul θ _ _))
        have hcent := d4_cross_pair_central_of_comp hc (θ.comp (D.hom k)) hker hR₁ hR₂ hmem₁
          hmem₂ hne₁ hne₂ hz₁ hz₂ hx
        have hCm : w p * w r ∈ Subgroup.centralizer ({c} : Set G) := mul_mem (hwC p) (hwC r)
        have hxA : ζ p * ζ r ∈ modOdd c A := (modOdd c A).mul_mem (hζmem p) (hζmem r)
        have hxnot : ζ p * ζ r ∉ modOdd c (Subgroup.zpowers c) := by
          have e : oddQuotMk c ⟨w p * w r, hCm⟩ = ζ p * ζ r := by
            rw [← map_mul]
            rfl
          rw [← e]
          refine oddQuotMk_notMem_modOdd_zpowers hc2 ?_ ?_ hprc ?_ hCm
          · calc (w p * w r) * (w p * w r) = w p * (w r * w p) * w r := by group
              _ = w p * (w p * w r) * w r := by rw [hwcomm r p]
              _ = (w p * w p) * (w r * w r) := by group
              _ = 1 := by rw [hwsq p, hwsq r, one_mul]
          · intro h1
            have h' : w r = (w p)⁻¹ := eq_inv_of_mul_eq_one_right h1
            exact hdist p r hpr ((inv_eq_of_mul_eq_one_right (hwsq p)).symm.trans h'.symm)
          · calc c * (w p * w r) = (c * w p) * w r := (mul_assoc _ _ _).symm
              _ = (w p * c) * w r := by rw [hcw p]
              _ = w p * (c * w r) := mul_assoc _ _ _
              _ = w p * (w r * c) := by rw [hcw r]
              _ = (w p * w r) * c := (mul_assoc _ _ _).symm
        obtain ⟨y, hy, hne⟩ := hmL _ hxA hxnot
        exact hne (hcent y hy)
      have hrow : AutOddFreeInnerTag t n := autOddFreeInnerTag_of_ne_D4 hd4 hadm
      have hker : (θ.comp (D.hom k)).rangeRestrict.ker ≤ Subgroup.center (D.kind k).G := by
        rw [MonoidHom.ker_rangeRestrict]
        intro x hx
        apply D.ker_le_center k
        rw [MonoidHom.mem_ker] at hx ⊢
        exact hθ (hx.trans (map_one θ).symm)
      have hAut : AutOddFreeInner ↥(θ.comp (D.hom k)).range :=
        autOddFreeInner_of_comp hrow hfund hadm hc (θ.comp (D.hom k)).rangeRestrict
          (θ.comp (D.hom k)).rangeRestrict_surjective hker
      have hBθ : ∀ b ∈ modOdd c A, b ∈ θ.range := by
        rintro b ⟨k', hk', rfl⟩
        exact ⟨π ⟨k', V.AY hk'⟩, rfl⟩
      have hbb : ∀ b ∈ modOdd c A, b * b = 1 := by
        rintro b ⟨k', hk', rfl⟩
        rw [← map_mul]
        have : k' * k' = 1 := Subtype.ext (Q3C.elem_sq V.elem hk')
        rw [this, map_one]
      have h2 : ∀ x ∈ Asc77.inducedImage (θ.comp (D.hom k)).range (modOdd c A), x * x = 1 := by
        intro x hx
        obtain ⟨n, hn, rfl⟩ := hx
        have hnn : n * n = 1 := Subtype.ext (hbb _ (Subgroup.mem_subgroupOf.mp hn))
        rw [← map_mul, hnn, map_one]
      have hne : ∃ x ∈ Asc77.inducedImage (θ.comp (D.hom k)).range (modOdd c A), x ≠ 1 := by
        obtain ⟨p₀, -, -, hp₀, -⟩ := exists_two_ne (c := c) hdist
        obtain ⟨y₀, hy₀, hne₀⟩ := hmL (ζ p₀) (hζmem p₀) (hζnot p₀ hp₀)
        have hn := mem_normalizer_of_mem_range D θ k (hζrange p₀)
        refine ⟨Asc77.toInducedAutOn (θ.comp (D.hom k)).range ⟨ζ p₀, hn⟩,
          ⟨⟨ζ p₀, hn⟩, Subgroup.mem_subgroupOf.mpr (hζmem p₀), rfl⟩, fun hx1 => hne₀ ?_⟩
        have h1 := congrArg (fun f : ↥(Asc77.inducedAutOn (θ.comp (D.hom k)).range) =>
          ((f : MulAut ↥(θ.comp (D.hom k)).range) ⟨y₀, hy₀⟩ : ↥(θ.comp (D.hom k)).range)) hx1
        have h3 : ζ p₀ * y₀ * (ζ p₀)⁻¹ = y₀ := congrArg Subtype.val h1
        calc ζ p₀ * y₀ = (ζ p₀ * y₀ * (ζ p₀)⁻¹) * ζ p₀ := by group
          _ = y₀ * ζ p₀ := by rw [h3]
      have hinn : ∀ x ∈ Asc77.inducedImage (θ.comp (D.hom k)).range (modOdd c A),
          ((x : ↥(Asc77.inducedAutOn (θ.comp (D.hom k)).range)) :
            MulAut ↥(θ.comp (D.hom k)).range) ∈ innSubgroup ↥(θ.comp (D.hom k)).range := by
        intro x hx
        obtain ⟨n, hn, rfl⟩ := hx
        obtain ⟨l, hl, hlx⟩ := exists_inner_of_mem_range D θ k
          (hBθ _ (Subgroup.mem_subgroupOf.mp hn))
        refine ⟨⟨l, hl⟩, ?_⟩
        ext y
        exact (hlx y y.2).symm
      exact alphaOf_inducedImage_eq_bot_of_inner _ _ hAut h2 hne hinn
    · exact absurd hc hksl
    · exfalso
      obtain ⟨p, q, hpq, hp, hq⟩ := exists_two_ne (c := c) hdist
      obtain ⟨R₁, hR₁, hK₁⟩ := exists_fund_of_le_range D (hKfam p) (hs p hp)
        (localFamily_not_le_center hΦ (hKΦ p).1)
      obtain ⟨R₂, hR₂, hK₂⟩ := exists_fund_of_le_range D (hKfam q) (hs q hq)
        (localFamily_not_le_center hΦ (hKΦ q).1)
      have P := V.pair p q hpq
      have P' := V.pair q p hpq.symm
      refine false_of_pair_m11_weak (D.hom k) (D.ker_le_center k) hc hR₁ hR₂
        (ζ := π ⟨w p, hwY p⟩) (ξ := π ⟨w q, hwY q⟩) ?_ ?_ (pairData3_image_sq P)
        (pairData3_image_sq P') (pairData3_image_ne_one P) (pairData3_image_ne_one P')
        (pairData3_image_ne P) ?_ ?_ ?_
      · rw [← hK₁]
        exact pairData3_mk_mem P
      · rw [← hK₂]
        exact pairData3_mk_mem P'
      · rw [← hK₁]
        exact pairData3_central_image P
      · rw [← hK₂]
        exact pairData3_central_image P'
      · rw [← hK₂]
        exact pairData3_cross_image P

end Main

end CFSG.ClassicalInvolution.Q3.Q3NH
