module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Twist
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddEllBasic
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddEllDef

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Frame

variable {L : Type} [Field L]

structure EllFrame (F : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L) (e : ℤ) : Prop where
  torus : ∀ t ∈ torusGroup TwistTag.D4.tag L, F t ∈ torusGroup TwistTag.D4.tag L
  rootSpan : ∀ q ∈ rootSpan TwistTag.D4.tag L d4LongA2, F q ∈ rootSpan TwistTag.D4.tag L d4LongA2
  diagram : F (diagramMap TwistTag.D4 L) = diagramMap TwistTag.D4 L
  torusPow : ∀ ν : Fin TwistTag.D4.tag.rank → Lˣ, (∀ i, ν (TwistTag.D4.perm i) = ν i) →
    F (rootDiagUnit TwistTag.D4.tag ν) = rootDiagUnit TwistTag.D4.tag (ν ^ e)
  exp : e ≠ 1

theorem EllFrame.leviGroup {F : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L} {e : ℤ}
    (hF : EllFrame F e) {g : ModGL TwistTag.D4.tag L} (hg : g ∈ leviGroup L) :
    F g ∈ leviGroup L := by
  obtain ⟨t, ht, q, hq, rfl⟩ := mem_leviGroup.1 hg
  rw [map_mul]
  exact mul_mem (torus_le_leviGroup (hF.torus t ht)) (rootSpan_le_leviGroup (hF.rootSpan q hq))

theorem exists_zpow_root [IsAlgClosed L] {m : ℤ} (hm : m ≠ 0) (x : Lˣ) :
    ∃ r : Lˣ, r ^ m = x := by
  have key : ∀ (k : ℕ), 0 < k → ∀ x : Lˣ, ∃ r : Lˣ, r ^ k = x := by
    intro k hk x
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : L) hk
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact x.ne_zero (by rw [← hz]; simp [hk.ne'])
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  rcases lt_or_gt_of_ne hm with h | h
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = -(k : ℤ) := ⟨(-m).toNat, by omega⟩
    obtain ⟨r, hr⟩ := key k (by omega) x⁻¹
    refine ⟨r, ?_⟩
    rw [hk, zpow_neg, zpow_natCast, hr, inv_inv]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = (k : ℤ) := ⟨m.toNat, by omega⟩
    obtain ⟨r, hr⟩ := key k (by omega) x
    exact ⟨r, by rw [hk, zpow_natCast, hr]⟩

end Frame

section Zeta

variable {L : Type} [Field L] [IsAlgClosed L]

@[expose] def tup1 (b : Lˣ) : Fin TwistTag.D4.tag.rank → Lˣ := ![1, 1, b, 1]

theorem rotElt_eq (b : Lˣ) :
    rotElt b = rootDiagUnit TwistTag.D4.tag (tup1 b) * (diagramMap TwistTag.D4 L)⁻¹ := rfl

theorem tup1_perm (b : Lˣ) (i : Fin TwistTag.D4.tag.rank) :
    tup1 b (TwistTag.D4.perm i) = tup1 b i := by
  fin_cases i <;> rfl

theorem rootChar_tup1 {b : Lˣ} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    ∀ α ∈ d4LongA2, rootChar (tup1 b) α ≠ 1 ∧ rootChar (tup1 b) α ^ 3 = 1 := by
  have hb2 : b ^ 2 ≠ 1 := fun h => hb1 (by
    have : b = b ^ 3 * (b ^ 2)⁻¹ := by group
    rw [this, hb3, h]; group)
  have hc : ∀ x c : ℤ, rootChar (tup1 b) (d4LongVec x c) = b ^ c := by
    intro x c
    rw [rootChar_d4_apply]
    simp [d4LongVec, tup1]
  intro α hα
  rw [d4LongA2_eq] at hα
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
  have hgen : ∀ c : ℤ, (c = 1 ∨ c = 2 ∨ c = -1 ∨ c = -2) → b ^ c ≠ 1 ∧ (b ^ c) ^ 3 = 1 := by
    intro c hc'
    refine ⟨?_, ?_⟩
    · rcases hc' with rfl | rfl | rfl | rfl
      · simpa using hb1
      · simpa using hb2
      · simpa using hb1
      · simpa [zpow_neg] using hb2
    · have : (b ^ c) ^ 3 = (b ^ 3) ^ c := by
        rw [← zpow_natCast, ← zpow_natCast b 3, ← zpow_mul, ← zpow_mul, mul_comm]
      rw [this, hb3, one_zpow]
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hc]; exact hgen 1 (by simp)
  · rw [hc]; exact hgen 1 (by simp)
  · rw [hc]; exact hgen 2 (by simp)
  · rw [hc]; exact hgen (-1) (by simp)
  · rw [hc]; exact hgen (-1) (by simp)
  · rw [hc]; exact hgen (-2) (by simp)

theorem diagramMap_inv_mul_rootDiagUnit (w : Fin TwistTag.D4.tag.rank → Lˣ) :
    (diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag w =
      rootDiagUnit TwistTag.D4.tag (fun i => w (TwistTag.D4.perm i)) *
        (diagramMap TwistTag.D4 L)⁻¹ := by
  calc (diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag w =
      ((diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag w *
        diagramMap TwistTag.D4 L) * (diagramMap TwistTag.D4 L)⁻¹ := by group
    _ = _ := by rw [d4Minus_h90_conj]

theorem diagramMap_inv_mul_of_mem_rootSpan {q : ModGL TwistTag.D4.tag L}
    (hq : q ∈ rootSpan TwistTag.D4.tag L d4LongA2) :
    (diagramMap TwistTag.D4 L)⁻¹ * q = q * (diagramMap TwistTag.D4 L)⁻¹ := by
  have h : diagramMap TwistTag.D4 L * q = q * diagramMap TwistTag.D4 L :=
    diagramMap_commute_of_mem_rootSpan hq
  have h2 : Commute q (diagramMap TwistTag.D4 L)⁻¹ := (Commute.symm (show Commute _ q from h)).inv_right
  exact h2.symm.eq

theorem ell_zeta_classify {b : Lˣ} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    {t q : ModGL TwistTag.D4.tag L} (ht : t ∈ torusGroup TwistTag.D4.tag L)
    (hq : q ∈ rootSpan TwistTag.D4.tag L d4LongA2)
    (hcomm : (t * q) * rotElt b = rotElt b * (t * q)) :
    ∃ hm : t * q ∈ monomialSubgroup TwistTag.D4.tag L,
      t * q ∈ torusGroup TwistTag.D4.tag L ∨
        ((∀ x, weylQuotientHom TwistTag.D4.tag L ⟨t * q, hm⟩ • x = d4MatThreeA *ᵥ x) ∨
          (∀ x, weylQuotientHom TwistTag.D4.tag L ⟨t * q, hm⟩ • x = d4MatThreeB *ᵥ x)) := by
  set P := diagramMap TwistTag.D4 L with hP
  obtain ⟨τ, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hPq : P⁻¹ * q = q * P⁻¹ := diagramMap_inv_mul_of_mem_rootSpan hq
  rw [rotElt_eq] at hcomm
  have h2 : rootDiagUnit TwistTag.D4.tag τ * q * rootDiagUnit TwistTag.D4.tag (tup1 b) =
      rootDiagUnit TwistTag.D4.tag (tup1 b) *
        rootDiagUnit TwistTag.D4.tag (fun i => τ (TwistTag.D4.perm i)) * q := by
    refine mul_right_cancel (b := P⁻¹) ?_
    calc rootDiagUnit TwistTag.D4.tag τ * q * rootDiagUnit TwistTag.D4.tag (tup1 b) * P⁻¹
        = rootDiagUnit TwistTag.D4.tag τ * q * (rootDiagUnit TwistTag.D4.tag (tup1 b) * P⁻¹) := by
          group
      _ = rootDiagUnit TwistTag.D4.tag (tup1 b) * P⁻¹ * (rootDiagUnit TwistTag.D4.tag τ * q) :=
          hcomm
      _ = rootDiagUnit TwistTag.D4.tag (tup1 b) * (P⁻¹ * rootDiagUnit TwistTag.D4.tag τ) * q := by
          group
      _ = _ := by
          rw [diagramMap_inv_mul_rootDiagUnit]
          calc rootDiagUnit TwistTag.D4.tag (tup1 b) *
              (rootDiagUnit TwistTag.D4.tag (fun i => τ (TwistTag.D4.perm i)) * P⁻¹) * q
              = rootDiagUnit TwistTag.D4.tag (tup1 b) *
                rootDiagUnit TwistTag.D4.tag (fun i => τ (TwistTag.D4.perm i)) * (P⁻¹ * q) := by
                group
            _ = _ := by rw [hPq]; group
  have hconj : q * rootDiagUnit TwistTag.D4.tag (tup1 b) * q⁻¹ =
      rootDiagUnit TwistTag.D4.tag (τ⁻¹ * tup1 b * fun i => τ (TwistTag.D4.perm i)) := by
    rw [rootDiagUnit_mul, rootDiagUnit_mul, ← rootDiagUnit_inv]
    calc q * rootDiagUnit TwistTag.D4.tag (tup1 b) * q⁻¹ =
        (rootDiagUnit TwistTag.D4.tag τ)⁻¹ * (rootDiagUnit TwistTag.D4.tag τ * q *
          rootDiagUnit TwistTag.D4.tag (tup1 b)) * q⁻¹ := by group
      _ = _ := by rw [h2]; group
  have hsame : ∀ α ∈ d4LongA2,
      rootChar (τ⁻¹ * tup1 b * fun i => τ (TwistTag.D4.perm i)) α = rootChar (tup1 b) α := by
    intro α hα
    rw [CTTorus.rootChar_mul, CTTorus.rootChar_mul, ← rootChar_permLattice τ TwistTag.D4.perm α,
      permLattice_d4LongA2_fixed hα, rootChar_inv_apply]
    rw [mul_comm (rootChar τ α)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  obtain ⟨hm, hcls, hiff⟩ := d4_A2_conj_monomial q hq (tup1 b) _ (rootChar_tup1 hb3 hb1) hsame hconj
  have hmt : rootDiagUnit TwistTag.D4.tag τ ∈ monomialSubgroup TwistTag.D4.tag L :=
    torusGroup_le_monomialSubgroup ht
  refine ⟨mul_mem hmt hm, ?_⟩
  have e : (⟨rootDiagUnit TwistTag.D4.tag τ * q, mul_mem hmt hm⟩ :
      monomialSubgroup TwistTag.D4.tag L) = ⟨_, hmt⟩ * ⟨q, hm⟩ := rfl
  have hw : weylQuotientHom TwistTag.D4.tag L ⟨rootDiagUnit TwistTag.D4.tag τ * q, mul_mem hmt hm⟩ =
      weylQuotientHom TwistTag.D4.tag L ⟨q, hm⟩ := by
    rw [e, map_mul, mp_image_torus ht, one_mul]
  rcases hcls with h1 | hA | hB
  · exact Or.inl (mul_mem ht (hiff.2 h1))
  · exact Or.inr (Or.inl fun x => by rw [hw]; exact hA x)
  · exact Or.inr (Or.inr fun x => by rw [hw]; exact hB x)

theorem leviGroup_le_adjointGroup {g : ModGL TwistTag.D4.tag L} (hg : g ∈ leviGroup L) :
    g ∈ adjointGroup TwistTag.D4.tag L := by
  obtain ⟨t, ht, q, hq, rfl⟩ := mem_leviGroup.1 hg
  exact mul_mem (torusGroup_le_adjointGroup' ht) (rootSpan_le_adjointGroup L d4LongA2 hq)

theorem EllFrame.rotElt {F : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L} {e : ℤ}
    (hF : EllFrame F e) {b : Lˣ} (hbe : b ^ e = b) : F (rotElt b) = rotElt b := by
  rw [rotElt_eq, map_mul, map_inv, hF.diagram, hF.torusPow _ (tup1_perm b)]
  congr 2
  funext i
  fin_cases i
  · exact one_zpow e
  · exact one_zpow e
  · exact hbe
  · exact one_zpow e

theorem ell_lang_torus {F : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L} {e : ℤ}
    (hF : EllFrame F e) (b : Lˣ) {ζ : ModGL TwistTag.D4.tag L}
    (hζT : ζ ∈ torusGroup TwistTag.D4.tag L) (hcomm : ζ * rotElt b = rotElt b * ζ) :
    ∃ z ∈ graphCentralizer TwistTag.D4.tag L (rotElt b), z⁻¹ * F z = ζ := by
  obtain ⟨κ, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hζT
  rw [rotElt_eq] at hcomm
  have hκ : ∀ i, κ (TwistTag.D4.perm i) = κ i := by
    have h1 : rootDiagUnit TwistTag.D4.tag κ * rootDiagUnit TwistTag.D4.tag (tup1 b) =
        rootDiagUnit TwistTag.D4.tag (tup1 b) *
          rootDiagUnit TwistTag.D4.tag (fun i => κ (TwistTag.D4.perm i)) := by
      refine mul_right_cancel (b := (diagramMap TwistTag.D4 L)⁻¹) ?_
      calc rootDiagUnit TwistTag.D4.tag κ * rootDiagUnit TwistTag.D4.tag (tup1 b) * (diagramMap TwistTag.D4 L)⁻¹
          = rootDiagUnit TwistTag.D4.tag κ * (rootDiagUnit TwistTag.D4.tag (tup1 b) * (diagramMap TwistTag.D4 L)⁻¹) := by
            group
        _ = rootDiagUnit TwistTag.D4.tag (tup1 b) * (diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag κ :=
            hcomm
        _ = rootDiagUnit TwistTag.D4.tag (tup1 b) * ((diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag κ) := by
            group
        _ = _ := by rw [diagramMap_inv_mul_rootDiagUnit]; group
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul] at h1
    have h2 := rootDiagUnit_injective h1
    intro i
    have h3 := congrFun h2 i
    simp only [Pi.mul_apply] at h3
    exact (mul_left_cancel (a := tup1 b i) (by rw [mul_comm, h3, mul_comm])).symm
  choose r hr using fun x : Lˣ => exists_zpow_root (L := L) (sub_ne_zero.2 hF.exp) x
  set ν : Fin TwistTag.D4.tag.rank → Lˣ := fun i => r (κ i) with hν
  have hνρ : ∀ i, ν (TwistTag.D4.perm i) = ν i := fun i => by simp only [hν, hκ i]
  have hzT : rootDiagUnit TwistTag.D4.tag ν ∈ torusGroup TwistTag.D4.tag L :=
    rootDiagUnit_mem_torusGroup ν
  refine ⟨rootDiagUnit TwistTag.D4.tag ν, Subgroup.mem_inf.2 ⟨torusGroup_le_adjointGroup' hzT,
    Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, ?_⟩
  · rw [rotElt_eq]
    have hc : (diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag ν = rootDiagUnit TwistTag.D4.tag ν * (diagramMap TwistTag.D4 L)⁻¹ := by
      rw [diagramMap_inv_mul_rootDiagUnit]
      congr 2
      funext i
      exact hνρ i
    calc rootDiagUnit TwistTag.D4.tag ν * (rootDiagUnit TwistTag.D4.tag (tup1 b) * (diagramMap TwistTag.D4 L)⁻¹)
        = (rootDiagUnit TwistTag.D4.tag ν * rootDiagUnit TwistTag.D4.tag (tup1 b)) * (diagramMap TwistTag.D4 L)⁻¹ := by
          group
      _ = (rootDiagUnit TwistTag.D4.tag (tup1 b) * rootDiagUnit TwistTag.D4.tag ν) * (diagramMap TwistTag.D4 L)⁻¹ := by
          rw [torusGroup_comm hzT (rootDiagUnit_mem_torusGroup _)]
      _ = rootDiagUnit TwistTag.D4.tag (tup1 b) * (rootDiagUnit TwistTag.D4.tag ν * (diagramMap TwistTag.D4 L)⁻¹) := by
          group
      _ = rootDiagUnit TwistTag.D4.tag (tup1 b) * ((diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag ν) := by
          rw [hc]
      _ = _ := by group
  · rw [hF.torusPow ν hνρ, rootDiagUnit_inv, ← rootDiagUnit_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
    rw [← hr (κ i)]
    simp only [hν]
    rw [zpow_sub_one]
    group

theorem ell_lang_descent {F : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L} {e : ℤ}
    (hF : EllFrame F e) {b : Lˣ} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) (hbe : b ^ e = b)
    {n h : ModGL TwistTag.D4.tag L} (hh : h ∈ leviGroup L)
    (hx : n * (diagramMap TwistTag.D4 L)⁻¹ = h * rotElt b * h⁻¹) (hFn : F n = n)
    (hlang : ∀ ζ ∈ graphCentralizer TwistTag.D4.tag L (rotElt b),
      (∃ t ∈ torusGroup TwistTag.D4.tag L, ∃ q ∈ rootSpan TwistTag.D4.tag L d4LongA2,
        ζ = t * q) →
      (∃ hm : ζ ∈ monomialSubgroup TwistTag.D4.tag L,
        (∀ x, weylQuotientHom TwistTag.D4.tag L ⟨ζ, hm⟩ • x = d4MatThreeA *ᵥ x) ∨
          (∀ x, weylQuotientHom TwistTag.D4.tag L ⟨ζ, hm⟩ • x = d4MatThreeB *ᵥ x)) →
      ∃ z ∈ graphCentralizer TwistTag.D4.tag L (rotElt b), z⁻¹ * F z = ζ) :
    ∃ y ∈ adjointGroup TwistTag.D4.tag L, F y = y ∧
      y * (n * (diagramMap TwistTag.D4 L)⁻¹) * y⁻¹ = rotElt b := by
  have hFA : F (rotElt b) = rotElt b := hF.rotElt hbe
  have hFx : F (n * (diagramMap TwistTag.D4 L)⁻¹) = n * (diagramMap TwistTag.D4 L)⁻¹ := by
    rw [map_mul, map_inv, hFn, hF.diagram]
  have hFh : F h ∈ leviGroup L := hF.leviGroup hh
  have hconjF : F h * rotElt b * (F h)⁻¹ = h * rotElt b * h⁻¹ := by
    have := hFx
    rw [hx, map_mul, map_mul, map_inv, hFA] at this
    exact this
  set ζ := h⁻¹ * F h with hζ
  have hζL : ζ ∈ leviGroup L := mul_mem (inv_mem hh) hFh
  have hcomm : ζ * rotElt b = rotElt b * ζ := by
    have h1 : h⁻¹ * (F h * rotElt b * (F h)⁻¹) * h = rotElt b := by
      rw [hconjF]; group
    calc ζ * rotElt b = h⁻¹ * (F h * rotElt b * (F h)⁻¹) * h * (h⁻¹ * F h) := by
          rw [hζ]; group
      _ = rotElt b * ζ := by rw [h1, hζ]
  have hZ : ζ ∈ graphCentralizer TwistTag.D4.tag L (rotElt b) :=
    Subgroup.mem_inf.2 ⟨leviGroup_le_adjointGroup hζL,
      Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
  obtain ⟨z, hzZ, hz⟩ : ∃ z ∈ graphCentralizer TwistTag.D4.tag L (rotElt b), z⁻¹ * F z = ζ := by
    obtain ⟨t, ht, q, hq, hζtq⟩ := mem_leviGroup.1 hζL
    have hcomm' : (t * q) * rotElt b = rotElt b * (t * q) := by rw [← hζtq]; exact hcomm
    obtain ⟨hm, hcls⟩ := ell_zeta_classify hb3 hb1 ht hq hcomm'
    rcases hcls with hT | hrot
    · exact ell_lang_torus hF b (by rw [hζtq]; exact hT) hcomm
    · have hmζ : ζ ∈ monomialSubgroup TwistTag.D4.tag L := by rw [hζtq]; exact hm
      have e : (⟨ζ, hmζ⟩ : monomialSubgroup TwistTag.D4.tag L) = ⟨t * q, hm⟩ := Subtype.ext hζtq
      refine hlang ζ hZ ⟨t, ht, q, hq, hζtq⟩ ⟨hmζ, ?_⟩
      rw [e]
      exact hrot
  obtain ⟨hzG, hzc⟩ := Subgroup.mem_inf.1 hzZ
  have hzA : z * rotElt b = rotElt b * z := Subgroup.mem_centralizer_singleton_iff.1 hzc
  refine ⟨z * h⁻¹, mul_mem hzG (inv_mem (leviGroup_le_adjointGroup hh)), ?_, ?_⟩
  · have hFz : F z = z * ζ := by rw [← hz]; group
    rw [map_mul, map_inv, hFz, hζ]
    group
  · calc z * h⁻¹ * (n * (diagramMap TwistTag.D4 L)⁻¹) * (z * h⁻¹)⁻¹
        = z * (h⁻¹ * (n * (diagramMap TwistTag.D4 L)⁻¹) * h) * z⁻¹ := by group
      _ = z * rotElt b * z⁻¹ := by rw [hx]; group
      _ = rotElt b := by rw [hzA]; group

end Zeta

end CFSG.HardMathSupport.Lang.E6Descent
