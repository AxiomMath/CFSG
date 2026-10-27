module

public import CFSG.CGT.Foote82.T66.CitedBAS
public import CFSG.CGT.Foote82.T66.CertProofsBASOmegaEight
public import Certificates.Certificate919011
public import Certificates.Certificate7093
public import Certificates.Certificate919001
public import Certificates.Certificate919003
public import Certificates.Certificate919004
public import Certificates.Certificate919005
import CFSG.CGT.Foote82.T66.CertProofsBASMaximal
import CFSG.CGT.Foote82.T66.CertProofsBASMaximalAlt
import CFSG.CGT.Foote82.T66.OmegaMinusMatrix
import CFSG.CGT.Foote82.T66.FaithfulBasic
import CFSG.ClassicalGroups.Orthogonal.NormalizerOmega
import Mathlib.Tactic.Group
import CFSG.Fischer.Uniq.CompTau
import CFSG.LargeExtraspecial.OrthoF2
import CFSG.LargeExtraspecial.S2Basic
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Foote82.OmegaEight

open CFSG.EvenSmallLie.OmegaEightMinus CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.CGT.Harada80 CFSG.ClassicalGroups.Orthogonal
open scoped Matrix

local notation "V8" => (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2)
local notation "O8" => TauCeti.QuadraticMap.orthogonalGroup (quadQ 3)

theorem eq_reflect_of_rank_one {D : V8 ≃ₗ[ZMod 2] V8} (hD : D ∈ O8) (hD1 : D ≠ 1) {c : V8}
    (hc0 : c ≠ 0) (hspan : ∀ v : V8, D v - v ∈ Submodule.span (ZMod 2) {c}) :
    quadQ 3 c = 1 ∧ D = reflect (quadQ 3) c := by
  have hz2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  choose lam hlam using fun v => Submodule.mem_span_singleton.mp (hspan v)
  have hlin : ∀ v w, lam (v + w) = lam v + lam w := by
    intro v w
    apply smul_left_injective (ZMod 2) hc0
    show lam (v + w) • c = (lam v + lam w) • c
    rw [hlam, add_smul, hlam, hlam, map_add D]
    abel
  have hiso : ∀ v, lam v = 1 → QuadraticMap.polar (quadQ 3) v c = quadQ 3 c := by
    intro v hv
    have h1 : quadQ 3 (D v) = quadQ 3 v := map_of_mem hD v
    have h2 : D v = v + c := by
      have h := hlam v
      rw [hv, one_smul] at h
      rw [h]
      abel
    rw [h2, QuadraticMap.map_add (quadQ 3) v c] at h1
    have h3 : quadQ 3 c + QuadraticMap.polar (quadQ 3) v c = 0 := by
      linear_combination h1
    have h2z : (2 : ZMod 2) = 0 := by decide
    linear_combination h3 - quadQ 3 c * h2z
  obtain ⟨u, hu⟩ : ∃ u, lam u = 1 := by
    by_contra hall
    push Not at hall
    apply hD1
    apply LinearEquiv.ext
    intro v
    have hv : lam v = 0 := (hz2 _).resolve_right (hall v)
    have := hlam v
    rw [hv, zero_smul] at this
    exact (sub_eq_zero.mp this.symm)
  have hpol : ∀ v, QuadraticMap.polar (quadQ 3) v c = lam v * quadQ 3 c := by
    intro v
    rcases hz2 (lam v) with h0 | h1
    · have h := hiso (v + u) (by rw [hlin, h0, hu, zero_add])
      rw [QuadraticMap.polar_add_left, hiso u hu] at h
      rw [h0, zero_mul]
      have := congrArg (· - quadQ 3 c) h
      simpa using this
    · rw [h1, one_mul, hiso v h1]
  have hQc : quadQ 3 c = 1 := by
    rcases hz2 (quadQ 3 c) with h0 | h1
    · exfalso
      apply hc0
      refine (nondegenerate_quadQ 3).1 c fun v => ?_
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm, hpol, h0, mul_zero]
    · exact h1
  refine ⟨hQc, LinearEquiv.ext fun v => ?_⟩
  rw [reflect_apply_of_map_eq_one hQc, hpol, hQc, mul_one, hlam]
  abel

theorem reflect_injective {a b : V8} (ha : quadQ 3 a = 1)
    (h : reflect (quadQ 3) a = reflect (quadQ 3) b) : a = b := by
  have hz2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, QuadraticMap.map_zero] at ha
    exact zero_ne_one ha
  obtain ⟨x, hx⟩ : ∃ x, QuadraticMap.polar (quadQ 3) x a ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ha0 ((nondegenerate_quadQ 3).1 a fun v => by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
      exact hall v)
  have hb : quadQ 3 b ≠ 0 := by
    intro hb0
    rw [reflect_of_map_eq_zero hb0] at h
    have := congrArg (fun g : V8 ≃ₗ[ZMod 2] V8 => g x) h
    simp only [reflect_apply_of_map_eq_one ha] at this
    rw [show ((1 : V8 ≃ₗ[ZMod 2] V8) x) = x from rfl, add_eq_left] at this
    rcases hz2 (QuadraticMap.polar (quadQ 3) x a) with h0 | h1
    · exact hx h0
    · rw [h1, one_smul] at this
      exact ha0 this
  have hb1 : quadQ 3 b = 1 := zmod_two_eq_one_of_ne_zero hb
  have hx1 : QuadraticMap.polar (quadQ 3) x a = 1 := zmod_two_eq_one_of_ne_zero hx
  have := congrArg (fun g : V8 ≃ₗ[ZMod 2] V8 => g x) h
  simp only [reflect_apply_of_map_eq_one ha, reflect_apply_of_map_eq_one hb1, hx1, one_smul,
    add_right_inj] at this
  rcases hz2 (QuadraticMap.polar (quadQ 3) x b) with h0 | h1
  · rw [h0, zero_smul] at this
    exact absurd this ha0
  · rw [h1, one_smul] at this
    exact this

theorem comm_reflect_iff {g : V8 ≃ₗ[ZMod 2] V8} (hg : g ∈ O8) {c : V8} (hc : quadQ 3 c = 1) :
    g * reflect (quadQ 3) c * g⁻¹ = reflect (quadQ 3) c ↔ g c = c := by
  rw [reflect_conj hg c]
  constructor
  · intro h
    exact reflect_injective (by rw [map_of_mem hg, hc]) h
  · intro h
    rw [h]

theorem commutator_le_O8 : ⁅O8, O8⁆ ≤ O8 := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
    (Subgroup.inv_mem _ hb)

@[expose] noncomputable def rhoO :
    ↥(⁅O8, O8⁆) →* Equiv.Perm (Fin 136) :=
  piO.comp (Subgroup.inclusion commutator_le_O8)

section Max


theorem rhoO_apply (g : ↥(⁅O8, O8⁆)) :
    rhoO g = piO (Subgroup.inclusion commutator_le_O8 g) := rfl

theorem exists_rhoO_apply_zero (j : Fin 136) : ∃ g : ↥(⁅O8, O8⁆), rhoO g 0 = j := by
  obtain ⟨x, hx, hxj⟩ := exists_omegaT_apply_zero j
  obtain ⟨G, hG, hGe⟩ := omegaT_le hx
  refine ⟨⟨G, hG⟩, ?_⟩
  rw [rhoO_apply, show Subgroup.inclusion commutator_le_O8 (⟨G, hG⟩ : ↥(⁅O8, O8⁆)) = G from
    Subtype.ext rfl, hGe, hxj]

theorem exists_rhoO_eq_sgen {j : ℕ} (hj : j ∈ stabIdx) :
    ∃ g : ↥(⁅O8, O8⁆), rhoO g = sgen j := by
  have hjs := (stab_ok.1 j hj).1
  rw [omegaS_size] at hjs
  obtain ⟨G, hG, hGe⟩ := omegaT_le (sgen_spec hjs).2.2
  exact ⟨⟨G, hG⟩, by rw [rhoO_apply, show Subgroup.inclusion commutator_le_O8
    (⟨G, hG⟩ : ↥(⁅O8, O8⁆)) = G from Subtype.ext rfl, hGe]⟩

end Max

section Tree

theorem stabTreeCheck_holds : stabTreeCheck () = true :=
  Certificates.certificate919011

private noncomputable def colOf (p : ℕ) : ℕ := (stabTree ()).2.2.2.1[p]!

private noncomputable def depOf (p : ℕ) : ℕ := (stabTree ()).2.2.1[p]!

private noncomputable def parOf (p : ℕ) : ℕ := (stabTree ()).1[p]!

private noncomputable def labOf (p : ℕ) : ℕ := (stabTree ()).2.1[p]!

private theorem tree_spec :
    colOf 0 = 0 ∧ ∃ r₁ r₂ : ℕ, colOf r₁ = 1 ∧ colOf r₂ = 2 ∧
      (∀ p, 1 ≤ p → p < 136 → (colOf p = 1 ∨ colOf p = 2) ∧
        (depOf p = 0 → p = r₁ ∨ p = r₂) ∧
        (depOf p ≠ 0 → parOf p < 136 ∧ labOf p < stabIdx.length ∧ depOf (parOf p) < depOf p ∧
          colOf (parOf p) = colOf p ∧ (omegaS[stabIdx.getD (labOf p) 0]!)[parOf p]! = p)) ∧
      (Finset.univ.filter fun p : Fin 136 => colOf p = 1).card = 63 ∧
      (Finset.univ.filter fun p : Fin 136 => colOf p = 2).card = 72 := by
  have h := stabTreeCheck_holds
  simp only [stabTreeCheck, stabTreeOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, -⟩, -⟩, -⟩, -⟩, hc1⟩, hc2⟩, hall⟩, hn1⟩, hn2⟩ := h
  refine ⟨h0, _, _, hc1, hc2, fun p hp1 hp2 => ?_, hn1, hn2⟩
  obtain ⟨hcol, hrest⟩ := hall (p - 1) (by omega)
  rw [show p - 1 + 1 = p by omega] at hcol hrest
  refine ⟨hcol, fun hd => ?_, fun hd => ?_⟩
  · rw [if_pos (show (stabTree ()).2.2.1[p]! = 0 from hd)] at hrest
    simp only [Bool.or_eq_true, beq_iff_eq] at hrest
    exact hrest
  · rw [if_neg (show ¬ (stabTree ()).2.2.1[p]! = 0 from hd)] at hrest
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hrest
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hrest
    exact ⟨h1, h2, h3, h4, h5⟩


theorem omegaS_apply {l : ℕ} (hl : l < stabIdx.length) {x : ℕ} (hx : x < 136) :
    (omegaS[stabIdx.getD l 0]!)[x]! = (sgen (stabIdx.getD l 0) ⟨x, hx⟩ : ℕ) := by
  have hj : stabIdx.getD l 0 ∈ stabIdx := by
    rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem _
  have hjs := (stab_ok.1 _ hj).1
  rw [omegaS_size] at hjs
  exact (sgen_spec hjs).1 ⟨x, hx⟩

private theorem class_subset {B : Set (Fin 136)}
    (hB : ∀ j ∈ stabIdx, ∀ x ∈ B, sgen j x ∈ B ∧ (sgen j)⁻¹ x ∈ B) {p : Fin 136} (hp : p ∈ B)
    (hp0 : p ≠ 0) : ∀ q : Fin 136, colOf q = colOf p → q ∈ B := by
  obtain ⟨h0, r₁, r₂, hc1, hc2, hall, -, -⟩ := tree_spec
  have hpos : ∀ x : Fin 136, x ≠ 0 → 1 ≤ (x : ℕ) := fun x hx => by
    have : (x : ℕ) ≠ 0 := fun h => hx (Fin.ext h)
    omega
  have hgen : ∀ x : Fin 136, x ≠ 0 → depOf x ≠ 0 →
      ∃ j ∈ stabIdx, ∃ y : Fin 136, sgen j y = x ∧ depOf y < depOf x ∧ colOf y = colOf x := by
    intro x hx hd
    obtain ⟨h1, h2, h3, h4, h5⟩ := (hall x (hpos x hx) x.2).2.2 hd
    refine ⟨stabIdx.getD (labOf x) 0, by rw [List.getD_eq_getElem _ _ h2]; exact List.getElem_mem _,
      ⟨parOf x, h1⟩, Fin.ext ?_, h3, h4⟩
    rw [← omegaS_apply h2 h1]
    exact h5
  have hcol0 : ∀ x : Fin 136, x ≠ 0 → colOf x ≠ 0 := fun x hx => by
    rcases (hall x (hpos x hx) x.2).1 with h | h <;> omega
  have hne0 : ∀ y : Fin 136, colOf y ≠ 0 → y ≠ 0 := fun y hy h => by
    rw [h] at hy
    exact hy h0
  have hrootcol : ∀ x : Fin 136, x ≠ 0 → depOf x = 0 →
      (x : ℕ) = if colOf x = 1 then r₁ else r₂ := by
    intro x hx hd
    rcases (hall x (hpos x hx) x.2).2.1 hd with h | h
    · rw [h, hc1, if_pos rfl]
    · rw [h, hc2, if_neg (by decide)]
  have hdesc : ∀ n, ∀ x : Fin 136, depOf x = n → x ∈ B → x ≠ 0 →
      ∃ y : Fin 136, (y : ℕ) = (if colOf x = 1 then r₁ else r₂) ∧ y ∈ B := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hxn hxB hx0
      by_cases hd : depOf x = 0
      · exact ⟨x, hrootcol x hx0 hd, hxB⟩
      · obtain ⟨j, hj, y, hsj, hdlt, hcol⟩ := hgen x hx0 hd
        have hyB : y ∈ B := by
          have := (hB j hj x hxB).2
          rwa [← hsj, Equiv.Perm.inv_eq_iff_eq.mpr rfl] at this
        have hy0 : y ≠ 0 := hne0 y (by rw [hcol]; exact hcol0 x hx0)
        obtain ⟨z, hz, hzB⟩ := ih _ (hxn ▸ hdlt) y rfl hyB hy0
        exact ⟨z, by rw [hz, hcol], hzB⟩
  obtain ⟨r, hr, hrB⟩ := hdesc _ p rfl hp hp0
  have hasc : ∀ n, ∀ x : Fin 136, depOf x = n → x ≠ 0 → colOf x = colOf p → x ∈ B := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hxn hx0 hxc
      by_cases hd : depOf x = 0
      · have e : x = r := Fin.ext (by rw [hr, hrootcol x hx0 hd, hxc])
        rw [e]
        exact hrB
      · obtain ⟨j, hj, y, hsj, hdlt, hcol⟩ := hgen x hx0 hd
        have hy0 : y ≠ 0 := hne0 y (by rw [hcol]; exact hcol0 x hx0)
        have hyB := ih _ (hxn ▸ hdlt) y rfl hy0 (hcol.trans hxc)
        rw [← hsj]
        exact (hB j hj _ hyB).1
  intro q hq
  exact hasc _ q rfl (hne0 q (by rw [hq]; exact hcol0 p hp0)) hq

private theorem eq_univ_of_dvd {B : Set (Fin 136)}
    (hB : ∀ j ∈ stabIdx, ∀ x ∈ B, sgen j x ∈ B ∧ (sgen j)⁻¹ x ∈ B) (h0B : (0 : Fin 136) ∈ B)
    {p : Fin 136} (hp : p ∈ B) (hp0 : p ≠ 0) (hdvd : B.ncard ∣ 136) : B = Set.univ := by
  obtain ⟨h0, r₁, r₂, -, -, hall, hn1, hn2⟩ := tree_spec
  have hpos : ∀ x : Fin 136, x ≠ 0 → 1 ≤ (x : ℕ) := fun x hx => by
    have : (x : ℕ) ≠ 0 := fun h => hx (Fin.ext h)
    omega
  have hcol : ∀ x : Fin 136, x ≠ 0 → colOf x = 1 ∨ colOf x = 2 := fun x hx =>
    (hall x (hpos x hx) x.2).1
  have h00 : colOf ((0 : Fin 136) : ℕ) = 0 := h0
  have hmeet : ∀ x ∈ B, x ≠ 0 → ∀ y : Fin 136, colOf y = colOf x → y ∈ B :=
    fun x hxB hx0 => class_subset hB hxB hx0
  by_contra hne
  have hBeq : B = ↑(insert (0 : Fin 136)
      (Finset.univ.filter fun x : Fin 136 => colOf x = colOf p)) := by
    ext y
    simp only [Finset.coe_insert, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_insert_iff, Set.mem_setOf_eq]
    constructor
    · intro hy
      by_cases hy0 : y = 0
      · exact Or.inl hy0
      · right
        by_contra hyc
        apply hne
        rw [Set.eq_univ_iff_forall]
        intro z
        by_cases hz0 : z = 0
        · rw [hz0]
          exact h0B
        · have hpz : colOf z = colOf p ∨ colOf z = colOf y := by
            rcases hcol z hz0 with hz | hz <;> rcases hcol p hp0 with hpc | hpc <;>
              rcases hcol y hy0 with hyc' | hyc' <;> first | omega | (left; omega) | (right; omega)
          rcases hpz with h | h
          · exact hmeet p hp hp0 z h
          · exact hmeet y hy hy0 z h
    · rintro (rfl | hyc)
      · exact h0B
      · exact hmeet p hp hp0 y hyc
  have hcard : B.ncard = (Finset.univ.filter fun x : Fin 136 => colOf x = colOf p).card + 1 := by
    rw [hBeq, Set.ncard_coe_finset, Finset.card_insert_of_notMem]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h00]
    rcases hcol p hp0 with h | h <;> omega
  rcases hcol p hp0 with hp1 | hp2
  · rw [hp1, hn1] at hcard
    rw [hcard] at hdvd
    exact absurd hdvd (by decide)
  · rw [hp2, hn2] at hcard
    rw [hcard] at hdvd
    exact absurd hdvd (by decide)

end Tree

section Coatom


theorem isCoatom_stabZero :
    IsCoatom ((MulAction.stabilizer (Equiv.Perm (Fin 136)) (0 : Fin 136)).comap rhoO) := by
  set H₀ := (MulAction.stabilizer (Equiv.Perm (Fin 136)) (0 : Fin 136)).comap rhoO with hH₀
  letI : MulAction ↥(⁅O8, O8⁆) (Fin 136) := MulAction.compHom (Fin 136) rhoO
  have hsmul : ∀ (g : ↥(⁅O8, O8⁆)) (j : Fin 136), g • j = rhoO g j := fun _ _ => rfl
  have hmemH : ∀ g, g ∈ H₀ ↔ rhoO g 0 = 0 := fun g => Iff.rfl
  have hstab : MulAction.stabilizer ↥(⁅O8, O8⁆) (0 : Fin 136) = H₀ := by
    ext g
    rw [MulAction.mem_stabilizer_iff, hsmul, hmemH]
  have horbit : MulAction.orbit ↥(⁅O8, O8⁆) (0 : Fin 136) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro j
    obtain ⟨g, hg⟩ := exists_rhoO_apply_zero j
    exact ⟨g, by show g • (0 : Fin 136) = j; rw [hsmul, hg]⟩
  have hidx : H₀.index = 136 := by
    rw [← hstab, MulAction.index_stabilizer, horbit, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  refine ⟨fun htop => ?_, fun K hK => ?_⟩
  · obtain ⟨g, hg⟩ := exists_rhoO_apply_zero 1
    have hgH : g ∈ H₀ := by rw [htop]; exact Subgroup.mem_top g
    rw [hmemH, hg] at hgH
    exact absurd hgH (by decide)
  · have hle : H₀ ≤ K := hK.le
    have hrel := Subgroup.relIndex_mul_index hle
    have hstabK : MulAction.stabilizer ↥K (0 : Fin 136) = H₀.subgroupOf K := by
      rw [← MulAction.stabilizer_subgroupOf, hstab]
    have hidxK : H₀.relIndex K = (MulAction.orbit ↥K (0 : Fin 136)).ncard := by
      rw [Subgroup.relIndex, ← hstabK, MulAction.index_stabilizer]
    set B := MulAction.orbit ↥K (0 : Fin 136) with hBdef
    have hksmul : ∀ (k : ↥K) (x : Fin 136), k • x = rhoO (k : ↥(⁅O8, O8⁆)) x := fun _ _ => rfl
    have hBst : ∀ j ∈ stabIdx, ∀ x ∈ B, sgen j x ∈ B ∧ (sgen j)⁻¹ x ∈ B := by
      intro j hj x hx
      obtain ⟨g, hg⟩ := exists_rhoO_eq_sgen hj
      have hgK : g ∈ K := hle (by rw [hmemH, hg]; exact sgen_fix_zero hj)
      obtain ⟨k, rfl⟩ := hx
      refine ⟨⟨⟨g, hgK⟩ * k, ?_⟩, ⟨⟨g, hgK⟩⁻¹ * k, ?_⟩⟩
      · show (⟨g, hgK⟩ * k : ↥K) • (0 : Fin 136) = sgen j (k • (0 : Fin 136))
        rw [mul_smul, hksmul]
        show rhoO g (k • (0 : Fin 136)) = sgen j (k • (0 : Fin 136))
        rw [hg]
      · show ((⟨g, hgK⟩ : ↥K)⁻¹ * k) • (0 : Fin 136) = (sgen j)⁻¹ (k • (0 : Fin 136))
        rw [mul_smul, hksmul]
        show rhoO g⁻¹ (k • (0 : Fin 136)) = (sgen j)⁻¹ (k • (0 : Fin 136))
        rw [map_inv, hg]
    have h0B : (0 : Fin 136) ∈ B := MulAction.mem_orbit_self 0
    obtain ⟨k, hkK, hkH⟩ := SetLike.exists_of_lt hK
    have hp : rhoO k 0 ∈ B := ⟨⟨k, hkK⟩, rfl⟩
    have hp0 : rhoO k 0 ≠ 0 := fun h => hkH ((hmemH k).mpr h)
    have hdvd : B.ncard ∣ 136 := by
      rw [← hidxK, ← hidx, ← hrel]
      exact Dvd.intro _ rfl
    have hBu := eq_univ_of_dvd hBst h0B hp hp0 hdvd
    have h136 : H₀.relIndex K = 136 := by
      rw [hidxK, hBu, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hKi : K.index = 1 := by
      rw [h136, hidx] at hrel
      omega
    exact Subgroup.index_eq_one.mp hKi

theorem isCoatom_stab (j : Fin 136) :
    IsCoatom ((MulAction.stabilizer (Equiv.Perm (Fin 136)) j).comap rhoO) := by
  obtain ⟨h, hh⟩ := exists_rhoO_apply_zero j
  have e : MulEquiv.mapSubgroup (MulAut.conj h)
      ((MulAction.stabilizer (Equiv.Perm (Fin 136)) (0 : Fin 136)).comap rhoO) =
      (MulAction.stabilizer (Equiv.Perm (Fin 136)) j).comap rhoO := by
    ext x
    rw [MulEquiv.coe_mapSubgroup, Subgroup.mem_map_equiv, Subgroup.mem_comap,
      Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
      MulAut.conj_symm_apply, map_mul, map_mul, map_inv, Equiv.Perm.smul_def,
      Equiv.Perm.smul_def, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hh]
    constructor
    · intro hx
      have := congrArg (rhoO h) hx
      rwa [Equiv.Perm.eq_inv_iff_eq.mp rfl] at this
    · intro hx
      rw [hx, Equiv.Perm.inv_eq_iff_eq.mpr rfl]
  rw [← e, OrderIso.isCoatom_iff]
  exact isCoatom_stabZero

end Coatom

section ModuleTransport

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem conj_eq_iff_comm {G : Type*} [Group G] (a b : G) :
    a * b * a⁻¹ = b ↔ a * b = b * a := by
  rw [mul_inv_eq_iff_eq_mul]

theorem basMaximal_omegaEight
    [Finite V] (L : Subgroup (GLV V))
    (hL : IsOmegaMinusModule L 3) (hf : FaithfulTildeV L) (d : GLV V)
    (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) (hd2 : orderOf d = 2)
    (htv : Module.finrank (ZMod 2) ↥(BAS.tvComm L d) =
      Module.finrank (ZMod 2) ↥(tildeVBot L) + 1) :
    IsCoatom ((L ⊓ Subgroup.centralizer ({d} : Set (GLV V))).subgroupOf L) := by
  obtain ⟨α, hαs, β, hβs, hβker, hrel⟩ := hL
  have hβk : ∀ w, β w = 0 ↔ (w : V) ∈ fixedSpace L := L13Aux.ker_iff_of_eq hβker
  have hrel' : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) w →
      β w' = (((α ℓ : ↥(omegaMinusTwo 3)) : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) *ᵥ β w := hrel
  have hdd : d * d = 1 := by
    have h := pow_orderOf_eq_one d
    rw [hd2, sq] at h
    exact h
  obtain ⟨D, hDD, hD⟩ := OmegaMinusMat.exists_matrix hβs hβk hd hdd
  have hconj := OmegaMinusMat.conj_eq hβs hrel' hd hdd hDD hD
  have hαi := OmegaMinusMat.injective_alpha hβk hrel' hf
  have hrk := OmegaMinusMat.finrank_range_add hβs hβk hd hdd hD
  have hrk1 : Module.finrank (ZMod 2) ↥(LinearMap.range (mulVecLin
      ((D : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) - 1))) = 1 := by
    omega
  have hN : ∀ y ∈ omegaMinusTwo 3, D * y * D⁻¹ ∈ omegaMinusTwo 3 := by
    intro y hy
    obtain ⟨ℓ, hℓ⟩ := hαs ⟨y, hy⟩
    have hℓ'L : d * (ℓ : GLV V) * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hd _).1 ℓ.2
    have h := hconj ℓ ⟨_, hℓ'L⟩ rfl
    rw [hℓ] at h
    have h' : D * y * D⁻¹ = ((α ⟨_, hℓ'L⟩ : ↥(omegaMinusTwo 3)) :
        GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) := h
    rw [h']
    exact (α _).2
  set e := toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) with he
  have hN' : ∀ x ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (3 + 1) (ZMod 2) 1 1),
      D * x * D⁻¹ ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (3 + 1) (ZMod 2) 1 1) := by
    rw [← CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.omegaMinusTwo_eq_statedOmega 3]
    exact hN
  have hDO : e D ∈ O8 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
    rw [he, toLinEquiv_apply]
    have h := isometry_of_normalizes_statedOmega
      (CFSG.LieType.Universal.Spin.coe_quadMinus (3 + 1) (ZMod 2) 1 1) (nondegenerate_quadQ 3)
      (by simp) hN' v
    rwa [← CFSG.LieType.Universal.Spin.coe_quadMinus (3 + 1) (ZMod 2) 1 1] at h
  obtain ⟨⟨c, hcR⟩, hc0, hcgen⟩ := finrank_eq_one_iff'.mp hrk1
  have hc0' : c ≠ 0 := fun h => hc0 (Subtype.ext h)
  have heD : ∀ u, e D u - u = ((D : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2)
      (ZMod 2)) - 1) *ᵥ u := fun u => by
    rw [he, toLinEquiv_apply, sub_mulVec, one_mulVec]
  have hspan : ∀ u, e D u - u ∈ Submodule.span (ZMod 2) {c} := by
    intro u
    obtain ⟨a, ha⟩ := hcgen ⟨_, LinearMap.mem_range_self _ u⟩
    have ha' : a • c = (mulVecLin ((D : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2)
        (ZMod 2)) - 1)) u := congrArg Subtype.val ha
    rw [heD, ← mulVecLin_apply, ← ha']
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hD1 : e D ≠ 1 := by
    intro h1
    obtain ⟨u, hu⟩ := hcR
    apply hc0'
    rw [← hu, mulVecLin_apply, ← heD, h1]
    exact sub_self u
  obtain ⟨hQc, hDr⟩ := eq_reflect_of_rank_one hDO hD1 hc0' hspan
  set j₀ := ptEquiv.symm ⟨c, hQc⟩ with hj₀
  have hvecj : vec 3 nsArr[(j₀ : ℕ)]! = c := by
    rw [← ptEquiv_val, hj₀, Equiv.apply_symm_apply]
  have hmemΩ' : ∀ y, y ∈ omegaMinusTwo 3 → e y ∈ ⁅O8, O8⁆ := by
    intro y hy
    rw [omegaMinusTwo_eq_comap, Subgroup.mem_comap] at hy
    exact hy
  have hmemΩ : ∀ g : ↥(omegaMinusTwo 3), e (g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) ∈
      ⁅O8, O8⁆ := fun g => hmemΩ' _ g.2
  let ψ : ↥(omegaMinusTwo 3) →* ↥(⁅O8, O8⁆) :=
    { toFun := fun g => ⟨e g, hmemΩ g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hψi : Function.Injective ψ := fun a b h =>
    Subtype.ext (e.injective (congrArg Subtype.val h))
  have hψs : Function.Surjective ψ := by
    intro g
    have hg : e.symm (g : V8 ≃ₗ[ZMod 2] V8) ∈ omegaMinusTwo 3 := by
      rw [omegaMinusTwo_eq_comap, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply]
      exact g.2
    exact ⟨⟨_, hg⟩, Subtype.ext (MulEquiv.apply_symm_apply e _)⟩
  let φ : ↥L ≃* ↥(⁅O8, O8⁆) :=
    MulEquiv.ofBijective (ψ.comp α) ⟨hψi.comp hαi, hψs.comp hαs⟩
  have hφ : ∀ ℓ : ↥L, ((φ ℓ : ↥(⁅O8, O8⁆)) : V8 ≃ₗ[ZMod 2] V8) =
      e ((α ℓ : ↥(omegaMinusTwo 3)) : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) := fun _ => rfl
  have hmem : ∀ ℓ : ↥L, ℓ ∈ (L ⊓ Subgroup.centralizer ({d} : Set (GLV V))).subgroupOf L ↔
      φ ℓ ∈ (MulAction.stabilizer (Equiv.Perm (Fin 136)) j₀).comap rhoO := by
    intro ℓ
    have hℓ'L : d * (ℓ : GLV V) * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hd _).1 ℓ.2
    set G : V8 ≃ₗ[ZMod 2] V8 := e ((α ℓ : ↥(omegaMinusTwo 3)) : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2))
      with hG
    have hGO : G ∈ O8 := commutator_le_O8 (hmemΩ (α ℓ))
    have hR : φ ℓ ∈ (MulAction.stabilizer (Equiv.Perm (Fin 136)) j₀).comap rhoO ↔ G c = c := by
      rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, rhoO_apply]
      have hincl : Subgroup.inclusion commutator_le_O8 (φ ℓ) = ⟨G, hGO⟩ := Subtype.ext rfl
      rw [hincl]
      have hv := vec_piO ⟨G, hGO⟩ j₀
      rw [hvecj] at hv
      constructor
      · intro h
        rw [h, hvecj] at hv
        exact hv.symm
      · intro h
        apply ptEquiv.injective
        apply Subtype.ext
        rw [ptEquiv_val, ptEquiv_val, hv, hvecj]
        exact h
    rw [hR, ← comm_reflect_iff hGO hQc, ← hDr, conj_eq_iff_comm, eq_comm, ← conj_eq_iff_comm]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    have hDG : e D * G * (e D)⁻¹ = G ↔ D * ((α ℓ : ↥(omegaMinusTwo 3)) :
        GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) * D⁻¹ =
          ((α ℓ : ↥(omegaMinusTwo 3)) : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) := by
      rw [hG, ← map_inv, ← map_mul, ← map_mul]
      exact e.injective.eq_iff
    rw [hDG, hconj ℓ ⟨_, hℓ'L⟩ rfl]
    constructor
    · rintro ⟨-, h⟩
      have h' : d * (ℓ : GLV V) * d⁻¹ = ℓ := (conj_eq_iff_comm d ℓ).mpr h.symm
      have := hαi.eq_iff.mpr (Subtype.ext h' : (⟨_, hℓ'L⟩ : ↥L) = ℓ)
      rw [this]
    · intro h
      refine ⟨ℓ.2, ?_⟩
      have h1 : (⟨_, hℓ'L⟩ : ↥L) = ℓ := hαi (Subtype.ext h)
      have h2 : d * (ℓ : GLV V) * d⁻¹ = ℓ := congrArg Subtype.val h1
      exact ((conj_eq_iff_comm d ℓ).mp h2).symm
  have hmap : MulEquiv.mapSubgroup φ ((L ⊓ Subgroup.centralizer ({d} : Set (GLV V))).subgroupOf L) =
      (MulAction.stabilizer (Equiv.Perm (Fin 136)) j₀).comap rhoO := by
    ext y
    rw [MulEquiv.coe_mapSubgroup, Subgroup.mem_map_equiv, hmem, MulEquiv.apply_symm_apply]
  rw [← OrderIso.isCoatom_iff (MulEquiv.mapSubgroup φ), hmap]
  exact isCoatom_stab j₀

end ModuleTransport

end CFSG.CGT.Foote82.OmegaEight

namespace CFSG.CGT.Foote82

theorem basMaximal_holds :
    BASMaximal := by
  intro V _ _ _ L htype hf hirr d hd hd2 htv
  rcases htype with hA | hO2 | hO3
  · exact basMaximal_altSix L hA hf d hd hd2 htv
  · exact basMaximal_omegaSix V L hO2 hf hirr d hd hd2 htv
  · exact OmegaEight.basMaximal_omegaEight L hO3 hf d hd hd2 htv

end CFSG.CGT.Foote82
