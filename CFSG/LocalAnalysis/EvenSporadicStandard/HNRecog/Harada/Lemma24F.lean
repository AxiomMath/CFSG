module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24E

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA
open scoped commutatorElement

variable {G : Type} [Group G] {ι : Elem2 6 →* G} {a : G}

private theorem mem_F24_iff {x : G} :
    x ∈ F24 ι a ↔ x ∈ indSub ι A5g ∧ x ∈ centralizer ({a} : Set G) :=
  Subgroup.mem_inf

private theorem coordElt_injective (hι : Function.Injective ι) :
    Function.Injective (coordElt ι) := by
  intro v w hvw
  exact (Multiplicative.ofAdd).injective (hι hvw)

private theorem coordElt_inv (ι : Elem2 6 →* G) (v : V6) :
    (coordElt ι v)⁻¹ = coordElt ι v := by
  rw [inv_eq_iff_mul_eq_one, ← coordElt_add]
  have hvv : v + v = 0 := by
    ext i
    exact CharTwo.add_self_eq_zero (v i)
  rw [hvv, coordElt_zero]

private theorem gA_mem_A5g : gA ∈ A5g :=
  Subgroup.subset_closure (show gA ∈ ({gA, gB, gC} : Set (Equiv.Perm V6)) by simp)

private theorem gB_mem_A5g : gB ∈ A5g :=
  Subgroup.subset_closure (show gB ∈ ({gA, gB, gC} : Set (Equiv.Perm V6)) by simp)

private theorem gC_mem_A5g : gC ∈ A5g :=
  Subgroup.subset_closure (show gC ∈ ({gA, gB, gC} : Set (Equiv.Perm V6)) by simp)

private theorem induces_pow {x : G} {g : Equiv.Perm V6} (hx : Induces ι x g) (m : ℕ) :
    Induces ι (x ^ m) (g ^ m) := by
  induction m with
  | zero => simpa using induces_one
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact ih.mul hx

private theorem Induces.zpow {x : G} {g : Equiv.Perm V6} (hx : Induces ι x g) (n : ℤ) :
    Induces ι (x ^ n) (g ^ n) := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, zpow_natCast]
    exact induces_pow hx m
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    exact (induces_pow hx m).inv

private theorem Induces.commutator {x y : G} {g k : Equiv.Perm V6}
    (hx : Induces ι x g) (hy : Induces ι y k) : Induces ι ⁅x, y⁆ ⁅g, k⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  exact ((hx.mul hy).mul hx.inv).mul hy.inv

private theorem coordElt_mem_F24 (h : Setting24 ι a) {v : V6} (hv : v ∈ Fix3) :
    coordElt ι v ∈ F24 ι a := by
  rw [mem_F24_iff]
  refine ⟨coordElt_mem_indSub A5g v, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := h.a_induces v
  rw [mem_Fix3] at hv
  rw [hv] at h1
  have h2 : a * coordElt ι v = coordElt ι v * a := by
    have := congrArg (· * a) h1
    simpa [mul_assoc] using this
  exact h2.symm

private theorem coordElt_add_mem_commutator (h : Setting24 ι a) {v : V6} (hv : v ∈ Fix3)
    {g : Equiv.Perm V6} (hg : g ∈ A5g) :
    coordElt ι (v + g v) ∈ ⁅F24 ι a, F24 ι a⁆ := by
  obtain ⟨f, hf, hfg⟩ := exists_lift_F24 h hg
  have hvF : coordElt ι v ∈ F24 ι a := coordElt_mem_F24 h hv
  have hmem := Subgroup.commutator_mem_commutator (H₁ := F24 ι a) (H₂ := F24 ι a) hvF hf
  have heq : coordElt ι (v + g v) = ⁅coordElt ι v, f⁆ := by
    rw [commutatorElement_def, coordElt_add, coordElt_inv, ← hfg v]
    group
  rw [heq]
  exact hmem

private theorem coordElt_smul_mem {w : V6}
    (hw : coordElt ι w ∈ ⁅F24 ι a, F24 ι a⁆) (c : ZMod 2) :
    coordElt ι (c • w) ∈ ⁅F24 ι a, F24 ι a⁆ := by
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
  · rw [zero_smul, coordElt_zero]
    exact one_mem _
  · rw [one_smul]
    exact hw

private theorem E24_le_commutator_F24 (h : Setting24 ι a) :
    E24 ι a ≤ ⁅F24 ι a, F24 ι a⁆ := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_E24_iff h).mp hx
  obtain ⟨c0, c1, c2, c3, hy_eq⟩ := Fix3_comm_span y hy
  rw [hy_eq]
  simp only [coordElt_add]
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_
  · exact coordElt_smul_mem (coordElt_add_mem_commutator h commV_mem.1 gA_mem_A5g) c0
  · exact coordElt_smul_mem (coordElt_add_mem_commutator h commV_mem.2.1 gA_mem_A5g) c1
  · exact coordElt_smul_mem (coordElt_add_mem_commutator h commV_mem.2.1 gB_mem_A5g) c2
  · exact coordElt_smul_mem (coordElt_add_mem_commutator h commV_mem.2.2 gC_mem_A5g) c3

private theorem A5g_le_indGroup_commutator_F (h : Setting24 ι a) :
    A5g ≤ indGroup ι ⁅F24 ι a, F24 ι a⁆ := by
  have hcomm : ⁅A5g, A5g⁆ ≤ indGroup ι ⁅F24 ι a, F24 ι a⁆ := by
    rw [Subgroup.commutator_le]
    intro g1 hg1 g2 hg2
    obtain ⟨f1, hf1, hf1g⟩ := exists_lift_F24 h hg1
    obtain ⟨f2, hf2, hf2g⟩ := exists_lift_F24 h hg2
    exact mem_indGroup.mpr
      ⟨⁅f1, f2⁆, Subgroup.commutator_mem_commutator hf1 hf2,
        Induces.commutator hf1g hf2g⟩
  rwa [A5g_perfect] at hcomm

theorem F24_perfect (h : Setting24 ι a) : ⁅F24 ι a, F24 ι a⁆ = F24 ι a := by
  have hcomm_le_F : ⁅F24 ι a, F24 ι a⁆ ≤ F24 ι a := by
    rw [Subgroup.commutator_le]
    intro g1 hg1 g2 hg2
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg1 hg2) (inv_mem hg1)) (inv_mem hg2)
  apply le_antisymm hcomm_le_F
  intro f hf
  obtain ⟨g, hg, hfg⟩ := mem_indSub.mp (mem_F24_iff.mp hf).1
  have hgR : g ∈ indGroup ι ⁅F24 ι a, F24 ι a⁆ := A5g_le_indGroup_commutator_F h hg
  obtain ⟨f', hf', hf'g⟩ := mem_indGroup.mp hgR
  have hx1 : Induces ι (f * f'⁻¹) 1 := by
    have hh := hfg.mul hf'g.inv
    rwa [mul_inv_cancel] at hh
  obtain ⟨v, hv⟩ := Induces.exists_eq_coordElt (ι := ι) h.centralizer_le hx1
  have hmemE : f * f'⁻¹ ∈ E24 ι a := by
    rw [← F24_inf_range (ι := ι) (a := a), Subgroup.mem_inf]
    exact ⟨mul_mem hf (inv_mem (hcomm_le_F hf')),
      MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd v, hv.symm⟩⟩
  have hcomm : f * f'⁻¹ ∈ ⁅F24 ι a, F24 ι a⁆ := E24_le_commutator_F24 h hmemE
  have hone : (f * f'⁻¹) * f' = f := by group
  rw [← hone]
  exact mul_mem hcomm hf'

theorem F24_inf_zpowers (h : Setting24 ι a) : F24 ι a ⊓ zpowers a = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨hzF, hzpow⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzpow
  have hmem : a ^ k ∈ F24 ι a := hk.symm ▸ hzF
  have hmem_ind : a ^ k ∈ indSub ι A5g := (mem_F24_iff.mp hmem).1
  have hkpow : Induces ι (a ^ k) (w3 ^ k) := h.a_induces.zpow k
  have hw3mem : w3 ^ k ∈ A5g := Induces.mem_of_mem_indSub h.inj hmem_ind hkpow
  have hfix : (w3 ^ k) ch1 = ch1 := A5g_fix_ch1 (w3 ^ k) hw3mem
  have hem : a ^ k = a ^ (k % 3) := zpow_eq_zpow_emod' k h.a_cube
  have hw3em : w3 ^ k = w3 ^ (k % 3) := zpow_eq_zpow_emod' k w3_pow_three
  rw [hw3em] at hfix
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
    have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have h1 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    omega
  rcases hk3 with hk0 | hk1 | hk2
  · rw [hk0, zpow_zero] at hem
    rw [hem] at hk
    exact hk.symm
  · exfalso
    have hfix1 : w3 ch1 = ch1 := by
      rw [hk1] at hfix
      simpa using hfix
    exact w3_moves_ch1.1 hfix1
  · exfalso
    have hfix2 : (w3 * w3) ch1 = ch1 := by
      rw [hk2] at hfix
      have h2 : w3 ^ (2 : ℤ) = w3 * w3 := by
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]
      rwa [h2] at hfix
    exact w3_moves_ch1.2 hfix2

theorem F24_center (h : Setting24 ι a) :
    ∀ x ∈ F24 ι a, (∀ f ∈ F24 ι a, x * f = f * x) → x = 1 := by
  intro x hxF hxcent
  have hxind : x ∈ indSub ι A5g := (mem_F24_iff.mp hxF).1
  obtain ⟨g, hg, hxg⟩ := mem_indSub.mp hxind
  have hg_center : ∀ k ∈ A5g, g * k = k * g := by
    intro k hk
    obtain ⟨f, hfF, hfg⟩ := exists_lift_F24 h hk
    have h1 : Induces ι (x * f) (g * k) := hxg.mul hfg
    have h2 : Induces ι (f * x) (k * g) := hfg.mul hxg
    have h3 : x * f = f * x := hxcent f hfF
    rw [h3] at h1
    exact Induces.unique h.inj h1 h2
  have hg1 : g = 1 := A5g_center_trivial g hg hg_center
  have hx1 : Induces ι x 1 := by
    rw [hg1] at hxg
    exact hxg
  obtain ⟨v, hv⟩ := Induces.exists_eq_coordElt (ι := ι) h.centralizer_le hx1
  have hvFix : v ∈ Fix3 := by
    rw [mem_Fix3]
    have hcomm_a : coordElt ι v * a = a * coordElt ι v := by
      rw [← hv]
      exact Subgroup.mem_centralizer_singleton_iff.mp (mem_F24_iff.mp hxF).2
    have haux : a * coordElt ι v * a⁻¹ = coordElt ι v := by
      rw [← hcomm_a]; group
    have h2 := h.a_induces v
    rw [haux] at h2
    exact (coordElt_injective h.inj h2).symm
  have hvfix_all : ∀ k ∈ A5g, k v = v := by
    intro k hk
    obtain ⟨f, hfF, hfg⟩ := exists_lift_F24 h hk
    have hxf : x * f = f * x := hxcent f hfF
    have hconj : f * coordElt ι v * f⁻¹ = coordElt ι v := by
      rw [← hv]
      have hfx : f * x = x * f := hxf.symm
      calc f * x * f⁻¹ = x * f * f⁻¹ := by rw [hfx]
        _ = x := by group
    have h1 := hfg v
    rw [hconj] at h1
    exact (coordElt_injective h.inj h1).symm
  have hv0 : v = 0 := A5g_no_fixed v hvFix hvfix_all
  rw [hv, hv0, coordElt_zero]

end CFSG.EvenSporadicStandard.HNRecog.Harada
