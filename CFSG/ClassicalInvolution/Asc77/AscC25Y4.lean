module

public import CFSG.ClassicalInvolution.Asc77.AscC25Y3
public import CFSG.ClassicalInvolution.Asc77.AscC25Y2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace C25Y

section Four

variable {G : Type} [Group G]

theorem mem_closure_pair {a z : G} (ha2 : a * a = 1) (hz2 : z * z = 1) (haz : a * z = z * a)
    {b : G} (hb : b ∈ Subgroup.closure ({a, z} : Set G)) :
    b = 1 ∨ b = a ∨ b = z ∨ b = a * z := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have h1 : z * a = a * z := haz.symm
  have h2 : a * (a * z) = z := by rw [← mul_assoc, ha2, one_mul]
  have h5 : (a * z) * z = a := by rw [mul_assoc, hz2, mul_one]
  have h3 : z * (a * z) = a := by
    calc z * (a * z) = (z * a) * z := (mul_assoc z a z).symm
      _ = (a * z) * z := by rw [h1]
      _ = a := h5
  have h4 : (a * z) * a = z := by rw [haz, mul_assoc, ha2, mul_one]
  have h6 : (a * z) * (a * z) = 1 := by
    calc (a * z) * (a * z) = a * (z * a) * z := by group
      _ = a * (a * z) * z := by rw [h1]
      _ = (a * a) * (z * z) := by group
      _ = 1 := by rw [ha2, hz2, one_mul]
  induction hb using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact Or.inr (Or.inl rfl)
    · rw [Set.mem_singleton_iff] at hx
      exact Or.inr (Or.inr (Or.inl hx))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
      simp [ha2, hz2, h1, h2, h3, h4, h5, h6]
  | inv x _ hx =>
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · simp
    · simp [hai]
    · simp [hzi]
    · right; right; right
      rw [mul_inv_rev, hai, hzi, h1]

theorem eq_four_of_card_le_four [Finite G] {A : Subgroup G} {a z : G}
    (hcard : Nat.card A ≤ 4) (ha2 : a * a = 1) (hz2 : z * z = 1) (ha1 : a ≠ 1) (hz1 : z ≠ 1)
    (haz : a ≠ z) (hcomm : a * z = z * a) (haA : a ∈ A) (hzA : z ∈ A) :
    ∀ b ∈ A, b = 1 ∨ b = a ∨ b = z ∨ b = a * z := by
  have hE := T7A.isElemAbelian2_closure_pair ha2 hz2 ha1 hz1 haz hcomm
  have hle : Subgroup.closure ({a, z} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact haA
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hzA
  have hc : Nat.card ↥(Subgroup.closure ({a, z} : Set G)) = 4 := by
    rw [hE.1]; norm_num
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hc]; exact hcard)
  intro b hb
  rw [← heq] at hb
  exact mem_closure_pair ha2 hz2 hcomm hb

end Four

section Model

variable {G : Type} [Group G]

theorem layerAut_involutive (Y : Subgroup G) {b : G} (hb : conjSub b Y = Y) (hb2 : b * b = 1)
    (x : ↥Y ⧸ classicalInvolutionOddCore ↥Y) : layerAut Y hb (layerAut Y hb x) = x := by
  refine QuotientGroup.induction_on x fun x => ?_
  rw [layerAut_mk, layerAut_mk]
  congr 1
  apply Subtype.ext
  show b * (b * (x : G) * b⁻¹) * b⁻¹ = x
  calc b * (b * (x : G) * b⁻¹) * b⁻¹ = (b * b) * (x : G) * (b * b)⁻¹ := by group
    _ = x := by rw [hb2]; group

end Model

section ModelFact

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Layer6Cen4 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (D : LieSystemData p f Y Φ)
    (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    D.card = 1 → (∃ i : Fin D.card, IsOrthTag 6 (!piSign p f) (D.tag i) (D.rank i)) →
    TwinSect0 Φ A A' z' a₀ b₀ → (∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) →
    ∀ β : Y ≃* Y, (∀ x : Y, β (β x) = x) →
      ∃ J ∈ Φ, ∃ y ∈ J, y * y * y * y = 1 ∧ y * y ≠ 1 ∧ β y = y

end ModelFact

section Six

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}



theorem not_layerOrthSix (hM6 : Layer6Cen4 p f) (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z)
    (haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    (hA0 : ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      b = 1 ∨ b = a ∨ b = z ∨ b = a * z) :
    ¬ LayerOrthType p f Ω a 6 (!piSign p f) := by
  classical
  intro hL
  obtain ⟨t', n, hT, D, hD1, i₀, hDt, hDn⟩ := hL
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hcent := Subgroup.mem_centralizer_iff.mp haA.2
  have haR : ∀ x ∈ R, a * x = x * a := fun x hx => (hcent x (Subgroup.mem_sup_left hx)).symm
  have haR' : ∀ x ∈ R', a * x = x * a := fun x hx => (hcent x (Subgroup.mem_sup_right hx)).symm
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', hgen, hlt, htw⟩ :=
    C25X.layer_a_frame hyp ha2 ha1 haR haR'
  have hnGF := not_goodFusion hyp ha2 ha1 haz haA hconj hA0
  unfold GoodFusion at hnGF
  push Not at hnGF
  obtain ⟨w, hwC, hw⟩ := hnGF
  have hb2 : (w * z * w⁻¹) * (w * z * w⁻¹) = 1 := by
    calc (w * z * w⁻¹) * (w * z * w⁻¹) = w * (z * z) * w⁻¹ := by group
      _ = 1 := by rw [hs.hz.sq]; group
  have hbY : conjSub (w * z * w⁻¹) (exactLayer Ω a) = exactLayer Ω a :=
    conjSub_exactLayer hΩ.conjInvariant hwC
  have htag : t' = .PSL ∨ t' = .PSU := by
    rcases hT with ⟨h5, _⟩ | ⟨_, _, ht, _⟩ | ⟨_, _, ht, _⟩ | ⟨h7, _⟩ | ⟨h8, _⟩ | ⟨h8, _⟩
    · omega
    · exact Or.inl ht
    · exact Or.inr ht
    · omega
    · omega
    · omega
  have hD4 : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
    intro i
    have hi : i = i₀ := Fin.ext (by have h1 := i.2; have h2 := i₀.2; omega)
    subst hi
    rw [hDt]
    rcases htag with rfl | rfl <;> simp
  have hΦ : ∀ J ∈ oddQuotientFamily (exactPair Ω a), ∀ y : ↥(exactLayer Ω a) ⧸
      classicalInvolutionOddCore ↥(exactLayer Ω a),
      conjSub y J ∈ oddQuotientFamily (exactPair Ω a) := by
    intro J hJ yb
    obtain ⟨M, hMtq, rfl⟩ := T7H.exists_exactImg_of_mem hJ
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective yb
    rw [← exactImg_conjSub_layer x]
    exact T7H.exactImg_mem (conjSub_mem_tqMembers hΩ.conjInvariant
      (exactLayer_le_centralizer Ω a x.2) hMtq)
  obtain ⟨J, hJ, y, hyJ, hy4, hy2, hβy⟩ := hM6 _ _ D _ _ _ _ _ hD1
    ⟨i₀, by rw [hDt, hDn]; exact hT⟩ htw hΦ (layerAut (exactLayer Ω a) hbY)
    (layerAut_involutive _ hbY hb2)
  obtain ⟨M, hM, hMb⟩ := nc4_lift hyp ha2 hwC hJ hyJ hy4 hy2 hβy
  obtain ⟨h, hhC, hh⟩ := exists_centralizer_conj_of_member hyp ha2 hzY hK₂ D hD1 hD4 hM hMb
  exact hw h hhC hh

end Six

end C25Y

end CFSG.ClassicalInvolution.Asc77
