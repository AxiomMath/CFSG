module

public import CFSG.ClassicalInvolution.Asc77.AscT3SMain
public import CFSG.ClassicalInvolution.Asc77.AscT3UConj
public import CFSG.ClassicalInvolution.Asc77.AscT3ULayer
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpModel
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuModel
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RInnerSL
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Inner

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3U

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Pieces

variable {G : Type} [Group G]

theorem conjSub_closure_triple (h x y w : G) :
    conjSub h (Subgroup.closure ({x, y, w} : Set G)) =
      Subgroup.closure ({h * x * h⁻¹, h * y * h⁻¹, h * w * h⁻¹} : Set G) := by
  unfold conjSub
  rw [MonoidHom.map_closure]
  congr 1
  ext v
  simp [Set.image_insert_eq, MulAut.conj_apply]

theorem closure_triple_mul_right {z t a : G} (hz : z * z = 1) :
    Subgroup.closure ({z, t, a * z} : Set G) = Subgroup.closure ({z, t, a} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro v hv
    rcases hv with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  · rw [Subgroup.closure_le]
    intro v hv
    rcases hv with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · have h1 : v * z ∈ Subgroup.closure ({z, t, v * z} : Set G) :=
        Subgroup.subset_closure (by simp)
      have h2 : z ∈ Subgroup.closure ({z, t, v * z} : Set G) :=
        Subgroup.subset_closure (by simp)
      have := Subgroup.mul_mem _ h1 h2
      rwa [mul_assoc, hz, mul_one] at this

theorem exactCore_mul_eq {K : Subgroup G} {z a : G} (hKz : K ≤ Subgroup.centralizer ({z} : Set G)) :
    exactCore (a * z) K = exactCore a K := by
  have h : K ⊓ Subgroup.centralizer ({a * z} : Set G) = K ⊓ Subgroup.centralizer ({a} : Set G) := by
    ext k
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hk, h1⟩
      refine ⟨hk, ?_⟩
      have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp (hKz hk)
      have : k * a * z = a * k * z := by
        calc k * a * z = k * (a * z) := by group
          _ = (a * z) * k := h1
          _ = a * (z * k) := by group
          _ = a * (k * z) := by rw [hkz]
          _ = a * k * z := by group
      exact mul_right_cancel this
    · rintro ⟨hk, h1⟩
      refine ⟨hk, ?_⟩
      have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp (hKz hk)
      calc k * (a * z) = (k * a) * z := by group
        _ = (a * k) * z := by rw [h1]
        _ = a * (k * z) := by group
        _ = a * (z * k) := by rw [hkz]
        _ = (a * z) * k := by group
  unfold exactCore triangleResidual
  rw [h]

end Pieces

section TwinSmall

variable (p : ℕ) [Fact p.Prime]

theorem twinSmallInner_proved' : TwinSmallInner p :=
  twinSmallInner_of_rows (twinSmallInnerSp p) (twinSmallInnerSL p) (twinSmallInnerSU p)
    (G2D4Models.Twin.twinSmallInnerD4 p)

end TwinSmall

section Main

variable {p f : ℕ} [Fact p.Prime]


theorem res20_7Hyp51At_proved : Res20_7Hyp51At p f := by
  intro G _ _ _ K K' J S R R' W V z t d c4 a ha ha1 ha2
  have hp : p ≠ 2 := d.branch.odd
  have hq : 5 ≤ p ^ f := d.branch.five
  have hΩ := d.hyp
  have hBelow : CITBelowU p f (Nat.card G) := d.below f hq
  have hKΩ : K ∈ CoreAssembly.conjClass K := d.late_mem_K
  have hK'Ω : K' ∈ CoreAssembly.conjClass K := d.late_mem_K'
  have hzK : IsUniqueInvolution K z := d.viol.hzK
  have hzK' : IsUniqueInvolution K' z := d.late_hzK'
  have hcK : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hKΩ hzK
  have hcK' : IsClassicalMember p f K' z := isClassicalMember_of_twin hΩ hK'Ω hzK'
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := T7S22.le_centralizer_of_classical hcK
  have hK'z : K' ≤ Subgroup.centralizer ({z} : Set G) := T7S22.le_centralizer_of_classical hcK'
  have hMz : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) := sup_le hKz hK'z
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_twin hK'Ω hKΩ d.ne hzK' hzK
  have hKN' : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hKΩ hK'Ω d.ne.symm hzK hzK'
  have hz2 : z * z = 1 := hzK.sq
  have ht2 : t * t = 1 := d.viol.hzJ.sq
  have hzt : z * t = t * z := d.late_zt_comm
  have haz : a * z = z * a := d.s_comm_z ha.1.1
  have hat : a * t = t * a := d.s_comm_t ha
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one ha2
  have haK : a ∈ trivialOnQuot K :=
    ⟨d.cent_le_normalizer ha.1, fun l hl => d.s_comm_K ha hl⟩
  have haK' : a ∈ trivialOnQuot K' :=
    ⟨d.cent_le_normalizer' ha.1, fun l hl => d.s_comm_K' ha hl⟩
  have hzK_tq : z ∈ trivialOnQuot K := mem_trivialOnQuot_of_le_centralizer hKz
  have hzK'_tq : z ∈ trivialOnQuot K' := mem_trivialOnQuot_of_le_centralizer hK'z
  have hza : z ≠ a := fun e => d.s_a_not_mem_closure c4 ha ha1 (by
    rw [← e]
    exact Subgroup.subset_closure (by simp))
  have hz1 : z ≠ 1 := hzK.ne_one
  have ht1 : t ≠ 1 := d.viol.hzJ.ne_one
  have htz : t ≠ z := d.late_ne_inv
  obtain ⟨g, hgM, hga, hgt⟩ := exists_conj_mem_exactCore_sup hcK hcK' hc2 haK haK' hKN' hK'N
    d.htKK ht2 hat
  have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp (hMz hgM)
  have hgzg : g * z * g⁻¹ = z := by rw [hgz]; group
  have hgag : g * a * g⁻¹ = a := by rw [← hga]; group
  set t' : G := g * t * g⁻¹ with ht'def
  have ht'2 : t' * t' = 1 := by
    calc t' * t' = g * (t * t) * g⁻¹ := by rw [ht'def]; group
      _ = 1 := by rw [ht2]; group
  have hzt' : z * t' = t' * z := by
    calc z * t' = (g * z * g⁻¹) * (g * t * g⁻¹) := by rw [hgzg]
      _ = g * (z * t) * g⁻¹ := by group
      _ = g * (t * z) * g⁻¹ := by rw [hzt]
      _ = (g * t * g⁻¹) * (g * z * g⁻¹) := by group
      _ = t' * z := by rw [hgzg]
  have hat' : a * t' = t' * a := by
    calc a * t' = (g * a * g⁻¹) * (g * t * g⁻¹) := by rw [hgag]
      _ = g * (a * t) * g⁻¹ := by group
      _ = g * (t * a) * g⁻¹ := by rw [hat]
      _ = (g * t * g⁻¹) * (g * a * g⁻¹) := by group
      _ = t' * a := by rw [hgag]
  have ht'1 : t' ≠ 1 := fun e => ht1 (by
    have : t = g⁻¹ * t' * g := by rw [ht'def]; group
    rw [this, e]
    group)
  have ht'z : t' ≠ z := fun e => htz (by
    have : t = g⁻¹ * t' * g := by rw [ht'def]; group
    rw [this, e]
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * z) := by rw [hgz]
      _ = z := by group)
  have hB'ab : IsElemAbelian 2 (Subgroup.closure ({z, t', a} : Set G)) :=
    isElemAbelian_closure_three hz2 ht'2 ha2 hzt' haz.symm hat'.symm
  have hB : conjSub g (Subgroup.closure ({z, t, a} : Set G)) =
      Subgroup.closure ({z, t', a} : Set G) := by
    rw [conjSub_closure_triple, hgzg, hgag]
  have hzB : z ∈ Subgroup.closure ({z, t', a} : Set G) := Subgroup.subset_closure (by simp)
  have ht'B : t' ∈ Subgroup.closure ({z, t', a} : Set G) := Subgroup.subset_closure (by simp)
  have haB : a ∈ Subgroup.closure ({z, t', a} : Set G) := Subgroup.subset_closure (by simp)
  have hres := twinSmallInner_proved' p
  have hlift : ∀ c : G, g * c * g⁻¹ = c →
      Hyp51At (Subgroup.closure ({z, t', a} : Set G)) c →
        Hyp51At (Subgroup.closure ({z, t, a} : Set G)) c := fun c hc h =>
    (hyp51At_conj g c _).mp (by rw [hB, hc]; exact h)
  refine ⟨hlift a hgag ?_, hlift (a * z) ?_ ?_⟩
  · exact hyp51At_of_twin_layer hres hp hq hΩ hBelow hKΩ hK'Ω d.ne hzK hzK'
      ⟨hKΩ, haK⟩ ⟨hK'Ω, haK'⟩ hB'ab hzB ht'B haB rfl ha1 hza ht'1 ht'z ht'2 hgt
  · calc g * (a * z) * g⁻¹ = (g * a * g⁻¹) * (g * z * g⁻¹) := by group
      _ = a * z := by rw [hgag, hgzg]
  · have haz1 : a * z ≠ 1 := fun e => hza (by
      have h1 : a = z⁻¹ := eq_inv_of_mul_eq_one_left e
      rw [h1]
      exact (inv_eq_of_mul_eq_one_right hz2).symm)
    have hzaz : z ≠ a * z := fun e => ha1 (by
      have : a * z = 1 * z := by rw [← e, one_mul]
      exact mul_right_cancel this)
    have hazB : a * z ∈ Subgroup.closure ({z, t', a} : Set G) := Subgroup.mul_mem _ haB hzB
    have hdsup : t' ∈ exactCore (a * z) K ⊔ exactCore (a * z) K' := by
      rw [exactCore_mul_eq hKz, exactCore_mul_eq hK'z]
      exact hgt
    exact hyp51At_of_twin_layer hres hp hq hΩ hBelow hKΩ hK'Ω d.ne hzK hzK'
      ⟨hKΩ, (trivialOnQuot K).mul_mem haK hzK_tq⟩
      ⟨hK'Ω, (trivialOnQuot K').mul_mem haK' hzK'_tq⟩ hB'ab hzB ht'B hazB
      (closure_triple_mul_right hz2).symm haz1 hzaz ht'1 ht'z ht'2 hdsup

theorem t3CaseII_of_res10 (hP1 : Res10bP1 p f) (hY : Res10aY p f) : T3CaseII p f :=
  t3CaseII_of_hyp51At res20_7Hyp51At_proved hP1 hY

end Main


end CFSG.ClassicalInvolution.Asc77.T3CII.T3U
