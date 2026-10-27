module

public import CFSG.ClassicalInvolution.Q3.Q3T6BExact
public import CFSG.ClassicalInvolution.Q3.Q3T6BLAut
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Uniform.U4
open CFSG.ClassicalInvolution.Q3.Q3T6B (ExAt exAt_conj)
open scoped commutatorElement

section Act

variable {F : Type} [Group F] [Finite F]

@[expose] def actTriv (δ : F) : Subgroup F where
  carrier := {g | g * δ = δ * g ∧
    ∀ I : Subgroup F, Mem3 I δ → g ∈ Subgroup.normalizer (I : Set F)}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, fun I hI => (Subgroup.normalizer (I : Set F)).mul_mem (ha2 I hI) (hb2 I hI)⟩
    calc a * b * δ = a * (b * δ) := by group
      _ = a * (δ * b) := by rw [hb1]
      _ = (a * δ) * b := by group
      _ = (δ * a) * b := by rw [ha1]
      _ = δ * (a * b) := by group
  one_mem' := ⟨by group, fun I _ => (Subgroup.normalizer (I : Set F)).one_mem⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    exact ⟨(Commute.inv_left (show Commute a δ from ha1)).eq,
      fun I hI => (Subgroup.normalizer (I : Set F)).inv_mem (ha2 I hI)⟩

theorem mem_actTriv_iff {δ g : F} : g ∈ actTriv δ ↔
    g * δ = δ * g ∧ ∀ I : Subgroup F, Mem3 I δ → g ∈ Subgroup.normalizer (I : Set F) :=
  Iff.rfl

theorem actTriv_conj_mem {δ c g : F} (hc : c * δ = δ * c) (hg : g ∈ actTriv δ) :
    c * g * c⁻¹ ∈ actTriv δ := by
  obtain ⟨hg1, hg2⟩ := mem_actTriv_iff.mp hg
  refine mem_actTriv_iff.mpr ⟨?_, fun I hI => ?_⟩
  · calc c * g * c⁻¹ * δ = c * g * (c⁻¹ * δ) := by group
      _ = c * g * (δ * c⁻¹) := by rw [(Commute.inv_left (show Commute c δ from hc)).eq]
      _ = c * (g * δ) * c⁻¹ := by group
      _ = c * (δ * g) * c⁻¹ := by rw [hg1]
      _ = (c * δ) * g * c⁻¹ := by group
      _ = (δ * c) * g * c⁻¹ := by rw [hc]
      _ = δ * (c * g * c⁻¹) := by group
  · have hI' : Mem3 (conjSub c⁻¹ I) δ := hI.conj_of_commute (inv_comm_of_comm hc)
    have h1 : conjSub g (conjSub c⁻¹ I) = conjSub c⁻¹ I :=
      conjSub_eq_of_mem_normalizer (hg2 _ hI')
    apply AscHypOmega.mem_normalizer_of_conjSub_eq
    calc conjSub (c * g * c⁻¹) I = conjSub c (conjSub g (conjSub c⁻¹ I)) := by
          rw [conjSub_mul, conjSub_mul]
      _ = I := by rw [h1, conjSub_conjSub_inv]

theorem exists_three_sq_elements {J : Subgroup F} {t : F} (hJ : Mem3 J t) :
    ∃ a₁ ∈ J, ∃ a₂ ∈ J, a₁ * a₁ = t ∧ a₂ * a₂ = t ∧ (a₁ * a₂) * (a₁ * a₂) = t := by
  obtain ⟨V, hV⟩ := exists_isSylow2In J
  obtain ⟨a₁, ha₁, a₂, ha₂, h1, h2, h12⟩ := hJ.exists_two_sq_elements hV
  have ha₁₂ : a₁ * a₂ ∈ V := V.mul_mem ha₁ ha₂
  have hpg : IsPGroup 2 (Subgroup.zpowers (a₁ * a₂)) :=
    hV.2.1.to_le (Subgroup.zpowers_le.mpr ha₁₂)
  have h4 : (a₁ * a₂) ^ 4 = 1 := hJ.pow_four_of_isPGroup (hV.1 ha₁₂) hpg
  have hsq : ((a₁ * a₂) * (a₁ * a₂)) * ((a₁ * a₂) * (a₁ * a₂)) = 1 := by
    simpa [pow_succ, mul_assoc] using h4
  rcases hJ.isUniqueInvolution.unique _ (J.mul_mem (hV.1 ha₁₂) (hV.1 ha₁₂)) hsq with h | h
  · exact absurd h h12
  · exact ⟨a₁, hV.1 ha₁, a₂, hV.1 ha₂, h1, h2, h⟩

theorem exists_conj_of_twin_pairs {K K' : Subgroup F} {z : F} (hK : Mem3 K z)
    (hK' : Mem3 K' z) (hne : K ≠ K') {a κ b κ' : F} (ha : a ∈ K) (hκ : κ ∈ K)
    (hb : b ∈ K') (hκ' : κ' ∈ K') (ha2 : a * a = z) (hb2 : b * b = z) (hab : a * b = b * a)
    (hκ2 : κ * κ = z) (hκ'2 : κ' * κ' = z) (hκκ' : κ * κ' = κ' * κ) :
    ∃ w : F, w * (a * b) * w⁻¹ = κ * κ' := by
  classical
  obtain ⟨g, hgK, hg⟩ := hK.exists_conj_in_member hκ ha hκ2 ha2
  obtain ⟨g', hg'K', hg'⟩ := hK'.exists_conj_in_member hκ' hb hκ'2 hb2
  obtain ⟨hK'N, hKN', -⟩ := hK.twin_facts hK' hne
  set M : Subgroup F := K ⊔ K' with hM
  have hKM : K ≤ M := le_sup_left
  have hK'M : K' ≤ M := le_sup_right
  set N : Subgroup F := oddCoreOf M with hN
  have hMN : ∀ m ∈ M, m ∈ Subgroup.normalizer (N : Set F) := fun m hm =>
    AscFusion.mem_normalizer_oddCoreOf_of_mem_normalizer' (Subgroup.le_normalizer hm)
  have hOK : oddCoreOf K ≤ N := by
    refine AscFusion.le_oddCoreOf_of_normal_odd ((oddCoreOf_le_self K).trans hKM) ?_
      (oddCoreOf_odd_natCard K)
    refine sup_le ?_ ?_
    · exact fun m hm =>
        AscFusion.mem_normalizer_oddCoreOf_of_mem_normalizer' (Subgroup.le_normalizer hm)
    · exact fun m hm => AscFusion.mem_normalizer_oddCoreOf_of_mem_normalizer' (hK'N hm)
  have hcN : ∀ u ∈ K, ∀ w ∈ K', ⁅u, w⁆ ∈ N := fun u hu w hw => by
    rw [← commutatorElement_inv]
    exact N.inv_mem (hOK (hK.commutator_mem_of_twin hK' hne hw u hu))
  have hcN' : ∀ w ∈ K', ∀ u ∈ K, ⁅w, u⁆ ∈ N := fun w hw u hu =>
    hOK (hK.commutator_mem_of_twin hK' hne hw u hu)
  set x : F := g * g' with hx
  set y : F := x * (κ * κ') * x⁻¹ with hy
  set c₁ : F := g' * κ * g'⁻¹ * κ⁻¹ with hc₁
  set c₂ : F := g * b * g⁻¹ * b⁻¹ with hc₂
  have hc₁N : c₁ ∈ N := by
    have : c₁ = ⁅g', κ⁆ := by rw [hc₁, commutatorElement_def]
    rw [this]
    exact hcN' g' hg'K' κ hκ
  have hc₂N : c₂ ∈ N := by
    have : c₂ = ⁅g, b⁆ := by rw [hc₂, commutatorElement_def]
    rw [this]
    exact hcN g hgK b hb
  have hgM : g ∈ M := hKM hgK
  have haM : a ∈ M := hKM ha
  have hbM : b ∈ M := hK'M hb
  have hy' : y = (g * c₁ * g⁻¹) * a * c₂ * b := by
    have e1 : g' * κ' * g'⁻¹ = b := hg'
    have e2 : g * κ * g⁻¹ = a := hg
    calc y = g * (g' * κ * g'⁻¹) * (g' * κ' * g'⁻¹) * g⁻¹ := by rw [hy, hx]; group
      _ = g * (c₁ * κ) * b * g⁻¹ := by
        rw [e1]
        congr 3
        rw [hc₁]
        group
      _ = (g * c₁ * g⁻¹) * (g * κ * g⁻¹) * (g * b * g⁻¹) := by group
      _ = (g * c₁ * g⁻¹) * a * c₂ * b := by
        rw [e2]
        have : g * b * g⁻¹ = c₂ * b := by rw [hc₂]; group
        rw [this]
        group
  have hn1 : g * c₁ * g⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hMN g hgM) c₁).mp hc₁N
  have hn2 : a⁻¹ * (g * c₁ * g⁻¹) * a ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (hMN a⁻¹ (M.inv_mem haM)) (g * c₁ * g⁻¹)).mp hn1
    simpa using this
  have hn3 : b⁻¹ * ((a⁻¹ * (g * c₁ * g⁻¹) * a) * c₂) * b ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (hMN b⁻¹ (M.inv_mem hbM)) _).mp
      (N.mul_mem hn2 hc₂N)
    simpa using this
  have hxy : (a * b)⁻¹ * y ∈ N := by
    have : (a * b)⁻¹ * y = b⁻¹ * ((a⁻¹ * (g * c₁ * g⁻¹) * a) * c₂) * b := by
      rw [hy']
      group
    rw [this]
    exact hn3
  have hab2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2]; exact hK.mul_self
  have hδ2 : (κ * κ') * (κ * κ') = 1 := by
    calc (κ * κ') * (κ * κ') = κ * (κ' * κ) * κ' := by group
      _ = κ * (κ * κ') * κ' := by rw [← hκκ']
      _ = (κ * κ) * (κ' * κ') := by group
      _ = 1 := by rw [hκ2, hκ'2]; exact hK.mul_self
  have hy2 : y * y = 1 := by
    calc y * y = x * ((κ * κ') * (κ * κ')) * x⁻¹ := by rw [hy]; group
      _ = 1 := by rw [hδ2]; group
  have hxt : IsPGroup 2 (Subgroup.zpowers (a * b)) :=
    AscFusion.isPGroup_zpowers_of_sq_sq (by rw [hab2]; group)
  have hyt : IsPGroup 2 (Subgroup.zpowers y) :=
    AscFusion.isPGroup_zpowers_of_sq_sq (by rw [hy2]; group)
  obtain ⟨h, -, hh⟩ := AscFusion.exists_conj_of_odd_coset (oddCoreOf_odd_natCard M) hxt hyt
    (hMN (a * b) (M.mul_mem haM hbM)) hxy
  refine ⟨x⁻¹ * h, ?_⟩
  calc (x⁻¹ * h) * (a * b) * (x⁻¹ * h)⁻¹ = x⁻¹ * (h * (a * b) * h⁻¹) * x := by group
    _ = x⁻¹ * y * x := by rw [hh]
    _ = κ * κ' := by rw [hy]; group

variable [IsSimpleGroup F]

end Act

end CFSG.ClassicalInvolution.Q3.Q3T6R
