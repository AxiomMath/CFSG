module

public import CFSG.ClassicalInvolution.AschTight.Sec7L713A

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem eq_of_le_sup (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) (h611 : EtaMeets Ω)
    (habel : EtaAbelian Ω) (h67 : RCommute Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {T T' : Subgroup G} (hT : T ∈ DSet Ω W) (hT' : T' ∈ DSet Ω W) (hle : T ≤ T' ⊔ W ⊔ OCW W)
    {L L' : Subgroup G} (hL : L ∈ Ω) (hL' : L' ∈ Ω) (hTL : T ≤ L) (hTL' : T' ≤ L') : L = L' := by
  have hW2 := isPGroup_of_mem_WSet hW
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    obtain ⟨η, hη, rfl⟩ := id hW
    exact habel η hη
  have hT2 := isPGroup_of_mem_RSet hT.1
  have hT'2 := isPGroup_of_mem_RSet hT'.1
  have hNX := normalizer_le_normalizer_OCW W
  have hB2 : IsPGroup 2 ↥(T' ⊔ W) := IsPGroup.to_sup_of_normal_right' hT'2 hW2 hT'.2
  have hBN : T' ⊔ W ≤ Subgroup.normalizer ((OCW W : Subgroup G) : Set G) :=
    sup_le (hT'.2.trans hNX) (Subgroup.le_normalizer.trans hNX)
  have hP₀ : T' ⊔ W ⊔ OCW W = OCW W ⊔ (T' ⊔ W) := sup_comm _ _
  have hcoe : ((OCW W ⊔ (T' ⊔ W) : Subgroup G) : Set G) =
      (OCW W : Set G) * ((T' ⊔ W : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBN
  have hBsyl : IsSylow2In (T' ⊔ W) (OCW W ⊔ (T' ⊔ W)) := by
    obtain ⟨P₁, hP₁, hBP₁⟩ := IsSylow2In.exists_ge hB2 (le_sup_right : T' ⊔ W ≤ OCW W ⊔ (T' ⊔ W))
    have hP₁B : P₁ ≤ T' ⊔ W := by
      intro y hy
      have hy' : y ∈ ((OCW W ⊔ (T' ⊔ W) : Subgroup G) : Set G) := hP₁.1 hy
      rw [hcoe] at hy'
      obtain ⟨x, hx, b, hb, rfl⟩ := hy'
      have hxP : x ∈ P₁ := by
        have : x = x * b * b⁻¹ := by group
        rw [this]
        exact P₁.mul_mem hy (P₁.inv_mem (hBP₁ hb))
      have hx1 : x = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hx
        (hP₁.2.1.to_le (Subgroup.zpowers_le.mpr hxP))
      show x * b ∈ T' ⊔ W
      rw [hx1, one_mul]
      exact hb
    rwa [le_antisymm hP₁B hBP₁] at hP₁
  obtain ⟨y, hy, hyB⟩ := exists_conj_le_of_isSylow2In hBsyl hT2 (hP₀ ▸ hle)
  have hy' : y ∈ ((OCW W ⊔ (T' ⊔ W) : Subgroup G) : Set G) := hy
  rw [hcoe] at hy'
  obtain ⟨x, hx, b, hb, rfl⟩ := hy'
  have hxB : conjSub (x * b) (T' ⊔ W) = conjSub x (T' ⊔ W) := by
    rw [conjSub_mul, conjSub_eq_self_of_mem hb]
  rw [hxB] at hyB
  have hxC : x ∈ Subgroup.centralizer (W : Set G) := oddCoreOf_le_self _ hx
  have hxW : conjSub x⁻¹ W = W :=
    mem_normalizer_iff_conjSub_eq.mp ((Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _
      hxC)))
  set T₁ := conjSub x⁻¹ T with hT₁def
  have hT₁B : T₁ ≤ T' ⊔ W := by
    rw [hT₁def, conjSub_le_iff, inv_inv]
    exact hyB
  have hT₁R : T₁ ∈ RSet Ω := RSet.conj hΩ.conjInvariant hT.1 x⁻¹
  obtain ⟨S', hS'⟩ := hB2.exists_le_sylow
  have hcen : ∀ w ∈ W, x * w * x⁻¹ = w := fun w hw => by
    have := (Subgroup.mem_centralizer_iff.mp hxC) w hw
    calc x * w * x⁻¹ = w * x * x⁻¹ := by rw [this]
      _ = w := by group
  obtain ⟨-, hTWU, hTcard, -⟩ := inf_W_of_mem_DSet hp hΩ h611 hW hT hL hTL
  obtain ⟨-, -, -, -, -, -, -, -, hTW4⟩ := hΩ.exists_data_of_mem_USet hp hTWU
  by_cases heq : T₁ = T'
  ·
    have hTW : T ⊓ W ≤ T' := by
      intro w hw
      rw [← heq, hT₁def, mem_conjSub_iff, inv_inv]
      rw [hcen w (Subgroup.mem_inf.mp hw).2]
      exact (Subgroup.mem_inf.mp hw).1
    exact hΩ.eq_of_le_of_le hL hL' (hT2.to_le inf_le_left) hTW4 (inf_le_left.trans hTL)
      (hTW.trans hTL')
  · exfalso
    have hc := h67 S' T₁ hT₁R T' hT'.1 (hT₁B.trans hS') (le_sup_left.trans hS') heq
    obtain ⟨-, hT'WU, hT'card, -⟩ := inf_W_of_mem_DSet hp hΩ h611 hW hT' hL' hTL'
    obtain ⟨-, -, -, -, -, -, hT'Wc, -, -⟩ := hΩ.exists_data_of_mem_USet hp hT'WU
    obtain ⟨t, htT, htW⟩ : ∃ t ∈ T, t ∉ W := by
      by_contra hcon
      push Not at hcon
      obtain ⟨a, ha, b', hb', hab⟩ := (hΩ.isQuatSub_of_mem_RSet hp hT.1).exists_not_commute
      exact hab (hWab a (hcon a ha) b' (hcon b' hb'))
    have hTN : T' ≤ Subgroup.normalizer ((W ⊔ OCW W : Subgroup G) : Set G) :=
      hT'.2.trans (normalizer_le_normalizer_sup_OCW W)
    have htm : t ∈ ((T' ⊔ (W ⊔ OCW W) : Subgroup G) : Set G) := by
      rw [← sup_assoc]
      exact hle htT
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTN] at htm
    obtain ⟨t', ht', h, hh, hth⟩ := htm
    have hhC : h ∈ Subgroup.centralizer (W : Set G) := sup_OCW_le_centralizer hWab hh
    have ht'W : t' ∉ W := by
      intro ht'W
      apply htW
      have h2 : IsPGroup 2 (Subgroup.zpowers t) := hT2.to_le (Subgroup.zpowers_le.mpr htT)
      refine mem_of_isPGroup_of_mem_sup_OCW hW2 ?_ h2
      rw [← hth]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht'W) hh
    have ht'n : t' ∉ T' ⊓ W := fun h' => ht'W (Subgroup.mem_inf.mp h').2
    have hnc : ¬ ∀ c ∈ T' ⊓ W, t' * c = c * t' := fun hall =>
      ht'n (mem_of_commute_of_index_two hp hΩ hT'.1 inf_le_left hT'Wc hT'card ht' hall)
    push Not at hnc
    obtain ⟨c, hc', hct⟩ := hnc
    have hcW : c ∈ W := (Subgroup.mem_inf.mp hc').2
    have ht₁ : x⁻¹ * t * x ∈ T₁ := by
      rw [hT₁def, mem_conjSub_iff, inv_inv]
      have e : x * (x⁻¹ * t * x) * x⁻¹ = t := by group
      rw [e]
      exact htT
    have h1 := hc _ ht₁ c (Subgroup.mem_inf.mp hc').1
    have hhc : h * c = c * h := ((Subgroup.mem_centralizer_iff.mp hhC) c hcW).symm
    apply hct
    have hxc : x * c * x⁻¹ = c := hcen c hcW
    have hconj : (x⁻¹ * t * x) * c * (x⁻¹ * t * x)⁻¹ = t' * c * t'⁻¹ := by
      have hc2 : x * c = c * x := by
        calc x * c = x * c * x⁻¹ * x := by group
          _ = c * x := by rw [hxc]
      have hc3 : x * (t' * c * t'⁻¹) * x⁻¹ = t' * c * t'⁻¹ := by
        refine hcen _ ?_
        exact (Subgroup.mem_normalizer_iff.mp (hT'.2 ht') c).mp hcW
      calc (x⁻¹ * t * x) * c * (x⁻¹ * t * x)⁻¹ = x⁻¹ * (t * (x * c * x⁻¹) * t⁻¹) * x := by group
        _ = x⁻¹ * (t * c * t⁻¹) * x := by rw [hxc]
        _ = x⁻¹ * (t' * (h * c * h⁻¹) * t'⁻¹) * x := by rw [← hth]; group
        _ = x⁻¹ * (t' * c * t'⁻¹) * x := by
          rw [show h * c * h⁻¹ = c by rw [hhc]; group]
        _ = x⁻¹ * (x * (t' * c * t'⁻¹) * x⁻¹) * x := by rw [hc3]
        _ = t' * c * t'⁻¹ := by group
    have hfix : (x⁻¹ * t * x) * c * (x⁻¹ * t * x)⁻¹ = c := by
      rw [h1]
      group
    rw [hconj] at hfix
    calc t' * c = t' * c * t'⁻¹ * t' := by group
      _ = c * t' := by rw [hfix]

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
