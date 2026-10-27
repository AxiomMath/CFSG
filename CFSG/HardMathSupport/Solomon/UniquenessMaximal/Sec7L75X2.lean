module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75Ctx
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsA
public import CFSG.LocalAnalysis.GLTheoremB.LayerTools

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Components

variable {Q : Type*} [Group Q]

private theorem isSubnormal_top_of_normal' {F : Subgroup Q} (hF : F.Normal) : IsSubnormal F ⊤ :=
  IsSubnormal.step le_top (hF.subgroupOf ⊤) (IsSubnormal.refl ⊤)

theorem isSubnormal_sup_three_components [Finite Q] {X₁ X₂ X₃ : Subgroup Q}
    (h₁ : IsComponentOf X₁ ⊤) (h₂ : IsComponentOf X₂ ⊤) (h₃ : IsComponentOf X₃ ⊤) :
    IsSubnormal (X₁ ⊔ X₂ ⊔ X₃) ⊤ := by
  have hAE : X₁ ⊔ X₂ ⊔ X₃ ≤ CFSG.ComponentClassification.Layer.subgroup Q :=
    sup_le (sup_le (CFSG.ComponentClassification.Layer.component_le h₁)
      (CFSG.ComponentClassification.Layer.component_le h₂))
      (CFSG.ComponentClassification.Layer.component_le h₃)
  have hEN : CFSG.ComponentClassification.Layer.subgroup Q ≤
      Subgroup.normalizer ((X₁ ⊔ X₂ ⊔ X₃ : Subgroup Q) : Set Q) := by
    refine sSup_le fun K hK => ?_
    by_cases hKX : K = X₁ ∨ K = X₂ ∨ K = X₃
    · have : K ≤ X₁ ⊔ X₂ ⊔ X₃ := by
        rcases hKX with h | h | h <;> rw [h]
        · exact le_sup_left.trans le_sup_left
        · exact le_sup_right.trans le_sup_left
        · exact le_sup_right
      exact this.trans Subgroup.le_normalizer
    · push Not at hKX
      obtain ⟨n1, n2, n3⟩ := hKX
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer ((X₁ ⊔ X₂ ⊔ X₃ : Subgroup Q) : Set Q))
      refine Subgroup.le_centralizer_iff.2 (sup_le (sup_le ?_ ?_) ?_)
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
          (CFSG.ComponentClassification.LocalComponents.commute_of_ne X₁ K h₁ hK (Ne.symm n1))
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
          (CFSG.ComponentClassification.LocalComponents.commute_of_ne X₂ K h₂ hK (Ne.symm n2))
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
          (CFSG.ComponentClassification.LocalComponents.commute_of_ne X₃ K h₃ hK (Ne.symm n3))
  have hEA : IsSubnormal (X₁ ⊔ X₂ ⊔ X₃) (CFSG.ComponentClassification.Layer.subgroup Q) :=
    IsSubnormal.step hAE ((Subgroup.normal_subgroupOf_iff_le_normalizer hAE).2 hEN)
      (IsSubnormal.refl _)
  exact isSubnormal_trans' hEA
    (isSubnormal_top_of_normal' (CFSG.ComponentClassification.Layer.normal Q))

theorem centralizer_zpowers_eq_singleton (y : Q) :
    Subgroup.centralizer ((Subgroup.zpowers y : Subgroup Q) : Set Q) =
      Subgroup.centralizer ({y} : Set Q) := by
  rw [Subgroup.zpowers_eq_closure]
  exact Subgroup.centralizer_closure _

end Components

section Quotient

variable {G : Type} [Group G]

theorem mkN_mem_barX {N T : Subgroup G} {a : G} (ha : a ∈ N) (haT : a ∈ T) :
    mkN N a ha ∈ barX 3 N T :=
  Subgroup.mem_map.2 ⟨⟨a, ha⟩, Subgroup.mem_subgroupOf.2 haT, rfl⟩

theorem exists_mem_of_mem_barX {N A : Subgroup G} {b : ↥N ⧸ GLAPPrimeCore 3 ↥N}
    (hb : b ∈ barX 3 N A) : ∃ (a : G) (ha : a ∈ N), a ∈ A ∧ b = mkN N a ha := by
  obtain ⟨⟨a, ha⟩, hmem, h⟩ := Subgroup.mem_map.1 hb
  exact ⟨a, ha, Subgroup.mem_subgroupOf.1 hmem, h.symm⟩

theorem barX_sup {N A B : Subgroup G} (hA : A ≤ N) (hB : B ≤ N) :
    barX 3 N (A ⊔ B) = barX 3 N A ⊔ barX 3 N B := by
  simp only [barX, Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

private theorem mkN_mul' {N : Subgroup G} {a b : G} (ha : a ∈ N) (hb : b ∈ N) :
    mkN N (a * b) (N.mul_mem ha hb) = mkN N a ha * mkN N b hb := rfl

private theorem mkN_inv' {N : Subgroup G} {a : G} (ha : a ∈ N) :
    mkN N a⁻¹ (N.inv_mem ha) = (mkN N a ha)⁻¹ := rfl

private theorem mkN_zpow' {N : Subgroup G} {a : G} (ha : a ∈ N) (k : ℤ) :
    mkN N (a ^ k) (N.zpow_mem ha k) = mkN N a ha ^ k := rfl

private theorem exists_mkN {N : Subgroup G} (z : ↥N ⧸ GLAPPrimeCore 3 ↥N) :
    ∃ (y : G) (hy : y ∈ N), z = mkN N y hy := by
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective z
  exact ⟨y, hy, rfl⟩

theorem barX_gLBConj_mk {N : Subgroup G} {x : G} (hx : x ∈ N) (L : Subgroup G) :
    barX 3 N (GLBConj x L) = GLBConj (mkN N x hx) (barX 3 N L) := by
  ext z
  obtain ⟨y, hy, rfl⟩ := exists_mkN z
  rw [mem_gLBConj]
  have hconj : mkN N x hx * mkN N y hy * (mkN N x hx)⁻¹ =
      mkN N (x * y * x⁻¹) (N.mul_mem (N.mul_mem hx hy) (N.inv_mem hx)) := rfl
  rw [hconj]
  constructor
  · intro h
    obtain ⟨a, ha, haL, hya⟩ := exists_mem_of_mem_barX h
    have hxa : x * a * x⁻¹ ∈ L := (mem_gLBConj ..).1 haL
    have hmk : mkN N (x * y * x⁻¹) (N.mul_mem (N.mul_mem hx hy) (N.inv_mem hx)) =
        mkN N (x * a * x⁻¹) (N.mul_mem (N.mul_mem hx ha) (N.inv_mem hx)) := by
      rw [← hconj, hya]; rfl
    rw [hmk]
    exact mkN_mem_barX _ hxa
  · intro h
    obtain ⟨a, ha, haL, hya⟩ := exists_mem_of_mem_barX h
    have hxa : x⁻¹ * a * x ∈ N := N.mul_mem (N.mul_mem (N.inv_mem hx) ha) hx
    have hmem : x⁻¹ * a * x ∈ GLBConj x L := by
      rw [mem_gLBConj]; convert haL using 1; group
    have hmk : mkN N y hy = mkN N (x⁻¹ * a * x) hxa := by
      have h1 : mkN N (x⁻¹ * a * x) hxa =
          (mkN N x hx)⁻¹ * mkN N a ha * mkN N x hx := rfl
      rw [h1, ← hya, ← hconj]
      group
    rw [hmk]
    exact mkN_mem_barX _ hmem

private theorem barX_zpowers {N : Subgroup G} {x : G} (hx : x ∈ N) :
    barX 3 N (Subgroup.zpowers x) = Subgroup.zpowers (mkN N x hx) := by
  ext b
  constructor
  · intro hb
    obtain ⟨a, ha, haA, rfl⟩ := exists_mem_of_mem_barX hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 haA
    exact Subgroup.mem_zpowers_iff.2 ⟨k, (mkN_zpow' hx k).symm⟩
  · intro hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have := mkN_mem_barX (N := N) (T := Subgroup.zpowers x) (N.zpow_mem hx k)
      (Subgroup.zpow_mem_zpowers x k)
    rwa [mkN_zpow'] at this

private theorem isPGroup_zpowers_three {x : G} (hx3 : x ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · refine IsPGroup.of_card (n := 0) ?_
    rw [Nat.card_zpowers, h]; rfl
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, h]; rfl

variable [Finite G] in
theorem centralizer_mkN_singleton {N : Subgroup G} {x : G} (hx : x ∈ N) (hx3 : x ^ 3 = 1) :
    Subgroup.centralizer ({mkN N x hx} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) =
      barX 3 N (N ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hle : Subgroup.zpowers x ≤ N := (Subgroup.zpowers_le).2 hx
  have h := centralizer_barX_eq Nat.prime_three hle (isPGroup_zpowers_three hx3)
  rw [barX_zpowers hx, centralizer_zpowers_eq_singleton (mkN N x hx),
    centralizer_zpowers_eq_singleton x] at h
  exact h

end Quotient

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
