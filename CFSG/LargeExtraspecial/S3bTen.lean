module

public import CFSG.LargeExtraspecial.S3bTenC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2

universe u

@[expose] def WeaklyClosedTITransitive : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (A : Subgroup X),
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x ^ 2 = 1) →
    (∀ g : X, A.map (MulAut.conj g).toMonoidHom = A ∨
      A ⊓ A.map (MulAut.conj g).toMonoidHom = ⊥) →
    IsWeaklyClosedInNormalizer A → CFSG.pCore 2 X = ⊥ →
    ∀ x ∈ A, x ≠ 1 → ∀ y ∈ A, y ≠ 1 → ∃ n ∈ normalizer (A : Set X), n * x * n⁻¹ = y

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem conj_mem_QG_inf_Qa_of_fix {g m w : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hm : m ∈ S.M)
    (hma : m * (g * S.z * g⁻¹) * m⁻¹ = g * S.z * g⁻¹ ∨
      m * (g * S.z * g⁻¹) * m⁻¹ = g * S.z * g⁻¹ * S.z) (hw : w ∈ S.QG ⊓ S.Qa g) :
    m * w * m⁻¹ ∈ S.QG ⊓ S.Qa g := by
  have hX : S.QG ⊓ S.Qa (m * g) = S.QG ⊓ S.Qa g := by
    rcases hma with h | h
    · rw [S.Qa_eq_of_conj_eq (show (m * g) * S.z * (m * g)⁻¹ = g * S.z * g⁻¹ by
        rw [← h]; group)]
    · exact S.QG_inf_Qa_eq_of_conj_eq_mul_z haQ hne (by rw [← h]; group)
  rw [← hX]
  exact ⟨S.conj_mem_QG hm hw.1, S.conj_mem_Qa_mul hw.2⟩

theorem false_of_weaklyClosedTITransitive (hTI : WeaklyClosedTITransitive.{u})
    (hn : 3 ≤ S.width) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hno : ¬ S.HasTypeAInL g) (hle : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ≤ 2 ^ S.width)
    (hP9 : ∀ h ∈ S.M, g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
      (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹) →
      (h * g) * S.z * (h * g)⁻¹ = g * S.z * g⁻¹ ∨
        (h * g) * S.z * (h * g)⁻¹ = g * S.z * g⁻¹ * S.z) : False := by
  classical
  have h2 : 2 ≤ S.width := by omega
  obtain ⟨h4, hcard⟩ := S.card_Abar_eq_four haQ hne hno hle
  set A := (S.Lbar g).subgroupOf S.Mbar with hA
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    Subtype.ext (S.Lbar_comm haQ (mem_subgroupOf.mp hx) (mem_subgroupOf.mp hy))
  have hsqA : ∀ x ∈ A, x ^ 2 = 1 := fun x hx =>
    Subtype.ext (by simpa using S.sq_eq_one_of_mem_Lbar haQ (mem_subgroupOf.mp hx))
  have hTIA : ∀ mb : S.Mbar, A.map (MulAut.conj mb).toMonoidHom = A ∨
      A ⊓ A.map (MulAut.conj mb).toMonoidHom = ⊥ := by
    intro mb
    obtain ⟨⟨h, hh⟩, hmh⟩ := MonoidHom.mem_range.mp mb.2
    rw [hA, S.map_conj_Lbar_subgroupOf hh mb hmh]
    by_cases hL : S.Lbar (h * g) = S.Lbar g
    · left
      rw [hL]
    · right
      have e : (S.Lbar g).subgroupOf S.Mbar ⊓ (S.Lbar (h * g)).subgroupOf S.Mbar =
          (S.Lbar g ⊓ S.Lbar (h * g)).subgroupOf S.Mbar := by
        ext x
        simp only [mem_inf, mem_subgroupOf]
      rw [e, S.Lbar_inf_eq_bot haQ hne hP9 hh hL, bot_subgroupOf]
  have hwc := S.isWeaklyClosedInNormalizer_Lbar h2 haQ hne hno
  obtain ⟨t, ht, ht1⟩ := exists_mem_not_mem_finset_of_card_lt (H := S.Abar g) {1}
    (by rw [Finset.card_singleton]; omega)
  simp only [Finset.mem_singleton] at ht1
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g (S.Abar_le_Lbar haQ hne ht)
  have htA : (⟨t, htM⟩ : S.Mbar) ∈ A := mem_subgroupOf.mpr (S.Abar_le_Lbar haQ hne ht)
  have ht1' : (⟨t, htM⟩ : S.Mbar) ≠ 1 := fun h' => ht1 (congrArg Subtype.val h')
  have hL0C : S.L0 g ≤ S.CQa g := by
    intro y hy
    have hyM := S.L0_le_M g hy
    have hfixW : ∀ w ∈ S.QG ⊓ S.Qa g, (S.ρ ⟨y, hyM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl w) =
        S.cl w := by
      by_cases hy1 : S.ρ ⟨y, hyM⟩ = 1
      · intro w _
        rw [hy1]
        rfl
      have hyA : (⟨S.ρ ⟨y, hyM⟩, S.Lbar_le_Mbar g (S.ρ_mem_Lbar hy)⟩ : S.Mbar) ∈ A :=
        mem_subgroupOf.mpr (S.ρ_mem_Lbar hy)
      obtain ⟨n, hnN, hnt⟩ := hTI S.Mbar A hcommA hsqA hTIA hwc S.pCore_Mbar_eq_bot _ htA ht1' _
        hyA (fun h' => hy1 (congrArg Subtype.val h'))
      obtain ⟨⟨m, hm⟩, hmn⟩ := MonoidHom.mem_range.mp n.2
      have hnN' : (n : S.O) ∈ normalizer (S.Lbar g : Set S.O) := by
        rw [← subgroupOf_normalizer_eq (S.Lbar_le_Mbar g)] at hnN
        exact hnN
      have hma := S.fixes_of_mem_normalizer_Lbar h2 haQ hne hno hnN'
      rw [← hmn, S.ρ_cl _ haQ] at hma
      have hma' := (S.cl_eq_cl_iff haQ (S.conj_mem_QG hm haQ)).mp hma.symm
      have hm'a : m⁻¹ * (g * S.z * g⁻¹) * m⁻¹⁻¹ = g * S.z * g⁻¹ ∨
          m⁻¹ * (g * S.z * g⁻¹) * m⁻¹⁻¹ = g * S.z * g⁻¹ * S.z := by
        rcases hma' with h' | h'
        · left
          calc m⁻¹ * (g * S.z * g⁻¹) * m⁻¹⁻¹ = m⁻¹ * (m * (g * S.z * g⁻¹) * m⁻¹) * m := by
                rw [h']; group
            _ = g * S.z * g⁻¹ := by group
        · right
          have hzm : m⁻¹ * S.z * m = S.z := by
            rw [S.z_comm (S.M.inv_mem hm)]
            group
          have e1 : g * S.z * g⁻¹ = m⁻¹ * (g * S.z * g⁻¹) * m * S.z := by
            calc g * S.z * g⁻¹ = m⁻¹ * (m * (g * S.z * g⁻¹) * m⁻¹) * m := by group
              _ = m⁻¹ * (g * S.z * g⁻¹ * S.z) * m := by rw [h']
              _ = m⁻¹ * (g * S.z * g⁻¹) * m * (m⁻¹ * S.z * m) := by group
              _ = m⁻¹ * (g * S.z * g⁻¹) * m * S.z := by rw [hzm]
          calc m⁻¹ * (g * S.z * g⁻¹) * m⁻¹⁻¹ = m⁻¹ * (g * S.z * g⁻¹) * m * S.z * S.z := by
                rw [inv_inv, mul_assoc _ S.z S.z, S.z_mul_z, mul_one]
            _ = g * S.z * g⁻¹ * S.z := by rw [← e1]
      intro w hw
      have hw' := S.conj_mem_QG_inf_Qa_of_fix haQ hne (S.M.inv_mem hm) hm'a hw
      have e : (S.ρ ⟨y, hyM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
          (S.ρ ⟨m, hm⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) *
            (S.ρ ⟨m⁻¹, S.M.inv_mem hm⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
        have h1 := congrArg (fun x : S.Mbar => ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) hnt
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
        rw [← h1, ← hmn]
        congr 1
        rw [← Subgroup.coe_inv, ← map_inv]
        rfl
      rw [e, LinearEquiv.mul_apply, LinearEquiv.mul_apply, S.ρ_cl _ hw.1,
        S.fix_cl_of_mem_Abar ht hw', S.ρ_cl _ hw'.1]
      congr 1
      group
    exact S.mem_CQa_of_fix hne hy hfixW
  have h1 := Subgroup.card_le_of_le hL0C
  rw [S.card_L0 haQ hne] at h1
  have h2' := S.card_CQa_mul haQ
  rw [hcard] at h2'
  have h3 : Nat.card (S.CQa g) = 2 ^ (S.width + 2) := by
    refine Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ S.width) ?_
    rw [h2', ← pow_add]
    congr 1
    ring
  rw [h3] at h1
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  omega

theorem lemma_3_10 (hTI : WeaklyClosedTITransitive.{u}) (hn : 3 ≤ S.width) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    Nat.card (S.Lbar g) = 2 ^ (S.width - 1) ∨ S.HasTypeAInL g ∨ S.IsReducible := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hcard, hno, hirr⟩ := hcon
  have hle : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ≤ 2 ^ S.width := by
    have h1 := S.card_Lbar_mul g
    rw [S.card_L0 haQ hne] at h1
    have h2 := S.card_QG_inf_Qa_eq haQ hne
    have h3 := S.card_QG_inf_Qa_le hne
    rw [h2] at h1 h3 ⊢
    set d := finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g))
    rw [← pow_succ'] at h3 h1 ⊢
    have hd : d ≤ S.width := by
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
      omega
    rcases Nat.lt_or_ge d S.width with hd' | hd'
    · exact Nat.pow_le_pow_right (by norm_num) hd'
    · exfalso
      apply hcard
      have hdn : d = S.width := le_antisymm hd hd'
      rw [hdn] at h1
      refine Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ (S.width + 1)) ?_
      rw [h1, ← pow_add]
      congr 1
      omega
  have hP8 := fun h (hh : h ∈ S.M) hab => S.mem_Qa_of_commute_of_card_le haQ hne hno hle hh hab
  have hP9 : ∀ h ∈ S.M, g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
      (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹) →
      (h * g) * S.z * (h * g)⁻¹ = g * S.z * g⁻¹ ∨
        (h * g) * S.z * (h * g)⁻¹ = g * S.z * g⁻¹ * S.z := by
    intro h hh hab
    by_contra h'
    push Not at h'
    exact hirr (S.isReducible_of_commute haQ hne hP8 hh hab h'.1 h'.2)
  exact S.false_of_weaklyClosedTITransitive hTI hn haQ hne hno hle hP9

end Setting

end CFSG.LargeExtraspecial
