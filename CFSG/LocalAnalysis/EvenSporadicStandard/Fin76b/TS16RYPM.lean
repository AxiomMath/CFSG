module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWPartI
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYDM

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem partIM_centralizer_subgroupOf {G : Type} [Group G] {W M : Subgroup G} (hWM : W ≤ M) :
    Subgroup.centralizer ((W.subgroupOf M : Subgroup ↥M) : Set ↥M) =
      (Subgroup.centralizer (W : Set G)).subgroupOf M := by
  ext m
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hm h hh
    have hh' : h ∈ W := hh
    have hmem : (⟨h, hWM hh'⟩ : ↥M) ∈ W.subgroupOf M := Subgroup.mem_subgroupOf.2 hh'
    exact congrArg Subtype.val (hm ⟨h, hWM hh'⟩ (SetLike.mem_coe.2 hmem))
  · intro hm h hh
    exact Subtype.ext (hm h (SetLike.mem_coe.2 (Subgroup.mem_subgroupOf.1 (SetLike.mem_coe.1 hh))))

theorem partIM_zpowers_subgroupOf {G : Type} [Group G] {t : G} {M : Subgroup G} (htM : t ∈ M) :
    (Subgroup.zpowers t).subgroupOf M = Subgroup.zpowers (⟨t, htM⟩ : ↥M) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, (Subgroup.coe_zpow M (⟨t, htM⟩ : ↥M) k).symm⟩

theorem partIM_conj_mem_centralizer {G : Type} [Group G] {W : Subgroup G} {m x : G}
    (hm : m ∈ Subgroup.normalizer (W : Set G)) (hx : x ∈ Subgroup.centralizer (W : Set G)) :
    m * x * m⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro h hh
  have hh' : m⁻¹ * h * m ∈ (W : Set G) := by
    refine (Subgroup.mem_set_normalizer_iff.1 hm (m⁻¹ * h * m)).2 ?_
    rw [show m * (m⁻¹ * h * m) * m⁻¹ = h by group]
    exact hh
  calc h * (m * x * m⁻¹) = m * ((m⁻¹ * h * m) * x) * m⁻¹ := by group
    _ = m * (x * (m⁻¹ * h * m)) * m⁻¹ := by rw [hx _ hh']
    _ = m * x * m⁻¹ * h := by group

theorem partIM_normal_subgroupOf {G : Type} [Group G] {W N : Subgroup G}
    (hNC : N ≤ Subgroup.centralizer (W : Set G)) (hNodd : ∀ n ∈ N, Odd (orderOf n))
    (hNcov : ∀ n ∈ Subgroup.centralizer (W : Set G), Odd (orderOf n) → n ∈ N) :
    (N.subgroupOf (Subgroup.normalizer (W : Set G))).Normal := by
  refine ⟨fun n hn m => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hC : (m : G) * (n : G) * (m : G)⁻¹ ∈ Subgroup.centralizer (W : Set G) :=
    partIM_conj_mem_centralizer m.2 (hNC hn)
  refine hNcov _ hC ?_
  have hord : orderOf ((m : G) * (n : G) * (m : G)⁻¹) = orderOf (n : G) := by
    have := MulEquiv.orderOf_eq (MulAut.conj (m : G)) (n : G)
    rwa [MulAut.conj_apply] at this
  show Odd (orderOf ((m : G) * (n : G) * (m : G)⁻¹))
  rw [hord]
  exact hNodd _ hn

section PartIM


theorem partI_clauses_M {G : Type} [Group G] [Finite G] {D E : Subgroup G}
    {eD : ↥D ≃* DihedralGroup 4} {t z σ : G} {N : Subgroup G} {eltE : ℕ → G}
    (hctx : W16.DECtx D E eD t eltE)
    [hNm : (D.subgroupOf (normalizer ((D ⊔ E : Subgroup G) : Set G)) ⊔
      E.subgroupOf (normalizer ((D ⊔ E : Subgroup G) : Set G))).Normal]
    (hΓ0 : W16.InducedStab (D.subgroupOf (normalizer ((D ⊔ E : Subgroup G) : Set G)))
      (E.subgroupOf (normalizer ((D ⊔ E : Subgroup G) : Set G))))
    (hNodd : ∀ n ∈ N, Odd (orderOf n))
    (hNcov : ∀ n ∈ centralizer ((D ⊔ E : Subgroup G) : Set G), Odd (orderOf n) → n ∈ N)
    (hker : centralizer ((D ⊔ E : Subgroup G) : Set G) = N ⊔ zpowers t)
    (hz2 : z * z = 1) (hzM : z ∈ normalizer ((D ⊔ E : Subgroup G) : Set G))
    (hzE : ∀ e ∈ E, z * e = e * z)
    (hza : z * sElt eD 1 * z⁻¹ = (sElt eD 1)⁻¹)
    (hzb : z * sElt eD 4 * z⁻¹ = (sElt eD 1)⁻¹ * sElt eD 4)
    (hσM : σ ∈ normalizer ((D ⊔ E : Subgroup G) : Set G))
    (hσa : σ * sElt eD 1 * σ⁻¹ = sElt eD 1)
    (hg : ∃ g ∈ normalizer ((D ⊔ E : Subgroup G) : Set G), g * z * g⁻¹ = σ) :
    ∃ Q' P : Subgroup ↥(normalizer ((D ⊔ E : Subgroup G) : Set G)), IsPGroup 2 Q' ∧
      ¬ 2 ∣ Q'.index ∧
      (⟨z, hzM⟩ : ↥(normalizer ((D ⊔ E : Subgroup G) : Set G))) ∈ Q' ∧ P ≤ Q' ∧
      P.relIndex Q' = 2 ∧
      (⟨z, hzM⟩ : ↥(normalizer ((D ⊔ E : Subgroup G) : Set G))) ∉ P ∧
      (∃ R : Subgroup ↥(normalizer ((D ⊔ E : Subgroup G) : Set G)), IsPGroup 2 R ∧
        R ≤ centralizer ({(⟨z, hzM⟩ : ↥(normalizer ((D ⊔ E : Subgroup G) : Set G)))} :
          Set ↥(normalizer ((D ⊔ E : Subgroup G) : Set G))) ∧
        Nat.card ↥R = 512) ∧
      (∀ η ∈ P, η * η = 1 → η ≠ 1 →
        ∃ R : Subgroup ↥(normalizer ((D ⊔ E : Subgroup G) : Set G)), IsPGroup 2 R ∧
          R ≤ centralizer ({η} : Set ↥(normalizer ((D ⊔ E : Subgroup G) : Set G))) ∧
          1024 ≤ Nat.card ↥R) ∧
      (∀ y ∈ Q', y * y = 1 → y ∉ P →
        512 ≤ Nat.card ↥(Q' ⊓ centralizer ({y} : Set ↥(normalizer ((D ⊔ E : Subgroup G) : Set G)))) →
          ∃ m : ↥(normalizer ((D ⊔ E : Subgroup G) : Set G)),
            y = m * (⟨z, hzM⟩ : ↥(normalizer ((D ⊔ E : Subgroup G) : Set G))) * m⁻¹) := by
  set M' : Subgroup G := normalizer ((D ⊔ E : Subgroup G) : Set G)
  have hWM : D ⊔ E ≤ M' := Subgroup.le_normalizer
  have hDM : D ≤ M' := le_trans (le_sup_left : D ≤ D ⊔ E) hWM
  have hEM : E ≤ M' := le_trans (le_sup_right : E ≤ D ⊔ E) hWM
  have htM : t ∈ M' := hDM hctx.tD
  obtain ⟨elt', hctx'⟩ := DECtx.subgroupOf hctx hDM hEM htM
  have hNC : N ≤ Subgroup.centralizer ((D ⊔ E : Subgroup G) : Set G) := by
    rw [hker]
    exact le_sup_left
  have hNM : N ≤ M' :=
    le_trans hNC (Subgroup.centralizer_le_normalizer ((D ⊔ E : Subgroup G) : Set G))
  haveI : (N.subgroupOf M').Normal := partIM_normal_subgroupOf hNC hNodd hNcov
  have hN' : ∀ n ∈ N.subgroupOf M', Odd (orderOf n) := by
    intro n hn
    rw [← Subgroup.orderOf_coe]
    exact hNodd _ (Subgroup.mem_subgroupOf.1 hn)
  have hNz : N.subgroupOf M' ⊔ Subgroup.zpowers (⟨t, htM⟩ : ↥M') =
      (N ⊔ Subgroup.zpowers t).subgroupOf M' := by
    rw [Subgroup.subgroupOf_sup hNM (Subgroup.zpowers_le.2 htM), partIM_zpowers_subgroupOf htM]
  have hker' : Subgroup.centralizer ((D.subgroupOf M' ⊔ E.subgroupOf M' : Subgroup ↥M') :
      Set ↥M') = N.subgroupOf M' ⊔ Subgroup.zpowers (⟨t, htM⟩ : ↥M') := by
    rw [← Subgroup.subgroupOf_sup hDM hEM, partIM_centralizer_subgroupOf hWM, hker, hNz]
  have hz2' : (⟨z, hzM⟩ : ↥M') * ⟨z, hzM⟩ = 1 := Subtype.ext hz2
  have hzE' : ∀ e ∈ E.subgroupOf M', (⟨z, hzM⟩ : ↥M') * e = e * ⟨z, hzM⟩ :=
    fun e he => Subtype.ext (hzE e (Subgroup.mem_subgroupOf.1 he))
  have hza' : (⟨z, hzM⟩ : ↥M') * sElt (eDSub hDM eD) 1 * (⟨z, hzM⟩ : ↥M')⁻¹ =
      (sElt (eDSub hDM eD) 1)⁻¹ := Subtype.ext hza
  have hzb' : (⟨z, hzM⟩ : ↥M') * sElt (eDSub hDM eD) 4 * (⟨z, hzM⟩ : ↥M')⁻¹ =
      (sElt (eDSub hDM eD) 1)⁻¹ * sElt (eDSub hDM eD) 4 := Subtype.ext hzb
  have hσa' : (⟨σ, hσM⟩ : ↥M') * sElt (eDSub hDM eD) 1 * (⟨σ, hσM⟩ : ↥M')⁻¹ =
      sElt (eDSub hDM eD) 1 := Subtype.ext hσa
  obtain ⟨g, hgM, hg⟩ := hg
  have hg' : (⟨g, hgM⟩ : ↥M') * ⟨z, hzM⟩ * (⟨g, hgM⟩ : ↥M')⁻¹ = ⟨σ, hσM⟩ :=
    Subtype.ext hg
  exact W16.partI_clauses hctx' hΓ0 hN' hker' hz2' hzE' hza' hzb' hσa' hg'

end PartIM

end CFSG.EvenSporadicStandard.Fin76b
