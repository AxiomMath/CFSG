module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWE0Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYDM

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

section PartIE

theorem partI_E0D_core {G : Type} [Group G] {D E M : Subgroup G} {eD : ↥D ≃* DihedralGroup 4}
    {t σ : G} {eltE : ℕ → G} (hctx : W16.DECtx D E eD t eltE)
    (hDM : D ≤ M) (hEM : E ≤ M) (hσM : σ ∈ M)
    [hNm : (D.subgroupOf M ⊔ E.subgroupOf M).Normal]
    (hσ2 : σ * σ = 1) (hσa : σ * sElt eD 1 * σ⁻¹ = sElt eD 1)
    (hσb : σ * sElt eD 4 * σ⁻¹ = sElt eD 2 * sElt eD 4)
    (hσE : ∀ e ∈ E, σ * e * σ⁻¹ ∈ E)
    (hcard : Nat.card ↥(E ⊓ centralizer ({σ} : Set G)) = 8)
    (hx : ∃ x ∈ E, x ≠ 1 ∧ x ≠ t ∧ x * x = 1 ∧ σ * x = x * σ) :
    Nonempty (↥E ≃* ↥(centralizer ({σ} : Set G) ⊓ (D ⊔ E))) ∧
    Nat.card ↥(centralizer ((centralizer ({σ} : Set G) ⊓ (D ⊔ E) : Subgroup G) : Set G) ⊓
      (D ⊔ E)) = 8 ∧
    ∀ y ∈ centralizer ((centralizer ({σ} : Set G) ⊓ (D ⊔ E) : Subgroup G) : Set G) ⊓ (D ⊔ E),
      y ∈ Subgroup.closure {w : G | w ∈ centralizer
        ((centralizer ({σ} : Set G) ⊓ (D ⊔ E) : Subgroup G) : Set G) ⊓ (D ⊔ E) ∧ w * w = 1} := by
  have hDEM : D ⊔ E ≤ M := sup_le hDM hEM
  have htM : t ∈ M := hDM hctx.tD
  obtain ⟨elt', hctx'⟩ := DECtx.subgroupOf hctx hDM hEM htM
  have hinj : Function.Injective M.subtype := M.subtype_injective
  obtain ⟨σ', hσ'⟩ : ∃ σ' : ↥M, (σ' : G) = σ := ⟨⟨σ, hσM⟩, rfl⟩
  have hsup : D.subgroupOf M ⊔ E.subgroupOf M = (D ⊔ E).subgroupOf M :=
    (Subgroup.subgroupOf_sup hDM hEM).symm
  have hmemW : ∀ y : ↥M, y ∈ D.subgroupOf M ⊔ E.subgroupOf M ↔ (y : G) ∈ D ⊔ E := by
    intro y
    rw [hsup]
    exact Subgroup.mem_subgroupOf
  have hcomm : ∀ y : ↥M, y * σ' = σ' * y ↔ (y : G) * σ = σ * (y : G) := by
    intro y
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hσ'] at h'
      exact h'
    · intro h
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hσ']
      exact h
  have hσ2' : σ' * σ' = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hσ', hσ2, Subgroup.coe_one]
  have hσa' : σ' * sElt (eDSub hDM eD) 1 * σ'⁻¹ = sElt (eDSub hDM eD) 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ', coe_sElt_eDSub]
    exact hσa
  have hσb' : σ' * sElt (eDSub hDM eD) 4 * σ'⁻¹ =
      sElt (eDSub hDM eD) 2 * sElt (eDSub hDM eD) 4 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ', coe_sElt_eDSub]
    exact hσb
  have hσE' : ∀ e ∈ E.subgroupOf M, σ' * e * σ'⁻¹ ∈ E.subgroupOf M := by
    intro e he
    rw [Subgroup.mem_subgroupOf] at he ⊢
    have h := hσE _ he
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hσ'] using h
  have hx' : ∃ x' ∈ E.subgroupOf M, x' ≠ 1 ∧ x' ≠ (⟨t, htM⟩ : ↥M) ∧ x' * x' = 1 ∧
      σ' * x' = x' * σ' := by
    obtain ⟨x, hxE, hx1, hxt, hxx, hxc⟩ := hx
    have hxM : x ∈ M := hEM hxE
    refine ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.2 hxE, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hx1 (congrArg Subtype.val h)
    · intro h
      exact hxt (congrArg Subtype.val h)
    · apply Subtype.ext
      exact hxx
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hσ']
      exact hxc
  obtain ⟨E0, hE0⟩ : ∃ E0 : Subgroup G, E0 = centralizer ({σ} : Set G) ⊓ (D ⊔ E) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Subgroup G, F = centralizer (E0 : Set G) ⊓ (D ⊔ E) := ⟨_, rfl⟩
  obtain ⟨E0', hE0'⟩ : ∃ E0' : Subgroup ↥M,
      E0' = (D.subgroupOf M ⊔ E.subgroupOf M) ⊓ centralizer ({σ'} : Set ↥M) := ⟨_, rfl⟩
  obtain ⟨F', hF'⟩ : ∃ F' : Subgroup ↥M,
      F' = (D.subgroupOf M ⊔ E.subgroupOf M) ⊓ centralizer (E0' : Set ↥M) := ⟨_, rfl⟩
  have hE0le : E0 ≤ D ⊔ E := by
    rw [hE0]
    exact inf_le_right
  have hFle : F ≤ D ⊔ E := by
    rw [hF]
    exact inf_le_right
  have hmemE0 : ∀ y : ↥M, y ∈ E0' ↔ (y : G) ∈ E0 := by
    intro y
    rw [hE0', hE0, Subgroup.mem_inf, Subgroup.mem_inf, hmemW,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, hcomm y]
    exact and_comm
  have hmemF : ∀ y : ↥M, y ∈ F' ↔ (y : G) ∈ F := by
    intro y
    rw [hF', hF, Subgroup.mem_inf, Subgroup.mem_inf, hmemW, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hyD, hyC⟩
      refine ⟨fun h hh => ?_, hyD⟩
      have hhE : h ∈ E0 := SetLike.mem_coe.1 hh
      have hhM : h ∈ M := hDEM (hE0le hhE)
      have h1 := hyC ⟨h, hhM⟩ (SetLike.mem_coe.2 ((hmemE0 ⟨h, hhM⟩).2 hhE))
      exact congrArg Subtype.val h1
    · rintro ⟨hyC, hyD⟩
      refine ⟨hyD, fun g hg => ?_⟩
      exact Subtype.ext (hyC (g : G) (SetLike.mem_coe.2 ((hmemE0 g).1 (SetLike.mem_coe.1 hg))))
  have hFmap : F'.map M.subtype = F := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmemF y).1 hy
    · intro hx
      have hxM : x ∈ M := hDEM (hFle hx)
      exact ⟨⟨x, hxM⟩, (hmemF ⟨x, hxM⟩).2 hx, rfl⟩
  have hE0map : E0'.map M.subtype = E0 := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmemE0 y).1 hy
    · intro hx
      have hxM : x ∈ M := hDEM (hE0le hx)
      exact ⟨⟨x, hxM⟩, (hmemE0 ⟨x, hxM⟩).2 hx, rfl⟩
  have hEC : (E.subgroupOf M ⊓ centralizer ({σ'} : Set ↥M)).map M.subtype
      = E ⊓ centralizer ({σ} : Set G) := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyE, hyC⟩ := Subgroup.mem_inf.1 hy
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hyE, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.2
        ((hcomm y).1 (Subgroup.mem_centralizer_singleton_iff.1 hyC))
    · intro hx
      obtain ⟨hxE, hxC⟩ := Subgroup.mem_inf.1 hx
      have hxM : x ∈ M := hEM hxE
      have hxC' : x * σ = σ * x := Subgroup.mem_centralizer_singleton_iff.1 hxC
      refine ⟨⟨x, hxM⟩, Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 hxE, ?_⟩, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 ((hcomm ⟨x, hxM⟩).2 hxC')
  have hcard' : Nat.card ↥(E.subgroupOf M ⊓ centralizer ({σ'} : Set ↥M)) = 8 := by
    have h := Subgroup.card_map_of_injective
      (K := E.subgroupOf M ⊓ centralizer ({σ'} : Set ↥M)) hinj
    rw [hEC, hcard] at h
    exact h.symm
  obtain ⟨elt0, hlab0, hc8⟩ := hctx'.E0_spec hσ2' hσa' hσb' hσE' hcard' hx'
  have hgen := hctx'.D0_gen hσ2' hσa' hσb' hσE' hcard' hx'
  rw [← hE0'] at hlab0 hc8 hgen
  rw [← hF'] at hc8 hgen
  obtain ⟨eE, -⟩ := ELabelling.exists_mulEquiv hctx'.L hlab0
  have hEE : ↥E ≃* ↥E0 :=
    (Subgroup.subgroupOfEquivOfLe hEM).symm.trans
      (eE.trans ((Subgroup.equivMapOfInjective E0' M.subtype hinj).trans
        (MulEquiv.subgroupCongr hE0map)))
  have hcardF : Nat.card ↥(F'.map M.subtype) = Nat.card ↥F' :=
    Subgroup.card_map_of_injective hinj
  rw [hFmap] at hcardF
  rw [← hE0, ← hF]
  refine ⟨⟨hEE⟩, hcardF.trans hc8, ?_⟩
  intro y hy
  rw [← hFmap] at hy
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
  have h2 := Subgroup.mem_map_of_mem M.subtype (hgen y' hy')
  rw [MonoidHom.map_closure] at h2
  have hsub : M.subtype '' {w : ↥M | w ∈ F' ∧ w * w = 1} ⊆ {w : G | w ∈ F ∧ w * w = 1} := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨hwF, hw2⟩ := hw
    show (w : G) ∈ F ∧ (w : G) * (w : G) = 1
    refine ⟨(hmemF w).1 hwF, ?_⟩
    rw [← Subgroup.coe_mul, hw2, Subgroup.coe_one]
  exact Subgroup.closure_mono hsub h2

theorem partI_E0D_G {G : Type} [Group G] [Finite G] {D E : Subgroup G}
    {eD : ↥D ≃* DihedralGroup 4} {t σ : G} {eltE : ℕ → G}
    (hctx : W16.DECtx D E eD t eltE)
    [hNm : (D.subgroupOf (normalizer ((D ⊔ E : Subgroup G) : Set G)) ⊔
      E.subgroupOf (normalizer ((D ⊔ E : Subgroup G) : Set G))).Normal]
    (hσM : σ ∈ normalizer ((D ⊔ E : Subgroup G) : Set G))
    (hσ2 : σ * σ = 1) (hσa : σ * sElt eD 1 * σ⁻¹ = sElt eD 1)
    (hσb : σ * sElt eD 4 * σ⁻¹ = sElt eD 2 * sElt eD 4)
    (hσE : ∀ e ∈ E, σ * e * σ⁻¹ ∈ E)
    (hcard : Nat.card ↥(E ⊓ centralizer ({σ} : Set G)) = 8)
    (hx : ∃ x ∈ E, x ≠ 1 ∧ x ≠ t ∧ x * x = 1 ∧ σ * x = x * σ) :
    Nonempty (↥E ≃* ↥(centralizer ({σ} : Set G) ⊓ (D ⊔ E))) ∧
    Nat.card ↥(centralizer ((centralizer ({σ} : Set G) ⊓ (D ⊔ E) : Subgroup G) : Set G) ⊓
      (D ⊔ E)) = 8 ∧
    ∀ y ∈ centralizer ((centralizer ({σ} : Set G) ⊓ (D ⊔ E) : Subgroup G) : Set G) ⊓ (D ⊔ E),
      y ∈ Subgroup.closure {w : G | w ∈ centralizer
        ((centralizer ({σ} : Set G) ⊓ (D ⊔ E) : Subgroup G) : Set G) ⊓ (D ⊔ E) ∧ w * w = 1} := by
  have hDN : D ≤ normalizer ((D ⊔ E : Subgroup G) : Set G) :=
    le_trans le_sup_left Subgroup.le_normalizer
  have hEN : E ≤ normalizer ((D ⊔ E : Subgroup G) : Set G) :=
    le_trans le_sup_right Subgroup.le_normalizer
  exact partI_E0D_core hctx hDN hEN hσM hσ2 hσa hσb hσE hcard hx

end PartIE

end CFSG.EvenSporadicStandard.Fin76b
