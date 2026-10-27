module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2G1Fac

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Subgroup CFSG.ABGLocalTools CFSG.EvenSmallLie.UnitarySix.YamadaEnd
  CFSG.EvenSmallLie.UnitarySix.YamadaPar
open scoped MatrixGroups commutatorElement

theorem normalizer_commutator_self {G : Type*} [Group G] {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) : g ∈ normalizer ((⁅X, X⁆ : Subgroup G) : Set G) := by
  have hmap : X.map (MulAut.conj g).toMonoidHom = X := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.mp hg y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply]; group⟩
      have := (mem_normalizer_iff.mp (inv_mem hg) x).mp hx
      simpa using this
  rw [mem_normalizer_iff]
  intro y
  have h1 : (⁅X, X⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom = ⁅X, X⁆ := by
    rw [Subgroup.map_commutator, hmap]
  constructor
  · intro hy
    rw [← h1]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h1] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := by
      have := congrArg (fun w => g⁻¹ * w * g) hzy
      simpa [MulAut.conj_apply, mul_assoc] using this
    rw [← this]
    exact hz

theorem normalizer_centralizer {G : Type*} [Group G] {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) :
    g ∈ normalizer ((centralizer (X : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g' ∈ normalizer (X : Set G), ∀ y ∈ centralizer (X : Set G),
      g' * y * g'⁻¹ ∈ centralizer (X : Set G) := by
    intro g' hg' y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro x hx
    have hx' : g'⁻¹ * x * g' ∈ X := by
      have := (mem_normalizer_iff.mp (inv_mem hg') x).mp hx
      simpa using this
    have := hy _ hx'
    calc x * (g' * y * g'⁻¹) = g' * ((g'⁻¹ * x * g') * y) * g'⁻¹ := by group
      _ = g' * (y * (g'⁻¹ * x * g')) * g'⁻¹ := by rw [this]
      _ = g' * y * g'⁻¹ * x := by group
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun h => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem normalizer_D₂_of {G : Type*} [Group G] {D₁ D₂ : Subgroup G} {p : G}
    (h416a : ⁅D₁ ⊔ D₂, D₁ ⊔ D₂⁆ = D₁ ⊓ D₂)
    (h416b : (D₁ ⊔ D₂) ⊓ centralizer ((D₁ ⊓ D₂ : Subgroup G) : Set G) = D₂)
    (hp : p ∈ normalizer ((D₁ ⊔ D₂ : Subgroup G) : Set G)) :
    p ∈ normalizer (D₂ : Set G) := by
  have h1 := normalizer_commutator_self hp
  rw [h416a] at h1
  have h2 := normalizer_centralizer h1
  rw [← h416b]
  exact mem_normalizer_inf hp h2

section Main

variable {G : Type} [Group G] {t : G} {D₁ V₁ A₁ K₁ D₂ : Subgroup G} {θ : K₁ ≃* SU42b}
  {ιG : (Fin 8 → ZMod 2) → G}

theorem Y13Hyp.P_facts [Finite G] (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) (hL44 : L44Input)
    {S P : Subgroup G} (χ : msigma CFSG.Fischer.F4 ≃* K₁)
    (hχS : ∀ A : msigma CFSG.Fischer.F4, (A : SL(4, CFSG.Fischer.F4)) ∈ pstd CFSG.Fischer.F4 →
      (χ A : G) ∈ S)
    (hP : IsSylowOf 2 P (nOne D₁ K₁ D₂)) (hSP : S ≤ P) (hD₁P : D₁ ≤ P) (hD₂P : D₂ ≤ P)
    (h416a : ⁅D₁ ⊔ D₂, D₁ ⊔ D₂⁆ = D₁ ⊓ D₂)
    (h416b : (D₁ ⊔ D₂) ⊓ centralizer ((D₁ ⊓ D₂ : Subgroup G) : Set G) = D₂)
    (hD₁D₂ : Nat.card (D₁ ⊓ D₂ : Subgroup G) ≤ 2 ^ 10) :
    P ≤ normalizer (D₂ : Set G) ∧ (∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ D₁ ⊔ D₂) ∧
      (∀ x ∈ P, x * x ∈ D₁ ⊔ D₂) ∧
      (∀ x ∈ P, x * t * x⁻¹ * t⁻¹ ∈ D₁ ⊔ D₂ → x ∈ S ⊔ D₁ ⊔ D₂) ∧
      (χ dωS : G) ∈ normalizer (P : Set G) ∧ (χ dωS : G) ^ 3 = 1 ∧
      ∀ x ∈ P, (χ dωS : G) * x * (χ dωS : G)⁻¹ * x⁻¹ ∈ D₁ ⊔ D₂ → x ∈ D₁ ⊔ D₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (ElemSec D₁ V₁) := ⟨h.sec⟩
  have : (D₁.subgroupOf (nOne D₁ K₁ D₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.D₁_le_nOne).mpr h.nOne_le_normalizer
  obtain ⟨fV, hfV⟩ := h.exists_fV
  obtain ⟨hfix, hcase⟩ := (h.r3Hyp fV hfV).main
  set χb := (kmap h).comp χ.toMonoidHom
  have hχb : Function.Injective χb := (kmap_injective h).comp χ.injective
  have hfixχ : ∀ γ, tauG h γ = γ ↔ γ ∈ χb.range := fun γ => by
    constructor
    · intro hγ
      obtain ⟨k, hk⟩ := hfix γ hγ
      exact ⟨χ.symm k, by simp [χb, hk]⟩
    · rintro ⟨A, rfl⟩
      exact h.r3_τK ⟨χ A, rfl⟩
  have hPN := hP.le
  have hDN : D₁ ⊔ D₂ ≤ nOne D₁ K₁ D₂ := sup_le h.D₁_le_nOne h.D₂_le_nOne
  have hDD : D₁ ≤ D₁ ⊔ D₂ := le_sup_left
  set Pb := barG D₁ K₁ D₂ P
  set Db := barG D₁ K₁ D₂ (D₁ ⊔ D₂)
  have hPcard : Nat.card P = 2 ^ 30 := by rw [hP.card_eq, h.factorization_card_nOne]
  have hPb : Nat.card Pb = 2 ^ 12 := by
    have := card_eq_mul_card_barG (K₁ := K₁) (D₂ := D₂) hD₁P hPN
    rw [hPcard, h.card_D₁] at this
    have h2 : 2 ^ 18 * Nat.card Pb = 2 ^ 18 * 2 ^ 12 := by rw [← this]; norm_num
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  have hP2 : IsPGroup 2 Pb := IsPGroup.of_card hPb
  have hPσ : ∀ A ∈ pSig CFSG.Fischer.F4, χb A ∈ Pb := fun A hA =>
    (mkG_mem_barG_iff hD₁P _).mpr (hSP (hχS A (Subgroup.mem_subgroupOf.mp hA)))
  have hDP : Db ≤ Pb := Subgroup.map_mono fun x hx => sup_le hD₁P hD₂P hx
  have hDc : ∀ x ∈ Db, ∀ y ∈ Db, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, mkG_eq_iff']
    have hc := Subgroup.commutator_mem_commutator (inv_mem (Subgroup.mem_subgroupOf.mp hy))
      (inv_mem (Subgroup.mem_subgroupOf.mp hx))
    rw [h416a] at hc
    have e : ((x * y : nOne D₁ K₁ D₂) : G)⁻¹ * ((y * x : nOne D₁ K₁ D₂) : G) =
        ⁅(y : G)⁻¹, (x : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, commutatorElement_def]; group
    rw [e]
    exact hc.1
  have hDcard : 2 ^ 8 ≤ Nat.card Db := by
    have hrange : (dmap h).range ≤ Db := by
      rintro _ ⟨d, rfl⟩
      exact ⟨Subgroup.inclusion h.D₂_le_nOne d, Subgroup.mem_subgroupOf.mpr
        (le_sup_right (a := D₁) d.2), rfl⟩
    have hcard := card_le_card_mul_of_hom (dmap h)
    have hker : Nat.card (dmap h).ker ≤ 2 ^ 10 := by
      refine (Nat.card_le_card_of_injective (fun d : (dmap h).ker =>
        (⟨((d : D₂) : G), h.mem_D₁_of_mkG_eq_one _ d.2, (d : D₂).2⟩ : (D₁ ⊓ D₂ : Subgroup G)))
        fun d d' hdd => ?_).trans hD₁D₂
      have := congrArg Subtype.val hdd
      simp only at this
      exact Subtype.ext (Subtype.ext this)
    rw [h.card_D₂] at hcard
    have : 2 ^ 8 ≤ Nat.card (dmap h).range := by
      by_contra hlt
      have := Nat.mul_le_mul (show Nat.card (dmap h).range ≤ 2 ^ 8 - 1 by omega) hker
      omega
    exact this.trans (Subgroup.card_le_of_le hrange)
  have hcase' : Nonempty (SL(4, CFSG.Fischer.F4) ≃* ↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf
      (nOne D₁ K₁ D₂)) ∨ ∃ ψ : SU42b × SU42b ≃* ↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf
        (nOne D₁ K₁ D₂), ∀ p, tauG h (ψ p) = ψ p.swap := by
    rcases hcase with ⟨ψ, -⟩ | hU
    · exact Or.inl ⟨ψ⟩
    · exact Or.inr hU
  have hF := gamma1_facts hL44 (tauG h) h.r3_ττ χb hχb hfixχ hcase' hP2 hPb hPσ hDP hDc hDcard
  have hPm : ∀ n : nOne D₁ K₁ D₂, mkG D₁ K₁ D₂ n ∈ Pb ↔ (n : G) ∈ P := mkG_mem_barG_iff hD₁P
  have hDm : ∀ n : nOne D₁ K₁ D₂, mkG D₁ K₁ D₂ n ∈ Db ↔ (n : G) ∈ D₁ ⊔ D₂ :=
    mkG_mem_barG_iff hDD
  have hconjD : ∀ p ∈ P, ∀ y ∈ D₁ ⊔ D₂, p * y * p⁻¹ ∈ D₁ ⊔ D₂ := by
    intro p hp y hy
    have h1 := (mem_normalizer_iff.mp (hF.norm ((hPm ⟨p, hPN hp⟩).mpr hp))
      (mkG D₁ K₁ D₂ ⟨y, hDN hy⟩)).mp ((hDm ⟨y, hDN hy⟩).mpr hy)
    rw [← map_inv, ← map_mul, ← map_mul, hDm] at h1
    simpa using h1
  set jn : nOne D₁ K₁ D₂ := ⟨χ dωS, h.K₁_le_nOne (χ dωS).2⟩
  have hj : χb dωS = mkG D₁ K₁ D₂ jn := rfl
  refine ⟨fun p hp => normalizer_D₂_of h416a h416b ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro y
    refine ⟨hconjD p hp y, fun hy => ?_⟩
    have := hconjD p⁻¹ (inv_mem hp) _ hy
    simpa [mul_assoc] using this
  · intro x hx y hy
    have h1 := hF.comm _ ((hPm ⟨x, hPN hx⟩).mpr hx) _ ((hPm ⟨y, hPN hy⟩).mpr hy)
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hDm] at h1
    simpa using h1
  · intro x hx
    have h1 := hF.sq _ ((hPm ⟨x, hPN hx⟩).mpr hx)
    rw [← map_mul, hDm] at h1
    simpa using h1
  · intro x hx hxt
    have h1 : mkG D₁ K₁ D₂ ⟨x, hPN hx⟩ * (tauG h (mkG D₁ K₁ D₂ ⟨x, hPN hx⟩))⁻¹ ∈ Db := by
      rw [tauG_mk, ← map_inv, ← map_mul, hDm]
      simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show x * (t * x * t⁻¹)⁻¹ = x * t * x⁻¹ * t⁻¹ by group]
      exact hxt
    obtain ⟨A, hA, hAx⟩ := hF.tfix _ ((hPm ⟨x, hPN hx⟩).mpr hx) h1
    have hχA : χb A = mkG D₁ K₁ D₂ ⟨χ A, h.K₁_le_nOne (χ A).2⟩ := rfl
    rw [hχA, ← map_inv, ← map_mul, hDm] at hAx
    have hAx' : (χ A : G)⁻¹ * x ∈ D₁ ⊔ D₂ := by simpa using hAx
    have e : x = (χ A : G) * ((χ A : G)⁻¹ * x) := by group
    rw [e, sup_assoc]
    exact mul_mem (Subgroup.mem_sup_left (hχS A (Subgroup.mem_subgroupOf.mp hA)))
      (Subgroup.mem_sup_right hAx')
  · rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 := (mem_normalizer_iff.mp hF.jnorm (mkG D₁ K₁ D₂ ⟨y, hPN hy⟩)).mp
        ((hPm ⟨y, hPN hy⟩).mpr hy)
      rw [hj, ← map_inv, ← map_mul, ← map_mul, hPm] at h1
      simpa using h1
    · intro hy
      have hyN : y ∈ nOne D₁ K₁ D₂ := by
        have h2 := hPN hy
        have e : y = (χ dωS : G)⁻¹ * ((χ dωS : G) * y * (χ dωS : G)⁻¹) * (χ dωS : G) := by
          group
        rw [e]
        exact mul_mem (mul_mem (inv_mem jn.2) h2) jn.2
      have h1 : χb dωS * mkG D₁ K₁ D₂ ⟨y, hyN⟩ * (χb dωS)⁻¹ ∈ Pb := by
        rw [hj, ← map_inv, ← map_mul, ← map_mul, hPm]
        simpa using hy
      exact (hPm ⟨y, hyN⟩).mp ((mem_normalizer_iff.mp hF.jnorm _).mpr h1)
  · have h3 : dωS ^ 3 = 1 := Subtype.ext dω_pow_three
    have h4 : χ dωS ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    have := congrArg (fun k : K₁ => (k : G)) h4
    simpa using this
  · intro x hx hxj
    have h1 : χb dωS * mkG D₁ K₁ D₂ ⟨x, hPN hx⟩ * (χb dωS)⁻¹ *
        (mkG D₁ K₁ D₂ ⟨x, hPN hx⟩)⁻¹ ∈ Db := by
      rw [hj, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hDm]
      simpa using hxj
    exact (hDm ⟨x, hPN hx⟩).mp (hF.jfix _ ((hPm ⟨x, hPN hx⟩).mpr hx) h1)

end Main

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
