module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorusFacts
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section TorusElement

variable {G : Type} [Group G]

theorem exists_torus_element_two {p : ℕ} [Fact p.Prime] {B X : Subgroup G}
    (htorus : ∃ φ : Multiplicative (GaloisField p 2) ≃* X, ∀ μ : (GaloisField p 2)ˣ,
      ∃ t ∈ B, ∀ a : Multiplicative (GaloisField p 2),
        t * (φ a : G) * t⁻¹ =
          φ (Multiplicative.ofAdd ((μ : GaloisField p 2) * Multiplicative.toAdd a))) :
    ∃ t : G, t ∈ B ∧ t ∈ Subgroup.normalizer (X : Set G) ∧
      ∀ k : ℕ, ¬ (p + 1) ∣ k → ∀ Y : Subgroup G, Y ≤ X →
        t ^ k ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = X := by
  have hp : p.Prime := Fact.out
  obtain ⟨φ, htor⟩ := htorus
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := (GaloisField p 2)ˣ)
  have hord : orderOf γ = p ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units,
      GaloisField.card p 2 (by norm_num)]
  obtain ⟨t, htB, ht⟩ := htor γ
  refine ⟨t, htB, mem_normalizer_of_torus_conj φ (Units.ne_zero γ) ht, fun k hk Y hYX hY => ?_⟩
  refine eq_bot_or_eq_of_torus_conj' (by norm_num) φ (γ := (γ : GaloisField p 2) ^ k) ?_
    (pow_ne_zero _ (Units.ne_zero γ)) (conj_pow_of_torus_conj φ ht k) hYX hY
  intro d hd0 hd2 hγd
  have hd1 : d = 1 := by omega
  subst hd1
  apply hk
  have h1 : γ ^ (k * (p - 1)) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_mul, Units.val_one]
    simpa using hγd
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at h2
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  have h3 : (p + 1) * (p - 1) ∣ k * (p - 1) := by
    have : p ^ 2 - 1 = (p + 1) * (p - 1) := by
      have := hp.two_le
      zify [show 1 ≤ p ^ 2 from Nat.one_le_pow _ _ hp.pos, show 1 ≤ p by omega]
      ring
    rwa [this] at h2
  exact Nat.dvd_of_mul_dvd_mul_right hp1 h3

end TorusElement

section TorusLift

variable {G : Type} [Group G] [Finite G]

theorem exists_torus_of_map_subgroupOf_eq' {p : ℕ} [Fact p.Prime] {H B X : Subgroup G}
    (hXH : X ≤ H) (hX : IsPGroup p X) (hNB : GLBPrimeCore p H ≤ B) {F : Type*} [Field F]
    (ψ : Multiplicative F →* H ⧸ primeComplementCore (G := H) p) (hψ : Function.Injective ψ)
    (hψX : ψ.range = (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    (hc : ∀ μ : Fˣ,
      ∃ c ∈ (B.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)),
        ∀ a : Multiplicative F,
          c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd ((μ : F) * Multiplicative.toAdd a))) :
    ∃ φ : Multiplicative F ≃* X, ∀ μ : Fˣ, ∃ t ∈ B, ∀ a : Multiplicative F,
      t * (φ a : G) * t⁻¹ = φ (Multiplicative.ofAdd ((μ : F) * Multiplicative.toAdd a)) := by
  set O := primeComplementCore (G := H) p with hOdef
  set A := X.subgroupOf H with hAdef
  have hA : IsPGroup p A := hX.comap_subtype
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hOB : O ≤ B.subgroupOf H := fun o ho =>
    Subgroup.mem_subgroupOf.mpr
      (hNB ((mem_glbPrimeCore_iff_mk_eq_one o).mpr ((QuotientGroup.eq_one_iff o).mpr ho)))
  let g : A →* H ⧸ O := (QuotientGroup.mk' O).comp A.subtype
  have hg : ∀ x : A, g x = QuotientGroup.mk' O (x : H) := fun x => rfl
  have hginj : Function.Injective g := by
    intro x y hxy
    have hmem : ((x * y⁻¹ : A) : H) ∈ A ⊓ O := by
      refine ⟨(x * y⁻¹).2, ?_⟩
      have h1 : QuotientGroup.mk' O ((x * y⁻¹ : A) : H) = 1 := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, ← hg, ← hg, hxy,
          mul_inv_cancel]
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [inf_eq_bot_of_isPGroup (Fact.out : p.Prime) hA hO, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp (Subtype.ext hmem)
  have hgr : ψ.range = g.range := by
    rw [hψX, MonoidHom.range_comp, Subgroup.range_subtype]
  let φ : Multiplicative F ≃* A := (MonoidHom.ofInjective hψ).trans
    ((MulEquiv.subgroupCongr hgr).trans (MonoidHom.ofInjective hginj).symm)
  have hφ : ∀ a, g (φ a) = ψ a := by
    intro a
    change g ((MonoidHom.ofInjective hginj).symm
      (MulEquiv.subgroupCongr hgr (MonoidHom.ofInjective hψ a))) = ψ a
    rw [MonoidHom.apply_ofInjective_symm, MulEquiv.subgroupCongr_apply,
      MonoidHom.ofInjective_apply]
  refine ⟨φ.trans (Subgroup.subgroupOfEquivOfLe hXH), fun μ => ?_⟩
  obtain ⟨_, ⟨b, hb, rfl⟩, hcψ⟩ := hc μ
  have hbN : QuotientGroup.mk' O b ∈
      Subgroup.normalizer ((A.map (QuotientGroup.mk' O) : Subgroup (H ⧸ O)) : Set (H ⧸ O)) := by
    rw [← hψX, Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, (hcψ a).symm⟩
    · rintro ⟨a, ha⟩
      refine ⟨Multiplicative.ofAdd ((μ : F)⁻¹ * Multiplicative.toAdd a), ?_⟩
      have h := hcψ (Multiplicative.ofAdd ((μ : F)⁻¹ * Multiplicative.toAdd a))
      rw [toAdd_ofAdd, mul_inv_cancel_left₀ μ.ne_zero, ofAdd_toAdd, ha] at h
      exact mul_left_cancel (mul_right_cancel h)
  obtain ⟨o, ho, t, ht, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (comap_normalizer_map_le_sup Fact.out O hO hA hbN)
  have ho1 : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  have hot : QuotientGroup.mk' O (o * t) = QuotientGroup.mk' O t := by
    rw [map_mul, ho1, one_mul]
  have htB : t ∈ B.subgroupOf H := by
    have h1 := (B.subgroupOf H).mul_mem ((B.subgroupOf H).inv_mem (hOB ho)) hb
    simpa using h1
  refine ⟨t, Subgroup.mem_subgroupOf.mp htB, fun a => ?_⟩
  have hmem : t * (φ a : H) * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp ht _).mp (φ a).2
  have heq : (⟨t * (φ a : H) * t⁻¹, hmem⟩ : A) =
      φ (Multiplicative.ofAdd ((μ : F) * Multiplicative.toAdd a)) := by
    apply hginj
    rw [hφ, ← hcψ, ← hφ a, hg, hg, hot, map_mul, map_mul, map_inv]
  have := congrArg (fun z : A => ((z : H) : G)) heq
  exact this

end TorusLift

end CFSG.AGLEmbedding
