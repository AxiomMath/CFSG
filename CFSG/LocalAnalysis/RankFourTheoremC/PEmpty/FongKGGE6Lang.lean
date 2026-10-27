module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGGE6Inner

public noncomputable section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.E6Pilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

set_option linter.unusedSectionVars false

section Basic

variable {F : Type} [Field F] [Finite F]

theorem conj_injective_C6 : Function.Injective (MulAut.conj : C6 F →* MulAut (C6 F)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hc : g ∈ Subgroup.center (C6 F) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun φ : MulAut (C6 F) => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  rw [center_adjointGroup_eq_bot (τ := Tag.E6) (K := F)] at hc
  exact hc

theorem conj_mem_stabU {u : C6 F} (hu : u ∈ U6 F) : MulAut.conj u ∈ stabU F := by
  intro x
  rw [MulAut.conj_apply]
  constructor
  · intro h
    have : u⁻¹ * (u * x * u⁻¹) * u ∈ U6 F :=
      (U6 F).mul_mem ((U6 F).mul_mem ((U6 F).inv_mem hu) h) hu
    simpa [mul_assoc] using this
  · intro hx
    exact (U6 F).mul_mem ((U6 F).mul_mem hu hx) ((U6 F).inv_mem hu)

theorem inner_two_mem_U6 [CharP F 2] {g : C6 F} {m : ℕ} (hs : MulAut.conj g ∈ stabU F)
    (hg : (MulAut.conj g) ^ (2 ^ m) = 1) : g ∈ U6 F := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := U6_sylow F
  have hgm : g ^ (2 ^ m) = 1 := by
    apply conj_injective_C6 (F := F)
    rw [map_pow, map_one]
    exact hg
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers g) := by
    apply IsPGroup.of_card_dvd_pow (n := m)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hgm
  have hnorm : g ∈ Subgroup.normalizer (P₀ : Subgroup (C6 F)) := by
    rw [Subgroup.mem_normalizer_iff, hP₀]
    intro x
    exact (hs x).symm.trans (by rw [MulAut.conj_apply])
  have h1 := IsPGroup.inf_normalizer_sylow hzp P₀
  have hmem : g ∈ Subgroup.zpowers g ⊓ (P₀ : Subgroup (C6 F)) := by
    rw [← h1]
    exact ⟨Subgroup.mem_zpowers g, hnorm⟩
  rw [← hP₀]
  exact hmem.2

end Basic

section Field

variable {F : Type} [Field F] [Finite F]

@[expose] def IsCoord (Θ : MulAut (C6 F) →* (F ≃+* F) × Multiplicative (ZMod 2)) : Prop :=
  ∀ (g : C6 F) (a : Fin Tag.E6.rank → Fˣ) (ρ : F ≃+* F) (ε : ℕ),
    Θ (MulAut.conj g * exactNormalAut .E6 F a ρ ε) = (ρ, Multiplicative.ofAdd (ε : ZMod 2))

@[expose] def fieldAutE6 (F : Type) [Field F] (δ : F ≃+* F) : MulAut (C6 F) :=
  exactNormalAut .E6 F 1 δ 0

theorem Θ_conj {Θ : MulAut (C6 F) →* (F ≃+* F) × Multiplicative (ZMod 2)} (hΘ : IsCoord Θ)
    (g : C6 F) : Θ (MulAut.conj g) = 1 := by
  have := hΘ g 1 1 0
  rw [exactNormalAut_one_one_zero_E6, mul_one] at this
  rw [this]
  simp

theorem Θ_fieldAut {Θ : MulAut (C6 F) →* (F ≃+* F) × Multiplicative (ZMod 2)} (hΘ : IsCoord Θ)
    (δ : F ≃+* F) : Θ (fieldAutE6 F δ) = (δ, 1) := by
  have := hΘ 1 1 δ 0
  rw [map_one, one_mul] at this
  rw [fieldAutE6, this]
  simp

theorem fieldAutE6_mem_stabU (δ : F ≃+* F) : fieldAutE6 F δ ∈ stabU F :=
  mem_stabU_iff_map.mpr (exactNormalAut_mem 1 δ 0).1

theorem fieldAutE6_sq {δ : F ≃+* F} (hδ2 : δ * δ = 1) :
    fieldAutE6 F δ * fieldAutE6 F δ = 1 := by
  rw [fieldAutE6, exactNormalAut_one_mul_one_E6, hδ2]
  simpa using exactNormalAut_one_one_zero_E6 (K := F)

theorem fieldAutE6_inv {δ : F ≃+* F} (hδ2 : δ * δ = 1) :
    (fieldAutE6 F δ)⁻¹ = fieldAutE6 F δ :=
  inv_eq_of_mul_eq_one_right (fieldAutE6_sq hδ2)

theorem mulAut_conj_conj {M : Type*} [Group M] (φ : MulAut M) (g : M) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

@[expose] def intU (F : Type) [Field F] : Subgroup (MulAut (C6 F)) :=
  (U6 F).map (MulAut.conj : C6 F →* MulAut (C6 F))

theorem intU_isPGroup [CharP F 2] : IsPGroup 2 ↥(intU F) := by
  obtain ⟨P₀, hP₀⟩ := U6_sylow F
  have := P₀.isPGroup'.map (MulAut.conj : C6 F →* MulAut (C6 F))
  rw [hP₀] at this
  exact this

@[expose] def T0 (F : Type) [Field F] (δ : F ≃+* F) : Subgroup (MulAut (C6 F)) :=
  intU F ⊔ Subgroup.zpowers (fieldAutE6 F δ)

theorem T0_isPGroup [CharP F 2] {δ : F ≃+* F} (hδ2 : δ * δ = 1) : IsPGroup 2 ↥(T0 F δ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : IsPGroup 2 ↥(Subgroup.zpowers (fieldAutE6 F δ)) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact fieldAutE6_sq hδ2)
  refine IsPGroup.to_sup_of_normal_left' intU_isPGroup hz ?_
  rw [Subgroup.zpowers_le]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hs := fieldAutE6_mem_stabU δ
  constructor
  · rintro ⟨u, hu, rfl⟩
    show fieldAutE6 F δ * MulAut.conj u * (fieldAutE6 F δ)⁻¹ ∈ intU F
    rw [mulAut_conj_conj]
    exact ⟨fieldAutE6 F δ u, (mem_stabU_iff.mp hs u).mpr hu, rfl⟩
  · rintro ⟨u, hu, hu'⟩
    have hy : y = (fieldAutE6 F δ)⁻¹ * MulAut.conj u * fieldAutE6 F δ := by
      rw [hu']
      group
    rw [hy]
    have hs' : (fieldAutE6 F δ)⁻¹ ∈ stabU F := (stabU F).inv_mem hs
    have h2 := mulAut_conj_conj (fieldAutE6 F δ)⁻¹ u
    rw [inv_inv] at h2
    rw [h2]
    exact ⟨(fieldAutE6 F δ)⁻¹ u, (mem_stabU_iff.mp hs' u).mpr hu, rfl⟩

@[expose] def B' (Θ : MulAut (C6 F) →* (F ≃+* F) × Multiplicative (ZMod 2)) (δ : F ≃+* F) :
    Subgroup (MulAut (C6 F)) :=
  stabU F ⊓ (Subgroup.zpowers ((δ, 1) : (F ≃+* F) × Multiplicative (ZMod 2))).comap Θ

theorem B'_le_stabU (Θ : MulAut (C6 F) →* (F ≃+* F) × Multiplicative (ZMod 2)) (δ : F ≃+* F) :
    B' Θ δ ≤ stabU F := inf_le_left

theorem mem_zpowers_of_sq {Q : Type*} [Group Q] {q : Q} (hq : q * q = 1) {x : Q}
    (hx : x ∈ Subgroup.zpowers q) : x = 1 ∨ x = q := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases Int.even_or_odd' k with ⟨n, hn | hn⟩
  · left
    rw [hn, zpow_mul]
    have : q ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hq
    rw [this, one_zpow]
  · right
    rw [hn, zpow_add_one, zpow_mul]
    have : q ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hq
    rw [this, one_zpow, one_mul]

theorem exists_pow_eq_one_of_mem {G : Type*} [Group G] {P : Subgroup G} (hP : IsPGroup 2 ↥P)
    {p : G} (hp : p ∈ P) : ∃ m : ℕ, p ^ (2 ^ m) = 1 := by
  obtain ⟨m, hm⟩ := hP ⟨p, hp⟩
  exact ⟨m, congrArg Subtype.val hm⟩

theorem intU_le_T0 (δ : F ≃+* F) : intU F ≤ T0 F δ := le_sup_left

theorem fieldAutE6_mem_T0 (δ : F ≃+* F) : fieldAutE6 F δ ∈ T0 F δ :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem T0_le_B' {Θ : MulAut (C6 F) →* (F ≃+* F) × Multiplicative (ZMod 2)} (hΘ : IsCoord Θ)
    (δ : F ≃+* F) : T0 F δ ≤ B' Θ δ := by
  refine sup_le ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨conj_mem_stabU hu, ?_⟩
    show Θ (MulAut.conj u) ∈ Subgroup.zpowers _
    rw [Θ_conj hΘ]
    exact Subgroup.one_mem _
  · rw [Subgroup.zpowers_le]
    refine ⟨fieldAutE6_mem_stabU δ, ?_⟩
    show Θ (fieldAutE6 F δ) ∈ Subgroup.zpowers _
    rw [Θ_fieldAut hΘ]
    exact Subgroup.mem_zpowers _

theorem T0_maximal [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {Θ : MulAut (C6 F) →* (F ≃+* F) × Multiplicative (ZMod 2)} (hΘ : IsCoord Θ)
    {δ : F ≃+* F} (hδ2 : δ * δ = 1) {P : Subgroup (MulAut (C6 F))} (hP : IsPGroup 2 ↥P)
    (hTP : T0 F δ ≤ P) (hPB : P ≤ B' Θ δ) : P ≤ T0 F δ := by
  intro p hp
  have hpB := hPB hp
  have hq : ((δ, 1) : (F ≃+* F) × Multiplicative (ZMod 2)) *
      ((δ, 1) : (F ≃+* F) × Multiplicative (ZMod 2)) = 1 := by
    refine Prod.ext ?_ ?_
    · simpa using hδ2
    · simp
  have hinU : ∀ y ∈ P, y ∈ stabU F → Θ y = 1 → y ∈ T0 F δ := by
    intro y hy hys hΘy
    obtain ⟨m, hm⟩ := exists_pow_eq_one_of_mem hP hy
    obtain ⟨g, rfl⟩ := e6_inner_of_ker hF Θ hΘ hΘy hm
    exact intU_le_T0 δ ⟨g, inner_two_mem_U6 hys hm, rfl⟩
  rcases mem_zpowers_of_sq hq hpB.2 with h1 | h2
  · exact hinU p hp hpB.1 h1
  · have hδP : fieldAutE6 F δ ∈ P := hTP (fieldAutE6_mem_T0 δ)
    have hp' : p * (fieldAutE6 F δ)⁻¹ ∈ P := P.mul_mem hp (P.inv_mem hδP)
    have hps : p * (fieldAutE6 F δ)⁻¹ ∈ stabU F :=
      (stabU F).mul_mem hpB.1 ((stabU F).inv_mem (fieldAutE6_mem_stabU δ))
    have hΘp : Θ (p * (fieldAutE6 F δ)⁻¹) = 1 := by
      rw [map_mul, map_inv, Θ_fieldAut hΘ, h2]
      exact mul_inv_cancel _
    have := hinU _ hp' hps hΘp
    have hmul := (T0 F δ).mul_mem this (fieldAutE6_mem_T0 δ)
    simpa using hmul

theorem mulAut_mul_conj' {M : Type*} [Group M] (φ : MulAut M) (g : M) :
    φ * MulAut.conj g = MulAut.conj (φ g) * φ := by
  rw [← mulAut_conj_conj, inv_mul_cancel_right]

theorem mem_T0 {δ : F ≃+* F} (hδ2 : δ * δ = 1) {y : MulAut (C6 F)} (hy : y ∈ T0 F δ) :
    ∃ u ∈ U6 F, y = MulAut.conj u ∨ y = MulAut.conj u * fieldAutE6 F δ := by
  have hs := fieldAutE6_mem_stabU (F := F) δ
  have hsq := fieldAutE6_sq hδ2
  have hU : ∀ u ∈ U6 F, fieldAutE6 F δ u ∈ U6 F := fun u hu => (mem_stabU_iff.mp hs u).mpr hu
  let Y : Subgroup (MulAut (C6 F)) :=
    { carrier := {y | ∃ u ∈ U6 F, y = MulAut.conj u ∨ y = MulAut.conj u * fieldAutE6 F δ}
      one_mem' := ⟨1, (U6 F).one_mem, Or.inl (by rw [map_one])⟩
      mul_mem' := by
        rintro a b ⟨u, hu, ha⟩ ⟨u', hu', hb⟩
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact ⟨u * u', (U6 F).mul_mem hu hu', Or.inl (by rw [map_mul])⟩
        · refine ⟨u * u', (U6 F).mul_mem hu hu', Or.inr ?_⟩
          rw [map_mul, mul_assoc]
        · refine ⟨u * fieldAutE6 F δ u', (U6 F).mul_mem hu (hU u' hu'), Or.inr ?_⟩
          rw [mul_assoc, mulAut_mul_conj', map_mul, mul_assoc]
        · refine ⟨u * fieldAutE6 F δ u', (U6 F).mul_mem hu (hU u' hu'), Or.inl ?_⟩
          calc MulAut.conj u * fieldAutE6 F δ * (MulAut.conj u' * fieldAutE6 F δ)
              = MulAut.conj u * (fieldAutE6 F δ * MulAut.conj u') * fieldAutE6 F δ := by group
            _ = MulAut.conj u * (MulAut.conj (fieldAutE6 F δ u') * fieldAutE6 F δ) *
                  fieldAutE6 F δ := by rw [mulAut_mul_conj']
            _ = MulAut.conj u * MulAut.conj (fieldAutE6 F δ u') *
                  (fieldAutE6 F δ * fieldAutE6 F δ) := by group
            _ = MulAut.conj (u * fieldAutE6 F δ u') := by rw [hsq, mul_one, map_mul]
      inv_mem' := by
        rintro a ⟨u, hu, ha⟩
        rcases ha with rfl | rfl
        · exact ⟨u⁻¹, (U6 F).inv_mem hu, Or.inl (by rw [map_inv])⟩
        · refine ⟨fieldAutE6 F δ u⁻¹, hU _ ((U6 F).inv_mem hu), Or.inr ?_⟩
          rw [mul_inv_rev, fieldAutE6_inv hδ2, ← map_inv, mulAut_mul_conj'] }
  have hle : T0 F δ ≤ Y := by
    refine sup_le ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact ⟨u, hu, Or.inl rfl⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨1, (U6 F).one_mem, Or.inr (by rw [map_one, one_mul])⟩
  exact hle hy

@[expose] def ULang (F : Type) [Field F] (δ : F ≃+* F) : Prop :=
  ∀ u ∈ U6 F, u * fieldAutE6 F δ u = 1 → ∃ v ∈ U6 F, u = v * (fieldAutE6 F δ v)⁻¹

theorem e6_lang [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {Θ : MulAut (C6 F) →* (F ≃+* F) × Multiplicative (ZMod 2)} (hΘ : IsCoord Θ)
    (hcomm : ∀ a b : F ≃+* F, a * b = b * a) {δ : F ≃+* F} (hδ2 : δ * δ = 1) (hδ1 : δ ≠ 1)
    (hU : ULang F δ) {σ : MulAut (C6 F)} (hσ : σ ∈ stabU F) (hσ2 : σ * σ = 1)
    (hΘσ : Θ σ = (δ, 1)) :
    ∃ β ∈ stabU F, σ = β * fieldAutE6 F δ * β⁻¹ := by
  haveI := finite_mulAut_E6 (K := F)
  have hσB : σ ∈ B' Θ δ := by
    refine ⟨hσ, ?_⟩
    show Θ σ ∈ Subgroup.zpowers _
    rw [hΘσ]
    exact Subgroup.mem_zpowers _
  obtain ⟨x, hx, hxT⟩ := exists_conj_into_maximal_two (T0_le_B' hΘ δ) (T0_isPGroup hδ2)
    (fun P hP hTP hPB => T0_maximal hF hΘ hδ2 hP hTP hPB) hσB (m := 1)
    (by rw [pow_one, pow_two]; exact hσ2)
  obtain ⟨u, hu, hy⟩ := mem_T0 hδ2 hxT
  have hQcomm : ∀ a b : (F ≃+* F) × Multiplicative (ZMod 2), a * b = b * a := fun a b =>
    Prod.ext (hcomm _ _) (mul_comm _ _)
  have hΘy : Θ (x⁻¹ * σ * x) = (δ, 1) := by
    rw [map_mul, map_mul, map_inv, hΘσ]
    have h1 := hQcomm ((Θ x)⁻¹) ((δ, 1) : (F ≃+* F) × Multiplicative (ZMod 2))
    rw [h1, mul_assoc]
    exact mul_eq_left.mpr (inv_mul_cancel (Θ x))
  have hy2 : (x⁻¹ * σ * x) * (x⁻¹ * σ * x) = 1 := by
    calc (x⁻¹ * σ * x) * (x⁻¹ * σ * x) = x⁻¹ * (σ * σ) * x := by group
      _ = 1 := by rw [hσ2]; group
  have hsq := fieldAutE6_sq hδ2
  rcases hy with hy | hy
  · exfalso
    rw [hy, Θ_conj hΘ] at hΘy
    have := (Prod.ext_iff.mp hΘy).1
    exact hδ1 (by simpa using this.symm)
  ·
    have hcocycle : u * fieldAutE6 F δ u = 1 := by
      apply conj_injective_C6 (F := F)
      rw [hy] at hy2
      have : MulAut.conj u * fieldAutE6 F δ * (MulAut.conj u * fieldAutE6 F δ) =
          MulAut.conj (u * fieldAutE6 F δ u) := by
        calc MulAut.conj u * fieldAutE6 F δ * (MulAut.conj u * fieldAutE6 F δ)
            = MulAut.conj u * (fieldAutE6 F δ * MulAut.conj u) * fieldAutE6 F δ := by group
          _ = MulAut.conj u * (MulAut.conj (fieldAutE6 F δ u) * fieldAutE6 F δ) *
                fieldAutE6 F δ := by rw [mulAut_mul_conj']
          _ = MulAut.conj u * MulAut.conj (fieldAutE6 F δ u) *
                (fieldAutE6 F δ * fieldAutE6 F δ) := by group
          _ = MulAut.conj (u * fieldAutE6 F δ u) := by rw [hsq, mul_one, map_mul]
      rw [← this, hy2, map_one]
    obtain ⟨v, hv, huv⟩ := hU u hu hcocycle
    refine ⟨x * MulAut.conj v, (stabU F).mul_mem (B'_le_stabU Θ δ hx) (conj_mem_stabU hv), ?_⟩
    have hconj : MulAut.conj u * fieldAutE6 F δ =
        MulAut.conj v * fieldAutE6 F δ * (MulAut.conj v)⁻¹ := by
      rw [huv, map_mul, map_inv, ← mulAut_conj_conj]
      group
    have : σ = x * (x⁻¹ * σ * x) * x⁻¹ := by group
    rw [this, hy, hconj]
    group

end Field

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG
