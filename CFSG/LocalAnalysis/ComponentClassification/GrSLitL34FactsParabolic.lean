module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Out

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open scoped Pointwise

private theorem factorization_20160 : (20160 : ℕ).factorization 2 = 6 := by
  have h : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]
  simp

theorem card_T0_subgroupOf :
    Nat.card (T0.subgroupOf S) = 2 ^ (Nat.card S).factorization 2 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe T0_le_S).toEquiv, card_T0, card_S,
    factorization_20160]
  norm_num

noncomputable def sylowT0
    [Fact (Nat.Prime 2)] : Sylow 2 S :=
  Sylow.ofCard (T0.subgroupOf S) card_T0_subgroupOf

theorem coe_sylowT0
    [Fact (Nat.Prime 2)] : ((sylowT0 : Sylow 2 S) : Subgroup S) = T0.subgroupOf S :=
  Sylow.coe_ofCard _ _

theorem mem_normalizer_T0_subgroupOf
    {b : Equiv.Perm (Fin 42)} (hb : b ∈ B0) :
    (⟨b, B0_le_S hb⟩ : S) ∈ Subgroup.normalizer ((T0.subgroupOf S : Subgroup S) : Set S) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hn := Subgroup.mem_normalizer_iff.1 (B0_le_normalizer hb) (h : Equiv.Perm (Fin 42))
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact hn

theorem conj_mem_normalizer_smul {G : Type*} [Group G] {H : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (H : Set G)) (g : G) :
    g * n * g⁻¹ ∈ Subgroup.normalizer ((MulAut.conj g • H : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro x
  simp only [Subgroup.mem_smul_pointwise_iff_exists, MulAut.smul_def, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨n * y * n⁻¹, (hn y).1 hy, by group⟩
  · rintro ⟨y, hy, hxy⟩
    refine ⟨n⁻¹ * y * n, ?_, ?_⟩
    · have := (hn (n⁻¹ * y * n)).2
      rw [show n * (n⁻¹ * y * n) * n⁻¹ = y by group] at this
      exact this hy
    · have e : g * (n⁻¹ * y * n) * g⁻¹ = (g * n * g⁻¹)⁻¹ * (g * y * g⁻¹) * (g * n * g⁻¹) := by
        group
      rw [e, hxy]
      group

theorem symm_mem_normalizer {K L : Type*} [Group K] [Group L] (φ : K ≃* L) {H : Subgroup K}
    {m : L} (hm : m ∈ Subgroup.normalizer ((H.map φ.toMonoidHom : Subgroup L) : Set L)) :
    φ.symm m ∈ Subgroup.normalizer (H : Set K) := by
  rw [Subgroup.mem_normalizer_iff] at hm ⊢
  intro y
  have e := hm (φ y)
  have h1 : φ y ∈ H.map φ.toMonoidHom ↔ y ∈ H := by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have h2 : m * φ y * m⁻¹ ∈ H.map φ.toMonoidHom ↔ φ.symm m * y * (φ.symm m)⁻¹ ∈ H := by
    rw [Subgroup.mem_map_equiv]
    simp
  rw [← h1, e, h2]

theorem l34ParabolicFact :
    L34ParabolicFact := by
  intro K _ _ hK T X hN h9
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hK
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S sylowT0
    (T.mapSurjective (f := φ.toMonoidHom) φ.surjective)
  have hgT : MulAut.conj g • (T0.subgroupOf S) = (T : Subgroup K).map φ.toMonoidHom := by
    have h1 := congrArg (fun P : Sylow 2 S => (P : Subgroup S)) hg
    simp only [Sylow.coe_subgroup_smul] at h1
    exact h1
  set ψ : K →* S := (MulAut.conj g⁻¹).toMonoidHom.comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := by
    rw [hψ, MonoidHom.coe_comp]
    exact (MulAut.conj g⁻¹).injective.comp φ.injective
  set Y : Subgroup (Equiv.Perm (Fin 42)) := (X.map ψ).map S.subtype with hY
  have hYS : Y ≤ S := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hcard : Nat.card Y = Nat.card X := by
    rw [hY, Subgroup.card_subtype, Subgroup.card_map_of_injective hψinj]
  have hBY : B0 ≤ Y := by
    intro b hb
    refine ⟨⟨b, B0_le_S hb⟩, ⟨φ.symm (g * ⟨b, B0_le_S hb⟩ * g⁻¹), ?_, ?_⟩, rfl⟩
    · have hn := conj_mem_normalizer_smul (mem_normalizer_T0_subgroupOf hb) g
      rw [hgT] at hn
      exact hN (symm_mem_normalizer φ hn)
    · simp [hψ, mul_assoc]
  have hYeq := eq_S_of_borel_le hYS hBY (hcard ▸ h9)
  rw [eq_top_iff]
  intro k _
  have hmem : ((ψ k : S) : Equiv.Perm (Fin 42)) ∈ Y := by
    rw [hYeq]
    exact (ψ k).2
  obtain ⟨y, ⟨x, hx, hxy⟩, hyy⟩ := hmem
  have hy : y = ψ k := Subtype.ext hyy
  rw [hy] at hxy
  rwa [← hψinj hxy]

end CFSG.ComponentClassification.GrSLit.L34Facts
