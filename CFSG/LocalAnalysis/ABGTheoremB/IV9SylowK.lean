module

public import CFSG.LocalAnalysis.ABGTheoremB.IV7Data
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.ABGTheoremB.Setting

open CFSG.ABGLocalTools

section Frattini

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem sylowK_isSylowOf_map_conj {P K : Subgroup G} (hP : IsSylowOf p P K) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    IsSylowOf p (P.map (MulAut.conj g).toMonoidHom) K := by
  refine isSylowOf_of_card (fun y hy => ?_) ?_
  · obtain ⟨z, hz, rfl⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.mp hg z).mp (hP.le hz)
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP.card_eq]

private theorem sylowK_exists_mem_normalizer {P K : Subgroup G} (hP : IsSylowOf p P K) {x : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k ∈ K, k⁻¹ * x ∈ Subgroup.normalizer (P : Set G) := by
  obtain ⟨k, hk, hconj⟩ := hP.exists_mem_conj (sylowK_isSylowOf_map_conj hP hx)
  refine ⟨k, hk, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 : y ∈ P ↔ x * y * x⁻¹ ∈ P.map (MulAut.conj x).toMonoidHom := by
    constructor
    · intro hy
      exact ⟨y, hy, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    · rintro ⟨z, hz, hzy⟩
      have hzy' : x * z * x⁻¹ = x * y * x⁻¹ := hzy
      rwa [← mul_left_cancel (mul_right_cancel hzy')]
  rw [h1, hconj, show k⁻¹ * (x * y * x⁻¹) * k = k⁻¹ * x * y * (k⁻¹ * x)⁻¹ by group]

end Frattini

theorem exists_sylow_two_between_D_and_normalizer_R {G : Type*} [Group G] [Finite G]
    (σ : Setting G) (hσ : σ.IsValid) {r : ℕ} (hr : σ.HypIV7 r) (d : σ.IV7Data r) :
    ∃ S₁ : Sylow 2 G, σ.D ≤ (S₁ : Subgroup G) ∧
      (S₁ : Subgroup G) ≤ Subgroup.normalizer (d.R : Set G) ⊓ σ.N := by
  have : Fact r.Prime := ⟨hr.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Subgroup.normalizer (d.R : Set G) ⊓ σ.N with hK
  have hKN : K ≤ σ.N := inf_le_right
  have hsup : σ.ON ⊔ K = σ.N := by
    refine le_antisymm (sup_le σ.ON_le_N hKN) fun x hxN => ?_
    obtain ⟨o, ho, hon⟩ := sylowK_exists_mem_normalizer d.R_sylow (σ.N_le_normalizer_ON hxN)
    have hoK : o⁻¹ * x ∈ K := ⟨hon, σ.N.mul_mem (σ.N.inv_mem (σ.ON_le_N ho)) hxN⟩
    rw [show x = o * (o⁻¹ * x) by group]
    exact Subgroup.mul_mem_sup ho hoK
  have hKodd : ¬ 2 ∣ K.relIndex σ.N := by
    rw [← hsup, relIndex_sup_eq_relIndex_of_le_normalizer (hKN.trans σ.N_le_normalizer_ON)]
    intro h2
    exact (Nat.not_even_iff_odd.mpr σ.odd_card_ON)
      (even_iff_two_dvd.mpr (h2.trans (Subgroup.relIndex_dvd_card K σ.ON)))
  have hNodd : ¬ 2 ∣ σ.N.index := by
    intro h2
    apply Sylow.not_dvd_index σ.S
    rw [← Subgroup.relIndex_mul_index (σ.S_le_N hσ)]
    exact Dvd.dvd.mul_left h2 _
  have hDK : σ.D ≤ K := le_inf d.R_D (σ.D_le_N hσ)
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  obtain ⟨Q₀, hQ₀⟩ := (hD2.comap_subtype (K := K)).exists_le_sylow
  have hQK : (Q₀ : Subgroup K).map K.subtype ≤ K := Subgroup.map_subtype_le _
  obtain ⟨-, hQ2, hQodd⟩ := isSylowOf_iff.mp (⟨Q₀, rfl⟩ : IsSylowOf 2 ((Q₀ : Subgroup K).map
    K.subtype) K)
  have hQindex : ¬ 2 ∣ ((Q₀ : Subgroup K).map K.subtype).index := by
    rw [← Subgroup.relIndex_mul_index hQK, ← Subgroup.relIndex_mul_index hKN]
    intro h
    rcases Nat.prime_two.dvd_mul.mp h with h | h
    · exact hQodd h
    · rcases Nat.prime_two.dvd_mul.mp h with h | h
      · exact hKodd h
      · exact hNodd h
  refine ⟨hQ2.toSylow hQindex, fun g hg => ?_, hQK⟩
  exact ⟨⟨g, hDK hg⟩, hQ₀ (show (⟨g, hDK hg⟩ : K) ∈ σ.D.comap K.subtype from hg), rfl⟩

end CFSG.ABGTheoremB.Setting
