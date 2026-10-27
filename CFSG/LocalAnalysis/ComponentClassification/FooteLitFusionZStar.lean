module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitClassical

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

variable {H : Type} [Group H] [Finite H]

theorem conj_comm_cases {t t' : H} (ht : orderOf t = 2)
    (P : Sylow 2 ↥(centralizer ({t} : Set H)))
    (hP : ∀ x : H, (x ∈ (P : Subgroup _).map (centralizer ({t} : Set H)).subtype ∧
      IsConj t x) ↔ x = t ∨ x = t')
    {x : H} (hxt : IsConj t x) (hcomm : x * t = t * x) :
    x = t ∨ ∃ c ∈ centralizer ({t} : Set H), x = c * t' * c⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxC : x ∈ centralizer ({t} : Set H) := mem_centralizer_singleton_iff.mpr hcomm
  have hx2 : orderOf x = 2 := by
    obtain ⟨c, rfl⟩ := isConj_iff.mp hxt
    rw [← ht]
    exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective t
  have hpg : IsPGroup 2 (zpowers (⟨x, hxC⟩ : centralizer ({t} : Set H))) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx2, pow_one]
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq (centralizer ({t} : Set H)) P Q
  have hmem : (⟨x, hxC⟩ : centralizer ({t} : Set H)) ∈
      ((c • P : Sylow 2 (centralizer ({t} : Set H))) : Subgroup _) := hQ (mem_zpowers _)
  rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv] at hmem
  have hy : (c : H)⁻¹ * x * c ∈ (P : Subgroup _).map (centralizer ({t} : Set H)).subtype :=
    ⟨_, hmem, by simp⟩
  have hyc : IsConj t ((c : H)⁻¹ * x * c) :=
    hxt.trans (isConj_iff.mpr ⟨(c : H)⁻¹, by group⟩)
  have hct : (c : H) * t = t * c := mem_centralizer_singleton_iff.mp c.2
  rcases (hP _).mp ⟨hy, hyc⟩ with h | h
  · left
    calc x = c * ((c : H)⁻¹ * x * c) * (c : H)⁻¹ := by group
      _ = c * t * (c : H)⁻¹ := by rw [h]
      _ = t := by rw [hct]; group
  · right
    refine ⟨c, c.2, ?_⟩
    calc x = c * ((c : H)⁻¹ * x * c) * (c : H)⁻¹ := by group
      _ = c * t' * (c : H)⁻¹ := by rw [h]

end CFSG.ComponentClassification.FooteLit
