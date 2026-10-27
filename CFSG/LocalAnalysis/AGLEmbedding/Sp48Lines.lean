module

public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorLayer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section LinesAux

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_centralizer {Y : Type*} [Group Y] (T : Subgroup Y) (g : Y) :
    (Subgroup.centralizer (T : Set Y)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((T.map (MulAut.conj g).toMonoidHom : Subgroup Y) : Set Y) := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hc t ht
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * t * g⁻¹ * (g * c * g⁻¹) = g * (t * c) * g⁻¹ := by group
      _ = g * (c * t) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * (g * t * g⁻¹) := by group
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro t ht
    have h1 := Subgroup.mem_centralizer_iff.mp hx (g * t * g⁻¹) ⟨t, ht, by simp [MulAut.conj_apply]⟩
    calc t * (g⁻¹ * x * g) = g⁻¹ * ((g * t * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * t * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * x * g * t := by group

omit [Finite G] in
theorem barM_inf_preM {M A : Subgroup G} {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hT : T ≤ barM M A) : barM M (A ⊓ preM M T) = T := by
  apply le_antisymm
  · rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
    exact (mem_preM hxM).mp (Subgroup.mem_subgroupOf.mp hx).2
  · intro t ht
    obtain ⟨⟨a, haM⟩, ha, rfl⟩ := hT ht
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
      ⟨Subgroup.mem_subgroupOf.mp ha, (mem_preM haM).mpr ht⟩)

end LinesAux

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section Lines

variable {Y : Type*} [Group Y]

@[expose] def lineOf (Ab B B' : Subgroup Y) : Subgroup Y :=
  (Subgroup.centralizer (B : Set Y) ⊓ Subgroup.centralizer (B' : Set Y)) ⊓ Ab

theorem lineOf_comm (Ab B B' : Subgroup Y) : lineOf Ab B B' = lineOf Ab B' B := by
  rw [lineOf, lineOf, inf_comm (Subgroup.centralizer (B : Set Y))]

theorem lineOf_map_conj (Ab B B' : Subgroup Y) (g : Y) :
    (lineOf Ab B B').map (MulAut.conj g).toMonoidHom =
      lineOf (Ab.map (MulAut.conj g).toMonoidHom) (B.map (MulAut.conj g).toMonoidHom)
        (B'.map (MulAut.conj g).toMonoidHom) := by
  rw [lineOf, lineOf, Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, map_conj_centralizer,
    map_conj_centralizer]

theorem lineOf_cases (Ab B₀ B₁ B₂ : Subgroup Y) {B B' : Subgroup Y}
    (hB : B = B₀ ∨ B = B₁ ∨ B = B₂) (hB' : B' = B₀ ∨ B' = B₁ ∨ B' = B₂) (hne : B ≠ B') :
    lineOf Ab B B' = lineOf Ab B₁ B₂ ∨ lineOf Ab B B' = lineOf Ab B₀ B₂ ∨
      lineOf Ab B B' = lineOf Ab B₀ B₁ := by
  rcases hB with rfl | rfl | rfl <;> rcases hB' with rfl | rfl | rfl
  · exact absurd rfl hne
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (lineOf_comm _ _ _))
  · exact absurd rfl hne
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (lineOf_comm _ _ _))
  · exact Or.inl (lineOf_comm _ _ _)
  · exact absurd rfl hne

end Lines

end CFSG.AGLEmbedding
