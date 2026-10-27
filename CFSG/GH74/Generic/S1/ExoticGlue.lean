module

public import CFSG.GH74.Generic.S1.Glue

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic

@[expose] def GraphLinRefine : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F % 4 = 3 → ∀ α : MulAut ↥(StatedSL 4 F),
    α * α = 1 → IsGraphLike (StatedSL 4 F) α →
      GoodFixedCentral (Nat.card F = 3) α ∨ IsExoticLin (StatedSL 4 F) α

@[expose] def GraphUniRefine : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (q : ℕ), Nat.card F = q ^ 2 → q % 4 = 1 →
    ∀ α : MulAut ↥(StatedSU 4 q F), α * α = 1 → IsGraphFieldLike (StatedSU 4 q F) q α →
      GoodFixedCentral False α ∨ IsExoticUni (StatedSU 4 q F) q α

@[expose] def IsExoticAut {K : Type} [Group K] (α : MulAut K) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (e : K ≃* StatedSL 4 F), Nat.card F % 4 = 3 ∧
      IsExoticLin (StatedSL 4 F) (MulAut.congr e α)) ∨
  (∃ (q : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (e : K ≃* StatedSU 4 q F),
      Nat.card F = q ^ 2 ∧ q % 4 = 1 ∧ IsExoticUni (StatedSU 4 q F) q (MulAut.congr e α))

@[expose] def S1ExoticExcludedExplicit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ∀ (v : G) (hv : v ∈ centralizer ({x} : Set G)), IsConj x v → v ≠ x → v * v = 1 →
      barOf hv ∉ K → ∀ α : MulAut ↥K,
        (∀ k : ↥K, ((α k : ↥K) : CentralizerBar x) = barOf hv * k * (barOf hv)⁻¹) →
          IsExoticAut α → False

theorem s1ExoticExcluded_of_explicit (hL : GraphLinRefine) (hU : GraphUniRefine)
    (h : S1ExoticExcludedExplicit) : S1ExoticExcluded := by
  intro G _ _ x K hset hfr v hv hconj hvx hv2 hvK α hα hGr hnotA
  have hα2 : α * α = 1 := by
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    have h1 := hα (α k)
    have h2 := hα k
    change ((α (α k) : ↥K) : CentralizerBar x) = k
    rw [h1, h2]
    have hbar2 : barOf hv * barOf hv = 1 := by
      have : proj x ((⟨v, hv⟩ : ↥(centralizer ({x} : Set G))) * ⟨v, hv⟩) = 1 := by
        rw [show (⟨v, hv⟩ : ↥(centralizer ({x} : Set G))) * ⟨v, hv⟩ = 1 from Subtype.ext hv2,
          map_one]
      rwa [map_mul] at this
    calc barOf hv * (barOf hv * (k : CentralizerBar x) * (barOf hv)⁻¹) * (barOf hv)⁻¹
        = (barOf hv * barOf hv) * (k : CentralizerBar x) * (barOf hv * barOf hv)⁻¹ := by group
      _ = k := by rw [hbar2]; simp
  refine h G x K hset hfr v hv hconj hvx hv2 hvK α hα ?_
  rcases hGr with ⟨F, _, _, e, hF, hG⟩ | ⟨q, F, _, _, e, hF, hq, hG⟩
  · rcases hL F hF (MulAut.congr e α) (congr_mul_self_eq_one e hα2) hG with hA | hE
    · exfalso
      apply hnotA
      have h1 := (hA.of_mulEquiv e.symm).mono (T' := ThreeModel ↥K) (fun h => ⟨F, inferInstance,
        inferInstance, h, Or.inl ⟨e⟩⟩)
      rwa [congr_symm_congr] at h1
    · exact Or.inl ⟨F, inferInstance, inferInstance, e, hF, hE⟩
  · rcases hU F q hF hq (MulAut.congr e α) (congr_mul_self_eq_one e hα2) hG with hA | hE
    · exfalso
      apply hnotA
      have h1 := (hA.of_mulEquiv e.symm).mono (T' := ThreeModel ↥K) (fun h => h.elim)
      rwa [congr_symm_congr] at h1
    · exact Or.inr ⟨q, F, inferInstance, inferInstance, e, hF, hq, hE⟩

end CFSG.GH74.Generic.S1
