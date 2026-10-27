module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitReach
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {X : Type} [Group X]

@[expose] def SmallType (J : Subgroup X) : Prop :=
  Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) ∨
    Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2

@[expose] def ConclusionB1 (J : Subgroup X) : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) ∧
    ∃ (b : X) (L : Subgroup X) (ρ e : ℕ), orderOf b = 2 ∧ L ≤ centralizer ({b} : Set X) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set X))) ∧ ρ.Prime ∧ ρ ≠ 2 ∧
      1 ≤ e ∧ Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 ρ (2 * e) ∧
      zpowers b ≤ coreActionKernel L ∧
      ∃ P : Sylow 2 ↥(coreActionKernel L),
        (P : Subgroup _) = (zpowers b).subgroupOf (coreActionKernel L)

@[expose] def ConclusionB2a (a : X) (J : Subgroup X) : Prop :=
  ∀ b : X, orderOf b = 2 → b ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
    (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
    ∃ K : Subgroup X, UnbalancedGS.GSIsoCorr a J b K

@[expose] def ConclusionB2b (a : X) (J : Subgroup X) : Prop :=
  ∀ (b : X) (K : Subgroup X), orderOf b = 2 →
    b ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
    (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
    UnbalancedGS.GSIsoCorr a J b K →
    ∀ S : Subgroup X, S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
      (∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
        (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X))) →
      b ∈ S → (∀ s ∈ S, s * b = b * s) →
      S ≤ centralizer ({b} : Set X) ⊓ normalizer (K : Set X) ∧
        ∃ P : Sylow 2 ↥(centralizer ({b} : Set X) ⊓ normalizer (K : Set X)),
          (P : Subgroup _) = S.subgroupOf (centralizer ({b} : Set X) ⊓ normalizer (K : Set X))

@[expose] def CorollaryCConclusion (X : Type) [Group X] : Prop :=
  ∀ (a : X) (J : Subgroup X), orderOf a = 2 → J ≤ centralizer ({a} : Set X) →
    IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X))) →
    Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)) →
    ∀ E : Subgroup X, E ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
      Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
      ⁅J, centralizer ({a} : Set X) ⊓ ⨅ (e : X) (_ : e ∈ E) (_ : e ≠ 1),
          (pPrimeCore 2 (centralizer ({e} : Set X))).map (centralizer ({e} : Set X)).subtype⁆ =
        J →
      ∃ n : ℕ, Odd n ∧ 11 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))

theorem conclusionB2b_of_maximal {a x : X} {J : Subgroup X}
    (hmax : GSMaximalUnbalancingTriple a x J) : ConclusionB2b a J := by
  intro b K hb hbH _ hK S hSH hSsyl hbS hbZ
  exact ((hmax.2 b K hb (mem_inf.mp hbH).1 hK.1).2) S hSH hSsyl hbS hbZ

theorem theoremBInput_of_parts
    (hB : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
      Assembly.KProper Blueprint.Catalog X →
      (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
      ¬ OutcomeLocal.UOutcome X →
      ∀ (a x : X) (J : Subgroup X), GSMaximalUnbalancingTriple a x J → SmallType J →
        ConclusionB1 J ∨ ConclusionB2a a J)
    (hC : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
      Assembly.KProper Blueprint.Catalog X →
      (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
      ¬ OutcomeLocal.UOutcome X → CorollaryCConclusion X) :
    GSLit.TheoremBInput := by
  intro X _ _ _ hnonab hK hz hU
  refine ⟨fun a x J hmax htype => ?_, hC X hnonab hK hz hU⟩
  rcases hB X hnonab hK hz hU a x J hmax htype with h1 | h2
  · exact Or.inl h1
  · exact Or.inr ⟨h2, conclusionB2b_of_maximal hmax⟩

theorem conj_mem_coreActionKernel {J : Subgroup X} {h k : X} (hh : h ∈ normalizer (J : Set X))
    (hk : k ∈ coreActionKernel J) : h⁻¹ * k * h ∈ coreActionKernel J := by
  obtain ⟨hkN, hkJ⟩ := mem_coreActionKernel.mp hk
  refine mem_coreActionKernel.mpr ⟨mul_mem (mul_mem (inv_mem hh) hkN) hh, fun j hj => ?_⟩
  have hj' : h * j * h⁻¹ ∈ J := (mem_normalizer_iff.mp hh j).mp hj
  have hO := inv_mem
    (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J (pPrimeCore 2 J) hh)
  have h1 := (mem_normalizer_iff.mp hO _).mp (hkJ _ hj')
  rw [show h⁻¹ * ((h * j * h⁻¹)⁻¹ * k⁻¹ * (h * j * h⁻¹) * k) * h⁻¹⁻¹ =
    j⁻¹ * (h⁻¹ * k * h)⁻¹ * j * (h⁻¹ * k * h) by group] at h1
  exact h1

variable [Finite X]

theorem gsIsoCorr_conjugate {c b : X} {J L : Subgroup X} (h : UnbalancedGS.GSIsoCorr c J b L)
    (g : X) :
    UnbalancedGS.GSIsoCorr (g⁻¹ * c * g) (conjugate J g) (g⁻¹ * b * g) (conjugate L g) := by
  obtain ⟨hC, hK, hsup⟩ := UnbalancedGS.gsIsoCorr_iff_sup.mp h
  set φ : X ≃* X := MulAut.conj g⁻¹ with hφ
  have hφc : ∀ y : X, φ y = g⁻¹ * y * g := fun y => by
    rw [hφ, MulAut.conj_apply, inv_inv]
  have hconjL : conjugate (conjugate L g) (g⁻¹ * c * g) = conjugate (conjugate L c) g := by
    simp only [conjugate, map_map]
    congr 1
    ext y
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply]
    group
  refine UnbalancedGS.gsIsoCorr_iff_sup.mpr ⟨GSLit.gsCorr_conjugate hC g, ?_, ?_⟩
  · rw [hconjL, show conjugate L g ⊔ conjugate (conjugate L c) g =
      conjugate (L ⊔ conjugate L c) g from (Subgroup.map_sup _ _ _).symm, hK]
  · have h1 := congrArg (Subgroup.map φ.toMonoidHom) hsup
    rw [Subgroup.map_sup, GSLit.map_gsFixedLayer, GSLit.map_map_pPrimeCore, hφc] at h1
    exact h1

theorem conclusionB2a_of_sylow {a : X} {J S : Subgroup X}
    (hS : ∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
      (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X)))
    (h : ∀ b ∈ S ⊓ coreActionKernel J, orderOf b = 2 →
      ∃ K : Subgroup X, UnbalancedGS.GSIsoCorr a J b K) :
    ConclusionB2a a J := by
  intro b hb hbH hbJ
  have hbC : b ∈ coreActionKernel J := mem_coreActionKernel.mpr ⟨(mem_inf.mp hbH).2, hbJ⟩
  have hE : IsPGroup 2 (zpowers b) := IsPGroup.of_card (by
    rw [Nat.card_zpowers, hb, pow_one])
  obtain ⟨g, hg, hgS⟩ := exists_conjugate_le_of_sylow hS
    ((zpowers_le (G := X)).mpr hbH) hE
  have hga : g ∈ centralizer ({a} : Set X) := (mem_inf.mp hg).1
  have hgJ : g ∈ normalizer (J : Set X) := (mem_inf.mp hg).2
  have hb'S : g⁻¹ * b * g ∈ S := hgS (by
    rw [mem_conjugate_iff, show g * (g⁻¹ * b * g) * g⁻¹ = b by group]
    exact mem_zpowers b)
  have hb'C : g⁻¹ * b * g ∈ coreActionKernel J := conj_mem_coreActionKernel hgJ hbC
  have hb'2 : orderOf (g⁻¹ * b * g) = 2 := by
    rw [show g⁻¹ * b * g = (MulAut.conj g⁻¹) b by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq, hb]
  obtain ⟨K, hK⟩ := h _ (mem_inf.mpr ⟨hb'S, hb'C⟩) hb'2
  refine ⟨conjugate K g⁻¹, ?_⟩
  have h1 := gsIsoCorr_conjugate hK g⁻¹
  have hga' : g * a * g⁻¹ = a := by
    rw [mem_centralizer_singleton_iff.mp hga, mul_inv_cancel_right]
  rwa [inv_inv, hga', conjugate_eq_of_mem_normalizer (inv_mem hgJ),
    show g * (g⁻¹ * b * g) * g⁻¹ = b by group] at h1

end CFSG.ComponentClassification.GSThmB
