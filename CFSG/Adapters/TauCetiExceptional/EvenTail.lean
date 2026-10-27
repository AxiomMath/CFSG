module

public import CFSG.Adapters.TauCetiExceptional.EvenDegree
public import CFSG.Adapters.TauCetiExceptional.EvenConj
public import CFSG.Adapters.TauCetiExceptional.BigCellEndgameE

public noncomputable section

namespace CFSG.TauCetiBridge.Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti BigCell
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag}

theorem mem_adjointGroup_of_conj_entrywise_two
    {L : Type} [Field L] [IsAlgClosed L]
    (i₀ : Fin τ.rank) (hA3 : xCoeff τ L i₀ 3 = 0) (E : Subfield L) [Finite E] {k : ℕ}
    (hE : Nat.card E = 2 ^ k) (hk : 3 ≤ k) (σ : E ≃+* E) (t : Eˣ)
    (ht : ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ pairBound τ → t ^ m ≠ 1) (h : ModGL τ L)
    (hz : ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0)
    (hσ : ∀ x ∈ adjointGroup τ E, h * baseChangeGL E.subtype x * h⁻¹ =
      baseChangeGL E.subtype (Units.map (entrywiseHom σ.toRingHom) x)) :
    h ∈ adjointGroup τ L := by
  have hxc : ∀ i (c : E), h * xUnit τ L i (c : L) * h⁻¹ = xUnit τ L i ((σ c : E) : L) := by
    intro i c
    have e := hσ _ (xUnit_mem_adjointGroup i c)
    have e2 : Units.map (entrywiseHom σ.toRingHom) (xUnit τ E i c) = xUnit τ E i (σ c) :=
      Units.ext (entrywise_xOp σ.toRingHom i c)
    rw [e2, baseChangeGL_xUnit, baseChangeGL_xUnit] at e
    exact e
  have hσid := eq_refl_of_conj_xUnit E hE hk h hA3 σ (hxc i₀)
  have hσ' : σ.toRingHom = RingHom.id E := by
    rw [hσid]
    rfl
  have hfix : ∀ x ∈ adjointGroup τ E,
      h * baseChangeGL E.subtype x = baseChangeGL E.subtype x * h := by
    intro x hx
    have e := hσ x hx
    rw [hσ', show Units.map (entrywiseHom (RingHom.id E)) x = x from
      Units.ext (entrywise_id _)] at e
    exact mul_inv_eq_iff_eq_mul.1 e
  set t' : Lˣ := Units.map E.subtype.toMonoidHom t
  have ht' : ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ pairBound τ → t' ^ m ≠ 1 := by
    intro m hm hb e
    apply ht m hm hb
    have e' : Units.map E.subtype.toMonoidHom (t ^ m) = Units.map E.subtype.toMonoidHom 1 := by
      rw [map_zpow, e, map_one]
    exact Units.map_injective (f := E.subtype.toMonoidHom) E.subtype_injective e'
  have htor : ∀ j, h * torusElt τ L j t' = torusElt τ L j t' * h := by
    intro j
    have e := hfix _ (torusElt_mem_adjointGroup j t)
    rwa [baseChangeGL_torusElt] at e
  have hx1 : ∀ i, h * xUnit τ L i 1 = xUnit τ L i 1 * h := by
    intro i
    have e := hfix _ (xUnit_mem_adjointGroup i (1 : E))
    rwa [baseChangeGL_xUnit, map_one] at e
  exact mem_adjointGroup_of_isUnit_bigCellDet h hz
    (bigCellDet_ne_zero_of_diagonal h (diagonal_of_commute ht' htor hx1))

theorem mem_adjointGroup_of_conj_two
    {L : Type} [Field L] [IsAlgClosed L]
    (hτ : HasQuadraticNode τ) (E : Subfield L) [Finite E] {k : ℕ} (hE : Nat.card E = 2 ^ k)
    (hk : 3 ≤ k) (σ : E ≃+* E) (t : Eˣ)
    (ht : ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ pairBound τ → t ^ m ≠ 1) {H : Subgroup (ModGL τ L)}
    (hCH : adjointGroup τ L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0)
    {h : ModGL τ L} (hh : h ∈ H) {g : ModGL τ L} (hg : g ∈ adjointGroup τ L)
    (hσ : ∀ x ∈ adjointGroup τ E, g⁻¹ * h * baseChangeGL E.subtype x * (g⁻¹ * h)⁻¹ =
      baseChangeGL E.subtype (Units.map (entrywiseHom σ.toRingHom) x)) :
    h ∈ adjointGroup τ L := by
  have hh' : g⁻¹ * h ∈ H := H.mul_mem (H.inv_mem (hCH hg)) hh
  obtain ⟨i₀, hA3⟩ := hτ
  have hmem := mem_adjointGroup_of_conj_entrywise_two i₀ (hA3 L) E hE hk σ t ht _ (hH _ hh') hσ
  have e : h = g * (g⁻¹ * h) := by group
  rw [e]
  exact mul_mem hg hmem

theorem mem_adjointGroup_of_inner_entrywise_two
    {L : Type} [Field L] [IsAlgClosed L]
    (hτ : HasQuadraticNode τ) (E : Subfield L) [Finite E] {k : ℕ} (hE : Nat.card E = 2 ^ k)
    (hk : 3 ≤ k) (σ : E ≃+* E) (t : Eˣ)
    (ht : ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ pairBound τ → t ^ m ≠ 1) {H : Subgroup (ModGL τ L)}
    (hCH : adjointGroup τ L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0)
    {h : ModGL τ L} (hh : h ∈ H) (g : adjointGroup τ E) (α : MulAut (adjointGroup τ E))
    (hα : ∀ x : adjointGroup τ E,
      baseChangeGL E.subtype (α x : ModGL τ E) = h * baseChangeGL E.subtype (x : ModGL τ E) * h⁻¹)
    (hgσ : ∀ x : adjointGroup τ E, (α x : ModGL τ E) =
      (g : ModGL τ E) * Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ E) *
        (g : ModGL τ E)⁻¹) :
    h ∈ adjointGroup τ L := by
  refine mem_adjointGroup_of_conj_two hτ E hE hk σ t ht hCH hH hh
    (map_baseChangeGL_adjointGroup_le E.subtype (Subgroup.mem_map.2 ⟨(g : ModGL τ E), g.2, rfl⟩))
    fun x hx => ?_
  have e : (baseChangeGL E.subtype (g : ModGL τ E))⁻¹ * h * baseChangeGL E.subtype x *
      ((baseChangeGL E.subtype (g : ModGL τ E))⁻¹ * h)⁻¹ =
      (baseChangeGL E.subtype (g : ModGL τ E))⁻¹ *
        (h * baseChangeGL E.subtype x * h⁻¹) * baseChangeGL E.subtype (g : ModGL τ E) := by
    group
  rw [e, ← hα ⟨x, hx⟩, hgσ ⟨x, hx⟩, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  group

theorem mem_adjointGroup_of_diag_entrywise_two
    {L : Type} [Field L] [IsAlgClosed L]
    (hτ : τ ≠ .G2) (E : Subfield L) [Finite E] {k : ℕ} (hE : Nat.card E = 2 ^ k) (hk : 3 ≤ k)
    (σ : E ≃+* E) (t : Eˣ) (ht : ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ pairBound τ → t ^ m ≠ 1)
    {H : Subgroup (ModGL τ L)} (hCH : adjointGroup τ L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0)
    {h : ModGL τ L} (hh : h ∈ H) (g : adjointGroup τ E) (a : Fin τ.rank → Eˣ)
    (α : MulAut (adjointGroup τ E))
    (hα : ∀ x : adjointGroup τ E,
      baseChangeGL E.subtype (α x : ModGL τ E) = h * baseChangeGL E.subtype (x : ModGL τ E) * h⁻¹)
    (hgσ : ∀ x : adjointGroup τ E, (α x : ModGL τ E) =
      (g : ModGL τ E) * rootDiagUnit τ a * Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ E) *
        (rootDiagUnit τ a)⁻¹ * (g : ModGL τ E)⁻¹) :
    h ∈ adjointGroup τ L := by
  set g' : ModGL τ L := baseChangeGL E.subtype ((g : ModGL τ E) * rootDiagUnit τ a) with hg'
  have hgL : g' ∈ adjointGroup τ L := by
    rw [hg', map_mul, CFSG.TauCetiBridge.BigCell.baseChangeGL_rootDiagUnit]
    exact mul_mem (map_baseChangeGL_adjointGroup_le E.subtype
      (Subgroup.mem_map.2 ⟨(g : ModGL τ E), g.2, rfl⟩))
      (exceptional_Lang_adjoint_diagonal_lift τ L _).1
  refine mem_adjointGroup_of_conj_two (hasQuadraticNode_of_ne_G2 hτ) E hE hk σ t ht hCH hH hh
    hgL fun x hx => ?_
  have e : g'⁻¹ * h * baseChangeGL E.subtype x * (g'⁻¹ * h)⁻¹ =
      g'⁻¹ * (h * baseChangeGL E.subtype x * h⁻¹) * g' := by group
  rw [e, ← hα ⟨x, hx⟩, hgσ ⟨x, hx⟩, hg', ← map_inv, ← map_mul, ← map_mul]
  congr 1
  group

section Endgame

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [IsAlgClosed L] [CharP L p]
  [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L]

theorem le_adjointGroup_of_normalForm_two
    (hp : p = 2) (hτ : HasQuadraticNode τ)
    (hNF : ∀ k, 3 ≤ k → InnerFieldNormalForm τ (frobeniusFixedSubfield L p k))
    (H : Subgroup (ModGL τ L)) (hCH : adjointGroup τ L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0) :
    H ≤ adjointGroup τ L := by
  subst hp
  intro h hh
  obtain ⟨k, hk, ⟨t, ht⟩, α, hα⟩ := exists_conj_mulAut_of_three_le (p := 2) H hCH hH hh
  have : Finite (frobeniusFixedSubfield L 2 k) := finite_frobeniusFixedSubfield L 2 k (by omega)
  obtain ⟨g, σ, hgσ⟩ := hNF k hk α
  exact mem_adjointGroup_of_inner_entrywise_two hτ _
    (card_frobeniusFixedSubfield L 2 k (by omega)) hk σ t ht hCH hH hh g α hα hgσ

theorem le_adjointGroup_of_diagNormalForm_two
    (hp : p = 2) (hτ : τ ≠ .G2)
    (hNF : ∀ k, 3 ≤ k → DiagFieldNormalForm τ (frobeniusFixedSubfield L p k))
    (H : Subgroup (ModGL τ L)) (hCH : adjointGroup τ L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0) :
    H ≤ adjointGroup τ L := by
  subst hp
  intro h hh
  obtain ⟨k, hk, ⟨t, ht⟩, α, hα⟩ := exists_conj_mulAut_of_three_le (p := 2) H hCH hH hh
  have : Finite (frobeniusFixedSubfield L 2 k) := finite_frobeniusFixedSubfield L 2 k (by omega)
  obtain ⟨g, a, σ, hgσ⟩ := hNF k hk α
  exact mem_adjointGroup_of_diag_entrywise_two hτ _
    (card_frobeniusFixedSubfield L 2 k (by omega)) hk σ t ht hCH hH hh g a α hα hgσ

theorem le_adjointGroup_G2_two
    (hp : p = 2) (H : Subgroup (ModGL .G2 L))
    (hCH : adjointGroup .G2 L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat .G2 P →
      evalMat (natMat .G2 L (h : Module.End L (RootModule .G2 L))) P = 0) :
    H ≤ adjointGroup .G2 L :=
  le_adjointGroup_of_normalForm_two hp hasQuadraticNode_G2 (fun k hk α => by
    subst hp
    obtain ⟨⟨g, σ⟩, hgσ, -⟩ :=
      (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
        (by omega : 2 ≤ k) _ (card_frobeniusFixedSubfield L 2 k (by omega))).1 α
    exact ⟨g, σ, hgσ⟩) H hCH hH

theorem le_adjointGroup_E8_two
    (hp : p = 2) (H : Subgroup (ModGL .E8 L))
    (hCH : adjointGroup .E8 L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat .E8 P →
      evalMat (natMat .E8 L (h : Module.End L (RootModule .E8 L))) P = 0) :
    H ≤ adjointGroup .E8 L :=
  le_adjointGroup_of_diagNormalForm_two hp (by decide) (fun k hk => by
    have := finite_frobeniusFixedSubfield L p k (by omega)
    exact diagFieldNormalForm_E7_E8 (Or.inr rfl) _) H hCH hH

end Endgame

end CFSG.TauCetiBridge.Even
