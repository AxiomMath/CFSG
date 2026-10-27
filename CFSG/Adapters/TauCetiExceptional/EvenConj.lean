module

public import CFSG.Adapters.TauCetiExceptional.EvenLang
public import CFSG.Adapters.TauCetiExceptional.BigCellEndgame

public noncomputable section

namespace CFSG.TauCetiBridge.Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti BigCell

variable {τ : Tag} {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [IsAlgClosed L] [CharP L p]
  [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L]

theorem exists_conj_mulAut_of_three_le
    (H : Subgroup (ModGL τ L))
    (hCH : adjointGroup τ L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0)
    {h : ModGL τ L} (hh : h ∈ H) :
    ∃ k, 3 ≤ k ∧ (∃ t : (frobeniusFixedSubfield L p k)ˣ,
      ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ pairBound τ → t ^ m ≠ 1) ∧
      ∃ α : MulAut (adjointGroup τ (frobeniusFixedSubfield L p k)),
        ∀ x : adjointGroup τ (frobeniusFixedSubfield L p k),
          baseChangeGL (frobeniusFixedSubfield L p k).subtype
              (α x : ModGL τ (frobeniusFixedSubfield L p k)) =
            h * baseChangeGL (frobeniusFixedSubfield L p k).subtype
              (x : ModGL τ (frobeniusFixedSubfield L p k)) * h⁻¹ := by
  classical
  set S : Finset L := Finset.univ.image (fun ij : Fin (nLab τ) × Fin (nLab τ) =>
      natMat τ L (h : Module.End L (RootModule τ L)) ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin (nLab τ) × Fin (nLab τ) =>
      natMat τ L ((h⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) ij.1 ij.2) with hSdef
  obtain ⟨k, hk, hk₀, hS⟩ := exists_frobeniusFixedSubfield_of_finset (p := p) S
    (k₀ := pairBound τ + 3) (by omega)
  have hk3 : pairBound τ + 3 ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hk₀
  have : Finite (frobeniusFixedSubfield L p k) := finite_frobeniusFixedSubfield L p k hk
  have hcard : Nat.card (frobeniusFixedSubfield L p k) = p ^ k :=
    card_frobeniusFixedSubfield L p k hk
  have := isAlgClosure_frobeniusFixedSubfield (p := p) (L := L) k
  set E := frobeniusFixedSubfield L p k with hEdef
  have hpk : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left (Fact.out : p.Prime).two_le k
  have hbig : pairBound τ + 1 < Nat.card E := by
    rw [hcard]
    calc pairBound τ + 1 < 2 ^ (pairBound τ + 1) := Nat.lt_two_pow_self
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ p ^ k := hpk
  have hE3 : 3 ≤ Nat.card E := by
    rw [hcard]
    calc 3 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ p ^ k := hpk
  obtain ⟨t, ht⟩ := exists_unit_zpow_ne_one E (pairBound τ) hbig
  set Fr : L →+* L := iterateFrobenius L p k with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card E := fun c => by
    rw [hcard]
    rfl
  obtain ⟨-, -, -, hder⟩ := Lang_Frobenius_fixed_derived_of_perfect τ E
    (commutator_adjointGroup_eq_of_three_le τ E hE3) L Fr hFr
  set F : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom Fr) with hFdef
  set R := adjointGroup τ L ⊓ F.eqLocus (MonoidHom.id _) with hRdef
  set ι : ModGL τ E →* ModGL τ L := baseChangeGL (algebraMap E L) with hιdef
  have hFix : ∀ g : ModGL τ L, (∀ i j, natMat τ L (g : Module.End L (RootModule τ L)) i j ∈ E) →
      F g = g := by
    intro g hg
    refine Units.ext ?_
    change entrywise Fr (g : Module.End L (RootModule τ L)) = g
    refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [entrywise_single, Finsupp.mapRange_apply]
    have hx := hg (posEquiv τ a) (posEquiv τ b)
    rw [natMat_apply_posEquiv] at hx
    exact mem_frobeniusFixedSubfield.1 hx
  have hFh : F h = h := hFix h fun i j =>
    hS _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))
  have hFh' : F h⁻¹ = h⁻¹ := by rw [map_inv, hFh]
  have hRconj : ∀ g : ModGL τ L, g ∈ H → F g = g → ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
    intro g hg hFg r hr
    refine ⟨(Subgroup.mem_normalizer_iff.1
      (le_normalizer_adjointGroup H hCH hH hg) r).1 hr.1, ?_⟩
    have hr2 : F r = r := hr.2
    change F (g * r * g⁻¹) = g * r * g⁻¹
    rw [map_mul, map_mul, map_inv, hFg, hr2]
  have hRmap : R.map (MulAut.conj h : ModGL τ L →* ModGL τ L) = R := by
    refine le_antisymm ?_ fun r hr => ?_
    · rintro _ ⟨r, hr, rfl⟩
      exact hRconj h hh hFh r hr
    · refine ⟨h⁻¹ * r * h⁻¹⁻¹, hRconj h⁻¹ (H.inv_mem hh) hFh' r hr, ?_⟩
      change h * (h⁻¹ * r * h⁻¹⁻¹) * h⁻¹ = r
      group
  have hHE : ((adjointGroup τ E).map ι).map (MulAut.conj h : ModGL τ L →* ModGL τ L) =
      (adjointGroup τ E).map ι := by
    rw [← hder, Subgroup.map_commutator, hRmap]
  obtain ⟨α, hα⟩ := exists_mulAut_of_conj (algebraMap E L) h hHE
  rw [Subfield.algebraMap_ofSubfield] at hα
  exact ⟨k, by omega, ⟨t, ht⟩, α, hα⟩

end CFSG.TauCetiBridge.Even
