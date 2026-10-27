module

public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.TwE6.TwTorus
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.BaseChangeModels
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.Interfaces

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
  CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors TensorProduct


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

include hf hK hσ in
theorem twChi27_hatH_a0 (u : (orbitField TwistTag.E6 K σ twA0)ˣ) :
    twChi27 σ (hatH hf hK σ hσ twA0 u) = ((u : orbitField TwistTag.E6 K σ twA0) : K) := by
  unfold twChi27
  rw [twRep27_apply]
  change minRep e6Data_valid K (minOrbitHom σ twA0 (HSL u)) e6Y27 ⟨0, by decide⟩ = _
  rw [minRep_Psi_HSL_a0]
  simp [e6Y27]

include hf hK hσ in
theorem twChi27_hatH_ne (a : Fin TwistTag.E6.foldedTag.rank) (ha : a ≠ twA0)
    (u : (orbitField TwistTag.E6 K σ a)ˣ) :
    twChi27 σ (hatH hf hK σ hσ a u) = 1 := by
  unfold twChi27
  rw [twRep27_apply]
  change minRep e6Data_valid K (minOrbitHom σ a (HSL u)) e6Y27 ⟨0, by decide⟩ = 1
  rw [minRep_Psi_HSL_fix σ a ha u]
  simp [e6Y27]


include hf hK hσ in
theorem tw27SurvivorBound_holds :
    CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.Tw27SurvivorBound hf K hK σ hσ := by
  classical
  intro k _ _ _ inst₀ m ρ y χ J hρ hnt ht h27 A hA hel
  obtain ⟨hJ, b, hb, hχ⟩ := h27
  let alg : Algebra K k := ((algebraMap K k).comp (frobEquiv K b).toRingHom).toAlgebra
  have key : ∀ u : K, algebraMap K k u = (@algebraMap K k _ _ inst₀ u) ^ (2 ^ b) := fun u => by
    show @algebraMap K k _ _ inst₀ (frobEquiv K b u) = _
    rw [frobEquiv_apply, map_pow]
  have hd : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (w : (orbitField TwistTag.E6 K σ a)ˣ),
      χ (hatH hf hK σ hσ a w) = algebraMap K k (twChi27 σ (hatH hf hK σ hσ a w)) := by
    intro a w
    by_cases ha : a = twA0
    · subst ha
      exact (hχ w).trans (by rw [twChi27_hatH_a0 hf hK σ hσ w, key])
    · have haJ : a ∈ J := by
        rw [hJ]
        exact Finset.mem_erase.2 ⟨ha, Finset.mem_univ _⟩
      have h1 : χ (hatH hf hK σ hσ a w) = 1 := ((ht.2.2.2 a).1 haJ).1 w
      rw [h1, twChi27_hatH_ne hf hK σ hσ a ha w, map_one]
  have hρ₂ := isSimpleRep_bc_twRep27 hf hK σ hσ (k := k)
  have ht₂ := twRep27_bc_isCoverType hf hK σ hσ (k := k)
  have hH := tw_chi_eq_on_H hf hK σ hσ hρ hρ₂ ht ht₂ hd
  have ht' := ht.congr_H hH
  rw [hJ] at ht'
  obtain ⟨β, hβ⟩ := twisted_iso_27_bc hf hK σ hσ hρ ht'
  have hd27 : Module.finrank K (Fin e6Data.d →₀ K) = 27 := by
    rw [Module.finrank_finsupp_self]
    rfl
  have hm : m = 27 := by
    have := β.finrank_eq
    rw [Module.finrank_baseChange, hd27, Module.finrank_fin_fun] at this
    exact this.symm
  subst hm
  have e1 : Representation.invariants (ρ.comp A.subtype) = fixSub ρ A := by
    ext v
    rw [Representation.mem_invariants]
    exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g.1 g.2⟩
  rw [e1]
  have h1 := finrank_fixSub_of_iso β hβ A
  have h2 := finrank_fixSub_bcRep_le (K := K) (k := k) (twRep27 σ) A
  set A' : Subgroup ↥(e6Data_valid.minGroup K) := A.map (TwistedE6.fixedGroup K σ).subtype
    with hA'
  have hinj : Function.Injective (TwistedE6.fixedGroup K σ).subtype := Subtype.val_injective
  have hne' : A' ≠ ⊥ := fun h => hA ((Subgroup.map_eq_bot_iff_of_injective A hinj).1 h)
  have hel' : ∀ a ∈ A', a ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hel x hx, map_one]
  have h3 := bound27_K A' hne' hel'
  have hc : Nat.card A' = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ hinj).toEquiv).symm
  have e2 : fixSub (twRep27 σ) A = fixSub (e6Rep27 K) A' := by
    ext v
    constructor
    · intro hv g' hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      exact hv g hg
    · intro hv g hg
      exact hv _ ⟨g, hg, rfl⟩
  rw [hc, ← e2] at h3
  have h4 : Nat.card K ^ Module.finrank k ↥(fixSub ρ A) ≤
      Nat.card K ^ Module.finrank K ↥(fixSub (twRep27 σ) A) :=
    Nat.pow_le_pow_right Nat.card_pos (h1.symm ▸ h2)
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ h4) h3

end CFSG.HardMathSupport.Meierfrankenfeld.Proving.TwE6
