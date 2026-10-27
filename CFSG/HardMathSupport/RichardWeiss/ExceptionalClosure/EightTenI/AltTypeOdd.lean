module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.EightTenI.AltNaturalType
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem evenWeightOnes_eq_bot_of_odd {N : ℕ} (hN : Odd N) : evenWeightOnes N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨c, hc⟩ := CFSG.HardMathSupport.Cooperstein.Coordinator.exists_forall_eq_of_mem_evenWeightOnes hx
  have hsum : ∑ i : Fin N, ((x : Fin N → ZMod 2)) i = 0 := by
    have := x.2
    simpa [evenWeight] using this
  have hcN : (N : ZMod 2) * c = 0 := by
    simpa [hc] using hsum
  have hN1 : (N : ZMod 2) = 1 := (ZMod.natCast_eq_one_iff_odd).mpr hN
  rw [hN1, one_mul] at hcN
  subst hcN
  apply (AddSubgroup.mem_bot).mpr
  exact Subtype.ext (funext fun i => by simp [hc i])

theorem isAltType_of_isAltNaturalType_odd {L : Subgroup G} {N : ℕ} (hN : Odd N)
    (h : IsAltNaturalType L N) : IsAltType L N := by
  obtain ⟨α, hα, hαk, β, hβ, hβk, hβe⟩ := h
  have hbot := evenWeightOnes_eq_bot_of_odd hN
  have hbij : Function.Bijective (QuotientAddGroup.mk' (evenWeightOnes N)) := by
    refine ⟨?_, QuotientAddGroup.mk'_surjective _⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ evenWeightOnes N := (QuotientAddGroup.eq_zero_iff x).mp hx
    rw [hbot] at this
    exact (AddSubgroup.mem_bot).mp this
  let φ : evenWeight N ≃+ altHeart N := AddEquiv.ofBijective (QuotientAddGroup.mk' (evenWeightOnes N)) hbij
  let β' : blockU L →* Multiplicative (evenWeight N) :=
    (AddEquiv.toMultiplicative φ.symm).toMonoidHom.comp β
  refine ⟨α, hα, hαk, β', ?_, ?_, ?_⟩
  · intro x
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd (φ x))
    refine ⟨u, ?_⟩
    simp only [β', MonoidHom.comp_apply, hu]
    exact congrArg Multiplicative.ofAdd (φ.symm_apply_apply x)
  · rw [← hβk]
    ext u
    simp only [MonoidHom.mem_ker, β', MonoidHom.comp_apply]
    constructor
    · intro h1
      have := congrArg (fun z => φ (Multiplicative.toAdd z)) h1
      simpa using this
    · intro h1; rw [h1, map_one]
  · intro ℓ u v huv i
    set x : evenWeight N := φ.symm (Multiplicative.toAdd (β u)) with hxdef
    have hxu : (QuotientAddGroup.mk x : altHeart N) = Multiplicative.toAdd (β u) :=
      φ.apply_symm_apply (Multiplicative.toAdd (β u))
    have h2 := hβe ℓ u v huv x hxu.symm
    have hv' : Multiplicative.toAdd (β' v) = evenWeightPerm (α ℓ : Equiv.Perm (Fin N)) x := by
      show φ.symm (Multiplicative.toAdd (β v)) = _
      rw [AddEquiv.symm_apply_eq]
      exact h2
    have hu' : Multiplicative.toAdd (β' u) = x := rfl
    rw [hv', hu']
    rfl

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock blockV barM InClassXBlock)
open CFSG.Open (pCoreOf)
open CFSG.HardMathSupport.Cooperstein

variable [Finite G]

theorem inClassXBlock_of_natural_section_odd_of_center_bot
    {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) {N : ℕ} (hN : 7 ≤ N) (hodd : Odd N)
    (hZ : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥)
    (hsec : AlternatingGeometry.NaturalSectionLSL S L N)
    (hQV : ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L) (hshort : IsShort2 L) :
    InClassXBlock L := by
  refine ⟨hshort, Or.inr ?_⟩
  obtain ⟨n, hn⟩ := hodd
  subst hn
  exact ⟨n, by omega, isAltType_of_isAltNaturalType_odd ⟨n, rfl⟩
    (isAltNaturalType_of_natural_section_of_center_bot hX hA hL (by omega) hZ hsec hQV hshort)⟩

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

end
