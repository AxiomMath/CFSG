module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KSubTFacts
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def D4InnerDiagRes : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (J B : Subgroup H) (b : H),
    CFSG.Open.IsQuasisimple ↥J → catalogIs (PSimple 3 J) S9.isD4two → InnDiagOn 3 B J → b ∈ B →
      CFSG.Yardstones.Md0ec50421ce4.InducesInnerMod 3 J b

@[expose] def OmegaPlusCompRes : Prop :=
  ∀ (T : Type) [Group T], catalogIs T S9.isD4two → ∀ α : MulAut T, α ^ 3 = 1 → α ≠ 1 →
    (∃ s : T, α = MulAut.conj s) → ∀ L : Subgroup T, CFSG.Open.IsComponentOf L (fixSub α) →
      catalogIs (↥L ⧸ Subgroup.center ↥L) S9.isU4two

theorem piJ_eq_one_of_mem_core {H : Type} [Group H] {J : Subgroup H} {z : ↥J}
    (hz : (z : H) ∈ GLAPPrimeCoreOf 3 J) : piJ J z = 1 := by
  have hz2 : (z : H) ∈ (GLAPPrimeCore 3 ↥J).map J.subtype := hz
  have hz' : z ∈ GLAPPrimeCore 3 ↥J := by
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz2
    have hwe : w = z := Subtype.ext hwz
    rw [hwe] at hw
    exact hw
  have hx : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) z : ↥J ⧸ GLAPPrimeCore 3 ↥J) = 1 :=
    (QuotientGroup.eq_one_iff z).mpr hz'
  show (QuotientGroup.mk' (Subgroup.center (PQuot 3 J)))
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) z) = 1
  rw [hx, map_one]

theorem inner_of_inducesInnerMod {H : Type} [Group H] {J : Subgroup H} {d : H} {T : Type} [Group T]
    (e0 : PSimple 3 J ≃* T) (c : ↥J ≃* ↥J) (hc : ∀ x : ↥J, (c x : H) = d * x * d⁻¹)
    (hind : CFSG.Yardstones.Md0ec50421ce4.InducesInnerMod 3 J d)
    (α : MulAut T) (hrel : ∀ x : ↥J, e0 (piJ J (c x)) = α (e0 (piJ J x))) :
    ∃ s : T, α = MulAut.conj s := by
  obtain ⟨l, hl, hlinn⟩ := hind
  let l' : ↥J := ⟨l, hl⟩
  have key : ∀ x : ↥J, piJ J (c x) = piJ J l' * piJ J x * (piJ J l')⁻¹ := by
    intro x
    have hdx : d⁻¹ * (c x : H) * d = (x : H) := by
      rw [hc x]
      group
    have hmem := hlinn (c x) (c x).2
    rw [hdx] at hmem
    have hwmem : (((l'⁻¹ * c x * l')⁻¹ * x : ↥J) : H) ∈ GLAPPrimeCoreOf 3 J := hmem
    have hpw : piJ J ((l'⁻¹ * c x * l')⁻¹ * x) = 1 := piJ_eq_one_of_mem_core hwmem
    have h1 : piJ J (l'⁻¹ * c x * l') = piJ J x := by
      rw [map_mul, map_inv] at hpw
      exact inv_mul_eq_one.mp hpw
    calc piJ J (c x) = piJ J (l' * (l'⁻¹ * c x * l') * l'⁻¹) := by
          rw [show l' * (l'⁻¹ * c x * l') * l'⁻¹ = c x by group]
      _ = piJ J l' * piJ J (l'⁻¹ * c x * l') * (piJ J l')⁻¹ := by
          simp only [map_mul, map_inv]
      _ = piJ J l' * piJ J x * (piJ J l')⁻¹ := by rw [h1]
  have hsurj : Function.Surjective (fun x : ↥J => e0 (piJ J x)) :=
    e0.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  refine ⟨e0 (piJ J l'), MulEquiv.ext fun t => ?_⟩
  obtain ⟨x, rfl⟩ := hsurj t
  show α (e0 (piJ J x)) = MulAut.conj (e0 (piJ J l')) (e0 (piJ J x))
  rw [MulAut.conj_apply, ← hrel x, key x, map_mul, map_mul, map_inv]

theorem nontrivial_pSimple_isD4two {H : Type} [Group H] [Finite H] {J : Subgroup H}
    (hb : CatDistinct.OrderBridge) (h : catalogIs (PSimple 3 J) S9.isD4two) :
    Nontrivial (PSimple 3 J) := by
  have hc := CatDistinct.card_isD4two hb h
  exact Finite.one_lt_card_iff_nontrivial.1 (by rw [hc]; norm_num)

theorem d4_of_residuals (hb : CatDistinct.OrderBridge) (hI : D4InnerDiagRes) (hO : OmegaPlusCompRes) :
    KSubT.CompFact S9.isD4two S9.isU4two := by
  intro H _ _ J B d hJq hcat hdB hIn hd3 hdJ K hK
  have hdN : d ∈ Subgroup.normalizer (J : Set H) := hIn.1 hdB
  have hind := hI H J B d hJq hcat hIn hdB
  haveI : Nontrivial (PSimple 3 J) := nontrivial_pSimple_isD4two hb hcat
  obtain ⟨c, hc⟩ := exists_conj_equiv hdN
  obtain ⟨i, hi, ⟨e0⟩⟩ := hcat
  haveI : Nontrivial i.Group := e0.injective.nontrivial
  refine comp_fix hJq hdN hd3 hdJ e0 c hc ?_ K hK
  intro α hrel h3 h1 L hL
  obtain ⟨s, hs⟩ := inner_of_inducesInnerMod e0 c hc hind α hrel
  exact hO i.Group ⟨i, hi, ⟨MulEquiv.refl _⟩⟩ α h3 h1 ⟨s, hs⟩ L hL

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
