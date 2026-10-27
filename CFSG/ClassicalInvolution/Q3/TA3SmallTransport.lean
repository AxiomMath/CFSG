module

public import CFSG.ClassicalInvolution.Q3.TL3Induct

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')

theorem map_centralizer_singleton (t : Y) :
    (Subgroup.centralizer ({t} : Set Y)).map e.toMonoidHom =
      Subgroup.centralizer ({e t} : Set Y') := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg e h
    simpa using this
  · intro h
    apply e.injective
    simp [h]

theorem conjSub_map_equiv (g : Y) (H : Subgroup Y) :
    conjSub (e g) (H.map e.toMonoidHom) = (conjSub g H).map e.toMonoidHom := by
  ext x
  rw [mem_conjSub_iff, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, mem_conjSub_iff]
  simp [map_mul, map_inv]

theorem tightCore_map_equiv (R : Subgroup Y) :
    (tightCore R).map e.toMonoidHom = tightCore (R.map e.toMonoidHom) := by
  unfold tightCore
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨hxR, hx2⟩, rfl⟩
    refine ⟨⟨x, hxR, rfl⟩, ?_⟩
    rw [← MonoidHom.map_zpowers]
    exact hx2.map _
  · rintro ⟨hyR, hy2⟩
    refine ⟨e.symm y, ⟨Subgroup.mem_map_equiv.mp hyR, ?_⟩, by simp⟩
    have h : Subgroup.zpowers (e.symm y) = (Subgroup.zpowers y).map e.symm.toMonoidHom :=
      (MonoidHom.map_zpowers e.symm.toMonoidHom y).symm
    rw [h]
    exact hy2.map _

theorem oddCoreImg_map_equiv (R : Subgroup Y) :
    oddCoreImg (R.map e.toMonoidHom) = (oddCoreImg R).map e.toMonoidHom := by
  have h : (oddCore ↥R).map (R.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom =
      oddCore ↥(R.map e.toMonoidHom) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant _
  unfold oddCoreImg
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem mem_map_equiv_iff {H : Subgroup Y} {x : Y} : e x ∈ H.map e.toMonoidHom ↔ x ∈ H := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

variable [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_sylow_map_equiv (S : Sylow 2 R) :
    ∃ S' : Sylow 2 ↥(R.map e.toMonoidHom),
      Nonempty (↥(S : Subgroup R) ≃* ↥(S' : Subgroup ↥(R.map e.toMonoidHom))) ∧
      (S' : Subgroup ↥(R.map e.toMonoidHom)).map (R.map e.toMonoidHom).subtype =
        ((S : Subgroup R).map R.subtype).map e.toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eR := R.equivMapOfInjective e.toMonoidHom e.injective
  have hsurj : Function.Surjective eR.toMonoidHom := eR.surjective
  refine ⟨S.mapSurjective hsurj,
    ⟨(S : Subgroup R).equivMapOfInjective eR.toMonoidHom eR.injective⟩, ?_⟩
  show ((S : Subgroup R).map eR.toMonoidHom).map (R.map e.toMonoidHom).subtype = _
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite Y] in
theorem TightDatum.map_equiv (hd : TightDatum R S t) {S' : Sylow 2 ↥(R.map e.toMonoidHom)}
    (hSS : Nonempty (↥(S : Subgroup R) ≃* ↥(S' : Subgroup ↥(R.map e.toMonoidHom))))
    (hS₀ : (S' : Subgroup ↥(R.map e.toMonoidHom)).map (R.map e.toMonoidHom).subtype =
      ((S : Subgroup R).map R.subtype).map e.toMonoidHom) :
    TightDatum (R.map e.toMonoidHom) S' (e t) := by
  obtain ⟨eS⟩ := hSS
  have hcent : R.map e.toMonoidHom ≤ Subgroup.centralizer ({e t} : Set Y') := by
    rw [← map_centralizer_singleton e t]
    exact Subgroup.map_mono hd.cent
  refine ⟨?_, ?_, ?_, hcent, ?_, ?_⟩
  · obtain ⟨r, hr, ⟨eQ⟩⟩ := hd.quat
    exact ⟨r, hr, ⟨eS.symm.trans eQ⟩⟩
  · rw [hS₀]
    exact Subgroup.mem_map_of_mem _ hd.mem
  · rw [MulEquiv.orderOf_eq]
    exact hd.order
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hcent, ← map_centralizer_singleton e t,
      ← Subgroup.map_equiv_normalizer_eq R e]
    exact Subgroup.map_mono hd.le_normalizer
  · have hO := CFSG.ComponentClassification.OddCore.equiv_invariant
      (R.equivMapOfInjective e.toMonoidHom e.injective)
    exact hd.twoGroup.of_equiv
      (QuotientGroup.congr _ _ (R.equivMapOfInjective e.toMonoidHom e.injective) hO)

omit [Finite Y] in
theorem TightCls.map_equiv (hc : TightCls Y R S t) {S' : Sylow 2 ↥(R.map e.toMonoidHom)}
    (hSS : Nonempty (↥(S : Subgroup R) ≃* ↥(S' : Subgroup ↥(R.map e.toMonoidHom)))) :
    TightCls Y' (R.map e.toMonoidHom) S' (e t) := by
  obtain ⟨⟨eQ⟩, hgen, hO⟩ := hc
  obtain ⟨eS⟩ := hSS
  refine ⟨⟨eS.symm.trans eQ⟩, ?_, ?_⟩
  · have hgen' : (⨆ g : Y, conjSub g (tightCore R)) = ⊤ := hgen
    show (⨆ g : Y', conjSub g (tightCore (R.map e.toMonoidHom))) = ⊤
    rw [eq_top_iff, ← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective, ← hgen',
      Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [← conjSub_map_equiv e, tightCore_map_equiv e]
    exact le_iSup (fun g' : Y' => conjSub g' (tightCore (R.map e.toMonoidHom))) (e g)
  · have h : (classicalInvolutionOddCore Y).map e.toMonoidHom = classicalInvolutionOddCore Y' :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    have hO' : classicalInvolutionOddCore Y = ⊥ := hO
    show classicalInvolutionOddCore Y' = ⊥
    rw [← h, hO', Subgroup.map_bot]

omit [Finite Y] in
theorem TightInO2.of_map_equiv (h : TightInO2 (e t)) : TightInO2 t := by
  obtain ⟨P, hPn, hP2, htP⟩ := h
  exact ⟨P.comap e.toMonoidHom, hPn.comap _, hP2.comap_of_injective _ e.injective, htP⟩

end CFSG.ClassicalInvolution.Q3.TA3
