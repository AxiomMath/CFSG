module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Rep

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis

open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule

section Generic

variable {G : Type*} [Group G] {K k : Type*} [Field K] [Field k] (ι : K →+* k) {d : ℕ}

@[expose] def mapVec (v : Fin d →₀ K) : Fin d →₀ k := Finsupp.mapRange ι ι.map_zero v

theorem mapVec_add (v w : Fin d →₀ K) : mapVec ι (v + w) = mapVec ι v + mapVec ι w :=
  Finsupp.mapRange_add ι.map_add v w

theorem mapVec_smul (c : K) (v : Fin d →₀ K) : mapVec ι (c • v) = ι c • mapVec ι v := by
  ext a
  simp [mapVec]

theorem mapVec_single (a : Fin d) (c : K) :
    mapVec ι (Finsupp.single a c) = Finsupp.single a (ι c) := by
  simp [mapVec]

theorem mapVec_injective : Function.Injective (mapVec (d := d) ι) :=
  Finsupp.mapRange_injective _ ι.map_zero ι.injective

@[expose] def baseChangeLin (f : Module.End K (Fin d →₀ K)) : Module.End k (Fin d →₀ k) :=
  Finsupp.linearCombination k fun b => mapVec ι (f (Finsupp.single b 1))

theorem baseChangeLin_mapVec (f : Module.End K (Fin d →₀ K)) (v : Fin d →₀ K) :
    baseChangeLin ι f (mapVec ι v) = mapVec ι (f v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp [mapVec]
  | add v w hv hw => rw [mapVec_add, map_add, hv, hw, map_add, mapVec_add]
  | single a c =>
    rw [mapVec_single, baseChangeLin]
    have h1 : Finsupp.single a c = c • (Finsupp.single a 1 : Fin d →₀ K) := by simp
    have h2 : Finsupp.single a (ι c) = ι c • (Finsupp.single a 1 : Fin d →₀ k) := by simp
    rw [h2, map_smul, Finsupp.linearCombination_single, one_smul, h1, map_smul, mapVec_smul]

theorem baseChangeLin_single (f : Module.End K (Fin d →₀ K)) (b : Fin d) :
    baseChangeLin ι f (Finsupp.single b 1) = mapVec ι (f (Finsupp.single b 1)) := by
  have := baseChangeLin_mapVec ι f (Finsupp.single b 1)
  rwa [mapVec_single, map_one] at this

theorem baseChangeLin_mul (f g : Module.End K (Fin d →₀ K)) :
    baseChangeLin ι (f * g) = baseChangeLin ι f * baseChangeLin ι g := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply]
  rw [baseChangeLin_single, baseChangeLin_single, baseChangeLin_mapVec, Module.End.mul_apply]

theorem baseChangeLin_one : baseChangeLin ι (1 : Module.End K (Fin d →₀ K)) = 1 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.one_apply]
  rw [baseChangeLin_single, Module.End.one_apply, mapVec_single, map_one]

@[expose] def baseChangeRep (ρ : Representation K G (Fin d →₀ K)) :
    Representation k G (Fin d →₀ k) where
  toFun g := baseChangeLin ι (ρ g)
  map_one' := by rw [map_one, baseChangeLin_one]
  map_mul' g h := by rw [map_mul, baseChangeLin_mul]

theorem baseChangeRep_mapVec (ρ : Representation K G (Fin d →₀ K)) (g : G) (v : Fin d →₀ K) :
    baseChangeRep ι ρ g (mapVec ι v) = mapVec ι (ρ g v) :=
  baseChangeLin_mapVec ι (ρ g) v

end Generic

section E7

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Type} [Field k] [Finite k] [CharP k 2]
  (ι : K →+* k)

@[expose] def e7Rep56k : Representation k ↥(adjointGroup .E7 K) (Fin e7Data.d →₀ k) :=
  baseChangeRep ι (e7Rep56 K)

theorem e7Rep56k_mapVec (g : ↥(adjointGroup .E7 K)) (v : Fin e7Data.d →₀ K) :
    e7Rep56k ι g (mapVec ι v) = mapVec ι (e7Rep56 K g v) :=
  baseChangeRep_mapVec ι (e7Rep56 K) g v

@[expose] def e7Chi56k (g : ↥(adjointGroup .E7 K)) : k := ι (e7Chi56 g)

theorem e7Chi56k_dC (s : Fin (Tag.rank .E7)) (u : Kˣ) :
    e7Chi56k ι (dC .E7 K s u) = ι ((u ^ (if s = e7n6 then (1 : ℤ) else 0) : Kˣ) : K) := by
  rw [e7Chi56k, e7Chi56_dC]

theorem e7Rep56k_isChevType :
    IsChevType .E7 K 2 exists_weyl_neg_E7 (e7Rep56k ι) (mapVec ι e7Y56) (e7Chi56k ι)
      (Finset.univ.erase e7n6) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hfix, hne, hH, hJ⟩ := e7Rep56_isChevType (K := K)
  have := Fintype.ofFinite K
  refine ⟨?_, ?_, ?_, fun i => ?_⟩
  · refine (CurtisDatum.mem_fixU _ _).2 fun u hu => ?_
    rw [e7Rep56k_mapVec, (CurtisDatum.mem_fixU _ _).1 hfix u hu]
  · intro h
    exact hne (mapVec_injective ι (by rw [h]; simp [mapVec]))
  · intro h hh
    rw [e7Rep56k_mapVec, hH h hh, mapVec_smul]
    rfl
  · have hT : (chevDatum .E7 K 2 exists_weyl_neg_E7).heckeT (e7Rep56k ι) i (mapVec ι e7Y56) =
        mapVec ι ((chevDatum .E7 K 2 exists_weyl_neg_E7).heckeT (e7Rep56 K) i e7Y56) := by
      rw [heckeT_chevDatum, heckeT_chevDatum, e7Rep56k]
      let f : (Fin e7Data.d →₀ K) →+ (Fin e7Data.d →₀ k) := Finsupp.mapRange.addMonoidHom ι
      have hf : ∀ v, f v = mapVec ι v := fun v => rfl
      rw [show mapVec ι (∑ c : K, e7Rep56 K (xC .E7 K i c * nC .E7 K i) e7Y56) =
          f (∑ c : K, e7Rep56 K (xC .E7 K i c * nC .E7 K i) e7Y56) from rfl, map_sum]
      exact Finset.sum_congr rfl fun c _ => baseChangeRep_mapVec ι (e7Rep56 K) _ _
    rw [hT]
    simp only [e7Chi56k]
    have hi := hJ i
    constructor
    · intro hiJ
      obtain ⟨h1, h2⟩ := hi.1 hiJ
      refine ⟨fun t => ?_, ?_⟩
      · rw [h1 t, map_one]
      · rw [h2]; simp [mapVec]
    · rintro ⟨h1, h2⟩
      refine hi.2 ⟨fun t => ι.injective (by rw [h1 t, map_one]), ?_⟩
      exact mapVec_injective ι (by rw [h2]; simp [mapVec])

theorem e7Rep56_xC_one_single (i : Fin (Tag.rank .E7)) (b : Fin e7Data.d) :
    e7Rep56 K (xC .E7 K i 1) (Finsupp.single b 1) =
      Finsupp.single b 1 + (if e7Data.wt b i = -1 then Finsupp.single (e7Data_valid.sRefl i b) 1
        else 0) := by
  rw [e7Rep56, pullRep_apply, e7Psi_xC, minRep_xm]
  simp only [LinearMap.add_apply, Module.End.one_apply, one_smul]
  rw [e7Data_valid.rootOp_single_apply]

theorem e7Rep56k_xC_one (i : Fin (Tag.rank .E7)) :
    e7Rep56k ι (xC .E7 K i 1) = 1 + e7Data.rootOp k (Pi.single i 1) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.add_apply, Module.End.one_apply]
  rw [e7Data_valid.rootOp_single_apply]
  have h := e7Rep56k_mapVec ι (xC .E7 K i 1) (Finsupp.single b 1)
  rw [mapVec_single, map_one, e7Rep56_xC_one_single] at h
  rw [h, mapVec_add, mapVec_single, map_one]
  split_ifs
  · rw [mapVec_single, map_one]
  · simp [mapVec]

set_option maxRecDepth 20000 in
theorem e7Rep56k_fixU_le_line :
    ∀ x ∈ (e7Datum (K := K)).fixU (e7Rep56k ι), ∃ c : k, x = c • Finsupp.single (⟨0, by decide⟩ :
      Fin e7Data.d) 1 := by
  intro x hx
  have hx' := ((CurtisDatum.mem_fixU _ _).1 hx)
  refine ⟨x ⟨0, by decide⟩, ?_⟩
  refine eq_smul_of_rootOp_eq_zero (hV := e7Data_valid) e7_dominant fun i => ?_
  have hmem : xC .E7 K i 1 ∈ (e7Datum (K := K)).U :=
    (e7Datum (K := K)).X_le i (xC_mem_X (hw := exists_weyl_neg_E7) i 1)
  have h := hx' _ hmem
  rw [e7Rep56k_xC_one] at h
  simp only [LinearMap.add_apply, Module.End.one_apply] at h
  exact add_eq_left.1 h

theorem e7Rep56_orbitSpan_top :
    orbitSpan (e7Rep56 K) (e7Y56 : Fin e7Data.d →₀ K) = ⊤ :=
  (orbitSpan_pullRep e7Data_valid (e7Psi K) (e7Equiv (K := K)).symm.surjective _).trans
    (orbitSpan_minRep (hV := e7Data_valid) e7_reach)

theorem e7Rep56k_orbitSpan_top :
    orbitSpan (e7Rep56k ι) (mapVec ι (e7Y56 : Fin e7Data.d →₀ K)) = ⊤ := by
  set S := orbitSpan (e7Rep56k ι) (mapVec ι (e7Y56 : Fin e7Data.d →₀ K)) with hS
  have key : ∀ v ∈ orbitSpan (e7Rep56 K) (e7Y56 : Fin e7Data.d →₀ K), mapVec ι v ∈ S := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g, rfl⟩ := hv
      rw [← e7Rep56k_mapVec]
      exact Submodule.subset_span ⟨g, rfl⟩
    | zero => simp [mapVec]
    | add v w _ _ hv hw => rw [mapVec_add]; exact S.add_mem hv hw
    | smul c v _ hv => rw [mapVec_smul]; exact S.smul_mem _ hv
  refine (Submodule.eq_top_iff').2 fun v => ?_
  induction v using Finsupp.induction_linear with
  | zero => exact zero_mem _
  | add f g hf hg => exact add_mem hf hg
  | single a c =>
    have h1 : mapVec ι (Finsupp.single a 1) ∈ S :=
      key _ (by rw [e7Rep56_orbitSpan_top]; trivial)
    rw [mapVec_single, map_one] at h1
    have := S.smul_mem c h1
    rwa [Finsupp.smul_single, smul_eq_mul, mul_one] at this

theorem isSimpleRep_e7Rep56k : IsSimpleRep (e7Rep56k ι) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial (Fin e7Data.d →₀ k) := ⟨⟨Finsupp.single ⟨0, by decide⟩ 1, 0, fun h => by
    have := congrArg (fun v : Fin e7Data.d →₀ k => v ⟨0, by decide⟩) h
    simp at this⟩⟩
  exact (e7Datum (K := K)).isSimpleRep_of_fixU (p := 2) (e7Rep56k ι)
    (y := Finsupp.single ⟨0, by decide⟩ 1) (e7Rep56k_fixU_le_line ι)
    (by
      have h := e7Rep56k_orbitSpan_top ι
      simpa [e7Y56, mapVec_single] using h)

end E7

end CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis
