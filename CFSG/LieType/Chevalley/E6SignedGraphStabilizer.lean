module

public import CFSG.LieType.Chevalley.E6SignedGraphWeyl
public import CFSG.Monster.B.Geometry.F4Weyl

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SignedGraph

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.Monster.B.Geometry

@[expose] def F4Parity
    (u : WeylGroup .F4) : Prop :=
  Odd ((u • (Pi.single ⟨3, by decide⟩ 1 : Fin Tag.F4.rank → ℤ)) ⟨3, by decide⟩) ∧
    Even ((u • (Pi.single ⟨2, by decide⟩ 1 : Fin Tag.F4.rank → ℤ)) ⟨3, by decide⟩)

theorem card_f4_parity_check : ((Finset.univ : Finset (Fin 1152)).filter fun k : Fin 1152 =>
    Odd ((Tag.F4.rootCertificate.root (f4Digit (f4Code (k : ℕ)) 3)) ⟨3, by decide⟩) ∧
      Even ((Tag.F4.rootCertificate.root (f4Digit (f4Code (k : ℕ)) 2)) ⟨3, by decide⟩)).card =
    384 := by
  decide +kernel

theorem card_f4_parity
    : Nat.card {u : WeylGroup .F4 // F4Parity u} = 384 := by
  have e1 : {k : Fin 1152 // F4Parity (f4Elem k)} ≃ {u : WeylGroup .F4 // F4Parity u} :=
    (Equiv.ofBijective _ f4Elem_bijective).subtypeEquiv fun _ => Iff.rfl
  have e2 : {k : Fin 1152 // F4Parity (f4Elem k)} ≃ {k : Fin 1152 //
      Odd ((Tag.F4.rootCertificate.root (f4Digit (f4Code k) 3)) ⟨3, by decide⟩) ∧
        Even ((Tag.F4.rootCertificate.root (f4Digit (f4Code k) 2)) ⟨3, by decide⟩)} :=
    Equiv.subtypeEquivRight fun k => by
      rw [F4Parity, ((f4Realizes_elem k.2) ⟨3, by decide⟩).2,
        ((f4Realizes_elem k.2) ⟨2, by decide⟩).2]
  rw [← Nat.card_congr e1, Nat.card_congr e2, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_f4_parity_check

theorem single_one_eq_foldMap :
    (Pi.single ⟨1, by decide⟩ 1 : E6Vec) = TwistTag.E6.foldMap (Pi.single ⟨3, by decide⟩ 1) := by
  rw [TwistTag.foldMap_single]
  decide +kernel

theorem single_three_eq_foldMap :
    (Pi.single ⟨3, by decide⟩ 1 : E6Vec) = TwistTag.E6.foldMap (Pi.single ⟨2, by decide⟩ 1) := by
  rw [TwistTag.foldMap_single]
  decide +kernel

theorem mem_parityGroup_iff_foldedWeylEquiv
    (w : relWeylTwist TwistTag.E6) :
    (w : WeylGroup TwistTag.E6.tag) ∈ parityGroup ↔ F4Parity (foldedWeylEquiv TwistTag.E6 w) := by
  rw [mem_parityGroup_iff, single_one_eq_foldMap, single_three_eq_foldMap,
    smul_foldMap_foldedWeylEquiv, smul_foldMap_foldedWeylEquiv, TwistTag.foldMap_apply_apply,
    TwistTag.foldMap_apply_apply]
  exact ⟨fun h => h.2, fun h => ⟨w.2, h⟩⟩

theorem card_weylGroup :
    Nat.card weylGroup = 384 := by
  rw [weylGroup_eq_parityGroup, ← card_f4_parity]
  refine Nat.card_congr ?_
  have e : parityGroup ≃ {w : relWeylTwist TwistTag.E6 // (w : WeylGroup TwistTag.E6.tag) ∈
      parityGroup} :=
    { toFun := fun w => ⟨⟨w, w.2.1⟩, w.2⟩
      invFun := fun w => ⟨w.1, w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.trans ((foldedWeylEquiv TwistTag.E6).toEquiv.subtypeEquiv
    mem_parityGroup_iff_foldedWeylEquiv)

end CFSG.LieType.Chevalley.E6SignedGraph

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint E6SignedGraph
open scoped Pointwise

theorem E6_signed_graph_root_system_and_Weyl_stabilizer :
    Set.InjOn orbitVec orbits ∧ vecs.ncard = 32 ∧ posVecs.ncard = 16 ∧
    (∀ v ∈ vecs, ∃! c : Fin 4 → ℤ, v = ∑ i, c i • simpleVec i) ∧
    (∀ v ∈ vecs, ∀ c : Fin 4 → ℤ, v = ∑ i, c i • simpleVec i →
      (0 < height v ∧ ∀ i, 0 ≤ c i) ∨ (height v < 0 ∧ ∀ i, c i ≤ 0)) ∧
    (∀ i j, (2 * iform (simpleVec i) (simpleVec j) : ℚ) / iform (simpleVec i) (simpleVec i) =
      !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -2; 0, 0, -1, 2] i j) ∧
    (∀ i, simpleOrbit i ∈ orbits ∧ orbitVec (simpleOrbit i) = simpleVec i ∧
      ∀ O ∈ orbits, orbitVec O = simpleVec i → O = simpleOrbit i) ∧
    (weylGroup : Set (WeylGroup TwistTag.E6.tag)) =
      {w | w ∈ relWeylTwist TwistTag.E6 ∧
        Odd ((w⁻¹ • (Pi.single ⟨1, by decide⟩ 1 : Fin TwistTag.E6.tag.rank → ℤ)) ⟨1, by decide⟩) ∧
        Even ((w⁻¹ • (Pi.single ⟨3, by decide⟩ 1 : Fin TwistTag.E6.tag.rank → ℤ))
          ⟨1, by decide⟩)} ∧
    Nat.card weylGroup = 384 ∧
    (∀ i, Set.BijOn (gen i • ·) (posVecs \ {simpleVec i}) (posVecs \ {simpleVec i}) ∧
      gen i • simpleVec i = -simpleVec i) ∧
    (∀ w ∈ weylGroup, ∀ v ∈ vecs, w • v ∈ vecs) ∧
    (∀ w ∈ weylGroup, (∀ v ∈ vecs, w • v = v) → w = 1) ∧
    {v | ∃ w ∈ weylGroup, w • simpleVec 0 = v} = {v | v ∈ vecs ∧ iform v v = 4} ∧
    {v | ∃ w ∈ weylGroup, w • simpleVec 3 = v} = {v | v ∈ vecs ∧ iform v v = 8} ∧
    {v | v ∈ vecs ∧ iform v v = 4}.ncard = 24 ∧ {v | v ∈ vecs ∧ iform v v = 8}.ncard = 8 ∧
    vecs = {v | v ∈ vecs ∧ iform v v = 4} ∪ {v | v ∈ vecs ∧ iform v v = 8} ∧
    (∀ w ∈ weylGroup, wordLength w = {v | v ∈ posVecs ∧ w • v ∈ -posVecs}.ncard) ∧
    (∀ w ∈ weylGroup, ∀ i,
      (wordLength (w * gen i) = wordLength w - 1 ↔ height (w • simpleVec i) < 0) ∧
      (wordLength (gen i * w) = wordLength w - 1 ↔ height (w⁻¹ • simpleVec i) < 0)) ∧
    (∃! w, w ∈ weylGroup ∧ wordLength w = 16) ∧
    ∀ w ∈ weylGroup, wordLength w = 16 → ∀ v ∈ vecs, w • v = -v := by
  refine ⟨injOn_orbitVec, ncard_vecs, ncard_posVecs, fun v hv => ?_, fun v hv c hc => ?_,
    cartan_simpleVec, fun i => ?_, ?_, card_weylGroup,
    fun i => ⟨bijOn_gen i, gen_smul_simpleVec i⟩,
    fun w hw v hv => smul_mem_vecs (weylGroup_le_parityGroup hw) hv, fun w hw h => ?_,
    orbit_eq (by decide +kernel) fun v hv hm => (orbit_check v hv).1 hm,
    orbit_eq (by decide +kernel) fun v hv hm => (orbit_check v hv).2 hm,
    ncard_norm.trans (by decide +kernel), ncard_norm.trans (by decide +kernel), ?_,
    fun w hw => wordLength_eq_ncard hw,
    fun w hw i => ⟨wordLength_mul_gen hw i, wordLength_gen_mul hw i⟩,
    ⟨_, ⟨longest_mem, wordLength_longest⟩, fun w hw => eq_longest hw.1 hw.2⟩,
    fun w hw h v hv => by rw [eq_longest hw h]; exact longest_smul hv⟩
  ·
    obtain ⟨e, -⟩ := coeffs_spec hv
    exact ⟨coeffs v, e, fun c hc => simpleVec_sum_injective (hc.symm.trans e)⟩
  ·
    obtain ⟨e, hsign⟩ := coeffs_spec hv
    rwa [simpleVec_sum_injective (hc.symm.trans e)]
  ·
    obtain ⟨h1, h2⟩ := simpleOrbit_spec i
    exact ⟨h1, h2, fun O hO h => injOn_orbitVec hO h1 (h.trans h2.symm)⟩
  ·
    ext w
    rw [SetLike.mem_coe, weylGroup_eq_parityGroup, ← inv_mem_iff, mem_parityGroup_iff,
      Set.mem_ofPred_eq, inv_mem_iff]
  ·
    refine eq_one_of_forall_pos (weylGroup_le_parityGroup hw) fun v hv => ?_
    rw [h v hv.1]
    exact hv
  ·
    ext v
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro hv
      rcases norm_check v (mem_vecs_iff.1 hv) with h | h
      · exact Or.inl ⟨hv, h⟩
      · exact Or.inr ⟨hv, h⟩
    · rintro (⟨hv, -⟩ | ⟨hv, -⟩) <;> exact hv

end CFSG.LieType.Chevalley
