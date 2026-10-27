module

public import CFSG.Foundations.HigherElementaryThompson

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

theorem pRank_congr_transport {S S' : Type*} [Group S] [Group S'] (e : S ≃* S') (p : ℕ)
    [Fact p.Prime] : CFSG.pRank p S = CFSG.pRank p S' := by
  unfold CFSG.pRank
  congr 1
  ext r
  constructor
  · rintro ⟨A, hA, hcard⟩
    have := hA
    refine ⟨A.map e.toMonoidHom, IsElementaryAbelian.map e.toMonoidHom, ?_⟩
    rw [Subgroup.card_map_of_injective e.injective, hcard]
  · rintro ⟨A, hA, hcard⟩
    have := hA
    refine ⟨A.map e.symm.toMonoidHom, IsElementaryAbelian.map e.symm.toMonoidHom, ?_⟩
    rw [Subgroup.card_map_of_injective e.symm.injective, hcard]

theorem mem_family_map_transport {S S' : Type*} [Group S] [Group S'] (e : S ≃* S') (j : ℕ)
    {A : Subgroup S} (hA : A ∈ CFSG.higherElemThompsonFamily S j) :
    A.map e.toMonoidHom ∈ CFSG.higherElemThompsonFamily S' j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change IsElementaryAbelian 2 A ∧ CFSG.pRank 2 A = CFSG.pRank 2 S - j at hA
  obtain ⟨hA1, hA2⟩ := hA
  have := hA1
  change IsElementaryAbelian 2 (A.map e.toMonoidHom) ∧
    CFSG.pRank 2 (A.map e.toMonoidHom) = CFSG.pRank 2 S' - j
  have hmap : CFSG.pRank 2 (A.map e.toMonoidHom) = CFSG.pRank 2 A :=
    (pRank_congr_transport (MulEquiv.subgroupMap e A) 2).symm
  refine ⟨IsElementaryAbelian.map e.toMonoidHom, ?_⟩
  rw [hmap, hA2, pRank_congr_transport e 2]

theorem map_higherElemThompsonFamily_transport {S S' : Type*} [Group S] [Group S'] (e : S ≃* S')
    (j : ℕ) :
    (Subgroup.map e.toMonoidHom) '' CFSG.higherElemThompsonFamily S j =
      CFSG.higherElemThompsonFamily S' j := by
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact mem_family_map_transport e j hA
  · intro hB
    refine ⟨B.map e.symm.toMonoidHom, mem_family_map_transport e.symm j hB, ?_⟩
    rw [Subgroup.map_map]
    have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id S' := by
      ext x
      simp
    rw [hid, Subgroup.map_id]

theorem map_higherElemThompson_equiv {S S' : Type*} [Group S] [Group S'] [Finite S] [Finite S']
    (e : S ≃* S') (j : ℕ) :
    (CFSG.higherElemThompson S j).map e.toMonoidHom = CFSG.higherElemThompson S' j := by
  unfold CFSG.higherElemThompson
  rw [(Subgroup.gc_map_comap e.toMonoidHom).l_sSup, ← map_higherElemThompsonFamily_transport e j,
    sSup_image]

theorem mem_omegaOneCenter_iff_transport {S : Type*} [Group S] (J : Subgroup S) (z : S) :
    z ∈ CFSG.omegaOneCenter J ↔ z ∈ J ∧ z ^ 2 = 1 ∧ ∀ y ∈ J, y * z = z * y := by
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, h2⟩
    refine ⟨a.2, h2, fun y hy => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha ⟨y, hy⟩)
  · rintro ⟨hz, h2, hc⟩
    refine ⟨⟨⟨z, hz⟩, Subgroup.mem_center_iff.mpr (fun g => Subtype.ext (hc g.1 g.2)), rfl⟩, h2⟩

theorem map_omegaOneCenter_equiv_transport {S S' : Type*} [Group S] [Group S'] (e : S ≃* S')
    (J : Subgroup S) :
    (CFSG.omegaOneCenter J).map e.toMonoidHom =
      CFSG.omegaOneCenter (J.map e.toMonoidHom) := by
  ext z'
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hzJ, h2, hc⟩ := (mem_omegaOneCenter_iff_transport J z).mp hz
    rw [mem_omegaOneCenter_iff_transport]
    refine ⟨Subgroup.mem_map_of_mem _ hzJ, ?_, ?_⟩
    · rw [← map_pow, h2, map_one]
    · rintro y' hy'
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hy'
      rw [← map_mul, ← map_mul, hc y hy]
  · intro hz'
    obtain ⟨hz'J, h2, hc⟩ := (mem_omegaOneCenter_iff_transport (J.map e.toMonoidHom) z').mp hz'
    obtain ⟨z, hzJ, rfl⟩ := Subgroup.mem_map.mp hz'J
    refine ⟨z, ?_, rfl⟩
    rw [mem_omegaOneCenter_iff_transport]
    refine ⟨hzJ, ?_, ?_⟩
    · apply e.injective
      rw [map_pow, map_one]
      exact h2
    · intro y hy
      apply e.injective
      rw [map_mul, map_mul]
      exact hc _ (Subgroup.mem_map_of_mem _ hy)

theorem map_omegaOneCenter_top_equiv {S S' : Type*} [Group S] [Group S'] (e : S ≃* S') :
    (CFSG.omegaOneCenter (⊤ : Subgroup S)).map e.toMonoidHom =
      CFSG.omegaOneCenter (⊤ : Subgroup S') := by
  rw [map_omegaOneCenter_equiv_transport, Subgroup.map_top_of_surjective _ e.surjective]

theorem map_higherElemThompsonOmega_equiv {S S' : Type*} [Group S] [Group S'] [Finite S]
    [Finite S'] (e : S ≃* S') (j : ℕ) :
    (CFSG.higherElemThompsonOmega S j).map e.toMonoidHom =
      CFSG.higherElemThompsonOmega S' j := by
  unfold CFSG.higherElemThompsonOmega
  rw [map_omegaOneCenter_equiv_transport, map_higherElemThompson_equiv]

theorem subgroupOf_comp_transport {G : Type*} [Group G] {T X : Subgroup G} (hTX : T ≤ X) :
    X.subtype.comp (T.subgroupOf X).subtype =
      T.subtype.comp (Subgroup.subgroupOfEquivOfLe hTX).toMonoidHom := by
  ext x
  rfl

theorem map_omegaOneCenter_top_subgroupOf {G : Type*} [Group G] [Finite G] {T X : Subgroup G}
    (hTX : T ≤ X) :
    ((CFSG.omegaOneCenter (⊤ : Subgroup ↥(T.subgroupOf X))).map (T.subgroupOf X).subtype).map
      X.subtype = (CFSG.omegaOneCenter (⊤ : Subgroup ↥T)).map T.subtype := by
  rw [Subgroup.map_map, subgroupOf_comp_transport hTX, ← Subgroup.map_map,
    map_omegaOneCenter_top_equiv]

theorem map_higherElemThompson_subgroupOf {G : Type*} [Group G] [Finite G] {T X : Subgroup G}
    (hTX : T ≤ X) (j : ℕ) :
    ((CFSG.higherElemThompson ↥(T.subgroupOf X) j).map (T.subgroupOf X).subtype).map X.subtype =
      (CFSG.higherElemThompson ↥T j).map T.subtype := by
  rw [Subgroup.map_map, subgroupOf_comp_transport hTX, ← Subgroup.map_map,
    map_higherElemThompson_equiv]

theorem map_higherElemThompsonOmega_subgroupOf {G : Type*} [Group G] [Finite G]
    {T X : Subgroup G} (hTX : T ≤ X) (j : ℕ) :
    ((CFSG.higherElemThompsonOmega ↥(T.subgroupOf X) j).map (T.subgroupOf X).subtype).map
      X.subtype = (CFSG.higherElemThompsonOmega ↥T j).map T.subtype := by
  rw [Subgroup.map_map, subgroupOf_comp_transport hTX, ← Subgroup.map_map,
    map_higherElemThompsonOmega_equiv]

def conjRes_transport {G : Type*} [Group G] (T : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) : T ≃* T where
  toFun t := ⟨g * t * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg t.1).mp t.2⟩
  invFun t := ⟨g⁻¹ * t * g⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp (inv_mem hg) t.1).mp t.2⟩
  left_inv t := Subtype.ext (by simp [mul_assoc])
  right_inv t := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem normalizer_le_of_map_fixed_transport {G : Type*} [Group G] (T : Subgroup G) (W : Subgroup T)
    (hW : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (T : Set G)),
      W.map (conjRes_transport T hg).toMonoidHom = W) :
    Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer ((W.map T.subtype : Subgroup G) : Set G) := by
  have fwd : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (T : Set G)),
      ∀ x ∈ W.map T.subtype, g * x * g⁻¹ ∈ W.map T.subtype := by
    intro g hg x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    have hmem : conjRes_transport T hg w ∈ W.map (conjRes_transport T hg).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hw
    rw [hW g hg] at hmem
    exact Subgroup.mem_map.mpr ⟨conjRes_transport T hg w, hmem, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fwd g hg h
  · intro hh
    have := fwd g⁻¹ (inv_mem hg) _ hh
    simpa [mul_assoc] using this

theorem normalizer_le_normalizer_omegaOneCenter_top {G : Type*} [Group G] (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer
      (((CFSG.omegaOneCenter (⊤ : Subgroup ↥T)).map T.subtype : Subgroup G) : Set G) :=
  normalizer_le_of_map_fixed_transport T _ (fun _ hg =>
    map_omegaOneCenter_top_equiv (conjRes_transport T hg))

theorem normalizer_le_normalizer_higherElemThompson {G : Type*} [Group G] [Finite G]
    (T : Subgroup G) (j : ℕ) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer
      (((CFSG.higherElemThompson ↥T j).map T.subtype : Subgroup G) : Set G) :=
  normalizer_le_of_map_fixed_transport T _ (fun _ hg =>
    map_higherElemThompson_equiv (conjRes_transport T hg) j)

theorem normalizer_le_normalizer_higherElemThompsonOmega {G : Type*} [Group G] [Finite G]
    (T : Subgroup G) (j : ℕ) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer
      (((CFSG.higherElemThompsonOmega ↥T j).map T.subtype : Subgroup G) : Set G) :=
  normalizer_le_of_map_fixed_transport T _ (fun _ hg =>
    map_higherElemThompsonOmega_equiv (conjRes_transport T hg) j)

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
