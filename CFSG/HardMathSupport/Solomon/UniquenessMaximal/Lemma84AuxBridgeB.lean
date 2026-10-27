module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma84AuxQuot

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mulEquiv_quot_preimQ (X : Subgroup G) (T : Subgroup (Qt ↥X))
    [hn : ((GLAPPrimeCoreOf 2 X).subgroupOf ((preimQ T).map X.subtype)).Normal] :
    Nonempty (↥((preimQ T).map X.subtype) ⧸
      (GLAPPrimeCoreOf 2 X).subgroupOf ((preimQ T).map X.subtype) ≃* ↥T) := by
  set L := (preimQ T).map X.subtype with hL
  let e : ↥(preimQ T) ≃* ↥L := Subgroup.equivMapOfInjective _ X.subtype X.subtype_injective
  let f0 : ↥(preimQ T) →* ↥T :=
    ((mkQ ↥X).comp (preimQ T).subtype).codRestrict T (fun y => y.2)
  have hf0 : ∀ y, ((f0 y : ↥T) : Qt ↥X) = mkQ ↥X y.1 := fun _ => rfl
  let f : ↥L →* ↥T := f0.comp e.symm.toMonoidHom
  have hfe : ∀ z, f (e z) = f0 z := fun z => by simp [f]
  have hf : Function.Surjective f := by
    intro t
    obtain ⟨y, hy, hyt⟩ : ∃ y ∈ preimQ T, mkQ ↥X y = t.1 := by
      have : t.1 ∈ (preimQ T).map (mkQ ↥X) := by rw [map_mkQ_preimQ]; exact t.2
      exact this.imp fun y hy => ⟨hy.1, hy.2⟩
    refine ⟨e ⟨y, hy⟩, ?_⟩
    rw [hfe]
    exact Subtype.ext (by rw [hf0]; exact hyt)
  have hker : f.ker = (GLAPPrimeCoreOf 2 X).subgroupOf L := by
    ext ℓ
    obtain ⟨y, rfl⟩ := e.surjective ℓ
    rw [MonoidHom.mem_ker, hfe, Subgroup.mem_subgroupOf, Subtype.ext_iff, hf0]
    change mkQ ↥X y.1 = 1 ↔ y.1.1 ∈ GLAPPrimeCoreOf 2 X
    rw [show mkQ ↥X y.1 = QuotientGroup.mk y.1 from rfl, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨y.1, h, rfl⟩
    · rintro ⟨n, hn, hne⟩
      have : n = y.1 := X.subtype_injective hne
      rwa [← this]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

omit [Finite G] in
theorem normal_subgroupOf_glaPPrimeCoreOf (X : Subgroup G) {L : Subgroup G} (hLX : L ≤ X) :
    ((GLAPPrimeCoreOf 2 X).subgroupOf L).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 2 X (hLX g.2)) n.1).1 hn
  simpa using this

omit [Finite G] in
theorem isCatalogGroup_of_component {X : Subgroup G} (hG : IsKProper G) (hX : X ≠ ⊤)
    {K : Subgroup (Qt ↥X)} (hK : IsSimpleGroup ↥K) (hKn : ∃ a b : ↥K, a * b ≠ b * a) :
    IsCatalogGroup ↥K := by
  set T := (preimQ K).map X.subtype with hT
  have hTX : T ≤ X := by rintro _ ⟨n, -, rfl⟩; exact n.2
  have hOT : GLAPPrimeCoreOf 2 X ≤ T := by
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨n, ker_le_preimQ K hn, rfl⟩
  have hTtop : T ≠ ⊤ := fun h => hX (top_le_iff.1 (h ▸ hTX))
  have hn : ((GLAPPrimeCoreOf 2 X).subgroupOf T).Normal :=
    normal_subgroupOf_glaPPrimeCoreOf X hTX
  obtain ⟨e⟩ := exists_mulEquiv_quot_preimQ X K
  have := hK
  have hs : IsSimpleGroup (↥T ⧸ (GLAPPrimeCoreOf 2 X).subgroupOf T) := e.isSimpleGroup
  have hna : ∃ a b : ↥T ⧸ (GLAPPrimeCoreOf 2 X).subgroupOf T, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKn
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  obtain ⟨i, ⟨φ⟩⟩ := hG T (GLAPPrimeCoreOf 2 X) hTtop hOT hs hna
  exact ⟨i, ⟨e.symm.trans φ⟩⟩

omit [Finite G] in
theorem normal_subgroupOf_map_subtype {X : Subgroup G} {A B : Subgroup ↥X} (hAB : A ≤ B)
    (h : (A.subgroupOf B).Normal) :
    ((A.map X.subtype).subgroupOf (B.map X.subtype)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨a, ha, hae⟩ := hn
  obtain ⟨b, hb, hbe⟩ := g.2
  have key := h.conj_mem ⟨a, hAB ha⟩ (by simpa [Subgroup.mem_subgroupOf] using ha) ⟨b, hb⟩
  rw [Subgroup.mem_subgroupOf] at key
  refine ⟨_, key, ?_⟩
  simp [← hae, ← hbe]

omit [Finite G] in
theorem mem_map_preimQ_iff {X : Subgroup G} {T : Subgroup (Qt ↥X)} {t : G} :
    t ∈ (preimQ T).map X.subtype ↔ ∃ ht : t ∈ X, mkQ ↥X ⟨t, ht⟩ ∈ T := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨ht, h⟩
    exact ⟨⟨t, ht⟩, h, rfl⟩

omit [Finite G] in
theorem mkQ_mem_barX {X J : Subgroup G} (hJ : J ≤ X) {j : G} (hj : j ∈ J) :
    mkQ ↥X ⟨j, hJ hj⟩ ∈ barX 2 X J :=
  ⟨⟨j, hJ hj⟩, hj, rfl⟩

omit [Finite G] in
theorem commutator_mem_glaPPrimeCoreOf_of_commute {X : Subgroup G} {x y : G} (hx : x ∈ X)
    (hy : y ∈ X) (h : mkQ ↥X ⟨x, hx⟩ * mkQ ↥X ⟨y, hy⟩ = mkQ ↥X ⟨y, hy⟩ * mkQ ↥X ⟨x, hx⟩) :
    x * y * x⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 2 X := by
  have h1 : (⟨x, hx⟩ : ↥X) * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ ∈ GLAPPrimeCore 2 ↥X := by
    rw [← QuotientGroup.eq_one_iff]
    change mkQ ↥X (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [h]
    group
  exact ⟨_, h1, by simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]⟩

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
