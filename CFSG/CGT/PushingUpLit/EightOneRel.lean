module

public import CFSG.CGT.PushingUpLit.NineChoiceJ
public import CFSG.CGT.PushingUpLit.ThreeFromEightOneCore
public import CFSG.GroupTheory.ConjugatePairSubnormality

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open CFSG.GroupTheory (isSubnormal_subgroupOf_conjugate isSubnormal_subgroupOf_of_le
  isSubnormal_subgroupOf_subgroupOf_iff)
open scoped commutatorElement

section Arrow

variable {G G' : Type} [Group G] [Group G']

theorem EightOneRel.map_shortU_map_subtype (f : G →* G') (hf : Function.Injective f)
    (X : Subgroup G) :
    (shortU ↥(X.map f)).map (X.map f).subtype = ((shortU ↥X).map X.subtype).map f := by
  let e : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
  have hcomp : (X.map f).subtype.comp e.toMonoidHom = f.comp X.subtype := by
    ext x
    rfl
  rw [← map_shortU_mulEquiv e, Subgroup.map_map, hcomp, ← Subgroup.map_map]

theorem arrow_map_of_injective (f : G →* G') (hf : Function.Injective f) {X L : Subgroup G}
    (h : Arrow X L) : Arrow (X.map f) (L.map f) := by
  rcases h with rfl | ⟨n, m, ⟨ψ⟩, φ, F, hF, hU, hXL, hstab⟩
  · exact Or.inl rfl
  · let eX : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
    let eL : ↥L ≃* ↥(L.map f) := L.equivMapOfInjective f hf
    refine Or.inr ⟨n, m, ⟨(quotPCoreEquiv eX).symm.trans ψ⟩, (quotPCoreEquiv eL).symm.trans φ,
      F, hF, ?_, Subgroup.map_mono hXL, ?_⟩
    · rw [EightOneRel.map_shortU_map_subtype f hf, EightOneRel.map_shortU_map_subtype f hf]
      exact Subgroup.map_mono hU
    · have hsub : (X.subgroupOf L).map eL.toMonoidHom = (X.map f).subgroupOf (L.map f) := by
        ext z
        obtain ⟨y, rfl⟩ := eL.surjective z
        refine (Subgroup.mem_map_iff_mem (f := eL.toMonoidHom) eL.injective).trans ?_
        exact (Subgroup.mem_map_iff_mem hf (K := X) (x := (y : G))).symm
      have hq : ((X.subgroupOf L).map eL.toMonoidHom).map
          (QuotientGroup.mk' (pCore 2 ↥(L.map f))) =
          ((X.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))).map
            (quotPCoreEquiv eL).toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
      have hφ : ∀ T : Subgroup (↥L ⧸ pCore 2 ↥L),
          (T.map (quotPCoreEquiv eL).toMonoidHom).map
            ((quotPCoreEquiv eL).symm.trans φ).toMonoidHom = T.map φ.toMonoidHom := by
        intro T
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp
      rw [← hsub, hq, hφ]
      exact hstab

theorem arrow_map_mulEquiv (e : G ≃* G') {X L : Subgroup G} (h : Arrow X L) :
    Arrow (X.map e.toMonoidHom) (L.map e.toMonoidHom) :=
  arrow_map_of_injective e.toMonoidHom e.injective h

theorem arrow_map_subtype {K : Subgroup G} {X L : Subgroup ↥K} (h : Arrow X L) :
    Arrow (X.map K.subtype) (L.map K.subtype) :=
  arrow_map_of_injective K.subtype K.subtype_injective h

theorem arrow_conj {X L : Subgroup G} (h : Arrow X L) (g : G) :
    Arrow (conjugate X g) (conjugate L g) :=
  arrow_map_mulEquiv (MulAut.conj g⁻¹) h

end Arrow

namespace EightOneRel

section Ambient

variable {G : Type} [Group G]

theorem normalizer_subgroupOf_eq {N R : Subgroup G} (hRN : R ≤ N) :
    Subgroup.normalizer ((R.subgroupOf N : Subgroup ↥N) : Set ↥N) =
      (Subgroup.normalizer (R : Set G) ⊓ N).subgroupOf N := by
  rw [Subgroup.inf_subgroupOf_right, Subgroup.subgroupOf_normalizer_eq hRN]

theorem jIn_subgroupOf [Finite G] {A K : Subgroup G} (hAK : A ≤ K) :
    jIn (A.subgroupOf K) = (jIn A).subgroupOf K := by
  have h := map_jIn_subgroupOf hAK
  rw [← h]
  exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective _).symm

theorem isSylowOf_subgroupOf_iff [Finite G] {N X R : Subgroup G} (hXN : X ≤ N) (hRN : R ≤ N) :
    IsSylowOf 2 (R.subgroupOf N) (centralizerModCore (X.subgroupOf N)) ↔
      IsSylowOf 2 R (centralizerModCore X ⊓ N) := by
  rw [← Sec9B.isSylowOf_map_iff (f := N.subtype) N.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hRN, map_centralizerModCore_subgroupOf hXN]

theorem sylowClause_subgroupOf_iff {N X R : Subgroup G} (hXN : X ≤ N) (hRN : R ≤ N) :
    (X.subgroupOf N ≤ Subgroup.normalizer ((R.subgroupOf N : Subgroup ↥N) : Set ↥N) ∧
      ((X.subgroupOf N).subgroupOf
        (Subgroup.normalizer ((R.subgroupOf N : Subgroup ↥N) : Set ↥N))).IsSubnormal) ↔
    (X ≤ Subgroup.normalizer (R : Set G) ∧
      (X.subgroupOf (Subgroup.normalizer (R : Set G) ⊓ N)).IsSubnormal) := by
  rw [normalizer_subgroupOf_eq hRN]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, (isSubnormal_subgroupOf_subgroupOf_iff inf_le_right).mp h2⟩
    have h3 := h1 (show (⟨x, hXN hx⟩ : ↥N) ∈ X.subgroupOf N from hx)
    exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 h3)).1
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, (isSubnormal_subgroupOf_subgroupOf_iff inf_le_right).mpr h2⟩
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨h1 hx, x.2⟩)

theorem sylowClauseJ_subgroupOf_iff [Finite G] {N X R : Subgroup G} (hXN : X ≤ N)
    (hRN : R ≤ N) :
    (X.subgroupOf N ≤ Subgroup.normalizer ((jIn (R.subgroupOf N) : Subgroup ↥N) : Set ↥N) ∧
      ((X.subgroupOf N).subgroupOf
        (Subgroup.normalizer ((jIn (R.subgroupOf N) : Subgroup ↥N) : Set ↥N))).IsSubnormal) ↔
    (X ≤ Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ∧
      (X.subgroupOf (Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ⊓ N)).IsSubnormal) := by
  rw [jIn_subgroupOf hRN]
  exact sylowClause_subgroupOf_iff hXN ((jIn_le R).trans hRN)

theorem commutatorClause_subgroupOf_iff [Finite G] {N X : Subgroup G} (hXN : X ≤ N) :
    (X.subgroupOf N = ⁅jIn (Subgroup.normalizer ((X.subgroupOf N : Subgroup ↥N) : Set ↥N)),
      X.subgroupOf N⁆) ↔ (X = ⁅jIn (Subgroup.normalizer (X : Set G) ⊓ N), X⁆) := by
  rw [normalizer_subgroupOf_eq hXN, jIn_subgroupOf inf_le_right]
  have hJ : jIn (Subgroup.normalizer (X : Set G) ⊓ N) ≤ N := (jIn_le _).trans inf_le_right
  constructor
  · intro h
    have h' := congrArg (Subgroup.map N.subtype) h
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXN,
      Subgroup.map_subgroupOf_eq_of_le hJ] at h'
  · intro h
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXN,
      Subgroup.map_subgroupOf_eq_of_le hJ]
    exact h

theorem conjugate_normalizer_eq (D : Subgroup G) (a : G) :
    conjugate (Subgroup.normalizer (D : Set G)) a =
      Subgroup.normalizer ((conjugate D a : Subgroup G) : Set G) :=
  Subgroup.map_equiv_normalizer_eq D (MulAut.conj a⁻¹)

theorem conjugate_inf_eq (A B : Subgroup G) (a : G) :
    conjugate (A ⊓ B) a = conjugate A a ⊓ conjugate B a :=
  Subgroup.map_inf_eq A B _ (MulAut.conj a⁻¹).injective

theorem conjugate_jIn [Finite G] (D : Subgroup G) (a : G) :
    conjugate (jIn D) a = jIn (conjugate D a) :=
  (jIn_map_equiv (MulAut.conj a⁻¹) D).symm

theorem conjugate_eq_of_mem {N : Subgroup G} {a : G} (ha : a ∈ N) : conjugate N a = N :=
  ThreeFromEight.conjugate_eq_self_of_mem_normalizer (Subgroup.le_normalizer ha)

theorem exists_conjugate_eq_of_isSylowOf [Finite G] {K R D : Subgroup G}
    (hR : IsSylowOf 2 R K) (hD : IsSylowOf 2 D K) : ∃ a ∈ K, R = conjugate D a := by
  obtain ⟨SR, hSR⟩ := sylow_of_isSylowOf hR
  obtain ⟨SD, hSD⟩ := sylow_of_isSylowOf hD
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K SD SR
  have hmem : ∀ y : K, y ∈ (SR : Subgroup K) ↔ g⁻¹ * y * g ∈ (SD : Subgroup K) := by
    intro y
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.inv_def, MulAut.conj_symm_apply]
  refine ⟨(g : G)⁻¹, K.inv_mem g.2, ?_⟩
  ext x
  rw [ThreeFromEight.mem_conjugate_iff]
  simp only [inv_inv]
  constructor
  · intro hx
    have hxK : x ∈ K := hR.1 hx
    have h1 : (⟨x, hxK⟩ : K) ∈ (SR : Subgroup K) := by
      rw [hSR]
      exact hx
    have h2 := (hmem _).mp h1
    rw [hSD] at h2
    exact h2
  · intro hx
    have hxK : x ∈ K := by
      have hD' : (g : G)⁻¹ * x * g ∈ K := hD.1 hx
      have := K.mul_mem (K.mul_mem g.2 hD') (K.inv_mem g.2)
      simpa [mul_assoc] using this
    have h1 : (g⁻¹ * ⟨x, hxK⟩ * g : K) ∈ (SD : Subgroup K) := by
      rw [hSD]
      exact hx
    have h2 := (hmem _).mpr h1
    rw [hSR] at h2
    exact h2

theorem sylowClause_conjugate {N X D : Subgroup G} {a : G}
    (haX : a ∈ Subgroup.normalizer (X : Set G)) (haN : a ∈ N)
    (h : X ≤ Subgroup.normalizer (D : Set G) ∧
      (X.subgroupOf (Subgroup.normalizer (D : Set G) ⊓ N)).IsSubnormal) :
    X ≤ Subgroup.normalizer ((conjugate D a : Subgroup G) : Set G) ∧
      (X.subgroupOf
        (Subgroup.normalizer ((conjugate D a : Subgroup G) : Set G) ⊓ N)).IsSubnormal := by
  have hX : conjugate X a = X := ThreeFromEight.conjugate_eq_self_of_mem_normalizer haX
  have hN : conjugate N a = N := conjugate_eq_of_mem haN
  refine ⟨?_, ?_⟩
  · have h1 : conjugate X a ≤ conjugate (Subgroup.normalizer (D : Set G)) a :=
      Subgroup.map_mono h.1
    rwa [hX, conjugate_normalizer_eq] at h1
  · have h2 := isSubnormal_subgroupOf_conjugate a h.2
    rwa [hX, conjugate_inf_eq, conjugate_normalizer_eq, hN] at h2

theorem isSubnormal_subgroupOf_inf_top_iff (X K : Subgroup G) :
    (X.subgroupOf (K ⊓ ⊤)).IsSubnormal ↔ (X.subgroupOf K).IsSubnormal := by
  rw [inf_top_eq]

end Ambient

end EightOneRel

section ClassXIn

variable {G : Type} [Group G] [Finite G]

open EightOneRel

@[expose] def InClassXGIn (N X : Subgroup G) : Prop := X ≤ N ∧ InClassXG (X.subgroupOf N)

theorem inClassXGIn_iff {N X : Subgroup G} :
    InClassXGIn N X ↔ X ≤ N ∧ InClassX ↥X ∧
      ∀ R : Subgroup G, IsSylowOf 2 R (centralizerModCore X ⊓ N) →
        (X ≤ Subgroup.normalizer (R : Set G) ∧
          (X.subgroupOf (Subgroup.normalizer (R : Set G) ⊓ N)).IsSubnormal) ∧
        (X = ⁅jIn (Subgroup.normalizer (X : Set G) ⊓ N), X⁆ ∨
          (X ≤ Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ∧
            (X.subgroupOf
              (Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ⊓ N)).IsSubnormal)) := by
  constructor
  · rintro ⟨hXN, hX1, hX2⟩
    refine ⟨hXN, (inClassX_subgroupOf_iff hXN).mp hX1, fun R hR => ?_⟩
    have hRN : R ≤ N := hR.1.trans inf_le_right
    obtain ⟨hc1, hc2⟩ :=
      hX2 (R.subgroupOf N) ((isSylowOf_subgroupOf_iff hXN hRN).mpr hR)
    exact ⟨(sylowClause_subgroupOf_iff hXN hRN).mp hc1,
      hc2.imp (commutatorClause_subgroupOf_iff hXN).mp (sylowClauseJ_subgroupOf_iff hXN hRN).mp⟩
  · rintro ⟨hXN, hX1, hX2⟩
    refine ⟨hXN, (inClassX_subgroupOf_iff hXN).mpr hX1, fun R' hR' => ?_⟩
    obtain ⟨R, hRN, rfl⟩ : ∃ R : Subgroup G, R ≤ N ∧ R.subgroupOf N = R' :=
      ⟨R'.map N.subtype, Subgroup.map_subtype_le R',
        Subgroup.comap_map_eq_self_of_injective N.subtype_injective R'⟩
    obtain ⟨hc1, hc2⟩ := hX2 R ((isSylowOf_subgroupOf_iff hXN hRN).mp hR')
    exact ⟨(sylowClause_subgroupOf_iff hXN hRN).mpr hc1,
      hc2.imp (commutatorClause_subgroupOf_iff hXN).mpr (sylowClauseJ_subgroupOf_iff hXN hRN).mpr⟩

theorem inClassXGIn_of_sylow {N X D : Subgroup G} (hXN : X ≤ N) (hX : InClassX ↥X)
    (hD : IsSylowOf 2 D (centralizerModCore X ⊓ N))
    (h1 : X ≤ Subgroup.normalizer (D : Set G) ∧
      (X.subgroupOf (Subgroup.normalizer (D : Set G) ⊓ N)).IsSubnormal)
    (h2 : X = ⁅jIn (Subgroup.normalizer (X : Set G) ⊓ N), X⁆ ∨
      (X ≤ Subgroup.normalizer ((jIn D : Subgroup G) : Set G) ∧
        (X.subgroupOf
          (Subgroup.normalizer ((jIn D : Subgroup G) : Set G) ⊓ N)).IsSubnormal)) :
    InClassXGIn N X := by
  rw [inClassXGIn_iff]
  refine ⟨hXN, hX, fun R hR => ?_⟩
  obtain ⟨a, ha, rfl⟩ := exists_conjugate_eq_of_isSylowOf hR hD
  have ha' := Subgroup.mem_inf.1 ha
  have haX : a ∈ Subgroup.normalizer (X : Set G) := (mem_centralizerModCore_iff.1 ha'.1).1
  have haN : a ∈ N := ha'.2
  refine ⟨sylowClause_conjugate haX haN h1, h2.imp_right fun h2' => ?_⟩
  rw [← conjugate_jIn]
  exact sylowClause_conjugate haX haN h2'

theorem inClassXG_iff_inClassXGIn_top {X : Subgroup G} : InClassXG X ↔ InClassXGIn ⊤ X := by
  rw [inClassXGIn_iff]
  simp only [inf_top_eq, le_top, true_and, isSubnormal_subgroupOf_inf_top_iff]
  exact Iff.rfl

theorem inClassXG_of_sylow {X D : Subgroup G} (hX : InClassX ↥X)
    (hD : IsSylowOf 2 D (centralizerModCore X))
    (h1 : X ≤ Subgroup.normalizer (D : Set G) ∧
      (X.subgroupOf (Subgroup.normalizer (D : Set G))).IsSubnormal)
    (h2 : X = ⁅jIn (Subgroup.normalizer (X : Set G)), X⁆ ∨
      (X ≤ Subgroup.normalizer ((jIn D : Subgroup G) : Set G) ∧
        (X.subgroupOf (Subgroup.normalizer ((jIn D : Subgroup G) : Set G))).IsSubnormal)) :
    InClassXG X := by
  rw [inClassXG_iff_inClassXGIn_top]
  refine inClassXGIn_of_sylow (D := D) le_top hX ?_ ?_ ?_
  · rwa [inf_top_eq]
  · simpa only [isSubnormal_subgroupOf_inf_top_iff] using h1
  · simpa only [inf_top_eq, isSubnormal_subgroupOf_inf_top_iff] using h2

end ClassXIn

section Conj

variable {G : Type} [Group G]

theorem inClassX_conjugate [Finite G] {X : Subgroup G} (h : InClassX ↥X) (g : G) :
    InClassX ↥(conjugate X g) :=
  InClassX.of_mulEquiv ((MulAut.conj g⁻¹).subgroupMap X) h

theorem isSubnormal_conjugate {X N : Subgroup G} {g : G} (h : (X.subgroupOf N).IsSubnormal)
    (hN : g ∈ N) : ((conjugate X g).subgroupOf N).IsSubnormal := by
  have h1 := isSubnormal_subgroupOf_conjugate g h
  rwa [EightOneRel.conjugate_eq_of_mem hN] at h1

theorem isSubnormal_subgroupOf_mono {X K N : Subgroup G} (_hXK : X ≤ K) (hKN : K ≤ N)
    (h : (X.subgroupOf N).IsSubnormal) : (X.subgroupOf K).IsSubnormal :=
  isSubnormal_subgroupOf_of_le hKN h

end Conj

end CFSG.CGT.PushingUpLit
