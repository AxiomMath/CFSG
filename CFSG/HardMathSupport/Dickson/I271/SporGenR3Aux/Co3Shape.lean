module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Co3Cent
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.L28Leaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Pair
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Co3
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalBridge
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SimpleLeaf

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Open CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.Sporadic.Schreier.Co3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T
  CFSG.HardMathSupport.Dickson.I271.Co3Cent CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump
  CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

section Classes


open CFSG.HardMathSupport.Solomon.Coordinator.YS08 in
theorem XA_eq : XA = Co3Copy.xA :=
  CFSG.RankThree.Native.permOfArr_eq_of_rep Co3Copy.rep_xA

open CFSG.HardMathSupport.Solomon.Coordinator.YS08 in
theorem XB_eq : XB = Co3Copy.xB :=
  CFSG.RankThree.Native.permOfArr_eq_of_rep Co3Copy.rep_xB

open CFSG.HardMathSupport.Solomon.Coordinator.YS08 in
theorem exists_conj_classes {s : Equiv.Perm (Fin 276)} (hs : s ∈ co3P) (hs3 : orderOf s = 3) :
    ∃ k ∈ co3P, ∃ c : Equiv.Perm (Fin 276), (c = XA ∨ c = XB ∨ c = yPerm) ∧ ∃ e : ℕ,
      (e = 1 ∨ e = 2) ∧ k * c ^ e * k⁻¹ = s := by
  obtain ⟨h, hh, hcase⟩ := exists_conj_D_or_y hs hs3
  have hhinv : h⁻¹ ∈ co3P := co3P.inv_mem hh
  have hback : h⁻¹ * (h * s * h⁻¹) * h⁻¹⁻¹ = s := by group
  rcases hcase with hD | hy | hy2
  · obtain ⟨a, ha⟩ := hD
    have hk : idx a.toAdd < 243 := idx_lt _
    have hvec : φ (Multiplicative.ofAdd (vec (idx a.toAdd))) = h * s * h⁻¹ := by
      rw [vec_idx]
      exact ha
    have hk0 : idx a.toAdd ≠ 0 := by
      intro h0
      have ha0 : a.toAdd = 0 := (idx_eq_zero_iff _).1 h0
      have : a = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_one]
        exact ha0
      rw [this, map_one] at ha
      have hs1 : s = 1 := by
        have : h * s * h⁻¹ = 1 := ha.symm
        simpa using this
      rw [hs1, orderOf_one] at hs3
      omega
    obtain ⟨h', hh', hfuse⟩ := Co3Copy.fuse_sound _ hk hk0
    rw [hvec] at hfuse
    refine ⟨h⁻¹ * h', co3P.mul_mem hhinv hh', ?_⟩
    rcases hfuse with hf | hf
    · refine ⟨XA, Or.inl rfl, 1, Or.inl rfl, ?_⟩
      rw [XA_eq]
      calc h⁻¹ * h' * Co3Copy.xA ^ 1 * (h⁻¹ * h')⁻¹
          = h⁻¹ * (h' * Co3Copy.xA * h'⁻¹) * h⁻¹⁻¹ := by group
        _ = s := by rw [hf]; exact hback
    · refine ⟨XB, Or.inr (Or.inl rfl), 1, Or.inl rfl, ?_⟩
      rw [XB_eq]
      calc h⁻¹ * h' * Co3Copy.xB ^ 1 * (h⁻¹ * h')⁻¹
          = h⁻¹ * (h' * Co3Copy.xB * h'⁻¹) * h⁻¹⁻¹ := by group
        _ = s := by rw [hf]; exact hback
  · refine ⟨h⁻¹, hhinv, yPerm, Or.inr (Or.inr rfl), 1, Or.inl rfl, ?_⟩
    rw [pow_one, ← hy]
    exact hback
  · refine ⟨h⁻¹, hhinv, yPerm, Or.inr (Or.inr rfl), 2, Or.inr rfl, ?_⟩
    rw [← hy2]
    exact hback

end Classes

section Shapes


theorem shape_XB {XBm : XB ∈ co3P} :
    ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (⟨XB, XBm⟩ : ↥co3P) := by
  left
  refine pConstrainedShape_of_map_injective co3P.subtype co3P.subtype_injective ?_
  rw [map_centralizer_subtype']
  obtain ⟨-, -, -, hcard, hle, hnorm, hcent⟩ := caseB_spec
  exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
    (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent

theorem shape_XA {XAm : XA ∈ co3P} :
    ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (⟨XA, XAm⟩ : ↥co3P) := by
  left
  refine pConstrainedShape_of_map_injective co3P.subtype co3P.subtype_injective ?_
  rw [map_centralizer_subtype']
  obtain ⟨-, -, -, hcard, hle, hnorm, hcent⟩ := caseA_spec
  exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
    (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent

@[expose] noncomputable def lGen (i : Fin 2) : Equiv.Perm (Fin 276) :=
  permOfArr 276 (lGens ())[i.val]!

theorem range_lGen : Set.range lGen = permsA 276 (lGens ()) := by
  have hl2 : (lGens ()).size = 2 := by simp [lGens]
  ext σ
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, by rw [hl2]; exact i.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    have hk2 : k < 2 := by rw [hl2] at hk; exact hk
    exact ⟨⟨k, hk2⟩, rfl⟩

theorem nonempty_mulEquiv_L :
    Nonempty (↥(closure (permsA 276 (lGens ()))) ≃*
      ↥(CFSG.GH74.KGroups.L28.QP.originalSubgroup)) := by
  obtain ⟨-, -, -, hLcard, hrels⟩ := caseC_spec
  rw [← range_lGen] at hLcard ⊢
  obtain ⟨e⟩ := nonempty_mulEquiv_P9_of_rels lGen hrels hLcard
  exact ⟨e⟩

theorem shape_y {yPm : yPerm ∈ co3P} :
    ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (⟨yPerm, yPm⟩ : ↥co3P) := by
  obtain ⟨⟨hC, hCcard⟩, hLC, hder, hLcard, hrels⟩ := caseC_spec
  obtain ⟨e⟩ := nonempty_mulEquiv_L
  refine shapeRkAt_of_subgroup_data (P := co3P) (L := closure (permsA 276 (lGens ())))
    Nat.prime_three (fun _ _ _ _ e h => LeafType.of_equiv e h) (fun _ _ _ _ _ h => h)
    ⟨yPerm, yPm⟩ (hC ▸ hLC) ?_ (isSimpleGroup_of_equiv_P9 e) (nonabelian_of_equiv_P9 e) ?_
    (k := 2) ?_ (leafType_three_of_equiv_P9 e) trivial
  · intro g hg l hl
    rw [← hC] at hg
    have h1 : ⁅g, l⁆ ∈ ⁅closure (permsA 276 (cGens ())), closure (permsA 276 (cGens ()))⁆ :=
      Subgroup.commutator_mem_commutator hg (hLC hl)
    have h2 := hder h1
    have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
      rw [commutatorElement_def]; group
    rw [h3]
    exact (closure (permsA 276 (lGens ()))).mul_mem h2 hl
  · rw [hLcard]; norm_num
  · rw [← hC, hCcard, hLcard]; norm_num

end Shapes

section Assembly


theorem co3_centShapeRk :
    CentShapeRk 3 (LeafType 3) (fun _ _ => True) ↥co3P := by
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → LeafType 3 T → LeafType 3 T' :=
    fun _ _ _ _ e h => LeafType.of_equiv e h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  obtain ⟨hXA3, -, hXAm, -⟩ := caseA_spec
  obtain ⟨hXB3, -, hXBm, -⟩ := caseB_spec
  intro k hk1 hkp
  have hs3 : orderOf (k : Equiv.Perm (Fin 276)) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h1 : (k : Equiv.Perm (Fin 276)) ^ 3 = 1 := by
      have := congrArg Subtype.val hkp
      simpa using this
    have h2 : (k : Equiv.Perm (Fin 276)) ≠ 1 := fun h => hk1 (Subtype.ext h)
    exact orderOf_eq_prime h1 h2
  obtain ⟨h, hh, c, hc, e, he, hcon⟩ := exists_conj_classes k.2 hs3
  have hrep : ∃ c' : ↥co3P, (c' : Equiv.Perm (Fin 276)) = c ∧ c' ^ 3 = 1 ∧
      ShapeRkAt 3 (LeafType 3) (fun _ _ => True) c' := by
    rcases hc with rfl | rfl | rfl
    · exact ⟨⟨XA, hXAm⟩, rfl, Subtype.ext (by simpa using hXA3), shape_XA (XAm := hXAm)⟩
    · exact ⟨⟨XB, hXBm⟩, rfl, Subtype.ext (by simpa using hXB3), shape_XB (XBm := hXBm)⟩
    · exact ⟨⟨yPerm, yPerm_mem⟩, rfl, Subtype.ext (by simpa using yPerm_pow),
        shape_y (yPm := yPerm_mem)⟩
  obtain ⟨c', hc'val, hc'3, hshape⟩ := hrep
  have hshape' : ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (c' ^ e) :=
    ShapeRkAt.of_centralizer_eq (CFSG.Quasithin.Kleidman.centralizer_pow_eq hc'3 he).symm hshape
  have hconj := ShapeRkAt.of_equiv Nat.prime_three hGood hRk
    (MulAut.conj (⟨h, hh⟩ : ↥co3P)) hshape'
  have hk : (MulAut.conj (⟨h, hh⟩ : ↥co3P)) (c' ^ e) = k := by
    apply Subtype.ext
    rw [← hcon, ← hc'val]
    simp [MulAut.conj_apply]
  rw [hk] at hconj
  exact hconj

theorem leafShape_Co3 : LeafShape .Co3 3 := by
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Co3) :=
    Finite.of_equiv ↥co3P (co3PermEquiv : CFSG.Blueprint.NativeSporadic.Co3 ≃* co3P).symm.toEquiv
  exact CentShape.of_centShapeRk (CentShapeRk.of_equiv Nat.prime_three
    (fun _ _ _ _ e h => LeafType.of_equiv e h) (fun _ _ _ _ _ h => h)
    (co3PermEquiv : CFSG.Blueprint.NativeSporadic.Co3 ≃* co3P).symm co3_centShapeRk)

end Assembly

end CFSG.HardMathSupport.Dickson.I271
