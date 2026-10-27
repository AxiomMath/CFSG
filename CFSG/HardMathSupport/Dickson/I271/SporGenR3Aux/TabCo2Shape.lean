module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2Cent
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2U42
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalBridge

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Open CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T
  CFSG.HardMathSupport.Dickson.I271.Co2Cent CFSG.HardMathSupport.Dickson.I271.U42Presentation

theorem normal_subgroupOf_of_forall_conj {S : Type*} [Group S] {R C : Subgroup S}
    (h : ∀ g ∈ C, ∀ r ∈ R, g * r * g⁻¹ ∈ R) : (R.subgroupOf C).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact h g g.2 x hx⟩

section Shapes


theorem co2Shape_XA {XAm : co2XA ∈ co2P} :
    ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (⟨co2XA, XAm⟩ : ↥co2P) := by
  left
  refine pConstrainedShape_of_map_injective co2P.subtype co2P.subtype_injective ?_
  rw [map_centralizer_subtype']
  obtain ⟨-, -, -, hcard, hle, hnorm, hcent⟩ := co2CaseA_spec
  exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_forall_conj hnorm)
    (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent

theorem co2Shape_XB {XBm : co2XB ∈ co2P} :
    ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (⟨co2XB, XBm⟩ : ↥co2P) := by
  obtain ⟨-, -, -, hcard, hLC, hLn, hcent, hrels⟩ := co2CaseB_spec
  obtain ⟨e⟩ := nonempty_mulEquiv_QP45_of_rels uvGen hrels hcard
  exact shapeRkAt_of_subgroup_data_nq Nat.prime_three
    (fun _ _ _ _ e h => LeafType.of_equiv e h) (fun _ _ _ _ _ h => h) co2P ⟨co2XB, XBm⟩ Lsub hLC hLn
    (isSimpleGroup_of_equiv_QP45 e) (nonabelian_of_equiv_QP45 e)
    (three_dvd_card_of_equiv_QP45 e) hcent (leafType_three_of_equiv_QP45 e) trivial

end Shapes

section Assembly


theorem co2_centShapeRk :
    CentShapeRk 3 (LeafType 3) (fun _ _ => True) ↥co2P := by
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → LeafType 3 T → LeafType 3 T' :=
    fun _ _ _ _ e h => LeafType.of_equiv e h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  obtain ⟨hXA3, -, hXAm, -⟩ := co2CaseA_spec
  obtain ⟨hXB3, -, hXBm, -⟩ := co2CaseB_spec
  intro k hk1 hkp
  have hs3 : orderOf (k : Equiv.Perm (Fin 2300)) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h1 : (k : Equiv.Perm (Fin 2300)) ^ 3 = 1 := by
      have := congrArg Subtype.val hkp
      simpa using this
    have h2 : (k : Equiv.Perm (Fin 2300)) ≠ 1 := fun h => hk1 (Subtype.ext h)
    exact orderOf_eq_prime h1 h2
  obtain ⟨h, hh, c, hc, e, he, hcon⟩ := co2_exists_conj_classes k.2 hs3
  have hrep : ∃ c' : ↥co2P, (c' : Equiv.Perm (Fin 2300)) = c ∧ c' ^ 3 = 1 ∧
      ShapeRkAt 3 (LeafType 3) (fun _ _ => True) c' := by
    rcases hc with rfl | rfl
    · exact ⟨⟨co2XA, hXAm⟩, rfl, Subtype.ext (by simpa using hXA3), co2Shape_XA (XAm := hXAm)⟩
    · exact ⟨⟨co2XB, hXBm⟩, rfl, Subtype.ext (by simpa using hXB3), co2Shape_XB (XBm := hXBm)⟩
  obtain ⟨c', hc'val, hc'3, hshape⟩ := hrep
  have hshape' : ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (c' ^ e) :=
    ShapeRkAt.of_centralizer_eq (CFSG.Quasithin.Kleidman.centralizer_pow_eq hc'3 he).symm hshape
  have hconj := ShapeRkAt.of_equiv Nat.prime_three hGood hRk
    (MulAut.conj (⟨h, hh⟩ : ↥co2P)) hshape'
  have hk : (MulAut.conj (⟨h, hh⟩ : ↥co2P)) (c' ^ e) = k := by
    apply Subtype.ext
    rw [← hcon, ← hc'val]
    simp [MulAut.conj_apply]
  rw [hk] at hconj
  exact hconj

end Assembly

section Carrier


theorem leafShape_Co2 : LeafShape .Co2 3 := by
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Co2) :=
    Finite.of_equiv ↥co2P (co2PermEquiv : CFSG.Blueprint.NativeSporadic.Co2 ≃* co2P).symm.toEquiv
  exact CentShape.of_centShapeRk (CentShapeRk.of_equiv Nat.prime_three
    (fun _ _ _ _ e h => LeafType.of_equiv e h) (fun _ _ _ _ _ h => h)
    (co2PermEquiv : CFSG.Blueprint.NativeSporadic.Co2 ≃* co2P).symm co2_centShapeRk)

end Carrier

end CFSG.HardMathSupport.Dickson.I271
