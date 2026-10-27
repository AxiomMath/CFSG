module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SimpleLeaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Leaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNThreeBR
public import Certificates.Certificate17380
public import Certificates.Certificate13609
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HN
public import CFSG.Sporadic.HNSchreier.Intrinsic

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open scoped commutatorElement

section General

theorem shapeRkAt_of_data {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T') (x : Q)
    (L : Subgroup Q) (hLC : L ≤ Subgroup.centralizer ({x} : Set Q))
    (hLn : ∀ g ∈ Subgroup.centralizer ({x} : Set Q), ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hpL : p ∣ Nat.card ↥L)
    {k : ℕ} (hk : Nat.card ↥(Subgroup.centralizer ({x} : Set Q)) = Nat.card ↥L * p ^ k)
    (hG : Good ↥L) (hR : Rk ↥L) : ShapeRkAt p Good Rk x := by
  let C' : Subgroup Q := Subgroup.centralizer ({x} : Set Q)
  let E : Subgroup ↥C' := L.subgroupOf C'
  have hEn : E.Normal := by
    refine ⟨fun e he g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at he ⊢
    exact hLn _ g.2 _ he
  haveI := hEn
  have hEmap : E.map C'.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLC
  have eE : ↥(E.map C'.subtype) ≃* ↥L := MulEquiv.subgroupCongr hEmap
  have hsE : IsSimpleGroup ↥(E.map C'.subtype) := eE.isSimpleGroup_congr.2 hs
  have hnabE : ∃ a b : ↥(E.map C'.subtype), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eE.symm a, eE.symm b, fun h => hab (by simpa using congrArg eE h)⟩
  have hpE : p ∣ Nat.card ↥(E.map C'.subtype) := by
    rw [Nat.card_congr eE.toEquiv]; exact hpL
  have hq : IsPGroup p (↥C' ⧸ E) := by
    have hcardE : Nat.card ↥E = Nat.card ↥L := by
      rw [← Subgroup.card_map_of_injective C'.subtype_injective, hEmap]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup E
    haveI : Fact p.Prime := ⟨hp⟩
    refine IsPGroup.of_card (n := k) ?_
    have hpos : 0 < Nat.card ↥L := Nat.card_pos
    rw [hk, hcardE] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_comm (Nat.card ↥L) _, ← h1])
  have hZE : Subgroup.center ↥(E.map C'.subtype) = ⊥ := by
    haveI := hsE
    exact center_eq_bot_of_simple_nonab hnabE
  have hcoreE : GLAPPrimeCore p ↥(E.map C'.subtype) = ⊥ := by
    haveI := hsE
    exact glaPPrimeCore_eq_bot_of_simple hp hpE
  refine shapeRkAt_of_normal_pindex hp E hsE hnabE hpE hq ?_ ?_
  · exact hGood ↥L _ ((pSimpleEquivSelf (E.map C'.subtype) hcoreE hZE).trans eE).symm hG
  · exact hRk ↥L _ ((pQuotEquivSelf (E.map C'.subtype) hcoreE).trans eE).symm hR

theorem exists_noncomm_of_simple_card {G : Type} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := hc }
  exact h (IsSimpleGroup.prime_card (α := G))

theorem centShape_of_equiv_JH {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    (e : S ≃* ↥JH) (h : CentShapeRk p (LeafType p) (fun _ _ => True) ↥JH) :
    CentShape p (LeafType p) S := by
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → LeafType p T → LeafType p T' :=
    fun _ _ _ _ e h => LeafType.of_equiv e h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  exact CentShape.of_centShapeRk (@CentShapeRk.of_equiv ↥JH S (inferInstance : Group ↥JH)
    (inferInstance : Finite ↥JH) (inferInstance : Group S) p hp (LeafType p)
    (fun _ _ => True) hGood hRk (inferInstance : Finite S) e.symm h)

end General

section ThreeA


theorem L1J_leafType : LeafType 3 ↥L1J :=
  Or.inr ⟨9, by norm_num, by norm_num, by norm_num,
    ⟨(alt9Equiv.trans (alt3.equivMapOfInjective iotaA iotaA_injective)).symm⟩⟩

set_option maxRecDepth 4000 in
theorem shape_s1 : ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (sJ 0) := by
  obtain ⟨-, -, hcomm⟩ := CJ_s1_structure
  have hder := commutator_CJ_s1
  haveI hsimple : IsSimpleGroup ↥L1J := by
    have := alt3_simple
    exact MulEquiv.isSimpleGroup (alt3.equivMapOfInjective iotaA iotaA_injective).symm
  have hcard : Nat.card ↥L1J = 181440 := by
    rw [show (L1J : Subgroup JH) = alt3.map iotaA from rfl,
      Subgroup.card_map_of_injective iotaA_injective, card_alt3]
  have hLC : L1J ≤ Subgroup.centralizer ({sJ 0} : Set ↥JH) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx)
  have hnp : ¬ (Nat.card ↥L1J).Prime := by
    rw [hcard]
    norm_num
  have hnab : ∃ a b : ↥L1J, a * b ≠ b * a := exists_noncomm_of_simple_card (G := ↥L1J) hnp
  have h3 : 3 ∣ Nat.card ↥L1J := by
    rw [hcard]
    norm_num
  have hk : Nat.card ↥(Subgroup.centralizer ({sJ 0} : Set ↥JH)) = Nat.card ↥L1J * 3 ^ 1 := by
    rw [show Subgroup.centralizer ({sJ 0} : Set ↥JH) = CJ (sJ 0) from rfl, card_CJ_s1, hcard]
    norm_num
  refine shapeRkAt_of_data Nat.prime_three (fun _ _ _ _ e h => LeafType.of_equiv e h)
    (fun _ _ _ _ _ h => h) (sJ 0) L1J hLC ?_ hsimple hnab h3 hk L1J_leafType trivial
  intro g hg l hl
  have h1 : ⁅g, l⁆ ∈ ⁅CJ (sJ 0), CJ (sJ 0)⁆ := Subgroup.commutator_mem_commutator hg (hLC hl)
  rw [hder] at h1
  have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
    rw [commutatorElement_def]; group
  rw [h3]
  exact L1J.mul_mem h1 hl

end ThreeA

section ThreeB


theorem hn3bR_checks : ∃ R : Subgroup JH, R ≤ CJ (sJ 2) ∧ Nat.card R = 243 ∧
    (∀ g ∈ CJ (sJ 2), ∀ r ∈ R, g * r * g⁻¹ ∈ R) ∧
    CJ (sJ 2) ⊓ Subgroup.centralizer (R : Set JH) ≤ R :=
  Certificates.certificate17380

theorem shape_s3 : ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (sJ 2) :=
  Or.inl (pConstrainedShape_of_hn3bRChecks hn3bR_checks)

end ThreeB

section Table


theorem hn_centShapeRk : CentShapeRk 3 (LeafType 3) (fun _ _ => True) ↥JH := by
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → LeafType 3 T → LeafType 3 T' :=
    fun _ _ _ _ e h => LeafType.of_equiv e h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  intro k hk1 hkp
  have hk3 : orderOf k = 3 := orderOf_eq_prime hkp hk1
  rcases (order_three_classes k).1 hk3 with h | h
  · obtain ⟨g, hg⟩ := isConj_iff.1 h
    have := ShapeRkAt.of_equiv Nat.prime_three hGood hRk (MulAut.conj g) shape_s1
    rw [MulAut.conj_apply, hg] at this
    exact this
  · obtain ⟨g, hg⟩ := isConj_iff.1 h
    have := ShapeRkAt.of_equiv Nat.prime_three hGood hRk (MulAut.conj g) shape_s3
    rw [MulAut.conj_apply, hg] at this
    exact this

theorem leafShape_HN : LeafShape .HN 3 := by
  haveI hf : Finite CFSG.Blueprint.NativeSporadic.HN :=
    Finite.of_equiv ↥JH (hnEquivJ : CFSG.Blueprint.NativeSporadic.HN ≃* JH).symm.toEquiv
  exact @centShape_of_equiv_JH 3 Nat.prime_three CFSG.Blueprint.NativeSporadic.HN
    (inferInstance : Group CFSG.Blueprint.NativeSporadic.HN) hf hnEquivJ hn_centShapeRk

end Table

end CFSG.HardMathSupport.Dickson.I271
