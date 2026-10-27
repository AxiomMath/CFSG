module

public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.ElationGroup
public import CFSG.Geometry.GeneralizedQuadrangles.Whorls

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.GH74.BNPair
open CFSG.Geometry.GeneralizedPolygons

variable {V : Type} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {H : Type} [Group H] [MulAction H V] [FaithfulSMul H V] [GraphAction H Γ]

theorem card_fixedPointFree {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X]
    [Nonempty X] (htrans : ∀ x x' : X, ∃ g : G, g • x = x')
    (hfix : ∀ g : G, g ≠ 1 → Nat.card (MulAction.fixedBy X g) ≤ 1) :
    Nat.card {g : G // g ≠ 1 ∧ ∀ x : X, g • x ≠ x} = Fintype.card X - 1 := by
  classical
  haveI : MulAction.IsPretransitive G X := ⟨htrans⟩
  let f : G → ℕ := fun g => Nat.card (MulAction.fixedBy X g)
  have h1 : f 1 = Fintype.card X := by
    dsimp [f]
    rw [MulAction.fixedBy_one_eq_univ]
    simp [Nat.card_eq_fintype_card]
  have hburn : (∑ g : G, f g) = Fintype.card G := by
    have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
    haveI : Subsingleton (MulAction.orbitRel.Quotient G X) :=
      (MulAction.pretransitive_iff_subsingleton_quotient G X).mp inferInstance
    haveI : Nonempty (MulAction.orbitRel.Quotient G X) :=
      ⟨Quotient.mk'' (Classical.arbitrary X)⟩
    haveI : Unique (MulAction.orbitRel.Quotient G X) :=
      uniqueOfSubsingleton (Quotient.mk'' (Classical.arbitrary X))
    have hΩ : Fintype.card (MulAction.orbitRel.Quotient G X) = 1 :=
      Fintype.card_eq_one_iff_nonempty_unique.mpr ⟨inferInstance⟩
    rw [hΩ, one_mul] at h
    rw [← h]
    exact Finset.sum_congr rfl fun g _ => Nat.card_eq_fintype_card
  have hsplit : Fintype.card X + (∑ g ∈ Finset.univ.erase (1 : G), f g) = Fintype.card G := by
    rw [← Finset.add_sum_erase (Finset.univ : Finset G) f (Finset.mem_univ 1)] at hburn
    rwa [h1] at hburn
  let T : Finset G := Finset.univ.erase 1
  have hTcard : T.card = Fintype.card G - 1 := by
    dsimp [T]
    rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : G)), Finset.card_univ]
  have hTsum : (∑ g ∈ T, f g) = Fintype.card G - Fintype.card X := by
    dsimp [T]
    have := hsplit
    omega
  let S0 : Finset G := T.filter (fun g => f g = 0)
  let S1 : Finset G := T.filter (fun g => ¬ f g = 0)
  have hS0sum : (∑ g ∈ S0, f g) = 0 := by
    refine Finset.sum_eq_zero fun g hg => ?_
    dsimp [S0] at hg
    exact (Finset.mem_filter.mp hg).2
  have hS1eval : ∀ g ∈ S1, f g = 1 := by
    intro g hg
    dsimp [S1, T] at hg
    rw [Finset.mem_filter] at hg
    have hne : g ≠ 1 := Finset.ne_of_mem_erase hg.1
    have hle : f g ≤ 1 := hfix g hne
    have hpos : 0 < f g := Nat.pos_of_ne_zero hg.2
    omega
  have hS1sum : (∑ g ∈ S1, f g) = S1.card := by
    calc
      (∑ g ∈ S1, f g) = ∑ g ∈ S1, 1 := by
        exact Finset.sum_congr rfl fun g hg => hS1eval g hg
      _ = S1.card := by simp
  have hTsplit : (∑ g ∈ S0, f g) + (∑ g ∈ S1, f g) = ∑ g ∈ T, f g := by
    dsimp [S0, S1]
    exact Finset.sum_filter_add_sum_filter_not T (fun g => f g = 0) f
  have hS1card : S1.card = Fintype.card G - Fintype.card X := by
    have := hTsplit
    rw [hS0sum, hS1sum, hTsum] at this
    simpa using this
  have hS0card : S0.card = Fintype.card X - 1 := by
    have hcard : S0.card + S1.card = Fintype.card G - 1 := by
      have := Finset.card_filter_add_card_filter_not (s := T) (p := fun g => f g = 0)
      rw [hTcard] at this
      simpa [S0, S1] using this
    omega
  have hS0eq : S0 = Finset.univ.filter (fun g : G => g ≠ 1 ∧ ∀ x : X, g • x ≠ x) := by
    ext g
    dsimp [S0, T]
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hg1, -⟩, hf0⟩
      refine ⟨hg1, ?_⟩
      intro x hx
      have hpos : 0 < f g := by
        haveI : Finite (MulAction.fixedBy X g) := Subtype.finite
        rw [show f g = Nat.card (MulAction.fixedBy X g) from rfl, Finite.card_pos_iff]
        exact ⟨⟨x, hx⟩⟩
      omega
    · rintro ⟨hg1, hfree⟩
      refine ⟨⟨hg1, trivial⟩, ?_⟩
      haveI : Finite (MulAction.fixedBy X g) := Subtype.finite
      rw [show f g = Nat.card (MulAction.fixedBy X g) from rfl, Finite.card_eq_zero_iff]
      exact ⟨fun x => hfree x x.2⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← hS0eq]
  exact hS0card

theorem rootGroup_le_whorlGroup_of_mem (v : ZMod 8 → V) {p : GPath Γ 4}
    (hp0 : v 0 ∈ ({p 1, p 2, p 3} : Set V)) :
    rootGroup H Γ (p 1) (p 2) (p 3) ≤ whorlGroup H Γ (v 0) := by
  intro r hr
  have hp0' : v 0 = p 1 ∨ v 0 = p 2 ∨ v 0 = p 3 := by simpa using hp0
  rcases hp0' with h | h | h
  · rw [h]
    exact ((mem_rootGroup H).mp hr).1
  · rw [h]
    exact ((mem_rootGroup H).mp hr).2.1
  · rw [h]
    exact ((mem_rootGroup H).mp hr).2.2

theorem eq_one_of_mem_rootGroup_of_fix_opposite_of_mem (v : ZMod 8 → V) {p : GPath Γ 4}
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (hp : p.NoBack)
    (hp0 : v 0 ∈ ({p 1, p 2, p 3} : Set V)) {r : H}
    (hr : r ∈ rootGroup H Γ (p 1) (p 2) (p 3)) {x : V}
    (hx : Γ.dist (v 0) x = 4) (hrx : r • x = x) : r = 1 := by
  have hp0' : v 0 = p 1 ∨ v 0 = p 2 ∨ v 0 = p 3 := by simpa using hp0
  rcases hp0' with h | h | h
  · refine eq_one_of_mem_rootGroup_of_fix_opposite_end hP hT p hp hr ?_ hrx
    rw [← h]
    exact hx
  · refine eq_one_of_mem_rootGroup_of_fix_opposite hP hT p hp hr ?_ hrx
    rw [← h]
    exact hx
  · have hmem : r ∈ rootGroup H Γ (p.rev 1) (p.rev 2) (p.rev 3) := by
      rw [show p.rev 1 = p 3 by simp, show p.rev 2 = p 2 by simp,
        show p.rev 3 = p 1 by simp, rootGroup_comm]
      exact hr
    refine eq_one_of_mem_rootGroup_of_fix_opposite_end hP hT p.rev hp.rev hmem ?_ hrx
    rw [show p.rev 1 = p 3 by simp, ← h]
    exact hx

theorem rootGroup_le_elationGroup (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hM : MoufangCondition H Γ 4) (v : ZMod 8 → V) (hv : IsPolygonApartment Γ 4 v)
    (hv0 : c (v 0) = 0) (hspan : ∀ x, Γ.dist (v 0) x = 4 → (spanSet Γ (v 0) x).ncard = 2)
    (p : GPath Γ 4) (hp : p.NoBack) (hp0 : v 0 ∈ ({p 1, p 2, p 3} : Set V)) :
    rootGroup H Γ (p 1) (p 2) (p 3) ≤ elationGroup H Γ v := by
  classical
  let E := elationGroup H Γ v
  let Q := whorlGroup H Γ (v 0)
  haveI : Fintype ↥E :=
    Fintype.ofInjective (fun e : ↥E => fun y : V => (e : H) • y) (by
      intro e f hef
      apply Subtype.ext
      exact eq_of_smul_eq_smul (m₁ := (e : H)) (m₂ := (f : H)) (fun y => congrFun hef y))
  haveI : Fintype ↥Q :=
    Fintype.ofInjective (fun q : ↥Q => fun y : V => (q : H) • y) (by
      intro q r hqr
      apply Subtype.ext
      exact eq_of_smul_eq_smul (m₁ := (q : H)) (m₂ := (r : H)) (fun y => congrFun hqr y))
  have hQfix : ∀ q : ↥Q, (q : H) • v 0 = v 0 := fun q => whorlGroup_fix_self hP hT q.2
  have h01 : Γ.Adj (v 0) (v 1) := by
    have h := hv.2 0
    have e : ((0 : ZMod 8) + 1) = 1 := by decide
    simpa [e] using h
  have a0apt : apt (n := 4) v 0 = v 0 := by
    show v ((0 : ℤ) : ZMod 8) = v 0
    exact congrArg v (by decide)
  have a4apt : apt (n := 4) v 4 = v 4 := by
    show v ((4 : ℤ) : ZMod 8) = v 4
    exact congrArg v (by decide)
  have hv4 : Γ.dist (v 0) (v 4) = 4 := by
    have h := hP.isGeodesic_of_noBack (by norm_num : 4 ≤ 4)
      (aptPath_noBack (by norm_num) hv 0)
    simpa [GPath.IsGeodesic, a0apt, a4apt] using h
  let O : SubMulAction ↥Q V :=
    { carrier := {y : V | Γ.dist (v 0) y = 4}
      smul_mem' := fun q y hy => by
        have hd := GPath.dist_smul hP.connected (q : H) (v 0) y
        rw [hQfix q, hy] at hd
        exact hd }
  haveI : Fintype O :=
    Fintype.ofInjective (fun y : O => (y : V)) (by
      intro a b h
      exact Subtype.ext h)
  have hsmul_val : ∀ (q : ↥Q) (y : O), ((q • y : O) : V) = (q : H) • (y : V) := by
    intro q y
    rw [SubMulAction.val_smul, Subgroup.smul_def]
  have htrans : ∀ x x' : O, ∃ q : ↥Q, q • x = x' := by
    intro x x'
    obtain ⟨gx, hgxE, hgx⟩ := exists_mem_elationGroup_smul_eq hP hT hM v hv x.2
    obtain ⟨gx', hgx'E, hgx'⟩ := exists_mem_elationGroup_smul_eq hP hT hM v hv x'.2
    have hgxQ : gx ∈ Q := elationGroup_le_whorlGroup v hv hgxE
    have hgx'Q : gx' ∈ Q := elationGroup_le_whorlGroup v hv hgx'E
    let q0 : ↥Q := ⟨gx' * gx⁻¹, Q.mul_mem hgx'Q (Q.inv_mem hgxQ)⟩
    refine ⟨q0, ?_⟩
    apply Subtype.ext
    rw [hsmul_val q0 x]
    dsimp [q0]
    rw [mul_smul]
    have hxinv : (gx⁻¹ : H) • (x : V) = v 4 := by
      have := congrArg (fun y => (gx⁻¹ : H) • y) hgx
      simpa using this.symm
    rw [hxinv, hgx']
  have hfix : ∀ q : ↥Q, q ≠ 1 → Nat.card (MulAction.fixedBy O q) ≤ 1 := by
    intro q hqne
    rw [Finite.card_le_one_iff_subsingleton]
    refine ⟨fun a b => ?_⟩
    by_contra hne
    have hne' : (a : O).1 ≠ (b : O).1 := fun h => hne (Subtype.ext (Subtype.ext h))
    have hqa : (q : H) • (a : O).1 = (a : O).1 := by
      have := congrArg Subtype.val a.2
      rwa [hsmul_val] at this
    have hqb : (q : H) • (b : O).1 = (b : O).1 := by
      have := congrArg Subtype.val b.2
      rwa [hsmul_val] at this
    have hq1 : (q : H) = 1 :=
      eq_one_of_mem_whorlGroup_of_fix_two hP hT c hdeg hst hv0 hspan q.2
        (a : O).2 (b : O).2 hne' hqa hqb
    exact hqne (Subtype.ext hq1)
  haveI : Nonempty O := ⟨⟨v 4, hv4⟩⟩
  have hF0card : Nat.card {q : ↥Q // q ≠ 1 ∧ ∀ x : O, q • x ≠ x} =
      Fintype.card O - 1 :=
    card_fixedPointFree htrans hfix

  let F0 := {q : ↥Q // q ≠ 1 ∧ ∀ x : ↥O, q • x ≠ x}
  have hcardEO : Fintype.card ↥E = Fintype.card ↥O := by
    let fEO : ↥E → ↥O := fun e =>
      ⟨(e : H) • v 4, by
        have heQ : (e : H) ∈ Q := elationGroup_le_whorlGroup v hv e.2
        have hfix0 : (e : H) • v 0 = v 0 := whorlGroup_fix_self hP hT heQ
        have hd := GPath.dist_smul hP.connected (e : H) (v 0) (v 4)
        rw [hfix0, hv4] at hd
        exact hd⟩
    have hinj : Function.Injective fEO := by
      intro e1 e2 h
      obtain ⟨g0, -, huniq⟩ := existsUnique_elationGroup hP hT hM v hv (fEO e1).2
      have h1 : (e1 : H) • v 4 = (fEO e1 : V) := rfl
      have h2 : (e2 : H) • v 4 = (fEO e1 : V) := congrArg Subtype.val h.symm
      exact (huniq e1 h1).trans (huniq e2 h2).symm
    have hsurj : Function.Surjective fEO := by
      intro x
      obtain ⟨e, he, -⟩ := existsUnique_elationGroup hP hT hM v hv x.2
      exact ⟨e, Subtype.ext he⟩
    exact Fintype.card_congr (Equiv.ofBijective fEO ⟨hinj, hsurj⟩)
  let SE := {e : ↥E // e ≠ 1}
  have hcardSE : Nat.card SE = Fintype.card ↥E - 1 := by
    dsimp [SE]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hfilter : (Finset.univ.filter fun e : ↥E => e ≠ 1) = Finset.univ.erase 1 := by
      ext e
      simp [Finset.mem_erase]
    rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ]
  let toF0 : SE → F0 := fun e =>
    ⟨⟨(e.1 : H), elationGroup_le_whorlGroup v hv e.1.2⟩, by
      refine ⟨?_, ?_⟩
      · intro hq
        apply e.2
        have hqH : (e.1 : H) = 1 := by
          have := congrArg (fun q : ↥Q => (q : H)) hq
          simpa using this
        exact Subtype.ext hqH
      · intro x hx
        have hxV : (e.1 : H) • (x : V) = (x : V) := by
          have := congrArg Subtype.val hx
          rwa [hsmul_val] at this
        obtain ⟨e0, he0, -⟩ := existsUnique_elationGroup hP hT hM v hv x.2
        have hfix : ((e0⁻¹ * e.1 * e0 : ↥E) : H) • v 4 = v 4 := by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
          rw [mul_smul, mul_smul, he0, hxV]
          have hxinv : (e0⁻¹ : H) • (x : V) = v 4 := by
            have := congrArg (fun y => (e0⁻¹ : H) • y) he0
            simpa using this.symm
          rw [hxinv]
        have h1 : (e0⁻¹ * e.1 * e0 : ↥E) = 1 := by
          obtain ⟨w0, -, huniq⟩ := existsUnique_elationGroup hP hT hM v hv hv4
          exact (huniq _ hfix).trans (huniq 1 (by simp)).symm
        have he1 : e.1 = 1 := by
          have := congrArg (fun z : ↥E => (e0 : ↥E) * z * e0⁻¹) h1
          simpa [mul_assoc] using this
        exact e.2 he1⟩
  have htoF0_inj : Function.Injective toF0 := by
    intro e1 e2 h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : F0 => (z.1.1 : H)) h
  have hcardSEF0 : Fintype.card SE = Fintype.card F0 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    rw [hcardSE, hF0card, hcardEO]
  have hbij : Function.Bijective toF0 :=
    (Fintype.bijective_iff_injective_and_card toF0).mpr ⟨htoF0_inj, hcardSEF0⟩
  intro r hr
  by_cases hr1 : r = 1
  · rw [hr1]
    exact E.one_mem
  · have hrQ : r ∈ Q := (rootGroup_le_whorlGroup_of_mem v (p := p) hp0) hr
    have hqne : (⟨r, hrQ⟩ : ↥Q) ≠ 1 := by
      intro hq
      have hqH : r = 1 := by
        have := congrArg (fun q : ↥Q => (q : H)) hq
        simpa using this
      exact hr1 hqH
    have hqfree : ∀ x : ↥O, (⟨r, hrQ⟩ : ↥Q) • x ≠ x := by
      intro x hx
      have hxV : r • (x : V) = (x : V) := by
        have := congrArg Subtype.val hx
        rwa [hsmul_val] at this
      exact hr1 (eq_one_of_mem_rootGroup_of_fix_opposite_of_mem (p := p) v hP hT hp hp0 hr x.2 hxV)
    let q : F0 := ⟨⟨r, hrQ⟩, ⟨hqne, hqfree⟩⟩
    obtain ⟨e, he⟩ := hbij.2 q
    have hEr : (e.1 : H) = r := congrArg (fun z : F0 => (z.1.1 : H)) he
    rw [← hEr]
    exact e.1.2

end CFSG.Geometry.GeneralizedQuadrangles
