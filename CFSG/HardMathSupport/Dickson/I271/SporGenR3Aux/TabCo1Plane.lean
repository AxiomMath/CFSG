module

public import CFSG.Sporadic.Co1Block.XFix
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Census
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1FiveA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1FiveC
public import Certificates.Certificate17328
public import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Block CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F CFSG.Open
  CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Dickson.I271 Matrix

section Burnside

theorem sq_dvd_card_of_noncyclic {G : Type} [Group G] {p : ℕ} (hp : p.Prime) (E : Subgroup G)
    [Finite ↥E] (hE : ∀ x ∈ E, x ^ p = 1) (hnc : ¬ IsCyclic ↥E) : p ^ 2 ∣ Nat.card ↥E := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p ↥E := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE x x.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hpg
  rcases n with _ | _ | n
  · exfalso
    apply hnc
    haveI : Subsingleton ↥E := (Nat.card_eq_one_iff_unique.1 (by simpa using hn)).1
    exact isCyclic_of_subsingleton
  · exact absurd (isCyclic_of_prime_card (by simpa using hn)) hnc
  · rw [hn]
    exact pow_dvd_pow p (by omega)

theorem card_dvd_sub_of_fixedBy {E X : Type} [Group E] [Finite E] [MulAction E X] [Finite X]
    {N f : ℕ} (hN : Nat.card X = N) (hfN : f ≤ N)
    (hf : ∀ g : E, g ≠ 1 → Nat.card ↥(MulAction.fixedBy X g) = f) : Nat.card E ∣ N - f := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Fintype X := Fintype.ofFinite X
  haveI : ∀ g : E, Fintype ↥(MulAction.fixedBy X g) := fun g => Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient E X) := Fintype.ofFinite _
  have key := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group E X
  simp only [Fintype.card_eq_nat_card] at key
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : E))] at key
  have h1 : Nat.card ↥(MulAction.fixedBy X (1 : E)) = N := by
    rw [MulAction.fixedBy_one_eq_univ, Nat.card_univ, hN]
  have h2 : ∑ g ∈ Finset.univ.erase (1 : E), Nat.card ↥(MulAction.fixedBy X g) =
      (Nat.card E - 1) * f := by
    rw [Finset.sum_congr rfl (fun g hg => hf g (Finset.ne_of_mem_erase hg)), Finset.sum_const,
      smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
  rw [h1, h2] at key
  have hn : 0 < Nat.card E := Nat.card_pos
  obtain ⟨o, ho⟩ : ∃ o, o = Nat.card (MulAction.orbitRel.Quotient E X) := ⟨_, rfl⟩
  rw [← ho] at key
  generalize Nat.card E = n at key hn ⊢
  rcases n with _ | m
  · omega
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hfN
    have e1 : f + a - f = a := by omega
    have e2 : m + 1 - 1 = m := by omega
    rw [e1]
    rw [e2] at key
    have h3 : (m + 1) * f + a = o * (m + 1) := by linarith
    exact (Nat.dvd_add_right (dvd_mul_right (m + 1) f)).1 (h3 ▸ dvd_mul_left (m + 1) o)

theorem isCyclic_of_fixed_count {G X : Type} [Group G] [MulAction G X] [Finite X] {p N f : ℕ}
    (hp : p.Prime) (E : Subgroup G) [Finite ↥E] (hE : ∀ x ∈ E, x ^ p = 1)
    (hN : Nat.card X = N) (hfN : f ≤ N) (hnd : ¬ p ^ 2 ∣ N - f)
    (hf : ∀ g ∈ E, g ≠ 1 → Nat.card ↥(MulAction.fixedBy X g) = f) : IsCyclic ↥E := by
  by_contra hnc
  have h1 := sq_dvd_card_of_noncyclic hp E hE hnc
  have h2 := card_dvd_sub_of_fixedBy (E := ↥E) (X := X) hN hfN
    (fun g hg => hf g g.2 (fun h => hg (Subtype.ext h)))
  exact hnd (h1.trans h2)

end Burnside

section Action


@[expose, instance_reducible] noncomputable def xAct' : MulAction ↥GA ↥certX where
  smul g x := ⟨(((g : ↥GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ x.1,
    mulVec_mem_certX g.2 x.2⟩
  one_smul x := Subtype.ext (by
    show (((1 : ↥GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ x.1 = x.1
    rw [Subgroup.coe_one, mulVec_one'])
  mul_smul a b x := Subtype.ext (by
    show (((a * b : ↥GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ x.1 =
      ((a : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
        (((b : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ x.1)
    rw [Subgroup.coe_mul, mulVec_mul'])

attribute [local instance] xAct'

theorem xAct'_smul_val (g : ↥GA) (x : ↥certX) :
    ((g • x : ↥certX) : Vec24) =
      (((g : ↥GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ x.1 := rfl

theorem card_fixedBy_xAct' (g : ↥GA) :
    Nat.card ↥(MulAction.fixedBy ↥certX g) = (xFix ((g : ↥GA) : GL24)).ncard := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, (xAct'_smul_val g x.1).symm.trans
        (congrArg Subtype.val (MulAction.mem_fixedBy.1 x.2))⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, MulAction.mem_fixedBy.2
        (Subtype.ext ((xAct'_smul_val g ⟨y.1, y.2.1⟩).trans y.2.2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Action

section Conj

variable {Q : Type} [Group Q] [Finite Q]

theorem atMostOneCompAt_conj_back {p : ℕ} (hp : p.Prime) {e c : Q}
    (h : AtMostOneCompAt p (c * e * c⁻¹)) : AtMostOneCompAt p e := by
  have h' := AtMostOneCompAt.of_equiv hp (MulAut.conj c⁻¹) h
  have e' : (MulAut.conj c⁻¹) (c * e * c⁻¹) = e := by
    rw [MulAut.conj_apply]
    group
  rwa [e'] at h'

theorem multiShapeAt_conj_back {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T') {e c : Q}
    (h : MultiShapeAt p Good Rk (c * e * c⁻¹)) : MultiShapeAt p Good Rk e := by
  have h' := MultiShapeAt.of_equiv hp hGood hRk (MulAut.conj c⁻¹) h
  have e' : (MulAut.conj c⁻¹) (c * e * c⁻¹) = e := by
    rw [MulAut.conj_apply]
    group
  rwa [e'] at h'

end Conj

section Fix


theorem ncard_fix_fiveB (e c : ↥GA) (hx : MRep repD1 ((c * e * c⁻¹ : ↥GA) : GL24)) :
    (xFix (e : GL24)).ncard = 60 := by
  have h1 := ncard_fix_isConj (x := e) (y := c * e * c⁻¹) (isConj_iff.2 ⟨c, rfl⟩)
  rw [ncard_fix_certX hx,
    (Certificates.certificate17328 : xFixCount certVecs repD1 = 60)] at h1
  exact h1.symm

end Fix

section Plane


attribute [local instance] xAct'

theorem atMostOne_or_fix (hOut : SporadicOuterLeTwo) (hG : GOK) (e : ↥GA) (he : orderOf e = 5) :
    AtMostOneCompAt 5 e ∨ (xFix (e : GL24)).ncard = 60 := by
  haveI : Finite ↥GA := finite_GA
  obtain ⟨c, h0 | h1 | h5⟩ := tabCo1_census hG e he
  · exact Or.inl (atMostOneCompAt_conj_back Nat.prime_five
      (atMostOneCompAt_of_shapeRkAt Nat.prime_five (tabCo1_fiveA hOut _ h0)))
  · exact Or.inr (ncard_fix_fiveB e c h1)
  · exact Or.inl (atMostOneCompAt_conj_back Nat.prime_five
      (atMostOneCompAt_of_pConstrained Nat.prime_five (tabCo1_fiveC _ h5)))

theorem tabCo1_plane (hOut : SporadicOuterLeTwo) (hG : GOK) (E : Subgroup ↥GA)
    (hE : IsElemAbelian 5 E) (hnc : ¬ IsCyclic ↥E) : ∃ e ∈ E, e ≠ 1 ∧ AtMostOneCompAt 5 e := by
  haveI : Finite ↥GA := finite_GA
  haveI : Finite ↥certX := certX_finite.to_subtype
  by_contra hcon
  apply hnc
  refine isCyclic_of_fixed_count (X := ↥certX) (N := 98280) (f := 60) Nat.prime_five E hE.2 ?_
    (by norm_num) (by norm_num) ?_
  · rw [Nat.card_coe_set_eq, ncard_certX]
  · intro g hg hg1
    have he : orderOf g = 5 := orderOf_eq_prime (hE.2 g hg) hg1
    rcases atMostOne_or_fix hOut hG g he with h | h
    · exact absurd ⟨g, hg, hg1, h⟩ hcon
    · rw [card_fixedBy_xAct' g, h]

end Plane

end CFSG.HardMathSupport.Dickson.I271.TabCo1
