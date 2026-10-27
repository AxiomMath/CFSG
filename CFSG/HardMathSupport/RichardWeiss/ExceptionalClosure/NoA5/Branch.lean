module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.NoA5.Pure
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.OfAlternating
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.Setup
public import CFSG.HardMathSupport.RichardWeiss.Proving.A5PairCarmichaelTriple
public import CFSG.HardMathSupport.RichardWeiss.Proving.ConjugateGeneration
public import CFSG.HardMathSupport.RichardWeiss.Proving.ConjugateGenerator

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.CGT.PushingUpLit.CGT6 CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation
open CFSG.HardMathSupport.RichardWeiss.Proving

variable {S : Type} [Group S]

theorem map_conj_conj_aux (Y : Subgroup S) (k g1 : S) :
    (Y.map (MulAut.conj g1).toMonoidHom).map (MulAut.conj k).toMonoidHom =
      Y.map (MulAut.conj (k * g1)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

theorem orderOf_three_of_dGen {Y : Subgroup S} (hY : Nat.card Y = 3) {p : S} (hp : IsDGen Y p) :
    orderOf p = 3 := by
  have h3 := hp.cube hY
  have h1 := hp.ne_one hY
  exact orderOf_eq_prime h3 h1

theorem pair_of_noA5 [Finite S] {Y : Subgroup S} (hY : Nat.card Y = 3)
    (hpair : ∀ g h : S, IsZ3E9A4A5 ↥(pairGen Y g h)) (hno : ¬ HasA5Pair Y) {p q : S}
    (hp : IsDGen Y p) (hq : IsDGen Y q) :
    p * q = q * p ∨ (p * q) ^ 2 = 1 ∨ (p * q⁻¹) ^ 2 = 1 := by
  obtain ⟨g, hg⟩ := hp
  obtain ⟨h, hh⟩ := hq
  have hpo := orderOf_three_of_dGen hY ⟨g, hg⟩
  have hqo := orderOf_three_of_dGen hY ⟨h, hh⟩
  by_cases hzq : Subgroup.zpowers p = Subgroup.zpowers q
  · left
    have hqmem : q ∈ Subgroup.zpowers p := hzq ▸ Subgroup.mem_zpowers q
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hqmem
    exact ((Commute.refl p).zpow_right k).eq
  · rcases pairType_of_conjugates (hpair g h) hpo hqo hzq hg.symm hh.symm with
      ⟨-, hc⟩ | ⟨-, hiff⟩ | ⟨hA5, -⟩
    · exact Or.inl hc
    · by_cases h1 : (p * q) ^ 2 = 1
      · exact Or.inr (Or.inl h1)
      · refine Or.inr (Or.inr ?_)
        by_contra h2
        exact h1 (hiff.mpr h2)
    · exact (hno ⟨g, h, hA5⟩).elim

theorem no_tri_of_noA5 [Finite S] {Y : Subgroup S} (hY : Nat.card Y = 3)
    (hno : ¬ HasA5Pair Y) {x y z : S} (hx : IsDGen Y x) (hy : IsDGen Y y) (hz : IsDGen Y z)
    (hxy : (x * y) ^ 2 = 1) (hxz : (x * z) ^ 2 = 1) (hyz : (y * z) ^ 2 = 1) : False := by
  let a : Fin 3 → S := ![x, y, z]
  have h3 : ∀ i, a i ^ 3 = 1 := by
    intro i
    fin_cases i
    · exact hx.cube hY
    · exact hy.cube hY
    · exact hz.cube hY
  have h2 : ∀ i j, i ≠ j → (a i * a j) ^ 2 = 1 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | skip
    · exact hxy
    · exact hxz
    · exact NoA5.sq_comm hxy
    · exact hyz
    · exact NoA5.sq_comm hxz
    · exact NoA5.sq_comm hyz
  have hne := hx.ne_one hY
  obtain ⟨g, hg⟩ := hx
  exact hno (hasA5Pair_of_carmichael_triple Y a h3 h2 hne ⟨g, hg⟩)

theorem noA5Branch : NoA5Branch := by
  intro S _ _ hS hnab Y hY hnc hpair hno
  have := hS
  obtain ⟨a, ha3, hag⟩ := exists_gen_map_conj hY 1
  have hEa : IsDGen Y a := ⟨1, hag.symm⟩
  have hE : NoA5.PureClass (IsDGen Y) :=
    { cube := fun p hp => hp.cube hY
      inv := fun p hp => hp.inv
      conj := fun g p hp => hp.conj g
      trans := by
        intro p q hp hq
        obtain ⟨g1, h1⟩ := hp
        obtain ⟨g2, h2⟩ := hq
        have hpD : IsDGen Y p := ⟨g1, h1⟩
        have hqD : IsDGen Y q := ⟨g2, h2⟩
        set k : S := g2 * g1⁻¹ with hk
        have hkD : IsDGen Y (k * p * k⁻¹) := by simpa using hpD.conj k⁻¹
        have hz : Subgroup.zpowers q = Subgroup.zpowers (k * p * k⁻¹) := by
          have e1 : (Subgroup.zpowers p).map (MulAut.conj k).toMonoidHom =
              Subgroup.zpowers (k * p * k⁻¹) := by
            rw [MonoidHom.map_zpowers]; simp [MulAut.conj_apply]
          have hkg : k * g1 = g2 := by simp [hk]
          rw [← e1, h1, map_conj_conj_aux, hkg, ← h2]
        have := (zpowers_eq_zpowers_iff_of_orderOf_three (orderOf_three_of_dGen hY hkD)
          (orderOf_three_of_dGen hY hqD)).mp hz.symm
        refine ⟨g1 * g2⁻¹, ?_⟩
        rcases this with h | h
        · left; rw [h]; simp [hk, mul_assoc]
        · right; rw [h]; simp [hk, mul_assoc]
      pair := fun p q hp hq => pair_of_noA5 hY hpair hno hp hq
      no_tri := fun x y z hx hy hz => no_tri_of_noA5 hY hno hx hy hz }
  have hcl : Subgroup.closure {x | IsDGen Y x} = ⊤ := by
    rw [eq_top_iff, ← conjClosure_eq_top_of_normalClosure hnc]
    unfold conjClosure
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hx
    obtain ⟨c, -, hcg⟩ := exists_gen_map_conj hY g
    have hcE : c ∈ {x | IsDGen Y x} := ⟨g, hcg.symm⟩
    have hx' : x ∈ Y.map (MulAut.conj g).toMonoidHom := hg
    rw [hcg] at hx'
    exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure hcE)) hx'
  exact hE.false_of_simple hcl hnab hEa

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
