module

public import CFSG.CGT.Stroth77.Stroth31CaseProofs

public section

namespace CFSG.CGT.Stroth77

open scoped commutatorElement IsMulCommutative

section WeakClosure

variable {S : Type*} [Group S] {B : Subgroup S} {τ : StrothTypeIndex}

theorem StrothWeakTypeData.closure_c_a_b (D : StrothWeakTypeData B τ) :
    Subgroup.closure ({(D.c : S), (D.a : S), (D.b : S)} : Set S) = B := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact D.c.2
    · exact D.a.2
    · exact D.b.2
  · intro x hx
    let xB : B := ⟨x, hx⟩
    let y : Torus τ.k := D.e (Additive.ofMul xB)
    choose z hz using fun i : Fin 3 => ZMod.intCast_surjective (y i)
    have hc : D.e (Additive.ofMul D.c) = gen τ.k 0 := by
      simp [StrothWeakTypeData.c, Torus.c, gen, ofMul_toMul]
    have ha : D.e (Additive.ofMul D.a) = gen τ.k 1 := by
      simp [StrothWeakTypeData.a, Torus.a, gen, ofMul_toMul]
    have hb : D.e (Additive.ofMul D.b) = gen τ.k 2 := by
      simp [StrothWeakTypeData.b, Torus.b, gen, ofMul_toMul]
    have hy : y = z 0 • gen τ.k 0 + z 1 • gen τ.k 1 + z 2 • gen τ.k 2 := by
      funext i
      fin_cases i <;>
        simp [gen, Pi.single_eq_same, Pi.single_eq_of_ne, hz, Pi.add_apply, Pi.smul_apply]
    have hx' : xB = D.c ^ (z 0) * D.a ^ (z 1) * D.b ^ (z 2) := by
      apply Additive.ofMul.injective
      apply D.e.injective
      rw [show D.e (Additive.ofMul xB) = y from rfl, hy]
      simp only [ofMul_mul, ofMul_zpow, map_add, map_zsmul]
      rw [hc, ha, hb]
    have hx'' : x = (D.c : S) ^ (z 0) * (D.a : S) ^ (z 1) * (D.b : S) ^ (z 2) := by
      simpa using congrArg (fun z : B => (z : S)) hx'
    rw [hx'']
    let cl : Subgroup S := Subgroup.closure ({(D.c : S), (D.a : S), (D.b : S)} : Set S)
    have hc : (D.c : S) ∈ cl := Subgroup.subset_closure (by simp)
    have ha : (D.a : S) ∈ cl := Subgroup.subset_closure (by simp)
    have hb : (D.b : S) ∈ cl := Subgroup.subset_closure (by simp)
    exact cl.mul_mem (cl.mul_mem (cl.zpow_mem hc _) (cl.zpow_mem ha _)) (cl.zpow_mem hb _)

end WeakClosure

variable {G : Type*} [Group G] [Finite G]

theorem stroth31_hfix {X : StrothAmbient G} {Z : StrothDatum X}
    {C : Subgroup G} {r : G}
    (hCR : C ≤ strothR X Z.D) (hrC : r ∈ C) (hrD : r ∉ Z.D)
    (hc : strothConj r (Z.dataD.c : G) = (Z.dataD.c : G))
    (ha : strothConj r (Z.dataD.a : G) = (Z.dataD.a : G))
    (hb : strothConj r (Z.dataD.b : G) = (Z.dataD.b : G)) : False := by
  have hrS : r ∈ (X.S : Subgroup G) := le_sylow_of_le_strothR hCR hrC
  refine hrD (mem_D_of_forall_strothConj_eq_self (X := X) (Z := Z) hrS ?_)
  intro x hx
  rw [← Z.dataD.closure_c_a_b] at hx
  refine Subgroup.closure_induction (p := fun x _ => strothConj r x = x) ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    exacts [hc, ha, hb]
  · exact strothConj_one r
  · intro y z _ _ hy hz
    rw [strothConj_mul, hy, hz]
  · intro y _ hy
    rw [strothConj_inv, hy]

end CFSG.CGT.Stroth77
