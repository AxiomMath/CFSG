module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcBigDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacShape
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE8

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

section Raw

set_option maxRecDepth 100000

theorem k1419e_e6_triple_raw : ∀ c ∈ e6Conn, c.length ≤ 6 →
    (1 ≤ c.length ∧ kacCount Tag.E6 ![1, 2, 2, 3, 2, 1]
      (c.map (idxNode (r := Tag.E6.rank))).toFinset = c.length * (c.length + 1)) ∨
    ∃ x ∈ c, ∃ y ∈ c, ∃ z ∈ c,
      k1419eSoList Tag.E6 (e6ExtVec (idxNode x)) (e6ExtVec (idxNode y)) ∧
      k1419eSoList Tag.E6 (e6ExtVec (idxNode x)) (e6ExtVec (idxNode z)) ∧
      k1419eSoList Tag.E6 (e6ExtVec (idxNode y)) (e6ExtVec (idxNode z)) := by
  decide +kernel

theorem k1419e_e7_triple_raw : ∀ c ∈ e7Conn, c.length ≤ 7 →
    (1 ≤ c.length ∧ kacCount Tag.E7 ![2, 2, 3, 4, 3, 2, 1]
      (c.map (idxNode (r := Tag.E7.rank))).toFinset = c.length * (c.length + 1)) ∨
    ∃ x ∈ c, ∃ y ∈ c, ∃ z ∈ c,
      k1419eSoList Tag.E7 (e7ExtVec (idxNode x)) (e7ExtVec (idxNode y)) ∧
      k1419eSoList Tag.E7 (e7ExtVec (idxNode x)) (e7ExtVec (idxNode z)) ∧
      k1419eSoList Tag.E7 (e7ExtVec (idxNode y)) (e7ExtVec (idxNode z)) := by
  decide +kernel

theorem k1419e_e8_triple_raw : ∀ c ∈ e8Conn, c.length ≤ 8 →
    (1 ≤ c.length ∧ kacCount Tag.E8 ![2, 3, 4, 6, 5, 4, 3, 2]
      (c.map (idxNode (r := Tag.E8.rank))).toFinset = c.length * (c.length + 1)) ∨
    ∃ x ∈ c, ∃ y ∈ c, ∃ z ∈ c,
      k1419eSoList Tag.E8 (e8ExtVec (idxNode x)) (e8ExtVec (idxNode y)) ∧
      k1419eSoList Tag.E8 (e8ExtVec (idxNode x)) (e8ExtVec (idxNode z)) ∧
      k1419eSoList Tag.E8 (e8ExtVec (idxNode y)) (e8ExtVec (idxNode z)) := by
  decide +kernel

end Raw

theorem k1419e_idxNode_mem {r : ℕ} {c : List ℕ} {x : ℕ} (hx : x ∈ c) :
    (idxNode x : Option (Fin r)) ∈
      (((c.map (idxNode (r := r))).toFinset : Finset (Option (Fin r))) :
        Set (Option (Fin r))) :=
  Finset.mem_coe.2 (List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩))

section Nodes


theorem k1419e_hasTriple_of_nodes {τ : Tag} (K : KacData τ) (v : WeylGroup τ)
    {C : Set (Option (Fin τ.rank))} {x y z : Option (Fin τ.rank)} (hx : x ∈ C) (hy : y ∈ C)
    (hz : z ∈ C) (hxy : k1419eStrongOrth τ (K.extRoot x) (K.extRoot y))
    (hxz : k1419eStrongOrth τ (K.extRoot x) (K.extRoot z))
    (hyz : k1419eStrongOrth τ (K.extRoot y) (K.extRoot z)) :
    k1419eHasTriple τ ((fun α => v • α) '' K.rootsOf C) :=
  (show k1419eHasTriple τ (K.rootsOf C) from
    ⟨K.extRoot x, extRoot_mem_rootsOf K hx, K.extRoot y, extRoot_mem_rootsOf K hy,
      K.extRoot z, extRoot_mem_rootsOf K hz, hxy, hxz, hyz⟩).image_smul v

end Nodes

section Dispatch


theorem k1419e_hasTriple_E6 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) :
    k1419eHasTriple Tag.E6 (componentRoots (rootCharHom a) i) := by
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S Nat.prime_three
      (k1419e_natCast_three_ne_zero L) hTp i
  have hncard' : (componentRoots (rootCharHom a) i).ncard = kacCount Tag.E6 ![1, 2, 2, 3, 2, 1]
      (c.map (idxNode (r := Tag.E6.rank))).toFinset := hncard
  rcases k1419e_e6_triple_raw c hc hlen with hA | ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩
  · rw [← hncard', ← hrank] at hA
    exact (hnonA hA).elim
  · rw [hroots]
    rw [← kacE6_extRoot] at hxy hxz hyz
    exact k1419e_hasTriple_of_nodes kacE6 v
      (k1419e_idxNode_mem hx) (k1419e_idxNode_mem hy) (k1419e_idxNode_mem hz)
      hxy.strongOrth hxz.strongOrth hyz.strongOrth

theorem k1419e_hasTriple_E7 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E7 L p₀) {a : Fin Tag.E7.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) :
    k1419eHasTriple Tag.E7 (componentRoots (rootCharHom a) i) := by
  have hTp : rootDiagUnit Tag.E7 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S Nat.prime_three
      (k1419e_natCast_three_ne_zero L) hTp i
  have hncard' : (componentRoots (rootCharHom a) i).ncard = kacCount Tag.E7 ![2, 2, 3, 4, 3, 2, 1]
      (c.map (idxNode (r := Tag.E7.rank))).toFinset := hncard
  rcases k1419e_e7_triple_raw c hc hlen with hA | ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩
  · rw [← hncard', ← hrank] at hA
    exact (hnonA hA).elim
  · rw [hroots]
    rw [← kacE7_extRoot] at hxy hxz hyz
    exact k1419e_hasTriple_of_nodes kacE7 v
      (k1419e_idxNode_mem hx) (k1419e_idxNode_mem hy) (k1419e_idxNode_mem hz)
      hxy.strongOrth hxz.strongOrth hyz.strongOrth

theorem k1419e_hasTriple_E8 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E8 L p₀) {a : Fin Tag.E8.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) :
    k1419eHasTriple Tag.E8 (componentRoots (rootCharHom a) i) := by
  have hTp : rootDiagUnit Tag.E8 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S Nat.prime_three
      (k1419e_natCast_three_ne_zero L) hTp i
  have hncard' : (componentRoots (rootCharHom a) i).ncard =
      kacCount Tag.E8 ![2, 3, 4, 6, 5, 4, 3, 2]
        (c.map (idxNode (r := Tag.E8.rank))).toFinset := hncard
  rcases k1419e_e8_triple_raw c hc hlen with hA | ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩
  · rw [← hncard', ← hrank] at hA
    exact (hnonA hA).elim
  · rw [hroots]
    rw [← kacE8_extRoot] at hxy hxz hyz
    exact k1419e_hasTriple_of_nodes kacE8 v
      (k1419e_idxNode_mem hx) (k1419e_idxNode_mem hy) (k1419e_idxNode_mem hz)
      hxy.strongOrth hxz.strongOrth hyz.strongOrth

end Dispatch

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
