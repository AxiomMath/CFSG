module

public import CFSG.HardMathSupport.RichardWeiss.Proving.A5PairThreeCycle

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.CGT.PushingUpLit.CGT6

theorem pairGen_map_conj_right {S : Type} [Group S] (Y : Subgroup S) (x g h : S) :
    pairGen (Y.map (MulAut.conj x).toMonoidHom) g h = pairGen Y (g * x) (h * x) := by
  have key : ∀ k : S, (Y.map (MulAut.conj x).toMonoidHom).map (MulAut.conj k).toMonoidHom =
      Y.map (MulAut.conj (k * x)).toMonoidHom := by
    intro k
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  simp only [pairGen, key]

theorem hasA5Pair_map_conj_iff {S : Type} [Group S] (Y : Subgroup S) (x : S) :
    (∃ g h : S, Nonempty (↥(pairGen (Y.map (MulAut.conj x).toMonoidHom) g h) ≃*
      alternatingGroup (Fin 5))) ↔
    ∃ g h : S, Nonempty (↥(pairGen Y g h) ≃* alternatingGroup (Fin 5)) := by
  constructor
  · rintro ⟨g, h, hgh⟩
    exact ⟨g * x, h * x, by rwa [pairGen_map_conj_right] at hgh⟩
  · rintro ⟨g, h, hgh⟩
    have eg : g * x⁻¹ * x = g := by group
    have eh : h * x⁻¹ * x = h := by group
    refine ⟨g * x⁻¹, h * x⁻¹, ?_⟩
    rw [pairGen_map_conj_right, eg, eh]
    exact hgh

theorem hasA5Pair_of_carmichael_triple {S : Type} [Group S] (Y : Subgroup S) (a : Fin 3 → S)
    (h3 : ∀ i, a i ^ 3 = 1) (h2 : ∀ i j, i ≠ j → (a i * a j) ^ 2 = 1) (ha0 : a 0 ≠ 1)
    (hY : ∃ x : S, Subgroup.zpowers (a 0) = Y.map (MulAut.conj x).toMonoidHom) :
    ∃ g h : S, Nonempty (↥(pairGen Y g h) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨x, hx⟩ := hY
  have key := hasA5Pair_zpowers_of_carmichael a h3 h2 ha0
  rw [hx] at key
  exact (hasA5Pair_map_conj_iff Y x).mp key

end CFSG.HardMathSupport.RichardWeiss.Proving

end
