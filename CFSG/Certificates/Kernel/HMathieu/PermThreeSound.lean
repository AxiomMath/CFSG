module

public import Certificates.Data.Kernel.HMathieu.PermThree
public import CFSG.Certificates.Kernel.HMathieu.BfsSound
public import CFSG.Quasithin.Background.HNPrimeMathieuInputs

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M22Hat
  CFSG.Quasithin.H.MathieuLat

theorem comp24_unpk (p : Nat) {q : Nat} (hq : vpK q = true) :
    comp24 (unpk p) (unpk q) = unpk (pc24 p q) := by
  apply Array.ext (by simp [comp24, size_unpk])
  intro i h1 h2
  have hi : i < 24 := by simpa [size_unpk] using h2
  rw [← getElem!_pos (unpk (pc24 p q)) i h2, unpk_get _ hi, pg_pc24 p q hi]
  simp only [comp24, Array.getElem_ofFn]
  rw [unpk_get q hi, unpk_get p ((vpK_spec hq).2 i hi)]

theorem contains_unpk {E : List Nat} {z : Nat} (h : E.contains z = true) :
    (E.map unpk).toArray.contains (unpk z) = true := by
  rw [List.contains_toArray, List.contains_iff_mem]
  exact List.mem_map_of_mem (List.contains_iff_mem.1 h)

theorem permThreeOK_of_K {T : PT 24} {E : List Nat} {a : Array Nat} {y w1 w2 : Nat}
    (hE : T.elems = (E.map unpk).toArray) (hn : T.n = T.elems.size)
    (hv : ∀ e ∈ E, vpK e = true) (ha : a = unpk y) (h1 : invArr a = unpk w1)
    (h2 : pow24 (invArr a) 2 = unpk w2) (hw1 : vpK w1 = true) (hw2 : vpK w2 = true)
    (h3 : pow24 a 3 = id24) (hne : a ≠ id24) (hK : permThreeK E y w1 w2 = true) :
    permThreeOK T a = true := by
  unfold permThreeOK
  rw [h2, h1]
  subst ha
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨h3, hne⟩, fun p hp => ?_⟩
  have hpE : p < E.length := by
    rw [hn, hE] at hp
    simpa using hp
  have hget : T.elems[p]! = unpk E[p] := by
    rw [hE, getElem!_pos _ p (by simpa using hpE)]
    simp
  have hK' := List.all_eq_true.1 hK _ (List.getElem_mem hpE)
  rw [hget, comp24_unpk _ (hv _ (List.getElem_mem hpE)), comp24_unpk _ hw1, comp24_unpk _ hw2,
    hE]
  simp only [Bool.or_eq_true] at hK' ⊢
  rcases hK' with (h | h) | h
  · exact Or.inl (Or.inl (contains_unpk h))
  · exact Or.inl (Or.inr (contains_unpk h))
  · exact Or.inr (contains_unpk h)

end CFSG.KC.HMathieu

end
