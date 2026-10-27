module

public import CFSG.CGT.T75JM.N6Quot
public import CFSG.CGT.T75JM.N6A6
public import CFSG.CGT.T75JM.N6Split

public section

namespace CFSG.CGT.T75JM

open Equiv

variable {G : Type*} [Group G] {T : Subgroup G}

theorem evalG_wordR {H : Type*} [Group H] (g h : H) :
    evalG g h wordR1 = g * g ∧ evalG g h wordR2 = h ^ 4 ∧ evalG g h wordR3 = (g * h) ^ 5 ∧
      evalG g h wordR4 = (g * h * h) ^ 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [wordR1, evalG_flatten_replicate]; simp [evalG, pow_two]
  · rw [wordR2, evalG_flatten_replicate]; simp [evalG, pow_succ, mul_assoc]
  · rw [wordR3, evalG_flatten_replicate]; simp [evalG]
  · rw [wordR4, evalG_flatten_replicate]; simp [evalG, mul_assoc]

theorem evalG_map {H K : Type*} [Group H] [Group K] (f : H →* K) (g h : H) (w : List ℕ) :
    evalG (f g) (f h) w = f (evalG g h w) := by
  induction w with
  | nil => simp [evalG]
  | cons l w ih =>
    simp only [evalG, map_mul, ih]
    by_cases hl : l = 0 <;> simp [hl]

theorem evalG_coe {H : Type*} [Group H] (S : Subgroup H) (g h : S) (w : List ℕ) :
    ((evalG g h w : S) : H) = evalG (g : H) (h : H) w := by
  induction w with
  | nil => simp [evalG]
  | cons l w ih =>
    simp only [evalG, Subgroup.coe_mul, ih]
    by_cases hl : l = 0 <;> simp [hl]

theorem closure_pair_eq_top' {M : Type*} [Group M] {K : Subgroup M} {x y : M}
    (hK : K = Subgroup.closure {x, y}) (hx : x ∈ K) (hy : y ∈ K) :
    Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set K) = ⊤ := by
  subst hK
  refine Eq.trans ?_ (Subgroup.closure_closure_coe_preimage (k := {x, y}))
  congr 1
  ext ⟨g, hg⟩
  simp [Subtype.ext_iff]

theorem closure_pair_symm {M K : Type*} [Group M] [Group K] (φ : M ≃* K) (x y : K)
    (h : Subgroup.closure ({x, y} : Set K) = ⊤) :
    Subgroup.closure ({φ.symm x, φ.symm y} : Set M) = ⊤ := by
  have := MonoidHom.map_closure φ.symm.toMonoidHom ({x, y} : Set K)
  rw [h] at this
  have htop : Subgroup.map φ.symm.toMonoidHom ⊤ = ⊤ := by
    ext g; simp only [Subgroup.mem_map, Subgroup.mem_top, iff_true]
    exact ⟨φ g, trivial, by simp⟩
  rw [htop] at this
  rw [this]
  simp

theorem a6_closure_twist (hn : A6Nodup) :
    Subgroup.closure ({a6x, a6twist} : Set (Perm (Fin 6))) = alternatingGroup (Fin 6) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact a6x_mem
    · exact a6twist_mem
  · rw [← a6_closure hn, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · rw [a6y_eq]
      exact evalG_mem_closure _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)) _

section Branch

variable (c : Coords T)

theorem colsOf_lt (g : Subgroup.normalizer (T : Set G)) (i : Fin 4) : (colsOf c g).col i < 16 := by
  fin_cases i <;> exact c.lt _

theorem colsQ_lt (q : NQ T) (i : Fin 4) : (colsQ c q).col i < 16 := colsOf_lt c _ i

theorem branch_data (hC : Subgroup.centralizer (T : Set G) = T)
    (φ : NQ T ≃* alternatingGroup (Fin 6)) (hmod : ModClass) (hnodup : A6Nodup) :
    ∃ a b : NQ T, (evalG a b wordR1 = 1 ∧ evalG a b wordR2 = 1 ∧ evalG a b wordR3 = 1 ∧
        evalG a b wordR4 = 1) ∧
      Subgroup.closure ({a, b} : Set (NQ T)) = ⊤ ∧ EquivC (colsQ c a) (colsQ c b) := by
  set ψ : NQ T →* Perm (Fin 6) := (alternatingGroup (Fin 6)).subtype.comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ :=
    (alternatingGroup (Fin 6)).subtype_injective.comp φ.injective
  set qx : NQ T := φ.symm ⟨a6x, a6x_mem⟩ with hqx
  set qy : NQ T := φ.symm ⟨a6y, a6y_mem⟩ with hqy
  set qt : NQ T := φ.symm ⟨a6twist, a6twist_mem⟩ with hqt
  have ψx : ψ qx = a6x := by simp [hψ, hqx]
  have ψy : ψ qy = a6y := by simp [hψ, hqy]
  have ψt : ψ qt = a6twist := by simp [hψ, hqt]
  have relQ : ∀ (g h : NQ T) (u v r : Perm (Fin 6)) (w : List ℕ), ψ g = u → ψ h = v →
      evalG u v w = r → ψ (evalG g h w) = r := by
    intro g h u v r w hg hh hw
    rw [← evalG_map, hg, hh, hw]
  have hR : evalG qx qy wordR1 = 1 ∧ evalG qx qy wordR2 = 1 ∧ evalG qx qy wordR3 = 1 ∧
      evalG qx qy wordR4 = 1 := by
    obtain ⟨r1, r2, r3, r4⟩ := a6_rel
    obtain ⟨e1, e2, e3, e4⟩ := evalG_wordR a6x a6y
    refine ⟨hψinj ?_, hψinj ?_, hψinj ?_, hψinj ?_⟩
    · rw [relQ qx qy a6x a6y _ _ ψx ψy (e1.trans r1), map_one]
    · rw [relQ qx qy a6x a6y _ _ ψx ψy (e2.trans r2), map_one]
    · rw [relQ qx qy a6x a6y _ _ ψx ψy (e3.trans r3), map_one]
    · rw [relQ qx qy a6x a6y _ _ ψx ψy (e4.trans r4), map_one]
  have hrel : RelC (colsQ c qx) (colsQ c qy) := by
    obtain ⟨h1, h2, h3, h4⟩ := hR
    obtain ⟨e1, e2, e3, e4⟩ := evalG_wordR qx qy
    rw [e1] at h1; rw [e2] at h2; rw [e3] at h3; rw [e4, mul_assoc] at h4
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← colsQ_mul, h1, colsQ_one]
    · intro hX
      have := eq_one_of_colsQ c hC qx hX
      have h' : ψ qx = 1 := by rw [this, map_one]
      rw [ψx] at h'
      exact a6x_ne_one h'
    · rw [← colsQ_pow, h2, colsQ_one]
    · rw [← colsQ_mul, ← colsQ_pow, h3, colsQ_one]
    · rw [← colsQ_mul, ← colsQ_mul, ← colsQ_pow, h4, colsQ_one]
  rcases hmod _ _ (colsQ_lt c qx) (colsQ_lt c qy) hrel with hA | hB
  · refine ⟨qx, qy, hR, ?_, hA⟩
    exact closure_pair_symm φ _ _ (closure_pair_eq_top' (a6_closure hnodup).symm a6x_mem a6y_mem)
  ·
    have hqt' : qt = evalG qx qy twistWord := by
      apply hψinj
      rw [ψt, a6twist, ← evalG_map, ψx, ψy]
    obtain ⟨hrt1, hrt2, hrt3, hrt4⟩ := a6twist_rel
    obtain ⟨e1, e2, e3, e4⟩ := evalG_wordR a6x a6twist
    have hRt : evalG qx qt wordR1 = 1 ∧ evalG qx qt wordR2 = 1 ∧ evalG qx qt wordR3 = 1 ∧
        evalG qx qt wordR4 = 1 := by
      refine ⟨hψinj ?_, hψinj ?_, hψinj ?_, hψinj ?_⟩
      · rw [relQ qx qt a6x a6twist _ _ ψx ψt (e1.trans hrt1), map_one]
      · rw [relQ qx qt a6x a6twist _ _ ψx ψt (e2.trans hrt2), map_one]
      · rw [relQ qx qt a6x a6twist _ _ ψx ψt (e3.trans hrt3), map_one]
      · rw [relQ qx qt a6x a6twist _ _ ψx ψt (e4.trans hrt4), map_one]
    refine ⟨qx, qt, hRt, ?_, ?_⟩
    · exact closure_pair_symm φ _ _
        (closure_pair_eq_top' (a6_closure_twist hnodup).symm a6x_mem a6twist_mem)
    · rw [hqt', colsQ_evalG]
      exact hB

end Branch

end CFSG.CGT.T75JM
