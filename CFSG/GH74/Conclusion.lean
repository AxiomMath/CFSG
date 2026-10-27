module

public import CFSG.GH74.Defs

public section

namespace CFSG.GH74

open Subgroup Blueprint Assembly.LowTwoRank

@[expose] def GH74Conclusion (G : Type) [Group G] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
    (LieModel G .G2 0 p f ∨ LieModel G .trialityD4 0 p f)) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel G .PSp 2 p f) ∨
  (∃ f : ℕ, LieModel G .twistedG2 0 3 f) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 1 ∧ LieModel G .PSL 4 p f) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 7 ∧ LieModel G .PSU 4 p f) ∨
  (∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧ LieModel G .PSL 5 p f) ∨
  (∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧ LieModel G .PSU 5 p f) ∨
  (LieModel G .PSL 2 2 3 ∨ LieModel G .PSL 2 2 4 ∨ LieModel G .PSL 3 2 2 ∨
    LieModel G .twistedB2 0 2 3) ∨
  (∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
  (NativeSporadic.IsSporadic G .M12 ∨ NativeSporadic.IsSporadic G .M22 ∨
    NativeSporadic.IsSporadic G .M23 ∨ NativeSporadic.IsSporadic G .J1 ∨
    NativeSporadic.IsSporadic G .J2 ∨ NativeSporadic.IsSporadic G .J3 ∨
    NativeSporadic.IsSporadic G .McL ∨ NativeSporadic.IsSporadic G .Ly)

@[expose] def GH74Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → GH74Conclusion G

namespace GH74Conclusion

variable {G : Type} [Group G]

theorem of_eight (h : LieModel G .PSL 2 2 3 ∨ LieModel G .PSL 2 2 4 ∨ LieModel G .PSL 3 2 2 ∨
    LieModel G .twistedB2 0 2 3) : GH74Conclusion G :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h

theorem of_nine (h : ∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) :
    GH74Conclusion G :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h

theorem of_ten (h : NativeSporadic.IsSporadic G .M12 ∨ NativeSporadic.IsSporadic G .M22 ∨
    NativeSporadic.IsSporadic G .M23 ∨ NativeSporadic.IsSporadic G .J1 ∨
    NativeSporadic.IsSporadic G .J2 ∨ NativeSporadic.IsSporadic G .J3 ∨
    NativeSporadic.IsSporadic G .McL ∨ NativeSporadic.IsSporadic G .Ly) : GH74Conclusion G :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr h

theorem of_M12 (h : NativeSporadic.IsSporadic G .M12) : GH74Conclusion G := of_ten (Or.inl h)
theorem of_M22 (h : NativeSporadic.IsSporadic G .M22) : GH74Conclusion G :=
  of_ten (Or.inr <| Or.inl h)
theorem of_M23 (h : NativeSporadic.IsSporadic G .M23) : GH74Conclusion G :=
  of_ten (Or.inr <| Or.inr <| Or.inl h)
theorem of_J1 (h : NativeSporadic.IsSporadic G .J1) : GH74Conclusion G :=
  of_ten (Or.inr <| Or.inr <| Or.inr <| Or.inl h)
theorem of_J2 (h : NativeSporadic.IsSporadic G .J2) : GH74Conclusion G :=
  of_ten (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h)
theorem of_J3 (h : NativeSporadic.IsSporadic G .J3) : GH74Conclusion G :=
  of_ten (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h)
theorem of_McL (h : NativeSporadic.IsSporadic G .McL) : GH74Conclusion G :=
  of_ten (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h)
theorem of_Ly (h : NativeSporadic.IsSporadic G .Ly) : GH74Conclusion G :=
  of_ten (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr h)

end GH74Conclusion

theorem isSporadic_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {s : TauCeti.SporadicName} (h : NativeSporadic.IsSporadic G s) :
    NativeSporadic.IsSporadic G' s :=
  let ⟨e'⟩ := h; ⟨e.symm.trans e'⟩

theorem lieModel_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {t : StatedLieTag} {n p f : ℕ} (h : LieModel G t n p f) : LieModel G' t n p f :=
  CFSG.Blueprint.LieModel.of_mulEquiv e h

theorem nonempty_alternating_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {n : ℕ}
    (h : Nonempty (G ≃* alternatingGroup (Fin n))) : Nonempty (G' ≃* alternatingGroup (Fin n)) :=
  let ⟨e'⟩ := h; ⟨e.symm.trans e'⟩

theorem GH74Conclusion.of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : GH74Conclusion G) : GH74Conclusion G' := by
  have L := fun {t : StatedLieTag} {n p f : ℕ} (h : LieModel G t n p f) => lieModel_of_mulEquiv e h
  have S := fun {s : TauCeti.SporadicName} (h : NativeSporadic.IsSporadic G s) =>
    isSporadic_of_mulEquiv e h
  rcases h with ⟨p, f, hp, hp2, hf, h | h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ |
      ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hf, hq, h⟩ |
      ⟨p, f, hp, hf, hq, h⟩ | (h | h | h | h) | ⟨n, hn, hn', h⟩ |
      (h | h | h | h | h | h | h | h)
  · exact Or.inl ⟨p, f, hp, hp2, hf, Or.inl (L h)⟩
  · exact Or.inl ⟨p, f, hp, hp2, hf, Or.inr (L h)⟩
  · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, L h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, L h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hq, L h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hq, L h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hf, hq, L h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hf, hq, L h⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (L h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (Or.inr (Or.inl (L h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (Or.inr (Or.inr (Or.inl (L h)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (Or.inr (Or.inr (Or.inr (L h)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨n, hn, hn', nonempty_alternating_of_mulEquiv e h⟩))))))))
  all_goals
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))))
  · exact Or.inl (S h)
  · exact Or.inr (Or.inl (S h))
  · exact Or.inr (Or.inr (Or.inl (S h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (S h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (S h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (S h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (S h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (S h)))))))

theorem GH74Conclusion.ghList {G : Type} [Group G] (h : GH74Conclusion G) : GHList G := by
  rcases h with ⟨p, f, hp, hp2, hf, h | h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ |
      ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hf, hq, h⟩ |
      ⟨p, f, hp, hf, hq, h⟩ | (h | h | h | h) | ⟨n, hn, hn', h⟩ |
      (h | h | h | h | h | h | h | h)
  · exact Or.inr (Or.inr ⟨p, f, hp, hf, Or.inl ⟨hp2, Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h))))⟩⟩)
  · exact Or.inr (Or.inr ⟨p, f, hp, hf, Or.inl ⟨hp2, Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr h))))⟩⟩)
  · exact Or.inr (Or.inr ⟨p, f, hp, hf, Or.inl ⟨hp2, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩⟩)
  ·
    have hf : 1 ≤ f := by
      rcases h with ⟨ht, -⟩ | ⟨-, -, ⟨⟨-, hf, -⟩, -⟩⟩ | ⟨-, -, ⟨⟨-, hf, -⟩, -⟩⟩ | ⟨-, ht, -⟩
      · exact absurd ht (by decide)
      · exact hf
      · exact hf
      · exact absurd ht (by decide)
    exact Or.inr (Or.inr ⟨3, f, Nat.prime_three, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h)))))⟩)
  · exact Or.inr (Or.inr ⟨p, f, hp, hf, Or.inr (Or.inl ⟨hp2, hq, h⟩)⟩)
  · exact Or.inr (Or.inr ⟨p, f, hp, hf, Or.inr (Or.inr (Or.inl ⟨hp2, hq, h⟩))⟩)
  · exact Or.inr (Or.inr ⟨p, f, hp, hf, Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, h⟩)))⟩)
  · exact Or.inr (Or.inr ⟨p, f, hp, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, h⟩))))⟩)
  · exact Or.inr (Or.inr ⟨2, 1, Nat.prime_two, le_rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨rfl, Or.inl h⟩)))))⟩)
  · exact Or.inr (Or.inr ⟨2, 1, Nat.prime_two, le_rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨rfl, Or.inr (Or.inl h)⟩)))))⟩)
  · exact Or.inr (Or.inr ⟨2, 1, Nat.prime_two, le_rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl h))⟩)))))⟩)
  · exact Or.inr (Or.inr ⟨2, 1, Nat.prime_two, le_rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr h)))⟩)))))⟩)
  · exact Or.inl ⟨n, by omega, hn', h⟩
  all_goals refine Or.inr (Or.inl ?_)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

theorem GHList.of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X') (h : GHList X) :
    GHList X' := by
  have L := fun {t : StatedLieTag} {n p f : ℕ} (h : LieModel X t n p f) => lieModel_of_mulEquiv e h
  have S := fun {s : TauCeti.SporadicName} (h : NativeSporadic.IsSporadic X s) =>
    isSporadic_of_mulEquiv e h
  rcases h with ⟨n, hn, hn', h⟩ | (h | h | h | h | h | h | h | h | h) |
      ⟨p, f, hp, hf, ⟨hp2, h | h | h | h | h | h⟩ | ⟨hp2, hq, h⟩ | ⟨hp2, hq, h⟩ | ⟨hq, h⟩ |
        ⟨hq, h⟩ | h | ⟨hp2, h | h | h | h | h⟩⟩
  · exact Or.inl ⟨n, hn, hn', nonempty_alternating_of_mulEquiv e h⟩
  · exact Or.inr (Or.inl (Or.inl (S h)))
  · exact Or.inr (Or.inl (Or.inr (Or.inl (S h))))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (S h)))))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (S h))))))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (S h)))))))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (S h))))))))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (S h)))))))))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (S h))))))))))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (S h))))))))))
  all_goals refine Or.inr (Or.inr ⟨p, f, hp, hf, ?_⟩)
  · exact Or.inl ⟨hp2, Or.inl (L h)⟩
  · exact Or.inl ⟨hp2, Or.inr (Or.inl (L h))⟩
  · exact Or.inl ⟨hp2, Or.inr (Or.inr (Or.inl (L h)))⟩
  · exact Or.inl ⟨hp2, Or.inr (Or.inr (Or.inr (Or.inl (L h))))⟩
  · exact Or.inl ⟨hp2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (L h)))))⟩
  · exact Or.inl ⟨hp2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (L h)))))⟩
  · exact Or.inr (Or.inl ⟨hp2, hq, L h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hp2, hq, L h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, L h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, L h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (L h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp2, Or.inl (L h)⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp2, Or.inr (Or.inl (L h))⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp2, Or.inr (Or.inr (Or.inl
      (L h)))⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp2, Or.inr (Or.inr (Or.inr (Or.inl
      (L h))))⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp2, Or.inr (Or.inr (Or.inr (Or.inr
      (L h))))⟩)))))

end CFSG.GH74
