module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5Inputs

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

open CFSG.CGT.PushingUpLit.CGT6

@[expose] def PairAlt {G : Type*} [Group G] (p q : G) : Prop :=
  p * q = 1 ∨ p * q⁻¹ = 1 ∨ p * q = q * p ∨ (p * q) ^ 2 = 1 ∨ (p * q⁻¹) ^ 2 = 1 ∨
    ((p * q) ^ 5 = 1 ∧ (p * q * p * q⁻¹) ^ 2 = 1 ∧ (p * q⁻¹) ^ 5 = 1 ∧
      (p * q⁻¹ * p * q) ^ 2 = 1)

instance {G : Type*} [Group G] [DecidableEq G] (p q : G) : Decidable (PairAlt p q) := by
  unfold PairAlt
  infer_instance

theorem PairAlt.of_comm {G : Type*} [Group G] {p q : G} (h : p * q = q * p) : PairAlt p q :=
  Or.inr (Or.inr (Or.inl h))

theorem PairAlt.of_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {p q : G} (h : PairAlt (f p) (f q)) : PairAlt p q := by
  have key : ∀ x : G, f x = 1 → x = 1 := fun x hx => hf (hx.trans f.map_one.symm)
  rcases h with h | h | h | h | h | ⟨h1, h2, h3, h4⟩
  · exact Or.inl (key _ (by simpa using h))
  · exact Or.inr (Or.inl (key _ (by simpa using h)))
  · exact Or.inr (Or.inr (Or.inl (hf (by simpa using h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (key _ (by simpa using h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key _ (by simpa using h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨key _ (by simpa using h1), key _ (by simpa using h2), key _ (by simpa using h3),
        key _ (by simpa using h4)⟩))))

theorem PairAlt.map {G H : Type*} [Group G] [Group H] (f : G →* H) {p q : G}
    (h : PairAlt p q) : PairAlt (f p) (f q) := by
  rcases h with h | h | h | h | h | ⟨h1, h2, h3, h4⟩
  · exact Or.inl (by rw [← map_mul, h, map_one])
  · exact Or.inr (Or.inl (by rw [← map_inv, ← map_mul, h, map_one]))
  · exact Or.inr (Or.inr (Or.inl (by rw [← map_mul, ← map_mul, h])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← map_mul, ← map_pow, h, map_one]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by rw [← map_inv, ← map_mul, ← map_pow, h, map_one])))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩))))
    · rw [← map_mul, ← map_pow, h1, map_one]
    · rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, h2, map_one]
    · rw [← map_inv, ← map_mul, ← map_pow, h3, map_one]
    · rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, h4, map_one]

theorem pairAlt_alt_four (u v : alternatingGroup (Fin 4)) (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) :
    PairAlt u v := by
  revert u v
  decide +kernel

theorem pairAlt_alt_five (u v : alternatingGroup (Fin 5)) (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) :
    PairAlt u v := by
  revert u v
  decide +kernel

theorem PairAlt.of_isZ3E9A4A5 {K : Type} [Group K] (hK : IsZ3E9A4A5 K) {p q : K}
    (hp : p ^ 3 = 1) (hq : q ^ 3 = 1) : PairAlt p q := by
  rcases hK with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · refine PairAlt.of_comm (e.injective ?_)
    rw [map_mul, map_mul, mul_comm]
  · refine PairAlt.of_comm (e.injective ?_)
    rw [map_mul, map_mul, mul_comm]
  · exact PairAlt.of_map e.toMonoidHom e.injective
      (pairAlt_alt_four _ _ (by rw [← map_pow]; simp [hp]) (by rw [← map_pow]; simp [hq]))
  · exact PairAlt.of_map e.toMonoidHom e.injective
      (pairAlt_alt_five _ _ (by rw [← map_pow]; simp [hp]) (by rw [← map_pow]; simp [hq]))

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

end
