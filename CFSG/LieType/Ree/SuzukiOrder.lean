module

public import CFSG.LieType.Ree.SuzukiBruhatNormalForm

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint

variable {a : ℕ} {K : Type} [Field K]

@[expose] noncomputable def suzukiNormalForm
    (a : ℕ) (K : Type) [Field K] :
    ((K × K) × Kˣ) ⊕ ((K × K) × Kˣ × (K × K)) → suzukiGroup a K
  | .inl p => suzukiSElt a K p.1.1 p.1.2 * suzukiDElt a K p.2
  | .inr p => suzukiSElt a K p.1.1 p.1.2 * suzukiDElt a K p.2.1 * suzukiWElt a K *
      suzukiSElt a K p.2.2.1 p.2.2.2

theorem suzukiNormalForm_bijective
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Bijective (suzukiNormalForm a K) := by
  refine ⟨?_, fun g => ?_⟩
  · rintro (⟨⟨u, v⟩, l⟩ | ⟨⟨u, v⟩, l, ⟨c, d⟩⟩) (⟨⟨u', v'⟩, l'⟩ | ⟨⟨u', v'⟩, l', ⟨c', d'⟩⟩) h <;>
      simp only [suzukiNormalForm] at h
    · obtain ⟨rfl, rfl, rfl⟩ := (suzuki_bruhat_normal_form hK _).2.2.1 u v u' v' l l' rfl h
      rfl
    · exact absurd ⟨⟨u, v, l, rfl⟩, ⟨u', v', l', c', d', h⟩⟩
        (suzuki_bruhat_normal_form hK _).2.1
    · exact absurd ⟨⟨u', v', l', h⟩, ⟨u, v, l, c, d, rfl⟩⟩
        (suzuki_bruhat_normal_form hK _).2.1
    · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :=
        (suzuki_bruhat_normal_form hK _).2.2.2 u v c d u' v' c' d' l l' rfl h
      rfl
  · rcases (suzuki_bruhat_normal_form hK g).1 with ⟨u, v, l, rfl⟩ | ⟨u, v, l, c, d, rfl⟩
    · exact ⟨.inl ((u, v), l), rfl⟩
    · exact ⟨.inr ((u, v), l, (c, d)), rfl⟩

theorem suzuki_order [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (suzukiGroup a K) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (suzukiNormalForm_bijective hK))]
  simp only [Nat.card_sum, Nat.card_prod, Nat.card_units, hK]
  ring

end CFSG.LieType.Ree
