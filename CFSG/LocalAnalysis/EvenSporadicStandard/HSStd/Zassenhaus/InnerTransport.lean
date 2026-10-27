module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerFacts

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert

open Subgroup CFSG.Open

@[expose] def letterOfCode : ℕ → Letter
  | 0 => .g
  | 1 => .gi
  | _ => .y

theorem innerWordEval_cons {M : Type*} [Group M] (g y : M) (l : Letter) (w : List Letter) :
    wordEval g y (l :: w) = l.eval g y * wordEval g y w := by
  simp [wordEval]

theorem innerWordEval_nil {M : Type*} [Group M] (g y : M) : wordEval g y ([] : List Letter) = 1 := by
  simp [wordEval]

theorem innerMap_wordEval {M N : Type*} [Group M] [Group N] (f : M →* N) (g y : M)
    (w : List Letter) : f (wordEval g y w) = wordEval (f g) (f y) w := by
  induction w with
  | nil => simp [innerWordEval_nil]
  | cons l w ih =>
    rw [innerWordEval_cons, innerWordEval_cons, map_mul, ih]
    cases l <;> simp [Letter.eval]

noncomputable def innerDataMap {H G : Type*} [Group H] [Group G] {z₀ : H} {L : Subgroup G} {z : G}
    (ψ : H →* G) (hψ : Function.Injective ψ) (hL : ψ.range = L) (hz : ψ z₀ = z)
    (D : InnerData (⊤ : Subgroup H) z₀) : InnerData L z := by
  classical
  have hmemL : ∀ x : H, ψ x ∈ L := fun x => hL ▸ ⟨x, rfl⟩
  have hsurj : ∀ y ∈ L, ∃ x : H, ψ x = y := fun y hy => by
    rw [← hL] at hy
    exact hy
  have hC : ∀ x : H, ψ x ∈ L ⊓ centralizer ({z} : Set G) ↔
      x ∈ (⊤ : Subgroup H) ⊓ centralizer ({z₀} : Set H) := by
    intro x
    rw [mem_inf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← hz,
      ← map_mul, ← map_mul, hψ.eq_iff]
    exact ⟨fun h => ⟨mem_top _, h.2⟩, fun h => ⟨hmemL x, h.2⟩⟩
  have hconj : ∀ (a b : H), (∃ k ∈ (⊤ : Subgroup H), k * a * k⁻¹ = b) →
      ∃ k ∈ L, k * ψ a * k⁻¹ = ψ b := by
    rintro a b ⟨k, -, e⟩
    exact ⟨ψ k, hmemL k, by rw [← map_inv, ← map_mul, ← map_mul, e]⟩
  have hE : closure (Set.range fun j : Fin 4 => wordEval (ψ D.g₁) (ψ D.a) (D.eW j)) =
      (closure (Set.range fun j : Fin 4 => wordEval D.g₁ D.a (D.eW j))).map ψ := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    congr 1
    ext x
    simp only [Set.mem_range, Function.comp_apply, innerMap_wordEval]
  refine
    { g₁ := ψ D.g₁
      a := ψ D.a
      g₁_mem := (hC _).2 D.g₁_mem
      a_mem := (hC _).2 D.a_mem
      orderOf_g₁ := (orderOf_injective ψ hψ _).trans D.orderOf_g₁
      order_five := ?_
      h := ψ D.h
      h_mem := (hC _).2 D.h_mem
      h_comm := by rw [← map_mul, ← map_mul, D.h_comm]
      ys := fun i => ψ (D.ys i)
      ys_mem := fun i => (hC _).2 (D.ys_mem i)
      filter := ?_
      a_conj := ?_
      eW := D.eW
      E_elemAbelian := ?_
      E_card := ?_
      z_mem_E := ?_
      E_conj := ?_
      pres := ?_
      wb := D.wb
      wb_odd := D.wb_odd
      invol := ?_
      not_conj := ?_
      u := ψ D.u
      u_mem := hmemL _
      u_comm := ?_
      u_sq := ?_
      u_ne_one := fun h => D.u_ne_one (hψ (by rw [h, map_one]))
      u_ne_b := ?_
      u_conj := ?_
      ub_conj := ?_
      swap_ys := ?_
      swap_b := ?_
      yW := D.yW
      zmul := D.zmul
      zmul_spec := ?_
      eOne := D.eOne
      eOne_spec := ?_
      eA := D.eA
      eA_spec := ?_
      stab := ?_ }
  · intro x hx h5
    obtain ⟨x₀, rfl⟩ := hsurj x hx.1
    obtain ⟨c, hc, hce⟩ := D.order_five x₀ ((hC x₀).1 hx)
      (by rw [← orderOf_injective ψ hψ x₀]; exact h5)
    exact ⟨ψ c, (hC c).2 hc, by rw [← map_inv, ← map_mul, ← map_mul, hce]⟩
  · intro y hy hyp
    obtain ⟨y₀, rfl⟩ := hsurj y hy.1
    have hyp' : ∀ w : List Letter, wordEval D.g₁ y₀ w = 1 ↔ wordEval D.g₁ D.a w = 1 := by
      intro w
      have h1 := hyp w
      rw [← innerMap_wordEval, ← innerMap_wordEval, ← map_one ψ, hψ.eq_iff, hψ.eq_iff] at h1
      exact h1
    obtain ⟨k, i, e⟩ := D.filter y₀ ((hC y₀).1 hy) hyp'
    exact ⟨k, i, by rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, e]⟩
  · obtain ⟨k, -, e⟩ := D.a_conj
    exact ⟨ψ k, hmemL k, by rw [← hz, ← map_inv, ← map_mul, ← map_mul, e]⟩
  · rw [hE]
    obtain ⟨hab, hsq⟩ := D.E_elemAbelian
    rw [isMulCommutative_iff_of_setLike] at hab
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff_of_setLike]
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hab a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hsq a ha, map_one]
  · rw [hE, Subgroup.card_map_of_injective hψ]
    exact D.E_card
  · rw [hE]
    exact ⟨z₀, D.z_mem_E, hz⟩
  · intro e he he1
    rw [hE] at he
    obtain ⟨x, hx, rfl⟩ := he
    have hx1 : x ≠ 1 := fun h => he1 (by rw [h, map_one])
    obtain ⟨k, hk, e⟩ := D.E_conj x hx hx1
    rw [← hz]
    exact hconj _ _ ⟨k, hk, e⟩
  · intro i hi
    obtain ⟨h1, c, hc, hcE⟩ := D.pres i hi
    refine ⟨?_, ψ c, (hC c).2 hc, fun j => ?_⟩
    · rw [← hz]
      exact hconj _ _ h1
    · rw [hE]
      refine ⟨_, hcE j, ?_⟩
      rw [map_mul, map_mul, map_inv, innerMap_wordEval]
  · intro x hx hx1 hx2
    obtain ⟨x₀, rfl⟩ := hsurj x hx
    have hx01 : x₀ ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hx02 : x₀ * x₀ = 1 := hψ (by rw [map_mul, hx2, map_one])
    rcases D.invol x₀ (mem_top _) hx01 hx02 with h | h
    · rw [← hz]
      exact Or.inl (hconj _ _ h)
    · obtain ⟨k, hk, e⟩ := h
      refine Or.inr ⟨ψ k, hmemL k, ?_⟩
      rw [← innerMap_wordEval] at *
      rw [← map_inv, ← map_mul, ← map_mul, e]
  · intro k hk h
    obtain ⟨k₀, rfl⟩ := hsurj k hk
    apply D.not_conj k₀ (mem_top _)
    apply hψ
    rw [map_mul, map_mul, map_inv, hz, h, innerMap_wordEval]
  · rw [← innerMap_wordEval, ← map_mul, ← map_mul, D.u_comm]
  · rw [← map_mul, D.u_sq, map_one]
  · intro h
    apply D.u_ne_b
    apply hψ
    rw [innerMap_wordEval]
    exact h
  · obtain ⟨k, -, e⟩ := D.u_conj
    refine ⟨ψ k, hmemL k, ?_⟩
    have := congrArg ψ e
    simpa only [map_mul, map_inv, innerMap_wordEval] using this
  · obtain ⟨k, -, e⟩ := D.ub_conj
    refine ⟨ψ k, hmemL k, ?_⟩
    have := congrArg ψ e
    simpa only [map_mul, map_inv, innerMap_wordEval] using this
  · intro i hi
    obtain ⟨k, -, e⟩ := D.swap_ys i hi
    refine ⟨ψ k, hmemL k, ?_⟩
    have := congrArg ψ e
    simpa only [map_mul, map_inv, innerMap_wordEval] using this
  · intro i hi
    obtain ⟨k, -, e⟩ := D.swap_b i hi
    refine ⟨ψ k, hmemL k, ?_⟩
    have := congrArg ψ e
    simpa only [map_mul, map_inv, innerMap_wordEval, hz] using this
  · intro e
    have := congrArg ψ (D.zmul_spec e)
    simpa only [map_mul, innerMap_wordEval, hz] using this
  · have := congrArg ψ D.eOne_spec
    simpa only [innerMap_wordEval, map_one] using this
  · have := congrArg ψ D.eA_spec
    simpa only [innerMap_wordEval] using this
  · intro i hi
    obtain ⟨c, ψ', m, gs, σ, word, x, hc, h1, h2, h3, h4, k, -, e⟩ := D.stab i hi
    refine ⟨ψ c, ψ', m, fun j => ψ (gs j), σ, word, x, (hC c).2 hc, fun e' => ?_,
      fun j => ⟨hmemL _, fun e' => ?_⟩, h3, h4, ψ k, hmemL k, ?_⟩
    · have := congrArg ψ (h1 e')
      simpa only [map_mul, map_inv, innerMap_wordEval] using this
    · have := congrArg ψ ((h2 j).2 e')
      simpa only [map_mul, map_inv, innerMap_wordEval] using this
    · have := congrArg ψ e
      simpa only [map_mul, map_inv, innerMap_wordEval] using this

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert
