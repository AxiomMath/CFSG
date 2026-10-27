module

public import CFSG.Quasithin.Background.HCocBase

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Coc CFSG.Quasithin.H.ModChk

variable {n : ℕ}

theorem wAct_lt {cs : List (List ℕ)} {k : ℕ} (hcs : ∀ i < k, ∀ c ∈ cs.getD i [], c < 2 ^ n) :
    ∀ u : List ℕ, (∀ i ∈ u, i < k) → ∀ m < 2 ^ n, wAct cs u m < 2 ^ n
  | [], _, _, hm => hm
  | i :: _, hu, _, _ => actM_lt (hcs i (hu i List.mem_cons_self)) _

theorem eq_refl_of_words {X : Subgroup (MulAut (Wn n))} {gs : List (MulAut (Wn n))}
    {cs : List (List ℕ)} (hmem : ∀ i < gs.length, gs.getD i 1 ∈ X)
    (hact : ∀ i < gs.length, ActsBy (gs.getD i 1) (cs.getD i []))
    (hcs : ∀ i < gs.length, ∀ c ∈ cs.getD i [], c < 2 ^ n)
    {t0 v0 : ℕ} (ht0 : t0 < 2 ^ n) (hv0 : v0 < 2 ^ n) (ht0ne : t0 ≠ 0) (hv0ne : v0 ≠ 0)
    (hvt : v0 ≠ t0) {G H S : List (List ℕ)} {u₂ u₃ : List ℕ}
    (hG : ∀ u ∈ G, ∀ i ∈ u, i < gs.length) (hH : ∀ u ∈ H, ∀ i ∈ u, i < gs.length)
    (hS : ∀ u ∈ S, ∀ i ∈ u, i < gs.length) (h₂ : ∀ i ∈ u₂, i < gs.length)
    (h₃ : ∀ i ∈ u₃, i < gs.length) (hGt : ∀ u ∈ G, wAct cs u t0 = t0)
    (hGfix : ∀ m < 2 ^ n, (∀ u ∈ G, wAct cs u m = m) → m = 0 ∨ m = t0)
    (hHv : ∀ u ∈ H, wAct cs u v0 = v0)
    (hHfix : ∀ m < 2 ^ n, (∀ u ∈ H, wAct cs u m = m) →
      m = 0 ∨ m = t0 ∨ m = v0 ∨ m = v0 ^^^ t0)
    (h₂t : wAct cs u₂ t0 = t0) (h₃t : wAct cs u₃ t0 = t0)
    (htri : v0 ^^^ wAct cs u₂ v0 ^^^ wAct cs u₃ v0 = 0)
    (hspan : ∀ m < 2 ^ n, m ∈ combos (S.map fun u => wAct cs u v0))
    (ψ : Wn n ≃* Wn n) (hψ : ∀ x ∈ X, ∀ w, ψ (x w) = x (ψ w)) :
    ψ = MulEquiv.refl (Wn n) := by
  have hpos : (0 : ℕ) < 2 ^ n := Nat.two_pow_pos n
  have hmap : ∀ u : List ℕ, (∀ i ∈ u, i < gs.length) → ∀ a b : ℕ, ψ (toW n a) = toW n b →
      ψ (toW n (wAct cs u a)) = toW n (wAct cs u b) := by
    intro u hu a b hab
    rw [← wProd_toW hact u hu a, ← wProd_toW hact u hu b, ← hab]
    exact hψ _ (wProd_mem hmem u) _
  have hone : ∀ a : ℕ, a < 2 ^ n → ψ (toW n a) = 1 → a = 0 := by
    intro a ha h
    refine toW_inj ha hpos ?_
    rw [toW_zero]
    exact ψ.injective (by rw [h, map_one])
  have hfix : ∀ (W : List (List ℕ)), (∀ u ∈ W, ∀ i ∈ u, i < gs.length) → ∀ a b : ℕ, a < 2 ^ n →
      b < 2 ^ n → ψ (toW n a) = toW n b → (∀ u ∈ W, wAct cs u a = a) →
      ∀ u ∈ W, wAct cs u b = b := by
    intro W hW a b ha hb hab hWa u hu
    have h1 := hmap u (hW u hu) a b hab
    rw [hWa u hu, hab] at h1
    exact (toW_inj hb (wAct_lt hcs u (hW u hu) b hb) h1).symm
  obtain ⟨b₁, hb₁, hψt⟩ := toW_surj n (ψ (toW n t0))
  have hψt0 : ψ (toW n t0) = toW n t0 := by
    have hfb := hfix G hG t0 b₁ ht0 hb₁ hψt.symm hGt
    rcases hGfix b₁ hb₁ hfb with rfl | rfl
    · rw [toW_zero] at hψt
      exact absurd (hone t0 ht0 hψt.symm) ht0ne
    · exact hψt.symm
  obtain ⟨b₂, hb₂, hψv⟩ := toW_surj n (ψ (toW n v0))
  have hfb₂ := hfix H hH v0 b₂ hv0 hb₂ hψv.symm hHv
  have hb₂' : b₂ = v0 ∨ b₂ = v0 ^^^ t0 := by
    rcases hHfix b₂ hb₂ hfb₂ with rfl | rfl | h | h
    · rw [toW_zero] at hψv
      exact absurd (hone v0 hv0 hψv.symm) hv0ne
    · exact absurd (toW_inj hv0 ht0 (ψ.injective (hψv.symm.trans hψt0.symm))) hvt
    · exact Or.inl h
    · exact Or.inr h
  have hψv0 : ψ (toW n v0) = toW n v0 := by
    rcases hb₂' with rfl | rfl
    · exact hψv.symm
    · exfalso
      have hv2 := hmap u₂ h₂ v0 _ hψv.symm
      have hv3 := hmap u₃ h₃ v0 _ hψv.symm
      have hx2 : wAct cs u₂ (v0 ^^^ t0) = wAct cs u₂ v0 ^^^ t0 := by
        rw [xorLin_wAct cs u₂ v0 t0, h₂t]
      have hx3 : wAct cs u₃ (v0 ^^^ t0) = wAct cs u₃ v0 ^^^ t0 := by
        rw [xorLin_wAct cs u₃ v0 t0, h₃t]
      rw [hx2] at hv2
      rw [hx3] at hv3
      have h1 : toW n v0 * toW n (wAct cs u₂ v0) * toW n (wAct cs u₃ v0) = 1 := by
        rw [← toW_xor, ← toW_xor, htri, toW_zero]
      have h2 : ψ (toW n v0 * toW n (wAct cs u₂ v0) * toW n (wAct cs u₃ v0)) = 1 := by
        rw [h1, map_one]
      rw [map_mul, map_mul, ← hψv, hv2, hv3, toW_xor, toW_xor, toW_xor] at h2
      have hpp : toW n t0 * toW n t0 = 1 := by
        rw [← toW_xor, Nat.xor_self, toW_zero]
      have h3 : toW n t0 = 1 := by
        calc toW n t0 = (toW n v0 * toW n (wAct cs u₂ v0) * toW n (wAct cs u₃ v0)) *
              (toW n t0 * toW n t0 * toW n t0) := by
              rw [h1, hpp, one_mul, one_mul]
          _ = 1 := by
              rw [← h2]
              ac_rfl
      exact ht0ne (toW_inj ht0 hpos (h3.trans (toW_zero n).symm))
  let U : Subgroup (Wn n) :=
    { carrier := {w | ψ w = w}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      one_mem' := map_one ψ
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv, ha]
        rfl }
  have hSU : ∀ v ∈ S.map fun u => wAct cs u v0, (MaskCoords.std n).vm v ∈ U := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hv
    exact hmap u (hS u hu) v0 v0 hψv0
  refine MulEquiv.ext fun w => ?_
  obtain ⟨m, hm, rfl⟩ := toW_surj n w
  exact (MaskCoords.std n).vm_mem_of_combos U hSU m (hspan m hm)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
