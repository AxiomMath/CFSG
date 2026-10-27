module

public import CFSG.Quasithin.Recognition.Kleidman.F204.O2Alg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2016Sp

open Module CFSG.Quasithin.Kleidman.F204.O2Alg

section Restrict

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def restrictEquiv (S : Submodule (ZMod 2) V) (g : V ≃ₗ[ZMod 2] V) (n : ℕ)
    (hn : g ^ (n + 1) = 1) (hS : ∀ u ∈ S, g u ∈ S) : S ≃ₗ[ZMod 2] S :=
  LinearEquiv.ofSubmodules g S S (map_eq_of_pow S g n hn hS)

theorem restrictEquiv_apply (S : Submodule (ZMod 2) V) (g : V ≃ₗ[ZMod 2] V) (n : ℕ)
    (hn : g ^ (n + 1) = 1) (hS : ∀ u ∈ S, g u ∈ S) (s : S) :
    ((restrictEquiv S g n hn hS s : S) : V) = g s := rfl

theorem restrictEquiv_pow_apply (S : Submodule (ZMod 2) V) (g : V ≃ₗ[ZMod 2] V) (n : ℕ)
    (hn : g ^ (n + 1) = 1) (hS : ∀ u ∈ S, g u ∈ S) (k : ℕ) (s : S) :
    (((restrictEquiv S g n hn hS ^ k) s : S) : V) = (g ^ k) s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => rw [pow_succ_apply, pow_succ_apply, restrictEquiv_apply, ih]

end Restrict

theorem fixed_eq_zero_of_order_five {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (hdim : finrank (ZMod 2) V = 8)
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (hB : ∀ w, (∀ v, B v w = 0) → w = 0)
    (x g : V ≃ₗ[ZMod 2] V) (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1) (hg3 : g ^ 3 = 1)
    (hgfix : ∀ v, g v = v → v = 0) (hc : Commute x g)
    (hxB : ∀ v w, B (x v) (x w) = B v w) (hgB : ∀ v w, B (g v) (g w) = B v w) :
    ∀ v, x v = v → v = 0 := by
  intro c₀ hc₀
  by_contra hne
  have hx5v : ∀ v, x (x (x (x (x v)))) = v := fun v => by
    have h5 : (x ^ 5) v = v := by rw [hx5]; rfl
    have e : (x ^ 5) v = x (x (x (x (x v)))) := by simp [pow_succ_apply]
    rw [e] at h5
    exact h5
  have hxg : ∀ v, x (g v) = g (x v) := fun v => by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) hc.eq
    simpa using this
  set W : Submodule (ZMod 2) V := LinearMap.range ((x : V →ₗ[ZMod 2] V) - LinearMap.id) with hW
  have hWmem : ∀ u, x u - u ∈ W := fun u => ⟨u, rfl⟩
  have hWmem' : ∀ w ∈ W, ∃ u, w = x u - u := by
    rintro w ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  have hdec : ∀ v, ∃ c, x c = c ∧ ∃ w ∈ W, v = c + w := by
    intro v
    refine ⟨v + x v + x (x v) + x (x (x v)) + x (x (x (x v))), ?_,
      x (x v + x (x (x v))) - (x v + x (x (x v))), hWmem _, ?_⟩
    · simp only [map_add]
      rw [hx5v v]
      abel
    · simp only [map_add, sub_eq_add']
      have h1 := add_self_eq_zero (x v)
      have h2 := add_self_eq_zero (x (x v))
      have h3 := add_self_eq_zero (x (x (x v)))
      have h4 := add_self_eq_zero (x (x (x (x v))))
      calc v = v + ((x v + x v) + (x (x v) + x (x v)) + (x (x (x v)) + x (x (x v))) +
            (x (x (x (x v))) + x (x (x (x v))))) := by rw [h1, h2, h3, h4]; simp
        _ = _ := by abel
  have hinter : ∀ c, x c = c → c ∈ W → c = 0 := by
    intro c hcx hcW
    obtain ⟨u, rfl⟩ := hWmem' c hcW
    have h1 : x (x u - u) = x u - u := hcx
    simp only [sub_eq_add', map_add] at h1
    have h2 : x (x u) = u := by
      have h3 : x (x u) + x u = u + x u := by rw [h1, add_comm]
      exact add_right_cancel h3
    have h4 : x u = u := by
      have := hx5v u
      rw [h2, h2] at this
      exact this
    rw [h4, sub_self]
  have horth : ∀ c, x c = c → ∀ w ∈ W, B c w = 0 := by
    intro c hcx w hw
    obtain ⟨u, rfl⟩ := hWmem' w hw
    rw [map_sub, ← hxB c u, hcx, sub_self]
  have hWx : ∀ w ∈ W, x w ∈ W := by
    intro w hw
    obtain ⟨u, rfl⟩ := hWmem' w hw
    have : x (x u - u) = x (x u) - x u := by rw [map_sub]
    rw [this]
    exact hWmem (x u)
  have hWg : ∀ w ∈ W, g w ∈ W := by
    intro w hw
    obtain ⟨u, rfl⟩ := hWmem' w hw
    have : g (x u - u) = x (g u) - g u := by rw [map_sub, ← hxg]
    rw [this]
    exact hWmem (g u)
  obtain ⟨u₀, hu₀⟩ : ∃ u, x u ≠ u := by
    by_contra h
    exact hx1 (LinearEquiv.ext fun u => by by_contra h'; exact h ⟨u, h'⟩)
  have hWbot : W ≠ ⊥ := by
    intro h
    have : x u₀ - u₀ ∈ W := hWmem u₀
    rw [h, Submodule.mem_bot] at this
    exact hu₀ (sub_eq_zero.mp this)
  have hWtop : W ≠ ⊤ := by
    intro h
    have : c₀ ∈ W := by rw [h]; trivial
    exact hne (hinter c₀ hc₀ this)
  have hWfpf : ∀ w ∈ W, x w = w → w = 0 := fun w hw hxw => hinter w hxw hw
  let xW : W ≃ₗ[ZMod 2] W := restrictEquiv W x 4 hx5 hWx
  let gW : W ≃ₗ[ZMod 2] W := restrictEquiv W g 2 hg3 hWg
  have hxW5 : xW ^ 5 = 1 := by
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [restrictEquiv_pow_apply, hx5]
    rfl
  have hgW3 : gW ^ 3 = 1 := by
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [restrictEquiv_pow_apply, hg3]
    rfl
  have hxWfpf : ∀ w : W, xW w = w → w = 0 := fun w hw =>
    Subtype.ext (hWfpf w w.2 (congrArg Subtype.val hw))
  have hgWfpf : ∀ w : W, gW w = w → w = 0 := fun w hw =>
    Subtype.ext (hgfix w (congrArg Subtype.val hw))
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWbot
  have hxW1 : xW ≠ 1 := by
    intro h
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    exact hw (hxWfpf w (by rw [h]; rfl))
  have hgW1 : gW ≠ 1 := by
    intro h
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    exact hw (hgWfpf w (by rw [h]; rfl))
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxWord : orderOf xW = 5 := orderOf_eq_prime hxW5 hxW1
  have hgWord : orderOf gW = 3 := orderOf_eq_prime hgW3 hgW1
  have hWcomm : Commute xW gW := by
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    show x (g w) = g (x w)
    exact hxg w
  have h4 : 4 ∣ finrank (ZMod 2) W := four_dvd_finrank xW hxW5 hxWfpf
  have hlt : finrank (ZMod 2) W < 8 := hdim ▸ Submodule.finrank_lt hWtop
  have hpos : 1 ≤ finrank (ZMod 2) W := Submodule.one_le_finrank_iff.mpr hWbot
  have hdimW : finrank (ZMod 2) W = 4 := by omega
  let BW : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2 := B.compl₁₂ W.subtype W.subtype
  have hBW : ∃ v w : W, BW v w ≠ 0 := by
    obtain ⟨w₀, hw₀, hw₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWbot
    have : ¬ ∀ v, B v w₀ = 0 := fun h => hw₀ne (hB w₀ h)
    obtain ⟨v, hv⟩ := not_forall.1 this
    obtain ⟨c, hcx, w₁, hw₁, rfl⟩ := hdec v
    rw [map_add, LinearMap.add_apply, horth c hcx w₀ hw₀, zero_add] at hv
    exact ⟨⟨w₁, hw₁⟩, ⟨w₀, hw₀⟩, hv⟩
  exact no_invariant_form hdimW xW gW hWcomm hxWord hgWord hxWfpf BW
    (fun v w => hxB v w) (fun v w => hgB v w) hBW

end CFSG.LocalAnalysis.GLTheoremA.I2016Sp

end
