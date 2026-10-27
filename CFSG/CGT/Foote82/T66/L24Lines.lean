module

public import CFSG.CGT.Foote82.T66.L24Group
import CFSG.CGT.Foote82.T66.MC2Perm
import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.CGT.Foote82.L24

open CFSG.Open CFSG.Quasithin.G11 Equiv Equiv.Perm

section Cyc

variable {N : ℕ}

@[expose] def cyc (a b c : Fin N) : Perm (Fin N) := swap a c * swap a b

variable {a b c : Fin N}

theorem cyc_apply_left (hab : a ≠ b) (hbc : b ≠ c) : cyc a b c a = b := by
  rw [cyc, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hab) hbc]

theorem cyc_apply_mid : cyc a b c b = c := by
  rw [cyc, Perm.mul_apply, swap_apply_right, swap_apply_left]

theorem cyc_apply_right (hac : a ≠ c) (hbc : b ≠ c) : cyc a b c c = a := by
  rw [cyc, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc), swap_apply_right]

theorem cyc_apply_of_ne {m : Fin N} (hma : m ≠ a) (hmb : m ≠ b) (hmc : m ≠ c) :
    cyc a b c m = m := by
  rw [cyc, Perm.mul_apply, swap_apply_of_ne_of_ne hma hmb, swap_apply_of_ne_of_ne hma hmc]

theorem cyc_inv_apply_of_ne {m : Fin N} (hma : m ≠ a) (hmb : m ≠ b) (hmc : m ≠ c) :
    (cyc a b c)⁻¹ m = m := by
  rw [Perm.inv_eq_iff_eq]
  exact (cyc_apply_of_ne hma hmb hmc).symm

theorem cyc_mem_altOn {S : Finset (Fin N)} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b)
    (hac : a ≠ c) : cyc a b c ∈ altOn (S : Set (Fin N)) :=
  swap_mul_swap_mem_altOn ha hc ha hb hac hab

theorem cyc_mem_alternatingGroup (hab : a ≠ b) (hac : a ≠ c) :
    cyc a b c ∈ alternatingGroup (Fin N) := by
  rw [Perm.mem_alternatingGroup, cyc, map_mul, sign_swap hac, sign_swap hab]
  decide

theorem cyc_pow_three (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : cyc a b c ^ 3 = 1 :=
  MC2.c3_pow_three hac hab (Ne.symm hbc)

theorem conj_cyc (π : Perm (Fin N)) (a b c : Fin N) :
    π * cyc a b c * π⁻¹ = cyc (π a) (π b) (π c) := by
  rw [cyc, cyc, swap_apply_apply, swap_apply_apply]
  group

theorem cyc_rotate (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : cyc b c a = cyc a b c := by
  ext m
  by_cases hma : m = a
  · rw [hma, cyc_apply_right (Ne.symm hab) (Ne.symm hac), cyc_apply_left hab hbc]
  by_cases hmb : m = b
  · rw [hmb, cyc_apply_left hbc (Ne.symm hac), cyc_apply_mid]
  by_cases hmc : m = c
  · rw [hmc, cyc_apply_mid, cyc_apply_right hac hbc]
  · rw [cyc_apply_of_ne hmb hmc hma, cyc_apply_of_ne hma hmb hmc]

theorem cyc_swap (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : cyc b a c = (cyc a b c)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left (Equiv.ext fun m => ?_)
  rw [Perm.mul_apply, Perm.one_apply]
  by_cases hma : m = a
  · rw [hma, cyc_apply_left hab hbc, cyc_apply_left (Ne.symm hab) hac]
  by_cases hmb : m = b
  · rw [hmb, cyc_apply_mid, cyc_apply_right hbc hac]
  by_cases hmc : m = c
  · rw [hmc, cyc_apply_right hac hbc, cyc_apply_mid]
  · rw [cyc_apply_of_ne hma hmb hmc, cyc_apply_of_ne hmb hma hmc]

end Cyc

section Rg

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def Rg (t : GLV V) : Submodule (ZMod 2) V :=
  LinearMap.range ((t : V →ₗ[ZMod 2] V) - LinearMap.id)

theorem mem_Rg {t : GLV V} {y : V} : y ∈ Rg t ↔ ∃ w, t w - w = y := by
  simp [Rg]

theorem sub_mem_Rg (t : GLV V) (w : V) : t w - w ∈ Rg t :=
  mem_Rg.2 ⟨w, rfl⟩

theorem apply_apply_apply {t : GLV V} (ht : t ^ 3 = 1) (w : V) : t (t (t w)) = w := by
  have := congrArg (fun f : GLV V => f w) ht
  simpa [pow_succ, mul_assoc] using this

theorem eq_of_mem_Rg {t : GLV V} (ht : t ^ 3 = 1) {y : V} (hy : y ∈ Rg t) :
    t (t y) - t y = y := by
  obtain ⟨w, rfl⟩ := mem_Rg.1 hy
  rw [map_sub, map_sub, apply_apply_apply ht w]
  simp only [sub_eq_add_V]
  calc w + t (t w) + (t (t w) + t w) = (t (t w) + t (t w)) + (t w + w) := by abel
    _ = t w + w := by rw [add_self_V, zero_add]

theorem eq_zero_of_mem_Rg_of_fixed {t : GLV V} (ht : t ^ 3 = 1) {y : V} (hy : y ∈ Rg t)
    (hfix : t y = y) : y = 0 := by
  have := eq_of_mem_Rg ht hy
  rw [hfix, hfix, sub_self] at this
  exact this.symm

theorem Rg_conj (g t : GLV V) {y : V} (hy : y ∈ Rg t) : g y ∈ Rg (g * t * g⁻¹) := by
  obtain ⟨w, rfl⟩ := mem_Rg.1 hy
  refine mem_Rg.2 ⟨g w, ?_⟩
  simp [map_sub]

theorem Rg_le_commSpace {K : Subgroup (GLV V)} {t : GLV V} (ht : t ∈ K) :
    Rg t ≤ commSpace K ⊤ := by
  intro y hy
  obtain ⟨w, rfl⟩ := mem_Rg.1 hy
  exact sub_mem_commSpace ht Submodule.mem_top

theorem Rg_inv_le {t : GLV V} (ht : t ^ 3 = 1) : Rg t⁻¹ ≤ Rg t := by
  intro y hy
  obtain ⟨w, rfl⟩ := mem_Rg.1 hy
  have hinv : t⁻¹ = t * t :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ← pow_two, ← pow_succ]; exact ht)
  have e : t⁻¹ w - w = (t (t w) - t w) + (t w - w) := by
    rw [hinv]
    change t (t w) - w = _
    abel
  rw [e]
  exact (Rg t).add_mem (sub_mem_Rg t (t w)) (sub_mem_Rg t w)

theorem Rg_inv {t : GLV V} (ht : t ^ 3 = 1) : Rg t⁻¹ = Rg t := by
  refine le_antisymm (Rg_inv_le ht) ?_
  have := Rg_inv_le (t := t⁻¹) (by rw [inv_pow, ht, inv_one])
  rwa [inv_inv] at this

end Rg

section T3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {G : Subgroup (GLV V)} {N : ℕ}
  (φ : ↥G ≃* alternatingGroup (Fin N))

theorem pm_injective : Function.Injective (pm φ) := fun _ _ e => φ.injective (Subtype.ext e)

theorem pm_pow (g : ↥G) (k : ℕ) : pm φ (g ^ k) = pm φ g ^ k := by
  simp [pm]

open Classical in
@[expose] noncomputable def elt (σ : Perm (Fin N)) : ↥G :=
  if h : σ ∈ alternatingGroup (Fin N) then el φ σ h else 1

theorem pm_elt {σ : Perm (Fin N)} (h : σ ∈ alternatingGroup (Fin N)) : pm φ (elt φ σ) = σ := by
  rw [elt, dif_pos h, pm_el]

theorem elt_conj (g : ↥G) {σ : Perm (Fin N)} (h : σ ∈ alternatingGroup (Fin N)) :
    elt φ (pm φ g * σ * (pm φ g)⁻¹) = g * elt φ σ * g⁻¹ := by
  have hm : pm φ g * σ * (pm φ g)⁻¹ ∈ alternatingGroup (Fin N) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (pm_mem_alternatingGroup φ g) h)
      (Subgroup.inv_mem _ (pm_mem_alternatingGroup φ g))
  apply pm_injective φ
  rw [pm_elt φ hm, pm_mul, pm_mul, pm_inv, pm_elt φ h]

theorem elt_inv {σ : Perm (Fin N)} (h : σ ∈ alternatingGroup (Fin N)) :
    elt φ σ⁻¹ = (elt φ σ)⁻¹ := by
  apply pm_injective φ
  rw [pm_elt φ (Subgroup.inv_mem _ h), pm_inv, pm_elt φ h]

@[expose] noncomputable def T3 (a b c : Fin N) : GLV V :=
  (elt φ (cyc a b c) : GLV V)

variable {a b c : Fin N}

theorem T3_pow_three (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : T3 φ a b c ^ 3 = 1 := by
  have h : elt φ (cyc a b c) ^ 3 = 1 := by
    apply pm_injective φ
    rw [pm_pow, pm_elt φ (cyc_mem_alternatingGroup hab hac), cyc_pow_three hab hac hbc, pm_one]
  rw [T3, ← Subgroup.coe_pow, h, Subgroup.coe_one]

theorem T3_mem_AS {S : Finset (Fin N)} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b)
    (hac : a ≠ c) : T3 φ a b c ∈ AS φ S := by
  rw [T3, coe_mem_AS, pm_elt φ (cyc_mem_alternatingGroup hab hac)]
  exact cyc_mem_altOn ha hb hc hab hac

theorem T3_conj (g : ↥G) (hab : a ≠ b) (hac : a ≠ c) :
    (g : GLV V) * T3 φ a b c * (g : GLV V)⁻¹ = T3 φ (pm φ g a) (pm φ g b) (pm φ g c) := by
  rw [T3, T3, ← conj_cyc (pm φ g) a b c, elt_conj φ g (cyc_mem_alternatingGroup hab hac)]
  simp

theorem T3_rotate (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : T3 φ b c a = T3 φ a b c := by
  rw [T3, T3, cyc_rotate hab hac hbc]

theorem Rg_T3_swap (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Rg (T3 φ b a c) = Rg (T3 φ a b c) := by
  have e : T3 φ b a c = (T3 φ a b c)⁻¹ := by
    rw [T3, T3, cyc_swap hab hac hbc, elt_inv φ (cyc_mem_alternatingGroup hab hac),
      Subgroup.coe_inv]
  rw [e, Rg_inv (T3_pow_three φ hab hac hbc)]

theorem apply_mem_Rg_T3 (g : ↥G) (hab : a ≠ b) (hac : a ≠ c) {y : V}
    (hy : y ∈ Rg (T3 φ a b c)) :
    (g : GLV V) y ∈ Rg (T3 φ (pm φ g a) (pm φ g b) (pm φ g c)) := by
  rw [← T3_conj φ g hab hac]
  exact Rg_conj _ _ hy

@[expose] noncomputable def I4 (a b c d : Fin N) : Submodule (ZMod 2) V :=
  Rg (T3 φ a b c) ⊓ Rg (T3 φ a b d)

end T3

section InF

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {G : Subgroup (GLV V)} {N : ℕ}
  {φ : ↥G ≃* alternatingGroup (Fin N)} {F : Finset (Fin N)} {θ : (Fin N → ZMod 2) →ₗ[ZMod 2] V}

theorem eq_zero_of_mem_Rg_T3 {a b c : Fin N} (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {y : V} (hy : y ∈ Rg (T3 φ a b c))
    (hyT : y ∈ tildeVBot (AS φ F)) : y = 0 :=
  eq_zero_of_mem_Rg_of_fixed (T3_pow_three φ hab hac hbc) hy
    (apply_of_mem_tildeVBot (T3_mem_AS φ ha hb hc hab hac) hyT)

private theorem ev_identity (a b d : Fin N) : ev b + ev d - (ev a + ev d) = ev a + ev b := by
  rw [sub_eq_add]
  calc ev b + ev d + (ev a + ev d) = ev a + ev b + (ev d + ev d) := by abel
    _ = ev a + ev b := by rw [add_self, add_zero]

theorem HeartW.exists_mem_Rg (h : HeartW φ F θ) {a b c d : Fin N} (ha : a ∈ F) (hb : b ∈ F)
    (hc : c ∈ F) (hd : d ∈ F) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ x ∈ Rg (T3 φ a b c), x - θ (ev a + ev b) ∈ tildeVBot (AS φ F) := by
  have hcF : cyc a b c ∈ altOn (F : Set (Fin N)) := cyc_mem_altOn ha hb hc hab hac
  have hcA := cyc_mem_alternatingGroup (a := a) (b := b) (c := c) hab hac
  have he := h.equiv (elt φ (cyc a b c)) (by rw [pm_elt φ hcA]; exact hcF) (ev a + ev d)
    (ev_add_ev_mem_Ew ha hd)
  rw [pm_elt φ hcA, LinearMap.map_add (pa (cyc a b c)) (ev a) (ev d), pa_ev, pa_ev,
    cyc_apply_left hab hbc, cyc_apply_of_ne (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd)] at he
  refine ⟨T3 φ a b c (θ (ev a + ev d)) - θ (ev a + ev d), sub_mem_Rg _ _, ?_⟩
  have e : T3 φ a b c (θ (ev a + ev d)) - θ (ev a + ev d) - θ (ev a + ev b) =
      ((elt φ (cyc a b c) : GLV V) (θ (ev a + ev d)) - θ (ev b + ev d)) +
        (θ (ev b + ev d - (ev a + ev d)) - θ (ev a + ev b)) := by
    rw [map_sub, T3]
    abel
  rw [e, ev_identity, sub_self, add_zero]
  exact he

theorem HeartW.exists_of_mem_Rg (h : HeartW φ F θ) {a b c : Fin N} (ha : a ∈ F) (hb : b ∈ F)
    (hc : c ∈ F) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {y : V} (hy : y ∈ Rg (T3 φ a b c)) :
    ∃ z ∈ Ew F, (∀ m, m ≠ a → m ≠ b → m ≠ c → z m = 0) ∧
      y - θ z ∈ tildeVBot (AS φ F) := by
  have hcF : cyc a b c ∈ altOn (F : Set (Fin N)) := cyc_mem_altOn ha hb hc hab hac
  have hcA := cyc_mem_alternatingGroup (a := a) (b := b) (c := c) hab hac
  have htA := T3_mem_AS φ ha hb hc hab hac
  have hyW : y ∈ commSpace (AS φ F) ⊤ := Rg_le_commSpace htA hy
  have hu : T3 φ a b c y ∈ commSpace (AS φ F) ⊤ := apply_mem_commSpace htA hyW
  obtain ⟨_, ⟨z₀, hz₀, rfl⟩, τ, hτ, hzτ⟩ := Submodule.mem_sup.1 (h.span hu)
  refine ⟨pa (cyc a b c) z₀ - z₀, (Ew F).sub_mem (pa_mem_Ew hcF hz₀) hz₀,
    fun m hma hmb hmc => ?_, ?_⟩
  · rw [Pi.sub_apply, pa_apply, cyc_inv_apply_of_ne hma hmb hmc, sub_self]
  · have he := h.equiv (elt φ (cyc a b c)) (by rw [pm_elt φ hcA]; exact hcF) z₀ hz₀
    rw [pm_elt φ hcA] at he
    have hy' := eq_of_mem_Rg (T3_pow_three φ hab hac hbc) hy
    have e : y - θ (pa (cyc a b c) z₀ - z₀) =
        ((elt φ (cyc a b c) : GLV V) (θ z₀) - θ (pa (cyc a b c) z₀)) := by
      rw [← hy', ← hzτ, map_add, apply_of_mem_tildeVBot htA hτ, map_sub, T3]
      abel
    rw [e]
    exact he

theorem HeartW.mem_T_or (h : HeartW φ F θ) {a b c d m : Fin N} (ha : a ∈ F) (hb : b ∈ F)
    (hc : c ∈ F) (hd : d ∈ F) (hm : m ∈ F) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hma : m ≠ a) (hmb : m ≠ b) (hmc : m ≠ c)
    (hmd : m ≠ d) {y : V} (hy : y ∈ I4 φ a b c d) :
    y ∈ tildeVBot (AS φ F) ∨ y - θ (ev a + ev b) ∈ tildeVBot (AS φ F) := by
  obtain ⟨z₁, hz₁, hs₁, hy₁⟩ := h.exists_of_mem_Rg ha hb hc hab hac hbc hy.1
  obtain ⟨z₂, hz₂, hs₂, hy₂⟩ := h.exists_of_mem_Rg ha hb hd hab had hbd hy.2
  have hdiff : θ (z₁ - z₂) ∈ tildeVBot (AS φ F) := by
    have e : θ (z₁ - z₂) = (y - θ z₂) - (y - θ z₁) := by
      rw [map_sub]
      abel
    rw [e]
    exact Submodule.sub_mem _ hy₂ hy₁
  have hz : z₁ = z₂ := by
    rcases (h.ker _ ((Ew F).sub_mem hz₁ hz₂)).1 hdiff with h0 | hj
    · exact sub_eq_zero.1 h0
    · exfalso
      have h1 : z₁ m - z₂ m = jS F m := congrFun hj m
      rw [hs₁ m hma hmb hmc, hs₂ m hma hmb hmd, sub_self, jS_apply, if_pos hm] at h1
      exact absurd h1 (by decide)
  have hsupp : ∀ k, k ≠ a → k ≠ b → z₁ k = 0 := by
    intro k hka hkb
    by_cases hkc : k = c
    · rw [hz, hkc]
      exact hs₂ c (Ne.symm hac) (Ne.symm hbc) hcd
    · exact hs₁ k hka hkb hkc
  have hform := eq_smul_of_supp_two hab hsupp hz₁.2
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) (z₁ a) with h0 | h1
  · left
    rw [hform, h0, zero_smul, map_zero, sub_zero] at hy₁
    exact hy₁
  · right
    rw [hform, h1, one_smul] at hy₁
    exact hy₁

theorem eq_of_mem_Rg_T3 {a b c : Fin N} (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) {x x' u : V} (hx : x ∈ Rg (T3 φ a b c))
    (hx' : x' ∈ Rg (T3 φ a b c)) (h : x - u ∈ tildeVBot (AS φ F))
    (h' : x' - u ∈ tildeVBot (AS φ F)) : x = x' := by
  have hd : x - x' ∈ tildeVBot (AS φ F) := by
    have e : x - x' = (x - u) - (x' - u) := by abel
    rw [e]
    exact Submodule.sub_mem _ h h'
  exact sub_eq_zero.1 (eq_zero_of_mem_Rg_T3 ha hb hc hab hac hbc ((Rg _).sub_mem hx hx') hd)

theorem HeartW.conj_mem (h : HeartW φ F θ) {a b c : Fin N} (ha : a ∈ F) (hb : b ∈ F)
    (hab : a ≠ b) (hac : a ≠ c) (s : ↥G) (hs : pm φ s ∈ altOn (F : Set (Fin N)))
    (hsa : pm φ s a = a) (hsb : pm φ s b = b) {x : V} (hx : x ∈ Rg (T3 φ a b c))
    (hxT : x - θ (ev a + ev b) ∈ tildeVBot (AS φ F)) :
    (s : GLV V) x ∈ Rg (T3 φ a b (pm φ s c)) ∧
      (s : GLV V) x - θ (ev a + ev b) ∈ tildeVBot (AS φ F) := by
  have hsA : (s : GLV V) ∈ AS φ F := (coe_mem_AS φ).2 hs
  refine ⟨?_, ?_⟩
  · have := apply_mem_Rg_T3 φ s hab hac hx
    rwa [hsa, hsb] at this
  · have he := h.equiv s hs (ev a + ev b) (ev_add_ev_mem_Ew ha hb)
    rw [LinearMap.map_add (pa (pm φ s)) (ev a) (ev b), pa_ev, pa_ev, hsa, hsb] at he
    have e : (s : GLV V) x - θ (ev a + ev b) =
        (s : GLV V) (x - θ (ev a + ev b)) + ((s : GLV V) (θ (ev a + ev b)) -
          θ (ev a + ev b)) := by
      rw [map_sub]
      abel
    rw [e, apply_of_mem_tildeVBot hsA hxT]
    exact Submodule.add_mem _ hxT he

theorem HeartW.mem_Rg_of_mem_Rg (h : HeartW φ F θ) {a b c d e : Fin N} (ha : a ∈ F) (hb : b ∈ F)
    (hc : c ∈ F) (hd : d ∈ F) (he : e ∈ F) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) {x : V} (hx : x ∈ Rg (T3 φ a b c))
    (hxT : x - θ (ev a + ev b) ∈ tildeVBot (AS φ F)) : x ∈ Rg (T3 φ a b d) := by
  have hsA : cyc c d e ∈ alternatingGroup (Fin N) := cyc_mem_alternatingGroup hcd hce
  set s := elt φ (cyc c d e) with hs
  have hps : pm φ s = cyc c d e := pm_elt φ hsA
  have hsF : pm φ s ∈ altOn (F : Set (Fin N)) := by
    rw [hps]
    exact cyc_mem_altOn hc hd he hcd hce
  have hsa : pm φ s a = a := by rw [hps]; exact cyc_apply_of_ne hac had hae
  have hsb : pm φ s b = b := by rw [hps]; exact cyc_apply_of_ne hbc hbd hbe
  have hsc : pm φ s c = d := by rw [hps]; exact cyc_apply_left hcd hde
  have hsd : pm φ s d = e := by rw [hps]; exact cyc_apply_mid
  have hse : pm φ s e = c := by rw [hps]; exact cyc_apply_right hce hde
  have hsAS : (s : GLV V) ∈ AS φ F := (coe_mem_AS φ).2 hsF
  obtain ⟨hd1, hd2⟩ := h.conj_mem ha hb hab hac s hsF hsa hsb hx hxT
  rw [hsc] at hd1
  obtain ⟨he1, he2⟩ := h.conj_mem ha hb hab had s hsF hsa hsb hd1 hd2
  rw [hsd] at he1
  obtain ⟨hc1, hc2⟩ := h.conj_mem ha hb hab hae s hsF hsa hsb he1 he2
  rw [hse] at hc1
  have hback : (s : GLV V) ((s : GLV V) ((s : GLV V) x)) = x :=
    eq_of_mem_Rg_T3 ha hb hc hab hac hbc hc1 hx hc2 hxT
  have hdiff : ∀ {y z : V}, y - θ (ev a + ev b) ∈ tildeVBot (AS φ F) →
      z - θ (ev a + ev b) ∈ tildeVBot (AS φ F) → (s : GLV V) (y - z) = y - z := by
    intro y z hy hz
    refine apply_of_mem_tildeVBot hsAS ?_
    have e : y - z = (y - θ (ev a + ev b)) - (z - θ (ev a + ev b)) := by abel
    rw [e]
    exact Submodule.sub_mem _ hy hz
  set xd := (s : GLV V) x
  set xe := (s : GLV V) xd
  have h1 : xd - xe = x - xd := by
    rw [← hdiff hxT hd2, map_sub]
  have h2 : xe - x = xd - xe := by
    have := hdiff hd2 he2
    rw [map_sub, hback] at this
    exact this
  have hsum : (x - xd) + (xd - xe) + (xe - x) = 0 := by abel
  rw [h2, h1, add_self_V, zero_add] at hsum
  have hx' : x = xd := sub_eq_zero.1 hsum
  rw [hx']
  exact hd1

theorem HeartW.exists_vF (h : HeartW φ F θ) {a b c d e : Fin N} (ha : a ∈ F) (hb : b ∈ F)
    (hc : c ∈ F) (hd : d ∈ F) (he : e ∈ F) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) :
    ∃ x ∈ I4 φ a b c d, x - θ (ev a + ev b) ∈ tildeVBot (AS φ F) ∧ x ≠ 0 ∧
      ∀ y ∈ I4 φ a b c d, y = 0 ∨ y = x := by
  obtain ⟨x, hx, hxT⟩ := h.exists_mem_Rg ha hb hc hd hab hac had hbc hbd hcd
  have hxd := h.mem_Rg_of_mem_Rg ha hb hc hd he hab hac had hae hbc hbd hbe hcd hce hde hx hxT
  refine ⟨x, ⟨hx, hxd⟩, hxT, fun hx0 => ?_, fun y hy => ?_⟩
  · rw [hx0, zero_sub, neg_mem_iff] at hxT
    rcases (h.ker _ (ev_add_ev_mem_Ew ha hb)).1 hxT with h0 | hj
    · exact ev_add_ev_ne_zero hab h0
    · exact ev_add_ev_ne_jS hc (Ne.symm hac) (Ne.symm hbc) hj
  · rcases h.mem_T_or ha hb hc hd he hab hac had hbc hbd hcd (Ne.symm hae) (Ne.symm hbe)
      (Ne.symm hce) (Ne.symm hde) hy with hyT | hyT
    · exact Or.inl (eq_zero_of_mem_Rg_T3 ha hb hc hab hac hbc hy.1 hyT)
    · exact Or.inr (eq_of_mem_Rg_T3 ha hb hc hab hac hbc hy.1 hx hyT hxT)

end InF

end CFSG.CGT.Foote82.L24
