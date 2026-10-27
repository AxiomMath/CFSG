module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreCls

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore

open CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem pow_mod_three {G : Type*} [Group G] {ρ : G} (h : ρ ^ 3 = 1) (n : ℕ) :
    ρ ^ (n % 3) = ρ ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, h, one_pow, mul_one]

theorem exists_gen_data {n : ℕ} {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian 3 E)
    {X : Fin n → Submodule (ZMod 2) V} (hinv : ∀ i, Inv2 E (X i))
    (hirr : ∀ i, IsIrrE E (X i)) :
    ∃ ρf : Fin n → (V ≃ₗ[ZMod 2] V), ∀ i, ρf i ∈ E ∧
      ((Module.finrank (ZMod 2) (X i) = 1 ∧ ∀ g ∈ E, ∀ x ∈ X i, g x = x) ∨
        (Module.finrank (ZMod 2) (X i) = 2 ∧ (∀ x ∈ X i, ρf i x = x → x = 0) ∧
          (∀ x ∈ X i, ρf i (ρf i x) + ρf i x + x = 0) ∧
          (∀ g ∈ E, ∃ k : Fin 3, ∀ x ∈ X i, g x = (ρf i ^ (k : ℕ)) x))) := by
  have h : ∀ i, ∃ ρ : V ≃ₗ[ZMod 2] V, ρ ∈ E ∧
      ((Module.finrank (ZMod 2) (X i) = 1 ∧ ∀ g ∈ E, ∀ x ∈ X i, g x = x) ∨
        (Module.finrank (ZMod 2) (X i) = 2 ∧ (∀ x ∈ X i, ρ x = x → x = 0) ∧
          (∀ x ∈ X i, ρ (ρ x) + ρ x + x = 0) ∧
          (∀ g ∈ E, ∃ k : Fin 3, ∀ x ∈ X i, g x = (ρ ^ (k : ℕ)) x))) := by
    intro i
    rcases irr_trichotomy hE (hinv i) (hirr i) with ⟨htriv, hfr⟩ | ⟨ρ, hρ, hfr, hfix, hquad, hpow⟩
    · exact ⟨1, E.one_mem, Or.inl ⟨hfr, htriv⟩⟩
    · exact ⟨ρ, hρ, Or.inr ⟨hfr, hfix, hquad, hpow⟩⟩
  choose ρf hρf using h
  exact ⟨ρf, hρf⟩

open Classical in
noncomputable def expo {n : ℕ} (ρf : Fin n → (V ≃ₗ[ZMod 2] V)) (X : Fin n → Submodule (ZMod 2) V)
    (i : Fin n) (g : V ≃ₗ[ZMod 2] V) : Fin 3 :=
  if h : ∃ k : Fin 3, ∀ x ∈ X i, g x = (ρf i ^ (k : ℕ)) x then h.choose else 0

theorem expo_spec {n : ℕ} {ρf : Fin n → (V ≃ₗ[ZMod 2] V)} {X : Fin n → Submodule (ZMod 2) V}
    {i : Fin n} {g : V ≃ₗ[ZMod 2] V} (h : ∃ k : Fin 3, ∀ x ∈ X i, g x = (ρf i ^ (k : ℕ)) x) :
    ∀ x ∈ X i, g x = (ρf i ^ ((expo ρf X i g : Fin 3) : ℕ)) x := by
  have hd : expo ρf X i g = h.choose := by
    unfold expo
    rw [dif_pos h]
  rw [hd]
  exact h.choose_spec

theorem expo_unique {n : ℕ} {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian 3 E)
    {ρf : Fin n → (V ≃ₗ[ZMod 2] V)} {X : Fin n → Submodule (ZMod 2) V}
    {i : Fin n} (hirr : IsIrrE E (X i)) (hρ : ρf i ∈ E)
    (hfix : ∀ x ∈ X i, ρf i x = x → x = 0) {k k' : Fin 3}
    (h : ∀ x ∈ X i, (ρf i ^ (k : ℕ)) x = (ρf i ^ (k' : ℕ)) x) : k = k' :=
  pow_fin3_unique hE hirr hρ hfix h

theorem expo_mul {n : ℕ} {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian 3 E)
    {ρf : Fin n → (V ≃ₗ[ZMod 2] V)} {X : Fin n → Submodule (ZMod 2) V}
    (hinv : ∀ i, Inv2 E (X i)) {i : Fin n} (hirr : IsIrrE E (X i)) (hρ : ρf i ∈ E)
    (hfix : ∀ x ∈ X i, ρf i x = x → x = 0)
    (hpow : ∀ g ∈ E, ∃ k : Fin 3, ∀ x ∈ X i, g x = (ρf i ^ (k : ℕ)) x)
    {g h : V ≃ₗ[ZMod 2] V} (hg : g ∈ E) (hh : h ∈ E) :
    expo ρf X i (g * h) = expo ρf X i g + expo ρf X i h := by
  have hρ3 : ρf i ^ 3 = 1 := pow3_eq_one_of_mem hE hρ
  have hgh : g * h ∈ E := E.mul_mem hg hh
  apply expo_unique hE hirr hρ hfix
  intro x hx
  have hhx : h x ∈ X i := hinv i h hh x hx
  calc (ρf i ^ ((expo ρf X i (g * h) : Fin 3) : ℕ)) x
      = (g * h) x := (expo_spec (hpow (g * h) hgh) x hx).symm
    _ = g (h x) := LinearEquiv.mul_apply _ _ _
    _ = (ρf i ^ ((expo ρf X i g : Fin 3) : ℕ)) (h x) := expo_spec (hpow g hg) (h x) hhx
    _ = (ρf i ^ ((expo ρf X i g : Fin 3) : ℕ))
          ((ρf i ^ ((expo ρf X i h : Fin 3) : ℕ)) x) := by
        rw [expo_spec (hpow h hh) x hx]
    _ = (ρf i ^ (((expo ρf X i g : Fin 3) : ℕ) + ((expo ρf X i h : Fin 3) : ℕ))) x := by
        rw [pow_add, LinearEquiv.mul_apply]
    _ = (ρf i ^ ((expo ρf X i g + expo ρf X i h : Fin 3) : ℕ)) x := by
        rw [Fin.val_add, pow_mod_three hρ3]

theorem eq_of_expo_eq {n : ℕ} {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian 3 E)
    {ρf : Fin n → (V ≃ₗ[ZMod 2] V)} {X : Fin n → Submodule (ZMod 2) V}
    (hρf : ∀ i, ρf i ∈ E ∧
      ((Module.finrank (ZMod 2) (X i) = 1 ∧ ∀ g ∈ E, ∀ x ∈ X i, g x = x) ∨
        (Module.finrank (ZMod 2) (X i) = 2 ∧ (∀ x ∈ X i, ρf i x = x → x = 0) ∧
          (∀ x ∈ X i, ρf i (ρf i x) + ρf i x + x = 0) ∧
          (∀ g ∈ E, ∃ k : Fin 3, ∀ x ∈ X i, g x = (ρf i ^ (k : ℕ)) x)))) 
    (hsup : iSup X = ⊤) {g h : V ≃ₗ[ZMod 2] V} (hg : g ∈ E) (hh : h ∈ E)
    (hexp : ∀ i, Module.finrank (ZMod 2) (X i) = 2 → expo ρf X i g = expo ρf X i h) :
    g = h := by
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ ⨆ i, X i := by rw [hsup]; trivial
  refine Submodule.iSup_induction X (motive := fun v => g v = h v) hv ?_ ?_ ?_
  · intro i x hx
    rcases (hρf i).2 with hline | hplane
    · rw [hline.2 g hg x hx, hline.2 h hh x hx]
    · rw [expo_spec (hplane.2.2.2 g hg) x hx, expo_spec (hplane.2.2.2 h hh) x hx,
        hexp i hplane.1]
  · simp
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

theorem card_le_planes {n : ℕ} {E : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype E]
    (hE : IsElemAbelian 3 E)
    {ρf : Fin n → (V ≃ₗ[ZMod 2] V)} {X : Fin n → Submodule (ZMod 2) V}
    (hρf : ∀ i, ρf i ∈ E ∧
      ((Module.finrank (ZMod 2) (X i) = 1 ∧ ∀ g ∈ E, ∀ x ∈ X i, g x = x) ∨
        (Module.finrank (ZMod 2) (X i) = 2 ∧ (∀ x ∈ X i, ρf i x = x → x = 0) ∧
          (∀ x ∈ X i, ρf i (ρf i x) + ρf i x + x = 0) ∧
          (∀ g ∈ E, ∃ k : Fin 3, ∀ x ∈ X i, g x = (ρf i ^ (k : ℕ)) x))))
    (hsup : iSup X = ⊤) (hdim : Module.finrank (ZMod 2) V = ∑ i, Module.finrank (ZMod 2) (X i)) :
    Fintype.card E ≤ 3 ^ Fintype.card {i // Module.finrank (ZMod 2) (X i) = 2} ∧
      2 * Fintype.card {i // Module.finrank (ZMod 2) (X i) = 2} ≤ Module.finrank (ZMod 2) V := by
  constructor
  · let Θ : E → ({i // Module.finrank (ZMod 2) (X i) = 2} → Fin 3) :=
      fun g p => expo ρf X p.1 (g : V ≃ₗ[ZMod 2] V)
    have hinj : Function.Injective Θ := by
      intro g h hgh
      apply Subtype.ext
      apply eq_of_expo_eq hE hρf hsup g.2 h.2
      intro i hi
      have := congrFun hgh ⟨i, hi⟩
      exact this
    have := Fintype.card_le_of_injective Θ hinj
    simpa [Fintype.card_fun] using this
  · rw [hdim]
    have h1 : ∑ i, (if Module.finrank (ZMod 2) (X i) = 2 then 2 else 0) =
        2 * Fintype.card {i // Module.finrank (ZMod 2) (X i) = 2} := by
      rw [Fintype.card_subtype, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, smul_eq_mul, mul_comm]
    rw [← h1]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h2
    · rw [h2]
    · exact Nat.zero_le _

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore

end
