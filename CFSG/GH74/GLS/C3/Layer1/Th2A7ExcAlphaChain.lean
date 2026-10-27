module

public import CFSG.GH74.GLS.C3.Layer1.Th2A7ExcAlphaStep
public import CFSG.GH74.GLS.C3.Layer1.Th2P43fPerm

public section

namespace CFSG.GH74.GLS.Th2.AlphaStep

open Equiv Equiv.Perm Subgroup CFSG.LieType.SteinbergBR.SmallAlt CFSG.GH74.GLS.Th2.P43f

theorem conj_trans {G : Type*} [Group G] {u v w : G} (h1 : ∃ g : G, g * u * g⁻¹ = v)
    (h2 : ∃ g : G, g * v * g⁻¹ = w) : ∃ g : G, g * u * g⁻¹ = w := by
  obtain ⟨g, hg⟩ := h1
  obtain ⟨h, hh⟩ := h2
  exact ⟨h * g, by rw [← hh, ← hg]; group⟩

theorem conj_symm {G : Type*} [Group G] {u v : G} (h : ∃ g : G, g * u * g⁻¹ = v) :
    ∃ g : G, g * v * g⁻¹ = u := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, by rw [← hg]; group⟩

theorem a7P_sq {j : Fin 8} (hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 6 ∨ j = 7) :
    a7P j * a7P j = 1 := by
  rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide

structure ChainData {G : Type*} [Group G] (C K : Subgroup G) (psi : G → Perm (Fin 7))
    (x z a p₁ s f f' : G) (i j : Fin 8) (τ₀ : Perm (Fin 7)) : Prop where
  psiD : PsiData C K psi
  hxC : x ∈ C
  hxx : x * x = 1
  hxK : ∀ k ∈ K, k * x = x * k
  hz : z ∈ K
  hzz : z * z = 1
  hzx : z * x = x * z
  hxz : a * z * a⁻¹ = x
  hp₁ : p₁ ∈ K
  hp₁p₁ : p₁ * p₁ = 1
  hs : s ∈ K
  hss : s * s = 1
  hzp₁ : z * p₁ = p₁ * z
  hzs : z * s = s * z
  hfa : a⁻¹ * f * a = p₁
  hfa' : a * f' * a⁻¹ = s
  hf : f ∈ C
  hf' : f' ∈ C
  hsf : s * f = f * s
  hp₁f' : p₁ * f' = f' * p₁
  hzf' : z * f' = f' * z
  psi_z : psi z = a7P 1
  psi_x : psi x = 1
  psi_p₁ : psi p₁ = a7P i
  psi_s : psi s = a7P j
  psi_f : psi f = τ₀
  psi_f' : psi f' = τ₀
  hi : i = 2 ∨ i = 3 ∨ i = 6 ∨ i = 7
  hj : j = 2 ∨ j = 3 ∨ j = 6 ∨ j = 7
  τ₀_sq : τ₀ * τ₀ = 1
  τ₀_comm : ∀ k : Fin 8, τ₀ * a7P k = a7P k * τ₀
  card1 : (a7P j * τ₀).support.card = τ₀.support.card
  card2 : (a7P 1 * τ₀).support.card = (a7P i * τ₀).support.card

namespace ChainData

variable {G : Type*} [Group G] {C K : Subgroup G} {psi : G → Perm (Fin 7)}
  {x z a p₁ s f f' : G} {i j : Fin 8} {τ₀ : Perm (Fin 7)}

theorem exists_conj_x_v (D : ChainData C K psi x z a p₁ s f f' i j τ₀) :
    ∃ g : G, g * x * g⁻¹ = z * x := by
  have hK := D.psiD.K_le
  have hzC : z ∈ C := hK D.hz
  have hp₁C : p₁ ∈ C := hK D.hp₁
  have hsC : s ∈ C := hK D.hs
  have hpm := D.psiD.mul
  have h11 : a7P 1 * a7P 1 = 1 := a7P_sq (Or.inl rfl)
  have hi5 : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 6 ∨ i = 7 := by
    rcases D.hi with h | h | h | h <;> simp [h]
  have hj5 : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 6 ∨ j = 7 := by
    rcases D.hj with h | h | h | h <;> simp [h]
  have hfeq : f = a * p₁ * a⁻¹ := by rw [← D.hfa]; group
  have hf'eq : f' = a⁻¹ * s * a := by rw [← D.hfa']; group
  have hza : a⁻¹ * x * a = z := by rw [← D.hxz]; group
  have hff : f * f = 1 := by
    calc f * f = a * (p₁ * p₁) * a⁻¹ := by rw [hfeq]; group
      _ = 1 := by rw [D.hp₁p₁]; group
  have hf'f' : f' * f' = 1 := by
    calc f' * f' = a⁻¹ * (s * s) * a := by rw [hf'eq]; group
      _ = 1 := by rw [D.hss]; group
  have hp₁z : (p₁ * z) * (p₁ * z) = 1 := by
    calc (p₁ * z) * (p₁ * z) = p₁ * (z * p₁) * z := by group
      _ = p₁ * (p₁ * z) * z := by rw [D.hzp₁]
      _ = (p₁ * p₁) * (z * z) := by group
      _ = 1 := by rw [D.hp₁p₁, D.hzz]; group
  have hsz : (s * z) * (s * z) = 1 := by
    calc (s * z) * (s * z) = s * (z * s) * z := by group
      _ = s * (s * z) * z := by rw [D.hzs]
      _ = (s * s) * (z * z) := by group
      _ = 1 := by rw [D.hss, D.hzz]; group
  have e0 : ∃ h : G, h * z * h⁻¹ = p₁ := by
    obtain ⟨ρ, hρs, hρ, -⟩ := a7P_rho D.hi
    have hmK : p₁ * z ∈ K := K.mul_mem D.hp₁ D.hz
    have hfm : (p₁ * z) * z = z * (p₁ * z) := by
      have h1 : (p₁ * z) * z = p₁ := by rw [mul_assoc, D.hzz, mul_one]
      have h2 : z * (p₁ * z) = p₁ := by
        calc z * (p₁ * z) = (z * p₁) * z := by group
          _ = (p₁ * z) * z := by rw [D.hzp₁]
          _ = p₁ := h1
      rw [h1, h2]
    obtain ⟨h, hh⟩ := D.psiD.exists_conj_step hzC hmK D.hzz hp₁z hfm hρs (by
      rw [hpm p₁ hp₁C z hzC, D.psi_p₁, D.psi_z, mul_assoc (a7P i), h11, mul_one]
      exact hρ)
    exact ⟨h, by rw [hh, mul_assoc, D.hzz, mul_one]⟩
  have e1 : ∃ h : G, h * f * h⁻¹ = s * f := by
    have hs2 : a7P j * a7P j = 1 := a7P_sq hj5
    have hσ' : (a7P j * τ₀) * (a7P j * τ₀) = 1 := by
      calc (a7P j * τ₀) * (a7P j * τ₀) = a7P j * (τ₀ * a7P j) * τ₀ := by group
        _ = a7P j * (a7P j * τ₀) * τ₀ := by rw [D.τ₀_comm j]
        _ = (a7P j * a7P j) * (τ₀ * τ₀) := by group
        _ = 1 := by rw [hs2, D.τ₀_sq]; group
    obtain ⟨g, hg, hgc⟩ := exists_even_conj_of_card_support_eq D.τ₀_sq hσ' D.card1.symm
    exact D.psiD.exists_conj_step D.hf D.hs hff D.hss D.hsf hg (by rw [D.psi_f, D.psi_s]; exact hgc)
  have e2 : ∃ h : G, h * (z * f') * h⁻¹ = p₁ * f' := by
    have hi2 : a7P i * a7P i = 1 := a7P_sq hi5
    have hzfC : z * f' ∈ C := C.mul_mem hzC D.hf'
    have hmK : p₁ * z ∈ K := K.mul_mem D.hp₁ D.hz
    have hzff : (z * f') * (z * f') = 1 := by
      calc z * f' * (z * f') = z * (f' * z) * f' := by group
        _ = z * (z * f') * f' := by rw [← D.hzf']
        _ = (z * z) * (f' * f') := by group
        _ = 1 := by rw [D.hzz, hf'f']; group
    have hfm : (p₁ * z) * (z * f') = (z * f') * (p₁ * z) := by
      have h1 : (p₁ * z) * (z * f') = p₁ * f' := by
        calc (p₁ * z) * (z * f') = p₁ * (z * z) * f' := by group
          _ = p₁ * f' := by rw [D.hzz]; group
      have h2 : (z * f') * (p₁ * z) = p₁ * f' := by
        calc (z * f') * (p₁ * z) = z * (f' * p₁) * z := by group
          _ = z * (p₁ * f') * z := by rw [D.hp₁f']
          _ = (z * p₁) * f' * z := by group
          _ = (p₁ * z) * f' * z := by rw [D.hzp₁]
          _ = p₁ * (z * f') * z := by group
          _ = p₁ * (f' * z) * z := by rw [D.hzf']
          _ = p₁ * f' * (z * z) := by group
          _ = p₁ * f' := by rw [D.hzz]; group
      rw [h1, h2]
    have hσ : (a7P 1 * τ₀) * (a7P 1 * τ₀) = 1 := by
      calc (a7P 1 * τ₀) * (a7P 1 * τ₀) = a7P 1 * (τ₀ * a7P 1) * τ₀ := by group
        _ = a7P 1 * (a7P 1 * τ₀) * τ₀ := by rw [D.τ₀_comm 1]
        _ = (a7P 1 * a7P 1) * (τ₀ * τ₀) := by group
        _ = 1 := by rw [h11, D.τ₀_sq]; group
    have hσ' : (a7P i * τ₀) * (a7P i * τ₀) = 1 := by
      calc (a7P i * τ₀) * (a7P i * τ₀) = a7P i * (τ₀ * a7P i) * τ₀ := by group
        _ = a7P i * (a7P i * τ₀) * τ₀ := by rw [D.τ₀_comm i]
        _ = (a7P i * a7P i) * (τ₀ * τ₀) := by group
        _ = 1 := by rw [hi2, D.τ₀_sq]; group
    obtain ⟨g, hg, hgc⟩ := exists_even_conj_of_card_support_eq hσ hσ' D.card2
    obtain ⟨h, hh⟩ := D.psiD.exists_conj_step hzfC hmK hzff hp₁z hfm hg (by
      rw [hpm z hzC f' D.hf', hpm p₁ hp₁C z hzC, D.psi_z, D.psi_f', D.psi_p₁, mul_assoc (a7P i),
        ← mul_assoc (a7P 1), h11, one_mul]
      exact hgc)
    refine ⟨h, ?_⟩
    rw [hh]
    calc p₁ * z * (z * f') = p₁ * (z * z) * f' := by group
      _ = p₁ * f' := by rw [D.hzz]; group
  have e3 : ∃ h : G, h * (z * x) * h⁻¹ = s * x := by
    obtain ⟨ρ, hρs, hρ, -⟩ := a7P_rho D.hj
    have hzxC : z * x ∈ C := C.mul_mem hzC D.hxC
    have hmK : s * z ∈ K := K.mul_mem D.hs D.hz
    have hsx : s * x = x * s := D.hxK s D.hs
    have hzxzx : (z * x) * (z * x) = 1 := by
      calc z * x * (z * x) = z * (x * z) * x := by group
        _ = z * (z * x) * x := by rw [← D.hzx]
        _ = (z * z) * (x * x) := by group
        _ = 1 := by rw [D.hzz, D.hxx]; group
    have h1 : (s * z) * (z * x) = s * x := by
      calc (s * z) * (z * x) = s * (z * z) * x := by group
        _ = s * x := by rw [D.hzz]; group
    have hfm : (s * z) * (z * x) = (z * x) * (s * z) := by
      have h2 : (z * x) * (s * z) = s * x := by
        calc (z * x) * (s * z) = z * (x * s) * z := by group
          _ = z * (s * x) * z := by rw [hsx]
          _ = (z * s) * x * z := by group
          _ = (s * z) * x * z := by rw [D.hzs]
          _ = s * (z * x) * z := by group
          _ = s * (x * z) * z := by rw [D.hzx]
          _ = s * x * (z * z) := by group
          _ = s * x := by rw [D.hzz]; group
      rw [h1, h2]
    obtain ⟨h, hh⟩ := D.psiD.exists_conj_step hzxC hmK hzxzx hsz hfm hρs (by
      rw [hpm z hzC x D.hxC, hpm s hsC z hzC, D.psi_z, D.psi_x, D.psi_s, mul_one,
        mul_assoc (a7P j), h11, mul_one]
      exact hρ)
    exact ⟨h, by rw [hh, h1]⟩
  obtain ⟨h₀, hh₀⟩ := e0
  have cA : ∃ g : G, g * x * g⁻¹ = f := by
    refine ⟨a * h₀ * a⁻¹, ?_⟩
    calc a * h₀ * a⁻¹ * x * (a * h₀ * a⁻¹)⁻¹ = a * (h₀ * (a⁻¹ * x * a) * h₀⁻¹) * a⁻¹ := by group
      _ = a * (h₀ * z * h₀⁻¹) * a⁻¹ := by rw [hza]
      _ = a * p₁ * a⁻¹ := by rw [hh₀]
      _ = f := hfeq.symm
  have cC : ∃ g : G, g * (s * f) * g⁻¹ = f' * p₁ := by
    refine ⟨a⁻¹, ?_⟩
    calc a⁻¹ * (s * f) * a⁻¹⁻¹ = (a⁻¹ * s * a) * (a⁻¹ * f * a) := by group
      _ = f' * p₁ := by rw [← hf'eq, D.hfa]
  have cD : ∃ g : G, g * (p₁ * f') * g⁻¹ = z * f' := conj_symm e2
  have cE : ∃ g : G, g * (z * f') * g⁻¹ = x * s := by
    refine ⟨a, ?_⟩
    calc a * (z * f') * a⁻¹ = (a * z * a⁻¹) * (a * f' * a⁻¹) := by group
      _ = x * s := by rw [D.hxz, D.hfa']
  have cF : ∃ g : G, g * (s * x) * g⁻¹ = z * x := conj_symm e3
  have hsx : s * x = x * s := D.hxK s D.hs
  have hp₁f'' : f' * p₁ = p₁ * f' := D.hp₁f'.symm
  rw [hp₁f''] at cC
  rw [← hsx] at cE
  exact conj_trans cA (conj_trans e1 (conj_trans cC (conj_trans cD (conj_trans cE cF))))

end ChainData

end CFSG.GH74.GLS.Th2.AlphaStep
