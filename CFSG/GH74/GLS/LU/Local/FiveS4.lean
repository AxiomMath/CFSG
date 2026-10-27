module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.GH74.GLS.LU.Local.Five

section S4

variable {M : Type} [Group M]

private theorem eq_one_of_mem_card_three_of_sq_eq_one {A V : Subgroup M} (hA : Nat.card A = 3)
    (hV2 : ∀ v ∈ V, v * v = 1) {x : M} (hxA : x ∈ A) (hxV : x ∈ V) : x = 1 := by
  have h3 : orderOf x ∣ 3 := hA ▸ A.orderOf_dvd_natCard hxA
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hV2 x hxV)
  have h1 : orderOf x ∣ Nat.gcd 3 2 := Nat.dvd_gcd h3 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using h1))

private theorem card_sylow_three_eq_three [Finite M] (hM : Nat.card M = 24) (T : Sylow 3 M) :
    Nat.card T = 3 := by
  rw [Sylow.card_eq_multiplicity, hM]
  have h1 : 1 ≤ Nat.factorization 24 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by norm_num)).mp (by norm_num)
  have h2 : ¬ 2 ≤ Nat.factorization 24 3 := fun h => by
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by norm_num)).mpr h
    norm_num at this
  have : Nat.factorization 24 3 = 1 := by omega
  rw [this, pow_one]

private theorem mul_comm_of_smul_eq [Finite M] {V : Subgroup M} [hVn : V.Normal]
    (hM : Nat.card M = 24) (hV2 : ∀ v ∈ V, v * v = 1) {T : Sylow 3 M} {c : M} (hcV : c ∈ V)
    (hcT : c • T = T) {t : M} (ht : t ∈ T) : c * t = t * c := by
  have hn := Sylow.smul_eq_iff_mem_normalizer.mp hcT
  have h1 : c * t * c⁻¹ ∈ T := (Subgroup.mem_set_normalizer_iff.mp hn t).mp ht
  have h2 : c * t * c⁻¹ * t⁻¹ ∈ T := T.mul_mem h1 (T.inv_mem ht)
  have h3 : c * t * c⁻¹ * t⁻¹ ∈ V := by
    have : c * (t * c⁻¹ * t⁻¹) ∈ V :=
      V.mul_mem hcV (hVn.conj_mem c⁻¹ (V.inv_mem hcV) t)
    simpa [mul_assoc] using this
  have h4 := eq_one_of_mem_card_three_of_sq_eq_one (card_sylow_three_eq_three hM T) hV2 h2 h3
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
  exact h4

private theorem eq_one_of_mul_comm_of_orderOf_eq_three [Finite M] {V : Subgroup M}
    [hVn : V.Normal] (hV : Nat.card V = 4) (hC : ∀ m : M, (∀ v ∈ V, m * v = v * m) → m ∈ V)
    {g c : M} (hg : orderOf g = 3) (hcV : c ∈ V) (hgc : g * c = c * g) : c = 1 := by
  by_contra hc1
  have hall : ∀ x ∈ V, g * x * g⁻¹ = x := by
    intro a ha
    by_contra hga
    have hg3 : g * g * g = 1 := by
      have := pow_orderOf_eq_one g
      rwa [hg, pow_three'] at this
    obtain ⟨b, hb⟩ : ∃ b, b = g * a * g⁻¹ := ⟨_, rfl⟩
    obtain ⟨b', hb'⟩ : ∃ b', b' = g * b * g⁻¹ := ⟨_, rfl⟩
    have hbV : b ∈ V := hb ▸ hVn.conj_mem a ha g
    have hb'V : b' ∈ V := hb' ▸ hVn.conj_mem b hbV g
    have hfix1 : g * 1 * g⁻¹ = 1 := by group
    have hfixc : g * c * g⁻¹ = c := by rw [hgc]; group
    have hσ3 : g * b' * g⁻¹ = a := by
      calc g * b' * g⁻¹ = (g * g * g) * a * (g * g * g)⁻¹ := by rw [hb', hb]; group
        _ = a := by rw [hg3]; group
    have hσinj : ∀ x y : M, g * x * g⁻¹ = g * y * g⁻¹ → x = y := by
      intro x y h
      simpa using h
    have hfd : ∀ x y : M, g * x * g⁻¹ = x → g * y * g⁻¹ ≠ y → x ≠ y := by
      rintro x y hx hy rfl
      exact hy hx
    have hba : b ≠ a := fun h => hga (hb ▸ h)
    have hb'b : b' ≠ b := by
      intro h
      apply hba
      apply hσinj
      rw [← hb, ← hb', h]
    have hb'a : b' ≠ a := by
      intro h
      apply hba
      calc b = g * a * g⁻¹ := hb
        _ = g * b' * g⁻¹ := by rw [h]
        _ = a := hσ3
    have nfa : g * a * g⁻¹ ≠ a := hga
    have nfb : g * b * g⁻¹ ≠ b := hb' ▸ hb'b
    have nfb' : g * b' * g⁻¹ ≠ b' := hσ3 ▸ hb'a.symm
    have h1a : 1 ≠ a := hfd 1 a hfix1 nfa
    have h1b : 1 ≠ b := hfd 1 b hfix1 nfb
    have h1b' : 1 ≠ b' := hfd 1 b' hfix1 nfb'
    have hca : c ≠ a := hfd c a hfixc nfa
    have hcb : c ≠ b := hfd c b hfixc nfb
    have hcb' : c ≠ b' := hfd c b' hfixc nfb'
    let f : Fin 5 → V := ![⟨1, V.one_mem⟩, ⟨c, hcV⟩, ⟨a, ha⟩, ⟨b, hbV⟩, ⟨b', hb'V⟩]
    have hf : Function.Injective f := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp [f] at h ⊢ <;>
        first | exact absurd h ‹_› | exact absurd h.symm ‹_›
    have := Nat.card_le_card_of_injective f hf
    simp [hV] at this
  have hgV : g ∈ V := hC g (fun v hv => by
    have := hall v hv
    rwa [mul_inv_eq_iff_eq_mul] at this)
  have := V.orderOf_dvd_natCard hgV
  rw [hg, hV] at this
  omega

private theorem card_sylow_three_eq_four [Finite M] {V : Subgroup M} [V.Normal]
    (hM : Nat.card M = 24) (hV : Nat.card V = 4) (hV2 : ∀ v ∈ V, v * v = 1)
    (hC : ∀ m : M, (∀ v ∈ V, m * v = v * m) → m ∈ V) : Nat.card (Sylow 3 M) = 4 := by
  obtain ⟨T⟩ : Nonempty (Sylow 3 M) := inferInstance
  have hT := card_sylow_three_eq_three hM T
  have hidx : (T : Subgroup M).index = 8 := by
    have h := Subgroup.card_mul_index (T : Subgroup M)
    have hT' : Nat.card (T : Subgroup M) = 3 := hT
    rw [hM, hT'] at h
    omega
  have hdvd : Nat.card (Sylow 3 M) ∣ 8 := hidx ▸ Sylow.card_dvd_index T
  have hmod : Nat.card (Sylow 3 M) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 M
  have hn : Nat.card (Sylow 3 M) = 1 ∨ Nat.card (Sylow 3 M) = 4 := by
    have hle : Nat.card (Sylow 3 M) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (Sylow 3 M) = n at *
    interval_cases n <;> simp_all [Nat.ModEq]
  rcases hn with h1 | h4
  · exfalso
    obtain ⟨hsub, _⟩ := Nat.card_eq_one_iff_unique.mp h1
    have hTV : (T : Subgroup M) ≤ V := by
      intro t ht
      apply hC
      intro v hv
      exact (mul_comm_of_smul_eq hM hV2 hv (Subsingleton.elim _ _) ht).symm
    have := Subgroup.card_dvd_of_le hTV
    rw [hT, hV] at this
    omega
  · exact h4

private theorem injective_toPermHom_sylow_three [Finite M] {V : Subgroup M}
    [hVn : V.Normal] (hM : Nat.card M = 24) (hV : Nat.card V = 4) (hV2 : ∀ v ∈ V, v * v = 1)
    (hC : ∀ m : M, (∀ v ∈ V, m * v = v * m) → m ∈ V) :
    Function.Injective (MulAction.toPermHom M (Sylow 3 M)) := by
  rw [injective_iff_map_eq_one]
  have hsm : ∀ m : M, MulAction.toPermHom M (Sylow 3 M) m = 1 → ∀ T : Sylow 3 M, m • T = T := by
    intro m hm T
    simpa using Equiv.ext_iff.mp hm T
  have claim : ∀ c ∈ V, MulAction.toPermHom M (Sylow 3 M) c = 1 → c = 1 := by
    intro c hcV hc
    obtain ⟨T⟩ : Nonempty (Sylow 3 M) := inferInstance
    have hT := card_sylow_three_eq_three hM T
    have h3 : 3 ∣ Nat.card T := by rw [hT]
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := T) 3 h3
    exact eq_one_of_mul_comm_of_orderOf_eq_three hV hC (g := (x : M))
      (by rw [Subgroup.orderOf_coe]; exact hx) hcV
      (mul_comm_of_smul_eq hM hV2 hcV (hsm c hc T) x.2).symm
  intro k hk
  have hkV : ∀ v ∈ V, k * v = v * k := by
    intro v hv
    have hx1 : k * v * k⁻¹ * v⁻¹ ∈ V := V.mul_mem (hVn.conj_mem v hv k) (V.inv_mem hv)
    have hx2 : MulAction.toPermHom M (Sylow 3 M) (k * v * k⁻¹ * v⁻¹) = 1 := by
      simp only [map_mul, map_inv, hk, inv_one, one_mul, mul_one, mul_inv_cancel]
    have := claim _ hx1 hx2
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  exact claim k (hC k hkV) hk

end S4

theorem exists_mulEquiv_perm_four_of_V4 {M : Type} [Group M] [Finite M] (V : Subgroup M)
    [V.Normal] (hM : Nat.card M = 24) (hV : Nat.card V = 4) (hV2 : ∀ v ∈ V, v * v = 1)
    (hC : ∀ m : M, (∀ v ∈ V, m * v = v * m) → m ∈ V) :
    Nonempty (M ≃* Equiv.Perm (Fin 4)) := by
  have hn : Nat.card (Sylow 3 M) = 4 := card_sylow_three_eq_four hM hV hV2 hC
  have hinj := injective_toPermHom_sylow_three hM hV hV2 hC
  let e : Sylow 3 M ≃ Fin 4 := Finite.equivFinOfCardEq hn
  let ψ : M →* Equiv.Perm (Fin 4) :=
    (e.permCongrHom : Equiv.Perm (Sylow 3 M) ≃* Equiv.Perm (Fin 4)).toMonoidHom.comp
      (MulAction.toPermHom M (Sylow 3 M))
  have hψ : Function.Injective ψ := e.permCongrHom.injective.comp hinj
  have hcard : Nat.card (Equiv.Perm (Fin 4)) ≤ Nat.card M := by
    rw [Nat.card_perm, hM]
    simp [Nat.factorial]
  exact ⟨MulEquiv.ofBijective ψ (hψ.bijective_of_nat_card_le hcard)⟩

end CFSG.GH74.GLS.LU.Local.Five
