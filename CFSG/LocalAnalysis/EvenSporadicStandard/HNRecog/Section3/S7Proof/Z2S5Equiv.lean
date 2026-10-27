module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Z2S5Set

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma s7e_perm_fin5_eq_one_of_forall_commute_swap
    {σ : Sym 5} (hσ : ∀ i j : Fin 5, σ * Equiv.swap i j = Equiv.swap i j * σ) : σ = 1 := by
  apply Equiv.ext
  intro i
  change σ i = i
  by_contra hne
  have hik : i ≠ σ i := fun h => hne h.symm
  have hlt : ({i, σ i} : Finset (Fin 5)).card < Fintype.card (Fin 5) := by
    rw [Finset.card_insert_of_notMem (by simpa using hik), Finset.card_singleton]
    simp
  obtain ⟨j, -, hjnot⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := ({i, σ i} : Finset (Fin 5)))
      (t := Finset.univ) (by simpa using hlt)
  have hji : j ≠ i := fun h => hjnot (by simp [h])
  have hjk : j ≠ σ i := fun h => hjnot (by simp [h])
  have h := congrArg (fun p : Sym 5 => p i) (hσ i j)
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at h
  rw [Equiv.swap_apply_of_ne_of_ne hne hjk.symm] at h
  exact hji (σ.injective h)

private lemma s7e_snd_eq_one_of_mem_center
    {z : Z 2 × Sym 5} (hz : ∀ g : Z 2 × Sym 5, g * z = z * g) : z.2 = 1 := by
  apply s7e_perm_fin5_eq_one_of_forall_commute_swap
  intro i j
  exact (congrArg Prod.snd (hz (1, Equiv.swap i j))).symm

private lemma s7e_eq_one_or_zeta_of_mem_center
    {z : Z 2 × Sym 5} (hz : ∀ g : Z 2 × Sym 5, g * z = z * g)
    (hz2 : z ^ 2 = 1) : z = 1 ∨ z = zetaZ2S5 := by
  have h2 : z.2 = 1 := s7e_snd_eq_one_of_mem_center hz
  have hgen : ∀ a : Z 2, a ^ 2 = 1 → a = 1 ∨ a = Multiplicative.ofAdd 1 := by decide
  have hp : z.1 ^ 2 = 1 := by
    have := congrArg Prod.fst hz2
    simpa using this
  rcases hgen z.1 hp with h1 | h1
  · left; exact Prod.ext h1 h2
  · right; exact Prod.ext h1 h2

theorem s7_closure_top_of_equiv {M : Type} [Group M] (φ : M ≃* Z 2 × Sym 5) (Y : Set M)
    (hinv : ∀ y ∈ Y, y ^ 2 = 1 ∧ y ≠ 1) (hnorm : ∀ y ∈ Y, ∀ m : M, m * y * m⁻¹ ∈ Y)
    (h3 : ∀ y ∈ Y, ∀ y' ∈ Y, (y * y') ^ 3 = 1 ∨ (y * y') ^ 2 = 1) {d : M} (hd : d ∈ Y)
    (hdc : ∀ m : M, m * d = d * m) (ht : ∃ t ∈ Y, t ≠ d) : Subgroup.closure Y = ⊤ := by
  have hcent : ∀ g : Z 2 × Sym 5, g * φ d = φ d * g := by
    intro g
    have h := congrArg φ (hdc (φ.symm g))
    simpa using h
  have hphi2 : φ d ^ 2 = 1 := by
    rw [← map_pow, (hinv d hd).1, map_one]
  have hphi1 : φ d ≠ 1 := fun h =>
    (hinv d hd).2 (φ.injective (by rw [h, map_one]))
  have hphid : φ d = zetaZ2S5 := by
    rcases s7e_eq_one_or_zeta_of_mem_center hcent hphi2 with h1 | hz
    · exact absurd h1 hphi1
    · exact hz
  have hzeta_cent : ∀ g : Z 2 × Sym 5, g * zetaZ2S5 = zetaZ2S5 * g := by
    intro g
    rw [← hphid]
    exact hcent g
  let X : Set (Z 2 × Sym 5) := {x | x ∈ φ '' Y ∧ x ≠ zetaZ2S5}
  obtain ⟨t, htY, htd⟩ := ht
  have htX : φ t ∈ X := by
    refine ⟨⟨t, htY, rfl⟩, ?_⟩
    intro h
    exact htd (φ.injective (by rw [h, hphid]))
  have hXne : X.Nonempty := ⟨φ t, htX⟩
  have hconj : ∀ g x : Z 2 × Sym 5, x ∈ X → g * x * g⁻¹ ∈ X := by
    intro g x hx
    obtain ⟨⟨y, hyY, hyx⟩, hxne⟩ := hx
    refine ⟨?_, ?_⟩
    · refine ⟨φ.symm g * y * (φ.symm g)⁻¹, hnorm y hyY (φ.symm g), ?_⟩
      rw [← hyx, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    · intro hgx
      apply hxne
      have hgx1 : g * x = zetaZ2S5 * g := (mul_inv_eq_iff_eq_mul).mp hgx
      calc x = g⁻¹ * (g * x) := (inv_mul_cancel_left g x).symm
        _ = g⁻¹ * (zetaZ2S5 * g) := congrArg (fun w => g⁻¹ * w) hgx1
        _ = (g⁻¹ * zetaZ2S5) * g := (mul_assoc g⁻¹ zetaZ2S5 g).symm
        _ = (zetaZ2S5 * g⁻¹) * g := congrArg (fun w => w * g) (hzeta_cent g⁻¹)
        _ = zetaZ2S5 * (g⁻¹ * g) := mul_assoc zetaZ2S5 g⁻¹ g
        _ = zetaZ2S5 * 1 := congrArg (fun w => zetaZ2S5 * w) (inv_mul_cancel g)
        _ = zetaZ2S5 := mul_one zetaZ2S5
  have hinvX : ∀ x ∈ X, x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ zetaZ2S5 := by
    intro x hx
    obtain ⟨⟨y, hyY, hyx⟩, hxne⟩ := hx
    obtain ⟨hy2, hy1⟩ := hinv y hyY
    refine ⟨?_, ?_, hxne⟩
    · rw [← hyx, ← map_pow, hy2, map_one]
    · intro h
      apply hy1
      apply φ.injective
      rw [hyx, h, map_one]
  have hins : insert zetaZ2S5 X = φ '' Y := by
    ext z
    constructor
    · intro hz
      rcases hz with hz | hz
      · exact ⟨d, hd, by rw [hz]; exact hphid⟩
      · exact hz.1
    · rintro ⟨y, hyY, rfl⟩
      by_cases hy : φ y = zetaZ2S5
      · exact Or.inl hy
      · exact Or.inr ⟨⟨y, hyY, rfl⟩, hy⟩
  have h3X : ∀ x ∈ insert zetaZ2S5 X, ∀ y ∈ insert zetaZ2S5 X,
      (x * y) ^ 3 = 1 ∨ (x * y) ^ 2 = 1 := by
    intro x hx y hy
    rw [hins] at hx hy
    obtain ⟨x', hx'Y, hx'⟩ := hx
    obtain ⟨y', hy'Y, hy'⟩ := hy
    rcases h3 x' hx'Y y' hy'Y with h | h
    · left
      rw [← hx', ← hy', ← map_mul, ← map_pow, h, map_one]
    · right
      rw [← hx', ← hy', ← map_mul, ← map_pow, h, map_one]
  obtain ⟨ε, hXε⟩ := s7_eq_swapSet hXne hconj hinvX h3X
  have hclos : Subgroup.closure (φ '' Y) = ⊤ := by
    rw [← hins, hXε]
    exact s7_closure_insert_swapSet ε
  have hmap : (Subgroup.closure Y).map φ.toMonoidHom = ⊤ := by
    rw [MonoidHom.map_closure]
    exact hclos
  rw [Subgroup.eq_top_iff']
  intro m
  have hm' : φ m ∈ (Subgroup.closure Y).map φ.toMonoidHom := by
    rw [hmap]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_map] at hm'
  obtain ⟨k, hk, hkφ⟩ := hm'
  rw [φ.injective hkφ] at hk
  exact hk

end CFSG.EvenSporadicStandard.HNRecog.Section3
