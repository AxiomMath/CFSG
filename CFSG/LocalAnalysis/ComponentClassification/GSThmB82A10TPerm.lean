module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29M

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.GSThmB.Catalog82A10
  CFSG.ComponentClassification.GSThmB.P29.A10

theorem false_of_fixedPoint {m : ℕ} {a x v w l b : Equiv.Perm (Fin m)} {Δ : Finset (Fin m)}
    (hab : a = l * b) (hl : ∀ i ∉ Δ, l i = i) (hbΔ : ∀ i ∈ Δ, b i = i)
    (hF' : ∀ i ∉ Δ, b i ≠ i) (hv : ∀ i ∈ Δ, v i = i)
    (hw : ∃ p ∈ Δ, l p = p ∧ w p ≠ p) (hxa : x * a = a * x) (hxv : x⁻¹ * v * x = w) :
    False := by
  obtain ⟨p, hpΔ, hlp, hwp⟩ := hw
  have hfix : ∀ i, a i = i → i ∈ Δ := by
    intro i hi
    by_contra hiΔ
    have hbi : b i ∉ Δ := fun h => hiΔ (by rwa [b.injective (hbΔ _ h)] at h)
    have hai : a i = b i := by rw [hab, Perm.mul_apply, hl _ hbi]
    exact hF' i hiΔ (hai.symm.trans hi)
  have hap : a p = p := by rw [hab, Perm.mul_apply, hbΔ p hpΔ, hlp]
  have hxp : a (x p) = x p := by
    have h := DFunLike.congr_fun hxa p
    rw [Perm.mul_apply, Perm.mul_apply, hap] at h
    exact h.symm
  apply hwp
  rw [← hxv, Perm.mul_apply, Perm.mul_apply, hv _ (hfix _ hxp)]
  exact x.symm_apply_apply p

abbrev z0 : Perm (Fin 10) := swap 4 5 * swap 6 7

abbrev r0 : Perm (Fin 10) := swap 8 9

@[expose] def U0 : Subgroup (Perm (Fin 10)) := P ⊓ alternatingGroup (Fin 10)

@[expose] def D0 : Subgroup (Perm (Fin 10)) := P ⊓ altOn fixTwo

@[expose] def E8 : Finset (Perm (Fin 10)) :=
  {1, sigmaTwo, z0, sigmaTwo * z0, r0, sigmaTwo * r0, z0 * r0, sigmaTwo * z0 * r0}

private theorem mem_U0_of {w : W} {u : Perm (Fin 10)} (hw : phiFun w = u) (hs : sign u = 1) :
    u ∈ U0 :=
  Subgroup.mem_inf.mpr ⟨mem_P.mpr ⟨w, hw⟩, mem_alternatingGroup.mpr hs⟩

private theorem r_two_comm :
    ∀ x : DihedralGroup 4, DihedralGroup.r 2 * x = x * DihedralGroup.r 2 := by
  decide

private theorem phi_comm {c1 c2 : DihedralGroup 4} (h1 : c1 = 1 ∨ c1 = DihedralGroup.r 2)
    (h2 : c2 = 1 ∨ c2 = DihedralGroup.r 2) (c3 : Multiplicative (ZMod 2)) {e : Perm (Fin 10)}
    (he : phiFun ((c1, c2), c3) = e) : ∀ u ∈ U0, e * u = u * e := by
  have hc : ∀ x : DihedralGroup 4, x = 1 ∨ x = DihedralGroup.r 2 → ∀ y, x * y = y * x := by
    rintro x (rfl | rfl) y
    · rw [one_mul, mul_one]
    · exact r_two_comm y
  intro u hu
  obtain ⟨⟨⟨x, y⟩, z⟩, rfl⟩ := mem_P.mp (Subgroup.mem_inf.mp hu).1
  subst he
  rw [← phi_apply, ← phi_apply, ← map_mul phi, ← map_mul phi]
  congr 1
  change ((c1 * x, c2 * y), c3 * z) = ((x * c1, y * c2), z * c3)
  rw [hc c1 h1, hc c2 h2, mul_comm c3]

private theorem comm_E8 : ∀ e ∈ E8, ∀ u ∈ U0, e * u = u * e := by
  intro e he
  simp only [E8, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact phi_comm (.inl rfl) (.inl rfl) 1 (by decide)
  · exact phi_comm (.inr rfl) (.inl rfl) 1 (by decide)
  · exact phi_comm (.inl rfl) (.inr rfl) 1 (by decide)
  · exact phi_comm (.inr rfl) (.inr rfl) 1 (by decide)
  · exact phi_comm (.inl rfl) (.inl rfl) (.ofAdd 1) (by decide)
  · exact phi_comm (.inr rfl) (.inl rfl) (.ofAdd 1) (by decide)
  · exact phi_comm (.inl rfl) (.inr rfl) (.ofAdd 1) (by decide)
  · exact phi_comm (.inr rfl) (.inr rfl) (.ofAdd 1) (by decide)

private theorem apply_comm {g u : Perm (Fin 10)} (h : g * u = u * g) (i : Fin 10) :
    g (u i) = u (g i) :=
  DFunLike.congr_fun h i

private theorem apply_fix {g u : Perm (Fin 10)} (h : g * u = u * g) {i : Fin 10}
    (hi : u i = i) : u (g i) = g i := by
  rw [← apply_comm h, hi]

private theorem agree_of_comm {g h u : Perm (Fin 10)} (hg : g * u = u * g)
    (hh : h * u = u * h) {i j : Fin 10} (hij : u i = j) (hi : g i = h i) : g j = h j := by
  rw [← hij, apply_comm hg, apply_comm hh, hi]

private theorem mem_u1 : (swap 2 3 * swap 4 5 : Perm (Fin 10)) ∈ U0 :=
  mem_U0_of (w := ((.sr 2, .sr 0), 1)) (by decide) (by decide)

private theorem mem_u2 : (swap 2 3 * swap 8 9 : Perm (Fin 10)) ∈ U0 :=
  mem_U0_of (w := ((.sr 2, 1), .ofAdd 1)) (by decide) (by decide)

private theorem mem_u3 : (swap 2 3 * swap 6 7 : Perm (Fin 10)) ∈ U0 :=
  mem_U0_of (w := ((.sr 2, .sr 2), 1)) (by decide) (by decide)

private theorem mem_u4 : (swap 0 1 * swap 6 7 : Perm (Fin 10)) ∈ U0 :=
  mem_U0_of (w := ((.sr 0, .sr 2), 1)) (by decide) (by decide)

private theorem mem_u5 : (swap 6 7 * swap 8 9 : Perm (Fin 10)) ∈ U0 :=
  mem_U0_of (w := ((1, .sr 2), .ofAdd 1)) (by decide) (by decide)

private theorem mem_u6 : (swap 0 1 * swap 4 5 : Perm (Fin 10)) ∈ U0 :=
  mem_U0_of (w := ((.sr 0, .sr 0), 1)) (by decide) (by decide)

private theorem mem_u7 : (swap 0 1 * swap 8 9 : Perm (Fin 10)) ∈ U0 :=
  mem_U0_of (w := ((.sr 0, 1), .ofAdd 1)) (by decide) (by decide)

private theorem mem_sigmaTwo : sigmaTwo ∈ U0 :=
  mem_U0_of (w := ((.r 2, 1), 1)) (by decide) (by decide)

private theorem mem_z0 : z0 ∈ U0 :=
  mem_U0_of (w := ((1, .r 2), 1)) (by decide) (by decide)

private theorem mem_x0 : (swap 0 2 * swap 1 3 : Perm (Fin 10)) ∈ U0 :=
  mem_U0_of (w := ((.sr 1, 1), 1)) (by decide) (by decide)

private theorem mem_y0 : (swap 4 6 * swap 5 7 : Perm (Fin 10)) ∈ U0 :=
  mem_U0_of (w := ((1, .sr 1), 1)) (by decide) (by decide)

private theorem fix_zero : ∀ j : Fin 10, (swap 2 3 * swap 4 5 : Perm (Fin 10)) j = j →
    (swap 2 3 * swap 8 9 : Perm (Fin 10)) j = j → (swap 2 3 * swap 6 7 : Perm (Fin 10)) j = j →
    j = 0 ∨ j = 1 := by
  decide

private theorem fix_four : ∀ j : Fin 10, (swap 0 1 * swap 6 7 : Perm (Fin 10)) j = j →
    (swap 6 7 * swap 8 9 : Perm (Fin 10)) j = j → (swap 2 3 * swap 6 7 : Perm (Fin 10)) j = j →
    j = 4 ∨ j = 5 := by
  decide

private theorem fix_eight : ∀ j : Fin 10, (swap 0 1 * swap 4 5 : Perm (Fin 10)) j = j →
    (swap 2 3 * swap 6 7 : Perm (Fin 10)) j = j → j = 8 ∨ j = 9 := by
  decide

private theorem eq_of_agree {g h : Perm (Fin 10)} (hg : ∀ u ∈ U0, g * u = u * g)
    (hh : ∀ u ∈ U0, h * u = u * h) (h0 : g 0 = h 0) (h4 : g 4 = h 4) (h8 : g 8 = h 8) :
    g = h := by
  have key : ∀ u ∈ U0, ∀ i j, u i = j → g i = h i → g j = h j := fun u hu _ _ =>
    agree_of_comm (hg u hu) (hh u hu)
  have h1 := key _ mem_sigmaTwo 0 1 (by decide) h0
  have h2 := key _ mem_x0 0 2 (by decide) h0
  have h3 := key _ mem_sigmaTwo 2 3 (by decide) h2
  have h5 := key _ mem_z0 4 5 (by decide) h4
  have h6 := key _ mem_y0 4 6 (by decide) h4
  have h7 := key _ mem_z0 6 7 (by decide) h6
  have h9 := key _ mem_u7 8 9 (by decide) h8
  refine Equiv.ext fun i => ?_
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by
    revert i
    decide
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem mem_centralizer_U0_iff (g : Perm (Fin 10)) :
    (∀ u ∈ U0, g * u = u * g) ↔ g ∈ E8 := by
  refine ⟨fun hc => ?_, fun hg => comm_E8 g hg⟩
  have h0 := fix_zero (g 0) (apply_fix (hc _ mem_u1) (by decide))
    (apply_fix (hc _ mem_u2) (by decide)) (apply_fix (hc _ mem_u3) (by decide))
  have h4 := fix_four (g 4) (apply_fix (hc _ mem_u4) (by decide))
    (apply_fix (hc _ mem_u5) (by decide)) (apply_fix (hc _ mem_u3) (by decide))
  have h8 := fix_eight (g 8) (apply_fix (hc _ mem_u6) (by decide))
    (apply_fix (hc _ mem_u3) (by decide))
  have hagree : ∀ e ∈ E8, ∀ a b c : Fin 10, g 0 = a → g 4 = b → g 8 = c → e 0 = a → e 4 = b →
      e 8 = c → g ∈ E8 := fun e he _ _ _ ga gb gc ea eb ec =>
    (eq_of_agree hc (comm_E8 e he) (ga.trans ea.symm) (gb.trans eb.symm)
      (gc.trans ec.symm)) ▸ he
  rcases h0 with h0 | h0 <;> rcases h4 with h4 | h4 <;> rcases h8 with h8 | h8
  · exact hagree 1 (by simp [E8]) _ _ _ h0 h4 h8 (by decide) (by decide) (by decide)
  · exact hagree r0 (by simp [E8]) _ _ _ h0 h4 h8 (by decide) (by decide) (by decide)
  · exact hagree z0 (by simp [E8]) _ _ _ h0 h4 h8 (by decide) (by decide) (by decide)
  · exact hagree (z0 * r0) (by simp [E8]) _ _ _ h0 h4 h8 (by decide) (by decide) (by decide)
  · exact hagree sigmaTwo (by simp [E8]) _ _ _ h0 h4 h8 (by decide) (by decide) (by decide)
  · exact hagree (sigmaTwo * r0) (by simp [E8]) _ _ _ h0 h4 h8 (by decide) (by decide)
      (by decide)
  · exact hagree (sigmaTwo * z0) (by simp [E8]) _ _ _ h0 h4 h8 (by decide) (by decide)
      (by decide)
  · exact hagree (sigmaTwo * z0 * r0) (by simp [E8]) _ _ _ h0 h4 h8 (by decide) (by decide)
      (by decide)

theorem eq_r0_of_isSwap {g : Perm (Fin 10)} (hg : g.IsSwap) (hc : ∀ u ∈ U0, g * u = u * g) :
    g = r0 := by
  have h2 := card_support_eq_two.mpr hg
  have hE := (mem_centralizer_U0_iff g).mp hc
  simp only [E8, Finset.mem_insert, Finset.mem_singleton] at hE
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd h2 (by decide)
    | rfl

theorem mem_of_commute_t {t g : Perm (Fin 10)} (htU : ∀ u ∈ U0, t * u * t⁻¹ ∈ U0)
    (hta : t * sigmaTwo * t⁻¹ = z0) (htz : t * z0 * t⁻¹ = sigmaTwo)
    (hc : ∀ u ∈ U0, g * u = u * g) (hgt : g * t = t * g) :
    g = 1 ∨ g = sigmaTwo * z0 ∨ g = r0 ∨ g = sigmaTwo * z0 * r0 := by
  have hU : ∀ u ∈ U0, t⁻¹ * u * t ∈ U0 := by
    have hinj : Function.Injective (fun u : U0 => (⟨t * u * t⁻¹, htU u u.2⟩ : U0)) := by
      intro x y hxy
      exact Subtype.ext (by simpa using congrArg Subtype.val hxy)
    intro u hu
    obtain ⟨v, hv⟩ := Finite.injective_iff_surjective.mp hinj ⟨u, hu⟩
    have hv' : t * v * t⁻¹ = u := congrArg Subtype.val hv
    have : t⁻¹ * (t * v * t⁻¹) * t = v := by group
    rw [← hv', this]
    exact v.2
  have htr : t * r0 * t⁻¹ = r0 := by
    refine eq_r0_of_isSwap ⟨t 8, t 9, t.injective.ne (by decide),
      (swap_apply_apply t 8 9).symm⟩ fun u hu => ?_
    have h := comm_E8 r0 (by simp [E8]) _ (hU u hu)
    calc t * r0 * t⁻¹ * u = t * (r0 * (t⁻¹ * u * t)) * t⁻¹ := by group
      _ = t * (t⁻¹ * u * t * r0) * t⁻¹ := by rw [h]
      _ = u * (t * r0 * t⁻¹) := by group
  have hconj : ∀ x y : Perm (Fin 10), t * (x * y) * t⁻¹ = t * x * t⁻¹ * (t * y * t⁻¹) := by
    intro x y
    group
  have hgt' : t * g * t⁻¹ = g := by rw [← hgt, mul_inv_cancel_right]
  have hE := (mem_centralizer_U0_iff g).mp hc
  simp only [E8, Finset.mem_insert, Finset.mem_singleton] at hE
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl rfl
  · rw [hta] at hgt'
    exact absurd hgt' (by decide)
  · rw [htz] at hgt'
    exact absurd hgt' (by decide)
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · rw [hconj, hta, htr] at hgt'
    exact absurd hgt' (by decide)
  · rw [hconj, htz, htr] at hgt'
    exact absurd hgt' (by decide)
  · exact .inr (.inr (.inr rfl))

theorem isSwap_of_support_subset {α : Type*} [DecidableEq α] [Fintype α] {g : Perm α}
    {Δ : Finset α} (hΔ : Δ.card = 4) (hg2 : g * g = 1) (hgs : sign g = -1)
    (hsupp : g.support ⊆ Δ) : g.IsSwap := by
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [sign_one] at hgs
    exact absurd hgs (by decide)
  obtain ⟨hct, hcard, hm⟩ := cycleType_of_orderOf_two (orderOf_eq_prime (by rw [sq, hg2]) hg1)
  have hle : g.support.card ≤ 4 := hΔ ▸ Finset.card_le_card hsupp
  rw [sign_of_cycleType, hct, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul] at hgs
  rw [← card_support_eq_two]
  rcases (by omega : g.support.card / 2 = 1 ∨ g.support.card / 2 = 2) with h | h
  · omega
  · rw [h] at hgs
    exact absurd hgs (by decide)

end CFSG.ComponentClassification.GSThmB.A10T
