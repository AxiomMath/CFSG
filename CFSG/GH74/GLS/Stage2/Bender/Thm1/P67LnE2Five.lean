module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnE2

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.E2

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.OddAut.BlockTorus

section Coords

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

theorem Bs_c (c : Fin s) : Bs K p s (Sum.inr c) = ((0, 0), Pi.single c 1) := by
  simp [Bs]
  rfl

theorem coord_c (c : Fin s) (x y : Lq K p) (z : Fin s → K) :
    (Bs K p s).coord (Sum.inr c) ((x, y), z) = z c := by
  simp [Bs, Module.Basis.coord_apply]

theorem torEnd_Bs_of_notB2 (w : Lq K p) (a : (Fin 2 ⊕ Fin 2) ⊕ Fin s)
    (ha : ∀ α, a ≠ Sum.inl (Sum.inr α)) : torEnd K p s 1 w (Bs K p s a) = Bs K p s a := by
  rcases a with (α | α) | c
  · rw [Bs_ll, torEnd_apply]; simp
  · exact absurd rfl (ha α)
  · rw [Bs_c, torEnd_apply]; simp

theorem torEnd_Bs_of_notB1 (u : Lq K p) (a : (Fin 2 ⊕ Fin 2) ⊕ Fin s)
    (ha : ∀ α, a ≠ Sum.inl (Sum.inl α)) : torEnd K p s u 1 (Bs K p s a) = Bs K p s a := by
  rcases a with (α | α) | c
  · exact absurd rfl (ha α)
  · rw [Bs_lr, torEnd_apply]; simp
  · rw [Bs_c, torEnd_apply]; simp

theorem coord_torEnd_of_notB2 (w : Lq K p) (b : (Fin 2 ⊕ Fin 2) ⊕ Fin s)
    (hb : ∀ β, b ≠ Sum.inl (Sum.inr β)) (v : Em K p s) :
    (Bs K p s).coord b (torEnd K p s 1 w v) = (Bs K p s).coord b v := by
  obtain ⟨⟨x, y⟩, z⟩ := v
  rcases b with (β | β) | c
  · rw [torEnd_apply, coord_ll, coord_ll]; simp
  · exact absurd rfl (hb β)
  · rw [torEnd_apply, coord_c, coord_c]

theorem coord_torEnd_of_notB1 (u : Lq K p) (b : (Fin 2 ⊕ Fin 2) ⊕ Fin s)
    (hb : ∀ β, b ≠ Sum.inl (Sum.inl β)) (v : Em K p s) :
    (Bs K p s).coord b (torEnd K p s u 1 v) = (Bs K p s).coord b v := by
  obtain ⟨⟨x, y⟩, z⟩ := v
  rcases b with (β | β) | c
  · exact absurd rfl (hb β)
  · rw [torEnd_apply, coord_lr, coord_lr]; simp
  · rw [torEnd_apply, coord_c, coord_c]

theorem torEnd_comm_NB_notB2 (w : Lq K p) (a b : (Fin 2 ⊕ Fin 2) ⊕ Fin s)
    (ha : ∀ α, a ≠ Sum.inl (Sum.inr α)) (hb : ∀ β, b ≠ Sum.inl (Sum.inr β)) :
    torEnd K p s 1 w * NB K p s a b = NB K p s a b * torEnd K p s 1 w := by
  refine LinearMap.ext fun v => ?_
  simp only [Module.End.mul_apply, NB, LinearMap.smulRight_apply, map_smul,
    torEnd_Bs_of_notB2 K p s w a ha, coord_torEnd_of_notB2 K p s w b hb]

theorem torEnd_comm_NB_notB1 (u : Lq K p) (a b : (Fin 2 ⊕ Fin 2) ⊕ Fin s)
    (ha : ∀ α, a ≠ Sum.inl (Sum.inl α)) (hb : ∀ β, b ≠ Sum.inl (Sum.inl β)) :
    torEnd K p s u 1 * NB K p s a b = NB K p s a b * torEnd K p s u 1 := by
  refine LinearMap.ext fun v => ?_
  simp only [Module.End.mul_apply, NB, LinearMap.smulRight_apply, map_smul,
    torEnd_Bs_of_notB1 K p s u a ha, coord_torEnd_of_notB1 K p s u b hb]

end Coords

section Gen5

open scoped commutatorElement

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

theorem toSL_injective : Function.Injective (toSL K p s) := by
  intro f g h
  apply Subtype.ext
  apply Units.ext
  have h1 := ΦA_toSL K p s f
  have h2 := ΦA_toSL K p s g
  rw [h] at h1
  exact h1.symm.trans h2

theorem elemSL_val (a b : (Fin 2 ⊕ Fin 2) ⊕ Fin s) (hab : a ≠ b) (t : K) :
    ((elemSL K p s a b hab t).1 : Module.End K (Em K p s)) = 1 + t • NB K p s a b := rfl

theorem elemSL_comm (a k b : (Fin 2 ⊕ Fin 2) ⊕ Fin s) (hak : a ≠ k) (hkb : k ≠ b) (hab : a ≠ b)
    (t u : K) :
    ⁅elemSL K p s a k hak t, elemSL K p s k b hkb u⁆ = elemSL K p s a b hab (t * u) := by
  apply toSL_injective K p s
  rw [map_commutatorElement, toSL_elemSL, toSL_elemSL, toSL_elemSL]
  exact Matrix.SpecialLinearGroup.commutatorElement_transvection _ _ _ t u

theorem gen5 (g xa xb : GL (Fin (4 + 1)) K) (ζ : (Lq K p)ˣ)
    (ha : Φ K p 1 (g⁻¹ * xa * g) = torHom K p 1 (ζ, 1))
    (hb : Φ K p 1 (g⁻¹ * xb * g) = torHom K p 1 (1, ζ))
    (T : Subgroup (projectiveSL (4 + 1) K))
    (hTa : fixSub (conjAut (4 + 1) K xa) ≤ T) (hTb : fixSub (conjAut (4 + 1) K xb) ≤ T) :
    T = ⊤ := by
  apply CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.eq_top_of_rootElt_mem g T
  intro i j hij t
  obtain ⟨a, rfl⟩ := (eSum 1).surjective i
  obtain ⟨b, rfl⟩ := (eSum 1).surjective j
  have hab : a ≠ b := fun h => hij (by rw [h])
  rw [rootElt_eq_rho K p 1 g a b hab t]
  set T' : Subgroup (SLE K p 1) := T.comap (rho K p 1 g) with hT'
  have h1 : ∀ (a b : (Fin 2 ⊕ Fin 2) ⊕ Fin 1) (hab : a ≠ b),
      (∀ α, a ≠ Sum.inl (Sum.inr α)) → (∀ β, b ≠ Sum.inl (Sum.inr β)) → ∀ t : K,
        elemSL K p 1 a b hab t ∈ T' := by
    intro a b hab ha' hb' t
    apply hTb
    apply rho_mem_fixSub K p 1 g xb
    rw [hb, torHom_val, Units.val_one, elemSL_val]
    have hc := torEnd_comm_NB_notB2 K p 1 (ζ : Lq K p) a b ha' hb'
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hc]
  have h2 : ∀ (a b : (Fin 2 ⊕ Fin 2) ⊕ Fin 1) (hab : a ≠ b),
      (∀ α, a ≠ Sum.inl (Sum.inl α)) → (∀ β, b ≠ Sum.inl (Sum.inl β)) → ∀ t : K,
        elemSL K p 1 a b hab t ∈ T' := by
    intro a b hab ha' hb' t
    apply hTa
    apply rho_mem_fixSub K p 1 g xa
    rw [ha, torHom_val, Units.val_one, elemSL_val]
    have hc := torEnd_comm_NB_notB1 K p 1 (ζ : Lq K p) a b ha' hb'
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hc]
  have comm_step : ∀ (a b : (Fin 2 ⊕ Fin 2) ⊕ Fin 1) (hab : a ≠ b)
      (hak : a ≠ Sum.inr 0) (hkb : Sum.inr 0 ≠ b) (t : K),
      elemSL K p 1 a (Sum.inr 0) hak t ∈ T' → elemSL K p 1 (Sum.inr 0) b hkb 1 ∈ T' →
        elemSL K p 1 a b hab t ∈ T' := by
    intro a b hab hak hkb t e₁ e₂
    have := elemSL_comm K p 1 a (Sum.inr 0) b hak hkb hab t 1
    rw [mul_one] at this
    rw [← this, commutatorElement_def]
    exact T'.mul_mem (T'.mul_mem (T'.mul_mem e₁ e₂) (T'.inv_mem e₁)) (T'.inv_mem e₂)
  show elemSL K p 1 a b hab t ∈ T'
  rcases a with (α | α) | c <;> rcases b with (β | β) | d
  · exact h1 _ _ hab (by simp) (by simp) t
  · exact comm_step _ _ hab (by simp) (by simp) t (h1 _ _ _ (by simp) (by simp) t)
      (h2 _ _ _ (by simp) (by simp) 1)
  · exact h1 _ _ hab (by simp) (by simp) t
  · exact comm_step _ _ hab (by simp) (by simp) t (h2 _ _ _ (by simp) (by simp) t)
      (h1 _ _ _ (by simp) (by simp) 1)
  · exact h2 _ _ hab (by simp) (by simp) t
  · exact h2 _ _ hab (by simp) (by simp) t
  · exact h1 _ _ hab (by simp) (by simp) t
  · exact h2 _ _ hab (by simp) (by simp) t
  · exact absurd (by rw [Subsingleton.elim c d]) hab

end Gen5

section Main5

variable {K : Type} [Field K] [Finite K]

theorem false_of_e2_five (p : ℕ) [Fact p.Prime] [CharP K p] {r : ℕ} [Fact r.Prime] (hr2 : Odd r)
    (hrq : (Nat.card K : ZMod r) = -1) {V Z : Subgroup (MulAut (projectiveSL 5 K))}
    (h2 : N2Cfg (projectiveSL 5 K) r V Z) (h3 : N3Full (projectiveSL 5 K) V Z)
    (hVD : ∀ v ∈ V, ∃ A : GL (Fin 5) K, v = conjAut 5 K A) : False := by
  classical
  have h2' := h2
  obtain ⟨-, -, hVe, hVc, -⟩ := h2'
  have : IsElementaryAbelian r ↥V := hVe
  obtain ⟨g, xa, xb, -, ζ, hxaV, hxa1, hxbV, hxb1, -, -, hxa, hxb, -⟩ :=
    exists_torus_elems (K := K) (s := 1) p (by norm_num) hr2 hrq hVc hVD
  set T : Subgroup (projectiveSL 5 K) := ⨆ v ∈ V, ⨆ (_ : v ≠ 1), fixSub v with hT
  have hle : ∀ x : GL (Fin 5) K, conjAut 5 K x ∈ V → conjAut 5 K x ≠ 1 →
      fixSub (conjAut 5 K x) ≤ T := fun x hx hne =>
    le_iSup₂_of_le (conjAut 5 K x) hx
      (le_iSup (fun _ : conjAut 5 K x ≠ 1 => fixSub (conjAut 5 K x)) hne)
  have hgen : T = ⊤ :=
    gen5 K p g xa xb ζ hxa hxb T (hle xa hxaV hxa1) (hle xb hxbV hxb1)
  exact false_of_generation (isSimpleGroup_projectiveSL (by norm_num))
    (exists_noncomm_projectiveSL (by norm_num)) h2 h3 hgen

end Main5

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.E2
