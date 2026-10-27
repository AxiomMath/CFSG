module

public import CFSG.CGT.T75I.NHat
public import CFSG.CGT.T75I.NSixA
public import CFSG.CGT.T75I.NAlt8

public section

namespace CFSG.CGT.T75I

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.GH74.Exceptional
  CFSG.ComponentClassification.PresentationLocal Equiv Equiv.Perm
open scoped Matrix

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem normalizer_cases_of_six [Finite G] (hc : Sec6Ctx T T₁ 2 2)
    (hC : Subgroup.centralizer (T : Set G) = T)
    (e : ↥T ≃* Multiplicative (Fin 4 → ZMod 2))
    (hiso : Nonempty (↥(hGamma T₁ e) ≃* alternatingGroup (Fin 6))) :
    Subgroup.normalizer (T : Set G) ≤ hSub T (normIn T₁ T) ∨
      ∃ x ∈ Subgroup.normalizer (T : Set G), x * x = 1 ∧ x ∉ hSub T (normIn T₁ T) ∧
        ∀ n ∈ Subgroup.normalizer (T : Set G),
          n ∈ hSub T (normIn T₁ T) ∨ x⁻¹ * n ∈ hSub T (normIn T₁ T) := by
  classical
  have hTab := hc.hy.pair.wc.1
  obtain ⟨eΓ⟩ := hiso
  obtain ⟨α, hα⟩ := exists_iso_alt8_carm
  let Θ : ↥(Subgroup.normalizer (T : Set G)) →* ↥(alternatingGroup (Fin 8)) :=
    α.symm.toMonoidHom.comp (actGL e)
  have hΘ : ∀ n, α (Θ n) = actGL e n := fun n => α.apply_symm_apply _
  let K : Subgroup (alternatingGroup (Fin 8)) := (hGamma T₁ e).map α.symm.toMonoidHom
  let eK : ↥K ≃* alternatingGroup (Fin 6) :=
    ((hGamma T₁ e).equivMapOfInjective α.symm.toMonoidHom α.symm.injective).symm.trans eΓ
  have hKmem : ∀ g : alternatingGroup (Fin 8), g ∈ K ↔ α g ∈ hGamma T₁ e := by
    intro g
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      simpa using hγ
    · intro h
      exact ⟨α g, h, by simp⟩
  obtain ⟨p, q, hpq, hfixK, hfixonly⟩ := exists_two_fixed K eK
  have hP := mem_of_fix K eK hpq hfixK
  have hKnorm : ∀ (n : ↥(Subgroup.normalizer (T : Set G))) (k : alternatingGroup (Fin 8)),
      k ∈ K → (Θ n)⁻¹ * k * Θ n ∈ K := by
    intro n k hk
    rw [hKmem] at hk ⊢
    rw [map_mul, map_mul, map_inv, hΘ]
    have := conj_mem_hGamma (T₁ := T₁) n⁻¹ hk
    rwa [map_inv, inv_inv] at this
  let g : ↥(Subgroup.normalizer (T : Set G)) → Perm (Fin 8) :=
    fun n => ((Θ n : alternatingGroup (Fin 8)) : Perm (Fin 8))
  have hmoves : ∀ (n : ↥(Subgroup.normalizer (T : Set G))) (x : Fin 8),
      (∀ k ∈ K, (k : Perm (Fin 8)) x = x) → ∀ k ∈ K, (k : Perm (Fin 8)) (g n x) = g n x := by
    intro n x hx k hk
    have h1 := hx _ (hKnorm n k hk)
    have h2 : (g n)⁻¹ ((k : Perm (Fin 8)) (g n x)) = x := h1
    have h3 := congrArg (g n) h2
    simpa using h3
  have hpres : ∀ n : ↥(Subgroup.normalizer (T : Set G)),
      (g n p = p ∧ g n q = q) ∨ (g n p = q ∧ g n q = p) := by
    intro n
    have h1 := hfixonly (g n p) (hmoves n p (fun k hk => (hfixK k hk).1))
    have h2 := hfixonly (g n q) (hmoves n q (fun k hk => (hfixK k hk).2))
    have hinj : ∀ x y, g n x = g n y → x = y := fun x y h => (g n).injective h
    rcases h1 with h1 | h1
    · left
      refine ⟨h1, ?_⟩
      rcases h2 with h2 | h2
      · exact absurd (hinj _ _ (h2.trans h1.symm)).symm hpq
      · exact h2
    · right
      refine ⟨h1, ?_⟩
      rcases h2 with h2 | h2
      · exact h2
      · exact absurd (hinj _ _ (h2.trans h1.symm)) hpq.symm
  have hH : ∀ m : ↥(Subgroup.normalizer (T : Set G)), g m p = p → (m : G) ∈ hSub T (normIn T₁ T) := by
    intro m hm
    have hq : g m q = q := ((hpres m).resolve_right (fun h => hpq (h.1.symm.trans hm).symm)).2
    have hmK : Θ m ∈ K := hP (Θ m) hm hq
    have h1 := (hKmem _).1 hmK
    rw [hΘ] at h1
    exact mem_hSub_of_actGL_mem hC m h1
  by_cases hA : ∀ n : ↥(Subgroup.normalizer (T : Set G)), g n p = p
  · left
    intro n hn
    exact hH ⟨n, hn⟩ (hA ⟨n, hn⟩)
  · right
    push Not at hA
    obtain ⟨n₀, hn₀⟩ := hA
    have hn₀p : g n₀ p = q := ((hpres n₀).resolve_left (fun h => hn₀ h.1)).1
    have hn₀q : g n₀ q = p := ((hpres n₀).resolve_left (fun h => hn₀ h.1)).2
    have hcard : (Finset.univ.filter fun x : Fin 8 => x ≠ p ∧ x ≠ q).card = 6 := by
      have : (Finset.univ.filter fun x : Fin 8 => x ≠ p ∧ x ≠ q) =
          ({p, q} : Finset (Fin 8))ᶜ := by
        ext x
        simp
      rw [this, Finset.card_compl, Finset.card_pair hpq]
      simp
    obtain ⟨a, ha⟩ := Finset.card_pos.1 (by rw [hcard]; norm_num)
    obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne
      (by rw [hcard]; norm_num : 1 < (Finset.univ.filter fun x : Fin 8 => x ≠ p ∧ x ≠ q).card) a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hd : Equiv.Perm.Disjoint (swap p q) (swap a b) := by
      intro x
      by_cases h : x = p ∨ x = q
      · right
        rcases h with rfl | rfl
        · exact swap_apply_of_ne_of_ne ha.1.symm hb.1.symm
        · exact swap_apply_of_ne_of_ne ha.2.symm hb.2.symm
      · left
        push Not at h
        exact swap_apply_of_ne_of_ne h.1 h.2
    have hσalt : swap p q * swap a b ∈ alternatingGroup (Fin 8) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hpq, Perm.sign_swap hba.symm]
      decide
    let σ : alternatingGroup (Fin 8) := ⟨swap p q * swap a b, hσalt⟩
    have hσ : (σ : Perm (Fin 8)) = swap p q * swap a b := rfl
    have hσp : (σ : Perm (Fin 8)) p = q := by
      rw [hσ, Perm.mul_apply, swap_apply_of_ne_of_ne ha.1.symm hb.1.symm, swap_apply_left]
    have hσq : (σ : Perm (Fin 8)) q = p := by
      rw [hσ, Perm.mul_apply, swap_apply_of_ne_of_ne ha.2.symm hb.2.symm, swap_apply_right]
    have hσσ : σ * σ = 1 := by
      apply Subtype.ext
      show (swap p q * swap a b) * (swap p q * swap a b) = 1
      have hcomm : swap a b * swap p q = swap p q * swap a b := hd.commute.symm.eq
      calc (swap p q * swap a b) * (swap p q * swap a b)
          = swap p q * (swap a b * swap p q) * swap a b := by group
        _ = swap p q * (swap p q * swap a b) * swap a b := by rw [hcomm]
        _ = (swap p q * swap p q) * (swap a b * swap a b) := by group
        _ = 1 := by rw [swap_mul_self, swap_mul_self, mul_one]
    have hm'p : (((Θ n₀)⁻¹ * σ : alternatingGroup (Fin 8)) : Perm (Fin 8)) p = p := by
      show ((g n₀)⁻¹ * (σ : Perm (Fin 8))) p = p
      rw [Perm.mul_apply, hσp, Equiv.Perm.inv_eq_iff_eq]
      exact hn₀p.symm
    have hm'q : (((Θ n₀)⁻¹ * σ : alternatingGroup (Fin 8)) : Perm (Fin 8)) q = q := by
      show ((g n₀)⁻¹ * (σ : Perm (Fin 8))) q = q
      rw [Perm.mul_apply, hσq, Equiv.Perm.inv_eq_iff_eq]
      exact hn₀q.symm
    have hm'K := (hKmem _).1 (hP _ hm'p hm'q)
    obtain ⟨h, hh, hθh⟩ := mem_hGamma.1 hm'K
    let mm : ↥(Subgroup.normalizer (T : Set G)) := ⟨h, hSub_le_normalizer' hh⟩
    have hΘmm : Θ mm = (Θ n₀)⁻¹ * σ := by
      have : Θ mm = α.symm (actGL e mm) := rfl
      rw [this, hθh]
      simp
    let n₁ : ↥(Subgroup.normalizer (T : Set G)) := n₀ * mm
    have hΘn₁ : Θ n₁ = σ := by
      show Θ (n₀ * mm) = σ
      rw [map_mul, hΘmm]
      group
    have hn₁H : (n₁ : G) ∉ hSub T (normIn T₁ T) := by
      intro hn₁
      have h1 : actGL e n₁ ∈ hGamma T₁ e := mem_hGamma.2 ⟨n₁, hn₁, rfl⟩
      rw [← hΘ, hΘn₁, ← hKmem] at h1
      have := (hfixK σ h1).1
      rw [hσp] at this
      exact hpq this.symm
    have hn₁sq : (n₁ : G) * (n₁ : G) ∈ T := by
      have h1 : actGL e (n₁ * n₁) = 1 := by
        rw [← hΘ, map_mul, hΘn₁, hσσ, map_one]
      exact (actGL_eq_one_iff hC e (n₁ * n₁)).1 h1
    have hc4 : Nat.card ↥(T ⊓ Subgroup.centralizer ({(n₁ : G)} : Set G)) = 4 := by
      rw [← card_fix_eq_card_centralizer e n₁]
      have : actGL e n₁ = α σ := by rw [← hΘ, hΘn₁]
      rw [this]
      exact card_fix_type22 α hα hpq hba.symm ha.1.symm hb.1.symm ha.2.symm hb.2.symm σ rfl
    obtain ⟨t, htT, hx⟩ := exists_involution_of_card_four hTab (ctx_card_T hc) n₁.2 hn₁sq hc4
    have htH : t ∈ hSub T (normIn T₁ T) := left_le_hSub htT
    have hhH : h ∈ hSub T (normIn T₁ T) := hh
    refine ⟨(n₁ : G) * t, (Subgroup.normalizer (T : Set G)).mul_mem n₁.2
      (Subgroup.le_normalizer htT), hx, ?_, ?_⟩
    · intro hxH
      apply hn₁H
      have e1 : (n₁ : G) = ((n₁ : G) * t) * t⁻¹ := by group
      rw [e1]
      exact (hSub T (normIn T₁ T)).mul_mem hxH ((hSub T (normIn T₁ T)).inv_mem htH)
    · intro n hn
      rcases hpres ⟨n, hn⟩ with hfix | hswap
      · exact Or.inl (hH ⟨n, hn⟩ hfix.1)
      · right
        have h1 : g (n₀⁻¹ * ⟨n, hn⟩) p = p := by
          have : g (n₀⁻¹ * ⟨n, hn⟩) = (g n₀)⁻¹ * g ⟨n, hn⟩ := by
            show ((Θ (n₀⁻¹ * ⟨n, hn⟩) : alternatingGroup (Fin 8)) : Perm (Fin 8)) = _
            rw [map_mul, map_inv]
            rfl
          rw [this, Perm.mul_apply, hswap.1, Equiv.Perm.inv_eq_iff_eq]
          exact hn₀p.symm
        have h2 := hH _ h1
        have e2 : ((n₁ : G) * t)⁻¹ * n = t⁻¹ * h⁻¹ * ((n₀⁻¹ * ⟨n, hn⟩ : ↥(Subgroup.normalizer
            (T : Set G))) : G) := by
          show (((n₀ : G) * h) * t)⁻¹ * n = t⁻¹ * h⁻¹ * ((n₀ : G)⁻¹ * n)
          group
        rw [e2]
        exact (hSub T (normIn T₁ T)).mul_mem ((hSub T (normIn T₁ T)).mul_mem
          ((hSub T (normIn T₁ T)).inv_mem htH) ((hSub T (normIn T₁ T)).inv_mem hhH)) h2

end CFSG.CGT.T75I
