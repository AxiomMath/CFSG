module

public import CFSG.RankThree.PartOne.LIT.RankAbstract
public import CFSG.RankThree.PartTwo.Census.LinearRank
public import CFSG.RankThree.PartOne.LIT.RankMatrix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Module CFSG.RankThree.PartOne.LIT CFSG.RankThree.PartTwo.Census

universe u v

variable {K : Type u} [Field K]

theorem eq_one_of_pow_three_of_finrank_le_one (hω : ∀ c : K, c ^ 2 + c + 1 ≠ 0)
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hn : finrank K V ≤ 1) (g : V ≃ₗ[K] V) (hg : g ^ 3 = 1) : g = 1 := by
  rcases Nat.lt_or_ge (finrank K V) 1 with h0 | h1
  · have hsub : Subsingleton V := (Module.finrank_zero_iff (R := K) (M := V)).mp (by omega)
    exact LinearEquiv.ext fun v => Subsingleton.elim _ _
  · have hV : finrank K V = 1 := by omega
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hV (g : V →ₗ[K] V)
    have hgv : ∀ w : V, g w = c • w := fun w => by
      have := LinearMap.congr_fun hc w
      simpa using this
    have hpow : ∀ (k : ℕ) (w : V), (g ^ k) w = (c ^ k) • w := by
      intro k
      induction k with
      | zero => intro w; simp
      | succ k ih =>
        intro w
        rw [pow_succ, LinearEquiv.mul_apply, hgv, map_smul, ih, smul_smul, pow_succ']
    obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < finrank K V)
    have hc3 : c ^ 3 = 1 := by
      have h := hpow 3 w
      rw [hg] at h
      change w = (c ^ 3) • w at h
      have : (c ^ 3 - 1) • w = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
      rcases smul_eq_zero.mp this with h' | h'
      · exact sub_eq_zero.mp h'
      · exact absurd h' hw
    have hc1 : c = 1 := by
      have hfac : (c - 1) * (c ^ 2 + c + 1) = 0 := by linear_combination hc3
      rcases mul_eq_zero.mp hfac with h' | h'
      · exact sub_eq_zero.mp h'
      · exact absurd h' (hω c)
    ext u
    simp [hgv, hc1]

theorem card_le_pow_half_of_noCubeRoot (h3 : (3 : K) ≠ 0) (hω : ∀ c : K, c ^ 2 + c + 1 ≠ 0)
    (n : ℕ) : ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      finrank K V = n → ∀ (E : Subgroup (V ≃ₗ[K] V)) [Finite E],
      (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) → (∀ g ∈ E, g ^ 3 = 1) → Nat.card E ≤ 3 ^ (n / 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn E _ hcomm hexp
  have hpr : Nat.Prime 3 := Nat.prime_three
  have h3' : ((3 : ℕ) : K) ≠ 0 := by exact_mod_cast h3
  have hexpE : ∀ a : E, a ^ 3 = 1 := fun a => Subtype.ext (hexp a a.2)
  rcases Nat.lt_or_ge (Nat.card E) 9 with hsmall | hbig
  ·
    obtain ⟨k, hk⟩ := exists_card_eq_pow_of_exponent hpr hexpE
    rw [hk] at hsmall ⊢
    have hk2 : k < 2 := by
      by_contra hcon
      push_neg at hcon
      have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hcon
      omega
    interval_cases k
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · exfalso
        have hbot : E = ⊥ := by
          rw [eq_bot_iff]
          intro g hg
          rw [Subgroup.mem_bot]
          exact eq_one_of_pow_three_of_finrank_le_one hω (by omega) g (hexp g hg)
        rw [hbot, Subgroup.card_bot] at hk
        norm_num at hk
      · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  ·
    have h9 : 3 ^ 2 ≤ Nat.card E := by norm_num; omega
    obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ :=
      exists_fixed_of_sq_le_card hpr h3' E hcomm hexp h9
    have hx3 : x ^ 3 = 1 := hexp x hxE
    have hsplit : IsCompl (fixedSpace x) (commSpace x) := isCompl_fixedSpace_commSpace h3' hx3
    have hU : ∀ g : E, ∀ s ∈ fixedSpace x, E.subtype g s ∈ fixedSpace x :=
      fun g s hs => map_mem_fixedSpace (hcomm g.1 g.2 x hxE) hs
    have hW : ∀ g : E, ∀ s ∈ commSpace x, E.subtype g s ∈ commSpace x :=
      fun g s hs => map_mem_commSpace (hcomm g.1 g.2 x hxE) hs
    set U := fixedSpace x with hUdef
    set W := commSpace x with hWdef
    have hab : finrank K U + finrank K W = n := by
      rw [← hn]
      exact Submodule.finrank_add_eq_of_isCompl hsplit
    have hvU : v ∈ U := mem_fixedSpace.mpr hxv
    have ha : 0 < finrank K U :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hvU⟩, fun h => hv0 (congrArg Subtype.val h)⟩
    obtain ⟨v', hv'⟩ : ∃ v' : V, x v' ≠ v' := by
      by_contra hcon
      push_neg at hcon
      exact hx1 (LinearEquiv.ext hcon)
    have hwW : x v' - v' ∈ W := mem_commSpace.mpr ⟨v', rfl⟩
    have hb : 0 < finrank K W :=
      Module.finrank_pos_iff_exists_ne_zero.mpr
        ⟨⟨x v' - v', hwW⟩, fun h => hv' (by
          have := congrArg Subtype.val h
          exact sub_eq_zero.mp this)⟩
    let ρ₁ : E →* (U ≃ₗ[K] U) := restrictAction E.subtype U hU
    let ρ₂ : E →* (W ≃ₗ[K] W) := restrictAction E.subtype W hW
    have hc1 : ∀ g ∈ ρ₁.range, ∀ h ∈ ρ₁.range, g * h = h * g := by
      rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm _ g.2 _ h.2)
    have hc2 : ∀ g ∈ ρ₂.range, ∀ h ∈ ρ₂.range, g * h = h * g := by
      rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm _ g.2 _ h.2)
    have he1 : ∀ g ∈ ρ₁.range, g ^ 3 = 1 := by
      rintro _ ⟨g, rfl⟩
      rw [← map_pow, hexpE g, map_one]
    have he2 : ∀ g ∈ ρ₂.range, g ^ 3 = 1 := by
      rintro _ ⟨g, rfl⟩
      rw [← map_pow, hexpE g, map_one]
    haveI : Finite ρ₁.range := Finite.of_surjective _ ρ₁.rangeRestrict_surjective
    haveI : Finite ρ₂.range := Finite.of_surjective _ ρ₂.rangeRestrict_surjective
    have hlt1 : finrank K U < n := by omega
    have hlt2 : finrank K W < n := by omega
    have hb1 : Nat.card ρ₁.range ≤ 3 ^ (finrank K U / 2) :=
      ih (finrank K U) hlt1 U rfl ρ₁.range hc1 he1
    have hb2 : Nat.card ρ₂.range ≤ 3 ^ (finrank K W / 2) :=
      ih (finrank K W) hlt2 W rfl ρ₂.range hc2 he2
    have hinj : Nat.card E ≤ Nat.card ρ₁.range * Nat.card ρ₂.range := by
      rw [← Nat.card_prod]
      refine Nat.card_le_card_of_injective (ρ₁.rangeRestrict.prod ρ₂.rangeRestrict) ?_
      rw [injective_iff_map_eq_one]
      intro g hg
      rw [MonoidHom.prod_apply, Prod.mk_eq_one] at hg
      obtain ⟨h1, h2⟩ := hg
      have h1' : ρ₁ g = 1 := congrArg Subtype.val h1
      have h2' : ρ₂ g = 1 := congrArg Subtype.val h2
      have hU1 : ∀ u ∈ U, E.subtype g u = u := by
        intro u hu
        have := congrArg Subtype.val (LinearEquiv.congr_fun h1' ⟨u, hu⟩)
        simpa [ρ₁, restrictAction_apply] using this
      have hW1 : ∀ w ∈ W, E.subtype g w = w := by
        intro w hw
        have := congrArg Subtype.val (LinearEquiv.congr_fun h2' ⟨w, hw⟩)
        simpa [ρ₂, restrictAction_apply] using this
      have hlin : (g : V ≃ₗ[K] V) = 1 := by
        apply LinearEquiv.ext
        intro w
        have := LinearMap.congr_fun
          (ext_of_isCompl hsplit (f := ((g : V ≃ₗ[K] V) : V →ₗ[K] V)) (g := LinearMap.id)
            (fun u hu => by simpa using hU1 u hu) (fun w hw => by simpa using hW1 w hw)) w
        simpa using this
      exact Subtype.ext hlin
    calc Nat.card E ≤ Nat.card ρ₁.range * Nat.card ρ₂.range := hinj
      _ ≤ 3 ^ (finrank K U / 2) * 3 ^ (finrank K W / 2) := Nat.mul_le_mul hb1 hb2
      _ = 3 ^ (finrank K U / 2 + finrank K W / 2) := (pow_add _ _ _).symm
      _ ≤ 3 ^ (n / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_le_pow_half_gl {ι : Type} [Fintype ι] [DecidableEq ι] (h3 : (3 : K) ≠ 0)
    (hω : ∀ c : K, c ^ 2 + c + 1 ≠ 0) (E : Subgroup (GL ι K)) [Finite E]
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ 3 = 1) :
    Nat.card E ≤ 3 ^ (Fintype.card ι / 2) := by
  have hfin : Finite (E.map (glAut ι K)) :=
    Finite.of_equiv E (E.equivMapOfInjective (glAut ι K) glAut_injective).toEquiv
  have h := card_le_pow_half_of_noCubeRoot h3 hω (Fintype.card ι) (ι → K)
    (by rw [Module.finrank_fintype_fun_eq_card]) (E.map (glAut ι K))
    (map_glAut_comm hcomm) (map_glAut_exp hexp)
  rwa [card_map_glAut] at h

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
