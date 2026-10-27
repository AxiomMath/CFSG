module

public import CFSG.RankThree.PartOne.LIT.RankAbstract
public import CFSG.RankThree.PartTwo.Census.LinearRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Module CFSG.RankThree.PartOne.LIT CFSG.RankThree.PartTwo.Census

universe u v

structure SesqForm (K : Type u) [Field K] (q : ℕ) (V : Type v) [AddCommGroup V] [Module K V] where
  h : V → V → K
  add_left : ∀ v v' w, h (v + v') w = h v w + h v' w
  smul_left : ∀ (a : K) v w, h (a • v) w = a ^ q * h v w
  add_right : ∀ v w w', h v (w + w') = h v w + h v w'
  smul_right : ∀ (a : K) v w, h v (a • w) = a * h v w
  nondeg : ∀ v, (∀ w, h v w = 0) → v = 0

variable {K : Type u} [Field K]

theorem SesqForm.smul_smul_self {q : ℕ} {V : Type v} [AddCommGroup V] [Module K V]
    (B : SesqForm K q V) (c : K) (v : V) : B.h (c • v) (c • v) = c ^ (q + 1) * B.h v v := by
  rw [B.smul_left, B.smul_right, pow_succ]
  ring

theorem SesqForm.self_ne_zero_of_finrank_one {q : ℕ} {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : SesqForm K q V) (hV : finrank K V = 1) (v0 : V) (hv0 : v0 ≠ 0) :
    B.h v0 v0 ≠ 0 := by
  intro h0
  have hall : ∀ w, B.h v0 w = 0 := by
    intro w
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v0 hv0).mp hV w
    rw [← hc, B.smul_right, h0, mul_zero]
  exact hv0 (B.nondeg v0 hall)

theorem eq_one_of_sesq_finrank_le_one {q : ℕ} (hq : ∀ c : K, c ^ 3 = 1 → c ^ (q + 1) = 1 → c = 1)
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (B : SesqForm K q V)
    (hn : finrank K V ≤ 1) (g : V ≃ₗ[K] V) (hg : g ^ 3 = 1)
    (hB : ∀ v w, B.h (g v) (g w) = B.h v w) : g = 1 := by
  rcases Nat.lt_or_ge (finrank K V) 1 with h0 | h1
  · have hsub : Subsingleton V := (Module.finrank_zero_iff (R := K) (M := V)).mp (by omega)
    exact LinearEquiv.ext fun v => Subsingleton.elim _ _
  · have hV : finrank K V = 1 := by omega
    obtain ⟨v0, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < finrank K V)
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
    have hc3 : c ^ 3 = 1 := by
      have h := hpow 3 v0
      rw [hg] at h
      change v0 = (c ^ 3) • v0 at h
      have : (c ^ 3 - 1) • v0 = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
      rcases smul_eq_zero.mp this with h' | h'
      · exact sub_eq_zero.mp h'
      · exact absurd h' hv0
    have hsc : c ^ (q + 1) = 1 := by
      have hself := B.smul_smul_self c v0
      rw [← hgv v0] at hself
      rw [hB v0 v0] at hself
      have hne := B.self_ne_zero_of_finrank_one hV v0 hv0
      have : (c ^ (q + 1) - 1) * B.h v0 v0 = 0 := by linear_combination -hself
      rcases mul_eq_zero.mp this with h' | h'
      · exact sub_eq_zero.mp h'
      · exact absurd h' hne
    have hc1 : c = 1 := hq c hc3 hsc
    apply LinearEquiv.ext
    intro w
    rw [hgv, hc1, one_smul]
    rfl

theorem SesqForm.h_sub_right {q : ℕ} {V : Type v} [AddCommGroup V] [Module K V] (B : SesqForm K q V)
    (v w w' : V) : B.h v (w - w') = B.h v w - B.h v w' := by
  rw [sub_eq_add_neg, B.add_right, ← neg_one_smul K w', B.smul_right]
  ring

theorem SesqForm.orth_fixed_comm {q : ℕ} {V : Type v} [AddCommGroup V] [Module K V]
    (B : SesqForm K q V) {g : V ≃ₗ[K] V} (hB : ∀ v w, B.h (g v) (g w) = B.h v w) {u : V}
    (hu : g u = u) (y : V) : B.h u (g y - y) = 0 ∧ B.h (g y - y) u = 0 := by
  constructor
  · have h1 : B.h u (g y) = B.h u y := by
      have := hB u y
      rwa [hu] at this
    rw [B.h_sub_right, h1, sub_self]
  · have h2 : B.h (g y) u = B.h y u := by
      have := hB y u
      rwa [hu] at this
    have h3 := B.add_left (g y - y) y u
    rw [sub_add_cancel, h2] at h3
    linear_combination -h3

theorem card_le_pow_half_of_sesq {q : ℕ} (h3 : (3 : K) ≠ 0)
    (hq : ∀ c : K, c ^ 3 = 1 → c ^ (q + 1) = 1 → c = 1) (n : ℕ) :
    ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (B : SesqForm K q V),
      finrank K V = n → ∀ (E : Subgroup (V ≃ₗ[K] V)) [Finite E],
      (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) → (∀ g ∈ E, g ^ 3 = 1) →
      (∀ g ∈ E, ∀ v w, B.h (g v) (g w) = B.h v w) → Nat.card E ≤ 3 ^ (n / 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ B hn E _ hcomm hexp hinv
  have hpr : Nat.Prime 3 := Nat.prime_three
  have h3' : ((3 : ℕ) : K) ≠ 0 := by exact_mod_cast h3
  have hexpE : ∀ a : E, a ^ 3 = 1 := fun a => Subtype.ext (hexp a a.2)
  rcases Nat.lt_or_ge (Nat.card E) 9 with hsmall | hbig
  · obtain ⟨k, hk⟩ := exists_card_eq_pow_of_exponent hpr hexpE
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
          exact eq_one_of_sesq_finrank_le_one hq B (by omega) g (hexp g hg) (hinv g hg)
        rw [hbot, Subgroup.card_bot] at hk
        norm_num at hk
      · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · have h9 : 3 ^ 2 ≤ Nat.card E := by norm_num; omega
    obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ := exists_fixed_of_sq_le_card hpr h3' E hcomm hexp h9
    have hx3 : x ^ 3 = 1 := hexp x hxE
    have hsplit : IsCompl (fixedSpace x) (commSpace x) := isCompl_fixedSpace_commSpace h3' hx3
    have hxinv : ∀ v w, B.h (x v) (x w) = B.h v w := hinv x hxE
    set U := fixedSpace x with hUdef
    set W := commSpace x with hWdef
    have hUW : ∀ u ∈ U, ∀ w ∈ W, B.h u w = 0 ∧ B.h w u = 0 := by
      intro u hu w hw
      obtain ⟨y, rfl⟩ := mem_commSpace.mp hw
      exact B.orth_fixed_comm (fun a b => hinv x hxE a b) (mem_fixedSpace.mp hu) y
    have hdecomp : ∀ v : V, ∃ a ∈ U, ∃ b ∈ W, a + b = v := by
      intro v
      have hmem : v ∈ U ⊔ W := by
        rw [hsplit.sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
      exact ⟨a, ha, b, hb, hab⟩
    let BU : SesqForm K q U :=
      { h := fun a b => B.h a b
        add_left := fun a a' b => B.add_left a a' b
        smul_left := fun c a b => B.smul_left c a b
        add_right := fun a b b' => B.add_right a b b'
        smul_right := fun c a b => B.smul_right c a b
        nondeg := fun a ha => by
          apply Subtype.ext
          apply B.nondeg
          intro w
          obtain ⟨a1, ha1, b1, hb1, rfl⟩ := hdecomp w
          rw [B.add_right, ha ⟨a1, ha1⟩, (hUW a a.2 b1 hb1).1, add_zero] }
    let BW : SesqForm K q W :=
      { h := fun a b => B.h a b
        add_left := fun a a' b => B.add_left a a' b
        smul_left := fun c a b => B.smul_left c a b
        add_right := fun a b b' => B.add_right a b b'
        smul_right := fun c a b => B.smul_right c a b
        nondeg := fun a ha => by
          apply Subtype.ext
          apply B.nondeg
          intro w
          obtain ⟨a1, ha1, b1, hb1, rfl⟩ := hdecomp w
          rw [B.add_right, (hUW a1 ha1 a a.2).2, ha ⟨b1, hb1⟩, zero_add] }
    have hU : ∀ g : E, ∀ s ∈ U, E.subtype g s ∈ U :=
      fun g s hs => map_mem_fixedSpace (hcomm g.1 g.2 x hxE) hs
    have hW : ∀ g : E, ∀ s ∈ W, E.subtype g s ∈ W :=
      fun g s hs => map_mem_commSpace (hcomm g.1 g.2 x hxE) hs
    let ρ₁ : E →* (U ≃ₗ[K] U) := restrictAction E.subtype U hU
    let ρ₂ : E →* (W ≃ₗ[K] W) := restrictAction E.subtype W hW
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
    have hinvU : ∀ g ∈ ρ₁.range, ∀ a b : U, BU.h (g a) (g b) = BU.h a b := by
      rintro _ ⟨g, rfl⟩ a b
      exact hinv g g.2 a b
    have hinvW : ∀ g ∈ ρ₂.range, ∀ a b : W, BW.h (g a) (g b) = BW.h a b := by
      rintro _ ⟨g, rfl⟩ a b
      exact hinv g g.2 a b
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
      ih (finrank K U) hlt1 U BU rfl ρ₁.range hc1 he1 hinvU
    have hb2 : Nat.card ρ₂.range ≤ 3 ^ (finrank K W / 2) :=
      ih (finrank K W) hlt2 W BW rfl ρ₂.range hc2 he2 hinvW
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

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
