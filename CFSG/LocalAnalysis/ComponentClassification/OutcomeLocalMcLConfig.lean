module

public import CFSG.Fischer.Classification.Symplectic.Config

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.OutcomeLocal

open Module CFSG.Fischer.Classification.Symplectic

structure PreConfig (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] where
  b : LinearMap.BilinForm (ZMod 2) V
  D : Set V
  self_eq_zero : ∀ v, b v v = 0
  comm : ∀ u v, b u v = b v u
  nondeg : ∀ u, (∀ v, b u v = 0) → u = 0
  zero_notMem : (0 : V) ∉ D
  span_eq : Submodule.span (ZMod 2) D = ⊤
  add_mem : ∀ u ∈ D, ∀ v ∈ D, b u v = 1 → u + v ∈ D
  eq_of_closed : ∀ ℓ ⊆ D, ℓ.Nonempty → (∀ d ∈ D, ∀ p ∈ ℓ, p + b p d • d ∈ ℓ) → ℓ = D

namespace PreConfig

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (P : PreConfig V)

theorem b_cases (u v : V) : P.b u v = 0 ∨ P.b u v = 1 :=
  zmod_two_cases _

theorem b_add_left (u u' v : V) : P.b (u + u') v = P.b u v + P.b u' v := by
  rw [map_add, LinearMap.add_apply]

theorem b_add_right (u v v' : V) : P.b u (v + v') = P.b u v + P.b u v' :=
  map_add _ _ _

theorem ne_zero_of_mem {v : V} (hv : v ∈ P.D) : v ≠ 0 := fun h => P.zero_notMem (h ▸ hv)

theorem injective_of_isometry {f : V →ₗ[ZMod 2] V} (hf : ∀ u v, P.b (f u) (f v) = P.b u v) :
    Function.Injective f := by
  intro u v huv
  rw [← sub_eq_zero]
  refine P.nondeg _ fun w => ?_
  rw [← hf, map_sub, huv, sub_self, map_zero, LinearMap.zero_apply]

theorem exists_mem_b_eq_one {v : V} (hv : v ≠ 0) : ∃ p ∈ P.D, P.b p v = 1 := by
  by_contra h
  apply hv
  have hlin : P.b v = 0 := LinearMap.ext_on P.span_eq fun p hp => by
    rw [LinearMap.zero_apply, P.comm]
    exact zmod_two_eq_zero_of_ne_one fun h1 => h ⟨p, hp, h1⟩
  exact P.nondeg v fun w => by rw [hlin, LinearMap.zero_apply]

theorem exists_common {x y : V} (hx : x ∈ P.D) (hy : y ∈ P.D) (hxy : x ≠ y)
    (hb : P.b x y = 0) : ∃ u ∈ P.D, P.b u x = 1 ∧ P.b u y = 1 := by
  let ℓ : Set V := {p | p ∈ P.D ∧ (p = x ∨ P.b p x = 1 ∨ ∃ u ∈ P.D, P.b u x = 1 ∧ P.b u p = 1)}
  have hℓ : ℓ = P.D := by
    refine P.eq_of_closed ℓ (fun p hp => hp.1) ⟨x, hx, Or.inl rfl⟩ ?_
    rintro d hd p ⟨hpD, hp⟩
    rcases P.b_cases p d with hpd | hpd
    · rw [hpd, zero_smul, add_zero]
      exact ⟨hpD, hp⟩
    rw [hpd, one_smul]
    have hpdD : p + d ∈ P.D := P.add_mem p hpD d hd hpd
    have hdp : P.b d p = 1 := by rw [P.comm]; exact hpd
    refine ⟨hpdD, ?_⟩
    by_cases hpx : p = x
    · subst hpx
      right; left
      rw [P.b_add_left, P.self_eq_zero, zero_add, P.comm, hpd]
    rcases P.b_cases p x with hpx0 | hpx1
    ·
      obtain ⟨u, hu, hux, hup⟩ : ∃ u ∈ P.D, P.b u x = 1 ∧ P.b u p = 1 := by
        rcases hp with h | h | h
        · exact absurd h hpx
        · rw [hpx0] at h
          exact absurd h zero_ne_one
        · exact h
      rcases P.b_cases d x with hdx | hdx
      · right; right
        rcases P.b_cases u d with hud | hud
        · refine ⟨u, hu, hux, ?_⟩
          rw [P.b_add_right, hup, hud, add_zero]
        · refine ⟨u + d, P.add_mem u hu d hd hud, ?_, ?_⟩
          · rw [P.b_add_left, hux, hdx, add_zero]
          · rw [P.b_add_left, P.b_add_right, P.b_add_right, hup, hud, hdp, P.self_eq_zero,
              add_zero]
            rfl
      · right; left
        rw [P.b_add_left, hpx0, hdx, zero_add]
    · rcases P.b_cases d x with hdx | hdx
      · right; left
        rw [P.b_add_left, hpx1, hdx, add_zero]
      · right; right
        refine ⟨p, hpD, hpx1, ?_⟩
        rw [P.b_add_right, P.self_eq_zero, zero_add, hpd]
  have hyℓ : y ∈ ℓ := hℓ ▸ hy
  rcases hyℓ.2 with h | h | h
  · exact absurd h.symm hxy
  · rw [P.comm, hb] at h
    exact absurd h zero_ne_one
  · exact h

theorem mem_span_perp {s : V} (hs : s ≠ 0) {t : V} (ht : P.b t s = 0) :
    t ∈ Submodule.span (ZMod 2) {p | p ∈ P.D ∧ P.b p s = 0} := by
  set S := Submodule.span (ZMod 2) {p | p ∈ P.D ∧ P.b p s = 0}
  have hmemS : ∀ p ∈ P.D, P.b p s = 0 → p ∈ S := fun p hp hps =>
    Submodule.subset_span ⟨hp, hps⟩
  have hSperp : ∀ w ∈ S, P.b w s = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem p hp => exact hp.2
    | zero => simp
    | add x y _ _ hx hy => rw [P.b_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
  obtain ⟨p₀, hp₀, hp₀s⟩ := P.exists_mem_b_eq_one hs
  have hpair : ∀ p ∈ P.D, ∀ p' ∈ P.D, P.b p s = 1 → P.b p' s = 1 → p + p' ∈ S := by
    intro p hp p' hp' hps hp's
    have hr : ∀ r ∈ P.D, P.b r p = 1 → P.b r p' = 1 → P.b r s = 1 → p + p' ∈ S := by
      intro r hr hrp hrp' hrs
      have h1 : p + r ∈ P.D := P.add_mem p hp r hr (by rw [P.comm, hrp])
      have h2 : p' + r ∈ P.D := P.add_mem p' hp' r hr (by rw [P.comm, hrp'])
      rw [show p + p' = (p + r) + (p' + r) by zmod_two_abel]
      refine S.add_mem (hmemS _ h1 ?_) (hmemS _ h2 ?_)
      · rw [P.b_add_left, hps, hrs, zmod_two_one_add_one]
      · rw [P.b_add_left, hp's, hrs, zmod_two_one_add_one]
    rcases P.b_cases p p' with h | h
    · by_cases hpp : p = p'
      · rw [hpp, zmod_two_add_self]
        exact S.zero_mem
      · obtain ⟨r, hrD, hrp, hrp'⟩ := P.exists_common hp hp' hpp h
        rcases P.b_cases r s with hrs | hrs
        · refine hr (r + p) (P.add_mem r hrD p hp hrp) ?_ ?_ ?_
          · rw [P.b_add_left, hrp, P.self_eq_zero, add_zero]
          · rw [P.b_add_left, hrp', h, add_zero]
          · rw [P.b_add_left, hrs, hps, zero_add]
        · exact hr r hrD hrp hrp' hrs
    · refine hmemS _ (P.add_mem p hp p' hp' h) ?_
      rw [P.b_add_left, hps, hp's, zmod_two_one_add_one]
  have hall : ∀ t : V, t ∈ S ∨ t + p₀ ∈ S := by
    intro t
    have ht' : t ∈ Submodule.span (ZMod 2) P.D := by rw [P.span_eq]; trivial
    induction ht' using Submodule.span_induction with
    | mem p hp =>
      rcases P.b_cases p s with h | h
      · exact Or.inl (hmemS p hp h)
      · exact Or.inr (hpair p hp p₀ hp₀ h hp₀s)
    | zero => exact Or.inl S.zero_mem
    | add x y _ _ hx hy =>
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (S.add_mem hx hy)
      · right
        rw [show x + y + p₀ = x + (y + p₀) by zmod_two_abel]
        exact S.add_mem hx hy
      · right
        rw [show x + y + p₀ = (x + p₀) + y by zmod_two_abel]
        exact S.add_mem hx hy
      · left
        rw [show x + y = (x + p₀) + (y + p₀) by zmod_two_abel]
        exact S.add_mem hx hy
    | smul a x _ hx =>
      rcases zmod_two_cases a with rfl | rfl
      · left
        rw [zero_smul]
        exact S.zero_mem
      · rwa [one_smul]
  rcases hall t with h | h
  · exact h
  · exfalso
    have := hSperp _ h
    rw [P.b_add_left, ht, hp₀s, zero_add] at this
    exact one_ne_zero this

theorem eq_zero_or_eq_of_forall {s v : V} (h : ∀ t, P.b t s = 0 → P.b t v = 0) :
    v = 0 ∨ v = s := by
  by_cases hv : ∀ t, P.b t v = 0
  · left
    exact P.nondeg v fun t => by rw [P.comm]; exact hv t
  · right
    obtain ⟨t₀, ht₀⟩ : ∃ t₀, P.b t₀ v ≠ 0 := by
      by_contra hne
      exact hv fun t => by_contra fun h => hne ⟨t, h⟩
    have ht₀' : P.b t₀ v = 1 := zmod_two_eq_one_of_ne_zero ht₀
    have hs₀ : P.b t₀ s = 1 := by
      rcases P.b_cases t₀ s with h0 | h1
      · exact absurd (h t₀ h0) ht₀
      · exact h1
    have heq : ∀ t, P.b t v = P.b t s := by
      intro t
      rcases P.b_cases t s with h0 | h1
      · rw [h0]
        exact h t h0
      · have := h (t + t₀) (by rw [P.b_add_left, h1, hs₀, zmod_two_one_add_one])
        rw [P.b_add_left, ht₀'] at this
        rw [h1]
        rcases P.b_cases t v with h2 | h2
        · rw [h2, zero_add] at this
          exact absurd this one_ne_zero
        · exact h2
    rw [← sub_eq_zero]
    refine P.nondeg _ fun t => ?_
    rw [P.comm, map_sub, heq t, sub_self]

theorem exists_perp_b_eq_one {x p : V} (hx : x ∈ P.D) (hp : p ∈ P.D) (hpx : P.b p x = 0)
    (hpx' : p ≠ x) : ∃ r ∈ P.D, P.b r x = 0 ∧ r ≠ x ∧ P.b p r = 1 := by
  by_contra hno
  have hall : ∀ t, P.b t x = 0 → P.b t p = 0 := by
    intro t ht
    have hmem := P.mem_span_perp (P.ne_zero_of_mem hx) ht
    clear ht
    induction hmem using Submodule.span_induction with
    | mem r hr =>
      by_cases hrx : r = x
      · rw [hrx, P.comm]
        exact hpx
      · rw [P.comm]
        exact zmod_two_eq_zero_of_ne_one fun h1 => hno ⟨r, hr.1, hr.2, hrx, h1⟩
    | zero => simp
    | add u w _ _ hu hw => rw [P.b_add_left, hu, hw, add_zero]
    | smul a u _ hu => rw [map_smul, LinearMap.smul_apply, hu, smul_zero]
  rcases P.eq_zero_or_eq_of_forall hall with h | h
  · exact P.ne_zero_of_mem hp h
  · exact hpx' h

theorem mem_of_closed_perp {x : V} (hx : x ∈ P.D) {ℓ : Set V}
    (hℓR : ∀ p ∈ ℓ, p ∈ P.D ∧ P.b p x = 0 ∧ p ≠ x) (hne : ℓ.Nonempty)
    (hcl : ∀ r ∈ P.D, P.b r x = 0 → r ≠ x → ∀ p ∈ ℓ, P.b p r = 1 → p + r ∈ ℓ)
    {m : V} (hm : m ∈ P.D) (hmx : P.b m x = 0) (hmx' : m ≠ x) : m ∈ ℓ := by
  by_contra hmℓ
  have horth : ∀ p ∈ ℓ, ∀ q ∈ P.D, P.b q x = 0 → q ≠ x → q ∉ ℓ → P.b p q = 0 := by
    intro p hp q hq hqx hqx' hqℓ
    refine zmod_two_eq_zero_of_ne_one fun h1 => hqℓ ?_
    obtain ⟨hpD, hpx, hpx'⟩ := hℓR p hp
    have hpq : p + q ∈ ℓ := hcl q hq hqx hqx' p hp h1
    have := hcl p hpD hpx hpx' (p + q) hpq (by
      rw [P.b_add_left, P.self_eq_zero, zero_add, P.comm, h1])
    rwa [show p + q + p = q by zmod_two_abel] at this
  have hbridge : ∀ w ∈ P.D, P.b w x = 0 → w ≠ x → ∀ p ∈ ℓ, ∀ q ∈ P.D, P.b q x = 0 → q ≠ x →
      q ∉ ℓ → P.b w p = 1 → P.b w q = 1 → False := by
    intro w hw hwx hwx' p hp q hq hqx hqx' hqℓ hwp hwq
    by_cases hwℓ : w ∈ ℓ
    · have := horth w hwℓ q hq hqx hqx' hqℓ
      rw [hwq] at this
      exact one_ne_zero this
    · have := horth p hp w hw hwx hwx' hwℓ
      rw [P.comm, hwp] at this
      exact one_ne_zero this
  have hkey : ∀ p ∈ ℓ, ∀ q ∈ P.D, P.b q x = 0 → q ≠ x → q ∉ ℓ → ∀ u ∈ P.D, P.b u x = 1 →
      P.b u p = 1 → P.b u q = 1 → False := by
    intro p hp q hq hqx hqx' hqℓ u hu hux hup huq
    obtain ⟨hpD, hpx, hpx'⟩ := hℓR p hp
    have hpq : P.b p q = 0 := horth p hp q hq hqx hqx' hqℓ
    have h1 : p + u ∈ P.D := P.add_mem p hpD u hu (by rw [P.comm, hup])
    have h2 : p + u + q ∈ P.D := P.add_mem _ h1 q hq (by rw [P.b_add_left, hpq, huq, zero_add])
    have h3 : p + u + q + x ∈ P.D := P.add_mem _ h2 x hx (by
      rw [P.b_add_left, P.b_add_left, hpx, hux, hqx, zero_add, add_zero])
    have h4 : p + u + q + x + u ∈ P.D := P.add_mem _ h3 u hu (by
      rw [P.b_add_left, P.b_add_left, P.b_add_left, P.comm p u, hup, P.self_eq_zero,
        P.comm q u, huq, P.comm x u, hux]
      rfl)
    have hw : p + q + x ∈ P.D := by
      rwa [show p + u + q + x + u = p + q + x by zmod_two_abel] at h4
    have hwx : P.b (p + q + x) x = 0 := by
      rw [P.b_add_left, P.b_add_left, hpx, hqx, P.self_eq_zero, add_zero, add_zero]
    have hwx' : p + q + x ≠ x := by
      intro h
      have hpq0 : p + q = 0 := by simpa using congrArg (· + x) h
      exact hqℓ (zmod_two_eq_of_add_eq_zero hpq0 ▸ hp)
    obtain ⟨p', hp'D, hp'x, hp'x', hpp'⟩ := P.exists_perp_b_eq_one hx hpD hpx hpx'
    have hp'ℓ : p' ∈ ℓ := by
      by_contra h
      have := horth p hp p' hp'D hp'x hp'x' h
      rw [hpp'] at this
      exact one_ne_zero this
    obtain ⟨q', hq'D, hq'x, hq'x', hqq'⟩ := P.exists_perp_b_eq_one hx hq hqx hqx'
    have hq'ℓ : q' ∉ ℓ := fun h => by
      have := horth q' h q hq hqx hqx' hqℓ
      rw [P.comm, hqq'] at this
      exact one_ne_zero this
    refine hbridge _ hw hwx hwx' p' hp'ℓ q' hq'D hq'x hq'x' hq'ℓ ?_ ?_
    · rw [P.b_add_left, P.b_add_left, hpp', P.comm q p', horth p' hp'ℓ q hq hqx hqx' hqℓ,
        P.comm x p', hp'x, add_zero, add_zero]
    · rw [P.b_add_left, P.b_add_left, horth p hp q' hq'D hq'x hq'x' hq'ℓ, hqq',
        P.comm x q', hq'x, zero_add, add_zero]
  obtain ⟨p₀, hp₀⟩ := hne
  have hu : ∃ u ∈ P.D, P.b u x = 1 ∧ ∃ p ∈ ℓ, P.b u p = 1 := by
    by_contra hno
    have hℓ : ℓ = P.D := by
      refine P.eq_of_closed ℓ (fun p hp => (hℓR p hp).1) ⟨p₀, hp₀⟩ fun d hd p hp => ?_
      obtain ⟨hpD, hpx, hpx'⟩ := hℓR p hp
      rcases P.b_cases p d with hpd | hpd
      · rw [hpd, zero_smul, add_zero]
        exact hp
      rw [hpd, one_smul]
      by_cases hdx' : d = x
      · rw [hdx', hpx] at hpd
        exact absurd hpd zero_ne_one
      rcases P.b_cases d x with hdx | hdx
      · exact hcl d hd hdx hdx' p hp hpd
      · exact absurd ⟨d, hd, hdx, p, hp, by rw [P.comm, hpd]⟩ hno
    exact (hℓR x (hℓ ▸ hx)).2.2 rfl
  have hu' : ∃ u ∈ P.D, P.b u x = 1 ∧ ∃ q ∈ P.D, P.b q x = 0 ∧ q ≠ x ∧ q ∉ ℓ ∧ P.b u q = 1 := by
    by_contra hno
    let M : Set V := {q | q ∈ P.D ∧ P.b q x = 0 ∧ q ≠ x ∧ q ∉ ℓ}
    have hM : M = P.D := by
      refine P.eq_of_closed M (fun q hq => hq.1) ⟨m, hm, hmx, hmx', hmℓ⟩ fun d hd q hq => ?_
      obtain ⟨hqD, hqx, hqx', hqℓ⟩ := hq
      rcases P.b_cases q d with hqd | hqd
      · rw [hqd, zero_smul, add_zero]
        exact ⟨hqD, hqx, hqx', hqℓ⟩
      rw [hqd, one_smul]
      have hdx' : d ≠ x := by
        rintro rfl
        rw [hqx] at hqd
        exact zero_ne_one hqd
      have hdx : P.b d x = 0 := by
        rcases P.b_cases d x with h | h
        · exact h
        · exact absurd ⟨d, hd, h, q, hqD, hqx, hqx', hqℓ, by rw [P.comm, hqd]⟩ hno
      have hdℓ : d ∉ ℓ := fun h => by
        have := horth d h q hqD hqx hqx' hqℓ
        rw [P.comm, hqd] at this
        exact one_ne_zero this
      have hqdD : q + d ∈ P.D := P.add_mem q hqD d hd hqd
      have hqdx : P.b (q + d) x = 0 := by rw [P.b_add_left, hqx, hdx, add_zero]
      have hqdx' : q + d ≠ x := by
        intro h
        have := P.b_add_right q q d
        rw [h, hqx, P.self_eq_zero, hqd, zero_add] at this
        exact zero_ne_one this
      refine ⟨hqdD, hqdx, hqdx', fun h => hdℓ ?_⟩
      have := hcl q hqD hqx hqx' (q + d) h (by
        rw [P.b_add_left, P.self_eq_zero, zero_add, P.comm, hqd])
      rwa [show q + d + q = d by zmod_two_abel] at this
    exact (hM ▸ hx : x ∈ M).2.2.1 rfl
  obtain ⟨u, huD, hux, p, hp, hup⟩ := hu
  obtain ⟨u', hu'D, hu'x, q, hqD, hqx, hqx', hqℓ, hu'q⟩ := hu'
  obtain ⟨hpD, hpx, hpx'⟩ := hℓR p hp
  rcases P.b_cases u q with huq | huq
  swap
  · exact hkey p hp q hqD hqx hqx' hqℓ u huD hux hup huq
  rcases P.b_cases u' p with hu'p | hu'p
  swap
  · exact hkey p hp q hqD hqx hqx' hqℓ u' hu'D hu'x hu'p hu'q
  rcases P.b_cases u u' with huu' | huu'
  ·
    have hux' : u + x ∈ P.D := P.add_mem u huD x hx hux
    have hw : u + x + u' ∈ P.D := P.add_mem _ hux' u' hu'D (by
      rw [P.b_add_left, huu', P.comm x u', hu'x, zero_add])
    refine hbridge _ hw ?_ ?_ p hp q hqD hqx hqx' hqℓ ?_ ?_
    · rw [P.b_add_left, P.b_add_left, hux, P.self_eq_zero, hu'x, add_zero]
      rfl
    · intro h
      have huu : u = u' := by
        have : u + u' = 0 := by
          rw [show u + u' = u + x + u' + x by zmod_two_abel, h, zmod_two_add_self]
        exact zmod_two_eq_of_add_eq_zero this
      rw [huu, hu'q] at huq
      exact zero_ne_one huq.symm
    · rw [P.b_add_left, P.b_add_left, hup, P.comm x p, hpx, hu'p, add_zero, add_zero]
    · rw [P.b_add_left, P.b_add_left, huq, P.comm x q, hqx, hu'q, zero_add, zero_add]
  ·
    have hw : u + u' ∈ P.D := P.add_mem u huD u' hu'D huu'
    refine hbridge _ hw ?_ ?_ p hp q hqD hqx hqx' hqℓ ?_ ?_
    · rw [P.b_add_left, hux, hu'x]
      rfl
    · intro h
      have := P.b_add_left u u' p
      rw [h, P.comm x p, hpx, hup, hu'p, add_zero] at this
      exact zero_ne_one this
    · rw [P.b_add_left, hup, hu'p, add_zero]
    · rw [P.b_add_left, huq, hu'q, zero_add]

@[expose] def tr (d : V) : V →ₗ[ZMod 2] V :=
  LinearMap.id + (P.b.flip d).smulRight d

theorem tr_apply (d v : V) : P.tr d v = v + P.b v d • d :=
  rfl

theorem b_tr_tr (d u v : V) : P.b (P.tr d u) (P.tr d v) = P.b u v := by
  have hdv : P.b d v = P.b v d := P.comm d v
  have hdd : P.b d d = 0 := P.self_eq_zero d
  simp only [tr_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hdv, hdd]
  generalize P.b u v = γ
  generalize P.b u d = α
  generalize P.b v d = β
  revert α β γ
  decide

theorem tr_mem {d v : V} (hd : d ∈ P.D) (hv : v ∈ P.D) : P.tr d v ∈ P.D := by
  rw [tr_apply]
  rcases P.b_cases v d with h | h
  · rw [h, zero_smul, add_zero]
    exact hv
  · rw [h, one_smul]
    exact P.add_mem v hv d hd h

@[expose] def IsAuto (g : V →ₗ[ZMod 2] V) : Prop :=
  (∀ u v, P.b (g u) (g v) = P.b u v) ∧ ∀ u ∈ P.D, g u ∈ P.D

theorem isAuto_tr {d : V} (hd : d ∈ P.D) : P.IsAuto (P.tr d) :=
  ⟨P.b_tr_tr d, fun _ hu => P.tr_mem hd hu⟩

theorem isAuto_comp {g h : V →ₗ[ZMod 2] V} (hg : P.IsAuto g) (hh : P.IsAuto h) :
    P.IsAuto (g ∘ₗ h) :=
  ⟨fun u v => (hg.1 _ _).trans (hh.1 u v), fun u hu => hg.2 _ (hh.2 u hu)⟩

theorem isAuto_id : P.IsAuto LinearMap.id :=
  ⟨fun _ _ => rfl, fun _ hu => hu⟩

theorem exists_isAuto_apply_eq {x x' : V} (hx : x ∈ P.D) (hx' : x' ∈ P.D) :
    ∃ g, P.IsAuto g ∧ g x = x' := by
  let ℓ : Set V := {p | p ∈ P.D ∧ ∃ g, P.IsAuto g ∧ g x = p}
  have hℓ : ℓ = P.D := by
    refine P.eq_of_closed ℓ (fun p hp => hp.1) ⟨x, hx, LinearMap.id, P.isAuto_id, rfl⟩ ?_
    rintro d hd p ⟨hpD, g, hg, rfl⟩
    exact ⟨P.tr_mem hd hpD, P.tr d ∘ₗ g, P.isAuto_comp (P.isAuto_tr hd) hg, rfl⟩
  exact (hℓ ▸ hx' : x' ∈ ℓ).2

theorem exists_isAuto_fix_apply_eq {x y y' : V} (hx : x ∈ P.D) (hy : y ∈ P.D)
    (hyx : P.b y x = 0) (hyx' : y ≠ x) (hy' : y' ∈ P.D) (hy'x : P.b y' x = 0)
    (hy'x' : y' ≠ x) : ∃ g, P.IsAuto g ∧ g x = x ∧ g y = y' := by
  let ℓ : Set V := {p | (p ∈ P.D ∧ P.b p x = 0 ∧ p ≠ x) ∧ ∃ g, P.IsAuto g ∧ g x = x ∧ g y = p}
  have hmem := P.mem_of_closed_perp hx (ℓ := ℓ) (fun p hp => hp.1)
    ⟨y, ⟨hy, hyx, hyx'⟩, LinearMap.id, P.isAuto_id, rfl, rfl⟩ ?_ hy' hy'x hy'x'
  · exact hmem.2
  rintro r hr hrx hrx' p ⟨⟨hpD, hpx, hpx'⟩, g, hg, hgx, rfl⟩ hpr
  have hpr' : g y + r = P.tr r (g y) := by rw [tr_apply, hpr, one_smul]
  refine ⟨⟨P.add_mem _ hpD r hr hpr, ?_, ?_⟩, P.tr r ∘ₗ g, P.isAuto_comp (P.isAuto_tr hr) hg,
    ?_, ?_⟩
  · rw [P.b_add_left, hpx, hrx, add_zero]
  · intro h
    have := P.b_add_right (g y) (g y) r
    rw [h, hpx, P.self_eq_zero, hpr, zero_add] at this
    exact zero_ne_one this
  · rw [LinearMap.comp_apply, hgx, tr_apply, P.comm, hrx, zero_smul, add_zero]
  · rw [LinearMap.comp_apply, hpr']

theorem trans (x : V) (hx : x ∈ P.D) (y : V) (hy : y ∈ P.D) (x' : V) (hx' : x' ∈ P.D) (y' : V)
    (hy' : y' ∈ P.D) (hxy : x ≠ y) (hb : P.b x y = 0) (hxy' : x' ≠ y') (hb' : P.b x' y' = 0) :
    ∃ f : V →ₗ[ZMod 2] V, (∀ u v, P.b (f u) (f v) = P.b u v) ∧ (∀ u ∈ P.D, f u ∈ P.D) ∧
      f x = x' ∧ f y = y' := by
  obtain ⟨g₁, hg₁, hg₁x⟩ := P.exists_isAuto_apply_eq hx hx'
  have hinj := P.injective_of_isometry hg₁.1
  obtain ⟨g₂, hg₂, hg₂x, hg₂y⟩ := P.exists_isAuto_fix_apply_eq hx' (hg₁.2 y hy)
    (by rw [← hg₁x, hg₁.1, P.comm, hb]) (fun h => hxy (hinj (h.trans hg₁x.symm)).symm) hy'
    (by rw [P.comm]; exact hb') (Ne.symm hxy')
  refine ⟨g₂ ∘ₗ g₁, (P.isAuto_comp hg₂ hg₁).1, (P.isAuto_comp hg₂ hg₁).2, ?_, ?_⟩
  · rw [LinearMap.comp_apply, hg₁x, hg₂x]
  · rw [LinearMap.comp_apply, hg₂y]

@[expose] def toSympConfig : SympConfig V where
  b := P.b
  D := P.D
  self_eq_zero := P.self_eq_zero
  comm := P.comm
  nondeg := P.nondeg
  zero_notMem := P.zero_notMem
  span_eq := P.span_eq
  add_mem := P.add_mem
  eq_of_closed := P.eq_of_closed
  trans := P.trans

end PreConfig

end CFSG.ComponentClassification.OutcomeLocal
