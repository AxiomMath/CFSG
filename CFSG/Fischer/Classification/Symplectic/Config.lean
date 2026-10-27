module

public import Mathlib
public import CFSG.Fischer.Classification.Symplectic.Basic

public section

namespace CFSG.Fischer.Classification.Symplectic

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure SympConfig (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] where
  b : LinearMap.BilinForm (ZMod 2) V
  D : Set V
  self_eq_zero : ∀ v, b v v = 0
  comm : ∀ u v, b u v = b v u
  nondeg : ∀ u, (∀ v, b u v = 0) → u = 0
  zero_notMem : (0 : V) ∉ D
  span_eq : Submodule.span (ZMod 2) D = ⊤
  add_mem : ∀ u ∈ D, ∀ v ∈ D, b u v = 1 → u + v ∈ D
  eq_of_closed : ∀ ℓ ⊆ D, ℓ.Nonempty → (∀ d ∈ D, ∀ p ∈ ℓ, p + b p d • d ∈ ℓ) → ℓ = D
  trans : ∀ x ∈ D, ∀ y ∈ D, ∀ x' ∈ D, ∀ y' ∈ D, x ≠ y → b x y = 0 → x' ≠ y' → b x' y' = 0 →
    ∃ f : V →ₗ[ZMod 2] V, (∀ u v, b (f u) (f v) = b u v) ∧ (∀ u ∈ D, f u ∈ D) ∧ f x = x' ∧
      f y = y'

namespace SympConfig

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (C : SympConfig V)

section Basic

theorem b_cases (u v : V) : C.b u v = 0 ∨ C.b u v = 1 :=
  zmod_two_cases _

theorem b_add_left (u u' v : V) : C.b (u + u') v = C.b u v + C.b u' v := by
  rw [map_add, LinearMap.add_apply]

theorem b_add_right (u v v' : V) : C.b u (v + v') = C.b u v + C.b u v' :=
  map_add _ _ _

theorem ne_zero_of_mem {v : V} (hv : v ∈ C.D) : v ≠ 0 := fun h => C.zero_notMem (h ▸ hv)

theorem injective_of_isometry {f : V →ₗ[ZMod 2] V} (hf : ∀ u v, C.b (f u) (f v) = C.b u v) :
    Function.Injective f := by
  intro u v huv
  rw [← sub_eq_zero]
  refine C.nondeg _ fun w => ?_
  rw [← hf, map_sub, huv, sub_self, map_zero, LinearMap.zero_apply]

theorem exists_mem_b_eq_one {v : V} (hv : v ≠ 0) : ∃ p ∈ C.D, C.b p v = 1 := by
  by_contra h
  push Not at h
  apply hv
  have hlin : C.b v = 0 := LinearMap.ext_on C.span_eq fun p hp => by
    rw [LinearMap.zero_apply, C.comm]
    exact zmod_two_eq_zero_of_ne_one (h p hp)
  exact C.nondeg v fun w => by rw [hlin, LinearMap.zero_apply]

theorem nonempty_of_ne_zero {v : V} (hv : v ≠ 0) : C.D.Nonempty := by
  obtain ⟨p, hp, -⟩ := C.exists_mem_b_eq_one hv
  exact ⟨p, hp⟩

theorem b_eq_zero_of_forall_mem {v : V} (h : ∀ p ∈ C.D, C.b p v = 0) (w : V) : C.b w v = 0 := by
  have hw : w ∈ Submodule.span (ZMod 2) C.D := by rw [C.span_eq]; trivial
  induction hw using Submodule.span_induction with
  | mem p hp => exact h p hp
  | zero => simp
  | add x y _ _ hx hy => rw [C.b_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

theorem eq_zero_of_forall_mem {v : V} (h : ∀ p ∈ C.D, C.b p v = 0) : v = 0 :=
  C.nondeg v fun w => by rw [C.comm]; exact C.b_eq_zero_of_forall_mem h w

end Basic

section Common

theorem exists_common {x y : V} (hx : x ∈ C.D) (hy : y ∈ C.D) (hxy : x ≠ y)
    (hb : C.b x y = 0) : ∃ u ∈ C.D, C.b u x = 1 ∧ C.b u y = 1 := by
  by_contra hne
  push Not at hne
  have hall : ∀ x' ∈ C.D, ∀ y' ∈ C.D, x' ≠ y' → C.b x' y' = 0 → ∀ u ∈ C.D,
      C.b u x' = 1 → C.b u y' = 1 → False := by
    intro x' hx' y' hy' hne' hb' u hu h1 h2
    obtain ⟨f, hfb, hfD, hfx, hfy⟩ := C.trans x' hx' y' hy' x hx y hy hne' hb' hxy hb
    exact hne (f u) (hfD u hu) (by rw [← hfx, hfb, h1]) (by rw [← hfy, hfb, h2])
  have hnbr : ∀ u ∈ C.D, ∀ v ∈ C.D, C.b u v = 1 → ∀ w ∈ C.D, C.b u w = 1 →
      w = v ∨ w = u + v := by
    intro u hu v hv huv w hw huw
    by_contra hw'
    push Not at hw'
    obtain ⟨hwv, hwuv⟩ := hw'
    have h1 : C.b v w = 1 := by
      rcases C.b_cases v w with h | h
      · exact (hall v hv w hw (Ne.symm hwv) h u hu huv huw).elim
      · exact h
    have huv' : u + v ∈ C.D := C.add_mem u hu v hv huv
    have hu' : C.b u (u + v) = 1 := by rw [C.b_add_right, C.self_eq_zero, zero_add, huv]
    have h2 : C.b (u + v) w = 1 := by
      rcases C.b_cases (u + v) w with h | h
      · exact (hall (u + v) huv' w hw (Ne.symm hwuv) h u hu hu' huw).elim
      · exact h
    rw [C.b_add_left, huw, h1, zmod_two_one_add_one] at h2
    exact zero_ne_one h2
  obtain ⟨v₀, hv₀, hv₀x⟩ := C.exists_mem_b_eq_one (C.ne_zero_of_mem hx)
  have hxv₀ : C.b x v₀ = 1 := by rw [C.comm]; exact hv₀x
  have hxv₀D : x + v₀ ∈ C.D := C.add_mem x hx v₀ hv₀ hxv₀
  have hℓ : ({x, v₀, x + v₀} : Set V) = C.D := by
    refine C.eq_of_closed _ ?_ ⟨x, Set.mem_insert _ _⟩ ?_
    · rintro p (rfl | rfl | rfl)
      · exact hx
      · exact hv₀
      · exact hxv₀D
    · intro d hd p hp
      have mem1 : x ∈ ({x, v₀, x + v₀} : Set V) := Or.inl rfl
      have mem2 : v₀ ∈ ({x, v₀, x + v₀} : Set V) := Or.inr (Or.inl rfl)
      have mem3 : x + v₀ ∈ ({x, v₀, x + v₀} : Set V) := Or.inr (Or.inr rfl)
      rcases C.b_cases p d with h | h
      · rw [h, zero_smul, add_zero]
        exact hp
      · rw [h, one_smul]
        rcases hp with hp | hp | hp <;> rw [hp] at h ⊢
        · rcases hnbr x hx v₀ hv₀ hxv₀ d hd h with hd' | hd' <;> rw [hd']
          · exact mem3
          · rw [zmod_two_add_add_self]
            exact mem2
        · rcases hnbr v₀ hv₀ x hx hv₀x d hd h with hd' | hd' <;> rw [hd']
          · rw [add_comm v₀ x]
            exact mem3
          · rw [zmod_two_add_add_self]
            exact mem1
        · have hpx : C.b (x + v₀) x = 1 := by
            rw [C.b_add_left, C.self_eq_zero, zero_add, hv₀x]
          rcases hnbr _ hxv₀D x hx hpx d hd h with hd' | hd' <;> rw [hd']
          · rw [show x + v₀ + x = v₀ by zmod_two_abel]
            exact mem2
          · rw [show x + v₀ + (x + v₀ + x) = x by zmod_two_abel]
            exact mem1
  have hyℓ : y ∈ ({x, v₀, x + v₀} : Set V) := hℓ ▸ hy
  rcases hyℓ with hy' | hy' | hy'
  · exact hxy hy'.symm
  · rw [hy', hxv₀] at hb
    exact one_ne_zero hb
  · rw [hy', C.b_add_right, C.self_eq_zero, zero_add, hxv₀] at hb
    exact one_ne_zero hb

end Common

section Perp

theorem mem_span_perp {s : V} (hs : s ≠ 0) {t : V} (ht : C.b t s = 0) :
    t ∈ Submodule.span (ZMod 2) {p | p ∈ C.D ∧ C.b p s = 0} := by
  set S := Submodule.span (ZMod 2) {p | p ∈ C.D ∧ C.b p s = 0}
  have hmemS : ∀ p ∈ C.D, C.b p s = 0 → p ∈ S := fun p hp hps =>
    Submodule.subset_span ⟨hp, hps⟩
  have hSperp : ∀ w ∈ S, C.b w s = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem p hp => exact hp.2
    | zero => simp
    | add x y _ _ hx hy => rw [C.b_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
  obtain ⟨p₀, hp₀, hp₀s⟩ := C.exists_mem_b_eq_one hs
  have hpair : ∀ p ∈ C.D, ∀ p' ∈ C.D, C.b p s = 1 → C.b p' s = 1 → p + p' ∈ S := by
    intro p hp p' hp' hps hp's
    have hr : ∀ r ∈ C.D, C.b r p = 1 → C.b r p' = 1 → C.b r s = 1 → p + p' ∈ S := by
      intro r hr hrp hrp' hrs
      have h1 : p + r ∈ C.D := C.add_mem p hp r hr (by rw [C.comm, hrp])
      have h2 : p' + r ∈ C.D := C.add_mem p' hp' r hr (by rw [C.comm, hrp'])
      rw [show p + p' = (p + r) + (p' + r) by zmod_two_abel]
      refine S.add_mem (hmemS _ h1 ?_) (hmemS _ h2 ?_)
      · rw [C.b_add_left, hps, hrs, zmod_two_one_add_one]
      · rw [C.b_add_left, hp's, hrs, zmod_two_one_add_one]
    rcases C.b_cases p p' with h | h
    · by_cases hpp : p = p'
      · rw [hpp, zmod_two_add_self]
        exact S.zero_mem
      · obtain ⟨r, hrD, hrp, hrp'⟩ := C.exists_common hp hp' hpp h
        rcases C.b_cases r s with hrs | hrs
        · refine hr (r + p) (C.add_mem r hrD p hp hrp) ?_ ?_ ?_
          · rw [C.b_add_left, hrp, C.self_eq_zero, add_zero]
          · rw [C.b_add_left, hrp', h, add_zero]
          · rw [C.b_add_left, hrs, hps, zero_add]
        · exact hr r hrD hrp hrp' hrs
    · refine hmemS _ (C.add_mem p hp p' hp' h) ?_
      rw [C.b_add_left, hps, hp's, zmod_two_one_add_one]
  have hall : ∀ t : V, t ∈ S ∨ t + p₀ ∈ S := by
    intro t
    have ht' : t ∈ Submodule.span (ZMod 2) C.D := by rw [C.span_eq]; trivial
    induction ht' using Submodule.span_induction with
    | mem p hp =>
      rcases C.b_cases p s with h | h
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
    rw [C.b_add_left, ht, hp₀s, zero_add] at this
    exact one_ne_zero this

theorem eq_zero_or_eq_of_forall {s v : V} (h : ∀ t, C.b t s = 0 → C.b t v = 0) :
    v = 0 ∨ v = s := by
  by_cases hv : ∀ t, C.b t v = 0
  · left
    exact C.nondeg v fun t => by rw [C.comm]; exact hv t
  · right
    push Not at hv
    obtain ⟨t₀, ht₀⟩ := hv
    have ht₀' : C.b t₀ v = 1 := zmod_two_eq_one_of_ne_zero ht₀
    have hs₀ : C.b t₀ s = 1 := by
      rcases C.b_cases t₀ s with h0 | h1
      · exact absurd (h t₀ h0) ht₀
      · exact h1
    have heq : ∀ t, C.b t v = C.b t s := by
      intro t
      rcases C.b_cases t s with h0 | h1
      · rw [h0]
        exact h t h0
      · have := h (t + t₀) (by rw [C.b_add_left, h1, hs₀, zmod_two_one_add_one])
        rw [C.b_add_left, ht₀'] at this
        rw [h1]
        rcases C.b_cases t v with h2 | h2
        · rw [h2, zero_add] at this
          exact absurd this one_ne_zero
        · exact h2
    rw [← sub_eq_zero]
    refine C.nondeg _ fun t => ?_
    rw [C.comm, map_sub, heq t, sub_self]

theorem eq_zero_or_eq_of_perp {s v : V} (hs : s ≠ 0)
    (h : ∀ p ∈ C.D, C.b p s = 0 → C.b p v = 0) : v = 0 ∨ v = s := by
  refine C.eq_zero_or_eq_of_forall fun t ht => ?_
  have hmem := C.mem_span_perp hs ht
  clear ht
  induction hmem using Submodule.span_induction with
  | mem p hp => exact h p hp.1 hp.2
  | zero => simp
  | add x y _ _ hx hy => rw [C.b_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

end Perp

section All

theorem mem_iff_ne_zero_of_all
    (hall : ∀ x ∈ C.D, ∀ y ∈ C.D, x ≠ y → C.b x y = 0 → x + y ∈ C.D) (v : V) :
    v ∈ C.D ↔ v ≠ 0 := by
  refine ⟨C.ne_zero_of_mem, fun hv => ?_⟩
  have key : ∀ w : V, w = 0 ∨ w ∈ C.D := by
    intro w
    have hw : w ∈ Submodule.span (ZMod 2) C.D := by rw [C.span_eq]; trivial
    induction hw using Submodule.span_induction with
    | mem p hp => exact Or.inr hp
    | zero => exact Or.inl rfl
    | add x y _ _ hx hy =>
      rcases hx with rfl | hx
      · rw [zero_add]
        exact hy
      rcases hy with rfl | hy
      · rw [add_zero]
        exact Or.inr hx
      by_cases hxy : x = y
      · left
        rw [hxy, zmod_two_add_self]
      rcases C.b_cases x y with h | h
      · exact Or.inr (hall x hx y hy hxy h)
      · exact Or.inr (C.add_mem x hx y hy h)
    | smul a x _ hx =>
      rcases zmod_two_cases a with rfl | rfl
      · left
        exact zero_smul _ _
      · rwa [one_smul]
  exact (key v).resolve_left hv

theorem all_of_exists {x y : V} (hx : x ∈ C.D) (hy : y ∈ C.D) (hxy : x ≠ y) (hb : C.b x y = 0)
    (hxyD : x + y ∈ C.D) : ∀ x' ∈ C.D, ∀ y' ∈ C.D, x' ≠ y' → C.b x' y' = 0 → x' + y' ∈ C.D := by
  intro x' hx' y' hy' hne hb'
  obtain ⟨f, -, hfD, hfx, hfy⟩ := C.trans x hx y hy x' hx' y' hy' hxy hb hne hb'
  rw [← hfx, ← hfy, ← map_add]
  exact hfD _ hxyD

end All

section Mixed

theorem b_eq_zero_of_dec {s u v : V} (hu : u ∈ C.D) (hv : v ∈ C.D) (hus : C.b u s = 0)
    (hvs : C.b v s = 0) (hsu : s + u ∈ C.D) (hsv : s + v ∉ C.D) : C.b u v = 0 := by
  by_contra h
  have h1 : C.b u v = 1 := zmod_two_eq_one_of_ne_zero h
  have huv : u + v ∈ C.D := C.add_mem u hu v hv h1
  have hb : C.b (u + v) (s + u) = 1 := by
    rw [C.b_add_left, C.b_add_right, C.b_add_right, hus, C.self_eq_zero, hvs, C.comm v u, h1]
    rfl
  have := C.add_mem _ huv _ hsu hb
  rw [show u + v + (s + u) = s + v by zmod_two_abel] at this
  exact hsv this

theorem not_mixed (hnone : ∀ x ∈ C.D, ∀ y ∈ C.D, x ≠ y → C.b x y = 0 → x + y ∉ C.D)
    {x y z z' : V} (hx : x ∈ C.D) (hy : y ∈ C.D) (hz : z ∈ C.D) (hz' : z' ∈ C.D) (hxy : x ≠ y)
    (hbxy : C.b x y = 0) (hzx : C.b z x = 0) (hzy : C.b z y = 0) (hzx' : z ≠ x) (hzy' : z ≠ y)
    (hT : x + y + z ∈ C.D) (hz'x : C.b z' x = 0) (hz'y : C.b z' y = 0) (hz'x' : z' ≠ x)
    (hN : x + y + z' ∉ C.D) : False := by
  have hs0 : x + y ≠ 0 := fun h => hxy (zmod_two_eq_of_add_eq_zero h)
  have hsD : x + y ∉ C.D := hnone x hx y hy hxy hbxy
  have hperp : ∀ c, C.b c x = 0 → C.b c y = 0 → C.b c (x + y) = 0 := fun c h1 h2 => by
    rw [C.b_add_right, h1, h2, add_zero]
  have hxs : C.b x (x + y) = 0 := hperp x (C.self_eq_zero x) hbxy
  have hsx : x + y + x ∈ C.D := by rw [show x + y + x = y by zmod_two_abel]; exact hy
  have hz's : C.b z' (x + y) = 0 := hperp z' hz'x hz'y
  have hND : ∀ p ∈ C.D, C.b p (x + y) = 0 → x + y + p ∈ C.D → C.b p z' = 0 :=
    fun p hp hps hsp => C.b_eq_zero_of_dec hp hz' hps hz's hsp hN
  obtain ⟨u, hu, hux, huz'⟩ := C.exists_common hx hz' (Ne.symm hz'x')
    (by rw [C.comm]; exact hz'x)
  have hus : C.b u (x + y) = 1 := by
    rcases C.b_cases u (x + y) with h | h
    · exfalso
      by_cases hsu : x + y + u ∈ C.D
      · have := hND u hu h hsu
        rw [huz'] at this
        exact one_ne_zero this
      · have := C.b_eq_zero_of_dec hx hu hxs h hsx hsu
        rw [C.comm, hux] at this
        exact one_ne_zero this
    · exact h
  have huy : C.b u y = 0 := by
    rw [C.b_add_right, hux] at hus
    rcases C.b_cases u y with h | h
    · exact h
    · rw [h, zmod_two_one_add_one] at hus
      exact absurd hus zero_ne_one
  have key : ∀ c ∈ C.D, C.b c x = 0 → C.b c y = 0 → c ≠ x → c ≠ y → x + y + c ∈ C.D →
      C.b u c = 1 → False := by
    intro c hc hcx hcy hcx' hcy' hsc huc
    have hcs : C.b c (x + y) = 0 := hperp c hcx hcy
    have hcz' : C.b c z' = 0 := hND c hc hcs hsc
    have hxu : x + u ∈ C.D := C.add_mem x hx u hu (by rw [C.comm, hux])
    have hxuc : x + u + c ∈ C.D := C.add_mem _ hxu c hc (by
      rw [C.b_add_left, C.comm x c, hcx, huc, zero_add])
    have huz'D : u + z' ∈ C.D := C.add_mem u hu z' hz' huz'
    have ha : x + c + z' ∈ C.D := by
      have hb : C.b (x + u + c) (u + z') = 1 := by
        rw [C.b_add_left, C.b_add_left, C.b_add_right, C.b_add_right, C.b_add_right,
          C.comm x u, hux, C.comm x z', hz'x, C.self_eq_zero, huz', C.comm c u, huc, hcz']
        rfl
      have := C.add_mem _ hxuc _ huz'D hb
      rwa [show x + u + c + (u + z') = x + c + z' by zmod_two_abel] at this
    have has : C.b (x + c + z') (x + y) = 0 := by
      rw [C.b_add_left, C.b_add_left, hxs, hcs, hz's, add_zero, add_zero]
    by_cases hsa : x + y + (x + c + z') ∈ C.D
    ·
      have hz'0 : z' = 0 ∨ z' = x + y := C.eq_zero_or_eq_of_perp hs0 fun p hp hps => by
        by_cases hsp : x + y + p ∈ C.D
        · exact hND p hp hps hsp
        · rw [show z' = (x + c + z') + x + c by zmod_two_abel, C.b_add_right, C.b_add_right,
            C.comm p, C.b_eq_zero_of_dec ha hp has hps hsa hsp, C.comm p,
            C.b_eq_zero_of_dec hx hp hxs hps hsx hsp, C.comm p,
            C.b_eq_zero_of_dec hc hp hcs hps hsc hsp, add_zero, add_zero]
      rcases hz'0 with h | h
      · exact C.zero_notMem (h ▸ hz')
      · exact hsD (h ▸ hz')
    ·
      have hxc : x + c = 0 ∨ x + c = x + y := C.eq_zero_or_eq_of_perp hs0 fun p hp hps => by
        by_cases hsp : x + y + p ∈ C.D
        · rw [show x + c = (x + c + z') + z' by zmod_two_abel, C.b_add_right,
            C.b_eq_zero_of_dec hp ha hps has hsp hsa, hND p hp hps hsp, add_zero]
        · rw [C.b_add_right, C.comm p, C.b_eq_zero_of_dec hx hp hxs hps hsx hsp, C.comm p,
            C.b_eq_zero_of_dec hc hp hcs hps hsc hsp, add_zero]
      rcases hxc with h | h
      · exact hcx' (zmod_two_eq_of_add_eq_zero h).symm
      · exact hcy' (by simpa using congrArg (x + ·) h)
  have hwx : C.b (x + y + z) x = 0 := by
    rw [C.b_add_left, C.b_add_left, C.self_eq_zero, C.comm y x, hbxy, hzx, add_zero, add_zero]
  have hwy : C.b (x + y + z) y = 0 := by
    rw [C.b_add_left, C.b_add_left, C.self_eq_zero, hbxy, hzy, add_zero, add_zero]
  rcases C.b_cases u z with h | h
  · refine key (x + y + z) hT hwx hwy (fun h' => hzy' ?_) (fun h' => hzx' ?_) ?_ ?_
    · have := congrArg (· + (x + z)) h'
      simpa [add_assoc, add_left_comm, add_comm, zmod_two_add_self, zmod_two_add_add_self]
        using this.symm
    · have := congrArg (· + (y + z)) h'
      simpa [add_assoc, add_left_comm, add_comm, zmod_two_add_self, zmod_two_add_add_self]
        using this.symm
    · rw [show x + y + (x + y + z) = z by zmod_two_abel]
      exact hz
    · rw [C.b_add_right, C.b_add_right, hux, huy, h]
      rfl
  · exact key z hz hzx hzy hzx' hzy' hT h

end Mixed

section Orthogonal

@[expose] def IsTTriple (x y z : V) : Prop :=
  x ∈ C.D ∧ y ∈ C.D ∧ z ∈ C.D ∧ x ≠ y ∧ C.b x y = 0 ∧ C.b z x = 0 ∧ C.b z y = 0 ∧ z ≠ x ∧
    z ≠ y ∧ x + y + z ∈ C.D

theorem exists_tTriple_of_tTriple {x y z : V} (h : C.IsTTriple x y z) {x' y' : V}
    (hx' : x' ∈ C.D) (hy' : y' ∈ C.D) (hne : x' ≠ y') (hb : C.b x' y' = 0) :
    ∃ z', C.IsTTriple x' y' z' := by
  obtain ⟨hx, hy, hz, hxy, hbxy, hzx, hzy, hzx', hzy', hT⟩ := h
  obtain ⟨f, hfb, hfD, hfx, hfy⟩ := C.trans x hx y hy x' hx' y' hy' hxy hbxy hne hb
  have hinj := C.injective_of_isometry hfb
  refine ⟨f z, hx', hy', hfD z hz, hne, hb, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hfx, hfb, hzx]
  · rw [← hfy, hfb, hzy]
  · rw [← hfx]
    exact fun h' => hzx' (hinj h')
  · rw [← hfy]
    exact fun h' => hzy' (hinj h')
  · rw [← hfx, ← hfy, ← map_add, ← map_add]
    exact hfD _ hT

theorem add_add_mem_of_tTriple
    (hnone : ∀ x ∈ C.D, ∀ y ∈ C.D, x ≠ y → C.b x y = 0 → x + y ∉ C.D) {x₀ y₀ z₀ : V}
    (h₀ : C.IsTTriple x₀ y₀ z₀) {x y z : V} (hx : x ∈ C.D) (hy : y ∈ C.D) (hz : z ∈ C.D)
    (hxy : x ≠ y) (hbxy : C.b x y = 0) (hzx : C.b z x = 0) (hzy : C.b z y = 0) (hzx' : z ≠ x) :
    x + y + z ∈ C.D := by
  by_contra hN
  obtain ⟨w, hw⟩ := C.exists_tTriple_of_tTriple h₀ hx hy hxy hbxy
  obtain ⟨-, -, hwD, -, -, hwx, hwy, hwx', hwy', hT⟩ := hw
  exact C.not_mixed hnone hx hy hwD hz hxy hbxy hwx hwy hwx' hwy' hT hzx hzy hzx' hN

theorem mem_or_add_mem
    (hT : ∀ x ∈ C.D, ∀ y ∈ C.D, ∀ z ∈ C.D, x ≠ y → C.b x y = 0 → C.b z x = 0 → C.b z y = 0 →
      z ≠ x → z ≠ y → x + y + z ∈ C.D)
    {x v : V} (hx : x ∈ C.D) (hvx : C.b v x = 0) (hv0 : v ≠ 0) (hvx' : v ≠ x) :
    v ∈ C.D ∨ x + v ∈ C.D := by
  have key : ∀ t ∈ Submodule.span (ZMod 2) {p | p ∈ C.D ∧ C.b p x = 0},
      ∃ d, (d = 0 ∨ (d ∈ C.D ∧ C.b d x = 0)) ∧ (t = d ∨ t = d + x) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem p hp => exact ⟨p, Or.inr hp, Or.inl rfl⟩
    | zero => exact ⟨0, Or.inl rfl, Or.inl rfl⟩
    | add t₁ t₂ _ _ h₁ h₂ =>
      obtain ⟨d₁, hd₁, ht₁⟩ := h₁
      obtain ⟨d₂, hd₂, ht₂⟩ := h₂
      have hsum : ∃ d, (d = 0 ∨ (d ∈ C.D ∧ C.b d x = 0)) ∧ (d₁ + d₂ = d ∨ d₁ + d₂ = d + x) := by
        rcases hd₁ with rfl | ⟨hd₁D, hd₁x⟩
        · exact ⟨d₂, hd₂, Or.inl (zero_add _)⟩
        rcases hd₂ with rfl | ⟨hd₂D, hd₂x⟩
        · exact ⟨d₁, Or.inr ⟨hd₁D, hd₁x⟩, Or.inl (add_zero _)⟩
        by_cases h12 : d₁ = d₂
        · exact ⟨0, Or.inl rfl, Or.inl (by rw [h12, zmod_two_add_self])⟩
        rcases C.b_cases d₁ d₂ with h | h
        · by_cases h1x : d₁ = x
          · exact ⟨d₂, Or.inr ⟨hd₂D, hd₂x⟩, Or.inr (by rw [h1x, add_comm])⟩
          by_cases h2x : d₂ = x
          · exact ⟨d₁, Or.inr ⟨hd₁D, hd₁x⟩, Or.inr (by rw [h2x])⟩
          refine ⟨x + d₁ + d₂, Or.inr ⟨?_, ?_⟩, Or.inr (by zmod_two_abel)⟩
          · exact hT x hx d₁ hd₁D d₂ hd₂D (Ne.symm h1x) (by rw [C.comm]; exact hd₁x)
              (by rw [hd₂x]) (by rw [C.comm]; exact h) h2x (Ne.symm h12)
          · rw [C.b_add_left, C.b_add_left, C.self_eq_zero, hd₁x, hd₂x, add_zero, add_zero]
        · refine ⟨d₁ + d₂, Or.inr ⟨C.add_mem d₁ hd₁D d₂ hd₂D h, ?_⟩, Or.inl rfl⟩
          rw [C.b_add_left, hd₁x, hd₂x, add_zero]
      obtain ⟨d, hd, hsum⟩ := hsum
      refine ⟨d, hd, ?_⟩
      rcases ht₁ with ht₁ | ht₁ <;> rcases ht₂ with ht₂ | ht₂ <;> rw [ht₁, ht₂] <;>
        rcases hsum with hs | hs
      · exact Or.inl hs
      · exact Or.inr hs
      · right
        rw [← add_assoc, hs]
      · left
        rw [← add_assoc, hs, add_assoc, zmod_two_add_self, add_zero]
      · right
        rw [show d₁ + x + d₂ = d₁ + d₂ + x by zmod_two_abel, hs]
      · left
        rw [show d₁ + x + d₂ = d₁ + d₂ + x by zmod_two_abel, hs, add_assoc, zmod_two_add_self,
          add_zero]
      · left
        rw [show d₁ + x + (d₂ + x) = d₁ + d₂ by zmod_two_abel, hs]
      · right
        rw [show d₁ + x + (d₂ + x) = d₁ + d₂ by zmod_two_abel, hs]
    | smul a t _ h =>
      rcases zmod_two_cases a with rfl | rfl
      · exact ⟨0, Or.inl rfl, Or.inl (zero_smul _ _)⟩
      · rwa [one_smul]
  obtain ⟨d, hd, hv⟩ := key v (C.mem_span_perp (C.ne_zero_of_mem hx) hvx)
  rcases hv with rfl | rfl
  · rcases hd with rfl | ⟨hdD, -⟩
    · exact absurd rfl hv0
    · exact Or.inl hdD
  · rcases hd with rfl | ⟨hdD, -⟩
    · exact absurd (zero_add x) hvx'
    · right
      rw [show x + (d + x) = d by zmod_two_abel]
      exact hdD

theorem exists_quadraticForm
    (hnone : ∀ x ∈ C.D, ∀ y ∈ C.D, x ≠ y → C.b x y = 0 → x + y ∉ C.D)
    (hT : ∀ x ∈ C.D, ∀ y ∈ C.D, ∀ z ∈ C.D, x ≠ y → C.b x y = 0 → C.b z x = 0 → C.b z y = 0 →
      z ≠ x → z ≠ y → x + y + z ∈ C.D) :
    ∃ Q : QuadraticForm (ZMod 2) V, (∀ u v, QuadraticMap.polar Q u v = C.b u v) ∧
      ∀ v, v ∈ C.D ↔ Q v = 1 := by
  classical
  let q : V → ZMod 2 := fun v => if v ∈ C.D then 1 else 0
  have hq1 : ∀ v, q v = 1 ↔ v ∈ C.D := fun v => by
    by_cases h : v ∈ C.D
    · simp [q, h]
    · simp [q, h]
  have hq0 : ∀ v, v ∉ C.D → q v = 0 := fun v h => by simp [q, h]
  have hqD : ∀ v, v ∈ C.D → q v = 1 := fun v h => (hq1 v).2 h
  have hmem : ∀ x ∈ C.D, ∀ v, q (x + v) = q x + q v + C.b x v := by
    intro x hx v
    rw [hqD x hx]
    rcases C.b_cases x v with h | h
    · rw [h, add_zero]
      by_cases hv0 : v = 0
      · rw [hv0, add_zero, hqD x hx, hq0 0 C.zero_notMem, add_zero]
      by_cases hvx : v = x
      · rw [hvx, zmod_two_add_self, hq0 0 C.zero_notMem, hqD x hx, zmod_two_one_add_one]
      rcases C.mem_or_add_mem hT hx (by rw [C.comm]; exact h) hv0 hvx with hv | hv
      · rw [hqD v hv, zmod_two_one_add_one,
          hq0 _ (hnone x hx v hv (Ne.symm hvx) h)]
      · have hvD : v ∉ C.D := fun hv' => hnone x hx v hv' (Ne.symm hvx) h hv
        rw [hqD _ hv, hq0 v hvD, add_zero]
    · rw [h]
      by_cases hv : v ∈ C.D
      · rw [hqD v hv, hqD _ (C.add_mem x hx v hv h)]
        rfl
      · have hxv : x + v ∉ C.D := fun h' => hv (by
          have := C.add_mem x hx _ h' (by rw [C.b_add_right, C.self_eq_zero, zero_add, h])
          rwa [zmod_two_add_add_self] at this)
        rw [hq0 v hv, hq0 _ hxv, add_zero, zmod_two_one_add_one]
  have hadd : ∀ u v, q (u + v) = q u + q v + C.b u v := by
    intro u
    have hu : u ∈ Submodule.span (ZMod 2) C.D := by rw [C.span_eq]; trivial
    induction hu using Submodule.span_induction with
    | mem p hp => exact hmem p hp
    | zero => intro v; rw [zero_add, hq0 0 C.zero_notMem, zero_add, map_zero,
        LinearMap.zero_apply, add_zero]
    | add u₁ u₂ _ _ h₁ h₂ =>
      intro v
      rw [add_assoc, h₁, h₂, h₁ u₂, C.b_add_left, C.b_add_right]
      ring
    | smul a u _ h =>
      rcases zmod_two_cases a with rfl | rfl
      · intro v
        rw [zero_smul, zero_add, hq0 0 C.zero_notMem, zero_add, map_zero, LinearMap.zero_apply,
          add_zero]
      · rwa [one_smul]
  let Q : QuadraticForm (ZMod 2) V :=
    { toFun := q
      toFun_smul := fun a v => by
        rcases zmod_two_cases a with rfl | rfl
        · rw [zero_smul, hq0 0 C.zero_notMem, zero_mul, zero_smul]
        · rw [one_smul, one_mul, one_smul]
      exists_companion' := ⟨C.b, hadd⟩ }
  refine ⟨Q, fun u v => ?_, fun v => (hq1 v).symm⟩
  show q (u + v) - q u - q v = C.b u v
  rw [hadd]
  ring

end Orthogonal

section PlusFour

theorem fin_two_eq_of_dot (a₁ a₂ p₁ p₂ q₁ q₂ : ZMod 2) (ha : ¬ (a₁ = 0 ∧ a₂ = 0))
    (hp : ¬ (p₁ = 0 ∧ p₂ = 0)) (hq : ¬ (q₁ = 0 ∧ q₂ = 0)) (h1 : a₁ * p₁ + a₂ * p₂ = 0)
    (h2 : a₁ * q₁ + a₂ * q₂ = 0) : p₁ = q₁ ∧ p₂ = q₂ := by
  have key : ∀ a₁ a₂ p₁ p₂ q₁ q₂ : Fin 2, ¬ (a₁ = 0 ∧ a₂ = 0) → ¬ (p₁ = 0 ∧ p₂ = 0) →
      ¬ (q₁ = 0 ∧ q₂ = 0) → a₁ * p₁ + a₂ * p₂ = 0 → a₁ * q₁ + a₂ * q₂ = 0 →
      p₁ = q₁ ∧ p₂ = q₂ := by
    decide
  exact key a₁ a₂ p₁ p₂ q₁ q₂ ha hp hq h1 h2

theorem not_exists_totallySingular [FiniteDimensional (ZMod 2) V]
    (hdim : Module.finrank (ZMod 2) V = 4) {Q : QuadraticForm (ZMod 2) V}
    (hpol : ∀ u v, QuadraticMap.polar Q u v = C.b u v) (hQ : ∀ v, v ∈ C.D ↔ Q v = 1) :
    ¬ ∃ W : Submodule (ZMod 2) V, Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0 := by
  rintro ⟨W, hW2, hWQ⟩
  have hbW : ∀ w ∈ W, ∀ w' ∈ W, C.b w w' = 0 := by
    intro w hw w' hw'
    rw [← hpol, QuadraticMap.polar, hWQ _ (W.add_mem hw hw'), hWQ w hw, hWQ w' hw', sub_zero,
      sub_zero]
  have hnd : C.b.Nondegenerate :=
    ⟨fun u hu => C.nondeg u hu, fun u hu => C.nondeg u fun v => by rw [C.comm]; exact hu v⟩
  have hperp : C.b.orthogonal W = W := by
    symm
    refine Submodule.eq_of_le_of_finrank_eq (fun w hw => ?_) ?_
    · rw [LinearMap.BilinForm.mem_orthogonal_iff]
      exact fun n hn => hbW n hn w hw
    · rw [LinearMap.BilinForm.finrank_orthogonal hnd, hdim, hW2]
  let bW := Module.finBasisOfFinrankEq (ZMod 2) W hW2
  set w₁ : V := ((bW 0 : W) : V)
  set w₂ : V := ((bW 1 : W) : V)
  have hw₁ : w₁ ∈ W := (bW 0).2
  have hw₂ : w₂ ∈ W := (bW 1).2
  have hsing : ∀ v, C.b w₁ v = 0 → C.b w₂ v = 0 → Q v = 0 := by
    intro v h1 h2
    refine hWQ v ?_
    rw [← hperp, LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    have hrepr := bW.sum_repr ⟨n, hn⟩
    rw [Fin.sum_univ_two] at hrepr
    have hn' : n = bW.repr ⟨n, hn⟩ 0 • w₁ + bW.repr ⟨n, hn⟩ 1 • w₂ := by
      have := congrArg Subtype.val hrepr
      simpa [w₁, w₂] using this.symm
    rw [hn', map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, h1, h2, smul_zero, smul_zero, add_zero]
  have hnz : ∀ v, Q v = 1 → ¬ (C.b w₁ v = 0 ∧ C.b w₂ v = 0) := fun v hv h => by
    rw [hsing v h.1 h.2] at hv
    exact zero_ne_one hv
  have hli : ∀ a₁ a₂ : ZMod 2, a₁ • w₁ + a₂ • w₂ = 0 → a₁ = 0 ∧ a₂ = 0 := by
    intro a₁ a₂ h
    have h' : a₁ • bW 0 + a₂ • bW 1 = 0 := Subtype.ext (by simpa [w₁, w₂] using h)
    have := Fintype.linearIndependent_iff.1 bW.linearIndependent ![a₁, a₂]
      (by rw [Fin.sum_univ_two]; simpa using h')
    exact ⟨this 0, this 1⟩
  have hV0 : (w₁ : V) ≠ 0 := fun h => by
    have := hli 1 0 (by rw [one_smul, zero_smul, add_zero, h])
    exact one_ne_zero this.1
  obtain ⟨x, hx⟩ := C.nonempty_of_ne_zero hV0
  have hx1 : Q x = 1 := (hQ x).1 hx
  obtain ⟨a₁, a₂, ha, hk⟩ : ∃ a₁ a₂ : ZMod 2, ¬ (a₁ = 0 ∧ a₂ = 0) ∧
      a₁ * C.b w₁ x + a₂ * C.b w₂ x = 0 := by
    rcases C.b_cases w₁ x with h1 | h1
    · exact ⟨1, 0, by simp, by rw [h1]; ring⟩
    rcases C.b_cases w₂ x with h2 | h2
    · exact ⟨0, 1, by simp, by rw [h2]; ring⟩
    · exact ⟨1, 1, by simp, by rw [h1, h2]; rfl⟩
  set k : V := a₁ • w₁ + a₂ • w₂ with hk_def
  have hkW : k ∈ W := W.add_mem (W.smul_mem _ hw₁) (W.smul_mem _ hw₂)
  have hk0 : k ≠ 0 := fun h => ha (hli a₁ a₂ h)
  have hbk : ∀ v, C.b k v = a₁ * C.b w₁ v + a₂ * C.b w₂ v := fun v => by
    rw [hk_def, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  have hkx : C.b k x = 0 := by rw [hbk]; exact hk
  have hy : x + k ∈ C.D := by
    rw [hQ]
    have := hpol x k
    rw [QuadraticMap.polar, C.comm, hkx, hx1, hWQ k hkW, sub_zero] at this
    rw [show Q (x + k) = Q (x + k) - 1 + 1 by ring, this]
    rfl
  have hxy : x ≠ x + k := fun h => hk0 (by simpa using (congrArg (· - x) h).symm)
  have hbxy : C.b x (x + k) = 0 := by rw [C.b_add_right, C.self_eq_zero, C.comm, hkx, add_zero]
  obtain ⟨u, hu, hux, huy⟩ := C.exists_common hx hy hxy hbxy
  have hu1 : Q u = 1 := (hQ u).1 hu
  have hku : C.b k u = 0 := by
    rw [C.b_add_right, hux] at huy
    rw [C.comm]
    rcases C.b_cases u k with h | h
    · exact h
    · rw [h, zmod_two_one_add_one] at huy
      exact absurd huy zero_ne_one
  have hsame := fin_two_eq_of_dot a₁ a₂ _ _ _ _ ha (hnz x hx1) (hnz u hu1) hk
    (by rw [← hbk]; exact hku)
  have hux' : Q (u + x) = 0 := hsing _ (by rw [C.b_add_right, hsame.1, zmod_two_add_self])
    (by rw [C.b_add_right, hsame.2, zmod_two_add_self])
  rw [(hQ _).1 (C.add_mem u hu x hx hux)] at hux'
  exact one_ne_zero hux'

end PlusFour

theorem trichotomy :
    ((∀ v, v ∈ C.D ↔ v ≠ 0) ∧ ∃ x ∈ C.D, ∃ y ∈ C.D, x ≠ y ∧ C.b x y = 0) ∨
    ((∃ Q : QuadraticForm (ZMod 2) V, (∀ u v, QuadraticMap.polar Q u v = C.b u v) ∧
      ∀ v, v ∈ C.D ↔ Q v = 1) ∧ ∃ x ∈ C.D, ∃ y ∈ C.D, x ≠ y ∧ C.b x y = 0) ∨
    (∀ x ∈ C.D, ∀ y ∈ C.D, ∀ z ∈ C.D, x ≠ y → C.b x y = 0 → C.b z x = 0 → C.b z y = 0 →
      z ≠ x → z ≠ y → x + y + z ∉ C.D) := by
  by_cases hall : ∃ x ∈ C.D, ∃ y ∈ C.D, x ≠ y ∧ C.b x y = 0 ∧ x + y ∈ C.D
  · obtain ⟨x, hx, y, hy, hxy, hb, hxyD⟩ := hall
    exact Or.inl ⟨C.mem_iff_ne_zero_of_all (C.all_of_exists hx hy hxy hb hxyD),
      x, hx, y, hy, hxy, hb⟩
  have hnone : ∀ x ∈ C.D, ∀ y ∈ C.D, x ≠ y → C.b x y = 0 → x + y ∉ C.D :=
    fun x hx y hy hxy hb hxyD => hall ⟨x, hx, y, hy, hxy, hb, hxyD⟩
  by_cases hT : ∃ x y z, C.IsTTriple x y z
  · obtain ⟨x₀, y₀, z₀, h₀⟩ := hT
    right
    left
    refine ⟨C.exists_quadraticForm hnone fun x hx y hy z hz hxy hb hzx hzy hzx' _ =>
      C.add_add_mem_of_tTriple hnone h₀ hx hy hz hxy hb hzx hzy hzx', ?_⟩
    obtain ⟨hx, hy, -, hxy, hb, -⟩ := h₀
    exact ⟨x₀, hx, y₀, hy, hxy, hb⟩
  · right
    right
    intro x hx y hy z hz hxy hb hzx hzy hzx' hzy' hxyz
    exact hT ⟨x, y, z, hx, hy, hz, hxy, hb, hzx, hzy, hzx', hzy', hxyz⟩

end SympConfig

end CFSG.Fischer.Classification.Symplectic
