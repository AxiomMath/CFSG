module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOnePerfect

public section

namespace CFSG.EvenSporadicStandard.HypOne.Fi23

open Subgroup CFSG.ComponentClassification.M12Cover CFSG.EvenSporadicStandard.TwoCo1.HypOne

variable {G F : Type*} [Group G] [Group F] {u : G}

theorem exists_lift (κ : ↥(centralizer ({u} : Set G)) →* F) (hs : Function.Surjective κ)
    (hker : ∀ c, κ c = 1 → (c : G) = 1 ∨ (c : G) = u) {r : G} (hrc : r * u = u * r)
    (hL1 : ∀ g : G, g * r * g⁻¹ ≠ u * r) (v : F)
    (hv : v * κ ⟨r, mem_centralizer_singleton_iff.2 hrc⟩ =
      κ ⟨r, mem_centralizer_singleton_iff.2 hrc⟩ * v) :
    ∃ y : ↥(centralizer ({u} : Set G)), κ y = v ∧ (y : G) * r = r * (y : G) := by
  obtain ⟨y, rfl⟩ := hs v
  refine ⟨y, rfl, ?_⟩
  set rU : ↥(centralizer ({u} : Set G)) := ⟨r, mem_centralizer_singleton_iff.2 hrc⟩ with hrU
  have h1 : κ (y * rU * y⁻¹ * rU⁻¹) = 1 := by
    have h2 : κ y * κ rU * (κ y)⁻¹ = κ rU := by rw [hv]; group
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h2, mul_inv_cancel]
  rcases hker _ h1 with h | h
  · have h' : (y : G) * r * (y : G)⁻¹ * r⁻¹ = 1 := h
    calc (y : G) * r = (y : G) * r * (y : G)⁻¹ * r⁻¹ * (r * (y : G)) := by group
      _ = r * (y : G) := by rw [h', one_mul]
  · exfalso
    have h' : (y : G) * r * (y : G)⁻¹ * r⁻¹ = u := h
    refine hL1 y ?_
    calc (y : G) * r * (y : G)⁻¹ = (y : G) * r * (y : G)⁻¹ * r⁻¹ * r := by group
      _ = u * r := by rw [h']

theorem sq_mem_of_few_conjugates [Finite G] (κ : ↥(centralizer ({u} : Set G)) →* F)
    (hs : Function.Surjective κ) (hker : ∀ c, κ c = 1 → (c : G) = 1 ∨ (c : G) = u)
    (hF : ∀ v : F, orderOf v = 2 → FourClassesLarge ↥(centralizer ({v} : Set F)))
    {r : G} (hrr : r * r = 1) (hr1 : r ≠ 1) (hru : r ≠ u) (hrc : r * u = u * r)
    (hL1 : ∀ g : G, g * r * g⁻¹ ≠ u * r)
    {x : G} (hxr : x * r = r * x) (hxu : x * u = u * x) (hx4 : x ^ 4 = 1)
    (hfew : ¬ 5 ≤ Nat.card {y : ↥(centralizer ({r} : Set G)) //
      IsConj (⟨x, mem_centralizer_singleton_iff.2 hxr⟩ : ↥(centralizer ({r} : Set G))) y}) :
    x ^ 2 = 1 ∨ x ^ 2 = u := by
  classical
  set rU : ↥(centralizer ({u} : Set G)) := ⟨r, mem_centralizer_singleton_iff.2 hrc⟩ with hrU
  set xU : ↥(centralizer ({u} : Set G)) := ⟨x, mem_centralizer_singleton_iff.2 hxu⟩ with hxU
  set b : F := κ rU with hb
  have hb2 : orderOf b = 2 := by
    have hrU2 : rU * rU = 1 := Subtype.ext hrr
    refine orderOf_eq_prime (by rw [hb, sq, ← map_mul, hrU2, map_one]) ?_
    intro h
    rcases hker rU h with h1 | h1
    · exact hr1 h1
    · exact hru h1
  by_cases h2 : κ xU ^ 2 = 1
  · have hx2 : κ (xU ^ 2) = 1 := by rw [map_pow]; exact h2
    rcases hker (xU ^ 2) hx2 with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
  · exfalso
    apply hfew
    set x' : F := κ xU with hx'
    have hcomm : x' * b = b * x' := by
      rw [hx', hb, ← map_mul, ← map_mul]
      exact congrArg κ (Subtype.ext hxr)
    set xhat : ↥(centralizer ({b} : Set F)) := ⟨x', mem_centralizer_singleton_iff.2 hcomm⟩
      with hxhat
    have hxU4 : xU ^ 4 = 1 := Subtype.ext (by simpa using hx4)
    have hxhat4 : xhat ^ 4 = 1 := Subtype.ext (by
      show x' ^ 4 = 1
      rw [hx', ← map_pow, hxU4, map_one])
    have hxhat2 : xhat ^ 2 ≠ 1 := fun h => h2 (congrArg Subtype.val h)
    have h5 := hF b hb2 xhat hxhat4 hxhat2
    refine h5.trans ?_
    set xC : ↥(centralizer ({r} : Set G)) := ⟨x, mem_centralizer_singleton_iff.2 hxr⟩ with hxC
    let S : Set ↥(centralizer ({r} : Set G)) := {y | ∃ g : ↥(centralizer ({u} : Set G)),
      (g : G) * r = r * (g : G) ∧ (y : G) = g * x * (g : G)⁻¹}
    have hSU : ∀ y : S, ((y : ↥(centralizer ({r} : Set G))) : G) ∈ centralizer ({u} : Set G) := by
      rintro ⟨y, g, hg, hy⟩
      show (y : G) ∈ centralizer ({u} : Set G)
      rw [hy]
      exact mul_mem (mul_mem g.2 xU.2) (inv_mem g.2)
    have hSb : ∀ y : S, κ ⟨((y : ↥(centralizer ({r} : Set G))) : G), hSU y⟩ * b =
        b * κ ⟨((y : ↥(centralizer ({r} : Set G))) : G), hSU y⟩ := by
      intro y
      rw [hb, ← map_mul, ← map_mul]
      exact congrArg κ (Subtype.ext (by
        have := mem_centralizer_singleton_iff.1 (y : ↥(centralizer ({r} : Set G))).2
        exact this))
    have hSconj : ∀ y : S, IsConj xhat ⟨κ ⟨((y : ↥(centralizer ({r} : Set G))) : G), hSU y⟩,
        mem_centralizer_singleton_iff.2 (hSb y)⟩ := by
      intro y
      obtain ⟨g, hg, hy⟩ := y.2
      have hgb : κ g * b = b * κ g := by
        rw [hb, ← map_mul, ← map_mul]
        exact congrArg κ (Subtype.ext hg)
      refine isConj_iff.2 ⟨⟨κ g, mem_centralizer_singleton_iff.2 hgb⟩, Subtype.ext ?_⟩
      have hyU : (⟨((y : ↥(centralizer ({r} : Set G))) : G), hSU y⟩ :
          ↥(centralizer ({u} : Set G))) = g * xU * g⁻¹ :=
        Subtype.ext (by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
          exact hy)
      show κ g * x' * (κ g)⁻¹ = κ ⟨((y : ↥(centralizer ({r} : Set G))) : G), hSU y⟩
      rw [hyU, map_mul, map_mul, map_inv]
    let Φ : S → {y : ↥(centralizer ({b} : Set F)) // IsConj xhat y} := fun y =>
      ⟨⟨κ ⟨((y : ↥(centralizer ({r} : Set G))) : G), hSU y⟩,
        mem_centralizer_singleton_iff.2 (hSb y)⟩, hSconj y⟩
    have hΦ : Function.Surjective Φ := by
      rintro ⟨z, hz⟩
      obtain ⟨ĝ, hĝ⟩ := isConj_iff.1 hz
      obtain ⟨g, hgκ, hgr⟩ := exists_lift κ hs hker hrc hL1 (ĝ : F)
        (mem_centralizer_singleton_iff.1 ĝ.2)
      have hgi : (g : G)⁻¹ * r = r * (g : G)⁻¹ := by
        calc (g : G)⁻¹ * r = (g : G)⁻¹ * (r * g) * (g : G)⁻¹ := by group
          _ = (g : G)⁻¹ * (g * r) * (g : G)⁻¹ := by rw [hgr]
          _ = r * (g : G)⁻¹ := by group
      have hgy : (g : G) * x * (g : G)⁻¹ * r = r * ((g : G) * x * (g : G)⁻¹) := by
        calc (g : G) * x * (g : G)⁻¹ * r = (g : G) * x * ((g : G)⁻¹ * r) := by group
          _ = (g : G) * x * (r * (g : G)⁻¹) := by rw [hgi]
          _ = (g : G) * (x * r) * (g : G)⁻¹ := by group
          _ = (g : G) * (r * x) * (g : G)⁻¹ := by rw [hxr]
          _ = ((g : G) * r) * x * (g : G)⁻¹ := by group
          _ = (r * (g : G)) * x * (g : G)⁻¹ := by rw [hgr]
          _ = r * ((g : G) * x * (g : G)⁻¹) := by group
      have hgyU : (g : G) * x * (g : G)⁻¹ ∈ centralizer ({u} : Set G) :=
        mul_mem (mul_mem g.2 xU.2) (inv_mem g.2)
      let y : ↥(centralizer ({r} : Set G)) :=
        ⟨(g : G) * x * (g : G)⁻¹, mem_centralizer_singleton_iff.2 hgy⟩
      have hyS : y ∈ S := ⟨g, hgr, rfl⟩
      refine ⟨⟨y, hyS⟩, Subtype.ext (Subtype.ext ?_)⟩
      have hyU : (⟨(g : G) * x * (g : G)⁻¹, hgyU⟩ : ↥(centralizer ({u} : Set G))) = g * xU * g⁻¹ :=
        Subtype.ext (by simp [hxU])
      show κ ⟨(g : G) * x * (g : G)⁻¹, hSU ⟨y, hyS⟩⟩ = z
      rw [show (⟨(g : G) * x * (g : G)⁻¹, hSU ⟨y, hyS⟩⟩ : ↥(centralizer ({u} : Set G))) =
        g * xU * g⁻¹ from hyU, map_mul, map_mul, map_inv, hgκ, ← hĝ]
      rfl
    have hι : Function.Injective (fun y : S => (⟨((y : ↥(centralizer ({r} : Set G)))),
        by
          obtain ⟨y, g, hg, hy⟩ := y
          refine isConj_iff.2 ⟨⟨g, mem_centralizer_singleton_iff.2 hg⟩, Subtype.ext ?_⟩
          show (g : G) * x * (g : G)⁻¹ = (y : G)
          exact hy.symm⟩ :
        {y : ↥(centralizer ({r} : Set G)) // IsConj xC y})) := by
      intro a b hab
      have h := congrArg
        (fun z : {y : ↥(centralizer ({r} : Set G)) // IsConj xC y} => z.1) hab
      exact Subtype.ext h
    have hfin : Finite S := inferInstance
    exact (Nat.card_le_card_of_surjective Φ hΦ).trans (Nat.card_le_card_of_injective _ hι)

theorem inv_mul_mul_mem_centralizer {h c : G} (hc : c ∈ centralizer ({h * u * h⁻¹} : Set G)) :
    h⁻¹ * c * h ∈ centralizer ({u} : Set G) := by
  rw [mem_centralizer_singleton_iff] at hc ⊢
  calc h⁻¹ * c * h * u = h⁻¹ * (c * (h * u * h⁻¹)) * h := by group
    _ = h⁻¹ * ((h * u * h⁻¹) * c) * h := by rw [hc]
    _ = u * (h⁻¹ * c * h) := by group

@[expose] def kappaConj (κ : ↥(centralizer ({u} : Set G)) →* F) (h : G) :
    ↥(centralizer ({h * u * h⁻¹} : Set G)) →* F where
  toFun c := κ ⟨h⁻¹ * (c : G) * h, inv_mul_mul_mem_centralizer c.2⟩
  map_one' := by
    have : (⟨h⁻¹ * ((1 : ↥(centralizer ({h * u * h⁻¹} : Set G))) : G) * h,
        inv_mul_mul_mem_centralizer (1 : ↥(centralizer ({h * u * h⁻¹} : Set G))).2⟩ :
        ↥(centralizer ({u} : Set G))) = 1 := Subtype.ext (by simp)
    rw [this, map_one]
  map_mul' a b := by
    rw [← map_mul]
    congr 1
    refine Subtype.ext ?_
    show h⁻¹ * ((a : G) * (b : G)) * h = h⁻¹ * (a : G) * h * (h⁻¹ * (b : G) * h)
    group

theorem kappaConj_surjective (κ : ↥(centralizer ({u} : Set G)) →* F)
    (hs : Function.Surjective κ) (h : G) : Function.Surjective (kappaConj κ h) := by
  intro v
  obtain ⟨y, rfl⟩ := hs v
  have hy : h * (y : G) * h⁻¹ ∈ centralizer ({h * u * h⁻¹} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.1 y.2
    calc h * (y : G) * h⁻¹ * (h * u * h⁻¹) = h * ((y : G) * u) * h⁻¹ := by group
      _ = h * (u * (y : G)) * h⁻¹ := by rw [this]
      _ = h * u * h⁻¹ * (h * (y : G) * h⁻¹) := by group
  refine ⟨⟨h * (y : G) * h⁻¹, hy⟩, ?_⟩
  show κ ⟨h⁻¹ * (h * (y : G) * h⁻¹) * h, _⟩ = κ y
  congr 1
  refine Subtype.ext ?_
  show h⁻¹ * (h * (y : G) * h⁻¹) * h = (y : G)
  group

theorem kappaConj_eq_one (κ : ↥(centralizer ({u} : Set G)) →* F)
    (hker : ∀ c, κ c = 1 → (c : G) = 1 ∨ (c : G) = u) (h : G) :
    ∀ c, kappaConj κ h c = 1 → (c : G) = 1 ∨ (c : G) = h * u * h⁻¹ := by
  intro c hc
  rcases hker _ hc with e | e
  · left
    have e' : h⁻¹ * (c : G) * h = 1 := e
    calc (c : G) = h * (h⁻¹ * (c : G) * h) * h⁻¹ := by group
      _ = 1 := by rw [e']; group
  · right
    have e' : h⁻¹ * (c : G) * h = u := e
    calc (c : G) = h * (h⁻¹ * (c : G) * h) * h⁻¹ := by group
      _ = h * u * h⁻¹ := by rw [e']

theorem fourClassesLarge_of_perfect_few {K P : Subgroup G} [Finite K] (hPK : P ≤ K)
    (hP : P ≤ ⁅P, P⁆)
    (hC : ∀ (x : G) (hx : x ∈ K), (∀ p ∈ P, p * x = x * p) → x ^ 4 = 1 →
      ¬ 5 ≤ Nat.card {y : ↥K // IsConj (⟨x, hx⟩ : ↥K) y} → x ^ 2 = 1) :
    FourClassesLarge ↥K := by
  intro x hx4 hx2
  by_contra hlt
  have hlt' : Nat.card {y : ↥K // IsConj x y} ≤ 4 := by omega
  have hP' : P.subgroupOf K ≤ ⁅P.subgroupOf K, P.subgroupOf K⁆ := by
    have hmap : (P.subgroupOf K).map K.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPK
    rw [← Subgroup.map_le_map_iff_of_injective K.subtype_injective, Subgroup.map_commutator,
      hmap]
    exact hP
  have hset : conjugatesOf x = {y | IsConj x y} := rfl
  have hn : (conjugatesOf x).ncard ≤ 4 := by
    rw [hset, ← Nat.card_coe_set_eq]
    exact hlt'
  have hle := le_centralizer_of_ncard_conjugatesOf_le_four hP' hn
  refine hx2 (Subtype.ext ?_)
  have := hC x x.2 (fun p hp => by
    have h1 := mem_centralizer_singleton_iff.1
      (hle (show (⟨p, hPK hp⟩ : ↥K) ∈ P.subgroupOf K from hp))
    exact congrArg Subtype.val h1) (by simpa using congrArg Subtype.val hx4) hlt
  simpa using this

theorem fourClassesLarge_centralizer_of_pair [Finite G] {d : G}
    (κ : ↥(centralizer ({d} : Set G)) →* F) (hs : Function.Surjective κ)
    (hker : ∀ c, κ c = 1 → (c : G) = 1 ∨ (c : G) = d)
    (hF : ∀ v : F, orderOf v = 2 → FourClassesLarge ↥(centralizer ({v} : Set F)))
    {h e : G} (he : e = h * d * h⁻¹) {r : G} (hrr : r * r = 1) (hr1 : r ≠ 1) (hrd : r ≠ d)
    (hre : r ≠ e) (hde : d ≠ e) (hrcd : r * d = d * r) (hrce : r * e = e * r)
    (hLd : ∀ g : G, g * r * g⁻¹ ≠ d * r) (hLe : ∀ g : G, g * r * g⁻¹ ≠ e * r)
    {P : Subgroup G} (hPK : P ≤ centralizer ({r} : Set G)) (hP : P ≤ ⁅P, P⁆) (hdP : d ∈ P)
    (heP : e ∈ P) : FourClassesLarge ↥(centralizer ({r} : Set G)) := by
  subst he
  refine fourClassesLarge_of_perfect_few hPK hP fun x hx hxP hx4 hfew => ?_
  have hxr : x * r = r * x := mem_centralizer_singleton_iff.1 hx
  have h1 := sq_mem_of_few_conjugates κ hs hker hF hrr hr1 hrd hrcd hLd hxr (hxP d hdP).symm hx4
    hfew
  have h2 := sq_mem_of_few_conjugates (kappaConj κ h) (kappaConj_surjective κ hs h)
    (kappaConj_eq_one κ hker h) hF hrr hr1 hre hrce hLe hxr (hxP _ heP).symm hx4 hfew
  rcases h1 with h1 | h1
  · exact h1
  · rcases h2 with h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) hde

theorem fourClassesLarge_of_isConj {r v : G} (hc : IsConj r v)
    (hr : FourClassesLarge ↥(centralizer ({r} : Set G))) :
    FourClassesLarge ↥(centralizer ({v} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  have e := (centralizerEquiv (MulAut.conj c) r).trans
    (MulEquiv.subgroupCongr (show centralizer ({(MulAut.conj c) r} : Set G) =
      centralizer ({v} : Set G) by rw [MulAut.conj_apply, hc]))
  exact FourClassesLarge.of_mulEquiv e.symm hr

end CFSG.EvenSporadicStandard.HypOne.Fi23
