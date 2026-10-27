module

public import CFSG.GH74.GLS.C3.Layer2.L5A1
public import CFSG.GH74.GLS.C3.Prop121.Coord
public import CFSG.GH74.GLS.C3.Prop121.G5Iota

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

structure Coord5 (h : IsAConfig 5 x K T Q S a) where
  ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp 5)
  hι1 : ((ι (xC x) : Fgrp 5) : Amb 5) = x0 5
  hιQ : ∀ c : ↥(centralizer ({x} : Set G)), (((ι c : Fgrp 5) : Amb 5).1 = 1 ↔ (c : G) ∈ Q)
  hιT : ∀ c : ↥(centralizer ({x} : Set G)), (c : G) ∈ T ↔ ((ι c : Fgrp 5) : Amb 5) ∈ T5

theorem exists_coord5
    (hG4 : pRank 2 G ≤ 4) (h : IsAConfig 5 x K T Q S a) : Nonempty (Coord5 h) := by
  obtain ⟨ι₀, hι₀1, hι₀Q⟩ := exists_coord (Or.inl rfl) hG4 h
  obtain ⟨ι, hι1, hιQ, hιT⟩ := exists_equiv_T5 h ι₀ hι₀1 hι₀Q
  exact ⟨⟨ι, hι1, hιQ, hιT⟩⟩

theorem card_K (h : IsAConfig 5 x K T Q S a) : Nat.card K = 60 := by
  obtain ⟨e⟩ := h.K_equiv_alt
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem K_center_trivial (h : IsAConfig 5 x K T Q S a) {y : G} (hyK : y ∈ K) (hy : ∀ k ∈ K, k * y = y * k) : y = 1 := by
  obtain ⟨e⟩ := h.K_equiv_alt
  have hc : e ⟨y, hyK⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hy k k.2)
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
  have : (⟨y, hyK⟩ : ↥K) = 1 := e.injective (by rw [hc, map_one])
  exact congrArg Subtype.val this

namespace Coord5

variable {h : IsAConfig 5 x K T Q S a} (c : Coord5 h)

@[expose] def co (g : ↥(centralizer ({x} : Set G))) : Amb 5 := ((c.ι g : Fgrp 5) : Amb 5)

theorem co_mul (g g' : ↥(centralizer ({x} : Set G))) : c.co (g * g') = c.co g * c.co g' := by
  unfold co
  rw [map_mul]
  rfl

theorem co_one : c.co 1 = 1 := by
  unfold co
  rw [map_one]
  rfl

theorem co_inv (g : ↥(centralizer ({x} : Set G))) : c.co g⁻¹ = (c.co g)⁻¹ := by
  unfold co
  rw [map_inv]
  rfl

theorem co_inj {g g' : ↥(centralizer ({x} : Set G))} (hgg : c.co g = c.co g') : g = g' :=
  c.ι.injective (Subtype.ext hgg)

theorem co_mem (g : ↥(centralizer ({x} : Set G))) : c.co g ∈ Fgrp 5 := (c.ι g).2

theorem co_surj {p : Amb 5} (hp : p ∈ Fgrp 5) : ∃ g, c.co g = p := by
  obtain ⟨g, hg⟩ := c.ι.surjective ⟨p, hp⟩
  exact ⟨g, congrArg Subtype.val hg⟩

theorem co_eq_one_iff {g : ↥(centralizer ({x} : Set G))} : c.co g = 1 ↔ g = 1 := by
  constructor
  · intro hg
    exact c.co_inj (hg.trans c.co_one.symm)
  · rintro rfl
    exact c.co_one

@[expose] def lift (M : Subgroup (Amb 5)) : Subgroup G where
  carrier := {g | ∃ hg : g ∈ centralizer ({x} : Set G), c.co ⟨g, hg⟩ ∈ M}
  one_mem' := ⟨one_mem _, by
    have : c.co (⟨1, one_mem _⟩ : ↥(centralizer ({x} : Set G))) = 1 := c.co_one
    rw [this]
    exact M.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have : c.co (⟨a * b, mul_mem ha hb⟩ : ↥(centralizer ({x} : Set G))) =
        c.co ⟨a, ha⟩ * c.co ⟨b, hb⟩ := c.co_mul ⟨a, ha⟩ ⟨b, hb⟩
    rw [this]
    exact M.mul_mem ha' hb'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have : c.co (⟨a⁻¹, inv_mem ha⟩ : ↥(centralizer ({x} : Set G))) = (c.co ⟨a, ha⟩)⁻¹ :=
      c.co_inv ⟨a, ha⟩
    rw [this]
    exact M.inv_mem ha'

variable {c}

theorem lift_mem_cent {M : Subgroup (Amb 5)} {g : G} (hg : g ∈ c.lift M) :
    g ∈ centralizer ({x} : Set G) := hg.elim fun h _ => h

theorem mem_lift_iff {M : Subgroup (Amb 5)} {g : G} (hg : g ∈ centralizer ({x} : Set G)) :
    g ∈ c.lift M ↔ c.co ⟨g, hg⟩ ∈ M :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨hg, h⟩⟩

theorem lift_mono {M₁ M₂ : Subgroup (Amb 5)} (hM : M₁ ≤ M₂) : c.lift M₁ ≤ c.lift M₂ :=
  fun _ ⟨hg, h⟩ => ⟨hg, hM h⟩

theorem lift_inf {M₁ M₂ : Subgroup (Amb 5)} : c.lift (M₁ ⊓ M₂) = c.lift M₁ ⊓ c.lift M₂ := by
  ext g
  constructor
  · rintro ⟨hg, h1, h2⟩
    exact ⟨⟨hg, h1⟩, ⟨hg, h2⟩⟩
  · rintro ⟨⟨hg, h1⟩, ⟨_, h2⟩⟩
    exact ⟨hg, h1, h2⟩

theorem lift_bot : c.lift (⊥ : Subgroup (Amb 5)) = ⊥ := by
  ext g
  constructor
  · rintro ⟨hg, hmem⟩
    have : c.co ⟨g, hg⟩ = 1 := Subgroup.mem_bot.1 hmem
    have h1 : (⟨g, hg⟩ : ↥(centralizer ({x} : Set G))) = 1 := c.co_eq_one_iff.1 this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
  · intro hg
    rw [Subgroup.mem_bot] at hg
    subst hg
    exact ⟨one_mem _, by
      have : c.co (⟨1, one_mem _⟩ : ↥(centralizer ({x} : Set G))) = 1 := c.co_one
      rw [this]
      exact Subgroup.one_mem _⟩

theorem card_lift {M : Subgroup (Amb 5)} (hM : M ≤ Fgrp 5) :
    Nat.card (c.lift M) = Nat.card M := by
  apply Nat.card_congr
  exact
    { toFun := fun g => ⟨c.co ⟨g.1, lift_mem_cent g.2⟩, (mem_lift_iff (lift_mem_cent g.2)).1 g.2⟩
      invFun := fun p => ⟨((c.ι.symm ⟨p.1, hM p.2⟩ : ↥(centralizer ({x} : Set G))) : G),
        ⟨(c.ι.symm ⟨p.1, hM p.2⟩).2, by
          have : c.co (⟨((c.ι.symm ⟨p.1, hM p.2⟩ : ↥(centralizer ({x} : Set G))) : G),
              (c.ι.symm ⟨p.1, hM p.2⟩).2⟩ : ↥(centralizer ({x} : Set G))) = p.1 := by
            unfold co
            simp
          rw [this]
          exact p.2⟩⟩
      left_inv := fun g => by
        apply Subtype.ext
        simp [co]
      right_inv := fun p => by
        apply Subtype.ext
        simp [co] }

theorem T_eq_lift : T = c.lift T5 := by
  ext g
  constructor
  · intro hg
    exact ⟨h.T_le_C hg, (c.hιT ⟨g, h.T_le_C hg⟩).1 hg⟩
  · rintro ⟨hg, hg'⟩
    exact (c.hιT ⟨g, hg⟩).2 hg'

theorem Q_eq_lift : Q = c.lift Qm := by
  ext g
  constructor
  · intro hg
    have hgC : g ∈ centralizer ({x} : Set G) := h.T_le_C (h.Q_le_T hg)
    have hT5 : c.co ⟨g, hgC⟩ ∈ T5 := (c.hιT ⟨g, hgC⟩).1 (h.Q_le_T hg)
    refine ⟨hgC, ?_⟩
    exact (Qm_coord hT5).1 ((c.hιQ ⟨g, hgC⟩).2 hg)
  · rintro ⟨hgC, hQ⟩
    have hT5 : c.co ⟨g, hgC⟩ ∈ T5 := Qm_le_T5 hQ
    exact (c.hιQ ⟨g, hgC⟩).1 ((Qm_coord hT5).2 hQ)

theorem K_le_lift : K ≤ c.lift Km := by
  let φ : ↥K →* Perm (Fin 4) := (MonoidHom.snd (Perm (Fin 5)) (Perm (Fin 4))).comp
    ((Fgrp 5).subtype.comp (c.ι.toMonoidHom.comp (Subgroup.inclusion h.K_le_C)))
  have hφ : ∀ k : ↥K, φ k = (c.co ⟨(k : G), h.K_le_C k.2⟩).2 := fun k => rfl
  have hV : ∀ k : ↥K, φ k ∈ V4l := by
    intro k
    have hkC : (k : G) ∈ centralizer ({x} : Set G) := h.K_le_C k.2
    have hcomm : ∀ f : Amb 5, f ∈ Qm → c.co ⟨k, hkC⟩ * f = f * c.co ⟨k, hkC⟩ := by
      intro f hf
      have hfF : f ∈ Fgrp 5 := Qm_le_Fgrp hf
      obtain ⟨q, hq⟩ := c.co_surj hfF
      have hqQ : (q : G) ∈ Q := by
        rw [Q_eq_lift (c := c)]
        exact ⟨q.2, by rw [hq]; exact hf⟩
      have hkq : (k : G) * q = q * k := ((h.mem_Q_iff q).1 hqQ).2 k k.2
      have h1 : (⟨k, hkC⟩ : ↥(centralizer ({x} : Set G))) * q = q * ⟨k, hkC⟩ := Subtype.ext hkq
      have h2 := congrArg c.co h1
      rw [c.co_mul, c.co_mul, hq] at h2
      exact h2
    have h1 := congrArg Prod.snd (hcomm f1 f1_mem_Qm)
    have h2 := congrArg Prod.snd (hcomm f2 f2_mem_Qm)
    simp only [Prod.snd_mul, f1_snd, f2_snd] at h1 h2
    rw [hφ]
    exact V4_cent h1 h2
  have : IsSimpleGroup ↥K := by
    obtain ⟨e⟩ := h.K_equiv_alt
    exact e.isSimpleGroup
  have hker : φ.ker = ⊥ ∨ φ.ker = ⊤ := IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker
  have hker1 : φ.ker = ⊤ := by
    rcases hker with hb | ht
    · exfalso
      have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hb
      have hle : Nat.card K ≤ Nat.card {τ : Perm (Fin 4) // τ ∈ V4l} :=
        Nat.card_le_card_of_injective (fun k => ⟨φ k, hV k⟩)
          (fun k k' hkk => hinj (congrArg Subtype.val hkk))
      have h4 : Nat.card {τ : Perm (Fin 4) // τ ∈ V4l} ≤ 4 := by
        classical
        have hset : {τ : Perm (Fin 4) | τ ∈ V4l} = (V4l.toFinset : Set (Perm (Fin 4))) := by
          ext τ
          simp
        calc Nat.card {τ : Perm (Fin 4) // τ ∈ V4l} = Set.ncard {τ : Perm (Fin 4) | τ ∈ V4l} :=
              (Nat.card_coe_set_eq _).symm
          _ = V4l.toFinset.card := by rw [hset, Set.ncard_coe_finset]
          _ ≤ V4l.length := List.toFinset_card_le V4l
          _ = 4 := rfl
      have h60 := card_K h
      omega
    · exact ht
  intro k hk
  have hkC := h.K_le_C hk
  refine ⟨hkC, ?_⟩
  rw [mem_Km]
  have h2 : (c.co ⟨k, hkC⟩).2 = 1 := by
    have : (⟨k, hk⟩ : ↥K) ∈ φ.ker := by rw [hker1]; trivial
    exact this
  refine ⟨h2, ?_⟩
  have hF := c.co_mem ⟨k, hkC⟩
  rw [mem_Fgrp5] at hF
  rw [hF.2, h2]
  simp

theorem K_eq_lift : K = c.lift Km :=
  Subgroup.eq_of_le_of_card_ge K_le_lift (by rw [card_lift Km_le_Fgrp, card_Km, card_K h])

theorem P_eq_lift : T ⊓ K = c.lift Pm := by
  rw [← T5_inf_Km, lift_inf, ← T_eq_lift (c := c), ← K_eq_lift (c := c)]

theorem x_co : c.co (xC x) = f1 := c.hι1

theorem x_mem_lift_Qm
    : x ∈ c.lift Qm := (SetLike.ext_iff.1 (Q_eq_lift (c := c)) x).1 h.x_mem_Q

theorem card_lift_Pm : Nat.card (c.lift Pm) = 4 := by
  rw [card_lift Pm_le_Fgrp, card_Pm]

theorem card_lift_Rm : Nat.card (c.lift Rm) = 16 := by
  rw [card_lift Rm_le_Fgrp, card_Rm]

theorem co_mul_mk {g g' : G} (hg : g ∈ centralizer ({x} : Set G))
    (hg' : g' ∈ centralizer ({x} : Set G)) :
    c.co ⟨g * g', mul_mem hg hg'⟩ = c.co ⟨g, hg⟩ * c.co ⟨g', hg'⟩ := c.co_mul ⟨g, hg⟩ ⟨g', hg'⟩

theorem co_inv_mk {g : G} (hg : g ∈ centralizer ({x} : Set G)) :
    c.co ⟨g⁻¹, inv_mem hg⟩ = (c.co ⟨g, hg⟩)⁻¹ := c.co_inv ⟨g, hg⟩

theorem eq_of_co_eq {g g' : G} (hg : g ∈ centralizer ({x} : Set G))
    (hg' : g' ∈ centralizer ({x} : Set G)) (hco : c.co ⟨g, hg⟩ = c.co ⟨g', hg'⟩) : g = g' :=
  congrArg Subtype.val (c.co_inj hco)

theorem lift_sq {M : Subgroup (Amb 5)} (hM : ∀ p ∈ M, p * p = 1) {g : G} (hg : g ∈ c.lift M) :
    g * g = 1 := by
  obtain ⟨hgC, hmem⟩ := hg
  refine eq_of_co_eq (c := c) (mul_mem hgC hgC) (one_mem _) ?_
  rw [co_mul_mk hgC hgC, hM _ hmem]
  exact c.co_one.symm

theorem lift_comm {M : Subgroup (Amb 5)} (hM : ∀ p ∈ M, ∀ q ∈ M, p * q = q * p) {g g' : G}
    (hg : g ∈ c.lift M) (hg' : g' ∈ c.lift M) : g * g' = g' * g := by
  obtain ⟨hgC, hmem⟩ := hg
  obtain ⟨hgC', hmem'⟩ := hg'
  refine eq_of_co_eq (c := c) (mul_mem hgC hgC') (mul_mem hgC' hgC) ?_
  rw [co_mul_mk hgC hgC', co_mul_mk hgC' hgC, hM _ hmem _ hmem']

theorem Rg_le_T : c.lift Rm ≤ T :=
  (lift_mono Rm_le_T5).trans (T_eq_lift (c := c)).ge

theorem Rg_norm_T
    {t r : G} (ht : t ∈ T) (hr : r ∈ c.lift Rm) : t * r * t⁻¹ ∈ c.lift Rm := by
  obtain ⟨hrC, hrm⟩ := hr
  have htC := h.T_le_C ht
  have ht5 : c.co ⟨t, htC⟩ ∈ T5 := (c.hιT ⟨t, htC⟩).1 ht
  refine ⟨mul_mem (mul_mem htC hrC) (inv_mem htC), ?_⟩
  have : c.co ⟨t * r * t⁻¹, mul_mem (mul_mem htC hrC) (inv_mem htC)⟩ =
      c.co ⟨t, htC⟩ * c.co ⟨r, hrC⟩ * (c.co ⟨t, htC⟩)⁻¹ := by
    rw [← co_inv_mk htC, ← co_mul_mk htC hrC, ← co_mul_mk (mul_mem htC hrC) (inv_mem htC)]
  rw [this]
  exact T5_norm_Rm ht5 hrm

theorem Rg_cent
    {g : G} (hg : ∀ r ∈ c.lift Rm, g * r = r * g) : g ∈ c.lift Rm := by
  have hx : x ∈ c.lift Rm := (lift_mono Qm_le_Rm) x_mem_lift_Qm
  have hgC : g ∈ centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hg x hx
  refine ⟨hgC, centRm (c.co_mem _) ?_⟩
  intro p hp
  obtain ⟨r, hr⟩ := c.co_surj (Rm_le_Fgrp hp)
  have hrR : (r : G) ∈ c.lift Rm := ⟨r.2, by rw [hr]; exact hp⟩
  have h1 := hg r hrR
  have h2 : (⟨g, hgC⟩ : ↥(centralizer ({x} : Set G))) * r = r * ⟨g, hgC⟩ := Subtype.ext h1
  have h3 := congrArg c.co h2
  rw [c.co_mul, c.co_mul, hr] at h3
  exact h3

theorem Rg_inf_centK
    {r : G} (hr : r ∈ c.lift Rm) (hrK : ∀ k ∈ K, r * k = k * r) : r ∈ Q := by
  obtain ⟨hrC, hrm⟩ := hr
  obtain ⟨p, hp, q, hq, hpq⟩ := Rm_prod _ hrm
  obtain ⟨p', hp'⟩ := c.co_surj (Pm_le_Fgrp hp)
  obtain ⟨q', hq'⟩ := c.co_surj (Qm_le_Fgrp hq)
  have h1 : (⟨r, hrC⟩ : ↥(centralizer ({x} : Set G))) = p' * q' := by
    apply c.co_inj
    rw [c.co_mul, hp', hq']
    exact hpq
  have hrpq : r = (p' : G) * (q' : G) := congrArg Subtype.val h1
  have hp'P : (p' : G) ∈ c.lift Pm := ⟨p'.2, by rw [hp']; exact hp⟩
  have hq'Q : (q' : G) ∈ Q := (SetLike.ext_iff.1 (Q_eq_lift (c := c)) (q' : G)).2
    ⟨q'.2, by rw [hq']; exact hq⟩
  have hp'K : (p' : G) ∈ K := ((SetLike.ext_iff.1 (P_eq_lift (c := c)) (p' : G)).2 hp'P).2
  have hqK : ∀ k ∈ K, k * (q' : G) = (q' : G) * k := ((h.mem_Q_iff (q' : G)).1 hq'Q).2
  have hp'c : ∀ k ∈ K, k * (p' : G) = (p' : G) * k := by
    intro k hk
    have h2 : k * (r * (q' : G)⁻¹) = (r * (q' : G)⁻¹) * k := by
      have hq'k : (q' : G)⁻¹ * k = k * (q' : G)⁻¹ := by
        have := hqK k hk
        calc (q' : G)⁻¹ * k = (q' : G)⁻¹ * (k * q') * (q' : G)⁻¹ := by group
          _ = (q' : G)⁻¹ * (q' * k) * (q' : G)⁻¹ := by rw [this]
          _ = k * (q' : G)⁻¹ := by group
      calc k * (r * (q' : G)⁻¹) = (k * r) * (q' : G)⁻¹ := by group
        _ = (r * k) * (q' : G)⁻¹ := by rw [hrK k hk]
        _ = r * (k * (q' : G)⁻¹) := by group
        _ = r * ((q' : G)⁻¹ * k) := by rw [hq'k]
        _ = (r * (q' : G)⁻¹) * k := by group
    have hp'eq : (p' : G) = r * (q' : G)⁻¹ := by rw [hrpq]; group
    rw [hp'eq]
    exact h2
  have hp1 : (p' : G) = 1 := K_center_trivial h hp'K hp'c
  rw [hrpq, hp1, one_mul]
  exact hq'Q

@[expose] noncomputable def wC
    (c : Coord5 h) : ↥(centralizer ({x} : Set G)) :=
  c.ι.symm ⟨wm, Km_le_Fgrp wm_mem_Km⟩

theorem co_wC : c.co c.wC = wm := by
  unfold co wC
  simp

theorem wC_cube : c.wC * c.wC * c.wC = 1 := by
  apply c.co_inj
  rw [c.co_mul, c.co_mul, co_wC, c.co_one]
  exact wm_cube

theorem wG_norm_P
    {p : G} (hp : p ∈ c.lift Pm) : (c.wC : G) * p * (c.wC : G)⁻¹ ∈ c.lift Pm := by
  obtain ⟨hpC, hpm⟩ := hp
  refine ⟨mul_mem (mul_mem c.wC.2 hpC) (inv_mem c.wC.2), ?_⟩
  have : c.co ⟨(c.wC : G) * p * (c.wC : G)⁻¹, mul_mem (mul_mem c.wC.2 hpC) (inv_mem c.wC.2)⟩ =
      wm * c.co ⟨p, hpC⟩ * wm⁻¹ := by
    rw [← co_wC (c := c), ← co_inv_mk c.wC.2, ← co_mul_mk c.wC.2 hpC,
      ← co_mul_mk (mul_mem c.wC.2 hpC) (inv_mem c.wC.2)]
  rw [this]
  exact wm_norm_P _ hpm

theorem wG_cent_Q
    {q : G} (hq : q ∈ c.lift Qm) : (c.wC : G) * q = q * (c.wC : G) := by
  obtain ⟨hqC, hqm⟩ := hq
  refine eq_of_co_eq (c := c) (mul_mem c.wC.2 hqC) (mul_mem hqC c.wC.2) ?_
  rw [co_mul_mk c.wC.2 hqC, co_mul_mk hqC c.wC.2]
  have := wm_comm_Q _ hqm
  rw [co_wC] at *
  exact this

attribute [-instance] CFSG.GorensteinWalter.instDecidableEqPermFinOfNatNat_certificates in
theorem card_T_cent_le
    {t : G} (ht : t ∈ T) (htR : t ∉ c.lift Rm) :
    Nat.card ↥(T ⊓ centralizer ({t} : Set G)) ≤ 8 := by
  have htC := h.T_le_C ht
  have ht5 : c.co ⟨t, htC⟩ ∈ T5 := (c.hιT ⟨t, htC⟩).1 ht
  have ht5R : c.co ⟨t, htC⟩ ∉ Rm := fun hm => htR ⟨htC, hm⟩
  have heq : T ⊓ centralizer ({t} : Set G) =
      c.lift (T5 ⊓ centralizer ({c.co ⟨t, htC⟩} : Set (Amb 5))) := by
    ext g
    constructor
    · rintro ⟨hgT, hgc⟩
      have hgC := h.T_le_C hgT
      refine ⟨hgC, ?_, ?_⟩
      · exact (c.hιT ⟨g, hgC⟩).1 hgT
      · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        have h1 : (⟨g, hgC⟩ : ↥(centralizer ({x} : Set G))) * ⟨t, htC⟩ =
            ⟨t, htC⟩ * ⟨g, hgC⟩ := Subtype.ext (mem_centralizer_singleton_iff.1 hgc)
        have h2 := congrArg c.co h1
        rwa [c.co_mul, c.co_mul] at h2
    · rintro ⟨hgC, hT5, hc⟩
      refine ⟨(c.hιT ⟨g, hgC⟩).2 hT5, ?_⟩
      refine mem_centralizer_singleton_iff.2 ?_
      have h2 := mem_centralizer_singleton_iff.1 hc
      refine eq_of_co_eq (c := c) (mul_mem hgC htC) (mul_mem htC hgC) ?_
      rw [co_mul_mk hgC htC, co_mul_mk htC hgC]
      exact h2
  rw [heq, card_lift (inf_le_left.trans T5_le_Fgrp)]
  have hnd : (allT5.filter (fun s => decide (s * c.co ⟨t, htC⟩ = c.co ⟨t, htC⟩ * s))).Nodup :=
    allT5_facts.2.filter _
  have hlen := natCard_eq_length (T5 ⊓ centralizer ({c.co ⟨t, htC⟩} : Set (Amb 5)))
    (allT5.filter (fun s => decide (s * c.co ⟨t, htC⟩ = c.co ⟨t, htC⟩ * s))) hnd (fun p => by
      simp only [Subgroup.mem_inf, List.mem_filter, mem_allT5, decide_eq_true_eq,
        Subgroup.mem_centralizer_singleton_iff])
  rw [hlen]
  exact T5_cent_le ht5 ht5R

theorem card_T_cent_ge {r : G} (hr : r ∈ c.lift Rm) :
    16 ≤ Nat.card ↥(T ⊓ centralizer ({r} : Set G)) := by
  have hle : c.lift Rm ≤ T ⊓ centralizer ({r} : Set G) := by
    intro g hg
    refine ⟨Rg_le_T hg, ?_⟩
    refine mem_centralizer_singleton_iff.2 ?_
    exact lift_comm (fun a ha b hb => Rm_comm a ha b hb) hg hr
  have := Subgroup.card_le_of_le hle
  rwa [card_lift_Rm] at this

omit [Finite G] in
theorem card_cent_T_conj {g r : G} (hg : g ∈ normalizer (T : Set G)) :
    Nat.card ↥(T ⊓ centralizer ({g * r * g⁻¹} : Set G)) =
      Nat.card ↥(T ⊓ centralizer ({r} : Set G)) := by
  have heq : T ⊓ centralizer ({g * r * g⁻¹} : Set G) =
      (T ⊓ centralizer ({r} : Set G)).map (MulAut.conj g).toMonoidHom := by
    ext z
    constructor
    · rintro ⟨hzT, hzc⟩
      refine ⟨g⁻¹ * z * g, ⟨?_, ?_⟩, ?_⟩
      · have := (mem_normalizer_iff.1 (inv_mem hg) z).1 hzT
        simpa using this
      · have hzc' := mem_centralizer_singleton_iff.1 hzc
        refine mem_centralizer_singleton_iff.2 ?_
        calc g⁻¹ * z * g * r = g⁻¹ * (z * (g * r * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * r * g⁻¹) * z) * g := by rw [hzc']
          _ = r * (g⁻¹ * z * g) := by group
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    · rintro ⟨w, ⟨hwT, hwc⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · exact (mem_normalizer_iff.1 hg w).1 hwT
      · have hwc' := mem_centralizer_singleton_iff.1 hwc
        refine mem_centralizer_singleton_iff.2 ?_
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc g * w * g⁻¹ * (g * r * g⁻¹) = g * (w * r) * g⁻¹ := by group
          _ = g * (r * w) * g⁻¹ := by rw [hwc']
          _ = g * r * g⁻¹ * (g * w * g⁻¹) := by group
  rw [heq]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem R_char
    : ∀ g ∈ normalizer (T : Set G), g ∈ normalizer ((c.lift Rm : Subgroup G) : Set G) := by
  have key : ∀ g ∈ normalizer (T : Set G), ∀ r ∈ c.lift Rm, g * r * g⁻¹ ∈ c.lift Rm := by
    intro g hg r hr
    have hrT := Rg_le_T hr
    have hgT : g * r * g⁻¹ ∈ T := (mem_normalizer_iff.1 hg r).1 hrT
    by_contra hnot
    have hle := card_T_cent_le hgT hnot
    have hge := card_T_cent_ge hr
    have heq := card_cent_T_conj (r := r) hg
    omega
  intro g hg
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact key g hg y
  · intro hy
    have h1 := key g⁻¹ (inv_mem hg) (g * y * g⁻¹) hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rw [e] at h1
    exact h1

open Classical in
@[expose] noncomputable def rco (c : Coord5 h) (g : G) : Amb 5 :=
  if hg : g ∈ centralizer ({x} : Set G) then c.co ⟨g, hg⟩ else 1

theorem rco_of_mem (c : Coord5 h) {g : G} (hg : g ∈ centralizer ({x} : Set G)) :
    c.rco g = c.co ⟨g, hg⟩ := by
  simp [rco, hg]

theorem rco_mul (c : Coord5 h) {g g' : G} (hg : g ∈ centralizer ({x} : Set G))
    (hg' : g' ∈ centralizer ({x} : Set G)) : c.rco (g * g') = c.rco g * c.rco g' := by
  rw [rco_of_mem c (mul_mem hg hg'), rco_of_mem c hg, rco_of_mem c hg']
  exact c.co_mul ⟨g, hg⟩ ⟨g', hg'⟩

theorem rco_inv (c : Coord5 h) {g : G} (hg : g ∈ centralizer ({x} : Set G)) :
    c.rco g⁻¹ = (c.rco g)⁻¹ := by
  rw [rco_of_mem c (inv_mem hg), rco_of_mem c hg]
  exact c.co_inv ⟨g, hg⟩

theorem rco_one (c : Coord5 h) : c.rco 1 = 1 := by
  rw [rco_of_mem c (one_mem _)]
  exact c.co_one

theorem rco_inj (c : Coord5 h) {g g' : G} (hg : g ∈ centralizer ({x} : Set G))
    (hg' : g' ∈ centralizer ({x} : Set G)) (hgg : c.rco g = c.rco g') : g = g' := by
  rw [rco_of_mem c hg, rco_of_mem c hg'] at hgg
  exact congrArg Subtype.val (c.co_inj hgg)

theorem mem_lift_rco (c : Coord5 h) {M : Subgroup (Amb 5)} {g : G} :
    g ∈ c.lift M ↔ g ∈ centralizer ({x} : Set G) ∧ c.rco g ∈ M := by
  constructor
  · rintro ⟨hg, hm⟩
    exact ⟨hg, by rw [rco_of_mem c hg]; exact hm⟩
  · rintro ⟨hg, hm⟩
    exact ⟨hg, by rw [rco_of_mem c hg] at hm; exact hm⟩

theorem rco_mem (c : Coord5 h) {M : Subgroup (Amb 5)} {g : G} (hg : g ∈ c.lift M) :
    c.rco g ∈ M := ((mem_lift_rco c).1 hg).2

theorem rco_conj_w
    (c : Coord5 h) {g : G} (hg : g ∈ centralizer ({x} : Set G)) :
    c.rco ((c.wC : G) * g * (c.wC : G)⁻¹) = wm * c.rco g * wm⁻¹ := by
  have hw : (c.wC : G) ∈ centralizer ({x} : Set G) := c.wC.2
  rw [rco_mul c (mul_mem hw hg) (inv_mem hw), rco_mul c hw hg, rco_inv c hw,
    rco_of_mem c hw]
  have : c.co ⟨(c.wC : G), hw⟩ = wm := co_wC
  rw [this]

end Coord5

end CFSG.GH74.GLS.C3.Layer2.L5
