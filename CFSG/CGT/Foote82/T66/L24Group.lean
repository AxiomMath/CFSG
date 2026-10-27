module

public import CFSG.CGT.Foote82.Setup
public import CFSG.CGT.Foote82.T66.L24Perm
import CFSG.CGT.Foote82.T66.MC2Perm
import CFSG.CGT.Foote82.ClimbIrr
import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.CGT.Foote82.L24

open CFSG.Open CFSG.Quasithin.G11 Equiv Equiv.Perm

section Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem apply_mem_commSpace {K : Subgroup (GLV V)} {k : GLV V} (hk : k ∈ K) {w : V}
    (hw : w ∈ commSpace K ⊤) : k w ∈ commSpace K ⊤ := by
  have := (commSpace K ⊤).add_mem (sub_mem_commSpace hk (Submodule.mem_top (x := w))) hw
  rwa [sub_add_cancel] at this

theorem apply_of_mem_tildeVBot {K : Subgroup (GLV V)} {k : GLV V} (hk : k ∈ K) {t : V}
    (ht : t ∈ tildeVBot K) : k t = t :=
  ht.1 k hk

theorem add_self_V (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem sub_eq_add_V (u v : V) : u - v = u + v := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (add_self_V v)]

theorem mem_tildeVBot_of_fixed {K : Subgroup (GLV V)} (hperf : ⁅K, K⁆ = K) {w : V}
    (hw : w ∈ commSpace K ⊤) (hfix : ∀ k ∈ K, k w - w ∈ tildeVBot K) : w ∈ tildeVBot K := by
  set U : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {w} ⊔ tildeVBot K with hU
  have hwU : w ∈ U := Submodule.mem_sup_left (Submodule.mem_span_singleton_self w)
  have hUinv : Invariant K U := by
    intro k hk u hu
    obtain ⟨y, hy, t, ht, rfl⟩ := Submodule.mem_sup.1 hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have e : k (c • w + t) = c • w + (c • (k w - w) + t) := by
      rw [map_add, map_smul, apply_of_mem_tildeVBot hk ht, smul_sub]
      abel
    rw [e]
    exact U.add_mem (U.smul_mem c hwU)
      (Submodule.mem_sup_right ((tildeVBot K).add_mem ((tildeVBot K).smul_mem c (hfix k hk)) ht))
  have hcomm : commSpace K U ≤ fixedSpace K := by
    refine commSpace_le_iff.2 fun k hk u hu => ?_
    obtain ⟨y, hy, t, ht, rfl⟩ := Submodule.mem_sup.1 hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have e : k (c • w + t) - (c • w + t) = c • (k w - w) := by
      rw [map_add, map_smul, apply_of_mem_tildeVBot hk ht, smul_sub]
      abel
    rw [e]
    exact (fixedSpace K).smul_mem c (hfix k hk).1
  have htriv := trivial_of_commSpace_le_fixedSpace_of_perfect hperf hUinv hcomm
  exact ⟨fun k hk => htriv k hk w hwU, hw⟩

end Module

section AS

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {G : Subgroup (GLV V)} {N : ℕ}
  (φ : ↥G ≃* alternatingGroup (Fin N))

@[expose] def pm (g : ↥G) : Perm (Fin N) := ((φ g : alternatingGroup (Fin N)) : Perm (Fin N))

theorem pm_mul (g h : ↥G) : pm φ (g * h) = pm φ g * pm φ h := by
  simp [pm]

theorem pm_inv (g : ↥G) : pm φ g⁻¹ = (pm φ g)⁻¹ := by
  simp [pm]

theorem pm_one : pm φ 1 = 1 := by
  simp [pm]

theorem pm_mem_alternatingGroup (g : ↥G) : pm φ g ∈ alternatingGroup (Fin N) :=
  (φ g).2

@[expose] def el (σ : Perm (Fin N)) (hσ : σ ∈ alternatingGroup (Fin N)) : ↥G :=
  φ.symm ⟨σ, hσ⟩

theorem pm_el (σ : Perm (Fin N)) (hσ : σ ∈ alternatingGroup (Fin N)) : pm φ (el φ σ hσ) = σ := by
  simp [pm, el]

@[expose] def AS (S : Finset (Fin N)) : Subgroup (GLV V) :=
  ((altOn (S : Set (Fin N))).comap
    ((alternatingGroup (Fin N)).subtype.comp φ.toMonoidHom)).map G.subtype

theorem mem_AS {S : Finset (Fin N)} {x : GLV V} :
    x ∈ AS φ S ↔ ∃ g : ↥G, pm φ g ∈ altOn (S : Set (Fin N)) ∧ (g : GLV V) = x := by
  simp only [AS, Subgroup.mem_map, Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply,
    Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, pm]

theorem coe_mem_AS {S : Finset (Fin N)} {g : ↥G} :
    (g : GLV V) ∈ AS φ S ↔ pm φ g ∈ altOn (S : Set (Fin N)) := by
  rw [mem_AS]
  constructor
  · rintro ⟨h, hh, he⟩
    rwa [Subtype.ext he] at hh
  · intro h
    exact ⟨g, h, rfl⟩

theorem commutator_altOn {S : Finset (Fin N)} (hS : 5 ≤ S.card) :
    ⁅altOn (S : Set (Fin N)), altOn (S : Set (Fin N))⁆ = altOn (S : Set (Fin N)) := by
  have hrange : (Perm.ofSubtype : Perm ↥S →* Perm (Fin N)).range =
      fixingSubgroup (Perm (Fin N)) ((S : Set (Fin N))ᶜ) := by
    ext g
    rw [Perm.mem_range_ofSubtype_iff, mem_fixingSubgroup_compl_iff_movedBy_subset]
    refine ⟨fun h x hx => h (mem_support.2 hx), fun h x hx => h ?_⟩
    simpa using mem_support.1 hx
  have hmap : (alternatingGroup ↥S).map (Perm.ofSubtype : Perm ↥S →* Perm (Fin N)) =
      altOn (S : Set (Fin N)) := by
    rw [alternatingGroup.map_ofSubtype, hrange, altOn, inf_comm]
  rw [← hmap, ← Subgroup.map_commutator,
    commutator_alternatingGroup_eq_self (by simpa using hS)]

theorem commutator_AS {S : Finset (Fin N)} (hS : 5 ≤ S.card) : ⁅AS φ S, AS φ S⁆ = AS φ S := by
  set f : ↥G →* Perm (Fin N) := (alternatingGroup (Fin N)).subtype.comp φ.toMonoidHom with hf
  set K : Subgroup ↥G := (altOn (S : Set (Fin N))).comap f with hK
  have hfi : Function.Injective f := Subtype.val_injective.comp φ.injective
  have hKmap : K.map f = altOn (S : Set (Fin N)) := by
    refine Subgroup.map_comap_eq_self fun σ hσ => ?_
    refine ⟨φ.symm ⟨σ, (MC2.mem_altOn_iff.1 hσ).1⟩, ?_⟩
    simp [hf]
  have hKK : ⁅K, K⁆ = K := by
    apply Subgroup.map_injective hfi
    rw [Subgroup.map_commutator, hKmap, commutator_altOn hS]
  show ⁅K.map G.subtype, K.map G.subtype⁆ = K.map G.subtype
  rw [← Subgroup.map_commutator, hKK]

structure HeartW (S : Finset (Fin N)) (θ : (Fin N → ZMod 2) →ₗ[ZMod 2] V) : Prop where
  mem : ∀ x ∈ Ew S, θ x ∈ commSpace (AS φ S) ⊤
  span : commSpace (AS φ S) ⊤ ≤ (Ew S).map θ ⊔ tildeVBot (AS φ S)
  ker : ∀ x ∈ Ew S, (θ x ∈ tildeVBot (AS φ S) ↔ x = 0 ∨ x = jS S)
  equiv : ∀ g : ↥G, pm φ g ∈ altOn (S : Set (Fin N)) → ∀ x ∈ Ew S,
    (g : GLV V) (θ x) - θ (pa (pm φ g) x) ∈ tildeVBot (AS φ S)

variable {φ}

theorem heartW_of_pre {S : Finset (Fin N)} (hS : 4 ≤ S.card) (hB : HasIrrTildeV (AS φ S))
    (hperf : ⁅AS φ S, AS φ S⁆ = AS φ S) {θ : (Fin N → ZMod 2) →ₗ[ZMod 2] V}
    (hmem : ∀ y ∈ Ew S, θ y ∈ commSpace (AS φ S) ⊤)
    (hequiv : ∀ g : ↥G, pm φ g ∈ altOn (S : Set (Fin N)) → ∀ y ∈ Ew S,
      (g : GLV V) (θ y) - θ (pa (pm φ g) y) ∈ tildeVBot (AS φ S))
    (hne : ∃ y ∈ Ew S, θ y ∉ tildeVBot (AS φ S)) : HeartW φ S θ := by
  classical
  obtain ⟨y0, hy0E, hy0T⟩ := hne
  have hYinv : Invariant (AS φ S) ((Ew S).map θ ⊔ tildeVBot (AS φ S)) := by
    intro k hk v hv
    obtain ⟨g, hg, rfl⟩ := (mem_AS φ).1 hk
    obtain ⟨_, ⟨y, hy, rfl⟩, t, ht, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, apply_of_mem_tildeVBot hk ht]
    have e : (g : GLV V) (θ y) =
        θ (pa (pm φ g) y) + ((g : GLV V) (θ y) - θ (pa (pm φ g) y)) := by abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.mem_sup_left ⟨_, pa_mem_Ew hg hy, rfl⟩)
      (Submodule.mem_sup_right (hequiv g hg y hy))) (Submodule.mem_sup_right ht)
  have hspan : commSpace (AS φ S) ⊤ ≤ (Ew S).map θ ⊔ tildeVBot (AS φ S) := by
    rcases hB.2 _ hYinv le_sup_right
        (sup_le (by rintro _ ⟨y, hy, rfl⟩; exact hmem y hy) inf_le_right) with h | h
    · exfalso
      have h0 : θ y0 ∈ (Ew S).map θ ⊔ tildeVBot (AS φ S) :=
        Submodule.mem_sup_left ⟨y0, hy0E, rfl⟩
      rw [h] at h0
      exact hy0T h0
    · exact h.ge
  have hj : jS S ∈ Ew S → θ (jS S) ∈ tildeVBot (AS φ S) := by
    intro hjE
    refine mem_tildeVBot_of_fixed hperf (hmem _ hjE) fun k hk => ?_
    obtain ⟨g, hg, rfl⟩ := (mem_AS φ).1 hk
    have := hequiv g hg _ hjE
    rwa [pa_jS hg] at this
  refine ⟨hmem, hspan, fun x hxE => ⟨fun hxT => ?_, ?_⟩, hequiv⟩
  ·
    by_contra hc
    push Not at hc
    have hinv : ∀ σ ∈ altOn (S : Set (Fin N)), ∀ y ∈ Ew S ⊓ (tildeVBot (AS φ S)).comap θ,
        pa σ y ∈ Ew S ⊓ (tildeVBot (AS φ S)).comap θ := by
      intro σ hσ y hy
      refine ⟨pa_mem_Ew hσ hy.1, ?_⟩
      set g := el φ σ (MC2.mem_altOn_iff.1 hσ).1 with hg
      have hgB : (g : GLV V) ∈ AS φ S := by
        rw [coe_mem_AS, hg, pm_el]
        exact hσ
      have hd := hequiv g (by rw [hg, pm_el]; exact hσ) y hy.1
      rw [hg, pm_el] at hd
      have hyT : θ y ∈ tildeVBot (AS φ S) := hy.2
      show θ (pa σ y) ∈ tildeVBot (AS φ S)
      have e : θ (pa σ y) = (g : GLV V) (θ y) - ((g : GLV V) (θ y) - θ (pa σ y)) := by abel
      rw [e]
      refine (tildeVBot (AS φ S)).sub_mem ?_ hd
      rw [apply_of_mem_tildeVBot hgB hyT]
      exact hyT
    have hle := Ew_le_of_invariant hS inf_le_left hinv ⟨hxE, hxT⟩ hc.1 hc.2
    exact hy0T (hle hy0E).2
  · rintro (rfl | rfl)
    · rw [map_zero]
      exact (tildeVBot _).zero_mem
    · exact hj hxE

end AS

end CFSG.CGT.Foote82.L24
