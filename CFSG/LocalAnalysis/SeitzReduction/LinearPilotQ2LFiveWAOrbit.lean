module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWOne
import CFSG.LocalAnalysis.SeitzReduction.Endgame
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

variable {G : Type*} [Group G] {V : Subgroup G} {t : G}

theorem mem_normalizer_of_forall_commute (htV : ∀ v ∈ V, v * t = t * v) :
    t ∈ normalizer (V : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← htV h hh, mul_inv_cancel_right]
    exact hh
  · intro hh
    have h1 : t⁻¹ * (t * h * t⁻¹) * t = t * h * t⁻¹ := by
      rw [mul_assoc, htV _ hh, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [show t⁻¹ * (t * h * t⁻¹) * t = h by group] at h1
    rw [h1]
    exact hh

theorem mem_sup_zpowers_iff (ht : t * t = 1) (htN : t ∈ normalizer (V : Set G)) {g : G} :
    g ∈ V ⊔ zpowers t ↔ g ∈ V ∨ g * t ∈ V := by
  refine ⟨mem_or_mul_mem_of_mem_sup_zpowers ht htN, ?_⟩
  rintro (h | h)
  · exact mem_sup_left h
  · have he : g = g * t * t⁻¹ := by group
    rw [he]
    exact (V ⊔ zpowers t).mul_mem (mem_sup_left h)
      ((V ⊔ zpowers t).inv_mem (mem_sup_right (mem_zpowers t)))

theorem sup_zpowers_mul_self (hV : ∀ v ∈ V, v * v = 1) (ht : t * t = 1)
    (htV : ∀ v ∈ V, v * t = t * v) {u : G} (hu : u ∈ V ⊔ zpowers t) : u * u = 1 := by
  rcases (mem_sup_zpowers_iff ht (mem_normalizer_of_forall_commute htV)).1 hu with h | h
  · exact hV u h
  · have he : u = u * t * t⁻¹ := by group
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rw [he, ht']
    calc u * t * t * (u * t * t) = (u * t) * (t * (u * t)) * t := by group
      _ = (u * t) * ((u * t) * t) * t := by rw [htV _ h]
      _ = ((u * t) * (u * t)) * (t * t) := by group
      _ = 1 := by rw [hV _ h, ht, one_mul]

theorem sup_zpowers_mul_comm (hV : ∀ v ∈ V, v * v = 1) (ht : t * t = 1)
    (htV : ∀ v ∈ V, v * t = t * v) {u u' : G} (hu : u ∈ V ⊔ zpowers t)
    (hu' : u' ∈ V ⊔ zpowers t) : u * u' = u' * u :=
  mul_comm_of_forall_mul_self_eq_one (W := V ⊔ zpowers t)
    (fun _ hw => sup_zpowers_mul_self hV ht htV hw) hu hu'

theorem mul_mem_iff_of_mem_sup_zpowers (ht : t * t = 1) (htV : ∀ v ∈ V, v * t = t * v)
    {u u' : G} (hu : u ∈ V ⊔ zpowers t) (hu' : u' ∈ V ⊔ zpowers t) :
    u * u' ∈ V ↔ (u ∈ V ↔ u' ∈ V) := by
  have htN := mem_normalizer_of_forall_commute htV
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  by_cases h1 : u ∈ V
  · rw [iff_true_left h1]
    exact ⟨fun h => by simpa using V.mul_mem (V.inv_mem h1) h, fun h => V.mul_mem h1 h⟩
  · rw [iff_false_left h1]
    have h1t : u * t ∈ V := ((mem_sup_zpowers_iff ht htN).1 hu).resolve_left h1
    constructor
    · intro h h2
      exact h1 (by simpa using V.mul_mem h (V.inv_mem h2))
    · intro h2
      have h2t : u' * t ∈ V := ((mem_sup_zpowers_iff ht htN).1 hu').resolve_left h2
      have h2t' : t * u' ∈ V := by
        have := (mem_normalizer_iff.1 htN (u' * t)).1 h2t
        rwa [ht', show t * (u' * t) * t = t * u' * (t * t) by group, ht, mul_one] at this
      have he : u * u' = (u * t) * (t * u') := by
        rw [show (u * t) * (t * u') = u * (t * t) * u' by group, ht, mul_one]
      rw [he]
      exact V.mul_mem h1t h2t'

theorem card_sup_zpowers_eq [Finite G] (ht : t * t = 1) (htN : t ∈ normalizer (V : Set G))
    (htV : t ∉ V) : Nat.card (V ⊔ zpowers t : Subgroup G) = 2 * Nat.card V := by
  have hle : V ≤ V ⊔ zpowers t := le_sup_left
  have hidx : (V.subgroupOf (V ⊔ zpowers t)).index = 2 := by
    rw [index_eq_two_iff]
    refine ⟨⟨t, mem_sup_right (mem_zpowers t)⟩, fun b => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf, coe_mul]
    rcases mem_or_mul_mem_of_mem_sup_zpowers ht htN b.2 with h | h
    · refine Or.inr ⟨h, fun hbt => htV ?_⟩
      simpa using V.mul_mem (V.inv_mem h) hbt
    · refine Or.inl ⟨h, fun hb => htV ?_⟩
      simpa using V.mul_mem (V.inv_mem hb) h
  have h := card_mul_index (V.subgroupOf (V ⊔ zpowers t))
  rw [hidx, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at h
  rw [← h, mul_comm]

theorem normalizer_sup_zpowers_le_normalizer (ht : t * t = 1) (htV : ∀ v ∈ V, v * t = t * v)
    (hconj : ∀ v ∈ V, ∃ g : G, g⁻¹ * t * g = t * v)
    (hnot : ∀ g : G, ∀ v ∈ V, g⁻¹ * t * g ≠ v) :
    normalizer ((V ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (V : Set G) := by
  have htN := mem_normalizer_of_forall_commute htV
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have key : ∀ g ∈ normalizer ((V ⊔ zpowers t : Subgroup G) : Set G), ∀ v ∈ V,
      g * v * g⁻¹ ∈ V := by
    intro g hg v hv
    have hU : g * v * g⁻¹ ∈ V ⊔ zpowers t := (mem_normalizer_iff.1 hg v).1 (mem_sup_left hv)
    rcases (mem_sup_zpowers_iff ht htN).1 hU with h | h
    · exact h
    · exfalso
      set w := g * v * g⁻¹ * t with hw
      have hgv : g * v * g⁻¹ = t * w := by
        rw [← htV w h, hw]
        simp only [mul_assoc, ht, mul_one]
      obtain ⟨k, hk⟩ := hconj w h
      exact hnot (k * g) v hv (calc (k * g)⁻¹ * t * (k * g) = g⁻¹ * (k⁻¹ * t * k) * g := by group
        _ = g⁻¹ * (g * v * g⁻¹) * g := by rw [hk, hgv]
        _ = v := by group)
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

@[expose] def seitzRadX (V : Subgroup G) (t : G) : Subgroup G :=
  centralizer (V : Set G) ⊓ normalizer ((V ⊔ zpowers t : Subgroup G) : Set G)

theorem mem_seitzRadX {x : G} :
    x ∈ seitzRadX V t ↔ x ∈ centralizer (V : Set G) ∧
      x ∈ normalizer ((V ⊔ zpowers t : Subgroup G) : Set G) :=
  Subgroup.mem_inf

theorem conj_eq_of_mem_centralizer {x : G} (hx : x ∈ centralizer (V : Set G)) {v : G}
    (hv : v ∈ V) : x * v * x⁻¹ = v := by
  rw [← mem_centralizer_iff.1 hx v hv, mul_inv_cancel_right]

theorem tcomm_mem_of_mem_seitzRadX (ht : t * t = 1) (htV : ∀ v ∈ V, v * t = t * v)
    (htnV : t ∉ V) {x : G} (hx : x ∈ seitzRadX V t) : t * x * t⁻¹ * x⁻¹ ∈ V := by
  obtain ⟨hxC, hxN⟩ := mem_seitzRadX.1 hx
  have htN := mem_normalizer_of_forall_commute htV
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hU : x * t * x⁻¹ ∈ V ⊔ zpowers t :=
    (mem_normalizer_iff.1 hxN t).1 (mem_sup_right (mem_zpowers t))
  rcases (mem_sup_zpowers_iff ht htN).1 hU with h | h
  · exfalso
    apply htnV
    have h1 := conj_eq_of_mem_centralizer (inv_mem hxC) h
    rw [show x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ = t by group] at h1
    rw [h1]
    exact h
  · have e : t * x * t⁻¹ * x⁻¹ = (x * t * x⁻¹ * t)⁻¹ := by
      rw [show (x * t * x⁻¹ * t)⁻¹ = t⁻¹ * x * t⁻¹ * x⁻¹ by group, ht']
    rw [e]
    exact V.inv_mem h

theorem conj_eq_mul_tcomm (ht : t * t = 1) (x : G) :
    x * t * x⁻¹ = t * (t * x * t⁻¹ * x⁻¹) := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [show t * (t * x * t⁻¹ * x⁻¹) = (t * t) * x * t⁻¹ * x⁻¹ by group, ht, one_mul, ht']

theorem tcomm_mul_of_mem_seitzRadX (ht : t * t = 1) (htV : ∀ v ∈ V, v * t = t * v)
    (htnV : t ∉ V) {x y : G} (hx : x ∈ seitzRadX V t) (hy : y ∈ seitzRadX V t) :
    t * (x * y) * t⁻¹ * (x * y)⁻¹ = (t * x * t⁻¹ * x⁻¹) * (t * y * t⁻¹ * y⁻¹) := by
  have h := conj_eq_of_mem_centralizer (mem_seitzRadX.1 hx).1
    (tcomm_mem_of_mem_seitzRadX ht htV htnV hy)
  calc t * (x * y) * t⁻¹ * (x * y)⁻¹ =
      (t * x * t⁻¹ * x⁻¹) * (x * (t * y * t⁻¹ * y⁻¹) * x⁻¹) := by group
    _ = (t * x * t⁻¹ * x⁻¹) * (t * y * t⁻¹ * y⁻¹) := by rw [h]

@[expose] def seitzTcommHom (ht : t * t = 1) (htV : ∀ v ∈ V, v * t = t * v) (htnV : t ∉ V) :
    seitzRadX V t →* V where
  toFun x := ⟨t * x * t⁻¹ * (x : G)⁻¹, tcomm_mem_of_mem_seitzRadX ht htV htnV x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    exact tcomm_mul_of_mem_seitzRadX ht htV htnV x.2 y.2

theorem coe_seitzTcommHom_apply (ht : t * t = 1) (htV : ∀ v ∈ V, v * t = t * v) (htnV : t ∉ V)
    (x : seitzRadX V t) :
    ((seitzTcommHom ht htV htnV x : V) : G) = t * x * t⁻¹ * (x : G)⁻¹ :=
  rfl

theorem mem_normalizer_sup_zpowers (ht : t * t = 1) (htV : ∀ v ∈ V, v * t = t * v) {l : G}
    (hlV : l ∈ normalizer (V : Set G)) (hlt : l * t = t * l) :
    l ∈ normalizer ((V ⊔ zpowers t : Subgroup G) : Set G) := by
  have htN := mem_normalizer_of_forall_commute htV
  rw [mem_normalizer_iff]
  intro h
  have hlt' : l⁻¹ * t = t * l⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hlt, mul_assoc, mul_inv_cancel, mul_one]
  have e : l * h * l⁻¹ * t = l * (h * t) * l⁻¹ := by
    calc l * h * l⁻¹ * t = l * h * (l⁻¹ * t) := by group
      _ = l * h * (t * l⁻¹) := by rw [hlt']
      _ = l * (h * t) * l⁻¹ := by group
  rw [mem_sup_zpowers_iff ht htN, mem_sup_zpowers_iff ht htN, e, ← mem_normalizer_iff.1 hlV h,
    ← mem_normalizer_iff.1 hlV (h * t)]

theorem conj_mem_centralizer_of_mem_normalizer {l y : G} (hl : l ∈ normalizer (V : Set G))
    (hy : y ∈ centralizer (V : Set G)) : l * y * l⁻¹ ∈ centralizer (V : Set G) := by
  rw [mem_centralizer_iff]
  intro h hh
  have hk : l⁻¹ * h * l ∈ V := by
    have := (mem_normalizer_iff.1 (inv_mem hl) h).1 hh
    rwa [inv_inv] at this
  have hyk : (l⁻¹ * h * l) * y = y * (l⁻¹ * h * l) := mem_centralizer_iff.1 hy _ hk
  have e1 : h * (l * y * l⁻¹) = l * ((l⁻¹ * h * l) * y) * l⁻¹ := by group
  have e2 : (l * y * l⁻¹) * h = l * (y * (l⁻¹ * h * l)) * l⁻¹ := by group
  rw [e1, e2, hyk]

theorem exists_conj_eq_mul_of_mem_normalizer (ht : t * t = 1) (htV : ∀ v ∈ V, v * t = t * v)
    (hnot : ∀ g : G, ∀ v ∈ V, g⁻¹ * t * g ≠ v) {g : G}
    (hg : g ∈ normalizer ((V ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ v ∈ V, g * t * g⁻¹ = t * v := by
  have htN := mem_normalizer_of_forall_commute htV
  have hU : g * t * g⁻¹ ∈ V ⊔ zpowers t :=
    (mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t))
  rcases (mem_sup_zpowers_iff ht htN).1 hU with h | h
  · exact (hnot g⁻¹ _ h (by group)).elim
  · refine ⟨g * t * g⁻¹ * t, h, ?_⟩
    rw [← htV _ h]
    simp only [mul_assoc, ht, mul_one]

theorem exists_mem_seitzRadX_tcomm_eq (ht : t * t = 1) (htV : ∀ v ∈ V, v * t = t * v)
    (hconj : ∀ v ∈ V, ∃ g : G, g⁻¹ * t * g = t * v)
    (hnot : ∀ g : G, ∀ v ∈ V, g⁻¹ * t * g ≠ v)
    {L₁ : Subgroup G} (hL₁t : L₁ ≤ centralizer ({t} : Set G))
    (hL₁V : L₁ ≤ normalizer (V : Set G))
    (htrans : ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → w ≠ 1 → ∃ l ∈ L₁, l * v * l⁻¹ = w)
    (haut : ∀ g ∈ normalizer (V : Set G), ∃ l ∈ L₁, ∀ v ∈ V, g * v * g⁻¹ = l * v * l⁻¹)
    (hmove : ∃ g ∈ normalizer ((V ⊔ zpowers t : Subgroup G) : Set G), g * t * g⁻¹ ≠ t) :
    ∀ v ∈ V, ∃ x ∈ seitzRadX V t, t * x * t⁻¹ * x⁻¹ = v := by
  have hlt : ∀ l ∈ L₁, l * t = t * l := fun l hl => mem_centralizer_singleton_iff.1 (hL₁t hl)
  have hlU : ∀ l ∈ L₁, l ∈ normalizer ((V ⊔ zpowers t : Subgroup G) : Set G) := fun l hl =>
    mem_normalizer_sup_zpowers ht htV (hL₁V hl) (hlt l hl)
  obtain ⟨g, hgN, hgt⟩ := hmove
  obtain ⟨v₀, hv₀, hgv₀⟩ := exists_conj_eq_mul_of_mem_normalizer ht htV hnot hgN
  have hv₀1 : v₀ ≠ 1 := by
    rintro rfl
    exact hgt (by rw [hgv₀, mul_one])
  have hgV : g ∈ normalizer (V : Set G) := normalizer_sup_zpowers_le_normalizer ht htV hconj hnot hgN
  obtain ⟨l, hl, hlg⟩ := haut g hgV
  have hx₀C : l⁻¹ * g ∈ centralizer (V : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    have e := hlg h hh
    calc h * (l⁻¹ * g) = l⁻¹ * (l * h * l⁻¹) * g := by group
      _ = l⁻¹ * (g * h * g⁻¹) * g := by rw [e]
      _ = l⁻¹ * g * h := by group
  have hx₀X : l⁻¹ * g ∈ seitzRadX V t :=
    mem_seitzRadX.2 ⟨hx₀C, mul_mem (inv_mem (hlU l hl)) hgN⟩
  set v₁ := l⁻¹ * v₀ * l⁻¹⁻¹ with hv₁
  have hv₁V : v₁ ∈ V := (mem_normalizer_iff.1 (inv_mem (hL₁V hl)) v₀).1 hv₀
  have hv₁1 : v₁ ≠ 1 := by
    intro h1
    apply hv₀1
    have : v₀ = l * v₁ * l⁻¹ := by rw [hv₁]; group
    rw [this, h1]
    group
  have hx₀t : t * (l⁻¹ * g) * t⁻¹ * (l⁻¹ * g)⁻¹ = v₁ := by
    have hl' : l⁻¹ * t = t * l⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hlt l hl, mul_assoc, mul_inv_cancel, mul_one]
    have h1 : (l⁻¹ * g) * t * (l⁻¹ * g)⁻¹ = t * v₁ := by
      calc (l⁻¹ * g) * t * (l⁻¹ * g)⁻¹ = l⁻¹ * (g * t * g⁻¹) * l := by group
        _ = (l⁻¹ * t) * v₀ * l := by rw [hgv₀]; group
        _ = t * v₁ := by rw [hl', hv₁]; group
    have h2 := conj_eq_mul_tcomm ht (l⁻¹ * g)
    rw [h1] at h2
    exact (mul_left_cancel h2).symm
  intro v hv
  by_cases hv1 : v = 1
  · exact ⟨1, one_mem _, by rw [hv1]; group⟩
  obtain ⟨l', hl', hl'v⟩ := htrans v₁ hv₁V v hv hv₁1 hv1
  refine ⟨l' * (l⁻¹ * g) * l'⁻¹, mem_seitzRadX.2 ⟨conj_mem_centralizer_of_mem_normalizer
    (hL₁V hl') hx₀C, mul_mem (mul_mem (hlU l' hl') (mem_seitzRadX.1 hx₀X).2)
      (inv_mem (hlU l' hl'))⟩, ?_⟩
  rw [tcomm_conj_of_commute (hlt l' hl'), hx₀t, hl'v]

theorem seitzRadX_inf_centralizer_eq (hV : ∀ v ∈ V, v * v = 1) (ht : t * t = 1)
    (htV : ∀ v ∈ V, v * t = t * v)
    (hker : centralizer (V : Set G) ⊓ centralizer ({t} : Set G) ≤ V ⊔ zpowers t) :
    seitzRadX V t ⊓ centralizer ({t} : Set G) = V ⊔ zpowers t := by
  apply le_antisymm
  · rintro x ⟨hxX, hxt⟩
    exact hker ⟨(mem_seitzRadX.1 hxX).1, hxt⟩
  · intro u hu
    refine Subgroup.mem_inf.2 ⟨mem_seitzRadX.2 ⟨mem_centralizer_iff.2 fun v hv => ?_, ?_⟩,
      mem_centralizer_singleton_iff.2 ?_⟩
    · exact sup_zpowers_mul_comm hV ht htV (mem_sup_left hv) hu
    · rw [mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        exact mul_mem (mul_mem hu hh) (inv_mem hu)
      · intro hh
        have := mul_mem (mul_mem (inv_mem hu) hh) hu
        rwa [show u⁻¹ * (u * h * u⁻¹) * u = h by group] at this
    · exact sup_zpowers_mul_comm hV ht htV hu (mem_sup_right (mem_zpowers t))

theorem card_seitzRadX [Finite G] (hV : ∀ v ∈ V, v * v = 1) (ht : t * t = 1)
    (htV : ∀ v ∈ V, v * t = t * v) (htnV : t ∉ V)
    (hker : centralizer (V : Set G) ⊓ centralizer ({t} : Set G) ≤ V ⊔ zpowers t)
    (hsurj : ∀ v ∈ V, ∃ x ∈ seitzRadX V t, t * x * t⁻¹ * x⁻¹ = v) :
    Nat.card (seitzRadX V t) = Nat.card V * Nat.card (V ⊔ zpowers t : Subgroup G) := by
  set φ := seitzTcommHom ht htV htnV with hφ
  have hsurjφ : Function.Surjective φ := by
    rintro ⟨v, hv⟩
    obtain ⟨x, hx, hxv⟩ := hsurj v hv
    exact ⟨⟨x, hx⟩, Subtype.ext hxv⟩
  have hUX : V ⊔ zpowers t ≤ seitzRadX V t := by
    rw [← seitzRadX_inf_centralizer_eq hV ht htV hker]
    exact inf_le_left
  have hkerφ : φ.ker = (V ⊔ zpowers t).subgroupOf (seitzRadX V t) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← seitzRadX_inf_centralizer_eq hV ht htV hker,
      Subgroup.mem_inf, ← tcomm_eq_one_iff, Subtype.ext_iff, coe_seitzTcommHom_apply]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurjφ).toEquiv, hkerφ,
    Nat.card_congr (subgroupOfEquivOfLe hUX).toEquiv]

theorem exists_mem_not_mem_finset [Finite G] {S : Finset G} (hS : S.card < Nat.card V) :
    ∃ v ∈ V, v ∉ S := by
  by_contra h
  have hsub : (V : Set G) ⊆ (S : Set G) := fun v hv => by
    by_contra hvS
    exact h ⟨v, hv, hvS⟩
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet S)
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at h1
  exact absurd (lt_of_lt_of_le hS h1) (lt_irrefl _)

theorem exists_three_of_four_lt [Finite G] (hcard : 4 < Nat.card V) :
    ∃ v₁ ∈ V, ∃ v₂ ∈ V, ∃ v₃ ∈ V, v₁ ≠ 1 ∧ v₂ ≠ 1 ∧ v₂ ≠ v₁ ∧ v₃ ≠ 1 ∧ v₃ ≠ v₁ ∧
      v₃ ≠ v₂ ∧ v₃ ≠ v₁ * v₂ := by
  classical
  obtain ⟨v₁, hv₁, hv₁S⟩ := exists_mem_not_mem_finset (V := V) (S := {1})
    (lt_of_le_of_lt (Finset.card_le_one.2 (by simp)) (by omega))
  obtain ⟨v₂, hv₂, hv₂S⟩ := exists_mem_not_mem_finset (V := V) (S := {1, v₁})
    (lt_of_le_of_lt (Finset.card_le_two) (by omega))
  obtain ⟨v₃, hv₃, hv₃S⟩ := exists_mem_not_mem_finset (V := V) (S := {1, v₁, v₂, v₁ * v₂})
    (lt_of_le_of_lt (Finset.card_le_four) (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv₁S hv₂S hv₃S
  exact ⟨v₁, hv₁, v₂, hv₂, v₃, hv₃, hv₁S, hv₂S.1, hv₂S.2, hv₃S.1, hv₃S.2.1, hv₃S.2.2.1,
    hv₃S.2.2.2⟩

theorem tcomm_inv_of_mem_seitzRadX (ht : t * t = 1) (htV : ∀ v ∈ V, v * t = t * v)
    (htnV : t ∉ V) {x : G} (hx : x ∈ seitzRadX V t) :
    t * x⁻¹ * t⁻¹ * x⁻¹⁻¹ = (t * x * t⁻¹ * x⁻¹)⁻¹ := by
  have h := tcomm_mul_of_mem_seitzRadX ht htV htnV hx (inv_mem hx)
  rw [mul_inv_cancel, show t * 1 * t⁻¹ * (1 : G)⁻¹ = 1 by group] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem mul_self_mem_and_commutator_mem_of_mem_seitzRadX [Finite G] (hV : ∀ v ∈ V, v * v = 1)
    (ht : t * t = 1) (htV : ∀ v ∈ V, v * t = t * v) (htnV : t ∉ V)
    (hker : centralizer (V : Set G) ⊓ centralizer ({t} : Set G) ≤ V ⊔ zpowers t)
    (hsurj : ∀ v ∈ V, ∃ x ∈ seitzRadX V t, t * x * t⁻¹ * x⁻¹ = v)
    {L₁ : Subgroup G} (hL₁t : L₁ ≤ centralizer ({t} : Set G))
    (hL₁V : L₁ ≤ normalizer (V : Set G))
    (htrans : ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → w ≠ 1 → ∃ l ∈ L₁, l * v * l⁻¹ = w)
    (hcard : 4 < Nat.card V) :
    (∀ x ∈ seitzRadX V t, x * x ∈ V) ∧
      ∀ x ∈ seitzRadX V t, ∀ y ∈ seitzRadX V t, x * y * x⁻¹ * y⁻¹ ∈ V := by
  set X := seitzRadX V t with hXdef
  set U := V ⊔ zpowers t with hUdef
  have hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hV hv hw
  have hXU : X ⊓ centralizer ({t} : Set G) = U := seitzRadX_inf_centralizer_eq hV ht htV hker
  have hUX : U ≤ X := by rw [← hXU]; exact inf_le_left
  have hVU : V ≤ U := le_sup_left
  have hkerU : ∀ z ∈ X, t * z * t⁻¹ * z⁻¹ = 1 → z ∈ U := fun z hz h => by
    rw [← hXU]
    exact Subgroup.mem_inf.2 ⟨hz, tcomm_eq_one_iff.1 h⟩
  have hψ := fun {x : G} (hx : x ∈ X) => tcomm_mem_of_mem_seitzRadX ht htV htnV hx
  have hψmul := fun {x y : G} (hx : x ∈ X) (hy : y ∈ X) =>
    tcomm_mul_of_mem_seitzRadX ht htV htnV hx hy
  have hψinv := fun {x : G} (hx : x ∈ X) => tcomm_inv_of_mem_seitzRadX ht htV htnV hx
  have hmulU := fun {u u' : G} (hu : u ∈ U) (hu' : u' ∈ U) =>
    mul_mem_iff_of_mem_sup_zpowers ht htV hu hu'
  have hUc := fun {u u' : G} (hu : u ∈ U) (hu' : u' ∈ U) => sup_zpowers_mul_comm hV ht htV hu hu'
  have H1 : ∀ x ∈ X, ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ V := by
    intro x hx u hu
    have hxU : x * u * x⁻¹ ∈ U := (mem_normalizer_iff.1 (mem_seitzRadX.1 hx).2 u).1 hu
    rw [hmulU hxU (inv_mem hu), inv_mem_iff]
    constructor
    · intro h
      have := conj_eq_of_mem_centralizer (inv_mem (mem_seitzRadX.1 hx).1) h
      rw [show x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u by group] at this
      rw [this]
      exact h
    · intro h
      rw [conj_eq_of_mem_centralizer (mem_seitzRadX.1 hx).1 h]
      exact h
  have H2 : ∀ x ∈ X, x * x ∈ U := fun x hx => hkerU _ (mul_mem hx hx) (by
    rw [hψmul hx hx, hV _ (hψ hx)])
  have H3 : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ U := fun x hx y hy => by
    refine hkerU _ (mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)) ?_
    rw [hψmul (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy),
      hψmul (mul_mem hx hy) (inv_mem hx), hψmul hx hy, hψinv hx, hψinv hy,
      hVc _ (hψ hx) _ (hψ hy)]
    group
  have H4 : ∀ x ∈ X, ∀ u ∈ U, (x * u) * (x * u) ∈ V ↔ x * x ∈ V := by
    intro x hx u hu
    have e : (x * u) * (x * u) = (x * u * x⁻¹ * u⁻¹) * (u * (x * x) * u) := by group
    have e2 : u * (x * x) * u = x * x := by
      rw [hUc hu (H2 x hx), mul_assoc, sup_zpowers_mul_self hV ht htV hu, mul_one]
    rw [e, e2]
    exact mul_mem_cancel_left (H1 x hx u hu)
  have H5 : ∀ x ∈ X, ∀ y ∈ X, t * x * t⁻¹ * x⁻¹ = t * y * t⁻¹ * y⁻¹ →
      (x * x ∈ V ↔ y * y ∈ V) := by
    intro x hx y hy hxy
    have hu : x⁻¹ * y ∈ U := hkerU _ (mul_mem (inv_mem hx) hy) (by
      rw [hψmul (inv_mem hx) hy, hψinv hx, hxy, inv_mul_cancel])
    have := H4 x hx _ hu
    rw [show x * (x⁻¹ * y) = y by group] at this
    exact this.symm
  have hlX : ∀ l ∈ L₁, ∀ x ∈ X, l * x * l⁻¹ ∈ X := fun l hl x hx =>
    mem_seitzRadX.2 ⟨conj_mem_centralizer_of_mem_normalizer (hL₁V hl) (mem_seitzRadX.1 hx).1,
      mul_mem (mul_mem (mem_normalizer_sup_zpowers ht htV (hL₁V hl)
        (mem_centralizer_singleton_iff.1 (hL₁t hl))) (mem_seitzRadX.1 hx).2)
        (inv_mem (mem_normalizer_sup_zpowers ht htV (hL₁V hl)
          (mem_centralizer_singleton_iff.1 (hL₁t hl))))⟩
  have H6 : ∀ l ∈ L₁, ∀ x ∈ X, (l * x * l⁻¹) * (l * x * l⁻¹) ∈ V ↔ x * x ∈ V := by
    intro l hl x hx
    rw [show (l * x * l⁻¹) * (l * x * l⁻¹) = l * (x * x) * l⁻¹ by group]
    exact (mem_normalizer_iff.1 (hL₁V hl) _).symm
  have H7 : ∀ x₀ ∈ X, x₀ * x₀ ∉ V → ∀ x ∈ X, t * x * t⁻¹ * x⁻¹ ≠ 1 → x * x ∉ V := by
    intro x₀ hx₀ h₀ x hx hx1
    have hx₀1 : t * x₀ * t⁻¹ * x₀⁻¹ ≠ 1 := by
      intro h
      exact h₀ (by rw [sup_zpowers_mul_self hV ht htV (hkerU _ hx₀ h)]; exact one_mem _)
    obtain ⟨l, hl, hle⟩ := htrans _ (hψ hx₀) _ (hψ hx) hx₀1 hx1
    have h1 : t * (l * x₀ * l⁻¹) * t⁻¹ * (l * x₀ * l⁻¹)⁻¹ = t * x * t⁻¹ * x⁻¹ := by
      rw [tcomm_conj_of_commute (mem_centralizer_singleton_iff.1 (hL₁t hl)), hle]
    rw [← H5 _ (hlX l hl x₀ hx₀) _ hx h1, H6 l hl x₀ hx₀]
    exact h₀
  have H8 : ∀ x ∈ X, ∀ y ∈ X, ((x * y) * (x * y) ∈ V ↔
      (y * x * y⁻¹ * x⁻¹ ∈ V ↔ (x * x ∈ V ↔ y * y ∈ V))) := by
    intro x hx y hy
    have hc := H3 y hy x hx
    have e : (x * y) * (x * y) = (x * (y * x * y⁻¹ * x⁻¹) * x⁻¹ * (y * x * y⁻¹ * x⁻¹)⁻¹) *
        ((y * x * y⁻¹ * x⁻¹) * ((x * x) * (y * y))) := by group
    have hk := H1 x hx _ hc
    rw [e, mul_mem_cancel_left hk, hmulU hc (mul_mem (H2 x hx) (H2 y hy)),
      hmulU (H2 x hx) (H2 y hy)]
  have H9 : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, (x * (y * z) * x⁻¹ * (y * z)⁻¹ ∈ V ↔
      (x * y * x⁻¹ * y⁻¹ ∈ V ↔ x * z * x⁻¹ * z⁻¹ ∈ V)) := by
    intro x hx y hy z hz
    have hc := H3 x hx z hz
    have hk := H1 y hy _ hc
    have hxy := H3 x hx y hy
    have e : x * (y * z) * x⁻¹ * (y * z)⁻¹ = (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹ *
        (x * z * x⁻¹ * z⁻¹)⁻¹) * ((x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹)) := by
      calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = (x * y * x⁻¹ * y⁻¹) * ((y * (x * z * x⁻¹ * z⁻¹) * y⁻¹ *
            (x * z * x⁻¹ * z⁻¹)⁻¹) * (x * z * x⁻¹ * z⁻¹)) := by group
        _ = ((x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹ * (x * z * x⁻¹ * z⁻¹)⁻¹)) *
            (x * z * x⁻¹ * z⁻¹) := by group
        _ = ((y * (x * z * x⁻¹ * z⁻¹) * y⁻¹ * (x * z * x⁻¹ * z⁻¹)⁻¹) * (x * y * x⁻¹ * y⁻¹)) *
            (x * z * x⁻¹ * z⁻¹) := by rw [hUc hxy (hVU hk)]
        _ = _ := by group
    rw [e, mul_mem_cancel_left hk, hmulU hxy hc]
  have hne : ∀ a ∈ V, ∀ b ∈ V, a ≠ b → a * b ≠ 1 := fun a _ b hb hab h => hab (by
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right (hV b hb)])
  have hindep : ∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V, c ≠ a * b → b * c ≠ a := by
    intro a ha b hb c _ hc hbc
    apply hc
    calc c = (b * b) * c := by rw [hV b hb, one_mul]
      _ = b * (b * c) := by group
      _ = b * a := by rw [hbc]
      _ = a * b := hVc b hb a ha
  have hsq : ∀ x ∈ X, x * x ∈ V := by
    by_contra hcon
    obtain ⟨x₀, hx₀, h₀⟩ : ∃ x₀ ∈ X, x₀ * x₀ ∉ V := by
      by_contra h
      exact hcon fun x hx => by
        by_contra hx'
        exact h ⟨x, hx, hx'⟩
    have hbad : ∀ a ∈ X, ∀ b ∈ X, t * a * t⁻¹ * a⁻¹ ≠ 1 → t * b * t⁻¹ * b⁻¹ ≠ 1 →
        t * (a * b) * t⁻¹ * (a * b)⁻¹ ≠ 1 → b * a * b⁻¹ * a⁻¹ ∉ V := by
      intro a ha b hb ha1 hb1 hab1
      have h8 := H8 a ha b hb
      have k1 := H7 x₀ hx₀ h₀ _ (mul_mem ha hb) hab1
      have k2 := H7 x₀ hx₀ h₀ b hb hb1
      have k3 := H7 x₀ hx₀ h₀ a ha ha1
      tauto
    obtain ⟨v₁, hv₁, v₂, hv₂, v₃, hv₃, h1, h2, h21, h3, h31, h32, h312⟩ :=
      exists_three_of_four_lt hcard
    obtain ⟨x₁, hx₁, e₁⟩ := hsurj v₁ hv₁
    obtain ⟨x₂, hx₂, e₂⟩ := hsurj v₂ hv₂
    obtain ⟨x₃, hx₃, e₃⟩ := hsurj v₃ hv₃
    have k12 := hbad x₂ hx₂ x₁ hx₁ (by rw [e₂]; exact h2) (by rw [e₁]; exact h1)
      (by rw [hψmul hx₂ hx₁, e₁, e₂]; exact hne _ hv₂ _ hv₁ h21)
    have k13 := hbad x₃ hx₃ x₁ hx₁ (by rw [e₃]; exact h3) (by rw [e₁]; exact h1)
      (by rw [hψmul hx₃ hx₁, e₁, e₃]; exact hne _ hv₃ _ hv₁ h31)
    have k123 := hbad (x₂ * x₃) (mul_mem hx₂ hx₃) x₁ hx₁
      (by rw [hψmul hx₂ hx₃, e₂, e₃]; exact hne _ hv₂ _ hv₃ (Ne.symm h32))
      (by rw [e₁]; exact h1)
      (by
        rw [hψmul (mul_mem hx₂ hx₃) hx₁, hψmul hx₂ hx₃, e₁, e₂, e₃]
        exact hne _ (V.mul_mem hv₂ hv₃) _ hv₁ (hindep v₁ hv₁ v₂ hv₂ v₃ hv₃ h312))
    exact k123 ((H9 x₁ hx₁ x₂ hx₂ x₃ hx₃).2 (iff_of_false k12 k13))
  refine ⟨hsq, fun x hx y hy => ?_⟩
  have h8 := H8 y hy x hx
  have k1 := hsq _ (mul_mem hy hx)
  have k2 := hsq y hy
  have k3 := hsq x hx
  tauto

end CFSG.SeitzReduction.LinearPilot
