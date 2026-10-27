module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeClasses
public import CFSG.LieType.Multipliers.U62Bridge

public section

namespace CFSG.EvenSmallLie.UnitarySix.ToddOrbit

open Subgroup CFSG.Sporadic.Schreier CFSG.Fischer

variable {G : Type*} [Group G]

structure Hyp
    (t : G) (L E : Subgroup G)
    (p : L →* Equiv.Perm (Fin 693)) : Prop where
  mem_T46 : ∀ y, p y ∈ T46
  surj : ∀ x ∈ T46, ∃ y, p y = x
  ker : ∀ y : L, p y = 1 ↔ (y : G) = 1 ∨ (y : G) = t
  t_mem : t ∈ L
  le_centralizer : L ≤ centralizer {t}
  orderOf_t : orderOf t = 2
  mem_E : ∀ g, g ∈ E ↔ ∃ h : g ∈ L, p ⟨g, h⟩ ∈ uA
  E_sq : ∀ e ∈ E, e ^ 2 = 1
  odd : ∀ g ∈ centralizer {t}, Odd (orderOf g) → g ∈ L
  fusion : ∀ g : G, g⁻¹ * t * g ∈ E → ∃ n ∈ normalizer (E : Set G), g⁻¹ * t * g = n⁻¹ * t * n
  move : ∃ n ∈ normalizer (E : Set G), n⁻¹ * t * n ≠ t
  nonsplit : E ≤ ⁅E, normalizer (E : Set G) ⊓ L⁆

theorem exists_hom_T46
    {G : Type} [Group G] {L : Subgroup G} {t : G} (htL : t ∈ L)
    (htZ : (⟨t, htL⟩ : L) ∈ center L) (ht1 : t ≠ 1) (hZ : Nat.card (center L) = 2)
    (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) :
    ∃ p : L →* Equiv.Perm (Fin 693), (∀ y, p y ∈ T46) ∧ (∀ x ∈ T46, ∃ y, p y = x) ∧
      ∀ y : L, p y = 1 ↔ (y : G) = 1 ∨ (y : G) = t := by
  obtain ⟨e⟩ := CFSG.LieType.Multipliers.U62.nonempty_mulEquiv_T46 hQ
  refine ⟨T46.subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center L))),
    fun y => (e _).2, fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm ⟨x, hx⟩)
    refine ⟨y, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype]
    rw [hy, MulEquiv.apply_symm_apply]
  · have h1 : (T46.subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center L)))) y = 1 ↔
        y ∈ center L := by
      simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom,
        Subgroup.coe_subtype, OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff,
        QuotientGroup.eq_one_iff]
    rw [h1]
    obtain ⟨w, hw1, hwu⟩ := (Nat.card_eq_two_iff' (1 : center L)).1 hZ
    have htw : (⟨⟨t, htL⟩, htZ⟩ : center L) = w :=
      hwu _ fun h => ht1 (congrArg (fun z : center L => ((z : L) : G)) h)
    constructor
    · intro hy
      by_cases hy1 : (⟨y, hy⟩ : center L) = 1
      · exact Or.inl (congrArg (fun z : center L => ((z : L) : G)) hy1)
      · have := (hwu _ hy1).trans htw.symm
        exact Or.inr (congrArg (fun z : center L => ((z : L) : G)) this)
    · rintro (h | h)
      · have : y = 1 := Subtype.ext h
        rw [this]
        exact (center L).one_mem
      · have : y = ⟨t, htL⟩ := Subtype.ext h
        rw [this]
        exact htZ

@[expose] def toddLift
    {L : Subgroup G} (p : L →* Equiv.Perm (Fin 693)) : Subgroup G :=
  (uA.comap p).map L.subtype

theorem mem_toddLift
    {L : Subgroup G} {p : L →* Equiv.Perm (Fin 693)} {g : G} :
    g ∈ toddLift p ↔ ∃ h : g ∈ L, p ⟨g, h⟩ ∈ uA := by
  simp only [toddLift, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hA⟩
    exact ⟨⟨g, h⟩, hA, rfl⟩

open Classical in
@[expose] noncomputable def pe {L : Subgroup G} (p : L →* Equiv.Perm (Fin 693)) (g : G) :
    Equiv.Perm (Fin 693) :=
  if h : g ∈ L then p ⟨g, h⟩ else 1

section pe

variable {L : Subgroup G} (p : L →* Equiv.Perm (Fin 693))

theorem pe_of_mem {g : G} (h : g ∈ L) : pe p g = p ⟨g, h⟩ := by
  simp [pe, h]

theorem pe_mul {g h : G} (hg : g ∈ L) (hh : h ∈ L) : pe p (g * h) = pe p g * pe p h := by
  rw [pe_of_mem p (L.mul_mem hg hh), pe_of_mem p hg, pe_of_mem p hh, ← map_mul]
  rfl

theorem pe_inv {g : G} (hg : g ∈ L) : pe p g⁻¹ = (pe p g)⁻¹ := by
  rw [pe_of_mem p (L.inv_mem hg), pe_of_mem p hg, ← map_inv]
  rfl

theorem pe_pow {g : G} (hg : g ∈ L) (n : ℕ) : pe p (g ^ n) = pe p g ^ n := by
  rw [pe_of_mem p (L.pow_mem hg n), pe_of_mem p hg, ← map_pow]
  rfl

theorem pe_conj {g h : G} (hg : g ∈ L) (hh : h ∈ L) :
    pe p (g * h * g⁻¹) = pe p g * pe p h * (pe p g)⁻¹ := by
  rw [pe_mul p (L.mul_mem hg hh) (L.inv_mem hg), pe_mul p hg hh, pe_inv p hg]

end pe

namespace Hyp

variable {t : G} {L E : Subgroup G} {p : L →* Equiv.Perm (Fin 693)}

theorem t_ne_one
    (H : Hyp t L E p) : t ≠ 1 := fun h => by
  have := H.orderOf_t
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem t_sq
    (H : Hyp t L E p) : t ^ 2 = 1 := by
  rw [← H.orderOf_t]
  exact pow_orderOf_eq_one t

theorem t_mul_t
    (H : Hyp t L E p) : t * t = 1 := by
  rw [← sq, H.t_sq]

theorem comm_t
    (H : Hyp t L E p) {g : G} (hg : g ∈ L) : g * t = t * g :=
  mem_centralizer_singleton_iff.1 (H.le_centralizer hg)

theorem pe_t
    (H : Hyp t L E p) : pe p t = 1 := by
  rw [pe_of_mem p H.t_mem]
  exact (H.ker ⟨t, H.t_mem⟩).2 (Or.inr rfl)

theorem pe_mem_T46
    (H : Hyp t L E p) (g : G) : pe p g ∈ T46 := by
  by_cases hg : g ∈ L
  · rw [pe_of_mem p hg]
    exact H.mem_T46 _
  · simp only [pe, hg, dite_false]
    exact T46.one_mem

theorem exists_lift
    (H : Hyp t L E p) {x : Equiv.Perm (Fin 693)} (hx : x ∈ T46) :
    ∃ g ∈ L, pe p g = x := by
  obtain ⟨⟨g, hg⟩, rfl⟩ := H.surj x hx
  exact ⟨g, hg, pe_of_mem p hg⟩

theorem pe_eq_one_iff
    (H : Hyp t L E p) {g : G} (hg : g ∈ L) : pe p g = 1 ↔ g = 1 ∨ g = t := by
  rw [pe_of_mem p hg]
  exact H.ker ⟨g, hg⟩

theorem pe_eq_pe_iff
    (H : Hyp t L E p) {g s : G} (hg : g ∈ L) (hs : s ∈ L) :
    pe p s = pe p g ↔ s = g ∨ s = g * t := by
  have h1 : pe p s = pe p g ↔ pe p (g⁻¹ * s) = 1 := by
    rw [pe_mul p (L.inv_mem hg) hs, pe_inv p hg, inv_mul_eq_one, eq_comm]
  rw [h1, H.pe_eq_one_iff (L.mul_mem (L.inv_mem hg) hs), inv_mul_eq_one, inv_mul_eq_iff_eq_mul]
  exact or_congr eq_comm Iff.rfl

theorem mem_E_iff
    (H : Hyp t L E p) {g : G} : g ∈ E ↔ g ∈ L ∧ pe p g ∈ uA := by
  rw [H.mem_E]
  constructor
  · rintro ⟨h, hA⟩
    exact ⟨h, by rwa [pe_of_mem p h]⟩
  · rintro ⟨h, hA⟩
    exact ⟨h, by rwa [← pe_of_mem p h]⟩

theorem E_le_L
    (H : Hyp t L E p) : E ≤ L := fun _ hg => (H.mem_E_iff.1 hg).1

theorem t_mem_E
    (H : Hyp t L E p) : t ∈ E :=
  H.mem_E_iff.2 ⟨H.t_mem, by rw [H.pe_t]; exact uA.one_mem⟩

theorem mul_t_mem_E
    (H : Hyp t L E p) {g : G} (hg : g ∈ E) : g * t ∈ E :=
  E.mul_mem hg H.t_mem_E

theorem inv_eq_self
    (H : Hyp t L E p) {a : G} (ha : a ∈ E) : a⁻¹ = a := by
  have := H.E_sq a ha
  rw [sq] at this
  exact inv_eq_of_mul_eq_one_right this

theorem E_comm
    (H : Hyp t L E p) {a b : G} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  rw [← H.inv_eq_self (E.mul_mem ha hb), mul_inv_rev, H.inv_eq_self ha, H.inv_eq_self hb]

theorem exists_lift_pow_three
    (H : Hyp t L E p) {x : Equiv.Perm (Fin 693)} (hx : x ∈ T46)
    (hx3 : x ^ 3 = 1) : ∃ g ∈ L, pe p g = x ∧ g ^ 3 = 1 := by
  obtain ⟨g, hg, rfl⟩ := H.exists_lift hx
  have h3 : pe p (g ^ 3) = 1 := by rw [pe_pow p hg, hx3]
  rcases (H.pe_eq_one_iff (L.pow_mem hg 3)).1 h3 with h | h
  · exact ⟨g, hg, rfl, h⟩
  · refine ⟨g * t, L.mul_mem hg H.t_mem, ?_, ?_⟩
    · rw [pe_mul p hg H.t_mem, H.pe_t, mul_one]
    · rw [(Commute.mul_pow (H.comm_t hg) 3), h, ← pow_succ', show t ^ (3 + 1) = (t ^ 2) ^ 2 by
        rw [← pow_mul], H.t_sq, one_pow]

theorem not_sq
    (H : Hyp t L E p) : ∀ y ∈ L, y ^ 2 ≠ t := by
  intro y hy hyt
  have hx : pe p y ^ 2 = 1 := by rw [← pe_pow p hy, hyt, H.pe_t]
  have hx1 : pe p y ≠ 1 := by
    intro h
    rcases (H.pe_eq_one_iff hy).1 h with rfl | rfl
    · rw [one_pow] at hyt
      exact H.t_ne_one hyt.symm
    · rw [H.t_sq] at hyt
      exact H.t_ne_one hyt.symm
  have ho : orderOf (pe p y) = 2 := orderOf_eq_prime hx hx1
  obtain ⟨g, hgT, hgA⟩ := conj_into_uA (H.pe_mem_T46 y) ho
  obtain ⟨g', hg', rfl⟩ := H.exists_lift hgT
  have hw : g' * y * g'⁻¹ ∈ E := by
    refine H.mem_E_iff.2 ⟨L.mul_mem (L.mul_mem hg' hy) (L.inv_mem hg'), ?_⟩
    rwa [pe_conj p hg' hy]
  have h1 := H.E_sq _ hw
  rw [conj_pow, hyt, mul_inv_eq_one, mul_eq_left] at h1
  exact H.t_ne_one h1

theorem exists_sq_lift
    (H : Hyp t L E p) :
    ∃ z ∈ E, pe p z = j1 ∧ ∃ u ∈ L, ∃ v ∈ L, u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * z = z * u ∧
      v * z = z * v ∧ (u * v) ^ 2 = z := by
  obtain ⟨u, hu, v, hv, hou, hov, huj, hvj, huv⟩ := sq_j1
  obtain ⟨u', hu', hpu, hu3⟩ :=
    H.exists_lift_pow_three hu (by rw [← hou]; exact pow_orderOf_eq_one u)
  obtain ⟨v', hv', hpv, hv3⟩ :=
    H.exists_lift_pow_three hv (by rw [← hov]; exact pow_orderOf_eq_one v)
  have hzL : (u' * v') ^ 2 ∈ L := L.pow_mem (L.mul_mem hu' hv') 2
  have hpz : pe p ((u' * v') ^ 2) = j1 := by
    rw [pe_pow p (L.mul_mem hu' hv'), pe_mul p hu' hv', hpu, hpv, huv]
  have hcomm : ∀ w ∈ L, w ^ 3 = 1 → pe p w * j1 = j1 * pe p w →
      w * (u' * v') ^ 2 = (u' * v') ^ 2 * w := by
    intro w hw hw3 hwj
    set z := (u' * v') ^ 2
    have hfib : w * z * w⁻¹ = z ∨ w * z * w⁻¹ = z * t := by
      refine (H.pe_eq_pe_iff hzL (L.mul_mem (L.mul_mem hw hzL) (L.inv_mem hw))).1 ?_
      rw [pe_conj p hw hzL, hpz, hwj, mul_inv_cancel_right]
    rcases hfib with h | h
    · calc w * z = w * z * w⁻¹ * w := by group
        _ = z * w := by rw [h]
    · exfalso
      have hwt : w * t = t * w := H.comm_t hw
      have e1 : w * z = z * t * w := by
        calc w * z = w * z * w⁻¹ * w := by group
          _ = z * t * w := by rw [h]
      have e2 : w ^ 2 * z = z * w ^ 2 := by
        calc w ^ 2 * z = w * (w * z) := by rw [sq, mul_assoc]
          _ = w * (z * t * w) := by rw [e1]
          _ = w * z * t * w := by group
          _ = z * t * w * t * w := by rw [e1]
          _ = z * t * (w * t) * w := by group
          _ = z * t * (t * w) * w := by rw [hwt]
          _ = z * (t * t) * (w * w) := by group
          _ = z * w ^ 2 := by rw [H.t_mul_t, sq]; group
      have e3 : w ^ 3 * z = z * t * w ^ 3 := by
        calc w ^ 3 * z = w * (w ^ 2 * z) := by rw [pow_succ', mul_assoc]
          _ = w * z * w ^ 2 := by rw [e2]; group
          _ = z * t * w * w ^ 2 := by rw [e1]
          _ = z * t * w ^ 3 := by rw [pow_succ' w 2]; group
      rw [hw3, one_mul, mul_one] at e3
      exact H.t_ne_one (by simpa using e3.symm)
  exact ⟨(u' * v') ^ 2, H.mem_E_iff.2 ⟨hzL, by rw [hpz]; exact j1_mem⟩, hpz, u', hu', v', hv',
    hu3, hv3, hcomm u' hu' hu3 (by rw [hpu]; exact huj),
    hcomm v' hv' hv3 (by rw [hpv]; exact hvj), rfl⟩

theorem not_conj_of_sq
    (H : Hyp t L E p) {z u v : G} (hu : u ^ 3 = 1) (hv : v ^ 3 = 1)
    (huz : u * z = z * u) (hvz : v * z = z * v) (hz : (u * v) ^ 2 = z) (g : G) :
    g⁻¹ * t * g ≠ z := by
  intro h
  have ht : t = g * z * g⁻¹ := by rw [← h]; group
  have hmem : ∀ w : G, w ^ 3 = 1 → w * z = z * w → g * w * g⁻¹ ∈ L := by
    intro w hw3 hwz
    refine H.odd _ (mem_centralizer_singleton_iff.2 ?_) ?_
    · rw [ht]
      calc g * w * g⁻¹ * (g * z * g⁻¹) = g * (w * z) * g⁻¹ := by group
        _ = g * (z * w) * g⁻¹ := by rw [hwz]
        _ = g * z * g⁻¹ * (g * w * g⁻¹) := by group
    · rw [show g * w * g⁻¹ = MulAut.conj g w from rfl, MulEquiv.orderOf_eq]
      exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hw3)
  refine H.not_sq _ (L.mul_mem (hmem u hu huz) (hmem v hv hvz)) ?_
  have e : g * u * g⁻¹ * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := by group
  rw [e, conj_pow, hz]
  exact ht.symm

end Hyp

end CFSG.EvenSmallLie.UnitarySix.ToddOrbit
