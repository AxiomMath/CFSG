module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRBase

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup

theorem center_eq_bot_of_not_prime {G : Type*} [Group G] (hs : IsSimpleGroup G) {n : ℕ}
    (hn : Nat.card G = n) (hp : ¬ n.Prime) : center G = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative G := ⟨⟨fun a b => (Subgroup.mem_center_iff.1
      (h ▸ Subgroup.mem_top b) a)⟩⟩
    have hq := Group.is_simple_iff_prime_card.1 hs
    rw [hn] at hq
    exact hp hq

theorem centralizer_map_subtype_eq {M : Type*} [Group M] (H : Subgroup M) (t : H) :
    (centralizer ({t} : Set H)).map H.subtype = H ⊓ centralizer ({(t : M)} : Set M) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype,
    Subgroup.mem_inf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa using congrArg Subtype.val hy⟩
  · rintro ⟨hx, hxt⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxt, rfl⟩

theorem not_isPGroup_centralizer_of_inf {M : Type*} [Group M] {H : Subgroup M} (t : H)
    (h : ¬ IsPGroup 2 ↥(H ⊓ centralizer ({(t : M)} : Set M))) :
    ¬ IsPGroup 2 ↥(centralizer ({t} : Set H)) := by
  intro hP
  apply h
  rw [← centralizer_map_subtype_eq]
  exact hP.of_equiv (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective)

theorem not_isPGroup_centralizer_of_isConj {G : Type*} [Group G] {a t : G} (h : IsConj a t)
    (ha : ¬ IsPGroup 2 ↥(centralizer ({a} : Set G))) :
    ¬ IsPGroup 2 ↥(centralizer ({t} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  intro hP
  apply ha
  have hmem : ∀ g : ↥(centralizer ({a} : Set G)),
      (MulAut.conj c).toMonoidHom.comp (centralizer ({a} : Set G)).subtype g ∈
        centralizer ({t} : Set G) := by
    intro g
    have hg : (g : G) * a = a * g := mem_centralizer_singleton_iff.mp g.2
    rw [mem_centralizer_singleton_iff, ← hc]
    change c * (g : G) * c⁻¹ * (c * a * c⁻¹) = c * a * c⁻¹ * (c * g * c⁻¹)
    calc c * (g : G) * c⁻¹ * (c * a * c⁻¹) = c * ((g : G) * a) * c⁻¹ := by group
      _ = c * (a * g) * c⁻¹ := by rw [hg]
      _ = c * a * c⁻¹ * (c * g * c⁻¹) := by group
  refine hP.of_injective (((MulAut.conj c).toMonoidHom.comp
    (centralizer ({a} : Set G)).subtype).codRestrict _ hmem) ?_
  intro y z hyz
  have h' : c * (y : G) * c⁻¹ = c * z * c⁻¹ := congrArg Subtype.val hyz
  exact Subtype.ext (by simpa using h')

theorem inner_of_bijective {P : Type*} [Group P]
    (h : Function.Bijective (MulAut.conj : P →* MulAut P)) :
    ∀ a : MulAut P, ∃ t : P, a = MulAut.conj t := by
  intro a
  obtain ⟨t, ht⟩ := h.2 a
  exact ⟨t, ht.symm⟩

theorem forall_of_inner_reps {P : Type} [Group P] (hZ : center P = ⊥)
    (hinn : ∀ a : MulAut P, ∃ t : P, a = MulAut.conj t) (reps : List P)
    (hcov : ∀ t : P, orderOf t = 2 → ∃ r ∈ reps, IsConj r t)
    (hrep : ∀ r ∈ reps, ¬ IsPGroup 2 ↥(centralizer ({r} : Set P))) :
    ∀ a : MulAut P, orderOf a = 2 → ¬ IsPGroup 2 ↥(fixedPoints a) := by
  refine forall_of_inner hZ hinn fun t ht => ?_
  obtain ⟨r, hr, hrt⟩ := hcov t ht
  exact not_isPGroup_centralizer_of_isConj hrt (hrep r hr)

theorem mem_inner_of_odd_outer {G : Type*} [Group G]
    (hodd : Odd (Nat.card (OuterAutomorphisms.Outer G))) {α : MulAut G} (hα : α ^ 2 = 1) :
    α ∈ OuterAutomorphisms.inner G := by
  set x : OuterAutomorphisms.Outer G := QuotientGroup.mk α
  have hx2 : x ^ 2 = 1 := by rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have h2 : Odd (orderOf x) := Odd.of_dvd_nat hodd (orderOf_dvd_natCard x)
  have h3 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd h2 (by decide)
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff α).mp h3

theorem not_isPGroup_inf_centralizer_conj_of_normalizes {M : Type*} [Group M] {H : Subgroup M}
    {g : M} (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H) {t : M}
    (h : ¬ IsPGroup 2 ↥(H ⊓ centralizer ({t} : Set M))) :
    ¬ IsPGroup 2 ↥(H ⊓ centralizer ({g * t * g⁻¹} : Set M)) := by
  intro hP
  apply h
  have hmem : ∀ z : ↥(H ⊓ centralizer ({t} : Set M)),
      g * (z : M) * g⁻¹ ∈ H ⊓ centralizer ({g * t * g⁻¹} : Set M) := by
    intro z
    refine Subgroup.mem_inf.mpr ⟨hg _ z.2.1, ?_⟩
    have hz : (z : M) * t = t * z := mem_centralizer_singleton_iff.mp z.2.2
    rw [mem_centralizer_singleton_iff]
    calc g * (z : M) * g⁻¹ * (g * t * g⁻¹) = g * ((z : M) * t) * g⁻¹ := by group
      _ = g * (t * z) * g⁻¹ := by rw [hz]
      _ = g * t * g⁻¹ * (g * z * g⁻¹) := by group
  refine hP.of_injective (((MulAut.conj g).toMonoidHom.comp
    (H ⊓ centralizer ({t} : Set M)).subtype).codRestrict _ hmem) ?_
  intro y z hyz
  have h' : g * (y : M) * g⁻¹ = g * z * g⁻¹ := congrArg Subtype.val hyz
  exact Subtype.ext (by simpa using h')

end CFSG.ComponentClassification.HarrisLit.L33.SR
