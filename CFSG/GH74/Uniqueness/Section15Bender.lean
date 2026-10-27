module

public import CFSG.GH74.Uniqueness.Bender.Out

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {X : Type} [Group X] [Finite X]

namespace Section15Bender

omit [Finite X] in
theorem coe_normalizerMonoidHom {L : Subgroup X} {g : X} (hg : g ∈ normalizer (L : Set X))
    (l : ↥L) : ((L.normalizerMonoidHom ⟨g, hg⟩ l : ↥L) : X) = g * l * g⁻¹ := rfl

omit [Finite X] in
theorem exists_mul_centralizer_of_eq_conj {L : Subgroup X} {g : X}
    (hg : g ∈ normalizer (L : Set X)) {r : ↥L}
    (hr : ∀ k : ↥L, L.normalizerMonoidHom ⟨g, hg⟩ k = r * k * r⁻¹) :
    ∃ j ∈ centralizer (L : Set X), g = (r : X) * j := by
  refine ⟨(r : X)⁻¹ * g, ?_, by group⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have h1 : g * h * g⁻¹ = (r : X) * h * (r : X)⁻¹ := congrArg Subtype.val (hr ⟨h, hh⟩)
  calc h * ((r : X)⁻¹ * g) = (r : X)⁻¹ * ((r : X) * h * (r : X)⁻¹) * g := by group
    _ = (r : X)⁻¹ * (g * h * g⁻¹) * g := by rw [h1]
    _ = (r : X)⁻¹ * g * h := by group

omit [Finite X] in
noncomputable def outerHom (L : Subgroup X) : ↥(normalizer (L : Set X)) →* Outer ↥L :=
  (QuotientGroup.mk' (inner ↥L)).comp L.normalizerMonoidHom

omit [Finite X] in
theorem outerHom_eq_one_iff {L : Subgroup X} (y : ↥(normalizer (L : Set X))) :
    outerHom L y = 1 ↔ (y : X) ∈ L ⊔ centralizer (L : Set X) := by
  obtain ⟨g, hg⟩ := y
  rw [outerHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨j, hj, hgj⟩ := exists_mul_centralizer_of_eq_conj hg (r := r) fun k => by
      rw [← hr]
      rfl
    change g ∈ L ⊔ centralizer (L : Set X)
    rw [hgj]
    exact Subgroup.mul_mem_sup r.2 hj
  · intro hmem
    obtain ⟨a, ha, b, hb, hab⟩ := Bender.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha) hmem
    refine ⟨⟨a, ha⟩, ?_⟩
    ext k
    change a * (k : X) * a⁻¹ = g * k * g⁻¹
    have hbk : (k : X) * b = b * k := Subgroup.mem_centralizer_iff.mp hb k k.2
    have hab' : g = a * b := hab
    rw [hab']
    calc a * (k : X) * a⁻¹ = a * ((k : X) * b) * b⁻¹ * a⁻¹ := by group
      _ = a * (b * k) * b⁻¹ * a⁻¹ := by rw [hbk]
      _ = a * b * k * (a * b)⁻¹ := by group

end Section15Bender

open Section15Bender

theorem bender_cent_sylow
    {L : Subgroup X} {n i e : ℕ} (hB : Bender.BenderType ↥L n i e)
    (Q : Sylow 2 ↥L) {g : X} (hg : g ∈ normalizer (L : Set X))
    (hgQ : ∀ x ∈ (Q : Subgroup ↥L).map L.subtype, g * x = x * g) :
    ∃ m ∈ (Bender.rootCenter (Q : Subgroup ↥L)).map L.subtype, ∃ j ∈ centralizer (L : Set X),
      g = m * j := by
  obtain ⟨r, hr, hσ⟩ := hB.lemma_3_6_a Q (L.normalizerMonoidHom ⟨g, hg⟩) fun x hx => by
    apply Subtype.ext
    rw [coe_normalizerMonoidHom]
    have h1 := hgQ (x : X) ⟨x, hx, rfl⟩
    calc g * (x : X) * g⁻¹ = (x : X) * g * g⁻¹ := by rw [h1]
      _ = x := by group
  obtain ⟨j, hj, hgj⟩ := exists_mul_centralizer_of_eq_conj hg hσ
  exact ⟨r, ⟨r, hr, rfl⟩, j, hj, hgj⟩

theorem bender_cent_cartan
    {L : Subgroup X} {n : ℕ} (hB : Bender.BenderType ↥L n 1 1)
    (Q : Sylow 2 ↥L) {t : ↥L} (ht : t * t = 1) (htQ : t ∉ Bender.borel (Q : Subgroup ↥L)) {g : X}
    (hg : g ∈ normalizer (L : Set X))
    (hgQ : ∀ x ∈ (Q : Subgroup ↥L).map L.subtype,
      g * x * g⁻¹ ∈ (Q : Subgroup ↥L).map L.subtype)
    (hgD : ∀ x ∈ (Bender.cartan (Q : Subgroup ↥L) t).map L.subtype, g * x = x * g) :
    ∃ k ∈ (Bender.cartan (Q : Subgroup ↥L) t).map L.subtype, ∃ j ∈ centralizer (L : Set X),
      g = k * j := by
  obtain ⟨d, hd, hσ⟩ := hB.aut_eq_conj_cartan_linear Q ht htQ (L.normalizerMonoidHom ⟨g, hg⟩)
    (fun x hx => by
      obtain ⟨y, hy, hyx⟩ := hgQ (x : X) ⟨x, hx, rfl⟩
      have h1 : L.normalizerMonoidHom ⟨g, hg⟩ x = y :=
        Subtype.ext (by rw [coe_normalizerMonoidHom]; exact hyx.symm)
      rw [h1]
      exact hy)
    (fun d hd => by
      apply Subtype.ext
      rw [coe_normalizerMonoidHom]
      have h1 := hgD (d : X) ⟨d, hd, rfl⟩
      calc g * (d : X) * g⁻¹ = (d : X) * g * g⁻¹ := by rw [h1]
        _ = d := by group)
  obtain ⟨j, hj, hgj⟩ := exists_mul_centralizer_of_eq_conj hg hσ
  exact ⟨d, ⟨d, hd, rfl⟩, j, hj, hgj⟩

theorem bender_out_cyclic {L : Subgroup X} {n : ℕ} (hB : Bender.BenderType ↥L n 1 1) :
    ∃ g₀ ∈ normalizer (L : Set X), ∀ g ∈ normalizer (L : Set X), ∃ i : ℕ,
      g * (g₀ ^ i)⁻¹ ∈ L ⊔ centralizer (L : Set X) := by
  have hcyc : IsCyclic (Outer ↥L) := hB.outer_linear.1
  have : Finite (MulAut ↥L) :=
    Finite.of_injective (fun f : MulAut ↥L => (f : ↥L → ↥L)) DFunLike.coe_injective
  have : Finite (Outer ↥L) := inferInstance
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := ↥(outerHom L).range)
  obtain ⟨g₀', hg₀'⟩ := c.2
  refine ⟨(g₀' : X), g₀'.2, fun g hg => ?_⟩
  have hx : outerHom L ⟨g, hg⟩ ∈ (outerHom L).range := ⟨⟨g, hg⟩, rfl⟩
  obtain ⟨i, hi⟩ := Submonoid.mem_powers_iff _ _ |>.mp
    (mem_powers_iff_mem_zpowers.mpr (hc ⟨outerHom L ⟨g, hg⟩, hx⟩))
  refine ⟨i, ?_⟩
  have h1 : outerHom L ⟨g, hg⟩ = outerHom L (g₀' ^ i) := by
    rw [map_pow, hg₀']
    have h2 := congrArg Subtype.val hi
    simpa using h2.symm
  have h2 : outerHom L (⟨g, hg⟩ * (g₀' ^ i)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← h1]
    exact mul_inv_cancel _
  have h3 := (outerHom_eq_one_iff _).mp h2
  simpa using h3

omit [Finite X] in
theorem bender_out_three {L : Subgroup X} (hB : Bender.BenderType ↥L 3 1 1) {g : X}
    (hg : g ∈ normalizer (L : Set X)) (hg2 : g * g ∈ L ⊔ centralizer (L : Set X)) :
    g ∈ L ⊔ centralizer (L : Set X) := by
  have hcard : Nat.card (Outer ↥L) = 3 := hB.outer_linear.2
  have h2 : outerHom L ⟨g, hg⟩ ^ 2 = 1 := by
    rw [sq, ← map_mul, outerHom_eq_one_iff]
    exact hg2
  have h3 : outerHom L ⟨g, hg⟩ ^ 3 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have h1 : outerHom L ⟨g, hg⟩ = 1 := by
    calc outerHom L ⟨g, hg⟩ = outerHom L ⟨g, hg⟩ ^ 3 * (outerHom L ⟨g, hg⟩ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h2, h3]; simp
  exact (outerHom_eq_one_iff _).mp h1

theorem bender_rank_le
    {L : Subgroup X} {n : ℕ} (hB : Bender.BenderType ↥L n 1 1) (A : Subgroup X)
    (hA : A ≤ normalizer (L : Set X)) (hsq : ∀ a ∈ A, a * a = 1) :
    Nat.card A ≤ 2 ^ n * Nat.card ↥(A ⊓ centralizer (L : Set X)) := by
  classical
  let φ : ↥A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hA)
  have hker : φ.ker = (A ⊓ centralizer (L : Set X)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h1
      refine ⟨a.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      have h2 : (a : X) * l * (a : X)⁻¹ = l :=
        congrArg Subtype.val (DFunLike.congr_fun h1 (⟨l, hl⟩ : ↥L))
      calc l * (a : X) = ((a : X) * l * (a : X)⁻¹) * a := by rw [h2]
        _ = (a : X) * l := by group
    · rintro ⟨-, h1⟩
      ext l
      change (a : X) * l * (a : X)⁻¹ = l
      have h2 : (l : X) * a = a * l := Subgroup.mem_centralizer_iff.mp h1 l l.2
      calc (a : X) * l * (a : X)⁻¹ = ((l : X) * a) * (a : X)⁻¹ := by rw [h2]
        _ = l := by group
  have hsq' : ∀ x ∈ φ.range, x * x = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have h1 : a * a = 1 := Subtype.ext (hsq a a.2)
    rw [h1, map_one]
  have hle : Nat.card φ.range ≤ 2 ^ n :=
    (hB.card_le_of_sq_eq_one_aut φ.range hsq').2 (by norm_num)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : A ⊓ centralizer (L : Set X) ≤ A)).toEquiv] at h1
  rw [h1]
  exact Nat.mul_le_mul_right _ hle

end CFSG.GH74.Uniqueness
