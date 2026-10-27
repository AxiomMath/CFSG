module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.Fusion
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.Orbit
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.Centralize
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.Zsig
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.FieldFacts

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open Subgroup CFSG.Open

@[expose] def ConjLines {G : Type} [Group G] (W : Subgroup G) (x : G) : Set (Subgroup G) :=
  {L | L ≤ W ∧ ∃ g : G, L = (zpowers x).map (MulAut.conj g).toMonoidHom}

theorem map_conj_map_conj {G : Type} [Group G] (L : Subgroup G) (m g : G) :
    (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj m).toMonoidHom =
      L.map (MulAut.conj (m * g)).toMonoidHom := by
  have hcomp : (MulAut.conj m).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (m * g)).toMonoidHom := MonoidHom.ext fun z => by simp [mul_assoc]
  rw [Subgroup.map_map, hcomp]

theorem conjLines_closed {G : Type} [Group G] {W : Subgroup G} {x m : G}
    (hm : m ∈ normalizer (W : Set G)) {L : Subgroup G} (hL : L ∈ ConjLines W x) :
    L.map (MulAut.conj m).toMonoidHom ∈ ConjLines W x := by
  obtain ⟨hLW, g, rfl⟩ := hL
  refine ⟨?_, m * g, map_conj_map_conj _ m g⟩
  rintro _ ⟨a, haL, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp hm a).mp (hLW haL)

namespace FusionData

variable {G : Type} [Group G] [Finite G] {p n : ℕ} {F : Type} [Field F] {f : F → G} {x : G}
  {W : Subgroup G} (h : FusionData G p n F f x W)

include h

omit [Finite G] in
theorem conjLines_trans {L : Subgroup G} (hL : L ∈ ConjLines W x) :
    ∃ m ∈ normalizer (W : Set G), L = (zpowers x).map (MulAut.conj m).toMonoidHom := by
  obtain ⟨hLW, g, rfl⟩ := hL
  have hg : g * x * g⁻¹ ∈ W := by
    apply hLW
    exact Subgroup.mem_map.mpr ⟨x, mem_zpowers x, by simp⟩
  obtain ⟨m, hm, hmx⟩ := h.trans g hg
  refine ⟨m, hm, ?_⟩
  rw [map_conj_zpowers', map_conj_zpowers', hmx]

omit [Finite G] in
theorem zpowers_mem_conjLines : zpowers x ∈ ConjLines W x :=
  ⟨(zpowers_le).mpr h.x_mem, conjLine_self x⟩

theorem not_conjLine_B_of_odd [hp : Fact p.Prime] [CharP F p] [Finite F] (hp2 : p ≠ 2)
    (hn : Odd n) {t : F} (ht : t ≠ 0) (hB : ConjLine x (f t)) : False := by
  obtain ⟨ν, hν⟩ := exists_natCast_not_isSquare h.card_F hp2 hn
  have hν0 : (ν : F) ≠ 0 := fun h0 => hν (by rw [h0]; exact IsSquare.zero)
  have hνt : ConjLine x (f ((ν : F) * t)) := by
    refine h.conjLine_of_mem hB ?_ ?_
    · rw [h.f_natCast_mul]
      exact Subgroup.pow_mem _ (mem_zpowers _) ν
    · intro h1
      exact mul_ne_zero hν0 ht (h.f_inj (h1.trans h.f_zero.symm))
  have hall : ∀ s : F, s ≠ 0 → ConjLine x (f s) := by
    intro s hs
    have hst : s / t ≠ 0 := div_ne_zero hs ht
    rcases isSquare_or_isSquare_mul hν hst with ⟨a, ha⟩ | ⟨a, ha⟩
    · have ha0 : a ≠ 0 := by
        rintro rfl
        exact hst (by rw [ha, mul_zero])
      have hsa : s = a ^ 2 * t := by
        rw [div_eq_iff ht] at ha
        rw [ha]; ring
      rw [hsa]
      exact h.conjLine_B_torus hB ha0
    · have ha0 : a ≠ 0 := by
        rintro rfl
        exact mul_ne_zero hst hν0 (by rw [ha, mul_zero])
      have h1 : s * ν = a * a * t := by
        have := ha
        rw [div_mul_eq_mul_div, div_eq_iff ht] at this
        exact this
      have hsa : s = (a * (ν : F)⁻¹) ^ 2 * ((ν : F) * t) := by
        have hinv : (ν : F) * (ν : F)⁻¹ = 1 := mul_inv_cancel₀ hν0
        linear_combination (ν : F)⁻¹ * h1 - s * hinv - a * a * t * (ν : F)⁻¹ * hinv +
          0 * h1
      rw [hsa]
      exact h.conjLine_B_torus hνt (mul_ne_zero ha0 (inv_ne_zero hν0))
  obtain ⟨c, hc⟩ := exists_not_natCast h.card_F h.two_le
  exact h.false_of_B_plane one_ne_zero hc fun m _ =>
    hall _ (mul_ne_zero one_ne_zero (natCast_add_ne_zero hc m))

theorem not_conjLine_A_of_odd [hp : Fact p.Prime] [CharP F p] [Finite F] (hp2 : p ≠ 2)
    (hnoB : ∀ t : F, t ≠ 0 → ¬ ConjLine x (f t)) {k : F} (hk : k ≠ 0)
    (hA : ConjLine x (f k * x)) : False := by
  classical
  by_cases hcase : ∃ s₀ : F, ConjLine x (f s₀ * x) ∧ s₀ ≠ 0 ∧ ¬ IsSquare (s₀ / k)
  · obtain ⟨s₀, hs₀, hs₀0, hns⟩ := hcase
    have hall : ∀ w : F, ConjLine x (f w * x) := by
      intro w
      by_cases hw : w = 0
      · rw [hw, h.f_zero, one_mul]
        exact conjLine_self x
      have hwk : w / k ≠ 0 := div_ne_zero hw hk
      rcases isSquare_or_isSquare_mul hns hwk with ⟨a, ha⟩ | ⟨a, ha⟩
      · have ha0 : a ≠ 0 := by
          rintro rfl
          exact hwk (by rw [ha, mul_zero])
        have hwa : w = a ^ 2 * k := by
          rw [div_eq_iff hk] at ha
          rw [ha]; ring
        rw [hwa]
        exact h.conjLine_A_torus hA ha0
      · have ha0 : a ≠ 0 := by
          rintro rfl
          exact mul_ne_zero hwk (div_ne_zero hs₀0 hk) (by rw [ha, mul_zero])
        have h1 : w * s₀ = a * a * (k * k) := by
          have := ha
          field_simp at this
          linear_combination this
        have hwa : w = (a * k * s₀⁻¹) ^ 2 * s₀ := by
          have hinv : s₀ * s₀⁻¹ = 1 := mul_inv_cancel₀ hs₀0
          linear_combination s₀⁻¹ * h1 - (w + a * a * k * k * s₀⁻¹) * hinv
        rw [hwa]
        exact h.conjLine_A_torus hs₀ (mul_ne_zero (mul_ne_zero ha0 hk) (inv_ne_zero hs₀0))
    exact h.false_of_A_plane hk fun m _ => hall ((m : F) * k)
  push Not at hcase
  let T : Set F := insert 0 ((fun a => k * a) '' squareSet F)
  let φ : F → Subgroup G := fun s => zpowers (f s * x)
  have hφinj : Function.Injective φ := fun s s' hss => h.eq_of_zpowers_mul_eq hss
  have hD : ConjLines W x = φ '' T := by
    ext L
    constructor
    · rintro ⟨hLW, g, hg⟩
      have hLy : L = zpowers (g * x * g⁻¹) := by rw [hg, map_conj_zpowers']
      have hyL : g * x * g⁻¹ ∈ L := by rw [hLy]; exact mem_zpowers _
      have hyW : g * x * g⁻¹ ∈ W := hLW hyL
      have hyc : ConjLine x (g * x * g⁻¹) := ⟨g, hLy.symm.trans hg⟩
      have hy1 : g * x * g⁻¹ ≠ 1 := by
        intro h1
        apply h.x_ne_one
        have h2 : g * x = g * 1 := by rw [mul_one]; exact mul_inv_eq_one.mp h1
        exact mul_left_cancel h2
      by_cases hyx : g * x * g⁻¹ ∈ zpowers x
      · have heq : zpowers (g * x * g⁻¹) = zpowers x :=
          h.zpowers_eq_of_mem (conjLine_self x) hyx hy1
        refine ⟨0, Set.mem_insert _ _, ?_⟩
        show zpowers (f 0 * x) = L
        rw [h.f_zero, one_mul, ← heq, hLy]
      · rcases h.exists_type hyW hyc hyx with ⟨t, ht, hte⟩ | ⟨t, ht, hte⟩
        · exfalso
          obtain ⟨g', hg'⟩ := hyc
          exact hnoB t ht ⟨g', hte.symm.trans hg'⟩
        · have hct : ConjLine x (f t * x) := by
            obtain ⟨g', hg'⟩ := hyc
            exact ⟨g', hte.symm.trans hg'⟩
          obtain ⟨a, ha⟩ := hcase t hct ht
          have ha0 : a ≠ 0 := by
            rintro rfl
            exact ht (by rw [div_eq_iff hk] at ha; rw [ha, mul_zero, zero_mul])
          refine ⟨t, Or.inr ⟨a ^ 2, ⟨a, ha0, rfl⟩, ?_⟩, ?_⟩
          · show k * a ^ 2 = t
            rw [div_eq_iff hk] at ha
            rw [ha]; ring
          · show zpowers (f t * x) = L
            rw [← hte, hLy]
    · rintro ⟨s, hs, rfl⟩
      rcases hs with rfl | ⟨u, ⟨a, ha0, rfl⟩, rfl⟩
      · show zpowers (f 0 * x) ∈ ConjLines W x
        rw [h.f_zero, one_mul]
        exact h.zpowers_mem_conjLines
      · have hc : ConjLine x (f (a ^ 2 * k) * x) := h.conjLine_A_torus hA ha0
        rw [mul_comm (a ^ 2) k] at hc
        refine ⟨?_, ?_⟩
        · exact (zpowers_le).mpr (mul_mem (h.f_mem _) h.x_mem)
        · obtain ⟨g, hg⟩ := hc
          exact ⟨g, hg⟩
  have hT : T.ncard = (p ^ n + 1) / 2 := by
    have h0 : (0 : F) ∉ (fun a => k * a) '' squareSet F := by
      rintro ⟨u, ⟨a, ha0, rfl⟩, h0⟩
      exact mul_ne_zero hk (pow_ne_zero 2 ha0) h0
    have hodd : Odd (p ^ n) := (hp.out.odd_of_ne_two hp2).pow
    rw [Set.ncard_insert_of_notMem h0 (Set.toFinite _),
      Set.ncard_image_of_injective _ (mul_right_injective₀ hk), ncard_squareSet h.card_F hp2]
    obtain ⟨c, hc⟩ := hodd
    generalize p ^ n = q at hc ⊢
    omega
  have hcard : Nat.card (ConjLines W x) = (p ^ n + 1) / 2 := by
    rw [Nat.card_coe_set_eq, hD, Set.ncard_image_of_injective _ hφinj, hT]
  obtain ⟨r, hr, hrp, hr2, hrd, hZ⟩ :=
    exists_prime_primitive_dvd_pow_add_one hp.out hp2 h.two_le
  have : Fact r.Prime := ⟨hr⟩
  have hnd := not_dvd_card_of_centralizes h.x_mem (ConjLines W x) h.zpowers_mem_conjLines
    (fun m hm L hL => conjLines_closed hm hL) (fun L hL => h.conjLines_trans hL)
    (fun m hm hmr => centralizes_of_isPGroup_zpowers hrp h.card_W hZ hm hmr)
  apply hnd
  rw [hcard]
  have hodd : Odd (p ^ n) := (hp.out.odd_of_ne_two hp2).pow
  have h2d : 2 * ((p ^ n + 1) / 2) = p ^ n + 1 := by
    obtain ⟨c, hc⟩ := hodd
    generalize p ^ n = q at hc ⊢
    omega
  have hdvd : r ∣ 2 * ((p ^ n + 1) / 2) := by rw [h2d]; exact hrd
  rcases (Nat.Prime.dvd_mul hr).mp hdvd with h2 | h2
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2) hr2
  · exact h2

end FusionData

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
