module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSK
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup
open scoped commutatorElement

section LevelF

variable {N : Type} [Group N]

@[expose] def preimg (C' : Subgroup N) [C'.Normal] (S : Subgroup (N ⧸ C')) : Subgroup N :=
  S.comap (QuotientGroup.mk' C')

theorem mem_preimg {C' : Subgroup N} [C'.Normal] {S : Subgroup (N ⧸ C')} {g : N} :
    g ∈ preimg C' S ↔ (g : N ⧸ C') ∈ S := Iff.rfl

@[expose] def Ecomm (C' : Subgroup N) [C'.Normal] (S : Subgroup (N ⧸ C')) : Subgroup N :=
  ⁅preimg C' S, preimg C' S⁆

theorem C_le_preimg {C' : Subgroup N} [C'.Normal] (S : Subgroup (N ⧸ C')) : C' ≤ preimg C' S :=
  fun c hc => mem_preimg.2 (by rw [(QuotientGroup.eq_one_iff c).2 hc]; exact one_mem _)

theorem Ecomm_le_preimg (C' : Subgroup N) [C'.Normal] (S : Subgroup (N ⧸ C')) :
    Ecomm C' S ≤ preimg C' S := commutator_le_self _

structure LevelFData [Finite N] (C' : Subgroup N) [C'.Normal] (S1 S2 : Subgroup (N ⧸ C'))
    (D1 D2 : Subgroup N) (z : N) (z2 : N ⧸ C') : Prop where
  card_C : ¬ 3 ∣ Nat.card C'
  D1_le : D1 ≤ C'
  D2_le : D2 ≤ C'
  prod : ∀ c ∈ C', ∃ a ∈ D1, ∃ b ∈ D2, c = a * b
  inf : D1 ⊓ D2 = ⊥
  comm12 : ∀ a ∈ D1, ∀ b ∈ D2, a * b = b * a
  comm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a
  perf1 : ⁅S1, S1⁆ = S1
  S12 : S1 ⊓ S2 = ⊥
  triv1 : ∀ g : N, (g : N ⧸ C') ∈ S1 → ∀ d ∈ D2, g * d = d * g
  triv2 : ∀ g : N, (g : N ⧸ C') ∈ S2 → ∀ d ∈ D1, g * d = d * g
  fpf1 : ∃ g1 : N, (g1 : N ⧸ C') ∈ S1 ∧ ∀ d ∈ D1, ∃ d' ∈ D1, g1 * d' * g1⁻¹ * d'⁻¹ = d
  z2_mem : z2 ∈ S2
  z2_cube : z2 * z2 * z2 = 1
  z2_ne : z2 ≠ 1
  fpf2 : ∀ g : N, (g : N ⧸ C') = z2 → ∀ d ∈ D2, g * d * g⁻¹ = d → d = 1
  z_sq : z * z = 1
  zD : ∀ d ∈ D1, z * d * z⁻¹ ∈ D2
  zD' : ∀ d ∈ D2, z * d * z⁻¹ ∈ D1
  zS12 : ∀ a ∈ S1, (z : N ⧸ C') * a * (z : N ⧸ C')⁻¹ ∈ S2
  zS21 : ∀ a ∈ S2, (z : N ⧸ C') * a * (z : N ⧸ C')⁻¹ ∈ S1

namespace LevelFData

variable [Finite N] {C' : Subgroup N} [C'.Normal] {S1 S2 : Subgroup (N ⧸ C')} {D1 D2 : Subgroup N}
  {z : N} {z2 : N ⧸ C'} (h : LevelFData C' S1 S2 D1 D2 z z2)
include h

theorem map_E : (Ecomm C' S1).map (QuotientGroup.mk' C') = S1 := by
  rw [Ecomm, Subgroup.map_commutator, preimg,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C'), h.perf1]

theorem D1_le_E : D1 ≤ Ecomm C' S1 := by
  intro d hd
  obtain ⟨g1, hg1, hfp⟩ := h.fpf1
  obtain ⟨d', hd', hdd⟩ := hfp d hd
  rw [← hdd]
  exact Subgroup.commutator_mem_commutator (mem_preimg.2 hg1)
    (C_le_preimg S1 (h.D1_le hd'))

theorem E1_eq {e : N} (he : e ∈ preimg C' S1) : ∃ x ∈ Ecomm C' S1, ∃ c ∈ C', e = x * c := by
  have hmem : (e : N ⧸ C') ∈ (Ecomm C' S1).map (QuotientGroup.mk' C') := by
    rw [h.map_E]; exact he
  obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 hmem
  refine ⟨x, hx, x⁻¹ * e, ?_, by group⟩
  rw [← QuotientGroup.eq]
  exact hxe

theorem lift_cent {g' : N} (hg' : (g' : N ⧸ C') = z2) (hg3 : g' * g' * g' = 1) {e : N}
    (he : e ∈ preimg C' S1) : ∃ c ∈ C', g' * (e * c) * g'⁻¹ = e * c := by
  classical
  have hg1 : g' ≠ 1 := by
    intro h1
    apply h.z2_ne
    rw [← hg', h1]
    rfl
  have hord : orderOf g' = 3 := orderOf_eq_prime (by rw [← pow_three'] at hg3; exact hg3) hg1
  have hA : IsPGroup 3 (zpowers g') :=
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  let α : ↥(zpowers g') →* MulAut N := (MulAut.conj : N →* MulAut N).comp (zpowers g').subtype
  let S : Set N := {x | ∃ c ∈ C', x = e * c}
  have hS : ∀ a : ↥(zpowers g'), ∀ x ∈ S, α a x ∈ S := by
    rintro ⟨a, ha⟩ x ⟨c, hc, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    have hpa : ((g' ^ k : N) : N ⧸ C') ∈ S2 := by
      have : ((g' ^ k : N) : N ⧸ C') = z2 ^ k := by
        have := map_zpow (QuotientGroup.mk' C') g' k
        simp [hg']
      rw [this]
      exact S2.zpow_mem h.z2_mem k
    have hcomm : (e : N ⧸ C') * ((g' ^ k : N) : N ⧸ C') =
        ((g' ^ k : N) : N ⧸ C') * (e : N ⧸ C') := h.comm _ he _ hpa
    have hc0 : e⁻¹ * (g' ^ k * e * (g' ^ k)⁻¹) ∈ C' := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hcomm]
      group
    refine ⟨(e⁻¹ * (g' ^ k * e * (g' ^ k)⁻¹)) * (g' ^ k * c * (g' ^ k)⁻¹),
      C'.mul_mem hc0 (Normal.conj_mem inferInstance c hc _), ?_⟩
    show g' ^ k * (e * c) * (g' ^ k)⁻¹ = _
    group
  have hcard : ¬ 3 ∣ Nat.card S := by
    have : Nat.card S = Nat.card C' :=
      Nat.card_congr
        { toFun := fun x => ⟨e⁻¹ * x.1, by
            obtain ⟨c, hc, hx⟩ := x.2
            rw [hx]
            simpa using hc⟩
          invFun := fun c => ⟨e * c.1, c.1, c.2, rfl⟩
          left_inv := fun x => by
            apply Subtype.ext
            simp
          right_inv := fun c => by
            apply Subtype.ext
            simp }
    rw [this]
    exact h.card_C
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, ⟨c, hc, rfl⟩, hfix⟩ :=
    CFSG.Semidihedral.Principal.CoprimeFixedPoint.exists_fixed_of_invariant 3 hA α S hS hcard
  have := hfix ⟨g', mem_zpowers g'⟩
  exact ⟨c, hc, by simpa [α, MulAut.conj_apply] using this⟩

theorem exists_cube_lift : ∃ g' : N, (g' : N ⧸ C') = z2 ∧ g' * g' * g' = 1 := by
  obtain ⟨g0, hg0⟩ := QuotientGroup.mk_surjective z2
  have hu : g0 ^ 3 ∈ C' := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hg0, pow_three']
    exact h.z2_cube
  set m := orderOf (g0 ^ 3) with hm
  have hm3 : ¬ 3 ∣ m := fun hd => h.card_C (hd.trans (Subgroup.orderOf_dvd_natCard C' hu))
  obtain ⟨a, ha⟩ : ∃ a, m = 3 * a + 1 ∨ m = 3 * a + 2 := ⟨m / 3, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, m * m = 3 * r + 1 := by
    rcases ha with ha | ha
    · exact ⟨3 * a * a + 2 * a, by rw [ha]; ring⟩
    · exact ⟨3 * a * a + 4 * a + 1, by rw [ha]; ring⟩
  have hz3 : z2 ^ 3 = 1 := by rw [pow_three']; exact h.z2_cube
  refine ⟨g0 ^ (m * m), ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, hg0, hr, pow_succ, pow_mul, hz3, one_pow, one_mul]
  · rw [← pow_three']
    calc (g0 ^ (m * m)) ^ 3 = (g0 ^ 3) ^ (m * m) := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((g0 ^ 3) ^ m) ^ m := pow_mul _ _ _
      _ = 1 := by rw [hm, pow_orderOf_eq_one, one_pow]

theorem D2_comm : ∀ a ∈ D2, ∀ b ∈ D2, a * b = b * a :=
  fun a ha b hb => (h.triv1 b (C_le_preimg S1 (h.D2_le hb)) a ha).symm

theorem E1_eq_Q {g' : N} (hg' : (g' : N ⧸ C') = z2) (hg3 : g' * g' * g' = 1) {e : N}
    (he : e ∈ preimg C' S1) :
    ∃ q ∈ preimg C' S1, g' * q * g'⁻¹ = q ∧ ∃ d ∈ D2, e = q * d := by
  obtain ⟨c, hc, hfix⟩ := h.lift_cent hg' hg3 he
  obtain ⟨d1, hd1, d2, hd2, rfl⟩ := h.prod c hc
  have hg2 : (g' : N ⧸ C') ∈ S2 := hg' ▸ h.z2_mem
  have hd1c : g' * d1 * g'⁻¹ = d1 := by
    rw [h.triv2 g' hg2 d1 hd1]
    group
  refine ⟨e * (d1 * d2) * d1⁻¹, ?_, ?_, d2⁻¹, D2.inv_mem hd2, ?_⟩
  · exact (preimg C' S1).mul_mem ((preimg C' S1).mul_mem he (C_le_preimg S1 hc))
      ((preimg C' S1).inv_mem (C_le_preimg S1 (h.D1_le hd1)))
  · calc g' * (e * (d1 * d2) * d1⁻¹) * g'⁻¹
        = (g' * (e * (d1 * d2)) * g'⁻¹) * (g' * d1 * g'⁻¹)⁻¹ := by group
      _ = (e * (d1 * d2)) * d1⁻¹ := by rw [hfix, hd1c]
  · have := h.comm12 d1 hd1 d2 hd2
    calc e = e * (d2 * d1) * d1⁻¹ * d2⁻¹ := by group
      _ = e * (d1 * d2) * d1⁻¹ * d2⁻¹ := by rw [this]

theorem Ecomm_fix {g' : N} (hg' : (g' : N ⧸ C') = z2) (hg3 : g' * g' * g' = 1) :
    ∀ x ∈ Ecomm C' S1, g' * x * g'⁻¹ = x := by
  have hle : Ecomm C' S1 ≤ centralizer ({g'} : Set N) := by
    refine commutator_le.2 fun x hx y hy => ?_
    obtain ⟨q, hq, hqc, d, hd, rfl⟩ := h.E1_eq_Q hg' hg3 hx
    obtain ⟨q', hq', hqc', d', hd', rfl⟩ := h.E1_eq_Q hg' hg3 hy
    have hxb : d * q' = q' * d := (h.triv1 q' (mem_preimg.1 hq') d hd).symm
    have hxx : d * d' = d' * d := h.D2_comm d hd d' hd'
    have hxa : d' * q = q * d' := (h.triv1 q (mem_preimg.1 hq) d' hd').symm
    rw [commutator_mul_central hxb hxx hxa, mem_centralizer_singleton_iff]
    have c1 : Commute q g' := by
      show q * g' = g' * q
      calc q * g' = (g' * q * g'⁻¹) * g' := by rw [hqc]
        _ = g' * q := by group
    have c2 : Commute q' g' := by
      show q' * g' = g' * q'
      calc q' * g' = (g' * q' * g'⁻¹) * g' := by rw [hqc']
        _ = g' * q' := by group
    exact ((c1.mul_left c2).mul_left c1.inv_left).mul_left c2.inv_left |>.eq
  intro x hx
  have := mem_centralizer_singleton_iff.1 (hle hx)
  rw [← this]
  group

theorem inf_D2 {x : N} (hx : x ∈ Ecomm C' S1) (hxD : x ∈ D2) : x = 1 := by
  obtain ⟨g', hg', hg3⟩ := h.exists_cube_lift
  exact h.fpf2 g' hg' x hxD (h.Ecomm_fix hg' hg3 x hx)

theorem inf_C {x : N} (hx : x ∈ Ecomm C' S1) (hxC : x ∈ C') : x ∈ D1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.prod x hxC
  have hb1 : b = 1 := by
    apply h.inf_D2 _ hb
    have := (Ecomm C' S1).mul_mem ((Ecomm C' S1).inv_mem (h.D1_le_E ha)) hx
    simpa using this
  rw [hb1, mul_one]
  exact ha

theorem D1_comm : ∀ a ∈ D1, ∀ b ∈ D1, a * b = b * a :=
  fun a ha b hb => (h.triv2 b (mem_preimg.1 (C_le_preimg S2 (h.D1_le hb))) a ha).symm

theorem D1_le_commE : D1 ≤ ⁅Ecomm C' S1, Ecomm C' S1⁆ := by
  intro d hd
  obtain ⟨g1, hg1, hfp⟩ := h.fpf1
  obtain ⟨d', hd', hdd⟩ := hfp d hd
  obtain ⟨x, hx, c, hc, hgc⟩ := h.E1_eq (mem_preimg.2 hg1)
  obtain ⟨a, ha, b, hb, rfl⟩ := h.prod c hc
  have hcd : (a * b) * d' = d' * (a * b) := by
    calc a * b * d' = a * (b * d') := by group
      _ = a * (d' * b) := by rw [← h.comm12 d' hd' b hb]
      _ = (a * d') * b := by group
      _ = (d' * a) * b := by rw [h.D1_comm a ha d' hd']
      _ = d' * (a * b) := by group
  rw [← hdd]
  have hg : g1 * d' * g1⁻¹ * d'⁻¹ = x * d' * x⁻¹ * d'⁻¹ := by
    rw [hgc]
    calc x * (a * b) * d' * (x * (a * b))⁻¹ * d'⁻¹
        = x * ((a * b) * d' * (a * b)⁻¹) * x⁻¹ * d'⁻¹ := by group
      _ = x * d' * x⁻¹ * d'⁻¹ := by rw [hcd]; group
  rw [hg]
  exact Subgroup.commutator_mem_commutator hx (h.D1_le_E hd')

theorem Eperf : ⁅Ecomm C' S1, Ecomm C' S1⁆ = Ecomm C' S1 := by
  refine le_antisymm (commutator_le_self _) ?_
  intro x hx
  have hmem : (x : N ⧸ C') ∈ (⁅Ecomm C' S1, Ecomm C' S1⁆).map (QuotientGroup.mk' C') := by
    rw [Subgroup.map_commutator, h.map_E, h.perf1]
    have := mem_map_of_mem (QuotientGroup.mk' C') hx
    rwa [h.map_E] at this
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hmem
  have hyE : y ∈ Ecomm C' S1 := commutator_le_self _ hy
  have hc : y⁻¹ * x ∈ C' := by
    rw [← QuotientGroup.eq]
    exact hyx
  have hD : y⁻¹ * x ∈ D1 :=
    h.inf_C ((Ecomm C' S1).mul_mem ((Ecomm C' S1).inv_mem hyE) hx) hc
  have := (⁅Ecomm C' S1, Ecomm C' S1⁆).mul_mem hy (h.D1_le_commE hD)
  simpa using this

theorem card_E : Nat.card (Ecomm C' S1) = Nat.card D1 * Nat.card S1 := by
  let f : Ecomm C' S1 →* N ⧸ C' := (QuotientGroup.mk' C').comp (Ecomm C' S1).subtype
  have hrange : f.range = S1 := by
    show ((QuotientGroup.mk' C').comp (Ecomm C' S1).subtype).range = S1
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact h.map_E
  have hker : Nat.card f.ker = Nat.card D1 := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, h.inf_C x.1.2 ((QuotientGroup.eq_one_iff _).1
          (MonoidHom.mem_ker.1 x.2))⟩
        invFun := fun d => ⟨⟨d.1, h.D1_le_E d.2⟩, MonoidHom.mem_ker.2
          ((QuotientGroup.eq_one_iff _).2 (h.D1_le d.2))⟩
        left_inv := fun x => rfl
        right_inv := fun d => rfl }
  have := Subgroup.card_ker_mul_card_range f
  rw [hrange, hker] at this
  exact this.symm

theorem conj_conj (a : N) : z * (z * a * z⁻¹) * z⁻¹ = a := by
  calc z * (z * a * z⁻¹) * z⁻¹ = (z * z) * a * (z * z)⁻¹ := by group
    _ = a := by rw [h.z_sq]; group

theorem E2_normalizes_E1 {g : N} (hg : g ∈ preimg C' S2) {e : N} (he : e ∈ preimg C' S1) :
    g * e * g⁻¹ ∈ preimg C' S1 := by
  have hc : (e : N ⧸ C') * (g : N ⧸ C') = (g : N ⧸ C') * (e : N ⧸ C') := h.comm _ he _ hg
  rw [mem_preimg, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hc]
  have : (e : N ⧸ C') * (g : N ⧸ C') * (g : N ⧸ C')⁻¹ = (e : N ⧸ C') := by group
  rw [this]
  exact he

theorem E2_normalizes_E {g : N} (hg : g ∈ preimg C' S2) {x : N} (hx : x ∈ Ecomm C' S1) :
    g * x * g⁻¹ ∈ Ecomm C' S1 := by
  have hle : (preimg C' S1).map (MulAut.conj g).toMonoidHom ≤ preimg C' S1 := by
    rintro _ ⟨e, he, rfl⟩
    exact h.E2_normalizes_E1 hg he
  have := Subgroup.commutator_mono hle hle
  rw [← Subgroup.map_commutator] at this
  exact this ⟨x, hx, rfl⟩

theorem conj_mem_E2 {a : N} (ha : a ∈ preimg C' S1) : z * a * z⁻¹ ∈ preimg C' S2 := by
  rw [mem_preimg, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  exact h.zS12 _ (mem_preimg.1 ha)

theorem inf_conj {a : N} (ha : a ∈ Ecomm C' S1) (hz : z * a * z⁻¹ ∈ Ecomm C' S1) : a = 1 := by
  have h2 : (z * a * z⁻¹ : N) ∈ preimg C' S2 := h.conj_mem_E2 (Ecomm_le_preimg C' S1 ha)
  have h1 : (z * a * z⁻¹ : N) ∈ preimg C' S1 := Ecomm_le_preimg C' S1 hz
  have hS : ((z * a * z⁻¹ : N) : N ⧸ C') ∈ S1 ⊓ S2 := ⟨mem_preimg.1 h1, mem_preimg.1 h2⟩
  rw [h.S12, Subgroup.mem_bot] at hS
  have hC : (z * a * z⁻¹ : N) ∈ C' := (QuotientGroup.eq_one_iff _).1 hS
  have hD : (z * a * z⁻¹ : N) ∈ D1 := h.inf_C hz hC
  have hD2 : z * (z * a * z⁻¹) * z⁻¹ ∈ D2 := h.zD _ hD
  rw [h.conj_conj] at hD2
  exact h.inf_D2 ha hD2

theorem comm_conj {a b : N} (ha : a ∈ Ecomm C' S1) (hb : b ∈ Ecomm C' S1) :
    a * (z * b * z⁻¹) = (z * b * z⁻¹) * a := by
  set y : N := z * b * z⁻¹ with hy
  have hyE2 : y ∈ preimg C' S2 := h.conj_mem_E2 (Ecomm_le_preimg C' S1 hb)
  have ha'E2 : z * a * z⁻¹ ∈ preimg C' S2 := h.conj_mem_E2 (Ecomm_le_preimg C' S1 ha)
  have hc1 : a * y * a⁻¹ * y⁻¹ ∈ Ecomm C' S1 := by
    have := (Ecomm C' S1).mul_mem ha (h.E2_normalizes_E hyE2 ((Ecomm C' S1).inv_mem ha))
    convert this using 1
    group
  have hc2 : z * (a * y * a⁻¹ * y⁻¹) * z⁻¹ ∈ Ecomm C' S1 := by
    have e1 : z * (a * y * a⁻¹ * y⁻¹) * z⁻¹ =
        (z * a * z⁻¹) * b * (z * a * z⁻¹)⁻¹ * b⁻¹ := by
      have := h.conj_conj b
      rw [← hy] at this
      calc z * (a * y * a⁻¹ * y⁻¹) * z⁻¹
          = (z * a * z⁻¹) * (z * y * z⁻¹) * (z * a * z⁻¹)⁻¹ * (z * y * z⁻¹)⁻¹ := by group
        _ = (z * a * z⁻¹) * b * (z * a * z⁻¹)⁻¹ * b⁻¹ := by rw [this]
    rw [e1]
    exact (Ecomm C' S1).mul_mem (h.E2_normalizes_E ha'E2 hb) ((Ecomm C' S1).inv_mem hb)
  have h1 := h.inf_conj hc1 hc2
  calc a * y = (a * y * a⁻¹ * y⁻¹) * (y * a) := by group
    _ = y * a := by rw [h1, one_mul]

end LevelFData

theorem levelF [Finite N] {C' : Subgroup N} [C'.Normal] {S1 S2 : Subgroup (N ⧸ C')}
    {D1 D2 : Subgroup N} {z : N} {z2 : N ⧸ C'} (h : LevelFData C' S1 S2 D1 D2 z z2) :
    ⁅Ecomm C' S1, Ecomm C' S1⁆ = Ecomm C' S1 ∧
    (∀ a ∈ Ecomm C' S1, ∀ b ∈ Ecomm C' S1, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a) ∧
    (∀ a ∈ Ecomm C' S1, z * a * z⁻¹ ∈ Ecomm C' S1 → a = 1) ∧
    Nat.card (Ecomm C' S1) = Nat.card D1 * Nat.card S1 :=
  ⟨h.Eperf, fun _ ha _ hb => h.comm_conj ha hb, fun _ ha hz => h.inf_conj ha hz, h.card_E⟩

end LevelF

end CFSG.EvenSporadicStandard.M24Std.DRes
