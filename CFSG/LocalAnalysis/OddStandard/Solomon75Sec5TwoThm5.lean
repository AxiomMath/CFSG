module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataSylow
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Defs

public section

namespace CFSG.OddStandard.Solomon75

namespace Sec5Two

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.ABGLocalTools
  CFSG.OddStandard.Solomon75.AhatData

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X}
  {S : Sylow 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))}

theorem exists_commuting_involutions {K : Type} [Group K] [Finite K] {m : ℕ} (hm : 8 ≤ m)
    (hK : IsDoubleCoverOfAlt K m) :
    ∃ a b : K, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  obtain ⟨u, v, hu, hv, huv, h4⟩ := ahatNoncommutingInvolutions K m hm hK
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hu1 : u ≠ 1 := fun e => huv (by rw [e]; simp)
  set z : K := u * v * (u * v) with hz
  have hz1 : z ≠ 1 := fun e => huv (by
    have h1 : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right e
    rw [mul_inv_rev, huinv, hvinv] at h1
    exact h1.symm)
  have hz2 : z * z = 1 := by
    have : z * z = (u * v) ^ 4 := by
      rw [hz]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this, h4]
  have hzinv : z = v * u * v * u := by
    have h1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    rw [← h1, hz]
    simp only [mul_inv_rev, huinv, hvinv, mul_assoc]
  have huz : u * z = z * u := by
    calc u * z = (u * u) * v * u * v := by rw [hz]; group
      _ = v * u * v := by rw [hu]; group
      _ = v * u * v * (u * u) := by rw [hu]; group
      _ = (v * u * v * u) * u := by group
      _ = z * u := by rw [← hzinv]
  have hzu : u ≠ z := fun e => hu1 (by
    have h1 : v * u * v = 1 := by
      have : u * (v * u * v) = u * 1 := by
        calc u * (v * u * v) = u * v * (u * v) := by group
          _ = u := e.symm
          _ = u * 1 := (mul_one u).symm
      exact mul_left_cancel this
    calc u = v⁻¹ * (v * u * v) * v⁻¹ := by group
      _ = v⁻¹ * v⁻¹ := by rw [h1]; group
      _ = 1 := by rw [hvinv, hv])
  exact ⟨u, z, hu, hz2, huz, hu1, hz1, hzu⟩

theorem two_le_pRank_top_doubleCover {K : Type} [Group K] [Finite K] {m : ℕ} (hm : 8 ≤ m)
    (hK : IsDoubleCoverOfAlt K m) : 2 ≤ Open.pRank 2 (⊤ : Subgroup K) := by
  obtain ⟨a, b, ha, hb, hab, ha1, hb1, hne⟩ := exists_commuting_involutions hm hK
  have hsq : ∀ e ∈ kleinSub a b ha hb hab, e * e = 1 := by
    intro e he
    rcases (mem_kleinSub (ha := ha) (hb := hb) (hab := hab)).1 he with rfl | rfl | rfl | rfl
    · simp
    · exact ha
    · exact hb
    · calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha, hb, one_mul]
  exact SectionRank.le_pRank (by norm_num) le_top (isElemAbelian_of_sq hsq)
    (by rw [card_kleinSub ha hb hab ha1 hb1 hne]; norm_num)

theorem two_le_pRank_comp {H A : Subgroup X} (hn8 : 8 ≤ n) (hA : Sec5Comp X n H A) :
    2 ≤ Open.pRank 2 A := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := two_le_pRank_top_doubleCover hn8 hA.2
  have hN : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥A) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 pPrimeCore_coprime_card
  have h2 : Open.pRank 2 (⊤ : Subgroup (↥A ⧸ pPrimeCore 2 ↥A)) =
      Open.pRank 2 (⊤ : Subgroup ↥A) := SectionRank.pRank_quotient_eq (pPrimeCore 2 ↥A) hN
  have h3 : Open.pRank 2 (⊤ : Subgroup ↥A) ≤ Open.pRank 2 A := by
    have := SectionRank.pRank_le_map (p := 2) (by norm_num) A.subtype A.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  omega

omit [Finite X] in
theorem oddCore_eq (Y : Type*) [Group Y] :
    CFSG.Open.aschbacherThm5OddCore Y = pPrimeCore 2 Y := by
  unfold CFSG.Open.aschbacherThm5OddCore CFSG.pPrimeCore
  congr 1
  ext K
  exact and_congr_right fun _ => Nat.coprime_two_left.symm

omit [Finite X] in
theorem core_eq (D : Subgroup X) : CFSG.Open.aschbacherThm5Core D = pPrimeCoreOf 2 D := by
  unfold CFSG.Open.aschbacherThm5Core pPrimeCoreOf
  rw [oddCore_eq]

@[expose] def bar (D L : Subgroup X) : Subgroup (D ⧸ CFSG.Open.aschbacherThm5OddCore D) :=
  (L.subgroupOf D).map (QuotientGroup.mk' (CFSG.Open.aschbacherThm5OddCore D))

omit [Finite X] in
theorem mem_pPrimeCoreOf_iff' {D : Subgroup X} (x : D) :
    (x : X) ∈ pPrimeCoreOf 2 D ↔ x ∈ pPrimeCore 2 ↥D :=
  Subgroup.mem_map_iff_mem D.subtype_injective

omit [Finite X] in
theorem preimage_bar {D L : Subgroup X} (hLD : L ≤ D) :
    CFSG.Open.aschbacherThm5Preimage D (bar D L) = L ⊔ pPrimeCoreOf 2 D := by
  unfold CFSG.Open.aschbacherThm5Preimage bar
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hLD, ← core_eq]
  rfl

omit [Finite X] in
theorem bar_commute {D L L' : Subgroup X}
    (hc : ∀ a ∈ L, ∀ b ∈ L', a * b * a⁻¹ * b⁻¹ ∈ pPrimeCoreOf 2 D) :
    ∀ x ∈ bar D L, ∀ y ∈ bar D L', x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have h1 : (a * b * a⁻¹ * b⁻¹ : D) ∈ CFSG.Open.aschbacherThm5OddCore D := by
    rw [oddCore_eq, ← mem_pPrimeCoreOf_iff']
    exact hc a ha b hb
  have h3 := (QuotientGroup.eq_one_iff _).mpr h1
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv] at h3
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
  calc (a : D ⧸ CFSG.Open.aschbacherThm5OddCore D) * b =
      (a : D ⧸ CFSG.Open.aschbacherThm5OddCore D) * b *
        (a : D ⧸ CFSG.Open.aschbacherThm5OddCore D)⁻¹ *
        (b : D ⧸ CFSG.Open.aschbacherThm5OddCore D)⁻¹ * (b * a) := by group
    _ = b * a := by rw [h3, one_mul]

omit [Finite X] in
theorem bar_iSup {ι : Type*} {D : Subgroup X} (L : ι → Subgroup X) (hL : ∀ i, L i ≤ D) :
    bar D (⨆ i, L i) = ⨆ i, bar D (L i) := by
  unfold bar
  rw [← Subgroup.map_iSup]
  congr 1
  apply Subgroup.map_injective D.subtype_injective
  rw [Subgroup.map_iSup, Subgroup.map_subgroupOf_eq_of_le (iSup_le hL)]
  simp only [fun i => Subgroup.map_subgroupOf_eq_of_le (hL i)]

omit [Finite X] in
theorem nonempty_quot_mulEquiv_bar {D L : Subgroup X} (hLD : L ≤ D)
    (h1 : pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 D) (h2 : L ⊓ pPrimeCoreOf 2 D ≤ pPrimeCoreOf 2 L) :
    Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* ↥(bar D L)) := by
  let φ : L →* D ⧸ CFSG.Open.aschbacherThm5OddCore D :=
    (QuotientGroup.mk' (CFSG.Open.aschbacherThm5OddCore D)).comp (Subgroup.inclusion hLD)
  have hker : φ.ker = pPrimeCore 2 L := by
    ext m
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, oddCore_eq]
    have e1 : Subgroup.inclusion hLD m ∈ pPrimeCore 2 ↥D ↔ (m : X) ∈ pPrimeCoreOf 2 D :=
      (mem_pPrimeCoreOf_iff' (Subgroup.inclusion hLD m)).symm
    rw [e1, ← mem_pPrimeCoreOf_iff' m]
    constructor
    · intro hm
      exact h2 (Subgroup.mem_inf.mpr ⟨m.2, hm⟩)
    · intro hm
      exact h1 hm
  have hrange : φ.range = bar D L := by
    unfold bar
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))⟩

end Sec5Two

end CFSG.OddStandard.Solomon75
