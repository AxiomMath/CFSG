module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Skeleton
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.Solomon75

namespace Sec5Two

open CFSG CFSG.GH74.GLS Subgroup

open scoped commutatorElement

theorem mem_of_central_of_normal_ne_bot {W : Type} [Group W] [Finite W]
    (hQ : IsQuasisimple W) (hc : Nat.card (center W) = 2) {S : Subgroup W} (hS : S.Normal)
    (hne : S ≠ ⊥) {w : W} (hw : w ∈ center W) : w ∈ S := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hS with h | h
  · rw [h]
    exact Subgroup.mem_top _
  · have h1 : Nat.card S ∣ Nat.card (center W) := Subgroup.card_dvd_of_le h
    rw [hc] at h1
    have h2 : Nat.card S ≠ 1 := fun h3 => hne (Subgroup.card_eq_one.mp h3)
    have h3 : Nat.card S = 2 := ((Nat.dvd_prime Nat.prime_two).mp h1).resolve_left h2
    have h4 : S = center W := Subgroup.eq_of_le_of_card_ge h (by rw [hc, h3])
    rw [h4]
    exact hw

theorem mem_of_sq_mem_of_odd_pow {X : Type} [Group X] {N : Subgroup X} {x : X} {m : ℕ}
    (hm : Odd m) (hx : x ^ m = 1) (h2 : x ^ 2 ∈ N) : x ∈ N := by
  obtain ⟨j, rfl⟩ := hm
  have h3 : x = (x ^ 2) ^ (j + 1) := by
    rw [← pow_mul, show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ, hx, one_mul]
  rw [h3]
  exact N.pow_mem h2 _

theorem not_subgroupOf_le_pPrimeCore {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    {D N B : Subgroup X} (hBD : B ≤ D)
    (hB : IsDoubleCoverOfAlt (↥B ⧸ pPrimeCore 2 ↥B) n)
    (hidx : N.relIndex D < n.factorial) :
    ¬ N.subgroupOf B ≤ pPrimeCore 2 ↥B := by
  intro hle
  have h1 : (pPrimeCore 2 ↥B).index ∣ (N.subgroupOf B).index := Subgroup.index_dvd_of_le hle
  have hne : (N.subgroupOf B).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : (pPrimeCore 2 ↥B).index ≤ (N.subgroupOf B).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h1
  have h3 : (N.subgroupOf B).index = N.relIndex B := rfl
  have h4 : N.relIndex B ≤ N.relIndex D :=
    Subgroup.relIndex_le_of_le_right hBD Subgroup.index_ne_zero_of_finite
  have h5 : (pPrimeCore 2 ↥B).index = n.factorial := by
    rw [Subgroup.index, ← natCard_eq_factorial_of_isDoubleCoverOfAlt hn hB]
  omega

theorem mem_of_central_mod_core {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    {D N B : Subgroup X} (hBD : B ≤ D) (hND : N ≤ D)
    (hNn : ∀ d ∈ D, ∀ c ∈ N, d * c * d⁻¹ ∈ N)
    (hB : IsDoubleCoverOfAlt (↥B ⧸ pPrimeCore 2 ↥B) n)
    (hidx : N.relIndex D < n.factorial)
    {u : X} (huB : u ∈ B) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (huZ : ∀ b ∈ B, ⁅b, u⁆ ∈ pPrimeCoreOf 2 B) : u ∈ N := by
  have _ : N ≤ D ∧ u ≠ 1 := ⟨hND, hu1⟩
  let θ : ↥B →* (↥B ⧸ pPrimeCore 2 ↥B) := QuotientGroup.mk' (pPrimeCore 2 ↥B)
  have hθs : Function.Surjective θ := QuotientGroup.mk'_surjective _
  have hθk : θ.ker = pPrimeCore 2 ↥B := QuotientGroup.ker_mk' _
  let K : Subgroup ↥B := N.subgroupOf B
  have hKn : K.Normal := ⟨fun k hk g => hNn g (hBD g.2) k hk⟩
  let u' : ↥B := ⟨u, huB⟩
  have hcen : θ u' ∈ center (↥B ⧸ pPrimeCore 2 ↥B) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨b, rfl⟩ := hθs w
    obtain ⟨x, hx, hxe⟩ := huZ b b.2
    have hcomm : ⁅b, u'⁆ = x := Subtype.ext (by simpa [commutatorElement_def] using hxe.symm)
    have h1 : θ ⁅b, u'⁆ = 1 := by
      rw [hcomm]
      exact (QuotientGroup.eq_one_iff x).mpr hx
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hne : K.map θ ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff, hθk] at h
    exact not_subgroupOf_le_pPrimeCore hn hBD hB hidx h
  have hmem : θ u' ∈ K.map θ :=
    mem_of_central_of_normal_ne_bot hB.1 hB.2.1 (hKn.map θ hθs) hne hcen
  obtain ⟨k, hk, hke⟩ := hmem
  have ho : k⁻¹ * u' ∈ pPrimeCore 2 ↥B := by
    rw [← hθk, MonoidHom.mem_ker, map_mul, map_inv, hke, inv_mul_cancel]
  have hoX : ((k⁻¹ * u' : ↥B) : X) ∈ oddCoreOf B := ⟨_, ho, rfl⟩
  have hom := orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard (oddCoreOf B) hoX)
  have hkN : (k : X) ∈ N := hk
  have hkiN : (k : X)⁻¹ ∈ N := N.inv_mem hkN
  have ho2 : ((k⁻¹ * u' : ↥B) : X) ^ 2 ∈ N := by
    have h1 : ((k⁻¹ * u' : ↥B) : X) ^ 2 =
        (k : X)⁻¹ * (u * (k : X)⁻¹ * u⁻¹) * (u * u) := by
      show ((k : X)⁻¹ * u) ^ 2 = _
      rw [sq]
      group
    rw [h1, hu2, mul_one]
    exact N.mul_mem hkiN (hNn u (hBD huB) _ hkiN)
  have hoN : ((k⁻¹ * u' : ↥B) : X) ∈ N :=
    mem_of_sq_mem_of_odd_pow (odd_card_oddCoreOf B) hom ho2
  have hu : u = (k : X) * ((k⁻¹ * u' : ↥B) : X) := by
    show u = (k : X) * ((k : X)⁻¹ * u)
    rw [mul_inv_cancel_left]
  rw [hu]
  exact N.mul_mem hkN hoN

theorem relIndex_eq_relIndex_of_mul_normal {X : Type} [Group X] {A N D : Subgroup X}
    (hAD : A ≤ D) (hND : N ≤ D)
    (hNn : ∀ d ∈ D, ∀ c ∈ N, d * c * d⁻¹ ∈ N)
    (hDAN : ∀ d ∈ D, ∃ a ∈ A, ∃ c ∈ N, d = a * c) : N.relIndex D = N.relIndex A := by
  have hnorm : (N.subgroupOf D).Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    simpa using hNn g g.2 c hc
  have hsup : A.subgroupOf D ⊔ N.subgroupOf D = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨a, ha, c, hc, hgac⟩ := hDAN g g.2
    have hg : g = ⟨a, hAD ha⟩ * ⟨c, hND hc⟩ := Subtype.ext hgac
    rw [hg]
    exact Subgroup.mul_mem_sup (by simpa [Subgroup.mem_subgroupOf] using ha)
      (by simpa [Subgroup.mem_subgroupOf] using hc)
  calc N.relIndex D = (N.subgroupOf D).relIndex (D.subgroupOf D) :=
        (Subgroup.relIndex_subgroupOf le_rfl).symm
    _ = (N.subgroupOf D).relIndex ⊤ := by rw [Subgroup.subgroupOf_self]
    _ = (N.subgroupOf D).relIndex (A.subgroupOf D ⊔ N.subgroupOf D) := by rw [hsup]
    _ = (N.subgroupOf D).relIndex (A.subgroupOf D) := Subgroup.relIndex_sup_right _ _
    _ = N.relIndex A := Subgroup.relIndex_subgroupOf hAD

theorem card_oddCoreOf_lt_card_inf {X : Type} [Group X] [Finite X] {A N : Subgroup X}
    (hON : pPrimeCoreOf 2 A ≤ N) {z : X} (hzA : z ∈ A) (hzN : z ∈ N) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) : Nat.card (oddCoreOf A) < Nat.card ↥(N ⊓ A) := by
  have hle : oddCoreOf A ≤ N ⊓ A := le_inf hON (oddCoreOf_le A)
  have hzn : z ∉ oddCoreOf A := by
    intro hz
    have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2)
    have h2 : orderOf z ∣ Nat.card (oddCoreOf A) := (oddCoreOf A).orderOf_dvd_natCard hz
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact hz1 (orderOf_eq_one_iff.mp h)
    · rw [h] at h2
      obtain ⟨k, hk⟩ := odd_card_oddCoreOf A
      obtain ⟨m, hm⟩ := h2
      omega
  by_contra hlt
  have heq := Subgroup.eq_of_le_of_card_ge hle (not_lt.mp hlt)
  apply hzn
  rw [heq]
  exact ⟨hzN, hzA⟩

theorem relIndex_lt_factorial {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    {A N D : Subgroup X} (hAD : A ≤ D) (hND : N ≤ D)
    (hNn : ∀ d ∈ D, ∀ c ∈ N, d * c * d⁻¹ ∈ N)
    (hDAN : ∀ d ∈ D, ∃ a ∈ A, ∃ c ∈ N, d = a * c)
    (hA : IsDoubleCoverOfAlt (↥A ⧸ pPrimeCore 2 ↥A) n)
    (hON : pPrimeCoreOf 2 A ≤ N) {z : X} (hzA : z ∈ A) (hzN : z ∈ N) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) : N.relIndex D < n.factorial := by
  have h1 : N.relIndex D = N.relIndex A :=
    relIndex_eq_relIndex_of_mul_normal hAD hND hNn hDAN
  have h2 : Nat.card (oddCoreOf A) < Nat.card ↥(N ⊓ A) :=
    card_oddCoreOf_lt_card_inf hON hzA hzN hz2 hz1
  have h3 : N.relIndex A * Nat.card ↥(N ⊓ A) = Nat.card A := Subgroup.relIndex_mul_card N A
  have h4 : Nat.card A = n.factorial * Nat.card (oddCoreOf A) := by
    have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥A)
    have e2 : Nat.card (oddCoreOf A) = Nat.card (pPrimeCore 2 ↥A) :=
      Subgroup.card_map_of_injective A.subtype_injective
    rw [e1, e2, natCard_eq_factorial_of_isDoubleCoverOfAlt hn hA]
  have hpos : 0 < n.factorial := Nat.factorial_pos n
  rw [h1]
  by_contra hge
  have h5 : n.factorial * Nat.card ↥(N ⊓ A) ≤ N.relIndex A * Nat.card ↥(N ⊓ A) :=
    Nat.mul_le_mul_right _ (not_lt.mp hge)
  have h6 : n.factorial * Nat.card (oddCoreOf A) < n.factorial * Nat.card ↥(N ⊓ A) :=
    Nat.mul_lt_mul_of_pos_left h2 hpos
  omega

end Sec5Two

end CFSG.OddStandard.Solomon75
