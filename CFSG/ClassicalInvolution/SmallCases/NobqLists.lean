module

public import Mathlib
public import CFSG.ClassicalInvolution.SmallCases.NobqCriteria
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Sporadic.Schreier (centralizerIn mem_centralizerIn map_centralizer_subtype)

variable {M : Type*} [Group M]

@[expose] def cqCheck [DecidableEq M] (r : M) (L : List M) : Bool :=
  L.all fun c => decide (c * c ≠ r) || L.any fun g =>
    decide ((c * (g * c * g⁻¹)) * (c * (g * c * g⁻¹)) = 1 ∧ c * (g * c * g⁻¹) ≠ 1 ∧
      c * (g * c * g⁻¹) ≠ r)

theorem mem_centralizerIn_of_mem_centralizer {H : Subgroup M} {t c : H}
    (hc : c ∈ Subgroup.centralizer ({t} : Set H)) : (c : M) ∈ centralizerIn H (t : M) := by
  rw [← map_centralizer_subtype H t]
  exact ⟨c, hc, rfl⟩

theorem not_uniqueInvNormal_of_witness_ambient (H : Subgroup M) (r : M) (hr : r ∈ H)
    (K : Subgroup M) (hK : centralizerIn H r = K)
    (hw : ∀ c ∈ K, c * c = r → ∃ g ∈ K, (c * (g * c * g⁻¹)) * (c * (g * c * g⁻¹)) = 1 ∧
      c * (g * c * g⁻¹) ≠ 1 ∧ c * (g * c * g⁻¹) ≠ r)
    (N : Subgroup H) : ¬ UniqueInvNormal (⟨r, hr⟩ : H) N := by
  refine not_uniqueInvNormal_of_witness fun c hc hct => ?_
  have hcK : (c : M) ∈ K := by
    rw [← hK]
    exact mem_centralizerIn_of_mem_centralizer hc
  obtain ⟨g, hgK, h1, h2, h3⟩ := hw c hcK (by rw [← Subgroup.coe_mul, hct])
  obtain ⟨hgH, hgc⟩ := mem_centralizerIn.1 (hK ▸ hgK)
  refine ⟨⟨g, hgH⟩, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hgc
  · apply Subtype.ext
    simpa using h1
  · intro h
    exact h2 (by simpa using congrArg Subtype.val h)
  · intro h
    exact h3 (by simpa using congrArg Subtype.val h)

theorem not_uniqueInvNormal_of_witness_sylow_ambient (H : Subgroup M) (r : M) (hr : r ∈ H)
    (K S : Subgroup M) [Finite K] (hK : centralizerIn H r = K) (hS : IsPGroup 2 S)
    (hidx : ¬ 2 ∣ (S.subgroupOf K).index)
    (hw : ∀ c ∈ S, c * c = r → ∃ g ∈ K, (c * (g * c * g⁻¹)) * (c * (g * c * g⁻¹)) = 1 ∧
      c * (g * c * g⁻¹) ≠ 1 ∧ c * (g * c * g⁻¹) ≠ r)
    (N : Subgroup H) : ¬ UniqueInvNormal (⟨r, hr⟩ : H) N := by
  intro h
  have hKH : ∀ k ∈ K, k ∈ H ∧ k * r = r * k := fun k hk =>
    mem_centralizerIn.mp (hK ▸ hk)
  have hlift : ∀ k ∈ K, ∃ k' : H, (k' : M) = k ∧
      k' ∈ Subgroup.centralizer ({(⟨r, hr⟩ : H)} : Set H) := fun k hk =>
    ⟨⟨k, (hKH k hk).1⟩, rfl, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (hKH k hk).2⟩
  obtain ⟨s, hsN, hst, hs4⟩ := h.exists_sq_eq
  have hsK : (s : M) ∈ K := by
    rw [← hK]
    exact mem_centralizerIn_of_mem_centralizer (h.le_centralizer hsN)
  have hSp : IsPGroup 2 (S.subgroupOf K) := hS.comap_of_injective K.subtype K.subtype_injective
  have hu : (⟨(s : M), hsK⟩ : K) ^ (2 ^ 2) = 1 := by
    apply Subtype.ext
    have h4 : orderOf (s : M) = 4 := by rw [← hs4]; exact Subgroup.orderOf_coe s
    simpa [h4] using pow_orderOf_eq_one (s : M)
  obtain ⟨c₀, hc₀⟩ := exists_conj_mem_of_twoPow (S.subgroupOf K) hSp hidx hu
  obtain ⟨c₁, hc₁e, hc₁⟩ := hlift (c₀ : M) c₀.2
  have hs' : c₁ * s * c₁⁻¹ ∈ N := h.conj_mem c₁ hc₁ s hsN
  have hs'S : (((c₁ * s * c₁⁻¹ : H)) : M) ∈ S := by
    have := Subgroup.mem_subgroupOf.1 hc₀
    simpa [hc₁e] using this
  have hs'2 : (c₁ * s * c₁⁻¹) * (c₁ * s * c₁⁻¹) = (⟨r, hr⟩ : H) := by
    have hct : c₁ * (⟨r, hr⟩ : H) * c₁⁻¹ = (⟨r, hr⟩ : H) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc₁
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    calc (c₁ * s * c₁⁻¹) * (c₁ * s * c₁⁻¹) = c₁ * (s * s) * c₁⁻¹ := by group
      _ = (⟨r, hr⟩ : H) := by rw [hst, hct]
  obtain ⟨g, hgK, h1, h2, h3⟩ := hw _ hs'S (by rw [← Subgroup.coe_mul, hs'2])
  obtain ⟨g', hg'e, hg'c⟩ := hlift g hgK
  set s' : H := c₁ * s * c₁⁻¹ with hs'def
  have hx : s' * (g' * s' * g'⁻¹) ∈ N := N.mul_mem hs' (h.conj_mem g' hg'c s' hs')
  have hxM : ((s' * (g' * s' * g'⁻¹) : H) : M) = (s' : M) * (g * (s' : M) * g⁻¹) := by
    simp [hg'e]
  have hx2 : (s' * (g' * s' * g'⁻¹)) * (s' * (g' * s' * g'⁻¹)) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hxM]
    simpa using h1
  have hx1 : s' * (g' * s' * g'⁻¹) ≠ 1 := fun h' => h2 (by
    rw [← hxM, h']
    rfl)
  have hord : orderOf (s' * (g' * s' * g'⁻¹)) = 2 := orderOf_eq_prime (by rwa [pow_two]) hx1
  have := h.eq_of_orderOf_eq_two _ hx hord
  apply h3
  rw [← hxM, this]

theorem not_uniqueInvNormal_of_cqCheck [DecidableEq M] (H : Subgroup M) (r : M) (hr : r ∈ H)
    (L : List M) (hL : ∀ g, g ∈ L ↔ g ∈ centralizerIn H r) (h : cqCheck r L = true)
    (N : Subgroup H) : ¬ UniqueInvNormal (⟨r, hr⟩ : H) N := by
  refine not_uniqueInvNormal_of_witness_ambient H r hr (centralizerIn H r) rfl ?_ N
  intro c hc hcr
  have hcL : c ∈ L := (hL _).2 hc
  simp only [cqCheck, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true] at h
  rcases h c hcL with hne | ⟨g, hgL, h1, h2, h3⟩
  · exact absurd hcr hne
  · exact ⟨g, (hL g).1 hgL, h1, h2, h3⟩

theorem not_uniqueInvNormal_of_card_eq_two_mul (H : Subgroup M) (r : M) (hr : r ∈ H)
    (N₀ : Subgroup M)
    (hN₀ : N₀ ≤ centralizerIn H r) [Finite (centralizerIn H r)]
    (hcard : Nat.card (centralizerIn H r) = 2 * Nat.card N₀) (hrN : r ∉ N₀)
    (N : Subgroup H) : ¬ UniqueInvNormal (⟨r, hr⟩ : H) N := by
  refine not_uniqueInvNormal_of_no_square fun c hc hct => hrN ?_
  have hcK : (c : M) ∈ centralizerIn H r := mem_centralizerIn_of_mem_centralizer hc
  set K := centralizerIn H r with hK
  have : Finite N₀ := Finite.of_injective (Subgroup.inclusion hN₀) (Subgroup.inclusion_injective _)
  have hpos : 0 < Nat.card N₀ := Nat.card_pos
  have hidx : (N₀.subgroupOf K).index = 2 := by
    have h := Subgroup.card_mul_index (N₀.subgroupOf K)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀).toEquiv, hcard] at h
    have h2 : Nat.card N₀ * (N₀.subgroupOf K).index = Nat.card N₀ * 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have hsq := Subgroup.mul_self_mem_of_index_two hidx ⟨(c : M), hcK⟩
  have hsq' : (c : M) * (c : M) ∈ N₀ := by simpa [Subgroup.mem_subgroupOf] using hsq
  rwa [← Subgroup.coe_mul, hct] at hsq'

theorem not_uniqueInvNormal_of_no_orderOf_eq_four (H : Subgroup M) (r : M) (hr : r ∈ H)
    (hK : ∀ x ∈ centralizerIn H r, orderOf x ≠ 4) (N : Subgroup H) :
    ¬ UniqueInvNormal (⟨r, hr⟩ : H) N := by
  intro h
  obtain ⟨s, hsN, hs4⟩ := h.exists_orderOf_eq_four
  refine hK (s : M) (mem_centralizerIn_of_mem_centralizer (h.le_centralizer hsN)) ?_
  rw [← hs4]
  exact Subgroup.orderOf_coe s

theorem noUniqueInvNormal_of_reps [DecidableEq M] (H : Subgroup M) (reps : List M)
    (hreps : ∀ r ∈ reps, r ∈ H)
    (hcov : ∀ u ∈ H, orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ H, u = c * r * c⁻¹)
    (hgood : ∀ r ∈ reps, ∀ hr : r ∈ H, ∀ N : Subgroup H, ¬ UniqueInvNormal (⟨r, hr⟩ : H) N) :
    NoUniqueInvNormal H := by
  refine NoUniqueInvNormal.of_conj_reps {x : H | ∃ r ∈ reps, (x : M) = r} ?_ ?_
  · intro u hu
    obtain ⟨r, hr, c, hc, hur⟩ := hcov u u.2 (by rw [← Subgroup.orderOf_coe] at hu; exact hu)
    refine ⟨⟨r, hreps r hr⟩, ⟨r, hr, rfl⟩, ⟨c, hc⟩, ?_⟩
    apply Subtype.ext
    simpa using hur
  · rintro s ⟨r, hr, hsr⟩ - N
    have hs : s = ⟨r, hreps r hr⟩ := Subtype.ext hsr
    subst hs
    exact hgood r hr _ N

end CFSG.ClassicalInvolution.Nobq
