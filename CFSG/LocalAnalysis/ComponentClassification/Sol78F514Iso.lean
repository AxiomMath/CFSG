module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Zs

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5

variable {G : Type} [Group G] [Finite G]

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem conj_z_ne_t_of_commute {a x : G} (haR : a ∈ S ⊓ L) (ha1 : a ≠ 1)
    (hxa : x * a = a * x) : x⁻¹ * z * x ≠ t := by
  intro hx
  set g := x * s⁻¹ with hg
  have hgz : g ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : g⁻¹ * z * g = z := by
      rw [hg, show (x * s⁻¹)⁻¹ * z * (x * s⁻¹) = s * (x⁻¹ * z * x) * s⁻¹ by group, hx,
        H.conj_s_t]
    calc g * z = g * (g⁻¹ * z * g) := by rw [h1]
      _ = z * g := by group
  have hgN := H.sec5.centralizer_le_normalizer hgz
  have h1 : g⁻¹ * a * g = s * a * s⁻¹ := by
    have hxa' : x⁻¹ * a * x = a := by
      calc x⁻¹ * a * x = x⁻¹ * (x * a) := by rw [mul_assoc, ← hxa]
        _ = a := by group
    rw [hg, show (x * s⁻¹)⁻¹ * a * (x * s⁻¹) = s * (x⁻¹ * a * x) * s⁻¹ by group, hxa']
  have h2 : s * a * s⁻¹ ∈ S ⊓ L := by
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp H.s_mem_normalizer a).mp (mem_inf.mp haR).1, ?_⟩
    rw [← h1]
    exact Foote5.conj_mem_of_mem_normalizer hgN (mem_inf.mp haR).2
  have h4 : s * a * s⁻¹ ∈ S ⊓ L ⊓ conjugate (S ⊓ L) s := mem_inf.mpr ⟨h2, H.conj_s_mem_Rs haR⟩
  rw [H.R_inf_Rs, mem_bot] at h4
  apply ha1
  calc a = s⁻¹ * (s * a * s⁻¹) * s := by group
    _ = 1 := by rw [h4]; group

theorem isolated_of_strongly_closed {a : G} (haR : a ∈ S ⊓ L) (ha1 : a ≠ 1) {P : Subgroup G}
    (hP : IsSylowOf 2 P (centralizer ({z * t} : Set G) ⊓ centralizer ({a} : Set G)))
    (hcl : ∀ x ∈ centralizer ({z * t} : Set G) ⊓ centralizer ({a} : Set G),
      x⁻¹ * z * x ∈ P → x⁻¹ * z * x = z ∨ x⁻¹ * z * x = t)
    {x : G} (hx : x ∈ centralizer ({z * t} : Set G) ⊓ centralizer ({a} : Set G))
    (hc : x * z * x⁻¹ * z = z * (x * z * x⁻¹)) : x * z * x⁻¹ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := centralizer ({z * t} : Set G) ⊓ centralizer ({a} : Set G) with hX
  have hza : a * z = z * a := H.sec5.zS a (mem_inf.mp haR).1
  have hzX : z ∈ X := mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr
    (H.commute_d_of_mem_S H.sec5.zS_mem), mem_centralizer_singleton_iff.mpr hza.symm⟩
  obtain ⟨w, hw⟩ : ∃ w, w = x * z * x⁻¹ := ⟨_, rfl⟩
  rw [← hw] at hc ⊢
  have hwX : w ∈ X := by rw [hw]; exact mul_mem (mul_mem hx hzX) (inv_mem hx)
  have hw2 : w * w = 1 := by
    rw [hw, show x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ by group, H.mul_self_z]; group
  have h4 : (z * w) ^ 4 = 1 := by
    have h2 : z * w * (z * w) = 1 := by
      calc z * w * (z * w) = z * (w * z) * w := by rw [mul_assoc, mul_assoc, mul_assoc]
        _ = z * (z * w) * w := by rw [hc]
        _ = 1 := by rw [← mul_assoc, H.mul_self_z, one_mul, hw2]
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq (z * w), h2, one_pow]
  have hcX : closure ({z, w} : Set G) ≤ X := by
    rw [closure_le]
    intro c hc'
    rcases hc' with rfl | rfl
    · exact hzX
    · exact hwX
  obtain ⟨k, hkX, hk⟩ := FooteLit.exists_conj_le_of_isSylowOf hP hcX
    (isPGroup_closure_pair H.mul_self_z hw2 h4)
  have hka : k * a = a * k := (mem_centralizer_singleton_iff.mp (mem_inf.mp hkX).2)
  have hk1 : k⁻¹ * z * k = z := by
    rcases hcl k hkX (hk z (subset_closure (by simp))) with h1 | h1
    · exact h1
    · exact absurd h1 (H.conj_z_ne_t_of_commute haR ha1 hka)
  have hxk : x⁻¹ * k ∈ X := mul_mem (inv_mem hx) hkX
  have hxka : x⁻¹ * k * a = a * (x⁻¹ * k) :=
    (mem_centralizer_singleton_iff.mp (mem_inf.mp hxk).2)
  have hk2 : (x⁻¹ * k)⁻¹ * z * (x⁻¹ * k) = z := by
    have hmem : (x⁻¹ * k)⁻¹ * z * (x⁻¹ * k) ∈ P := by
      have := hk w (subset_closure (by simp))
      rwa [hw, show k⁻¹ * (x * z * x⁻¹) * k = (x⁻¹ * k)⁻¹ * z * (x⁻¹ * k) by group] at this
    rcases hcl _ hxk hmem with h1 | h1
    · exact h1
    · exact absurd h1 (H.conj_z_ne_t_of_commute haR ha1 hxka)
  calc w = k * ((x⁻¹ * k)⁻¹ * z * (x⁻¹ * k)) * k⁻¹ := by rw [hw]; group
    _ = k * z * k⁻¹ := by rw [hk2]
    _ = k * (k⁻¹ * z * k) * k⁻¹ := by rw [hk1]
    _ = z := by group

theorem exists_odd_mul_centralizer {a : G} (haR : a ∈ S ⊓ L) (ha1 : a ≠ 1) {P : Subgroup G}
    (hP : IsSylowOf 2 P (centralizer ({z * t} : Set G) ⊓ centralizer ({a} : Set G)))
    (hcl : ∀ x ∈ centralizer ({z * t} : Set G) ⊓ centralizer ({a} : Set G),
      x⁻¹ * z * x ∈ P → x⁻¹ * z * x = z ∨ x⁻¹ * z * x = t) :
    ∃ N : Subgroup G, N ≤ centralizer ({z * t} : Set G) ⊓ centralizer ({a} : Set G) ∧
      (∀ c ∈ centralizer ({z * t} : Set G) ⊓ centralizer ({a} : Set G), ∀ n ∈ N,
        c * n * c⁻¹ ∈ N) ∧ Odd (Nat.card N) ∧
      ∀ x ∈ centralizer ({z * t} : Set G) ⊓ centralizer ({a} : Set G),
        ∃ k ∈ N, k⁻¹ * x * z = z * (k⁻¹ * x) := by
  set X := centralizer ({z * t} : Set G) ⊓ centralizer ({a} : Set G) with hX
  have hza : a * z = z * a := H.sec5.zS a (mem_inf.mp haR).1
  have hzX : z ∈ X := mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr
    (H.commute_d_of_mem_S H.sec5.zS_mem), mem_centralizer_singleton_iff.mpr hza.symm⟩
  let : Fintype X := Fintype.ofFinite _
  set z' : X := ⟨z, hzX⟩ with hz'
  have hz1 : z' ≠ 1 := fun h1 => H.z_ne_one (congrArg Subtype.val h1)
  have hz2 : z' * z' = 1 := Subtype.ext H.mul_self_z
  have hiso : ∀ g : X, g * z' * g⁻¹ * z' = z' * (g * z' * g⁻¹) → g * z' * g⁻¹ = z' :=
    fun g hg => Subtype.ext (H.isolated_of_strongly_closed haR ha1 hP hcl g.2
      (congrArg Subtype.val hg))
  obtain ⟨N, hNn, hNodd, hN⟩ := ZStar.glauberman_zStar X z' hz1 hz2 hiso
  have hcover := exists_mem_mul_centralizer hz2 hNodd hN
  refine ⟨N.map X.subtype, map_subtype_le N, ?_, ?_, fun x hx => ?_⟩
  · rintro c hc _ ⟨n, hn, rfl⟩
    exact ⟨⟨c, hc⟩ * n * ⟨c, hc⟩⁻¹, hNn.conj_mem n hn _, rfl⟩
  · rwa [card_map_of_injective X.subtype_injective]
  · obtain ⟨k, hk, hkc⟩ := hcover ⟨x, hx⟩
    exact ⟨k, ⟨k, hk, rfl⟩, congrArg Subtype.val (mem_centralizer_singleton_iff.mp hkc)⟩

end Hyp

end CFSG.ComponentClassification.Sol78.F514
