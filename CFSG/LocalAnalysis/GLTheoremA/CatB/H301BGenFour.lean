module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenIdx

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open
open scoped commutatorElement

section Four

variable {G : Type*} [Group G]

theorem eq_of_central_of_ne_one {R : Subgroup G} (hR : timmesfeldIsExtraspecial ↥R) {x y : G}
    (hx : x ∈ R) (hxc : ∀ r ∈ R, r * x = x * r) (hy : y ∈ R) (hyc : ∀ r ∈ R, r * y = y * r)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  obtain ⟨c, -, hc⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center ↥R)).mp hR.2.2.2
  have hxm : (⟨x, hx⟩ : ↥R) ∈ Subgroup.center ↥R :=
    Subgroup.mem_center_iff.2 fun r => Subtype.ext (hxc r r.2)
  have hym : (⟨y, hy⟩ : ↥R) ∈ Subgroup.center ↥R :=
    Subgroup.mem_center_iff.2 fun r => Subtype.ext (hyc r r.2)
  have h1 : (⟨⟨x, hx⟩, hxm⟩ : Subgroup.center ↥R) = c :=
    hc _ fun h => hx1 (congrArg (fun t : Subgroup.center ↥R => ((t : ↥R) : G)) h)
  have h2 : (⟨⟨y, hy⟩, hym⟩ : Subgroup.center ↥R) = c :=
    hc _ fun h => hy1 (congrArg (fun t : Subgroup.center ↥R => ((t : ↥R) : G)) h)
  exact congrArg (fun t : Subgroup.center ↥R => ((t : ↥R) : G)) (h1.trans h2.symm)

theorem comm_of_mem_normalizer {R₀ : Subgroup G} (hR₀ : timmesfeldIsExtraspecial ↥R₀) {z a : G}
    (hz : z ∈ R₀) (hzc : ∀ r ∈ R₀, r * z = z * r) (hz1 : z ≠ 1)
    (ha : a ∈ Subgroup.normalizer (R₀ : Set G)) : a * z = z * a := by
  have hza : a * z * a⁻¹ ∈ R₀ := (Subgroup.mem_normalizer_iff.1 ha z).1 hz
  have hc : ∀ r ∈ R₀, r * (a * z * a⁻¹) = (a * z * a⁻¹) * r := by
    intro r hr
    have hr' : a⁻¹ * r * a ∈ R₀ := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (R₀ : Set G)).inv_mem ha) r).1 hr
      rwa [inv_inv] at this
    have h := hzc _ hr'
    calc r * (a * z * a⁻¹) = a * ((a⁻¹ * r * a) * z) * a⁻¹ := by group
      _ = a * (z * (a⁻¹ * r * a)) * a⁻¹ := by rw [h]
      _ = (a * z * a⁻¹) * r := by group
  have h1 : a * z * a⁻¹ ≠ 1 := fun h => hz1 (by
    calc z = a⁻¹ * (a * z * a⁻¹) * a := by group
      _ = 1 := by rw [h]; group)
  have := eq_of_central_of_ne_one hR₀ hz hzc hza hc hz1 h1
  calc a * z = (a * z * a⁻¹) * a := by group
    _ = z * a := by rw [← this]

structure TwoCentralData (k : ℕ) (z : G) (R : Subgroup G) : Prop where
  extraspecial : timmesfeldIsExtraspecial ↥R
  card : Nat.card R = 2 ^ (2 * k + 1)
  z_mem : z ∈ R
  z_ne_one : z ≠ 1
  z_central : ∀ p ∈ R, p * z = z * p
  cent_le : ∀ g : G, g * z = z * g → (∀ p ∈ R, p * g = g * p) → g ∈ R
  normalizes : ∀ g : G, g * z = z * g → g ∈ Subgroup.normalizer (R : Set G)
  contains : ∀ F X : Subgroup G, F ≤ Subgroup.centralizer ({z} : Set G) →
    X ≤ Subgroup.centralizer ({z} : Set G) → IsElemAbelian 3 F → Nat.card F = 3 ^ k →
    IsPGroup 2 X → F ≤ Subgroup.normalizer (X : Set G) → X ≤ R

variable [Finite G]

theorem index_four_core {k m : ℕ} {z : G} {R : Subgroup G} (D : TwoCentralData k z R)
    (hm : m + 2 = 2 * k + 1) {B K R₀ R₁ : Subgroup G} {y : G} (hB : IsElemAbelian 3 B)
    (hBc : Nat.card B = 3 ^ k) (hyB : y ∈ B) (hy1 : y ≠ 1) (hR₀ : timmesfeldIsExtraspecial ↥R₀)
    (hR₀c : Nat.card R₀ = 2 ^ m) (hzR₀ : z ∈ R₀) (hzc : ∀ r ∈ R₀, r * z = z * r)
    (hyR₀ : ∀ r ∈ R₀, y * r = r * y) (hKB : K ⊔ B ≤ Subgroup.normalizer (R₀ : Set G))
    (hR₁ : IsPGroup 2 R₁) (hKB₁ : K ⊔ B ≤ Subgroup.normalizer (R₁ : Set G)) (h01 : R₀ < R₁) :
    timmesfeldIsExtraspecial ↥R₁ := by
  have hBA : B ≤ K ⊔ B := le_sup_right
  have hAz : ∀ a ∈ K ⊔ B, a * z = z * a := fun a ha =>
    comm_of_mem_normalizer hR₀ hzR₀ hzc D.z_ne_one (hKB ha)
  have hAc : K ⊔ B ≤ Subgroup.centralizer ({z} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (hAz a ha)
  have hZ : ∀ w ∈ (Subgroup.center ↥R).map R.subtype, w = 1 ∨ w = z := by
    intro w hw
    obtain ⟨hwR, hwc⟩ := mem_center_map_iff.1 hw
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr
        (eq_of_central_of_ne_one D.extraspecial hwR hwc D.z_mem D.z_central hw1 D.z_ne_one)
  have hZR₀ : (Subgroup.center ↥R).map R.subtype ≤ R₀ := fun w hw => by
    rcases hZ w hw with rfl | rfl
    · exact R₀.one_mem
    · exact hzR₀
  have hU : ∀ T : Subgroup G, IsPGroup 2 T → K ⊔ B ≤ Subgroup.normalizer (T : Set G) →
      T ≤ Subgroup.centralizer (((Subgroup.center ↥R).map R.subtype : Subgroup G) : Set G) →
      T ≤ R := by
    intro T hT2 hAT hTZ
    have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (hTZ ht) z
          (mem_center_map_iff.2 ⟨D.z_mem, D.z_central⟩)).symm
    exact D.contains B T (hBA.trans hAc) hTz hB hBc hT2 (hBA.trans hAT)
  have hR₀R : R₀ ≤ R := by
    refine hU R₀ hR₀.1 hKB fun r hr => Subgroup.mem_centralizer_iff.2 fun w hw => ?_
    rcases hZ w hw with rfl | rfl
    · simp
    · exact (hzc r hr).symm
  have hy : Odd (orderOf y) := by
    have h3 : y ^ 3 = 1 := hB.2 y hyB
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3)
  have hnc : ¬ ∀ r ∈ R, y * r = r * y := by
    intro hc
    have hyR : y ∈ R := D.cent_le y (hAz y (hBA hyB)) fun p hp => (hc p hp).symm
    obtain ⟨n, hn⟩ := D.extraspecial.1 (⟨y, hyR⟩ : ↥R)
    have hn' : y ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have h3 : y ^ 3 = 1 := hB.2 y hyB
    have hcop : Nat.Coprime 3 (2 ^ n) := (by norm_num : Nat.Coprime 3 2).pow_right n
    have := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3)
      (orderOf_dvd_of_pow_eq_one hn')
    exact hy1 (orderOf_eq_one_iff.1 this)
  have hidx : Nat.card R = 4 * Nat.card R₀ := by
    rw [D.card, hR₀c, show 2 * k + 1 = m + 2 from hm.symm, pow_add]
    ring
  have hRR : R₁ = R :=
    eq_of_index_four_chain D.extraspecial rfl hZR₀ hR₀R (Or.inl hR₀) hidx hKB
      (fun a ha => D.normalizes a (hAz a ha)) (hBA hyB) hy hyR₀ hnc hU hR₁ hKB₁ h01
  exact hRR ▸ D.extraspecial

end Four

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
