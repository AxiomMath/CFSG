module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Model
public import CFSG.LocalAnalysis.ComponentClassification.AS81L34Transport
public import CFSG.Sporadic.Co1Patterson.Defs

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec3

theorem exists_conj_mem_Q {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}
    {Zs P T Q B₀ : Subgroup G} {z y : G} (hSz : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y)
    (hz1 : z ≠ 1) : ∃ n ∈ A₁, n * z * n⁻¹ ∈ Q ∧ n * z * n⁻¹ ≠ z := by
  have hS := hSz.setting
  obtain ⟨-, -, hEel, -, hE16, -⟩ := frame_inf_A₁ hS
  have hzZ := hSz.z_mem
  rw [hSz.Zs_eq] at hzZ
  have hzE : z ∈ E ⊓ A₁ := by
    have h2 : z ∈ centerIn (E ⊔ F) := hzZ.2
    rw [← hS.frame.inf_eq_center] at h2
    exact ⟨h2.1, hzZ.1⟩
  have h8 : Nat.card ↥(E ⊓ A₁ ⊓ Q) = 8 := by
    have h := Subgroup.relIndex_mul_card (E ⊓ A₁ ⊓ Q) (E ⊓ A₁)
    rw [inf_of_le_left inf_le_left, hSz.Q_EA, hE16] at h
    omega
  obtain ⟨w, hw, hw1, hwz⟩ : ∃ w ∈ E ⊓ A₁ ⊓ Q, w ≠ 1 ∧ w ≠ z := by
    by_contra hcon
    push Not at hcon
    have hle : E ⊓ A₁ ⊓ Q ≤ zpowers z := fun w hw => by
      by_cases h1 : w = 1
      · rw [h1]
        exact one_mem _
      · rw [hcon w hw h1]
        exact mem_zpowers z
    have hc := Subgroup.card_le_of_le hle
    rw [h8, Nat.card_zpowers] at hc
    have := orderOf_le_of_pow_eq_one (by norm_num) (hEel.2 z hzE)
    omega
  have hodd : Odd (Nat.card (center ↥A₁)) := by
    rw [← card_centerIn, hS.center_A₁, Nat.card_zpowers, hS.order_x]
    decide
  obtain ⟨n, hn, hnz⟩ := exists_conj_eq_of_card_sixteen hS.quasisimple hS.typeA₁ hodd inf_le_right
    hEel hE16 hzE hw.1 hz1 hw1
  exact ⟨n, (mem_inf.mp hn).1, hnz ▸ hw.2, hnz ▸ hwz⟩

theorem notWeaklyClosed_of {X Q₁ : Subgroup G} {z : G} (hzX : z ∈ X)
    (hNC : normalizer (Q₁ : Set G) = centralizer ({z} : Set G)) (hQ₁ : IsPGroup 2 Q₁)
    {n : G} (hnX : n ∈ X) (hnQ : n * z * n⁻¹ ∈ Q₁) (hne : n * z * n⁻¹ ≠ z)
    (h : LargeExtraspecial.S14.PattersonCo1Hyp X ⟨z, hzX⟩) :
    Sporadic.Co1Patterson.NotWeaklyClosed h := by
  set t : X := ⟨z, hzX⟩
  let ι : ↥(centralizer ({t} : Set X)) →* G := X.subtype.comp (centralizer ({t} : Set X)).subtype
  have hι : Function.Injective ι := X.subtype_injective.comp (Subgroup.subtype_injective _)
  have hιC : ∀ c, ι c ∈ centralizer ({z} : Set G) := fun c =>
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mem_centralizer_singleton_iff.mp c.2))
  have hQC : Q₁ ≤ centralizer ({z} : Set G) := hNC ▸ le_normalizer
  have hnorm : (Q₁.comap ι).Normal := ⟨fun q hq c => by
    show ι (c * q * c⁻¹) ∈ Q₁
    rw [map_mul, map_mul, map_inv]
    have hcN : ι c ∈ normalizer (Q₁ : Set G) := hNC ▸ hιC c
    exact (mem_normalizer_iff.mp hcN _).mp hq⟩
  have hnil : Group.IsNilpotent (Q₁.comap ι) := (hQ₁.comap_of_injective ι hι).isNilpotent
  have hF : Q₁.comap ι ≤ timmesfeldFStar ↥(centralizer ({t} : Set X)) :=
    le_sup_of_le_left (le_sSup ⟨hnorm, hnil⟩)
  let g : X := ⟨n, hnX⟩
  have hc : g * t * g⁻¹ ∈ centralizer ({t} : Set X) :=
    mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp (hQC hnQ)))
  exact ⟨g, ⟨⟨g * t * g⁻¹, hc⟩, hF (show ι ⟨g * t * g⁻¹, hc⟩ ∈ Q₁ from hnQ), rfl⟩,
    fun he => hne (congrArg Subtype.val he)⟩

end Sec3

end CFSG.ComponentClassification.AS81
