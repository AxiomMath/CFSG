module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1CfgB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def y7aO (X V : Subgroup G) (t : G) : Set G :=
  {w | ∃ x ∈ X, (x * t * x⁻¹)⁻¹ * w ∈ V}

theorem y7a_O_t (X V : Subgroup G) (t : G) : t ∈ y7aO X V t := by
  refine ⟨1, X.one_mem, ?_⟩
  simp

theorem y7a_O_V {X V : Subgroup G} {t w v : G} (hw : w ∈ y7aO X V t) (hv : v ∈ V) :
    w * v ∈ y7aO X V t := by
  obtain ⟨x, hxX, hx⟩ := hw
  refine ⟨x, hxX, ?_⟩
  have h : (x * t * x⁻¹)⁻¹ * (w * v) = ((x * t * x⁻¹)⁻¹ * w) * v := by group
  rw [h]
  exact V.mul_mem hx hv

theorem y7a_O_V_iff {X V : Subgroup G} {t w v : G} (hv : v ∈ V) :
    w * v ∈ y7aO X V t ↔ w ∈ y7aO X V t := by
  constructor
  · intro h
    have := y7a_O_V (X := X) (V := V) (t := t) h (V.inv_mem hv)
    simpa using this
  · exact fun h => y7a_O_V h hv

theorem y7a_O_conj {X V : Subgroup G} {t : G} (hXV : X ≤ normalizer (V : Set G)) {x w : G}
    (hx : x ∈ X) (hw : w ∈ y7aO X V t) : x * w * x⁻¹ ∈ y7aO X V t := by
  obtain ⟨y, hyX, hy⟩ := hw
  refine ⟨x * y, X.mul_mem hx hyX, ?_⟩
  have hxn : ∀ n, n ∈ (V : Set G) ↔ x * n * x⁻¹ ∈ V := hXV hx
  have hconv : x * ((y * t * y⁻¹)⁻¹ * w) * x⁻¹ ∈ V := (hxn _).mp hy
  convert hconv using 1
  group

theorem y7a_O_conj_iff {X V : Subgroup G} {t : G} (hXV : X ≤ normalizer (V : Set G)) {x w : G}
    (hx : x ∈ X) : x * w * x⁻¹ ∈ y7aO X V t ↔ w ∈ y7aO X V t := by
  constructor
  · intro h
    have h' := y7a_O_conj (X := X) (V := V) (t := t) hXV (X.inv_mem hx) h
    convert h' using 1
    group
  · exact y7a_O_conj hXV hx

theorem y7a_O_sub {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}
    (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {X : Subgroup G}
    (hX1 : X ≤ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hX2 : X ≤ normalizer (V : Set G)) :
    ∀ w ∈ y7aO X V t, w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V := by
  intro w hw
  obtain ⟨x, hxX, hx⟩ := hw
  have hζV : (x * t * x⁻¹)⁻¹ * w ∈ V := hx
  have htC1 : t ∈ (A ⊔ C0 : Subgroup G) := mem_sup_right (y7a_t_mem_C0 h)
  have hxC1 : x * t * x⁻¹ ∈ (A ⊔ C0 : Subgroup G) := ((hX1 hxX) t).mp htC1
  have hζC1 : (x * t * x⁻¹)⁻¹ * w ∈ (A ⊔ C0 : Subgroup G) :=
    le_trans (y7a_V_le_C0 h) le_sup_right hζV
  have hwC1 : w ∈ A ⊔ C0 := by
    have hxζ : x * t * x⁻¹ * ((x * t * x⁻¹)⁻¹ * w) = w := by group
    rw [← hxζ]
    exact mul_mem hxC1 hζC1
  refine ⟨hwC1, ?_⟩
  intro hwAV
  have hxAV : x * t * x⁻¹ ∈ A ⊔ V := by
    have hwζ : x * t * x⁻¹ = w * ((x * t * x⁻¹)⁻¹ * w)⁻¹ := by group
    rw [hwζ]
    exact mul_mem hwAV (mem_sup_right (V.inv_mem hζV))
  have htAV : t ∈ A ⊔ V := ((y7a_conj_AV h (hX1 hxX) (hX2 hxX)) t).mpr hxAV
  exact y7a_t_not_mem_AV h htAV

theorem y7a_O_orbit {X Q V : Subgroup G} {t a a' k : G} (hQX : Q ≤ X)
    (hXV : X ≤ normalizer (V : Set G)) (hQt : ∀ k ∈ Q, k * t = t * k) (hk : k ∈ Q)
    (hζV : (k * a * k⁻¹)⁻¹ * a' ∈ V)
    (hζt : ((k * a * k⁻¹)⁻¹ * a') * t = t * ((k * a * k⁻¹)⁻¹ * a'))
    (ha : a * t ∈ y7aO X V t) : a' * t ∈ y7aO X V t := by
  have htk : t * k⁻¹ = k⁻¹ * t := by
    calc t * k⁻¹ = k⁻¹ * (k * t) * k⁻¹ := by group
      _ = k⁻¹ * (t * k) * k⁻¹ := by rw [hQt k hk]
      _ = k⁻¹ * t := by group
  have hkt : k * (a * t) * k⁻¹ = (k * a * k⁻¹) * t := by
    calc k * (a * t) * k⁻¹ = (k * a) * (t * k⁻¹) := by group
      _ = (k * a) * (k⁻¹ * t) := by rw [htk]
      _ = (k * a * k⁻¹) * t := by group
  have h1 : (k * a * k⁻¹) * t ∈ y7aO X V t := by
    rw [← hkt]
    exact y7a_O_conj hXV (hQX hk) ha
  have h2 : (k * a * k⁻¹) * t * ((k * a * k⁻¹)⁻¹ * a') ∈ y7aO X V t :=
    y7a_O_V h1 hζV
  have heq : (k * a * k⁻¹) * t * ((k * a * k⁻¹)⁻¹ * a') = a' * t := by
    calc (k * a * k⁻¹) * t * ((k * a * k⁻¹)⁻¹ * a')
        = (k * a * k⁻¹) * (t * ((k * a * k⁻¹)⁻¹ * a')) := by group
      _ = (k * a * k⁻¹) * (((k * a * k⁻¹)⁻¹ * a') * t) := by rw [← hζt]
      _ = ((k * a * k⁻¹) * ((k * a * k⁻¹)⁻¹ * a')) * t := by group
      _ = a' * t := by group
  rwa [heq] at h2

theorem y7a_O_dich {X Q V : Subgroup G} {z t : G} {S : Set G} (hQX : Q ≤ X)
    (hXV : X ≤ normalizer (V : Set G)) (hQt : ∀ k ∈ Q, k * t = t * k) (hzV : z ∈ V)
    (htz : t * z = z * t) (hS : IsOrbitMod Q (zpowers z) S) :
    (∀ a ∈ S, a * t ∈ y7aO X V t) ∨ (∀ a ∈ S, a * t ∉ y7aO X V t) := by
  obtain ⟨u, huS, hSu⟩ := hS
  have hzcent : z ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr htz.symm
  have hzleV : zpowers z ≤ V := Subgroup.zpowers_le.mpr hzV
  have hzleC : zpowers z ≤ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.zpowers_le.mpr hzcent
  by_cases hcase : u * t ∈ y7aO X V t
  · left
    intro a ha
    have ha' : a ∈ orbitMod Q (zpowers z) u := hSu ▸ ha
    obtain ⟨k, hk, hζZ⟩ := ha'
    exact y7a_O_orbit hQX hXV hQt hk (hzleV hζZ)
      (Subgroup.mem_centralizer_singleton_iff.mp (hzleC hζZ)) hcase
  · right
    intro a ha hat
    have ha' : a ∈ orbitMod Q (zpowers z) u := hSu ▸ ha
    obtain ⟨k, hk, hζZ⟩ := ha'
    have hζV : (k * u * k⁻¹)⁻¹ * a ∈ V := hzleV hζZ
    have hζt : ((k * u * k⁻¹)⁻¹ * a) * t = t * ((k * u * k⁻¹)⁻¹ * a) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hzleC hζZ)
    have haeq : a = (k * u * k⁻¹) * ((k * u * k⁻¹)⁻¹ * a) := by group
    have hat' : (k * u * k⁻¹) * t * ((k * u * k⁻¹)⁻¹ * a) ∈ y7aO X V t := by
      have h : a * t = (k * u * k⁻¹) * t * ((k * u * k⁻¹)⁻¹ * a) := by
        calc a * t = ((k * u * k⁻¹) * ((k * u * k⁻¹)⁻¹ * a)) * t := congrArg (· * t) haeq
          _ = (k * u * k⁻¹) * (((k * u * k⁻¹)⁻¹ * a) * t) := by group
          _ = (k * u * k⁻¹) * (t * ((k * u * k⁻¹)⁻¹ * a)) := by rw [hζt]
          _ = (k * u * k⁻¹) * t * ((k * u * k⁻¹)⁻¹ * a) := by group
      rwa [h] at hat
    have hw0 : (k * u * k⁻¹) * t ∈ y7aO X V t :=
      (y7a_O_V_iff (X := X) (V := V) (t := t) (w := (k * u * k⁻¹) * t)
        (v := (k * u * k⁻¹)⁻¹ * a) hζV).mp hat'
    have hconj := y7a_O_conj hXV (hQX (Q.inv_mem hk)) hw0
    have htk : t * k⁻¹ = k⁻¹ * t := by
      calc t * k⁻¹ = k⁻¹ * (k * t) * k⁻¹ := by group
        _ = k⁻¹ * (t * k) * k⁻¹ := by rw [hQt k hk]
        _ = k⁻¹ * t := by group
    have heq : k⁻¹ * ((k * u * k⁻¹) * t) * (k⁻¹)⁻¹ = u * t := by
      rw [inv_inv]
      calc k⁻¹ * (k * u * k⁻¹ * t) * k = u * (k⁻¹ * t * k) := by group
        _ = u * (t * k⁻¹ * k) := by rw [← htk]
        _ = u * t := by group
    rw [heq] at hconj
    exact hcase hconj

end CFSG.OddStandard.HigherRank.YamadaG23
