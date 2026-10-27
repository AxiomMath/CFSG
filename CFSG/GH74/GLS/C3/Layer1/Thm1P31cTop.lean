module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cS
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cC
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cLayer

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.E2
  CFSG.GH74.GLS.IVK CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1
  CFSG.GH74.GLS.C3.Layer1.PumpCalc

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P31c

section Top

variable {G : Type} [Group G] [Finite G] {x y : G} {K T : Subgroup G} {f z : G}

omit [Finite G] in
theorem Env31.hKcen (E : Env31 x y K T f z) : Subgroup.center (kBar K) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_center_iff] at hc
  rw [Subgroup.mem_bot]
  apply E.hcen
  refine MulEquiv.ext fun g => ?_
  show c * g * c⁻¹ = 1 * g * (1 : kBar K)⁻¹
  rw [one_mul, inv_one, mul_one, ← hc g]
  group

theorem Env31.pump_false
    (hGKF : GenericKnownFacts) (hF : E2ComponentFacts) (hC2 : C2Facts) (hG : C3Hyp G)
    (hV : NoV2Fine G) (h5 : ¬ HasL2Model (kBar K) (fun q => q = 5)) (E : Env31 x y K T f z)
    {f₁ b p : G} (D : Pump31Data E f₁ b p) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzC : z ∈ centralizer ({x} : Set G) := E.hTC E.hzP.1
  have hf₁C : f₁ ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 D.hxf₁.symm
  have hzx : z * x = x * z := mem_centralizer_singleton_iff.1 hzC
  have hzz : z * z = 1 := E.hz2'
  have hff : f₁ * f₁ = 1 := by
    have := pow_orderOf_eq_one f₁
    rwa [D.hf₁2, sq] at this
  obtain ⟨w, hw⟩ : ∃ w : G, w = f₁ * z := ⟨_, rfl⟩
  have hwC : w ∈ centralizer ({x} : Set G) := by
    rw [hw]; exact Subgroup.mul_mem _ hf₁C hzC
  have hφz : Back.actHom E.hKN ⟨z, hzC⟩ ∈ innAut (kBar K) := by
    rw [Back.actHom_of_mem E.hKN E.hzP.2 hzC]
    exact ⟨_, rfl⟩
  have hφw_eq : Back.actHom E.hKN ⟨w, hwC⟩ =
      Back.actHom E.hKN ⟨f₁, hf₁C⟩ * Back.actHom E.hKN ⟨z, hzC⟩ := by
    have h1 := (Back.actHom E.hKN).map_mul ⟨f₁, hf₁C⟩ ⟨z, hzC⟩
    have e : (⟨f₁, hf₁C⟩ * ⟨z, hzC⟩ : ↥(centralizer ({x} : Set G))) = ⟨w, hwC⟩ := Subtype.ext hw.symm
    rw [e] at h1
    exact h1
  have hφw : Back.actHom E.hKN ⟨w, hwC⟩ ∉ innAut (kBar K) := by
    intro h
    apply D.hf₁out hf₁C
    rw [hφw_eq] at h
    have := (innAut (kBar K)).mul_mem h ((innAut (kBar K)).inv_mem hφz)
    simpa using this
  have hw1 : w ≠ 1 := by
    intro h
    apply hφw
    have : (⟨w, hwC⟩ : ↥(centralizer ({x} : Set G))) = 1 := Subtype.ext h
    rw [this, map_one]
    exact (innAut (kBar K)).one_mem
  have hf₁z : f₁ * z = z * f₁ := D.hf₁z
  have hw2 : orderOf w = 2 := by
    rw [hw]
    exact orderOf_mul_eq_two_of_commute D.hf₁2 E.hz2 hf₁z (hw ▸ hw1)
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2, sq] at this
  have hwx : w ≠ x := by
    intro h
    apply hφw
    have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
    have : (⟨w, hwC⟩ : ↥(centralizer ({x} : Set G))) = ⟨x, hxC⟩ := Subtype.ext h
    rw [this, E.hxker]
    exact (innAut (kBar K)).one_mem
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hFA, -, -⟩ := E.core hG
  have hwT : w ∈ T := by rw [hw]; exact T.mul_mem D.hf₁T E.hzP.1
  have hwCT : (⟨w, hwC⟩ : ↥(centralizer ({x} : Set G))) ∈ T.subgroupOf (centralizer ({x} : Set G)) :=
    hwT
  have hw2' : orderOf (⟨w, hwC⟩ : ↥(centralizer ({x} : Set G))) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hw2
  have hwc' : ∀ q ∈ (T ⊓ K).subgroupOf (centralizer ({x} : Set G)),
      (⟨w, hwC⟩ : ↥(centralizer ({x} : Set G))) * q = q * ⟨w, hwC⟩ := by
    intro q hq
    have hq' : (q : G) ∈ T ⊓ K := hq
    apply Subtype.ext
    show w * (q : G) = (q : G) * w
    rw [hw]
    calc f₁ * z * (q : G) = f₁ * (z * (q : G)) := by group
      _ = f₁ * ((q : G) * z) := by rw [E.hzc q hq']
      _ = (f₁ * (q : G)) * z := by group
      _ = ((q : G) * f₁) * z := by rw [D.hf₁c q hq']
      _ = (q : G) * (f₁ * z) := by group
  have hFAw := hFA ⟨w, hwC⟩ hwCT hw2' hwc' hφw
  have hσ2 : Back.actHom E.hKN ⟨w, hwC⟩ * Back.actHom E.hKN ⟨w, hwC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨w, hwC⟩ * ⟨w, hwC⟩ : ↥(centralizer ({x} : Set G))) = 1 := Subtype.ext hww
    rw [this, map_one]
  obtain ⟨F₀, _, _, hodd₀, h3₀, ⟨e₀⟩⟩ := fixedPGL_of_isFAut E.hshape
    (not_hasL2Model_nine_of_noV2Fine hV E.hu2 h5) hFAw hσ2
  obtain ⟨n, hn3, hn⟩ := E.hdih
  obtain ⟨u, huP, huu⟩ := Thm1G33.exists_sq_eq_of_dihedral hn3 hn E.hzP E.hz1 E.hzc
  have hzw : z * w = w * z := by
    rw [hw]
    calc z * (f₁ * z) = (z * f₁) * z := by group
      _ = (f₁ * z) * z := by rw [← hf₁z]
  have huw : u * w = w * u := by
    rw [hw]
    calc u * (f₁ * z) = (u * f₁) * z := by group
      _ = (f₁ * u) * z := by rw [D.hf₁c u huP]
      _ = f₁ * (u * z) := by group
      _ = f₁ * (z * u) := by rw [E.hzc u huP]
      _ = (f₁ * z) * u := by group
  obtain ⟨Λ, hΛ, hΛK, hzΛ, hΛL2, hΛcen⟩ := exists_layer_comp E.hKC E.hKN hwC hw2 hodd₀ h3₀ e₀
    E.hzP.2 hzw E.hz2 huP.2 huw huu
  have hΛU : HasL2Model (kBar Λ) Odd := by
    obtain ⟨p₂, f₂, hp₂, hf₂, hq₂, hL₂⟩ := hΛL2
    exact ⟨p₂, f₂, hp₂, hf₂, hq₂ ▸ hodd₀, hL₂⟩
  have H : PumpHyp x w z b p K Λ :=
    { hx2 := E.hu2.1.1.1
      hw2 := hw2
      hz2 := E.hz2
      hxw := by
        rw [hw]
        calc x * (f₁ * z) = (x * f₁) * z := by group
          _ = (f₁ * x) * z := by rw [D.hxf₁]
          _ = f₁ * (x * z) := by group
          _ = f₁ * (z * x) := by rw [← hzx]
          _ = (f₁ * z) * x := by group
      hbw := by rw [hw]; exact D.hb
      hΛ := hΛ
      hzΛ := hzΛ
      hb := by
        rw [hw]
        calc b * z * b⁻¹ = f₁ := D.hbz
          _ = (f₁ * z) * z := by rw [mul_assoc, hzz, mul_one]
      hΛcen := hΛcen
      hΛU := hΛU
      hp := by
        rw [hw]
        calc p * (f₁ * z) * p⁻¹ = (p * f₁ * p⁻¹) * (p * z * p⁻¹) := by group
          _ = (x * f₁) * z := by rw [D.hp, D.hpz]
          _ = x * (f₁ * z) := by group
      hwx := hwx
      huniq := E.huniq
      hKcen := E.hKcen }
  exact H.false hGKF hF hC2 hG

end Top

end CFSG.GH74.GLS.C3.Layer1.Thm1P31c
