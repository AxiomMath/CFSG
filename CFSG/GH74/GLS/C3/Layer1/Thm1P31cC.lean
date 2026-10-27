module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cB

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.Thm1A7
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P31c

section Out

variable {G : Type} [Group G] [Finite G] {x y : G} {K T : Subgroup G} {f z : G}

theorem Env31.outer_of_commute
    (E : Env31 x y K T f z) {w : G} (hwT : w ∈ T) (hwc : ∀ q ∈ T ⊓ K, w * q = q * w)
    (hww : w * w = 1) (hw1 : w ≠ 1) (hwz : w ≠ z) (hwx : w ≠ x) (hwzx : w ≠ z * x) :
    ∀ hC : w ∈ centralizer ({x} : Set G), Back.actHom E.hKN ⟨w, hC⟩ ∉ innAut (kBar K) := by
  intro hC
  obtain ⟨q, hq, h⟩ := E.hCTP w hwT hwc
  have hzq : z * q = q * z := (E.hQcentP q hq z E.hzP).symm
  have hfC := E.hfC
  have hzC : z ∈ centralizer ({x} : Set G) := E.hTC E.hzP.1
  have hqC : q ∈ centralizer ({x} : Set G) := E.hTC hq.1
  have hφq : Back.actHom E.hKN ⟨q, hqC⟩ = 1 := by
    have : (⟨q, hqC⟩ : ↥(centralizer ({x} : Set G))) ∈ (Back.actHom E.hKN).ker := by
      rw [Back.actHom_ker E.hKN]
      exact hq.2
    exact this
  have hφz : Back.actHom E.hKN ⟨z, hzC⟩ ∈ innAut (kBar K) := by
    rw [Back.actHom_of_mem E.hKN E.hzP.2 hzC]
    exact ⟨_, rfl⟩
  rcases h with rfl | rfl | rfl | rfl
  · exfalso
    rcases E.hQ_unique w hq hww with h | h
    · exact hw1 h
    · exact hwx h
  · exfalso
    have hqq1 : q * q = 1 := by
      have : z * q * (z * q) = q * q := by
        calc z * q * (z * q) = z * (q * z) * q := by group
          _ = z * (z * q) * q := by rw [← hzq]
          _ = (z * z) * (q * q) := by group
          _ = q * q := by rw [E.hz2', one_mul]
      rw [← this]; exact hww
    rcases E.hQ_unique q hq hqq1 with h | h
    · exact hwz (by rw [h, mul_one])
    · exact hwzx (by rw [h])
  · have hmul : (⟨f * q, hC⟩ : ↥(centralizer ({x} : Set G))) = ⟨f, hfC⟩ * ⟨q, hqC⟩ := rfl
    rw [hmul, map_mul, hφq, mul_one]
    exact E.hfout hfC
  · have hmul : (⟨z * f * q, hC⟩ : ↥(centralizer ({x} : Set G))) =
        ⟨z, hzC⟩ * ⟨f, hfC⟩ * ⟨q, hqC⟩ := rfl
    rw [hmul, map_mul, map_mul, hφq, mul_one]
    intro hin
    apply E.hfout hfC
    have := (innAut (kBar K)).mul_mem ((innAut (kBar K)).inv_mem hφz) hin
    simpa using this

theorem Env31.hx_not_mem_P (E : Env31 x y K T f z) : x ∉ T ⊓ K := by
  intro hx
  have : x ∈ (T ⊓ K) ⊓ (T ⊓ CxK x K) := ⟨hx, E.hxQ⟩
  rw [E.hPQ, Subgroup.mem_bot] at this
  exact E.hx1 this

end Out

section Data

variable {G : Type} [Group G] [Finite G] {x y : G} {K T : Subgroup G} {f z : G}

structure Pump31Data (E : Env31 x y K T f z) (f₁ b p : G) : Prop where
  hf₁T : f₁ ∈ T
  hf₁2 : orderOf f₁ = 2
  hf₁c : ∀ q ∈ T ⊓ K, f₁ * q = q * f₁
  hf₁out : ∀ hC : f₁ ∈ centralizer ({x} : Set G), Back.actHom E.hKN ⟨f₁, hC⟩ ∉ innAut (kBar K)
  hf₁z : f₁ * z = z * f₁
  hxf₁ : x * f₁ = f₁ * x
  hb : b * (f₁ * z) = (f₁ * z) * b
  hbz : b * z * b⁻¹ = f₁
  hp : p * f₁ * p⁻¹ = x * f₁
  hpz : p * z * p⁻¹ = z

theorem Env31.exists_pump31data
    (hG : C3Hyp G) (hS34 : P34.S_prop34) (E : Env31 x y K T f z)
    (hQ3 : 2 < Nat.card ↥(T ⊓ CxK x K)) : ∃ f₁ b p : G, Pump31Data E f₁ b p := by
  classical
  obtain ⟨a, haN1, haN2, ha2, hxa⟩ := E.exists_a hG hS34
  have hza : a * x * a⁻¹ = z := E.hza haN1 haN2 hxa hQ3
  have haz : a * z * a⁻¹ = x := E.haz haN1 haN2 hxa hQ3 ha2
  have hax : a⁻¹ * z * a = x := by
    calc a⁻¹ * z * a = a⁻¹ * (a * x * a⁻¹) * a := by rw [hza]
      _ = x := by group
  have hxz : a⁻¹ * x * a = z := by
    calc a⁻¹ * x * a = a⁻¹ * (a * z * a⁻¹) * a := by rw [haz]
      _ = z := by group
  obtain ⟨n, hn3, hn⟩ := E.hdih
  obtain ⟨d, hdP, r₀, hr₀P, hdd, hd1, hdz, hr₀d⟩ :=
    exists_dihedral_data hn3 hn E.hzP E.hz1 E.hzc
  obtain ⟨f₁, hf₁def⟩ : ∃ f₁ : G, f₁ = a * d * a⁻¹ := ⟨_, rfl⟩
  obtain ⟨p, hpdef⟩ : ∃ p : G, p = a * r₀ * a⁻¹ := ⟨_, rfl⟩
  have hdf : d = a⁻¹ * f₁ * a := by rw [hf₁def]; group
  have hf₁T : f₁ ∈ T := by rw [hf₁def]; exact haN1 d hdP.1
  have hf₁f₁ : f₁ * f₁ = 1 := by
    calc f₁ * f₁ = a * (d * d) * a⁻¹ := by rw [hf₁def]; group
      _ = 1 := by rw [hdd]; group
  have hf₁1 : f₁ ≠ 1 := fun h => hd1 (by rw [hdf, h]; group)
  have hf₁2 : orderOf f₁ = 2 := orderOf_eq_prime (by rw [sq]; exact hf₁f₁) hf₁1
  have hdconj : a⁻¹ * f₁ * a ∈ T ⊓ K := by rw [← hdf]; exact hdP
  have hf₁c : ∀ q ∈ T ⊓ K, f₁ * q = q * f₁ := fun q hq =>
    (E.hcommPPa haN1 haN2 hxa hQ3 q hq f₁ hdconj).symm
  have hf₁z : f₁ * z = z * f₁ := hf₁c z E.hzP
  have hxf₁ : x * f₁ = f₁ * x := by
    have hzd : z * d = d * z := E.hzc d hdP
    calc x * f₁ = (a * z * a⁻¹) * (a * d * a⁻¹) := by rw [haz, hf₁def]
      _ = a * (z * d) * a⁻¹ := by group
      _ = a * (d * z) * a⁻¹ := by rw [hzd]
      _ = (a * d * a⁻¹) * (a * z * a⁻¹) := by group
      _ = f₁ * x := by rw [haz, hf₁def]
  have hf₁z' : f₁ ≠ z := by
    intro h
    apply E.hx_not_mem_P
    have : x = d := by
      calc x = a⁻¹ * z * a := hax.symm
        _ = a⁻¹ * f₁ * a := by rw [h]
        _ = d := hdf.symm
    rw [this]; exact hdP
  have hf₁x' : f₁ ≠ x := by
    intro h
    apply hdz
    calc d = a⁻¹ * f₁ * a := hdf
      _ = a⁻¹ * x * a := by rw [h]
      _ = z := hxz
  have hf₁zx' : f₁ ≠ z * x := by
    intro h
    apply E.hx_not_mem_P
    have h1 : d = x * z := by
      calc d = a⁻¹ * f₁ * a := hdf
        _ = a⁻¹ * (z * x) * a := by rw [h]
        _ = (a⁻¹ * z * a) * (a⁻¹ * x * a) := by group
        _ = x * z := by rw [hax, hxz]
    have : x = d * z⁻¹ := by rw [h1]; group
    rw [this]
    exact (T ⊓ K).mul_mem hdP ((T ⊓ K).inv_mem E.hzP)
  have hf₁out := E.outer_of_commute hf₁T hf₁c hf₁f₁ hf₁1 hf₁z' hf₁x' hf₁zx'
  have hd2 : orderOf d = 2 := orderOf_eq_prime (by rw [sq]; exact hdd) hd1
  obtain ⟨t₁, ht₁K, ht₁⟩ := E.exists_conj_z hG hdP hd2
  have ht₁x : t₁ * x = x * t₁ := E.hxcommK t₁ ht₁K
  obtain ⟨t, htdef⟩ : ∃ t : G, t = a * t₁ * a⁻¹ := ⟨_, rfl⟩
  have htz : t * z * t⁻¹ = z := by
    calc t * z * t⁻¹ = a * t₁ * (a⁻¹ * z * a) * t₁⁻¹ * a⁻¹ := by rw [htdef]; group
      _ = a * (t₁ * x * t₁⁻¹) * a⁻¹ := by rw [hax]; group
      _ = a * x * a⁻¹ := by rw [ht₁x]; group
      _ = z := hza
  have htx : t * x * t⁻¹ = f₁ := by
    calc t * x * t⁻¹ = a * t₁ * (a⁻¹ * x * a) * t₁⁻¹ * a⁻¹ := by rw [htdef]; group
      _ = a * (t₁ * z * t₁⁻¹) * a⁻¹ := by rw [hxz]; group
      _ = a * d * a⁻¹ := by rw [ht₁]
      _ = f₁ := hf₁def.symm
  have htz' : t⁻¹ * z * t = z := by
    calc t⁻¹ * z * t = t⁻¹ * (t * z * t⁻¹) * t := by rw [htz]
      _ = z := by group
  have htx' : t⁻¹ * f₁ * t = x := by
    calc t⁻¹ * f₁ * t = t⁻¹ * (t * x * t⁻¹) * t := by rw [htx]
      _ = x := by group
  obtain ⟨b, hbdef⟩ : ∃ b : G, b = t * a * t⁻¹ := ⟨_, rfl⟩
  have hbz : b * z * b⁻¹ = f₁ := by
    calc b * z * b⁻¹ = t * a * (t⁻¹ * z * t) * a⁻¹ * t⁻¹ := by rw [hbdef]; group
      _ = t * (a * z * a⁻¹) * t⁻¹ := by rw [htz']; group
      _ = t * x * t⁻¹ := by rw [haz]
      _ = f₁ := htx
  have hbf : b * f₁ * b⁻¹ = z := by
    calc b * f₁ * b⁻¹ = t * a * (t⁻¹ * f₁ * t) * a⁻¹ * t⁻¹ := by rw [hbdef]; group
      _ = t * (a * x * a⁻¹) * t⁻¹ := by rw [htx']; group
      _ = t * z * t⁻¹ := by rw [hza]
      _ = z := htz
  have hb : b * (f₁ * z) = (f₁ * z) * b := by
    have h1 : b * (f₁ * z) * b⁻¹ = f₁ * z := by
      calc b * (f₁ * z) * b⁻¹ = (b * f₁ * b⁻¹) * (b * z * b⁻¹) := by group
        _ = z * f₁ := by rw [hbf, hbz]
        _ = f₁ * z := hf₁z.symm
    calc b * (f₁ * z) = (b * (f₁ * z) * b⁻¹) * b := by group
      _ = (f₁ * z) * b := by rw [h1]
  have hpf : p * f₁ * p⁻¹ = x * f₁ := by
    calc p * f₁ * p⁻¹ = a * (r₀ * d * r₀⁻¹) * a⁻¹ := by rw [hpdef, hf₁def]; group
      _ = a * (z * d) * a⁻¹ := by rw [hr₀d]
      _ = (a * z * a⁻¹) * (a * d * a⁻¹) := by group
      _ = x * f₁ := by rw [haz, hf₁def]
  have hpconj : a⁻¹ * p * a ∈ T ⊓ K := by
    have : a⁻¹ * p * a = r₀ := by rw [hpdef]; group
    rw [this]; exact hr₀P
  have hzp : z * p = p * z := E.hcommPPa haN1 haN2 hxa hQ3 z E.hzP p hpconj
  have hpz : p * z * p⁻¹ = z := by
    calc p * z * p⁻¹ = (z * p) * p⁻¹ := by rw [hzp]
      _ = z := by group
  exact ⟨f₁, b, p, ⟨hf₁T, hf₁2, hf₁c, hf₁out, hf₁z, hxf₁, hb, hbz, hpf, hpz⟩⟩

end Data

end CFSG.GH74.GLS.C3.Layer1.Thm1P31c
