module

public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Out
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Env

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement Pointwise

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G33

section Vi

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

@[expose] noncomputable def Env33.rho (E : Env33 x y K T V W f z) :
    ↥V →* MulAut (kBar (pumpJ K f)) :=
  (Back.actHom E.hJn).comp (Subgroup.inclusion E.hVC)

theorem Env33.rho_ker (E : Env33 x y K T V W f z) (w : ↥V) :
    E.rho w = 1 ↔ (w : G) ∈ secD K f V := by
  have h1 : E.rho w = Back.actHom E.hJn ⟨(w : G), E.hVC w.2⟩ := rfl
  rw [h1, ← MonoidHom.mem_ker, Back.actHom_ker E.hJn, Subgroup.mem_subgroupOf, E.hDeq]
  exact ⟨fun h => ⟨w.2, h⟩, fun h => h.2⟩

theorem Env33.rho_mem_inn (E : Env33 x y K T V W f z) {w : ↥V} (hw : (w : G) ∈ pumpJ K f) :
    E.rho w ∈ innAut (kBar (pumpJ K f)) := by
  have h1 : E.rho w = Back.actHom E.hJn ⟨(w : G), E.hVC w.2⟩ := rfl
  rw [h1, Back.actHom_of_mem E.hJn hw (E.hVC w.2)]
  exact ⟨_, rfl⟩

theorem two_pow_le_card_of_isSylowOf {X S : Subgroup G} (hS : IsSylowOf 2 S X) {j : ℕ}
    (hj : 2 ^ j ∣ Nat.card ↥X) : 2 ^ j ≤ Nat.card ↥S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX0 : Nat.card ↥X ≠ 0 := Nat.card_pos.ne'
  have h3 : j ≤ (Nat.card ↥X).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hX0).1 hj
  rw [hS.card_eq]
  exact Nat.pow_le_pow_right (by norm_num) h3

theorem Env33.card_innAut (E : Env33 x y K T V W f z) :
    Nat.card ↥(innAut (kBar (pumpJ K f))) = Nat.card (kBar (pumpJ K f)) :=
  (Nat.card_congr (MonoidHom.ofInjective E.hcenJ).toEquiv).symm

theorem Env33.inn_decomp (E : Env33 x y K T V W f z) :
    ∀ v : ↥V, E.rho v ∈ innAut (kBar (pumpJ K f)) →
      ∃ p ∈ (T ⊓ K) ⊓ layerI K f, ∃ d ∈ secD K f V, (v : G) = p * d := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P₁ : Subgroup G := (T ⊓ K) ⊓ layerI K f with hP₁
  have hP₁V : P₁ ≤ V := fun p hp => E.hPV hp.1
  set P₁' : Subgroup ↥V := P₁.subgroupOf V with hP₁'
  have hker : ∀ p ∈ P₁', E.rho p = 1 → p = 1 := by
    intro p hp hρp
    have hpP : (p : G) ∈ T ⊓ K := (Subgroup.mem_subgroupOf.1 hp).1
    have hpD : (p : G) ∈ secD K f V := (E.rho_ker p).1 hρp
    have : (p : G) ∈ (T ⊓ K) ⊓ secD K f V := ⟨hpP, hpD⟩
    rw [E.hPD, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hPE : ∀ p ∈ P₁', E.rho p ∈ innAut (kBar (pumpJ K f)) := by
    intro p hp
    have hp1 : (p : G) ∈ P₁ := hp
    have : (p : G) ∈ V ⊓ pumpJ K f := by rw [E.hVJeq]; exact hp1
    exact E.rho_mem_inn this.2
  have hcard : ∀ j : ℕ, 2 ^ j ∣ Nat.card ↥(innAut (kBar (pumpJ K f))) → 2 ^ j ≤ Nat.card ↥P₁' := by
    intro j hj
    rw [E.card_innAut] at hj
    have h1 : 2 ^ j ∣ Nat.card ↥(pumpJ K f) :=
      hj.trans (Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥(pumpJ K f)))
    have h2 := two_pow_le_card_of_isSylowOf E.hVJ h1
    have h3 : Nat.card ↥P₁' = Nat.card ↥P₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₁V).toEquiv
    have h4 : V ⊓ pumpJ K f = P₁ := E.hVJeq
    rw [h3]
    rw [h4] at h2
    exact h2
  have himg := image_inf_eq_image E.hV2 E.rho (innAut (kBar (pumpJ K f))) P₁' hker hPE hcard
  intro v hv
  obtain ⟨p, hp, hpv⟩ := himg v hv
  have hq : E.rho (p⁻¹ * v) = 1 := by rw [map_mul, map_inv, hpv]; group
  have hqD : ((p⁻¹ * v : ↥V) : G) ∈ secD K f V := (E.rho_ker _).1 hq
  have hpP₁ : (p : G) ∈ P₁ := hp
  refine ⟨(p : G), hpP₁, ((p⁻¹ * v : ↥V) : G), hqD, ?_⟩
  simp

theorem Env33.conj_decomp (E : Env33 x y K T V W f z) :
    ∀ v ∈ V, ∀ p ∈ T ⊓ K, ∃ p' ∈ T ⊓ K, ∃ d ∈ secD K f V, v * p * v⁻¹ = p' * d := by
  intro v hv p hp
  obtain ⟨r, -, -, -, F₀, _, _, -, hF₀, ⟨e₀⟩⟩ := E.hJdata
  have hcomm : E.rho ⁅(⟨v, hv⟩ : ↥V), ⟨p, E.hPV hp⟩⁆ ∈ innAut (kBar (pumpJ K f)) := by
    rw [map_commutatorElement]
    exact outer_comm_mem_innAut hF₀ e₀ _ _
  obtain ⟨p₁, hp₁, d₁, hd₁, hc⟩ := E.inn_decomp _ hcomm
  have hc' : v * p * v⁻¹ * p⁻¹ = p₁ * d₁ := by
    have := hc
    simp only [commutatorElement_def] at this
    simpa using this
  have hp₁P : p₁ ∈ T ⊓ K := hp₁.1
  have hd₁' : p⁻¹ * d₁ * p ∈ secD K f V := by
    have := E.hDn p⁻¹ (V.inv_mem (E.hPV hp)) d₁ hd₁
    simpa using this
  refine ⟨p₁ * p, (T ⊓ K).mul_mem hp₁P hp, p⁻¹ * d₁ * p, hd₁', ?_⟩
  calc v * p * v⁻¹ = (v * p * v⁻¹ * p⁻¹) * p := by group
    _ = (p₁ * d₁) * p := by rw [hc']
    _ = p₁ * p * (p⁻¹ * d₁ * p) := by group

end Vi

end CFSG.GH74.GLS.C3.Layer1.Thm1G33
