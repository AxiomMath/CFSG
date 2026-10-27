module

public import CFSG.GH74.GLS.Balance.PStarComp
public import CFSG.GH74.GLS.Balance.SolvAPIDefs
public import CFSG.GH74.GLS.Balance.SubnormalChain
public import CFSG.GH74.GLS.TwoThin.Struct

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem isPStar_component {K : Subgroup X} (hK : IsComponent K) : IsPStar 2 ↥K :=
  isPStar_of_isQuasisimple hK.1

omit [Finite X] in
theorem le_normalizer_pPrimeCoreOf (C : Subgroup X) : C ≤ normalizer (pPrimeCoreOf 2 C : Set X) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨o, ho, rfl⟩
    refine ⟨⟨g, hg⟩ * o * ⟨g, hg⟩⁻¹, ?_, rfl⟩
    exact (inferInstance : (pPrimeCore 2 ↥C).Normal).conj_mem o ho ⟨g, hg⟩
  · rintro ⟨o, ho, hoe⟩
    refine ⟨⟨g, hg⟩⁻¹ * o * ⟨g, hg⟩, ?_, ?_⟩
    · have := (inferInstance : (pPrimeCore 2 ↥C).Normal).conj_mem o ho ⟨g, hg⟩⁻¹
      simpa using this
    · have : (C.subtype o : X) = g * h * g⁻¹ := hoe
      show (g⁻¹ * (o : X) * g : X) = h
      rw [show (o : X) = g * h * g⁻¹ from this]; group

theorem odd_card_pPrimeCoreOf (C : Subgroup X) : Odd (Nat.card (pPrimeCoreOf 2 C)) := by
  have h := TwoThin.odd_card_pPrimeCore ↥C
  have e : Nat.card (pPrimeCoreOf 2 C) = Nat.card (pPrimeCore 2 ↥C) :=
    Subgroup.card_map_of_injective C.subtype_injective
  rw [e]; exact h

@[expose] def innerNormalizer (K : Subgroup X) : Subgroup X where
  carrier := {r | r ∈ normalizer (K : Set X) ∧ ∃ k ∈ K, ∀ y ∈ K, r * y * r⁻¹ = k * y * k⁻¹}
  one_mem' := ⟨one_mem _, 1, one_mem _, fun y _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ka, hka, ha'⟩ ⟨hb, kb, hkb, hb'⟩
    refine ⟨mul_mem ha hb, ka * kb, mul_mem hka hkb, fun y hy => ?_⟩
    have hby : kb * y * kb⁻¹ ∈ K := K.mul_mem (K.mul_mem hkb hy) (K.inv_mem hkb)
    calc a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
      _ = a * (kb * y * kb⁻¹) * a⁻¹ := by rw [hb' y hy]
      _ = ka * (kb * y * kb⁻¹) * ka⁻¹ := ha' _ hby
      _ = (ka * kb) * y * (ka * kb)⁻¹ := by group
  inv_mem' := by
    rintro a ⟨ha, k, hk, ha'⟩
    refine ⟨inv_mem ha, k⁻¹, K.inv_mem hk, fun y hy => ?_⟩
    have h1 : k⁻¹ * y * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hk) hy) hk
    have h2 := ha' (k⁻¹ * y * k) h1
    have e : a * (k⁻¹ * y * k) * a⁻¹ = y := by rw [h2]; group
    calc a⁻¹ * y * a⁻¹⁻¹ = a⁻¹ * (a * (k⁻¹ * y * k) * a⁻¹) * a⁻¹⁻¹ := by rw [e]
      _ = k⁻¹ * y * k⁻¹⁻¹ := by group

omit [Finite X] in
theorem le_innerNormalizer_self (K : Subgroup X) : K ≤ innerNormalizer K :=
  fun k hk => ⟨Subgroup.le_normalizer hk, k, hk, fun _ _ => rfl⟩

omit [Finite X] in
theorem centralizer_le_innerNormalizer (K : Subgroup X) :
    centralizer (K : Set X) ≤ innerNormalizer K := by
  intro c hc
  refine ⟨(Subgroup.centralizer_le_normalizer (K : Set X)) hc, 1, K.one_mem, fun y hy => ?_⟩
  have := mem_centralizer_iff.mp hc y hy
  calc c * y * c⁻¹ = (c * y) * c⁻¹ := rfl
    _ = (y * c) * c⁻¹ := by rw [← this]
    _ = 1 * y * 1⁻¹ := by group

theorem layer_le_innerNormalizer {K : Subgroup X} (hK : IsComponent K) :
    layer X ≤ innerNormalizer K := by
  refine sSup_le fun L hL => ?_
  rcases CFSG.LocalCores.distinct_components_commute hL hK with rfl | h
  · exact le_innerNormalizer_self L
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
      (centralizer_le_innerNormalizer K)

@[expose] def invComps (x : X) : Set (Subgroup X) :=
  {K | IsComponent K ∧ x ∈ normalizer (K : Set X)}

@[expose] def invLayer (x : X) : Subgroup X := ⨆ K ∈ invComps x, K

section Step3

variable {x : X} {V : Subgroup X}

omit [Finite X] in
theorem normalizer_of_normal {N : Subgroup X} (hN : N.Normal) (g : X) :
    g ∈ normalizer (N : Set X) :=
  (Subgroup.normalizer_eq_top_iff.mpr hN) ▸ Subgroup.mem_top g

theorem step3_centralizes_pCore (hx : orderOf x = 2) (A : SolvAPI x V)
    (hF : ¬ oPrimeResidualOf 2 V ≤ pCore 2 X) : V ≤ centralizer (pCore 2 X : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVC : V ≤ centralizer ({x} : Set X) := A.hVC
  have hFn : (pCore 2 X).Normal := CFSG.pCore_normal
  have hF2 : IsPGroup 2 (pCore 2 X) := pCore_isPGroup
  have hxC : ∀ g ∈ centralizer ({x} : Set X), x * g = g * x := fun g hg =>
    (mem_centralizer_singleton_iff.mp hg).symm
  have hN2 : IsPGroup 2 ↥(pCore 2 X ⊓ centralizer ({x} : Set X)) := hF2.to_le inf_le_left
  have hNC : centralizer ({x} : Set X) ≤
      normalizer ((pCore 2 X ⊓ centralizer ({x} : Set X) : Subgroup X) : Set X) := by
    intro c hc
    rw [mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨hhF, hhC⟩
      exact ⟨hFn.conj_mem _ hhF c, (centralizer ({x} : Set X)).mul_mem ((centralizer ({x} : Set X)).mul_mem hc hhC) ((centralizer ({x} : Set X)).inv_mem hc)⟩
    · rintro ⟨h1, h2⟩
      have h1' : c⁻¹ * (c * h * c⁻¹) * c ∈ pCore 2 X := by
        simpa using hFn.conj_mem _ h1 c⁻¹
      have h2' : c⁻¹ * (c * h * c⁻¹) * c ∈ centralizer ({x} : Set X) :=
        (centralizer ({x} : Set X)).mul_mem ((centralizer ({x} : Set X)).mul_mem
          ((centralizer ({x} : Set X)).inv_mem hc) h2) hc
      have e : c⁻¹ * (c * h * c⁻¹) * c = h := by group
      rw [e] at h1' h2'
      exact ⟨h1', h2'⟩
  rcases A.dich (pCore 2 X ⊓ centralizer ({x} : Set X)) hN2 inf_le_right hNC with h | h
  · exact absurd (h.trans inf_le_left) hF
  · apply A.gen
    intro u hu hu2
    rw [mem_centralizer_iff]
    intro f hf
    have hu2' : ¬ 2 ∣ orderOf u := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hu2.symm
    have hnorm : ∀ g : X, g ∈ normalizer (pCore 2 X : Set X) := normalizer_of_normal hFn
    have := centralizes_of_centralizes_fixed hF2 ⟨1, by simpa using hx⟩ hu2'
      (hxC u (hVC hu)) (hnorm x) (hnorm u) (fun t ht hxt => by
        have htC : t ∈ centralizer ({x} : Set X) := mem_centralizer_singleton_iff.mpr hxt.symm
        exact (mem_centralizer_iff.mp (h hu) t ⟨ht, htC⟩).symm) f hf
    exact this.symm

omit [Finite X] in
theorem invLayer_conj_mem {g : X} (hg : g ∈ centralizer ({x} : Set X)) :
    ∀ ℓ ∈ invLayer x, g * ℓ * g⁻¹ ∈ invLayer x := by
  have key : invLayer x ≤ (invLayer x).comap (MulAut.conj g).toMonoidHom := by
    refine iSup₂_le fun K hK => ?_
    intro y hy
    have hK' : K.map (MulAut.conj g).toMonoidHom ∈ invComps x := by
      refine ⟨CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK.1, ?_⟩
      have hgx : g * x = x * g := mem_centralizer_singleton_iff.mp hg
      have hxK := hK.2
      have hxK' : x⁻¹ ∈ normalizer (K : Set X) := (normalizer (K : Set X)).inv_mem hxK
      rw [mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨x * y * x⁻¹, (mem_normalizer_iff.mp hxK y).mp hy, ?_⟩
        show g * (x * y * x⁻¹) * g⁻¹ = x * (g * y * g⁻¹) * x⁻¹
        have e : g * x = x * g := hgx
        calc g * (x * y * x⁻¹) * g⁻¹ = (g * x) * y * (x⁻¹ * g⁻¹) := by group
          _ = (x * g) * y * (x⁻¹ * g⁻¹) := by rw [e]
          _ = x * (g * y * g⁻¹) * x⁻¹ := by
            have e2 : x⁻¹ * g⁻¹ = g⁻¹ * x⁻¹ := by
              calc x⁻¹ * g⁻¹ = (g * x)⁻¹ := by group
                _ = (x * g)⁻¹ := by rw [e]
                _ = g⁻¹ * x⁻¹ := by group
            rw [e2]; group
      · rintro ⟨y, hy, hyh⟩
        refine ⟨x⁻¹ * y * x, ?_, ?_⟩
        · have := (mem_normalizer_iff.mp hxK' y).mp hy
          simpa using this
        · show g * (x⁻¹ * y * x) * g⁻¹ = h
          have e : g * x = x * g := hgx
          have hyh' : g * y * g⁻¹ = x * h * x⁻¹ := hyh
          have e1 : x⁻¹ * g = g * x⁻¹ := by
            calc x⁻¹ * g = x⁻¹ * (g * x) * x⁻¹ := by group
              _ = x⁻¹ * (x * g) * x⁻¹ := by rw [e]
              _ = g * x⁻¹ := by group
          have e2 : g⁻¹ * x = x * g⁻¹ := by
            calc g⁻¹ * x = g⁻¹ * (x * g) * g⁻¹ := by group
              _ = g⁻¹ * (g * x) * g⁻¹ := by rw [e]
              _ = x * g⁻¹ := by group
          calc g * (x⁻¹ * y * x) * g⁻¹ = (g * x⁻¹) * y * (x * g⁻¹) := by group
            _ = (x⁻¹ * g) * y * (g⁻¹ * x) := by rw [e1, e2]
            _ = x⁻¹ * (g * y * g⁻¹) * x := by group
            _ = h := by rw [hyh']; group
    have : (MulAut.conj g) y ∈ K.map (MulAut.conj g).toMonoidHom := ⟨y, hy, rfl⟩
    exact (le_iSup₂ (f := fun K (_ : K ∈ invComps x) => K) _ hK') this
  intro ℓ hℓ
  exact key hℓ

end Step3

end CFSG.GH74.GLS.Balance
