module

public import CFSG.GH74.GLS.C3.Layer1.Th2P85Bar
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR7

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCoreOf_le_of_isPCompIn {H J : Subgroup G} (hJ : IsPCompIn 2 H J) :
    pPrimeCoreOf 2 J ≤ pPrimeCoreOf 2 H := by
  obtain ⟨K, -, hsub, -⟩ := hJ.2
  exact Th2.pPrimeCoreOf_le_of_subnormal ⟨hJ.1, hsub⟩

theorem exists_theta {x t : G} {K J : Subgroup G} (hlt : PumpUpLT 2 x K t J)
    (hxJ : x ∈ normalizer (J : Set G)) (e : kBar J ≃* kBar K) :
    ∃ Θ : kBar J ≃* kBar K, ∀ (g : G) (hgJ : g ∈ normalizer (J : Set G))
      (hgK : g ∈ normalizer (K : Set G)), g * t = t * g →
        ∀ c : kBar J, Θ (barAct J ⟨g, hgJ⟩ c) = barAct K ⟨g, hgK⟩ (Θ c) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxY : x ∈ centralizer ({t} : Set G) := TwoThin.mem_centralizer_symm hlt.2.2.1
  have hle : TwoThin.hatCard J ≤ TwoThin.hatCard K := (Nat.card_congr e.toEquiv).le
  obtain ⟨Λ, hΛ, hJc, ⟨eΛ⟩, -, -, hcases⟩ := rigid_step hlt hxY hle
  have hvert : bar t Λ = bar t J := (hcases.resolve_right (fun h => h.1 hxJ)).2
  have hΛK : Λ ≤ K := hΛ.le.trans inf_le_left
  have hΛY : Λ ≤ centralizer ({t} : Set G) := hΛ.le.trans inf_le_right
  obtain ⟨φ, hφs, -, hφρ⟩ := TwoThin.exists_phi hΛK hΛY hΛ.cover
  have hφb : Function.Bijective φ :=
    hφs.bijective_of_nat_card_le (Nat.card_congr eΛ.toEquiv).ge
  have hJH : J ≤ centralizer ({t} : Set G) := hJc.1
  have hOH : pPrimeCoreOf 2 J ≤ pPrimeCoreOf 2 (centralizer ({t} : Set G)) :=
    pPrimeCoreOf_le_of_isPCompIn hJc
  let ι₀ : ↥J →* ↥(bar t J) := P85.toImgM hJH
  have hι₀s : Function.Surjective ι₀ := P85.toImgM_surjective hJH
  have hι₀k : ι₀.ker = pPrimeCore 2 ↥J := P85.ker_toImgM_eq hJH hOH
  let ι : kBar J ≃* ↥(bar t J) :=
    (QuotientGroup.quotientMulEquivOfEq hι₀k.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ι₀ hι₀s)
  have hι : ∀ l : ↥J, ι (QuotientGroup.mk l) = ι₀ l := fun l => rfl
  let Θ₁ : ↥(bar t J) →* kBar K := φ.comp (MulEquiv.subgroupCongr hvert.symm).toMonoidHom
  have hΘ₁b : Function.Bijective Θ₁ := hφb.comp (MulEquiv.subgroupCongr hvert.symm).bijective
  let Θ₀ : ↥(bar t J) ≃* kBar K := MulEquiv.ofBijective Θ₁ hΘ₁b
  have hΘ : ∀ (a : G) (ha : a ∈ J) (m : ↥(centralizer ({t} : Set G))) (hm : (m : G) ∈ Λ),
      TwoThin.barMk ↥(centralizer ({t} : Set G)) m = TwoThin.barMk ↥(centralizer ({t} : Set G)) ⟨a, hJH ha⟩ →
      Θ₀ (ι (QuotientGroup.mk ⟨a, ha⟩)) = QuotientGroup.mk ⟨(m : G), hΛK hm⟩ := by
    intro a ha m hm hma
    have e1 : (MulEquiv.subgroupCongr hvert.symm (ι₀ ⟨a, ha⟩) : ↥(bar t Λ)) =
        ⟨TwoThin.barMk ↥(centralizer ({t} : Set G)) m, ⟨m, Subgroup.mem_subgroupOf.2 hm, rfl⟩⟩ :=
      Subtype.ext hma.symm
    have h1 := hφρ (m : G) hm
    show φ (MulEquiv.subgroupCongr hvert.symm (ι₀ ⟨a, ha⟩)) = _
    rw [e1]
    exact h1
  refine ⟨ι.trans Θ₀, ?_⟩
  intro g hgJ hgK htg c
  obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective c
  have hgY : g ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 htg
  have hgX : g ∈ normalizer ((K ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) :=
    TwoThin.mem_normalizer_inf hgK (Subgroup.le_normalizer hgY)
  have hmem : TwoThin.barMk ↥(centralizer ({t} : Set G)) ⟨a, hJH ha⟩ ∈ bar t Λ := by
    rw [hvert]
    exact ⟨⟨a, hJH ha⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
  obtain ⟨m, hm, hma⟩ := hmem
  have hmΛ : (m : G) ∈ Λ := Subgroup.mem_subgroupOf.1 hm
  have hgmΛ : g * (m : G) * g⁻¹ ∈ Λ :=
    TwoThin.conj_mem_of_unique_isPCompIn hΛ.pc hΛ.uniq hgX hmΛ
  have hlhs := hΘ a ha m hmΛ hma
  have ha' : g * a * g⁻¹ ∈ J := normalizer_conj_mem g hgJ a ha
  let m' : ↥(centralizer ({t} : Set G)) := ⟨g, hgY⟩ * m * ⟨g, hgY⟩⁻¹
  have hm'c : (m' : G) = g * (m : G) * g⁻¹ := by simp [m']
  have hm'Λ : (m' : G) ∈ Λ := by rw [hm'c]; exact hgmΛ
  have hm'a : TwoThin.barMk ↥(centralizer ({t} : Set G)) m' =
      TwoThin.barMk ↥(centralizer ({t} : Set G)) ⟨g * a * g⁻¹, hJH ha'⟩ := by
    have h1 : (⟨g * a * g⁻¹, hJH ha'⟩ : ↥(centralizer ({t} : Set G))) =
        ⟨g, hgY⟩ * ⟨a, hJH ha⟩ * ⟨g, hgY⟩⁻¹ := Subtype.ext (by simp)
    rw [h1]
    simp only [m', map_mul, map_inv, hma]
  have hrhs := hΘ (g * a * g⁻¹) ha' m' hm'Λ hm'a
  show Θ₀ (ι (barAct J ⟨g, hgJ⟩ (QuotientGroup.mk ⟨a, ha⟩))) =
    barAct K ⟨g, hgK⟩ (Θ₀ (ι (QuotientGroup.mk ⟨a, ha⟩)))
  rw [barAct_mk', hrhs, hlhs, barAct_mk']
  congr 1

section Pullback

omit [Finite G] in
theorem exists_pullback {B : Subgroup G} {X : Type*} [Group X] [Finite X] (θ : ↥B →* X)
    {V' : Subgroup X} (hV' : V' ≤ θ.range) (hcard : Nat.card θ.range = 2 * Nat.card V') :
    ∃ (V : Subgroup G) (hVB : V ≤ B), Nat.card B = 2 * Nat.card V ∧
      (∀ (v : G) (hv : v ∈ V), θ ⟨v, hVB hv⟩ ∈ V') ∧
      ∀ x : ↥B, θ x ∈ V' → (x : G) ∈ V := by
  classical
  let θr : ↥B →* ↥θ.range := θ.rangeRestrict
  have hθr : Function.Surjective θr := θ.rangeRestrict_surjective
  let V'' : Subgroup ↥θ.range := V'.subgroupOf θ.range
  let C : Subgroup ↥B := V''.comap θr
  have hV''card : Nat.card V'' = Nat.card V' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV').toEquiv
  have hidx : V''.index = 2 := by
    have h1 := V''.index_mul_card
    rw [hV''card, hcard] at h1
    have hpos : 0 < Nat.card V' := Nat.card_pos
    have : V''.index * Nat.card V' = 2 * Nat.card V' := h1
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hCidx : C.index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ hθr]; exact hidx
  have hCcard : Nat.card B = 2 * Nat.card C := by
    have h := C.index_mul_card
    rw [hCidx] at h
    exact h.symm
  refine ⟨C.map B.subtype, Subgroup.map_subtype_le C, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective B.subtype_injective]; exact hCcard
  · rintro v ⟨c, hc, rfl⟩
    have : θr c ∈ V'' := hc
    exact this
  · intro x hx
    exact ⟨x, (show θr x ∈ V'' from hx), rfl⟩

end Pullback

end CFSG.GH74.GLS.Th2.Obs
