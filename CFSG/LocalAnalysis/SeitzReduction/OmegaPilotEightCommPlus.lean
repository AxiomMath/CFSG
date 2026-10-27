module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthCore

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect perfectCore_le)

section Transport

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_centralizer_of_coords_orth_aut (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {C : Type*} [Group C] (e : L ≃* C) {t : G}
    (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G)) {z₀ : C} (hz₀ : z₀ ≠ 1) {g : G}
    (hg : g⁻¹ * t * g = t * (e.symm z₀ : G)) {φ' : C →* G} (hφ' : Function.Injective φ')
    (hφ'r : φ'.range = CFSG.conjugate L g) (hφ'z : φ' z₀ = (e.symm z₀ : G))
    (Qz Mz : Subgroup C) (hF3 : perfectCore (centralizer ({z₀} : Set C)) = Qz ⊔ Mz)
    (hQ : IsPGroup 2 Qz) (hMN : Mz ≤ normalizer (Qz : Set C)) (hQM : Disjoint Qz Mz)
    (hM : ∀ N : Subgroup Mz, N.Normal → IsPGroup 2 N → N = ⊥) {J : Subgroup C} (hJ : J ≤ Mz)
    (hmodel : ∀ ι : Mz ≃* Mz, ∀ y ∈ ((J.subgroupOf Mz).map ι.toMonoidHom).map Mz.subtype,
      y ≠ 1 → Odd (orderOf y) → ∀ S' R' : Subgroup C,
      S' ≤ centralizer {y} →
      (∀ N : Subgroup C, z₀ ∈ N → (∀ s ∈ S', ∀ n ∈ N, s * n * s⁻¹ ∈ N) → S' ≤ N) →
      R' ≤ centralizer {z₀} → R' ≤ centralizer {y} → ⁅R', R'⁆ = R' →
      S' ≤ centralizer (R' : Set C))
    {y₀ : C} (hy₀J : y₀ ∈ J) (hy₀1 : y₀ ≠ 1) (hy₀o : Odd (orderOf y₀)) {S R : Subgroup G}
    (hSperf : ⁅S, S⁆ = S) (hSsimple : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤)
    (hSt : S ≤ centralizer ({g⁻¹ * t * g} : Set G))
    (hSy : S ≤ centralizer ({(e.symm y₀ : G)} : Set G)) (hzS : (e.symm z₀ : G) ∈ S)
    (hRL : R ≤ L) (hRz : R ≤ centralizer ({(e.symm z₀ : G)} : Set G))
    (hRy : R ≤ centralizer ({(e.symm y₀ : G)} : Set G)) (hRperf : ⁅R, R⁆ = R) :
    S ≤ centralizer (R : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : C →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := EPilot.range_subtype_comp_mulEquiv_symm e
  have hφz : φ z₀ = (e.symm z₀ : G) := rfl
  have hφy : φ y₀ = (e.symm y₀ : G) := rfl
  have hact := conj_eq_of_conj_eq_mul ht htC hg
  have hact' : ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = φ' z₀ * l * (φ' z₀)⁻¹ := by
    rw [hφ'z]; exact hact
  have hΛ := EPilot.map_perfectCore_centralizer_eq_of_inner hset hOut htC ht hφ hφr hφ' hφ'r
    (y := z₀) (Or.inr hg) hact'
  rw [hF3] at hΛ
  have hX2 : ¬ 2 ∣ Nat.card (zpowers (φ y₀)) := by
    rw [Nat.card_zpowers, orderOf_injective φ hφ y₀]
    exact fun h => (Nat.not_even_iff_odd.2 hy₀o) (even_iff_two_dvd.2 h)
  obtain ⟨hQeq, ι, -, q₀, hq₀, hXq⟩ := EPilot.exists_conj_le_map_of_two_decompositions hφ hφ'
    hQ hQ hM hM hMN hMN hQM hQM hΛ hJ (X := zpowers (φ y₀))
    ((zpowers_le (G := G)).mpr (mem_map_of_mem φ hy₀J)) hX2
  obtain ⟨_, ⟨y₁, hy₁J, rfl⟩, hy₁⟩ := hXq (mem_zpowers (φ y₀))
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hy₁
  have hq₀g : q₀ ∈ CFSG.conjugate L g := by
    rw [hQeq] at hq₀
    obtain ⟨q, -, rfl⟩ := hq₀
    rw [← hφ'r]
    exact ⟨q, rfl⟩
  have hq₀z : q₀ * (e.symm z₀ : G) = (e.symm z₀ : G) * q₀ := by
    obtain ⟨q, hq, rfl⟩ := hq₀
    have hqc : q ∈ centralizer ({z₀} : Set C) :=
      perfectCore_le _ (hF3 ▸ (mem_sup_left hq : q ∈ Qz ⊔ Mz))
    rw [← hφz, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hqc]
  set φ'' : C →* G := (MulAut.conj q₀).toMonoidHom.comp φ' with hφ''def
  have hφ'' : Function.Injective φ'' := (MulAut.conj q₀).injective.comp hφ'
  have hφ''z : φ'' z₀ = (e.symm z₀ : G) := by
    simp only [hφ''def, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hφ'z]
    rw [hq₀z, mul_inv_cancel_right]
  have hφ''y : φ'' y₁ = (e.symm y₀ : G) := by
    simp only [hφ''def, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    exact hy₁
  have hrange : ∀ x ∈ CFSG.conjugate L g, ∃ c, φ'' c = x := by
    intro x hx
    have hx' : q₀⁻¹ * x * q₀ ∈ CFSG.conjugate L g :=
      mul_mem (mul_mem (inv_mem hq₀g) hx) hq₀g
    rw [← hφ'r] at hx'
    obtain ⟨c, hc⟩ := hx'
    refine ⟨c, ?_⟩
    simp only [hφ''def, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hc]
    group
  have hSL' := le_conjugate_of_perfect_of_le_centralizer hset hOut htC ht g hSperf hSt
  have hΛeq := EPilot.perfectCore_inf_centralizer_eq_of_inv_mul_mem hset hOut htC ht
    (w := (e.symm z₀ : G)) (Or.inr hg) (EPilot.inv_mul_mem_centralizer_of_conj_eq hact)
  have hRL' : R ≤ CFSG.conjugate L g := by
    have h1 : R ≤ perfectCore (L ⊓ centralizer ({(e.symm z₀ : G)} : Set G)) :=
      le_perfectCore_of_perfect (le_inf hRL hRz) hRperf
    rw [hΛeq] at h1
    exact h1.trans ((perfectCore_le _).trans inf_le_left)
  have hcomm : ∀ {u v : C}, φ'' u * φ'' v = φ'' v * φ'' u → u * v = v * u := fun h => by
    rw [← map_mul, ← map_mul] at h
    exact hφ'' h
  have hz1 : (e.symm z₀ : G) ≠ 1 := fun h => hz₀ (by
    have := congrArg e (Subtype.ext h : e.symm z₀ = 1)
    simpa using this)
  have hS' : S.comap φ'' ≤ centralizer (R.comap φ'' : Set C) := by
    refine hmodel ι y₁ hy₁J ?_ ?_ (S.comap φ'') (R.comap φ'') ?_ ?_ ?_ ?_ ?_
    · intro h
      apply hy₀1
      have h' : (e.symm y₀ : G) = 1 := by rw [← hφ''y, h, map_one]
      have := congrArg e (Subtype.ext h' : e.symm y₀ = 1)
      simpa using this
    · rw [← orderOf_injective φ'' hφ'' y₁, hφ''y, ← hφy, orderOf_injective φ hφ y₀]
      exact hy₀o
    · intro u hu
      refine mem_centralizer_singleton_iff.mpr (hcomm ?_)
      rw [hφ''y]
      exact mem_centralizer_singleton_iff.mp (hSy hu)
    · intro N hzN hN
      have hle : S ≤ N.map φ'' := by
        refine le_of_normalized_of_simple hSsimple hzS hz1 ⟨z₀, hzN, hφ''z⟩ ?_
        rintro s hs _ ⟨n, hn, rfl⟩
        obtain ⟨c, rfl⟩ := hrange s (hSL' hs)
        exact ⟨c * n * c⁻¹, hN c hs n hn, by rw [map_mul, map_mul, map_inv]⟩
      intro c hc
      obtain ⟨n, hn, hnc⟩ := hle hc
      rwa [← hφ'' hnc]
    · intro u hu
      refine mem_centralizer_singleton_iff.mpr (hcomm ?_)
      rw [hφ''z]
      exact mem_centralizer_singleton_iff.mp (hRz hu)
    · intro u hu
      refine mem_centralizer_singleton_iff.mpr (hcomm ?_)
      rw [hφ''y]
      exact mem_centralizer_singleton_iff.mp (hRy hu)
    · apply Subgroup.map_injective hφ''
      have hRm : (R.comap φ'').map φ'' = R := Subgroup.map_comap_eq_self (fun x hx => by
        obtain ⟨c, hc⟩ := hrange x (hRL' hx)
        exact ⟨c, hc⟩)
      rw [Subgroup.map_commutator, hRm, hRperf]
  intro s hs
  rw [mem_centralizer_iff]
  intro r hr
  obtain ⟨c, rfl⟩ := hrange s (hSL' hs)
  obtain ⟨d, rfl⟩ := hrange r (hRL' hr)
  have h := mem_centralizer_iff.mp (hS' (show c ∈ S.comap φ'' from hs)) d hr
  rw [← map_mul, ← map_mul, h]

end Transport

end CFSG.SeitzReduction.OmegaPilot
