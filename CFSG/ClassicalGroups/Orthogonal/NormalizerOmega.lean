module

public import CFSG.LargeExtraspecial.O62Normalizer
public import CFSG.ClassicalGroups.Orthogonal.Matrix

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ClassicalGroups.Orthogonal

open Module QuadraticMap Matrix CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Literature.FSmith

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

private lemma mem_orthogonalGroup_of_maps_to {g : V ≃ₗ[ZMod 2] V}
    (hS : ∀ s, s ≠ 0 → Q s = 0 → Q (g s) = 0)
    (hN : ∀ n, Q n = 1 → Q (g n) = 1) : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  by_cases hv : v = 0
  · simp [hv]
  · rcases zmod2_eq_zero_or_eq_one (Q v) with h | h
    · rw [h]; exact hS v hv h
    · rw [h]; exact hN v h

private lemma false_of_const_on_nonzero {c : ZMod 2} (h : ∀ v, v ≠ 0 → Q v = c) {e e' : V}
    (he : Q e = 0) (he0 : e ≠ 0) (he' : Q e' = 1) (he'0 : e' ≠ 0) : False := by
  have h1 := h e he0
  have h2 := h e' he'0
  rw [he] at h1
  rw [he'] at h2
  rw [← h2] at h1
  exact zero_ne_one h1

private lemma false_of_map_add_eq_one (P P' : HypPair Q) (hPP' : P.Orth P')
    {g : V ≃ₗ[ZMod 2] V} (h : ∀ v, v ≠ 0 → Q (g v) + Q v = 1) : False := by
  let f : QuadraticForm (ZMod 2) V := Q.comp g.toLinearMap + Q
  have hf : ∀ v, f v = Q (g v) + Q v := by
    intro v
    simp [f]
  have hf1 : ∀ v, v ≠ 0 → f v = 1 := by
    intro v hv
    rw [hf v, h v hv]
  have hQef : Q (P.e + P.f) = 1 := by
    rw [QuadraticMap.map_add Q, P.Q_e, P.Q_f, P.polar_ef, zero_add, zero_add]
  have hPef : P.e + P.f ≠ 0 := by
    intro h0
    rw [h0, QuadraticMap.map_zero] at hQef
    exact zero_ne_one hQef
  have hPee : P.e + P'.e ≠ 0 := by
    have h1 : polar Q P'.f (P.e + P'.e) = 1 := by
      rw [polar_add_right, show polar Q P'.f P.e = 0 by rw [polar_comm, hPP'.ef],
        P'.polar_fe, zero_add]
    intro h0
    rw [h0, polar_zero_right] at h1
    exact zero_ne_one h1
  have hPfe : P.f + P'.e ≠ 0 := by
    have h1 : polar Q P'.f (P.f + P'.e) = 1 := by
      rw [polar_add_right, show polar Q P'.f P.f = 0 by rw [polar_comm, hPP'.ff],
        P'.polar_fe, zero_add]
    intro h0
    rw [h0, polar_zero_right] at h1
    exact zero_ne_one h1
  have hPefe : P.e + (P.f + P'.e) ≠ 0 := by
    have h1 : polar Q P'.f (P.e + (P.f + P'.e)) = 1 := by
      rw [polar_add_right, polar_add_right,
        show polar Q P'.f P.e = 0 by rw [polar_comm, hPP'.ef],
        show polar Q P'.f P.f = 0 by rw [polar_comm, hPP'.ff],
        P'.polar_fe, zero_add, zero_add]
    intro h0
    rw [h0, polar_zero_right] at h1
    exact zero_ne_one h1
  have key : ∀ w : V, w ≠ 0 → P.e + w ≠ 0 → polar f P.e w = 1 := by
    intro w hw hPew
    have hm := QuadraticMap.map_add f P.e w
    rw [hf1 P.e P.e_ne_zero, hf1 w hw, hf1 (P.e + w) hPew] at hm
    rw [zmod2_add_self, zero_add] at hm
    exact hm.symm
  have hp₁ : polar f P.e P.f = 1 := key P.f P.f_ne_zero hPef
  have hp₂ : polar f P.e P'.e = 1 := key P'.e P'.e_ne_zero hPee
  have hp : polar f P.e (P.f + P'.e) = 1 := key (P.f + P'.e) hPfe hPefe
  rw [QuadraticMap.polar_add_right] at hp
  rw [hp₁, hp₂, zmod2_add_self] at hp
  exact zero_ne_one hp

theorem mem_orthogonalGroup_of_normalizes_omegaGroup (hQ : Q.polarBilin.Nondegenerate)
    (h5 : 5 ≤ finrank (ZMod 2) V) {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ x ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ,
      g * x * g⁻¹ ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  obtain ⟨P₁, P₂, h₁₂, -, -⟩ := CFSG.LargeExtraspecial.S45Q.exists_two_hypPairs hQ h5
  have hef : Q (P₁.e + P₁.f) = 1 := by
    rw [QuadraticMap.map_add Q, P₁.Q_e, P₁.Q_f, P₁.polar_ef, zero_add, zero_add]
  have hef0 : P₁.e + P₁.f ≠ 0 := by
    intro h
    rw [h, QuadraticMap.map_zero] at hef
    exact zero_ne_one hef
  set cS : ZMod 2 := Q (g P₁.e) with hcS
  set cN : ZMod 2 := Q (g (P₁.e + P₁.f)) with hcN
  have hS : ∀ s, s ≠ 0 → Q s = 0 → Q (g s) = cS := by
    intro s hs0 hs
    exact (CFSG.LargeExtraspecial.O62.map_apply_eq_of_normalizes hQ h5 hg P₁.e_ne_zero hs0
      (by rw [P₁.Q_e, hs])).trans hcS.symm
  have hN : ∀ n, Q n = 1 → Q (g n) = cN := by
    intro n hn
    have hn0 : n ≠ 0 := by
      intro h
      rw [h, QuadraticMap.map_zero] at hn
      exact zero_ne_one hn
    exact (CFSG.LargeExtraspecial.O62.map_apply_eq_of_normalizes hQ h5 hg hef0 hn0
      (by rw [hef, hn])).trans hcN.symm
  rcases eq_or_ne cS cN with hc | hc
  · exfalso
    refine false_of_const_on_nonzero (c := cN) ?_ P₁.Q_e P₁.e_ne_zero hef hef0
    intro y hy
    have hx0 : g⁻¹ y ≠ 0 := by
      intro h0
      exact hy (by simpa using congrArg g h0)
    rcases zmod2_eq_zero_or_eq_one (Q (g⁻¹ y)) with h | h
    · have h1 := hS (g⁻¹ y) hx0 h
      simpa [hc] using h1
    · have h1 := hN (g⁻¹ y) h
      simpa using h1
  · rcases zmod2_eq_zero_or_eq_one cS with hS0 | hS1 <;>
      rcases zmod2_eq_zero_or_eq_one cN with hN0 | hN1
    · exfalso
      exact absurd (hS0.trans hN0.symm) hc
    · exact mem_orthogonalGroup_of_maps_to
        (fun s hs0 hs => by rw [hS s hs0 hs, hS0])
        (fun n hn => by rw [hN n hn, hN1])
    · exfalso
      refine false_of_map_add_eq_one (g := g) P₁ P₂ h₁₂ fun v hv => ?_
      rcases zmod2_eq_zero_or_eq_one (Q v) with h | h
      · rw [hS v hv h, hS1, h]; simp
      · rw [hN v h, hN0, h]; simp
    · exfalso
      exact absurd (hS1.trans hN1.symm) hc

theorem mem_orthogonalGroup_of_normalizes_commutator (hQ : Q.polarBilin.Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ x ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      g * x * g⁻¹ ∈
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [commutator_orthogonalGroup_eq_omegaGroup hQ h6] at hg
  exact mem_orthogonalGroup_of_normalizes_omegaGroup hQ (by omega) hg

theorem isometry_of_normalizes_statedOmega {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)} {Q₀ : (ι → ZMod 2) → ZMod 2} (hQ₀ : ⇑Q = Q₀)
    (hQ : Q.polarBilin.Nondegenerate) (h6 : 6 ≤ Fintype.card ι) {h : GL ι (ZMod 2)}
    (hh : ∀ x ∈ StatedOmega Q₀, h * x * h⁻¹ ∈ StatedOmega Q₀) (v : ι → ZMod 2) :
    Q₀ ((h : Matrix ι ι (ZMod 2)) *ᵥ v) = Q₀ v := by
  set g : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) := toLinEquiv ι (ZMod 2) h with hg
  have hfr : finrank (ZMod 2) (ι → ZMod 2) = Fintype.card ι :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine mem_orthogonalGroup_of_normalizes_commutator hQ (by rw [hfr]; exact h6) fun y hy => ?_
    have hx : (toLinEquiv ι (ZMod 2)).symm y ∈ StatedOmega Q₀ := by
      rw [statedOmega_eq_comap hQ₀, Subgroup.mem_comap]
      simpa using hy
    have hmem := hh _ hx
    rw [statedOmega_eq_comap hQ₀, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at hmem
    have key : toLinEquiv ι (ZMod 2) (h * ((toLinEquiv ι (ZMod 2)).symm y) * h⁻¹) =
        g * y * g⁻¹ := by
      simp [hg]
    rwa [key] at hmem
  have hv : (h : Matrix ι ι (ZMod 2)) *ᵥ v = g v := by
    rw [hg, toLinEquiv_apply]
  calc Q₀ ((h : Matrix ι ι (ZMod 2)) *ᵥ v)
      = Q₀ (g v) := by rw [hv]
    _ = Q (g v) := (congrFun hQ₀ (g v)).symm
    _ = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO v
    _ = Q₀ v := congrFun hQ₀ v

end CFSG.ClassicalGroups.Orthogonal
