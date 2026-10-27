module

public import CFSG.ClassicalInvolution.RouteD.TWS8Geo1
public import CFSG.ClassicalInvolution.Asc77.AscE189OrthV
public import CFSG.ClassicalGroups.Orthogonal.Restrict

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalGroups.Orthogonal.Small (stabSub)
open CFSG.ClassicalInvolution.ModelFacts.Orth15
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Stable

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem exists_map_ne_zero_of_nondeg {C : Submodule F V} (hC : PolarNondegOn Q C) {c : V}
    (hc : c ∈ C) (hc0 : c ≠ 0) : ∃ v ∈ C, Q v ≠ 0 := by
  obtain ⟨y, hy, hcy⟩ := hC.exists_polar_ne_zero hc hc0
  by_contra hcon
  push Not at hcon
  have h1 := hcon (c + y) (C.add_mem hc hy)
  rw [QuadraticMap.map_add Q, hcon c hc, hcon y hy] at h1
  exact hcy (by simpa using h1)

theorem eichler_smul_sub_self {u v : V} (hu : Q u = 0) (hv : polar Q u v = 0) (t : F) (b : V) :
    eichler Q u (t • v) b - b =
      (t * polar Q b u) • v - (t * polar Q b v + t * t * Q v * polar Q b u) • u := by
  have hv' : polar Q u (t • v) = 0 := by rw [polar_smul_right_eq, hv, mul_zero]
  rw [eichler_apply hu hv', polar_smul_right_eq, QuadraticMap.map_smul, smul_eq_mul]
  module

theorem mem_of_polar_ne_zero (h2 : (2 : F) ≠ 0) {u v₀ a : V} {N : Submodule F V} (hu : Q u = 0)
    (hv₀ : polar Q u v₀ = 0) (hQv₀ : Q v₀ ≠ 0)
    (hN : ∀ t : F, ∀ b ∈ N, eichler Q u (t • v₀) b ∈ N) (ha : a ∈ N) (hau : polar Q a u ≠ 0) :
    u ∈ N := by
  have m1 := N.sub_mem (hN 1 a ha) ha
  have m2 := N.sub_mem (hN 2 a ha) ha
  rw [eichler_smul_sub_self hu hv₀] at m1 m2
  have h3 := N.sub_mem m2 (N.smul_mem 2 m1)
  have h4 : (-(2 * Q v₀ * polar Q a u)) • u ∈ N := by
    convert h3 using 1
    module
  exact (Submodule.smul_mem_iff N
    (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero h2 hQv₀) hau))).mp h4

theorem mem_of_mem_C {u a v : V} {N : Submodule F V} (hu : Q u = 0) (hau : polar Q a u = 0)
    (hv : polar Q u v = 0) (hN : ∀ b ∈ N, eichler Q u v b ∈ N) (ha : a ∈ N)
    (hav : polar Q a v ≠ 0) : u ∈ N := by
  have m := N.sub_mem (hN a ha) ha
  have h1 : eichler Q u v a - a = (-(polar Q a v)) • u := by
    rw [eichler_apply hu hv, hau]
    module
  rw [h1] at m
  exact (Submodule.smul_mem_iff N (neg_ne_zero.mpr hav)).mp m

theorem to_all (h2 : (2 : F) ≠ 0) {u u' v₀ : V} {C N : Submodule F V} (hu' : Q u' = 0)
    (huu' : polar Q u u' = 1) (hC : ∀ x ∈ C, polar Q x u = 0 ∧ polar Q x u' = 0)
    (hv₀ : v₀ ∈ C) (hQv₀ : Q v₀ ≠ 0) (hN : ∀ v ∈ C, ∀ b ∈ N, eichler Q u' v b ∈ N)
    (huN : u ∈ N) : u' ∈ N ∧ ∀ v ∈ C, v ∈ N := by
  have key : ∀ v ∈ C, ∀ t : F, eichler Q u' (t • v) u - u ∈ N ∧
      eichler Q u' (t • v) u - u = t • v - (t * t * Q v) • u' := by
    intro v hv t
    have hv' : polar Q u' v = 0 := by rw [polar_comm]; exact (hC v hv).2
    have huv : polar Q u v = 0 := by rw [polar_comm]; exact (hC v hv).1
    refine ⟨N.sub_mem (hN (t • v) (C.smul_mem t hv) u huN) huN, ?_⟩
    rw [eichler_smul_sub_self hu' hv', huu', huv]
    module
  have hf : u' ∈ N := by
    have m1 := (key v₀ hv₀ 1).1
    have m2 := (key v₀ hv₀ 2).1
    rw [(key v₀ hv₀ 1).2] at m1
    rw [(key v₀ hv₀ 2).2] at m2
    have h3 := N.sub_mem m2 (N.smul_mem 2 m1)
    have h4 : (-(2 * Q v₀)) • u' ∈ N := by
      convert h3 using 1
      module
    exact (Submodule.smul_mem_iff N (neg_ne_zero.mpr (mul_ne_zero h2 hQv₀))).mp h4
  refine ⟨hf, fun v hv => ?_⟩
  have m1 := (key v hv 1).1
  rw [(key v hv 1).2] at m1
  have h5 := N.add_mem m1 (N.smul_mem (1 * 1 * Q v) hf)
  convert h5 using 1
  module

theorem stable_eq (h2 : (2 : F) ≠ 0) (P : HypPair Q) {C N : Submodule F V}
    (hC : ∀ x ∈ C, polar Q x P.e = 0 ∧ polar Q x P.f = 0) (hCnd : PolarNondegOn Q C)
    (hCne : ∃ c ∈ C, c ≠ 0)
    (hN : ∀ v ∈ C, ∀ b ∈ N, eichler Q P.e v b ∈ N ∧ eichler Q P.f v b ∈ N)
    {a : V} (haN : a ∈ N) (ha0 : a ≠ 0)
    (haC : polar Q a P.e ≠ 0 ∨ polar Q a P.f ≠ 0 ∨ a ∈ C) :
    P.e ∈ N ∧ P.f ∈ N ∧ ∀ v ∈ C, v ∈ N := by
  obtain ⟨c₀, hc₀, hc₀0⟩ := hCne
  obtain ⟨v₀, hv₀, hQv₀⟩ := exists_map_ne_zero_of_nondeg hCnd hc₀ hc₀0
  have hev : ∀ v ∈ C, polar Q P.e v = 0 := fun v hv => by
    rw [polar_comm]; exact (hC v hv).1
  have hfv : ∀ v ∈ C, polar Q P.f v = 0 := fun v hv => by
    rw [polar_comm]; exact (hC v hv).2
  have hone : P.e ∈ N ∨ P.f ∈ N := by
    rcases haC with h | h | h
    · left
      exact mem_of_polar_ne_zero h2 P.Q_e (hev v₀ hv₀) hQv₀
        (fun t b hb => (hN (t • v₀) (C.smul_mem t hv₀) b hb).1) haN h
    · right
      exact mem_of_polar_ne_zero h2 P.Q_f (hfv v₀ hv₀) hQv₀
        (fun t b hb => (hN (t • v₀) (C.smul_mem t hv₀) b hb).2) haN h
    · left
      obtain ⟨v, hv, hav⟩ := hCnd.exists_polar_ne_zero h ha0
      exact mem_of_mem_C P.Q_e (hC a h).1 (hev v hv) (fun b hb => (hN v hv b hb).1) haN hav
  rcases hone with he | hf
  · obtain ⟨hf, hall⟩ := to_all h2 P.Q_f P.polar_ef hC hv₀ hQv₀
      (fun v hv b hb => (hN v hv b hb).2) he
    exact ⟨he, hf, hall⟩
  · obtain ⟨he, hall⟩ := to_all (u := P.f) (u' := P.e) h2 P.Q_e P.polar_fe
      (fun x hx => ⟨(hC x hx).2, (hC x hx).1⟩) hv₀ hQv₀ (fun v hv b hb => (hN v hv b hb).1) hf
    exact ⟨he, hf, hall⟩

end Stable

section Mix

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [FiniteDimensional F V]

theorem La_mem_stabE (fr : OFrame Q) (A : SL(2, F)) : fr.La A ∈ stabE fr := by
  refine ⟨fr.La_mem_elementaryGroup A, mem_stabSub_of_mapsTo fun x hx => ?_⟩
  obtain ⟨X, rfl⟩ := hx
  rw [Frame.La_apply_incl]
  exact incl_mem_wPlane fr _

@[expose] def torus (c : F) (hc : c ≠ 0) : SL(2, F) :=
  ⟨!![c, 0; 0, c⁻¹], by simp [Matrix.det_fin_two, hc]⟩

omit [FiniteDimensional F V] in
theorem La_torus_e₁ (fr : OFrame Q) {c : F} (hc : c ≠ 0) :
    fr.La (torus c hc) fr.e₁ = c • fr.e₁ := by
  have h1 : fr.incl !![1, 0; 0, 0] = fr.e₁ := by simp [Frame.incl_apply]
  rw [← h1, Frame.La_apply_incl, ← map_smul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torus]

def mixMod (fr : OFrame Q) (H : Subgroup (V ≃ₗ[F] V)) (hH : stabE fr ≤ H) : Submodule F V where
  carrier := {a | a ∈ fr.perp ∧ eichler Q fr.e₁ a ∈ H}
  add_mem' := by
    rintro a b ⟨ha, haH⟩ ⟨hb, hbH⟩
    refine ⟨fr.perp.add_mem ha hb, ?_⟩
    rw [← eichler_mul (polar_wPlane_perp ha (e₁_mem_wPlane fr))
      (polar_wPlane_perp hb (e₁_mem_wPlane fr))]
    exact H.mul_mem haH hbH
  zero_mem' := ⟨fr.perp.zero_mem, by rw [eichler_zero_right]; exact H.one_mem⟩
  smul_mem' := by
    rintro c a ⟨ha, haH⟩
    refine ⟨fr.perp.smul_mem c ha, ?_⟩
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, eichler_zero_right]
      exact H.one_mem
    · have hgH : fr.La (torus c hc) ∈ H := hH (La_mem_stabE fr _)
      have h1 := eichler_conj (fr.La_mem_orthogonalGroup (torus c hc)) fr.e₁ a
      rw [La_torus_e₁ fr hc, Frame.La_apply_of_coords_eq_zero _ _
        ((Frame.mem_perp_iff fr).mp ha), eichler_smul_left] at h1
      rw [← h1]
      exact H.mul_mem (H.mul_mem hgH haH) (H.inv_mem hgH)

theorem mem_mixMod {fr : OFrame Q} {H : Subgroup (V ≃ₗ[F] V)} {hH : stabE fr ≤ H} {a : V} :
    a ∈ mixMod fr H hH ↔ a ∈ fr.perp ∧ eichler Q fr.e₁ a ∈ H :=
  Iff.rfl

theorem eichler_mem_mixMod {fr : OFrame Q} {H : Subgroup (V ≃ₗ[F] V)} (hH : stabE fr ≤ H)
    {u v a : V} (hu : u ∈ fr.perp) (hQu : Q u = 0) (hv : v ∈ fr.perp) (huv : polar Q u v = 0)
    (ha : a ∈ mixMod fr H hH) : eichler Q u v a ∈ mixMod fr H hH := by
  have hg : eichler Q u v ∈ stabE fr :=
    ⟨eichler_mem_elementaryGroup Q u v, mem_stabSub_of_mapsTo fun x hx => by
      rw [eichler_apply_of_polar_eq_zero (polar_wPlane_perp hu hx) (polar_wPlane_perp hv hx)]
      exact hx⟩
  have hgH := hH hg
  have hge : eichler Q u v fr.e₁ = fr.e₁ :=
    eichler_apply_of_polar_eq_zero (polar_wPlane_perp hu (e₁_mem_wPlane fr))
      (polar_wPlane_perp hv (e₁_mem_wPlane fr))
  obtain ⟨ha1, ha2⟩ := mem_mixMod.mp ha
  refine mem_mixMod.mpr ⟨?_, ?_⟩
  · rw [eichler_apply hQu huv]
    exact fr.perp.sub_mem (fr.perp.add_mem ha1 (fr.perp.smul_mem _ hv)) (fr.perp.smul_mem _ hu)
  · have h1 := eichler_conj (elementaryGroup_le_orthogonalGroup Q hg.1) fr.e₁ a
    rw [hge] at h1
    rw [← h1]
    exact H.mul_mem (H.mul_mem hgH ha2) (H.inv_mem hgH)

variable [Finite F]

omit [FiniteDimensional F V] [Finite F] in
theorem polarNondegOn_wPlane (hQ : (polarBilin Q).Nondegenerate) (fr : OFrame Q) :
    PolarNondegOn Q (wPlane fr) :=
  CFSG.ClassicalInvolution.Asc77.polarNondegOn_of_isCompl hQ fr.isCompl_span_perp
    (fun _ hx _ hy => polar_wPlane_perp hy hx)

omit [FiniteDimensional F V] [Finite F] in
theorem polarNondegOn_perp' (hQ : (polarBilin Q).Nondegenerate) (fr : OFrame Q) :
    PolarNondegOn Q fr.perp :=
  CFSG.ClassicalInvolution.Asc77.polarNondegOn_of_isCompl hQ fr.isCompl_span_perp.symm
    (fun _ hx _ hy => polar_perp_wPlane hx hy)

theorem eichler_mem_of_mixed (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (fr : OFrame Q) {H : Subgroup (V ≃ₗ[F] V)} (hH : stabE fr ≤ H)
    (h3 : 3 ≤ Module.finrank F fr.perp) {a : V} (ha : a ∈ fr.perp) (ha0 : a ≠ 0)
    (haH : eichler Q fr.e₁ a ∈ H) : ∀ w, polar Q fr.e₁ w = 0 → eichler Q fr.e₁ w ∈ H := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hnd := polarNondegOn_perp' hQ fr
  obtain ⟨P, hPe, hPf⟩ := CFSG.ClassicalInvolution.Asc77.exists_hypPair_le hodd hnd h3
  have hCnd : PolarNondegOn Q (fr.perp ⊓ P.perp) := hnd.inf_perp P hPe hPf
  have hdim := CFSG.ClassicalInvolution.Asc77.finrank_inf_perp_hypPair hQ P hPe hPf
  have hCne : ∃ c ∈ fr.perp ⊓ P.perp, c ≠ 0 := by
    have hpos : 0 < Module.finrank F ↥(fr.perp ⊓ P.perp) := by omega
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩
  have hC : ∀ x ∈ fr.perp ⊓ P.perp, polar Q x P.e = 0 ∧ polar Q x P.f = 0 := by
    intro x hx
    obtain ⟨h1, h2'⟩ := HypPair.mem_perp.mp (Submodule.mem_inf.mp hx).2
    exact ⟨by rw [polar_comm]; exact h1, by rw [polar_comm]; exact h2'⟩
  have hN : ∀ v ∈ fr.perp ⊓ P.perp, ∀ b ∈ mixMod fr H hH,
      eichler Q P.e v b ∈ mixMod fr H hH ∧ eichler Q P.f v b ∈ mixMod fr H hH := by
    intro v hv b hb
    have hvp := (Submodule.mem_inf.mp hv).1
    obtain ⟨h1, h2'⟩ := HypPair.mem_perp.mp (Submodule.mem_inf.mp hv).2
    exact ⟨eichler_mem_mixMod hH hPe P.Q_e hvp h1 hb, eichler_mem_mixMod hH hPf P.Q_f hvp h2' hb⟩
  have haN : a ∈ mixMod fr H hH := mem_mixMod.mpr ⟨ha, haH⟩
  have haC : polar Q a P.e ≠ 0 ∨ polar Q a P.f ≠ 0 ∨ a ∈ fr.perp ⊓ P.perp := by
    by_cases h1 : polar Q a P.e = 0
    · by_cases h2' : polar Q a P.f = 0
      · right
        right
        refine Submodule.mem_inf.mpr ⟨ha, HypPair.mem_perp.mpr ⟨?_, ?_⟩⟩
        · rw [polar_comm]; exact h1
        · rw [polar_comm]; exact h2'
      · right
        left
        exact h2'
    · left
      exact h1
  obtain ⟨heN, hfN, hCN⟩ := stable_eq h2 P hC hCnd hCne hN haN ha0 haC
  have hperp : ∀ x ∈ fr.perp, x ∈ mixMod fr H hH := by
    intro x hx
    have hxproj : P.proj x ∈ fr.perp ⊓ P.perp := by
      refine ⟨?_, P.proj_mem_perp x⟩
      rw [HypPair.proj]
      exact fr.perp.sub_mem (fr.perp.sub_mem hx (fr.perp.smul_mem _ hPe))
        (fr.perp.smul_mem _ hPf)
    rw [P.eq_add_proj x]
    exact (mixMod fr H hH).add_mem ((mixMod fr H hH).add_mem ((mixMod fr H hH).smul_mem _ heN)
      ((mixMod fr H hH).smul_mem _ hfN)) (hCN _ hxproj)
  intro w hw
  have hwAperp : w - fr.incl (fr.coords w) ∈ fr.perp := sub_incl_mem_perp fr w
  have hwWe : polar Q fr.e₁ (fr.incl (fr.coords w)) = 0 := by
    have h1 : polar Q fr.e₁ (w - fr.incl (fr.coords w)) = 0 :=
      polar_wPlane_perp hwAperp (e₁_mem_wPlane fr)
    rw [polar_sub_right, hw, zero_sub, neg_eq_zero] at h1
    exact h1
  have hsplit : w = fr.incl (fr.coords w) + (w - fr.incl (fr.coords w)) := by abel
  have hE1 : eichler Q fr.e₁ (fr.incl (fr.coords w)) ∈ H :=
    hH (eichler_mem_stabE fr (e₁_mem_wPlane fr) (incl_mem_wPlane fr _))
  have hE2 : eichler Q fr.e₁ (w - fr.incl (fr.coords w)) ∈ H :=
    (mem_mixMod.mp (hperp _ hwAperp)).2
  rw [hsplit, ← eichler_mul hwWe (polar_wPlane_perp hwAperp (e₁_mem_wPlane fr))]
  exact H.mul_mem hE1 hE2

omit [Finite F] in
theorem exists_stabE_apply_eq (hQ : (polarBilin Q).Nondegenerate) (fr : OFrame Q) {x y : V}
    (hx : x ∈ wPlane fr) (hy : y ∈ wPlane fr) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : Q x = Q y) :
    ∃ g ∈ stabE fr, g x = y := by
  have he₂ : fr.e₂ ∈ wPlane fr := ⟨!![0, -1; 0, 0], by simp [Frame.incl_apply]⟩
  have hf₂ : fr.f₂ ∈ wPlane fr := ⟨!![0, 0; 1, 0], by simp [Frame.incl_apply]⟩
  obtain ⟨g, hg, hgx, hgW, -⟩ := exists_mem_elementaryGroup_apply_eq_of_mem
    (polarNondegOn_wPlane hQ fr) fr.orth (e₁_mem_wPlane fr) (f₁_mem_wPlane fr) he₂ hf₂ hx hy hx0
    hy0 hxy
  exact ⟨g, ⟨hg, mem_stabSub_of_mapsTo hgW⟩, hgx⟩

theorem elementaryGroup_le_of_mixed (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (fr : OFrame Q) {H : Subgroup (V ≃ₗ[F] V)} (hH : stabE fr ≤ H)
    (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (h3 : 3 ≤ Module.finrank F fr.perp)
    {a : V} (ha : a ∈ fr.perp) (ha0 : a ≠ 0) (haH : eichler Q fr.e₁ a ∈ H) :
    elementaryGroup Q ≤ H := by
  have hU := eichler_mem_of_mixed hodd hQ fr hH h3 ha ha0 haH
  have he0 : fr.e₁ ≠ 0 := fun h => by
    have := fr.polar_e₁_f₁
    rw [h] at this
    simp at this
  have hf0 : fr.f₁ ≠ 0 := fun h => by
    have := fr.polar_e₁_f₁
    rw [h] at this
    simp at this
  obtain ⟨g, hg, hge⟩ := exists_stabE_apply_eq hQ fr (e₁_mem_wPlane fr) (f₁_mem_wPlane fr) he0
    hf0 (by rw [fr.Q_e₁, fr.Q_f₁])
  exact elementaryGroup_le_of_subgroup' (P := fr.P) H hQ hHO hU
    ⟨g, hH hg, 1, one_ne_zero, by rw [one_smul]; exact hge⟩

end Mix

end CFSG.ClassicalInvolution.RouteD.TWS8
