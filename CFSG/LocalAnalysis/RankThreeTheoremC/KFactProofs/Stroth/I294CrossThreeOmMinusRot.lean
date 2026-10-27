module

public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmMinus

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] noncomputable def rotMap (Q : QuadraticForm K V) (c : K) (u v : V) : V →ₗ[K] V :=
  LinearMap.id - c⁻¹ • ((polarBilin Q (u + v)).smulRight u + (polarBilin Q v).smulRight v)

theorem rotMap_apply (Q : QuadraticForm K V) (c : K) (u v x : V) :
    rotMap Q c u v x = x - c⁻¹ • (polar Q (u + v) x • u + polar Q v x • v) := by
  simp [rotMap, polarBilin_apply_apply]

structure IsRotPair (Q : QuadraticForm K V) (c : K) (u v : V) : Prop where
  c_ne : c ≠ 0
  Q_u : Q u = c
  Q_v : Q v = c
  polar_uv : polar Q u v = -c

namespace IsRotPair

variable {Q : QuadraticForm K V} {c : K} {u v : V} (h : IsRotPair Q c u v)
include h

theorem polar_vu : polar Q v u = -c := by rw [polar_comm]; exact h.polar_uv

theorem polar_uu : polar Q u u = 2 * c := by rw [polar_self_eq_two_mul, h.Q_u]

theorem polar_vv : polar Q v v = 2 * c := by rw [polar_self_eq_two_mul, h.Q_v]

theorem rotMap_apply' (x : V) :
    rotMap Q c u v x =
      x - c⁻¹ • ((polar Q u x + polar Q v x) • u + polar Q v x • v) := by
  rw [rotMap_apply, polar_add_left]

theorem rotMap_u : rotMap Q c u v u = v := by
  rw [h.rotMap_apply', h.polar_uu, h.polar_vu]
  have := h.c_ne
  match_scalars <;> field_simp <;> ring

theorem polar_u_rotMap (x : V) :
    polar Q u (rotMap Q c u v x) = -polar Q u x - polar Q v x := by
  rw [h.rotMap_apply', polar_sub_right, polar_smul_right, polar_add_right, polar_smul_right,
    polar_smul_right, h.polar_uu, h.polar_uv]
  simp only [smul_eq_mul]
  have := h.c_ne
  field_simp
  ring

theorem polar_v_rotMap (x : V) :
    polar Q v (rotMap Q c u v x) = polar Q u x := by
  rw [h.rotMap_apply', polar_sub_right, polar_smul_right, polar_add_right, polar_smul_right,
    polar_smul_right, h.polar_vu, h.polar_vv]
  simp only [smul_eq_mul]
  have := h.c_ne
  field_simp
  ring

theorem rotMap_of_perp {y : V} (hu : polar Q u y = 0) (hv : polar Q v y = 0) :
    rotMap Q c u v y = y := by
  rw [h.rotMap_apply', hu, hv]
  simp

theorem Q_rotMap (x : V) : Q (rotMap Q c u v x) = Q x := by
  have hexp : ∀ (p q : K), Q (x - (p • u + q • v)) = Q x + p ^ 2 * c + q ^ 2 * c +
      p * q * -c - p * polar Q u x - q * polar Q v x := by
    intro p q
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, QuadraticMap.map_add Q,
      QuadraticMap.map_smul, QuadraticMap.map_smul, polar_neg_right, polar_add_right,
      polar_smul_right, polar_smul_right, polar_smul_left, polar_smul_right, h.Q_u, h.Q_v,
      h.polar_uv, polar_comm Q x u, polar_comm Q x v]
    simp only [smul_eq_mul]
    ring
  have h1 : rotMap Q c u v x =
      x - ((c⁻¹ * (polar Q u x + polar Q v x)) • u + (c⁻¹ * polar Q v x) • v) := by
    rw [h.rotMap_apply', smul_add, smul_smul, smul_smul]
  rw [h1, hexp]
  have := h.c_ne
  field_simp
  ring

theorem rotMap_pow_three (x : V) :
    rotMap Q c u v (rotMap Q c u v (rotMap Q c u v x)) = x := by
  have hy1 := h.rotMap_apply' x
  have hα₁ := h.polar_u_rotMap x
  have hβ₁ := h.polar_v_rotMap x
  have hy2 := h.rotMap_apply' (rotMap Q c u v x)
  have hα₂ := h.polar_u_rotMap (rotMap Q c u v x)
  have hβ₂ := h.polar_v_rotMap (rotMap Q c u v x)
  have hy3 := h.rotMap_apply' (rotMap Q c u v (rotMap Q c u v x))
  rw [hy3, hα₂, hβ₂, hy2, hα₁, hβ₁, hy1]
  module

@[expose] noncomputable def rotAut : V ≃ₗ[K] V :=
  LinearEquiv.ofLinear (rotMap Q c u v) (rotMap Q c u v ∘ₗ rotMap Q c u v)
    (LinearMap.ext fun x => h.rotMap_pow_three x) (LinearMap.ext fun x => h.rotMap_pow_three x)

theorem rotAut_apply (x : V) : h.rotAut x = rotMap Q c u v x := rfl

theorem rotAut_mem_orthogonalGroup : h.rotAut ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  rw [h.rotAut_apply]
  exact h.Q_rotMap x

theorem rotAut_pow_three : h.rotAut ^ 3 = 1 := by
  refine LinearEquiv.ext fun x => ?_
  rw [pow_succ, pow_succ, pow_one]
  simp only [LinearEquiv.mul_apply, h.rotAut_apply, h.rotMap_pow_three]
  rfl

theorem rotAut_u : h.rotAut u = v := h.rotMap_u

theorem rotAut_ne (h3 : (3 : K) ≠ 0) : h.rotAut u ≠ u := by
  intro hu
  rw [h.rotAut_u] at hu
  have h1 := congrArg (polar Q u) hu
  rw [h.polar_uv, h.polar_uu] at h1
  have h3' : (3 : K) * c = 0 := by linear_combination -h1
  exact h.c_ne ((mul_eq_zero.mp h3').resolve_left h3)

end IsRotPair

section Commute

variable {Q : QuadraticForm K V} {c c' : K} {u v u' v' : V}

theorem polar_rotMap_of_perp (c : K) (u v y : V) (hu : polar Q y u = 0) (hv : polar Q y v = 0)
    (x : V) : polar Q y (rotMap Q c u v x) = polar Q y x := by
  rw [rotMap_apply, polar_sub_right, polar_smul_right, polar_add_right, polar_smul_right,
    polar_smul_right, hu, hv]
  simp

theorem rotMap_comm_rotMap (huu : polar Q u u' = 0) (huv : polar Q u v' = 0)
    (hvu : polar Q v u' = 0) (hvv : polar Q v v' = 0) (x : V) :
    rotMap Q c u v (rotMap Q c' u' v' x) = rotMap Q c' u' v' (rotMap Q c u v x) := by
  have h1 : polar Q (u + v) (rotMap Q c' u' v' x) = polar Q (u + v) x :=
    polar_rotMap_of_perp c' u' v' (u + v) (by rw [polar_add_left, huu, hvu, add_zero])
      (by rw [polar_add_left, huv, hvv, add_zero]) x
  have h2 : polar Q v (rotMap Q c' u' v' x) = polar Q v x :=
    polar_rotMap_of_perp c' u' v' v hvu hvv x
  have h3 : polar Q (u' + v') (rotMap Q c u v x) = polar Q (u' + v') x :=
    polar_rotMap_of_perp c u v (u' + v') (by rw [polar_add_left, polar_comm Q u' u, polar_comm Q v' u,
      huu, huv, add_zero]) (by rw [polar_add_left, polar_comm Q u' v, polar_comm Q v' v, hvu, hvv,
      add_zero]) x
  have h4 : polar Q v' (rotMap Q c u v x) = polar Q v' x :=
    polar_rotMap_of_perp c u v v' (by rw [polar_comm Q v' u]; exact huv)
      (by rw [polar_comm Q v' v]; exact hvv) x
  rw [rotMap_apply Q c u v (rotMap Q c' u' v' x), rotMap_apply Q c' u' v' (rotMap Q c u v x), h1, h2,
    h3, h4, rotMap_apply Q c' u' v' x, rotMap_apply Q c u v x]
  module

theorem rotMap_comm_of_fix {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgu : g u = u) (hgv : g v = v) (x : V) :
    g (rotMap Q c u v x) = rotMap Q c u v (g x) := by
  have h1 : polar Q (u + v) (g x) = polar Q (u + v) x := by
    have := polar_map_of_mem hg (u + v) x
    rwa [map_add, hgu, hgv] at this
  have h2 : polar Q v (g x) = polar Q v x := by
    have := polar_map_of_mem hg v x
    rwa [hgv] at this
  rw [rotMap_apply, rotMap_apply, h1, h2, map_sub, map_smul, map_add, map_smul, map_smul, hgu, hgv]

theorem rotMap_comm_of_rot {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgu : g u = v) (hgv : g v = -u - v) (x : V) :
    g (rotMap Q c u v x) = rotMap Q c u v (g x) := by
  have hgg : g (g v) = u := by
    rw [hgv, map_sub, map_neg, hgu, hgv]
    abel
  have h1 : polar Q u (g x) = -polar Q u x - polar Q v x := by
    have := polar_map_of_mem hg (g v) x
    rw [hgg, hgv, polar_sub_left, polar_neg_left] at this
    exact this
  have h2 : polar Q v (g x) = polar Q u x := by
    have := polar_map_of_mem hg u x
    rwa [hgu] at this
  rw [rotMap_apply, rotMap_apply, polar_add_left Q u v (g x), polar_add_left Q u v x, h1, h2,
    map_sub, map_smul, map_add, map_smul, map_smul, hgu, hgv]
  module

@[expose] def RotMode (g : V ≃ₗ[K] V) (u v : V) : Prop :=
  (g u = u ∧ g v = v) ∨ (g u = v ∧ g v = -u - v)

theorem IsRotPair.rotAut_comm_rotAut (h : IsRotPair Q c u v) (h' : IsRotPair Q c' u' v')
    (huu : polar Q u u' = 0) (huv : polar Q u v' = 0) (hvu : polar Q v u' = 0)
    (hvv : polar Q v v' = 0) : h.rotAut * h'.rotAut = h'.rotAut * h.rotAut :=
  LinearEquiv.ext fun x => rotMap_comm_rotMap huu huv hvu hvv x

theorem IsRotPair.rotAut_comm_of_mode (h : IsRotPair Q c u v) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hm : RotMode g u v) :
    h.rotAut * g = g * h.rotAut := by
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h.rotAut_apply, h.rotAut_apply]
  rcases hm with ⟨hgu, hgv⟩ | ⟨hgu, hgv⟩
  · exact (rotMap_comm_of_fix hg hgu hgv x).symm
  · exact (rotMap_comm_of_rot hg hgu hgv x).symm

theorem IsRotPair.rotAut_of_perp (h : IsRotPair Q c u v) {y : V} (hu : polar Q u y = 0)
    (hv : polar Q v y = 0) : h.rotAut y = y :=
  h.rotMap_of_perp hu hv

theorem RotMode.polar_perp {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hm : RotMode g u v) {x : V} (h1 : polar Q u x = 0) (h2 : polar Q v x = 0) :
    polar Q u (g x) = 0 ∧ polar Q v (g x) = 0 := by
  rcases hm with ⟨hgu, hgv⟩ | ⟨hgu, hgv⟩
  · have e1 := polar_map_of_mem hg u x
    have e2 := polar_map_of_mem hg v x
    rw [hgu] at e1
    rw [hgv] at e2
    exact ⟨e1.trans h1, e2.trans h2⟩
  · have hgg : g (g v) = u := by
      rw [hgv, map_sub, map_neg, hgu, hgv]
      abel
    have e1 := polar_map_of_mem hg (g v) x
    have e2 := polar_map_of_mem hg u x
    rw [hgg, hgv, polar_sub_left, polar_neg_left, h1, h2] at e1
    rw [hgu] at e2
    exact ⟨by rw [e1]; ring, e2.trans h1⟩

@[expose] def perp2 (Q : QuadraticForm K V) (u v : V) : Submodule K V :=
  LinearMap.ker (polarBilin Q u) ⊓ LinearMap.ker (polarBilin Q v)

theorem mem_perp2 {x : V} : x ∈ perp2 Q u v ↔ polar Q u x = 0 ∧ polar Q v x = 0 := by
  simp [perp2, polarBilin_apply_apply]

end Commute

section Complement

variable {Q : QuadraticForm K V} {c : K} {u v : V}

@[expose] noncomputable def rotProj (Q : QuadraticForm K V) (c : K) (u v x : V) : V :=
  ((3 * c)⁻¹ * (2 * polar Q u x + polar Q v x)) • u +
    ((3 * c)⁻¹ * (polar Q u x + 2 * polar Q v x)) • v

theorem IsRotPair.sub_rotProj_mem_perp2 (h : IsRotPair Q c u v) (h3 : (3 : K) ≠ 0) (x : V) :
    x - rotProj Q c u v x ∈ perp2 Q u v := by
  rw [mem_perp2]
  have hc := h.c_ne
  constructor
  · rw [polar_sub_right, rotProj, polar_add_right, polar_smul_right, polar_smul_right, h.polar_uu,
      h.polar_uv]
    simp only [smul_eq_mul]
    field_simp
    ring
  · rw [polar_sub_right, rotProj, polar_add_right, polar_smul_right, polar_smul_right, h.polar_vu,
      h.polar_vv]
    simp only [smul_eq_mul]
    field_simp
    ring

theorem rotProj_mem {S : Submodule K V} (hu : u ∈ S) (hv : v ∈ S) (x : V) :
    rotProj Q c u v x ∈ S :=
  S.add_mem (S.smul_mem _ hu) (S.smul_mem _ hv)

theorem IsRotPair.polarNondegOn_inf_perp2 (h : IsRotPair Q c u v) (h3 : (3 : K) ≠ 0)
    {S : Submodule K V} (hS : PolarNondegOn Q S) (hu : u ∈ S) (hv : v ∈ S) :
    PolarNondegOn Q (S ⊓ perp2 Q u v) := by
  intro y hy hy'
  rw [Submodule.mem_inf, mem_perp2] at hy
  apply hS y hy.1
  intro z hz
  have hmem : z - rotProj Q c u v z ∈ S ⊓ perp2 Q u v :=
    ⟨S.sub_mem hz (rotProj_mem hu hv z), h.sub_rotProj_mem_perp2 h3 z⟩
  have h1 := hy' _ hmem
  have hu' : polar Q y u = 0 := by rw [polar_comm]; exact hy.2.1
  have hv' : polar Q y v = 0 := by rw [polar_comm]; exact hy.2.2
  rw [polar_sub_right, rotProj, polar_add_right, polar_smul_right, polar_smul_right, hu', hv']
    at h1
  simpa using h1

theorem IsRotPair.finrank_inf_perp2 [FiniteDimensional K V] (h : IsRotPair Q c u v)
    (h3 : (3 : K) ≠ 0) {S : Submodule K V} (hu : u ∈ S) (hv : v ∈ S) :
    Module.finrank K (S ⊓ perp2 Q u v : Submodule K V) + 2 = Module.finrank K S := by
  have hc := h.c_ne
  set X : Submodule K V := Submodule.span K {u, v} with hX
  have hXS : X ≤ S := by
    rw [hX, Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hu
    · exact hv
  have hsup : X ⊔ (S ⊓ perp2 Q u v) = S := by
    refine le_antisymm (sup_le hXS inf_le_left) fun x hx => ?_
    have hmem : x - rotProj Q c u v x ∈ S ⊓ perp2 Q u v :=
      ⟨S.sub_mem hx (rotProj_mem hu hv x), h.sub_rotProj_mem_perp2 h3 x⟩
    have hproj : rotProj Q c u v x ∈ X :=
      X.add_mem (X.smul_mem _ (Submodule.subset_span (by simp)))
        (X.smul_mem _ (Submodule.subset_span (by simp)))
    rw [show x = rotProj Q c u v x + (x - rotProj Q c u v x) by abel]
    exact Submodule.add_mem_sup hproj hmem
  have hinf : X ⊓ (S ⊓ perp2 Q u v) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz, -, hzP⟩
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hz
    obtain ⟨h1, h2⟩ := mem_perp2.1 hzP
    rw [polar_add_right, polar_smul_right, polar_smul_right, h.polar_uu, h.polar_uv] at h1
    rw [polar_add_right, polar_smul_right, polar_smul_right, h.polar_vu, h.polar_vv] at h2
    simp only [smul_eq_mul] at h1 h2
    have hb : b * c = 2 * (a * c) := by linear_combination -h1
    have h3' : (3 : K) * (a * c) = 0 := by linear_combination h2 - 2 * hb
    have hac : a * c = 0 := (mul_eq_zero.1 h3').resolve_left h3
    have ha : a = 0 := (mul_eq_zero.1 hac).resolve_right hc
    have hbc : b * c = 0 := by rw [hb, hac, mul_zero]
    have hb' : b = 0 := (mul_eq_zero.1 hbc).resolve_right hc
    simp [ha, hb']
  have hli : LinearIndependent K ![u, v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (polar Q u) hst
    have h2 := congrArg (polar Q v) hst
    rw [polar_add_right, polar_smul_right, polar_smul_right, h.polar_uu, h.polar_uv,
      polar_zero_right] at h1
    rw [polar_add_right, polar_smul_right, polar_smul_right, h.polar_vu, h.polar_vv,
      polar_zero_right] at h2
    simp only [smul_eq_mul] at h1 h2
    have e1 : t * c = 2 * (s * c) := by linear_combination -h1
    have e2 : (3 : K) * (s * c) = 0 := by linear_combination h2 - 2 * e1
    have hsc : s * c = 0 := (mul_eq_zero.1 e2).resolve_left h3
    have hs : s = 0 := (mul_eq_zero.1 hsc).resolve_right hc
    have htc : t * c = 0 := by rw [e1, hsc, mul_zero]
    exact ⟨hs, (mul_eq_zero.1 htc).resolve_right hc⟩
  have hXdim : Module.finrank K X = 2 := by
    have h2 := finrank_span_eq_card hli
    rwa [Matrix.range_cons_cons_empty, Fintype.card_fin] at h2
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq X (S ⊓ perp2 Q u v)
  rw [hsup, hinf, finrank_bot, add_zero, hXdim] at hfin
  omega

theorem RotMode.stable_inf_perp2 {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hm : RotMode g u v) {S : Submodule K V}
    (hS : ∀ x ∈ S, g x ∈ S) : ∀ x ∈ S ⊓ perp2 Q u v, g x ∈ S ⊓ perp2 Q u v := by
  intro x hx
  rw [Submodule.mem_inf, mem_perp2] at hx
  rw [Submodule.mem_inf, mem_perp2]
  exact ⟨hS x hx.1, hm.polar_perp hg hx.2.1 hx.2.2⟩

end Complement

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmMinus
