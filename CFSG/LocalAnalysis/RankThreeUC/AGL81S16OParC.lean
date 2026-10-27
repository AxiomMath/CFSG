module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OParA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONat

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.LieType.Universal.Spin (quadMinus)

section ParC

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

@[expose] def cvHom (G : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
    GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F where
  toFun h := G⁻¹ * h * G
  map_one' := by simp
  map_mul' x y := by
    show G⁻¹ * (x * y) * G = G⁻¹ * x * G * (G⁻¹ * y * G)
    group

theorem cvHom_injective (G : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
    Function.Injective (cvHom G) := by
  intro x y h
  have h' : G⁻¹ * x * G = G⁻¹ * y * G := h
  exact mul_left_cancel (mul_right_cancel h')

theorem conj_std_preserves {G h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} {w u : OW F}
    (hGw : gv G (eV F idx0) = w) (hGu : gv G (eV F idx1) = u)
    (hw : ∃ s t : F, gv h w = s • w + t • u) (hu : ∃ s t : F, gv h u = s • w + t • u)
    (i : Fin (3 - 1)) :
    ∃ s t : F, gv (G⁻¹ * h * G) (eV F i) = s • eV F idx0 + t • eV F idx1 := by
  subst hGw hGu
  have hi : i = idx0 ∨ i = idx1 := by
    revert i
    decide
  rcases hi with rfl | rfl
  · obtain ⟨s, t, hst⟩ := hw
    refine ⟨s, t, ?_⟩
    rw [gv_mul, gv_mul, hst, gv_add, gv_smul, gv_smul, gv_inv_gv, gv_inv_gv]
  · obtain ⟨s, t, hst⟩ := hu
    refine ⟨s, t, ?_⟩
    rw [gv_mul, gv_mul, hst, gv_add, gv_smul, gv_smul, gv_inv_gv, gv_inv_gv]

theorem gv_iso_of_mem {G : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hG : toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F G ∈ orthogonalGroup (quadMinus 3 F b c))
    (v : OW F) : quadMinus 3 F b c (gv G v) = quadMinus 3 F b c v := by
  have h := map_of_mem hG v
  rwa [toLinEquiv_apply] at h

theorem gv_iso_inv {G : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hG : ∀ v : OW F, quadMinus 3 F b c (gv G v) = quadMinus 3 F b c v) (v : OW F) :
    quadMinus 3 F b c (gv G⁻¹ v) = quadMinus 3 F b c v := by
  conv_rhs => rw [← gv_gv_inv G v]
  rw [hG]

theorem iso_conj {G h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hG : ∀ v : OW F, quadMinus 3 F b c (gv G v) = quadMinus 3 F b c v)
    (hh : ∀ v : OW F, quadMinus 3 F b c (gv h v) = quadMinus 3 F b c v) (v : OW F) :
    quadMinus 3 F b c (gv (G⁻¹ * h * G) v) = quadMinus 3 F b c v := by
  rw [gv_mul, gv_mul, gv_iso_inv hG, hh, hG]

theorem conj_mem_omega_inv (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {G h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hGO : toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F G ∈ orthogonalGroup (quadMinus 3 F b c))
    (hh : h ∈ StatedOmega (StatedQuadMinus 3 F b c)) :
    G⁻¹ * h * G ∈ StatedOmega (StatedQuadMinus 3 F b c) := by
  have hGi : toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F G⁻¹ ∈
      orthogonalGroup (quadMinus 3 F b c) := by
    rw [map_inv]
    exact inv_mem hGO
  have := conj_mem_statedOmega hirr hGi hh
  rwa [inv_inv] at this

theorem rad_conj_conj {G₀ m g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} {w u : OW F}
    (hG₀iso : ∀ v : OW F, quadMinus 3 F b c (gv G₀ v) = quadMinus 3 F b c v)
    (hGw : gv G₀ (eV F idx0) = w) (hGu : gv G₀ (eV F idx1) = u)
    (hm : ∀ v : OW F, quadMinus 3 F b c (gv m v) = quadMinus 3 F b c v)
    (hmw : ∃ s t : F, gv m w = s • w + t • u) (hmu : ∃ s t : F, gv m u = s • w + t • u)
    (hmw' : ∃ s t : F, gv m⁻¹ w = s • w + t • u) (hmu' : ∃ s t : F, gv m⁻¹ u = s • w + t • u)
    (hρ : RadHyp b c (G₀⁻¹ * g * G₀)) : RadHyp b c (G₀⁻¹ * (m * g * m⁻¹) * G₀) := by
  have hξ : ∀ v : OW F, quadMinus 3 F b c (gv (G₀⁻¹ * m * G₀) v) = quadMinus 3 F b c v :=
    iso_conj hG₀iso hm
  have hY := conj_std_preserves hGw hGu hmw hmu
  have hY' : ∀ i : Fin (3 - 1), ∃ s t : F,
      gv (G₀⁻¹ * m * G₀)⁻¹ (eV F i) = s • eV F idx0 + t • eV F idx1 := by
    have e : (G₀⁻¹ * m * G₀)⁻¹ = G₀⁻¹ * m⁻¹ * G₀ := by group
    rw [e]
    exact conj_std_preserves hGw hGu hmw' hmu'
  have key := rad_conj_mem hξ hY hY' hρ
  have e2 : G₀⁻¹ * (m * g * m⁻¹) * G₀ =
      (G₀⁻¹ * m * G₀) * (G₀⁻¹ * g * G₀) * (G₀⁻¹ * m * G₀)⁻¹ := by group
  rw [e2]
  exact key

theorem rad_comm_conj {G₀ m g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} {w u : OW F}
    (hG₀iso : ∀ v : OW F, quadMinus 3 F b c (gv G₀ v) = quadMinus 3 F b c v)
    (hGw : gv G₀ (eV F idx0) = w) (hGu : gv G₀ (eV F idx1) = u)
    (hm : ∀ v : OW F, quadMinus 3 F b c (gv m v) = quadMinus 3 F b c v)
    (hmw : ∃ s t : F, gv m w = s • w + t • u) (hmu : ∃ s t : F, gv m u = s • w + t • u)
    (hmw' : ∃ s t : F, gv m⁻¹ w = s • w + t • u) (hmu' : ∃ s t : F, gv m⁻¹ u = s • w + t • u)
    (hρ : RadHyp b c (G₀⁻¹ * g * G₀)) : RadHyp b c (G₀⁻¹ * (m * g * m⁻¹ * g⁻¹) * G₀) := by
  have h1 := rad_conj_conj hG₀iso hGw hGu hm hmw hmu hmw' hmu' hρ
  have h2 := radHyp_inv hρ
  have e : G₀⁻¹ * (m * g * m⁻¹ * g⁻¹) * G₀ =
      (G₀⁻¹ * (m * g * m⁻¹) * G₀) * (G₀⁻¹ * g * G₀)⁻¹ := by group
  rw [e]
  exact radHyp_mul h1 h2

theorem quad_span_zero {w u : OW F} (hw : quadMinus 3 F b c w = 0) (hu : quadMinus 3 F b c u = 0)
    (hwu : polar (quadMinus 3 F b c) w u = 0) (s t : F) :
    quadMinus 3 F b c (s • w + t • u) = 0 := by
  have h1 := QuadraticMap.map_add (⇑(quadMinus 3 F b c)) (s • w) (t • u)
  rw [polar_smul_left_eq, polar_smul_right_eq, hwu, map_smul_eq_sq, map_smul_eq_sq, hw, hu] at h1
  simpa using h1

theorem finrank_span_pair {w u : OW F} (hli : LinearIndependent F ![w, u]) :
    Module.finrank F (Submodule.span F ({w, u} : Set (OW F))) = 2 := by
  have h := finrank_span_eq_card hli
  have hr : Set.range ![w, u] = ({w, u} : Set (OW F)) := by
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  rw [hr] at h
  simpa using h

theorem coeffs_of_mem_span {w u y : OW F}
    (hy : y ∈ Submodule.span F ({w, u} : Set (OW F))) : ∃ s t : F, y = s • w + t • u := by
  obtain ⟨s, t, h⟩ := Submodule.mem_span_pair.mp hy
  exact ⟨s, t, h.symm⟩

theorem w_mem_span (w u : OW F) : w ∈ Submodule.span F ({w, u} : Set (OW F)) :=
  Submodule.subset_span (Set.mem_insert w _)

theorem u_mem_span (w u : OW F) : u ∈ Submodule.span F ({w, u} : Set (OW F)) :=
  Submodule.subset_span (Set.mem_insert_of_mem w (Set.mem_singleton u))

theorem coeffs_of_stab {w u : OW F} {h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hh : ∀ y ∈ Submodule.span F ({w, u} : Set (OW F)),
      gv h y ∈ Submodule.span F ({w, u} : Set (OW F))) :
    (∃ s t : F, gv h w = s • w + t • u) ∧ (∃ s t : F, gv h u = s • w + t • u) :=
  ⟨coeffs_of_mem_span (hh w (w_mem_span w u)), coeffs_of_mem_span (hh u (u_mem_span w u))⟩

theorem coeffs_of_frame {w u : OW F} {h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} {τ : F}
    (hw : gv h w = w) (hu : gv h u = u + τ • w) :
    (∃ s t : F, gv h w = s • w + t • u) ∧ (∃ s t : F, gv h u = s • w + t • u) :=
  ⟨⟨1, 0, by rw [hw]; simp⟩, ⟨τ, 1, by rw [hu]; simp [add_comm]⟩⟩

end ParC

section Gen

variable {G : Type} [Group G]

theorem le_normalizer_of_conj_mem {S R : Subgroup G} (h : ∀ t ∈ S, ∀ x ∈ R, t * x * t⁻¹ ∈ R) :
    S ≤ normalizer (R : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h t ht x hx, fun hx => ?_⟩
  have := h t⁻¹ (S.inv_mem ht) _ hx
  simpa [mul_assoc] using this

theorem pgroup_le_sylow_of_normalized [Finite G] {Λ T₀ R : Subgroup G}
    (hT₀ : CFSG.ABGLocalTools.IsSylowOf 2 T₀ Λ) (hRΛ : R ≤ Λ) (hR : IsPGroup 2 R)
    (hN : ∀ t ∈ T₀, ∀ x ∈ R, t * x * t⁻¹ ∈ R) : R ≤ T₀ := by
  have hsup : IsPGroup 2 ↥(R ⊔ T₀) :=
    hR.to_sup_of_normal_left' hT₀.isPGroup (le_normalizer_of_conj_mem hN)
  have heq := hT₀.eq_of_le (le_sup_right : T₀ ≤ R ⊔ T₀) (sup_le hRΛ hT₀.le) hsup
  rw [← heq]
  exact le_sup_left

end Gen

section QFix

variable {G : Type} [Group G] [Finite G] {n : ℕ} {L V : Subgroup G} (d : O6NatData G n L V)

theorem O6NatData.q_fixes (hn : 1 ≤ n) {A : Subgroup G} (hAV : A ≤ normalizer (V : Set G))
    (hQ : ∀ B : Subgroup G, B ≤ A → B.relIndex A < 2 ^ (2 * n) →
      V ⊓ centralizer (B : Set G) ≤ centralizer (A : Set G))
    {w u : OW d.F} (hA : ∀ a : ↥A, ∃ t : d.F, d.rho A hAV a u = u + t • w) (a : ↥A) :
    d.rho A hAV a u = u := by
  classical
  letI : MulAction ↥A (OW d.F) := MulAction.compHom (OW d.F) (d.rho A hAV)
  have hsmul : ∀ (a : ↥A) (x : OW d.F), a • x = d.rho A hAV a x := fun a x => rfl
  set S : Subgroup ↥A := MulAction.stabilizer ↥A u with hS
  set B : Subgroup G := S.map A.subtype with hB
  have hBA : B ≤ A := Subgroup.map_subtype_le S
  have hrel : B.relIndex A = S.index := by
    rw [Subgroup.relIndex, hB, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
  have horb : MulAction.orbit ↥A u ⊆ Set.range (fun t : d.F => u + t • w) := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨t, ht⟩ := hA a
    exact ⟨t, ((hsmul a u).trans ht).symm⟩
  have hcard : S.index ≤ Nat.card d.F := by
    rw [hS, MulAction.index_stabilizer]
    calc (MulAction.orbit ↥A u).ncard ≤ (Set.range (fun t : d.F => u + t • w)).ncard :=
          Set.ncard_le_ncard horb (Set.toFinite _)
      _ ≤ Nat.card d.F := by
          rw [← Set.image_univ, ← Set.ncard_univ d.F]
          exact Set.ncard_image_le (Set.toFinite _)
  have hlt : B.relIndex A < 2 ^ (2 * n) := by
    rw [hrel]
    calc S.index ≤ Nat.card d.F := hcard
      _ = 2 ^ n := d.card_F
      _ < 2 ^ (2 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hQB := hQ B hBA hlt
  set v₀ : ↥V := d.eqv.symm u with hv₀
  have hv₀u : d.eqv v₀ = u := d.eqv.apply_symm_apply u
  have hmem : (v₀ : G) ∈ V ⊓ centralizer (B : Set G) := by
    refine ⟨v₀.2, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hb
    have hs' : d.rho A hAV s u = u := hs
    have h1 := d.rho_eqv A hAV s v₀
    rw [hv₀u, hs'] at h1
    have h2 : conjOn V s.1 (hAV s.2) v₀ = v₀ := d.eqv.injective (by rw [hv₀u]; exact h1.symm)
    have h3 : (s : G) * v₀ * (s : G)⁻¹ = v₀ := congrArg Subtype.val h2
    show (s : G) * v₀ = v₀ * (s : G)
    calc (s : G) * v₀ = ((s : G) * v₀ * (s : G)⁻¹) * (s : G) := by group
      _ = v₀ * (s : G) := by rw [h3]
  have hcomm := Subgroup.mem_centralizer_iff.mp (hQB hmem) a.1 a.2
  have h4 : conjOn V a.1 (hAV a.2) v₀ = v₀ := Subtype.ext (by
    show (a : G) * v₀ * (a : G)⁻¹ = v₀
    rw [hcomm]
    group)
  have h5 := d.rho_eqv A hAV a v₀
  rw [hv₀u, h4] at h5
  rw [h5, hv₀u]

end QFix

end CFSG.LocalAnalysis.RankThreeUC
