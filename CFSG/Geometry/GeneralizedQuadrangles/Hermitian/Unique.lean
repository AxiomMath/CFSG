module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Forms
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.HermGraph
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.PerpSpan
public import CFSG.LieType.BorelTits.ReflFormHermitian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.BorelTits

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem exists_iso_hermGraph_of_polarity (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {c : Γ.Coloring (Fin 2)} {q : ℕ} (hq : 2 ≤ q) {K : Type*} [Field K] [Fintype K]
    (hK : Fintype.card K = q ^ 2) {ι : V → Submodule K (Fin 5 → K)} (hι : IsProjGQ c ι ⊤)
    (hsec : HasConstantSecants c ι ⊤ q)
    (π : ProjectiveGeometry.Point 5 K → ProjectiveGeometry.Hyperplane 5 K)
    (hπ : ∀ x y : ProjectiveGeometry.Point 5 K,
      (x : Submodule K (Fin 5 → K)) ≤ π y ↔ (y : Submodule K (Fin 5 → K)) ≤ π x)
    (habs : ∀ x : ProjectiveGeometry.Point 5 K,
      ((x : Submodule K (Fin 5 → K)) ≤ π x ↔ ∃ v, c v = 0 ∧ ι v = x))
    (hlines : ∀ U : Submodule K (Fin 5 → K), finrank K U = 2 →
      ((∀ x : ProjectiveGeometry.Point 5 K, (x : Submodule K (Fin 5 → K)) ≤ U →
          U ≤ π x) ↔ ∃ L, c L = 1 ∧ ι L = U)) :
    ∃ σ : K ≃+* K, σ ≠ 1 ∧ σ * σ = 1 ∧ Nonempty (Γ ≃g HermGraph K σ) := by
  classical
  haveI : Finite K := Finite.of_fintype K
  obtain ⟨F, hF⟩ := exists_reflForm_of_polarity π hπ
  have habs_span : ∀ (v : Fin 5 → K) (hv : v ≠ 0), F.β v v = 0 →
      (K ∙ v) ≤
        (π ⟨K ∙ v, finrank_span_singleton hv⟩ : Submodule K (Fin 5 → K)) := by
    intro v hv hvv
    rw [hF]
    intro z hz
    rw [ReflForm.mem_perp]
    intro w hw
    rw [Submodule.mem_span_singleton] at hz hw
    obtain ⟨a, rfl⟩ := hz
    obtain ⟨b, rfl⟩ := hw
    rw [F.smul_left, F.smul_right, hvv, mul_zero, mul_zero]
  obtain ⟨s, t, hs, ht, -, hdeg⟩ := hP.exists_order (by norm_num) hT c
  obtain ⟨⟨x₀, hx₀⟩⟩ := hP.exists_point (by norm_num) hT c
  have hcard_out : 0 < (Finset.univ.filter fun y => Γ.dist x₀ y = 4).card := by
    rw [card_opposite hP hT c hdeg hx₀]
    nlinarith [hs, ht]
  obtain ⟨y, hy_mem⟩ := Finset.card_pos.mp hcard_out
  rw [Finset.mem_filter] at hy_mem
  obtain ⟨-, hy₄⟩ := hy_mem
  have hy₀ : c y = 0 := by
    have heven : Even (Γ.dist x₀ y) := by rw [hy₄]; exact ⟨2, by norm_num⟩
    have h := (hP.eq_iff_even_dist c x₀ y).mpr heven
    rw [hx₀] at h
    exact h.symm
  have hcard_out' : 0 < (Finset.univ.filter fun z => Γ.dist y z = 4).card := by
    rw [card_opposite hP hT c hdeg hy₀]
    nlinarith [hs, ht]
  obtain ⟨z, hz_mem⟩ := Finset.card_pos.mp hcard_out'
  rw [Finset.mem_filter] at hz_mem
  obtain ⟨-, hz₄⟩ := hz_mem
  have hz₀ : c z = 0 := by
    have heven : Even (Γ.dist y z) := by rw [hz₄]; exact ⟨2, by norm_num⟩
    have h := (hP.eq_iff_even_dist c y z).mpr heven
    rw [hy₀] at h
    exact h.symm
  have hyz : y ≠ z := by
    intro h
    rw [h] at hz₄
    simpa using hz₄
  let U : Submodule K (Fin 5 → K) := ι y ⊔ ι z
  have hy1 : finrank K (ι y) = 1 := hι.finrank_point y hy₀
  have hz1 : finrank K (ι z) = 1 := hι.finrank_point z hz₀
  have hiy_ne_iz : ι y ≠ ι z := fun h => hyz (hι.injective h)
  have hU2 : finrank K U = 2 :=
    finrank_sup_eq_two_of_finrank_eq_one hy1 hz1 hiy_ne_iz
  have hUle : U ≤ (⊤ : Submodule K (Fin 5 → K)) := le_top
  have hneU : ∀ L, c L = 1 → ι L ≠ U := by
    intro L hL hLU
    have hyL : Γ.Adj y L := (hι.adj_iff y L hy₀ hL).2 (by
      rw [hLU]
      exact le_sup_left)
    have hzL : Γ.Adj z L := (hι.adj_iff z L hz₀ hL).2 (by
      rw [hLU]
      exact le_sup_right)
    have hdist : Γ.dist y z = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hyL hzL.symm hyz
    omega
  have hsec_mem : ({y, z} : Set V) ⊆ sectionPoints c ι U := by
    intro v hv
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact ⟨hy₀, le_sup_left⟩
    · exact ⟨hz₀, le_sup_right⟩
  have hge : 2 ≤ (sectionPoints c ι U).ncard := by
    have h2 : ({y, z} : Set V).ncard = 2 := Set.ncard_pair hyz
    rw [← h2]
    exact Set.ncard_le_ncard hsec_mem
  have hsecEq : (sectionPoints c ι U).ncard = q + 1 :=
    hsec.ncard_eq hUle hU2 hneU hge
  have hynotbot : ι y ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hy1
    omega
  have hznotbot : ι z ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hz1
    omega
  obtain ⟨u, hu_mem, hu_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hynotbot
  obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hznotbot
  have hspan_y : ι y = K ∙ u :=
    eq_span_singleton_of_mem_of_finrank_eq_one hy1 hu_mem hu_ne
  have hspan_z : ι z = K ∙ w :=
    eq_span_singleton_of_mem_of_finrank_eq_one hz1 hw_mem hw_ne
  have hUeq : U = K ∙ u ⊔ K ∙ w := by
    rw [show U = ι y ⊔ ι z from rfl, hspan_y, hspan_z]
  have hspan_ne : (K ∙ u) ≠ (K ∙ w) := by
    rw [← hspan_y, ← hspan_z]
    exact hiy_ne_iz
  have hli : LinearIndependent K ![u, w] := by
    rw [LinearIndependent.pair_iff' hu_ne]
    intro a ha
    have hle : K ∙ w ≤ K ∙ u := by
      rw [Submodule.span_singleton_le_iff_mem]
      rw [← ha]
      exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self u)
    have hu1 : finrank K (K ∙ u) = 1 := finrank_span_singleton hu_ne
    have hw1 : finrank K (K ∙ w) = 1 := finrank_span_singleton hw_ne
    exact hspan_ne ((Submodule.eq_of_le_of_finrank_eq hle (by rw [hu1, hw1])).symm)
  have huw_ne : ∀ a : K, a • u + w ≠ 0 := by
    intro a ha
    have hcoeff := (LinearIndependent.pair_iff.mp hli) a 1 (by simpa using ha)
    exact one_ne_zero hcoeff.2
  have hspan_inj : ∀ a b : K, K ∙ (a • u + w) = K ∙ (b • u + w) → a = b := by
    intro a b heq
    obtain ⟨c, hc⟩ := (Submodule.span_singleton_eq_span_singleton).mp heq
    rw [Units.smul_def] at hc
    have hc' : ((c : K) * a) • u + (c : K) • w = b • u + (1 : K) • w := by
      calc
        ((c : K) * a) • u + (c : K) • w = (c : K) • (a • u + w) := by
          rw [smul_add, smul_smul]
        _ = b • u + w := hc
        _ = b • u + (1 : K) • w := by rw [one_smul]
    have hcoeff := (LinearIndependent.pair_iffₛ.mp hli) ((c : K) * a) (c : K) b (1 : K) hc'
    have hc1 : c = 1 := Units.ext hcoeff.2
    simpa [hc1] using hcoeff.1
  have hu_abs : F.β u u = 0 := by
    have hP : (K ∙ u) ≤
        (π ⟨ι y, hy1⟩ : Submodule K (Fin 5 → K)) := by
      rw [← hspan_y]
      exact (habs ⟨ι y, hy1⟩).mpr ⟨y, hy₀, rfl⟩
    have hle : ι y ≤ F.perp (ι y) := by
      have := hP
      rw [hF ⟨ι y, hy1⟩] at this
      simpa [hspan_y] using this
    exact F.mem_perp.mp (hle hu_mem) u hu_mem
  have hw_abs : F.β w w = 0 := by
    have hP : (K ∙ w) ≤
        (π ⟨ι z, hz1⟩ : Submodule K (Fin 5 → K)) := by
      rw [← hspan_z]
      exact (habs ⟨ι z, hz1⟩).mpr ⟨z, hz₀, rfl⟩
    have hle : ι z ≤ F.perp (ι z) := by
      have := hP
      rw [hF ⟨ι z, hz1⟩] at this
      simpa [hspan_z] using this
    exact F.mem_perp.mp (hle hw_mem) w hw_mem
  have hσ_ne : F.σ ≠ RingEquiv.refl K := by
    intro hσ
    rcases ReflForm.absolute_of_σ_eq_one F hσ hu_abs hw_abs with hcase1 | hcase2
    ·
      let P : K → ProjectiveGeometry.Point 5 K := fun a =>
        ⟨K ∙ (a • u + w), finrank_span_singleton (huw_ne a)⟩
      have hPabs : ∀ a, (P a : Submodule K (Fin 5 → K)) ≤ π (P a) := by
        intro a
        have := habs_span (a • u + w) (huw_ne a) (hcase1 a)
        simpa [P] using this
      let f : K → V := fun a => Classical.choose ((habs (P a)).mp (hPabs a))
      have hf_c : ∀ a, c (f a) = 0 := fun a =>
        (Classical.choose_spec ((habs (P a)).mp (hPabs a))).1
      have hf_ι : ∀ a, ι (f a) = (P a : Submodule K (Fin 5 → K)) := fun a =>
        (Classical.choose_spec ((habs (P a)).mp (hPabs a))).2
      have hf_mem : ∀ a, f a ∈ sectionPoints c ι U := by
        intro a
        refine ⟨hf_c a, ?_⟩
        rw [hf_ι a]
        change K ∙ (a • u + w) ≤ U
        rw [hUeq, Submodule.span_singleton_le_iff_mem]
        exact Submodule.add_mem _
          (Submodule.mem_sup_left (Submodule.smul_mem _ a
            (Submodule.mem_span_singleton_self u)))
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
      have hf_inj : Function.Injective f := by
        intro a b hab
        refine hspan_inj a b ?_
        have h := congrArg ι hab
        simpa [P, hf_ι] using h
      have hle_card : Fintype.card K ≤ (sectionPoints c ι U).ncard := by
        have hsub : Set.range f ⊆ sectionPoints c ι U := by
          rintro v ⟨a, rfl⟩
          exact hf_mem a
        have hrange : (Set.range f).ncard = Fintype.card K := by
          rw [Set.ncard_range_of_injective hf_inj, Nat.card_eq_fintype_card]
        rw [← hrange]
        exact Set.ncard_le_ncard hsub
      rw [hsecEq, hK] at hle_card
      nlinarith [hq]
    ·
      have hsub : sectionPoints c ι U ⊆ ({y, z} : Set V) := by
        intro v hv
        have hv1 : finrank K (ι v) = 1 := hι.finrank_point v hv.1
        have hvnotbot : ι v ≠ ⊥ := by
          intro hbot
          rw [hbot, finrank_bot] at hv1
          omega
        obtain ⟨t, ht_mem, ht_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hvnotbot
        have hPv_perp : ι v ≤ F.perp (ι v) := by
          have h := (habs ⟨ι v, hv1⟩).mpr ⟨v, hv.1, rfl⟩
          rw [hF ⟨ι v, hv1⟩] at h
          simpa using h
        have ht_abs : F.β t t = 0 := F.mem_perp.mp (hPv_perp ht_mem) t ht_mem
        have ht_U : t ∈ U := hv.2 ht_mem
        rw [hUeq, Submodule.mem_sup] at ht_U
        obtain ⟨t₁, ht₁, t₂, ht₂, ht_sum⟩ := ht_U
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp ht₁
        obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp ht₂
        have hv_span : ι v = K ∙ t :=
          eq_span_singleton_of_mem_of_finrank_eq_one hv1 ht_mem ht_ne
        by_cases hb : b = 0
        · have ht_eq : t = a • u := by rw [← ht_sum, hb, zero_smul, add_zero]
          have ha : a ≠ 0 := by
            intro ha
            rw [ha, zero_smul] at ht_eq
            exact ht_ne ht_eq
          have ht_span : K ∙ t = K ∙ u := by
            rw [ht_eq, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha)]
          rw [Set.mem_insert_iff, Set.mem_singleton_iff]
          left
          exact hι.injective (by rw [hv_span, ht_span, ← hspan_y])
        · let d : K := a / b
          have hbd : b * d = a := by
            dsimp [d]
            field_simp
          have ht_eq : t = b • (d • u + w) := by
            calc
              t = a • u + b • w := ht_sum.symm
              _ = (b * d) • u + b • w := by rw [hbd]
              _ = b • (d • u + w) := by rw [smul_add, smul_smul]
          have hβd : F.β (d • u + w) (d • u + w) = 0 := by
            have h := ht_abs
            rw [ht_eq, F.smul_left, F.smul_right] at h
            have hσb : F.σ b ≠ 0 := (map_ne_zero F.σ).mpr hb
            exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hσb)).resolve_left hb
          have hd : d = 0 := by
            by_contra hd
            exact hcase2 d hd hβd
          have ha : a = 0 := by rw [← hbd, hd, mul_zero]
          have ht_eq' : t = b • w := by rw [← ht_sum, ha, zero_smul, zero_add]
          have ht_span : K ∙ t = K ∙ w := by
            rw [ht_eq', Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hb)]
          rw [Set.mem_insert_iff, Set.mem_singleton_iff]
          right
          exact hι.injective (by rw [hv_span, ht_span, ← hspan_z])
      have hle2 : (sectionPoints c ι U).ncard ≤ 2 := by
        have h2 : ({y, z} : Set V).ncard = 2 := Set.ncard_pair hyz
        rw [← h2]
        exact Set.ncard_le_ncard hsub
      rw [hsecEq] at hle2
      omega
  have hdim : 2 ≤ Module.finrank K (Fin 5 → K) := by
    rw [Module.finrank_fin_fun]
    norm_num
  obtain ⟨hσ_sq_apply, μ, hμ, hherm⟩ := F.exists_hermitian_multiple hdim hσ_ne
  have hσ_mul : F.σ * F.σ = 1 := by
    ext a
    simpa using hσ_sq_apply a
  have hσ_sq : F.σ ^ 2 = 1 := by simpa [pow_two] using hσ_mul
  obtain ⟨hh, hhdef, hhsym, hhnd⟩ := F.exists_sesq hμ hherm
  obtain ⟨e, he⟩ :=
    CFSG.ComponentClassification.CatalogueBHermitian.exists_coordinate_isometry
      (sigma := F.σ) hh hhsym hhnd hσ_sq hσ_ne
  let hfr : finrank K (Fin 5 → K) = 5 := Module.finrank_fin_fun K
  let τ : (Fin (finrank K (Fin 5 → K)) → K) ≃ₗ[K] (Fin 5 → K) :=
    LinearEquiv.funCongrLeft K K (finCongr hfr.symm)
  have hτ : ∀ x y : Fin (finrank K (Fin 5 → K)) → K,
      CFSG.ClassicalGroups.Unitary.herm F.σ (τ x) (τ y) =
        CFSG.ClassicalGroups.Unitary.herm F.σ x y := by
    intro x y
    rw [CFSG.ClassicalGroups.Unitary.herm_def, CFSG.ClassicalGroups.Unitary.herm_def]
    simp only [τ, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    exact Equiv.sum_comp (finCongr hfr.symm) (fun j => F.σ (x j) * y j)
  let e' : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K) := e.trans τ
  have he' : ∀ x y : Fin 5 → K,
      CFSG.ClassicalGroups.Unitary.herm F.σ (e' x) (e' y) = μ * F.β x y := by
    intro x y
    change CFSG.ClassicalGroups.Unitary.herm F.σ (τ (e x)) (τ (e y)) = μ * F.β x y
    rw [hτ, he x y, hhdef x y]
  let eL : (Fin 5 → K) →ₗ[K] (Fin 5 → K) := e'
  have hpoint_iso : ∀ v, c v = 0 → ∀ x ∈ ι v, ∀ y ∈ ι v, F.β x y = 0 := by
    intro v hv x hx y hy
    have hP : (ι v) ≤
        (π ⟨ι v, hι.finrank_point v hv⟩ : Submodule K (Fin 5 → K)) :=
      (habs ⟨ι v, hι.finrank_point v hv⟩).mpr ⟨v, hv, rfl⟩
    have hle : ι v ≤ F.perp (ι v) := by
      have := hP
      rw [hF ⟨ι v, hι.finrank_point v hv⟩] at this
      simpa using this
    exact F.refl y x (F.mem_perp.mp (hle hx) y hy)
  have hline_iso : ∀ L, c L = 1 → ∀ x ∈ ι L, ∀ y ∈ ι L, F.β x y = 0 := by
    intro L hL x hx y hy
    have hL2 : finrank K (ι L) = 2 := hι.finrank_line L hL
    by_cases hy0 : y = 0
    · rw [hy0, F.β_zero_right]
    · let z : ProjectiveGeometry.Point 5 K :=
        ⟨K ∙ y, finrank_span_singleton hy0⟩
      have hzle : (z : Submodule K (Fin 5 → K)) ≤ ι L := by
        rw [Submodule.span_singleton_le_iff_mem]
        exact hy
      have hzperp : ι L ≤ (π z : Submodule K (Fin 5 → K)) :=
        (hlines (ι L) hL2).mpr ⟨L, hL, rfl⟩ z hzle
      have hxy : F.β y x = 0 := by
        have hxz : x ∈ F.perp (K ∙ y) := by
          have := hzperp hx
          rwa [hF z] at this
        exact F.mem_perp.mp hxz y (Submodule.mem_span_singleton_self y)
      exact F.refl y x hxy
  let HermV := {U : Submodule K (Fin 5 → K) //
    (finrank K U = 1 ∨ finrank K U = 2) ∧
      ∀ u ∈ U, ∀ v ∈ U, CFSG.ClassicalGroups.Unitary.herm F.σ u v = 0}
  have hfin2 : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  let toHerm : V → HermV := fun v =>
    ⟨(ι v).map eL,
      by
        rcases (hfin2 (c v)) with hv | hv
        · left
          rw [LinearEquiv.finrank_map_eq]
          exact hι.finrank_point v hv
        · right
          rw [LinearEquiv.finrank_map_eq]
          exact hι.finrank_line v hv,
      by
        intro x hx y hy
        obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.mp hx
        obtain ⟨y₀, hy₀, rfl⟩ := Submodule.mem_map.mp hy
        change CFSG.ClassicalGroups.Unitary.herm F.σ (e' x₀) (e' y₀) = 0
        rw [he' x₀ y₀]
        rcases (hfin2 (c v)) with hv | hv
        · rw [hpoint_iso v hv x₀ hx₀ y₀ hy₀, mul_zero]
        · rw [hline_iso v hv x₀ hx₀ y₀ hy₀, mul_zero]⟩
  have hinj : Function.Injective toHerm := by
    intro v w hvw
    have hmap : (ι v).map eL = (ι w).map eL := by
      simpa [toHerm] using congrArg Subtype.val hvw
    exact hι.injective
      ((Submodule.map_injective_of_injective (f := eL) e'.injective) hmap)
  have hsurj : Function.Surjective toHerm := by
    intro W
    let U' : Submodule K (Fin 5 → K) :=
      W.1.map (e'.symm : (Fin 5 → K) →ₗ[K] (Fin 5 → K))
    have hU'fin : finrank K U' = finrank K W.1 := by
      dsimp [U']
      rw [LinearEquiv.finrank_map_eq]
    have hU'iso : ∀ x ∈ U', ∀ y ∈ U', F.β x y = 0 := by
      intro x hx y hy
      obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨y₀, hy₀, rfl⟩ := Submodule.mem_map.mp hy
      have hherm0 : CFSG.ClassicalGroups.Unitary.herm F.σ x₀ y₀ = 0 :=
        W.2.2 x₀ hx₀ y₀ hy₀
      have hμ0 : μ * F.β (e'.symm x₀) (e'.symm y₀) = 0 := by
        rw [← he' (e'.symm x₀) (e'.symm y₀)]
        simpa using hherm0
      exact (mul_eq_zero.mp hμ0).resolve_left hμ
    have hmapU' : U'.map eL = W.1 := by
      dsimp [U']
      have hcomp : eL ∘ₛₗ
          (e'.symm : (Fin 5 → K) →ₗ[K] (Fin 5 → K)) = LinearMap.id := by
        ext x
        simp [eL]
      rw [← Submodule.map_comp (e'.symm : (Fin 5 → K) →ₗ[K] (Fin 5 → K)) eL W.1,
        hcomp, Submodule.map_id]
    rcases W.2.1 with hW1 | hW2
    · have hU'1 : finrank K U' = 1 := hU'fin.trans hW1
      let P : ProjectiveGeometry.Point 5 K := ⟨U', hU'1⟩
      have hPabs : (P : Submodule K (Fin 5 → K)) ≤
          (π P : Submodule K (Fin 5 → K)) := by
        rw [hF P]
        intro x hx
        rw [ReflForm.mem_perp]
        intro y hy
        exact F.refl x y (hU'iso x hx y hy)
      obtain ⟨v, -, hvP⟩ := (habs P).mp hPabs
      refine ⟨v, ?_⟩
      apply Subtype.ext
      change (ι v).map eL = W.1
      rw [show ι v = U' from hvP, hmapU']
    · have hU'2 : finrank K U' = 2 := hU'fin.trans hW2
      have hleft : ∀ z : ProjectiveGeometry.Point 5 K,
          (z : Submodule K (Fin 5 → K)) ≤ U' →
            U' ≤ (π z : Submodule K (Fin 5 → K)) := by
        intro z hz
        rw [hF z]
        intro x hx
        rw [ReflForm.mem_perp]
        intro y hy
        exact F.refl x y (hU'iso x hx y (hz hy))
      obtain ⟨L, -, hLU⟩ := (hlines U' hU'2).mp hleft
      refine ⟨L, ?_⟩
      apply Subtype.ext
      change (ι L).map eL = W.1
      rw [show ι L = U' from hLU, hmapU']
  have adj_of_lt : ∀ {v w : V}, ι v < ι w → Γ.Adj v w := by
    intro v w hlt
    have hle : ι v ≤ ι w := le_of_lt hlt
    have hne : ι v ≠ ι w := ne_of_lt hlt
    rcases hfin2 (c v) with hv | hv
    · have hv1 : finrank K (ι v) = 1 := hι.finrank_point v hv
      rcases hfin2 (c w) with hw | hw
      · have hw1 : finrank K (ι w) = 1 := hι.finrank_point w hw
        exact absurd (Submodule.eq_of_le_of_finrank_eq hle (by rw [hv1, hw1])) hne
      · exact (hι.adj_iff v w hv hw).2 hle
    · have hv2 : finrank K (ι v) = 2 := hι.finrank_line v hv
      rcases hfin2 (c w) with hw | hw
      · have hw1 : finrank K (ι w) = 1 := hι.finrank_point w hw
        have hle_fin : finrank K (ι v) ≤ finrank K (ι w) :=
          Submodule.finrank_mono hle
        omega
      · have hw2 : finrank K (ι w) = 2 := hι.finrank_line w hw
        exact absurd (Submodule.eq_of_le_of_finrank_eq hle (by rw [hv2, hw2])) hne
  have lt_of_adj : ∀ {v w : V}, Γ.Adj v w → ι v < ι w ∨ ι w < ι v := by
    intro v w hvw
    have hcne : c v ≠ c w := c.valid hvw
    rcases hfin2 (c v) with hv | hv
    · rcases hfin2 (c w) with hw | hw
      · exact absurd (hv.trans hw.symm) hcne
      · have hle : ι v ≤ ι w := (hι.adj_iff v w hv hw).1 hvw
        have hne : ι v ≠ ι w := by
          intro h
          have h1 : finrank K (ι v) = finrank K (ι w) := by rw [h]
          rw [hι.finrank_point v hv, hι.finrank_line w hw] at h1
          omega
        exact Or.inl (lt_of_le_of_ne hle hne)
    · rcases hfin2 (c w) with hw | hw
      · have hle : ι w ≤ ι v := (hι.adj_iff w v hw hv).1 hvw.symm
        have hne : ι w ≠ ι v := by
          intro h
          have h1 : finrank K (ι w) = finrank K (ι v) := by rw [h]
          rw [hι.finrank_point w hw, hι.finrank_line v hv] at h1
          omega
        exact Or.inr (lt_of_le_of_ne hle hne)
      · exact absurd (hv.trans hw.symm) hcne
  let iso : Γ ≃g HermGraph K F.σ :=
    RelIso.mk (Equiv.ofBijective toHerm ⟨hinj, hsurj⟩) (by
      intro v w
      change (HermGraph K F.σ).Adj (toHerm v) (toHerm w) ↔ Γ.Adj v w
      rw [HermGraph, SimpleGraph.fromRel_adj]
      constructor
      · rintro ⟨-, hlt | hlt⟩
        · exact adj_of_lt
            ((Submodule.map_lt_map_iff_of_injective (f := eL) e'.injective).mp hlt)
        · exact (adj_of_lt
            ((Submodule.map_lt_map_iff_of_injective (f := eL) e'.injective).mp hlt)).symm
      · intro hvw
        rcases lt_of_adj hvw with hlt | hlt
        · have hltmap : (ι v).map eL < (ι w).map eL :=
            (Submodule.map_lt_map_iff_of_injective (f := eL) e'.injective).mpr hlt
          exact ⟨fun h => (ne_of_lt hltmap)
            (by simpa [toHerm] using congrArg Subtype.val h), Or.inl hltmap⟩
        · have hltmap : (ι w).map eL < (ι v).map eL :=
            (Submodule.map_lt_map_iff_of_injective (f := eL) e'.injective).mpr hlt
          exact ⟨fun h => (ne_of_lt hltmap)
            (by simpa [toHerm] using (congrArg Subtype.val h).symm), Or.inr hltmap⟩)
  exact ⟨F.σ, hσ_ne, hσ_mul, ⟨iso⟩⟩
