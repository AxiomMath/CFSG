module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.ThreeSpaces.Basic
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.SubquadrangleTallini
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Conjugacy

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {c : Γ.Coloring (Fin 2)} {q : ℕ}

theorem neighborSet_commonNeighbor_eq (hP : IsGeneralizedPolygon Γ 4)
    {c : Γ.Coloring (Fin 2)} {a b : V} (ha : c a = 0) (hb : c b = 0)
    (hab : Γ.dist a b = 2) :
    Γ.neighborSet (commonNeighbor hP hab) =
      {w | c w = 0 ∧ Γ.dist w a ≤ 2 ∧ Γ.dist w b ≤ 2} := by
  classical
  let K0 := commonNeighbor hP hab
  have hK0a : Γ.Adj K0 a := (commonNeighbor_adj_left hP hab).symm
  have hK0b : Γ.Adj K0 b := (commonNeighbor_adj_right hP hab).symm
  have hK0 : c K0 = 1 := color_eq_one_of_adj_of_color_eq_zero ha (hK0a.symm)
  ext w
  constructor
  · intro hw
    have hw0 : c w = 0 := color_eq_zero_of_adj_of_color_eq_one hK0 hw
    refine ⟨hw0, ?_, ?_⟩
    · by_cases hwa : w = a
      · rw [hwa]; simp
      · exact le_of_eq (dist_eq_two_of_adj_of_adj_of_ne (x := w) (y := a) (L := K0) hP
          hw.symm hK0a hwa)
    · by_cases hwb : w = b
      · rw [hwb]; simp
      · exact le_of_eq (dist_eq_two_of_adj_of_adj_of_ne (x := w) (y := b) (L := K0) hP
          hw.symm hK0b hwb)
  · rintro ⟨hw0, hwa, hwb⟩
    by_cases hwa' : w = a
    · rw [hwa']
      exact hK0a
    by_cases hwb' : w = b
    · rw [hwb']
      exact hK0b
    have hwa2 : Γ.dist w a = 2 := dist_eq_two_of_le_two_of_ne hP hw0 ha hwa' hwa
    have hwb2 : Γ.dist w b = 2 := dist_eq_two_of_le_two_of_ne hP hw0 hb hwb' hwb
    let K1 := commonNeighbor hP hwa2
    let K2 := commonNeighbor hP hwb2
    have hK1w : Γ.Adj K1 w := (commonNeighbor_adj_left hP hwa2).symm
    have hK1a : Γ.Adj K1 a := (commonNeighbor_adj_right hP hwa2).symm
    have hK2w : Γ.Adj K2 w := (commonNeighbor_adj_left hP hwb2).symm
    have hK2b : Γ.Adj K2 b := (commonNeighbor_adj_right hP hwb2).symm
    by_cases h10 : K1 = K0
    · change w ∈ Γ.neighborSet K0
      rw [← h10]
      exact hK1w
    by_cases h20 : K2 = K0
    · change w ∈ Γ.neighborSet K0
      rw [← h20]
      exact hK2w
    by_cases h12 : K1 = K2
    · have hK1b : Γ.Adj K1 b := by rw [h12]; exact hK2b
      have hK1eq : K1 = K0 :=
        eq_commonNeighbor hP hab hK1a.symm hK1b.symm
      change w ∈ Γ.neighborSet K0
      rw [← hK1eq]
      exact hK1w
    · rcases eq_left_or_eq_right_of_three_lines hP (M := K0) (A := K1) (B := K2)
        (pA := a) (pB := b) (u := w) h12 (Ne.symm h10) hK0a hK0b hK1a hK1w hK2b hK2w with h | h
      · change w ∈ Γ.neighborSet K0
        exact h ▸ hK0a
      · change w ∈ Γ.neighborSet K0
        exact h ▸ hK0b

private theorem mem_traceSet_of_dist_le_two (hP : IsGeneralizedPolygon Γ 4)
    {c : Γ.Coloring (Fin 2)} {x y z : V} (hx : c x = 0)
    (hxy : Γ.dist x y = 4) (hz0 : c z = 0)
    (hzx : Γ.dist z x ≤ 2) (hzy : Γ.dist z y ≤ 2) :
    z ∈ traceSet Γ x y := by
  have hy0 : c y = 0 := by
    rw [← hx]
    exact ((hP.eq_iff_even_dist c x y).2 (by rw [hxy]; exact ⟨2, by norm_num⟩)).symm
  have hzx2 : Γ.dist z x = 2 :=
    dist_eq_two_of_le_two_of_ne hP hz0 hx (by
      rintro rfl
      rw [hxy] at hzy
      omega) hzx
  have hzy2 : Γ.dist z y = 2 :=
    dist_eq_two_of_le_two_of_ne hP hz0 hy0 (by
      rintro rfl
      rw [SimpleGraph.dist_comm, hxy] at hzx
      omega) hzy
  exact ⟨by rwa [SimpleGraph.dist_comm], by rwa [SimpleGraph.dist_comm]⟩

theorem existsUnique_mem_spanSet_of_mem_clSet (hΓ : IsThasQuadrangle Γ c q)
    {y z x : V} (hy : c y = 0) (hyz : Γ.dist y z = 4) (hx : c x = 0)
    (hxT : x ∉ traceSet Γ y z)
    {u : V} (hu : u ∈ spanSet Γ y z) (hxu : Γ.dist x u ≤ 2) :
    ∃! u' : V, u' ∈ spanSet Γ y z ∧ Γ.dist x u' ≤ 2 := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  refine ⟨u, ⟨hu, hxu⟩, ?_⟩
  rintro u' ⟨hu', hxu'⟩
  by_contra hne
  have hne' : u ≠ u' := Ne.symm hne
  have hu4 : Γ.dist u u' = 4 :=
    dist_eq_four_of_mem_span hP hT hyz hu hu' hne'
  have hu0 : c u = 0 := color_eq_zero_of_mem_span hP hT hy hyz hu
  have hu'0 : c u' = 0 := color_eq_zero_of_mem_span hP hT hy hyz hu'
  have hxmem : x ∈ traceSet Γ u u' :=
    mem_traceSet_of_dist_le_two hP hu0 hu4 hx hxu hxu'
  have htrace : traceSet Γ u u' = traceSet Γ y z :=
    (span_eq_of_mem hP hT hyz hu hu' hne').2.2
  exact hxT (htrace ▸ hxmem)

theorem exists_mem_traceSet_of_adj_of_mem_span (hΓ : IsThasQuadrangle Γ c q)
    {y z u K : V} (hy : c y = 0) (hyz : Γ.dist y z = 4)
    (hu : u ∈ spanSet Γ y z) (hK : Γ.Adj u K) :
    ∃ w ∈ traceSet Γ y z, Γ.Adj K w := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hTcard : (traceSet Γ y z).ncard = q ^ 3 + 1 := by
    rw [ncard_trace hP hyz, hΓ.deg y, if_pos hy]
  have hu0 : c u = 0 := color_eq_zero_of_mem_span hP hT hy hyz hu
  have huCard : (Γ.neighborSet u).ncard = q ^ 3 + 1 := by
    rw [SimpleGraph.ncard_neighborSet, hΓ.deg u, if_pos hu0]
  let T' := {w : V // w ∈ traceSet Γ y z}
  let S' := {K : V // K ∈ Γ.neighborSet u}
  have hcardT : Nat.card T' = q ^ 3 + 1 := by
    rw [Nat.card_coe_set_eq, hTcard]
  have hcardS : Nat.card S' = q ^ 3 + 1 := by
    change Nat.card ↥(Γ.neighborSet u) = q ^ 3 + 1
    rw [Nat.card_coe_set_eq]
    exact huCard
  have hd : ∀ w : T', Γ.dist u (w : V) = 2 := fun w => by
    have hw : (w : V) ∈ traceSet Γ y z := w.2
    exact dist_eq_two_of_mem_span_of_mem_trace (x := y) (y := z) (z := u) (w := (w : V))
      hP hT hyz hu hw
  let f : T' → S' := fun w =>
    ⟨commonNeighbor hP (hd w), commonNeighbor_adj_left hP (hd w)⟩
  have hf : Function.Injective f := by
    intro w w' hww
    have hw : (f w).1 = (f w').1 := congrArg Subtype.val hww
    have hwT : (w : V) ∈ traceSet Γ y z := w.2
    have hw'T : (w' : V) ∈ traceSet Γ y z := w'.2
    by_contra hne
    have hne' : (w : V) ≠ (w' : V) := fun h => hne (Subtype.ext h)
    have h4 : Γ.dist w.1 w'.1 = 4 := dist_eq_four_of_mem_trace hP hyz hwT hw'T hne'
    have h2 : Γ.dist w.1 w'.1 = 2 := by
      have h1 : Γ.Adj w.1 (f w).1 := commonNeighbor_adj_right hP (hd w)
      have h2' : Γ.Adj w'.1 (f w').1 := commonNeighbor_adj_right hP (hd w')
      rw [hw] at h1
      exact dist_eq_two_of_adj_of_adj_of_ne hP h1 h2'.symm hne'
    omega
  have hrange : (Set.range f).ncard = q ^ 3 + 1 := by
    rw [Set.ncard_range_of_injective hf, hcardT]
  have huniv : (Set.univ : Set S').ncard = q ^ 3 + 1 := by
    rw [Set.ncard_univ, hcardS]
  have hEq : Set.range f = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [hrange, huniv])
  have hmem : (⟨K, hK⟩ : S') ∈ Set.range f := by rw [hEq]; exact Set.mem_univ _
  obtain ⟨w, hw⟩ := hmem
  refine ⟨w.1, w.2, ?_⟩
  have h1 : Γ.Adj (w : V) (f w).1 := commonNeighbor_adj_right hP (hd w)
  rw [congrArg Subtype.val hw] at h1
  exact h1.symm

theorem neighborSet_coneLine_subset (hP : IsGeneralizedPolygon Γ 4)
    (hΓ : IsThasQuadrangle Γ c q) {a b z v : V} (ha : c a = 0) (hab : Γ.dist a b = 4)
    (hz : z ∈ traceSet Γ a b) (hv : v ∈ spanSet Γ a b)
    (hzv : Γ.dist z v = 2) :
    Γ.neighborSet (commonNeighbor hP hzv) ⊆ ptPerp Γ c {z} ∩ clSet Γ a b := by
  have hT : IsThick Γ := hΓ.thick
  have hz0 : c z = 0 := color_eq_zero_of_dist_eq_two hP ha hz.1
  have hv0 : c v = 0 := color_eq_zero_of_mem_span hP hT ha hab hv
  intro w hw
  have hw' : w ∈ Γ.neighborSet (commonNeighbor hP hzv) := hw
  rw [neighborSet_commonNeighbor_eq hP hz0 hv0 hzv] at hw'
  refine ⟨?_, ?_⟩
  · rw [mem_ptPerp]
    exact ⟨hw'.1, by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact hw'.2.1⟩
  · exact ⟨v, hv, hw'.2.2⟩

theorem conePlane_subset_iUnion (hP : IsGeneralizedPolygon Γ 4)
    (hΓ : IsThasQuadrangle Γ c q) {a b z : V} (ha : c a = 0) (hab : Γ.dist a b = 4)
    (hz : z ∈ traceSet Γ a b) {w : V}
    (hw : w ∈ ptPerp Γ c {z} ∩ clSet Γ a b) :
    ∃ v ∈ spanSet Γ a b, ∃ hzv : Γ.dist z v = 2,
      Γ.Adj (commonNeighbor hP hzv) w := by
  have hT : IsThick Γ := hΓ.thick
  have hz0 : c z = 0 := color_eq_zero_of_dist_eq_two hP ha hz.1
  obtain ⟨hw0, hwz⟩ := mem_ptPerp.mp hw.1
  obtain ⟨v, hv, hwv⟩ := hw.2
  have hv0 : c v = 0 := color_eq_zero_of_mem_span hP hT ha hab hv
  have hzv : Γ.dist z v = 2 := by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace (z := v) (w := z) hP hT hab hv hz
  refine ⟨v, hv, hzv, ?_⟩
  have hle : w ∈ {w | c w = 0 ∧ Γ.dist w z ≤ 2 ∧ Γ.dist w v ≤ 2} :=
    ⟨hw0, hwz z rfl, hwv⟩
  rw [← neighborSet_commonNeighbor_eq hP hz0 hv0 hzv] at hle
  exact hle

theorem coneLines_ne (hP : IsGeneralizedPolygon Γ 4)
    (hΓ : IsThasQuadrangle Γ c q) {a b z v₁ v₂ : V} (ha : c a = 0) (hab : Γ.dist a b = 4)
    (hz : z ∈ traceSet Γ a b) (hv₁ : v₁ ∈ spanSet Γ a b) (hv₂ : v₂ ∈ spanSet Γ a b)
    (hne : v₁ ≠ v₂) (hzv₁ : Γ.dist z v₁ = 2) (hzv₂ : Γ.dist z v₂ = 2) :
    commonNeighbor hP hzv₁ ≠ commonNeighbor hP hzv₂ := by
  have hT : IsThick Γ := hΓ.thick
  intro hEq
  have h1 : Γ.Adj v₁ (commonNeighbor hP hzv₁) := commonNeighbor_adj_right hP hzv₁
  have h2 : Γ.Adj v₂ (commonNeighbor hP hzv₂) := commonNeighbor_adj_right hP hzv₂
  rw [hEq] at h1
  have h4 : Γ.dist v₁ v₂ = 4 := dist_eq_four_of_mem_span hP hT hab hv₁ hv₂ hne
  have h2' : Γ.dist v₁ v₂ = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP h1 h2.symm hne
  omega

theorem ptPerp_conePlane_eq_singleton (hP : IsGeneralizedPolygon Γ 4)
    (hΓ : IsThasQuadrangle Γ c q) {a b z : V} (ha : c a = 0) (hab : Γ.dist a b = 4)
    (hz : z ∈ traceSet Γ a b) :
    ptPerp Γ c (ptPerp Γ c {z} ∩ clSet Γ a b) = {z} := by
  have hT : IsThick Γ := hΓ.thick
  have hz0 : c z = 0 := color_eq_zero_of_dist_eq_two hP ha hz.1
  have hspanCard : (spanSet Γ a b).ncard = q + 1 := hΓ.span a b ha hab
  have h2 : 1 < (spanSet Γ a b).ncard := by
    rw [hspanCard]
    have := hΓ.two_le
    omega
  obtain ⟨v₁, hv₁, v₂, hv₂, hne⟩ :=
    (Set.one_lt_ncard (s := spanSet Γ a b)).mp h2
  have hzv₁ : Γ.dist z v₁ = 2 := by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace (z := v₁) (w := z) hP hT hab hv₁ hz
  have hzv₂ : Γ.dist z v₂ = 2 := by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace (z := v₂) (w := z) hP hT hab hv₂ hz
  have hKne : commonNeighbor hP hzv₁ ≠ commonNeighbor hP hzv₂ :=
    coneLines_ne hP hΓ ha hab hz hv₁ hv₂ hne hzv₁ hzv₂
  have hzK₁ : Γ.Adj (commonNeighbor hP hzv₁) z :=
    (commonNeighbor_adj_left hP hzv₁).symm
  have hzK₂ : Γ.Adj (commonNeighbor hP hzv₂) z :=
    (commonNeighbor_adj_left hP hzv₂).symm
  have hK₁line : c (commonNeighbor hP hzv₁) = 1 :=
    color_eq_one_of_adj_of_color_eq_zero hz0 (commonNeighbor_adj_left hP hzv₁)
  have hK₂line : c (commonNeighbor hP hzv₂) = 1 :=
    color_eq_one_of_adj_of_color_eq_zero hz0 (commonNeighbor_adj_left hP hzv₂)
  have hsub₁ : Γ.neighborSet (commonNeighbor hP hzv₁) ⊆
      ptPerp Γ c {z} ∩ clSet Γ a b :=
    neighborSet_coneLine_subset hP hΓ ha hab hz hv₁ hzv₁
  have hsub₂ : Γ.neighborSet (commonNeighbor hP hzv₂) ⊆
      ptPerp Γ c {z} ∩ clSet Γ a b :=
    neighborSet_coneLine_subset hP hΓ ha hab hz hv₂ hzv₂
  ext w
  constructor
  · intro hw
    have hmono₁ : ptPerp Γ c (ptPerp Γ c {z} ∩ clSet Γ a b) ⊆
        ptPerp Γ c (Γ.neighborSet (commonNeighbor hP hzv₁)) := by
      intro x hx
      rw [mem_ptPerp] at hx ⊢
      exact ⟨hx.1, fun y hy => hx.2 y (hsub₁ hy)⟩
    have hmono₂ : ptPerp Γ c (ptPerp Γ c {z} ∩ clSet Γ a b) ⊆
        ptPerp Γ c (Γ.neighborSet (commonNeighbor hP hzv₂)) := by
      intro x hx
      rw [mem_ptPerp] at hx ⊢
      exact ⟨hx.1, fun y hy => hx.2 y (hsub₂ hy)⟩
    have hw1 : w ∈ Γ.neighborSet (commonNeighbor hP hzv₁) := by
      have h := hmono₁ hw
      rwa [ptPerp_neighborSet_eq hP hT hK₁line] at h
    have hw2 : w ∈ Γ.neighborSet (commonNeighbor hP hzv₂) := by
      have h := hmono₂ hw
      rwa [ptPerp_neighborSet_eq hP hT hK₂line] at h
    rw [Set.mem_singleton_iff]
    by_contra hwz
    exact hKne (eq_of_two_common_points hP hwz hw1 hzK₁ hw2 hzK₂)
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    rw [mem_ptPerp]
    refine ⟨hz0, ?_⟩
    intro x hx
    have hx' := (mem_ptPerp.mp hx.1).2 z rfl
    rw [SimpleGraph.dist_comm]
    exact hx'

theorem neighborSet_subset_of_isFullSubquadrangle_of_two_mem
    (hΓ : IsThasQuadrangle Γ c q) {E : Set V} (hF : IsFullSubquadrangle c E q) {L a b : V}
    (hL : c L = 1) (haE : a ∈ E) (hbE : b ∈ E) (hab : a ≠ b)
    (hLa : Γ.Adj L a) (hLb : Γ.Adj L b) : Γ.neighborSet L ⊆ E := by
  have hpair : ({a, b} : Set V) ⊆ Γ.neighborSet L ∩ E := by
    rintro x (rfl | hx)
    · exact ⟨hLa, haE⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨hLb, hbE⟩
  have hcard : 2 ≤ (Γ.neighborSet L ∩ E).ncard := by
    have hle := Set.ncard_le_ncard hpair (Set.toFinite _)
    rwa [Set.ncard_pair hab] at hle
  exact hF.2.1 L hL hcard

theorem ncard_traceSet_le_fullLinesThrough (hΓ : IsThasQuadrangle Γ c q) {E : Set V}
    (hF : IsFullSubquadrangle c E q) {y z u : V} (hy : c y = 0) (hyz : Γ.dist y z = 4)
    (hu : u ∈ spanSet Γ y z) (huE : u ∈ E) (hTE : traceSet Γ y z ⊆ E) :
    q ^ 3 + 1 ≤ (fullLinesThrough Γ E u).ncard := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hu0 : c u = 0 := color_eq_zero_of_mem_span hP hT hy hyz hu
  let T' := {w : V // w ∈ traceSet Γ y z}
  let Ft := {L : V // L ∈ fullLinesThrough Γ E u}
  have hTcard : Nat.card T' = q ^ 3 + 1 := by
    rw [Nat.card_coe_set_eq, ncard_trace hP hyz, hΓ.deg y, if_pos hy]
  have hFcard : Nat.card Ft = (fullLinesThrough Γ E u).ncard := by
    change Nat.card ↥(fullLinesThrough Γ E u) = (fullLinesThrough Γ E u).ncard
    rw [Nat.card_coe_set_eq]
  have hd : ∀ w : T', Γ.dist u (w : V) = 2 := fun w => by
    have hw : (w : V) ∈ traceSet Γ y z := w.2
    exact dist_eq_two_of_mem_span_of_mem_trace (z := u) (w := (w : V)) hP hT hyz hu hw
  have hne : ∀ w : T', u ≠ (w : V) := fun w h => by
    have hw : (w : V) ∈ traceSet Γ y z := w.2
    exact not_mem_spanSet_of_mem_traceSet hP hT hyz hw (h ▸ hu)
  let g : T' → Ft := fun w =>
    ⟨commonNeighbor hP (hd w), commonNeighbor_adj_left hP (hd w), by
      have hK : c (commonNeighbor hP (hd w)) = 1 :=
        color_eq_one_of_adj_of_color_eq_zero hu0 (commonNeighbor_adj_left hP (hd w))
      exact neighborSet_subset_of_isFullSubquadrangle_of_two_mem hΓ hF hK huE
        (hTE w.2) (hne w) (commonNeighbor_adj_left hP (hd w)).symm
        (commonNeighbor_adj_right hP (hd w)).symm⟩
  have hg : Function.Injective g := by
    intro w w' hww
    have hEq : (g w).1 = (g w').1 := congrArg Subtype.val hww
    by_contra hne'
    have hne'' : (w : V) ≠ (w' : V) := fun h => hne' (Subtype.ext h)
    have h1 : Γ.Adj (w : V) (g w).1 := commonNeighbor_adj_right hP (hd w)
    have h2 : Γ.Adj (w' : V) (g w').1 := commonNeighbor_adj_right hP (hd w')
    rw [hEq] at h1
    have h2' : Γ.dist (w : V) (w' : V) = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP h1 h2.symm hne''
    have h4 : Γ.dist (w : V) (w' : V) = 4 :=
      dist_eq_four_of_mem_trace hP hyz w.2 w'.2 hne''
    omega
  have hle := Nat.card_le_card_of_injective g hg
  rwa [hTcard, hFcard] at hle

theorem existsUnique_trace_of_mem_cl (hΓ : IsThasQuadrangle Γ c q) {y z x : V}
    (hy : c y = 0) (hyz : Γ.dist y z = 4) (hx : c x = 0)
    (hxT : x ∉ traceSet Γ y z) (hxcl : x ∈ clSet Γ y z) :
    ∃! E, IsThreespace Γ c q E ∧ traceSet Γ y z ⊆ E ∧ x ∈ E := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  obtain ⟨u, hu, hxu⟩ := hxcl
  obtain ⟨u₀, hu₀spec, huniq₀⟩ := existsUnique_mem_spanSet_of_mem_clSet hΓ hy hyz hx hxT hu hxu
  have hu_eq : u₀ = u := (huniq₀ u ⟨hu, hxu⟩).symm
  have hu0 : c u = 0 := color_eq_zero_of_mem_span hP hT hy hyz hu
  refine ⟨ptPerp Γ c {u}, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Or.inl ⟨u, hu0, rfl⟩
  · intro w hw
    rw [mem_ptPerp]
    refine ⟨color_eq_zero_of_dist_eq_two hP hy hw.1, ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    simpa only [SimpleGraph.dist_comm] using hu w hw
  · rw [mem_ptPerp]
    refine ⟨hx, ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    simpa only [SimpleGraph.dist_comm] using hxu
  · rintro E ⟨hE, hTE, hxE⟩
    rcases hE with ⟨v, hv0, rfl⟩ | hF
    · have hv_span : v ∈ spanSet Γ y z := by
        intro w hw
        rw [SimpleGraph.dist_comm]
        exact (mem_ptPerp.mp (hTE hw)).2 v rfl
      have hxv : Γ.dist x v ≤ 2 := (mem_ptPerp.mp hxE).2 v rfl
      have hvu : v = u := (huniq₀ v ⟨hv_span, hxv⟩).trans hu_eq
      rw [hvu]
    · exfalso
      have huE : u ∈ E := by
        by_cases hxu_eq : x = u
        · rw [← hxu_eq]
          exact hxE
        · have hdist : Γ.dist x u = 2 :=
            dist_eq_two_of_le_two_of_ne hP hx hu0 hxu_eq hxu
          let V := commonNeighbor hP hdist
          have hVline : c V = 1 :=
            color_eq_one_of_adj_of_color_eq_zero hx (commonNeighbor_adj_left hP hdist)
          obtain ⟨w, hwT, hwV⟩ :=
            exists_mem_traceSet_of_adj_of_mem_span hΓ hy hyz hu
              (commonNeighbor_adj_right hP hdist)
          have hxw : x ≠ w := fun h => hxT (h ▸ hwT)
          have hwE : w ∈ E := hTE hwT
          have hsub : Γ.neighborSet V ⊆ E :=
            neighborSet_subset_of_isFullSubquadrangle_of_two_mem hΓ hF hVline hxE hwE hxw
              (commonNeighbor_adj_left hP hdist).symm hwV
          exact hsub (commonNeighbor_adj_right hP hdist).symm
      have hle := ncard_traceSet_le_fullLinesThrough hΓ hF hy hyz hu huE hTE
      have hq : (fullLinesThrough Γ E u).ncard = q + 1 := hF.2.2.1 u huE
      rw [hq] at hle
      have hgt : q + 1 < q ^ 3 + 1 := by
        have h1 : 1 < q := by have := hΓ.two_le; omega
        have h2 : q < q ^ 3 := lt_self_pow₀ h1 (by norm_num : 1 < 3)
        omega
      omega

theorem existsUnique_trace_of_not_mem_cl (hΓ : IsThasQuadrangle Γ c q) {y z x : V}
    (hy : c y = 0) (hyz : Γ.dist y z = 4) (hx : c x = 0)
    (hxT : x ∉ traceSet Γ y z) (hxcl : x ∉ clSet Γ y z) :
    ∃! E, IsThreespace Γ c q E ∧ traceSet Γ y z ⊆ E ∧ x ∈ E := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hz0 : c z = 0 := (color_eq_of_dist_four hP hyz).symm.trans hy
  have hxne_y : x ≠ y := by
    intro h
    exact hxcl ⟨y, left_mem_spanSet hyz, by rw [h]; simp⟩
  have hxne_z : x ≠ z := by
    intro h
    exact hxcl ⟨z, right_mem_spanSet hyz, by rw [h]; simp⟩
  have hxy4 : Γ.dist x y = 4 := by
    rcases dist_eq_two_or_four_of_color_zero hP hx hy hxne_y with h2 | h4
    · exfalso
      exact hxcl ⟨y, left_mem_spanSet hyz, by rw [h2]⟩
    · exact h4
  have hxz4 : Γ.dist x z = 4 := by
    rcases dist_eq_two_or_four_of_color_zero hP hx hz0 hxne_z with h2 | h4
    · exfalso
      exact hxcl ⟨z, right_mem_spanSet hyz, by rw [h2]⟩
    · exact h4
  have hCcard : (centreSet Γ y z x).ncard = q + 1 :=
    ncard_centreSet hΓ (x := y) (y := z) (z := x) hy hyz
      (by rw [SimpleGraph.dist_comm]; exact hxy4)
      (by rw [SimpleGraph.dist_comm]; exact hxz4) hxcl
  have hCge : 1 < (centreSet Γ y z x).ncard := by
    rw [hCcard]
    have := hΓ.two_le
    omega
  obtain ⟨u₀, hu₀C, u₁, hu₁C, hu₀₁⟩ :=
    (Set.one_lt_ncard (s := centreSet Γ y z x)).mp hCge
  have hu₀T : u₀ ∈ traceSet Γ y z := hu₀C.1
  have hu₁T : u₁ ∈ traceSet Γ y z := hu₁C.1
  have hxu₀ : Γ.dist x u₀ = 2 := hu₀C.2
  have hxu₁ : Γ.dist x u₁ = 2 := hu₁C.2
  have hspanC : centreSet Γ y z x = spanSet Γ u₀ u₁ :=
    centreSet_eq_spanSet hΓ (x := y) (y := z) (z := x) hy hyz
      (by rw [SimpleGraph.dist_comm]; exact hxy4)
      (by rw [SimpleGraph.dist_comm]; exact hxz4) hxcl hu₀C hu₁C hu₀₁
  have hTcard : (traceSet Γ y z).ncard = q ^ 3 + 1 := by
    rw [ncard_trace hP hyz, hΓ.deg y, if_pos hy]
  have hClt : (centreSet Γ y z x).ncard < (traceSet Γ y z).ncard := by
    rw [hCcard, hTcard]
    have h1 : 1 < q := by have := hΓ.two_le; omega
    have h2 : q < q ^ 3 := lt_self_pow₀ h1 (by norm_num : 1 < 3)
    omega
  obtain ⟨w, hwT, hwC⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hClt
  have hwspan : w ∉ spanSet Γ u₀ u₁ := by
    rw [← hspanC]
    exact hwC
  have hw0 : c w = 0 := color_eq_zero_of_dist_eq_two hP hy hwT.1
  have hxne_w : x ≠ w := by
    intro h
    exact hxT (h.symm ▸ hwT)
  have hxw4 : Γ.dist x w = 4 := by
    rcases dist_eq_two_or_four_of_color_zero hP hx hw0 hxne_w with h2 | h4
    · exact absurd ⟨hwT, h2⟩ hwC
    · exact h4
  let V := commonNeighbor hP hxu₀
  have hVline : c V = 1 := color_eq_one_of_adj_of_color_eq_zero hx (commonNeighbor_adj_left hP hxu₀)
  have hVx : Γ.Adj x V := commonNeighbor_adj_left hP hxu₀
  have hVu₀ : Γ.Adj u₀ V := commonNeighbor_adj_right hP hxu₀
  have hnotV : ¬ Γ.Adj w V := by
    intro hwV
    have h2 : Γ.dist w x = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hwV hVx.symm (Ne.symm hxne_w)
    rw [SimpleGraph.dist_comm] at h2
    omega
  have hdistV : Γ.dist w V = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hnotV (by rw [hw0, hVline]; decide)
  let p := proj hP hdistV
  have hpV : Γ.Adj V p := proj_adj hP hdistV
  have hwp : Γ.dist w p = 2 := proj_dist hP hdistV
  have hpx : p ≠ x := by
    intro hpx
    rw [hpx, SimpleGraph.dist_comm] at hwp
    omega
  let L := commonNeighbor hP hwp
  have hLline : c L = 1 :=
    color_eq_one_of_adj_of_color_eq_zero hw0 (commonNeighbor_adj_left hP hwp)
  have hLw : Γ.Adj L w := (commonNeighbor_adj_left hP hwp).symm
  have hLp : Γ.Adj L p := (commonNeighbor_adj_right hP hwp).symm
  have hLneV : L ≠ V := by
    intro hEq
    exact hnotV (hEq ▸ commonNeighbor_adj_left hP hwp)
  let M := commonNeighbor hP hxu₁
  have hMline : c M = 1 :=
    color_eq_one_of_adj_of_color_eq_zero hx (commonNeighbor_adj_left hP hxu₁)
  have hMx : Γ.Adj x M := commonNeighbor_adj_left hP hxu₁
  have hMu₁ : Γ.Adj u₁ M := commonNeighbor_adj_right hP hxu₁
  have hMneV : M ≠ V := by
    intro hEq
    have h2 : Γ.dist u₀ u₁ = 2 := by
      refine dist_eq_two_of_adj_of_adj_of_ne hP hVu₀ ?_ hu₀₁
      rw [← hEq]
      exact (hMu₁).symm
    have h4 : Γ.dist u₀ u₁ = 4 :=
      dist_eq_four_of_mem_trace hP hyz hu₀T hu₁T hu₀₁
    omega
  have hLMne : L ≠ M := by
    intro hEq
    have h2 : Γ.dist w x = 2 := by
      refine dist_eq_two_of_adj_of_adj_of_ne hP (commonNeighbor_adj_left hP hwp) ?_
        (Ne.symm hxne_w)
      change Γ.Adj L x
      exact hEq.symm ▸ hMx.symm
    rw [SimpleGraph.dist_comm] at h2
    omega
  have hLM4 : Γ.dist L M = 4 := by
    have heven : Even (Γ.dist L M) :=
      (hP.eq_iff_even_dist c L M).1 (by rw [hLline, hMline])
    have hle := hP.dist_le (by norm_num) L M
    have hne0 : Γ.dist L M ≠ 0 := by
      intro h0
      exact hLMne ((hP.connected.dist_eq_zero_iff).mp h0)
    have hne2 : Γ.dist L M ≠ 2 := by
      intro h2
      obtain ⟨r, hr, -⟩ := existsUnique_commonNeighbor hP h2
      have hcases := eq_left_or_eq_right_of_three_lines hP
        (M := L) (A := V) (B := M) (pA := p) (pB := r) (u := x)
        (Ne.symm hMneV) hLneV hLp hr.1 hpV hVx.symm hr.2 hMx.symm
      rcases hcases with hpx' | hrx
      · exact hpx hpx'
      · have hxL : Γ.Adj L x := by rw [hrx] at hr; exact hr.1
        exact hLneV (eq_of_two_common_points hP hpx hLp hxL hpV hVx.symm)
    obtain ⟨k, hk⟩ := heven
    omega
  obtain ⟨S, ⟨hFS, hLS, hMS⟩, hSuniq⟩ := existsUnique_fullSubquadrangle hΓ hLline hLM4
  have hxS : x ∈ S := hMS hMx.symm
  have hpS : p ∈ S := hLS hLp
  have hwS : w ∈ S := hLS hLw
  have hu₁S : u₁ ∈ S := hMS hMu₁.symm
  have hVfull : Γ.neighborSet V ⊆ S :=
    neighborSet_subset_of_isFullSubquadrangle_of_two_mem hΓ hFS hVline hxS hpS
      (Ne.symm hpx) hVx.symm hpV
  have hu₀S : u₀ ∈ S := hVfull hVu₀.symm
  have hTS : traceSet Γ y z ⊆ S :=
    traceSet_subset_of_isFullSubquadrangle hΓ hFS hy hyz
      ⟨hu₀T, hu₀S⟩ ⟨hu₁T, hu₁S⟩ ⟨hwT, hwS⟩ hu₀₁ (by rw [← hspanC]; exact hwC)
  refine ⟨S, ⟨Or.inr hFS, hTS, hxS⟩, ?_⟩
  rintro E ⟨hE, hTE, hxE⟩
  rcases hE with ⟨v, hv0, rfl⟩ | hFE
  · exfalso
    have hv_span : v ∈ spanSet Γ y z := by
      intro w' hw'
      rw [SimpleGraph.dist_comm]
      exact (mem_ptPerp.mp (hTE hw')).2 v rfl
    exact hxcl ⟨v, hv_span, (mem_ptPerp.mp hxE).2 v rfl⟩
  · have hpE : p ∈ E := by
      have hxu₀ne : x ≠ u₀ := by
        intro h
        rw [h] at hxu₀
        simp at hxu₀
      have hVE : Γ.neighborSet V ⊆ E :=
        neighborSet_subset_of_isFullSubquadrangle_of_two_mem hΓ hFE hVline hxE (hTE hu₀T)
          hxu₀ne hVx.symm hVu₀.symm
      exact Set.mem_of_subset_of_mem (a := p) hVE hpV
    have hwE : w ∈ E := hTE hwT
    have hLE : Γ.neighborSet L ⊆ E :=
      neighborSet_subset_of_isFullSubquadrangle_of_two_mem hΓ hFE hLline hwE hpE
        (by intro h; rw [h] at hwp; simp at hwp) (commonNeighbor_adj_left hP hwp).symm
        (commonNeighbor_adj_right hP hwp).symm
    have hu₁E : u₁ ∈ E := hTE hu₁T
    have hME : Γ.neighborSet M ⊆ E :=
      neighborSet_subset_of_isFullSubquadrangle_of_two_mem hΓ hFE hMline hxE hu₁E
        (by intro h; rw [h] at hxu₁; simp at hxu₁) hMx.symm hMu₁.symm
    exact hSuniq E ⟨hFE, hLE, hME⟩

end CFSG.Geometry.GeneralizedQuadrangles
