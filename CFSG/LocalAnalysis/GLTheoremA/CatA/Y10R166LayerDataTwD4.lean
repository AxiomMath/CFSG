module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataTwD3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaMinusLD

open CFSG.SeitzReduction.OmegaPilot
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.Open
open QuadraticMap Subgroup ClassicalGroups.Orthogonal
open scoped Classical

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n q : ℕ} {b c : F}

theorem anisoTorus_lift_fixes (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hne : (anisoCoordLeft (n := 5) (by norm_num)) ≠
      anisoCoordRight (n := 5) (by norm_num))
    {hQ' : ∃ v, Qc F b c v ≠ 0} {x : matrixProjectiveDerived (Qc F b c)}
    (hx : x ∈ anisoTorusOf (Qc F b c) hne b c) {v : Fin (2 * 5) → F}
    (hv : v ∈ perpSub F (anisoCoordLeft (n := 5) (by norm_num))
      (anisoCoordRight (n := 5) (by norm_num))) :
    projLift hQ' x v = v := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus 5 F b c (by norm_num) hirr
  have hfix := (isAnisoCoord_coordinateQuadMinus (K := F) (by norm_num) hirr).fixSpace_comap_anisoTorusOf hQ hT
  rw [← hfix] at hv
  have hmem : (⟨projLift hQ' x, projLift_mem_orthDerived hQ' x⟩ : orthDerived (Qc F b c)) ∈
      (anisoTorusOf (Qc F b c) hne b c).comap (projHom (Qc F b c)) := by
    rw [Subgroup.mem_comap]
    exact (projHom_projLift hQ' x).symm ▸ hx
  exact hv _ hmem

theorem leviFixBar_lift_fixes {P₁ P₂ : HypPair (Qc F b c)} (hQ' : ∃ v, Qc F b c v ≠ 0)
    {x : matrixProjectiveDerived (Qc F b c)} (hx : x ∈ leviFixBar P₁ P₂) {v : Fin (2 * 5) → F}
    (hv : InW P₁ P₂ v) : projLift hQ' x v = v :=
  (mem_leviFix.mp (projLift_mem_leviFix hQ' hx)).2.2 v hv

structure LayerQGenerators where
  g0 : matrixProjectiveDerived (Qc F b c)
  g2 : matrixProjectiveDerived (Qc F b c)
  g3 : matrixProjectiveDerived (Qc F b c)
  u : matrixProjectiveDerived (Qc F b c)
  mem_g0 : g0 ∈ leviFixBar (cPair F b c 0) (cPair F b c 1)
  mem_g2 : g2 ∈ leviFixBar (cPair F b c 2) (cPair F b c 3)
  mem_g3 : g3 ∈ leviFixBar (cPair F b c 2) (flipPair (cPair F b c 3))
  mem_u : u ∈ anisoTorusOf (Qc F b c) (anisoCoord_ne (n := 5) (by norm_num)) b c
  ord_g0 : orderOf g0 = q
  ord_g2 : orderOf g2 = q
  ord_g3 : orderOf g3 = q
  ord_u : orderOf u = q

theorem exists_layerQGenerators (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hF : Nat.card F = 2 ^ n) (hq : q.Prime) (hqdvd : q ∣ 2 ^ n + 1) (hn : 2 ≤ n) :
    Nonempty (LayerQGenerators (F := F) (b := b) (c := c) (q := q)) := by
  obtain ⟨g0, hg0, hord0⟩ := exists_g0 (F := F) (n := n) (q := q) (b := b) (c := c) hirr hF hq hqdvd hn
  obtain ⟨g2, hg2, hord2⟩ := exists_g2 (F := F) (n := n) (q := q) (b := b) (c := c) hirr hF hq hqdvd hn
  obtain ⟨g3, hg3, hord3⟩ := exists_g3 (F := F) (n := n) (q := q) (b := b) (c := c) hirr hF hq hqdvd hn
  obtain ⟨u, hu, hordu⟩ := exists_u (F := F) (n := n) (q := q) (b := b) (c := c) hirr hF hq hqdvd hn
  exact ⟨⟨g0, g2, g3, u, hg0, hg2, hg3, hu, hord0, hord2, hord3, hordu⟩⟩

private theorem single_split_left_aniso_left (k : Fin 4) :
    (Pi.single (minusIndexEquiv 5 (by norm_num) (Sum.inl k)) (1 : F) : Fin (2 * 5) → F)
      (anisoCoordLeft (n := 5) (by norm_num)) = 0 :=
  Pi.single_eq_of_ne (pairDisjoint_aniso (n := 5) (by norm_num) k).left_ne_left.symm 1

private theorem single_split_left_aniso_right (k : Fin 4) :
    (Pi.single (minusIndexEquiv 5 (by norm_num) (Sum.inl k)) (1 : F) : Fin (2 * 5) → F)
      (anisoCoordRight (n := 5) (by norm_num)) = 0 :=
  Pi.single_eq_of_ne (pairDisjoint_aniso (n := 5) (by norm_num) k).left_ne_right.symm 1

private theorem single_split_right_aniso_left (k : Fin 4) :
    (Pi.single (minusIndexEquiv 5 (by norm_num) (Sum.inr (Sum.inl k))) (1 : F) : Fin (2 * 5) → F)
      (anisoCoordLeft (n := 5) (by norm_num)) = 0 :=
  Pi.single_eq_of_ne (pairDisjoint_aniso (n := 5) (by norm_num) k).right_ne_left.symm 1

private theorem single_split_right_aniso_right (k : Fin 4) :
    (Pi.single (minusIndexEquiv 5 (by norm_num) (Sum.inr (Sum.inl k))) (1 : F) : Fin (2 * 5) → F)
      (anisoCoordRight (n := 5) (by norm_num)) = 0 :=
  Pi.single_eq_of_ne (pairDisjoint_aniso (n := 5) (by norm_num) k).right_ne_right.symm 1

theorem anisoTorus_lift_fixes_split (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {hQ' : ∃ v, Qc F b c v ≠ 0} {x : matrixProjectiveDerived (Qc F b c)}
    (hx : x ∈ anisoTorusOf (Qc F b c) (anisoCoord_ne (n := 5) (by norm_num)) b c) (k : Fin 4) :
    projLift hQ' x (Pi.single (minusIndexEquiv 5 (by norm_num) (Sum.inl k)) (1 : F)) =
        Pi.single (minusIndexEquiv 5 (by norm_num) (Sum.inl k)) (1 : F) ∧
      projLift hQ' x (Pi.single (minusIndexEquiv 5 (by norm_num) (Sum.inr (Sum.inl k))) (1 : F)) =
        Pi.single (minusIndexEquiv 5 (by norm_num) (Sum.inr (Sum.inl k))) (1 : F) := by
  constructor
  · exact anisoTorus_lift_fixes hirr (anisoCoord_ne (n := 5) (by norm_num)) hx
      ⟨single_split_left_aniso_left k, single_split_left_aniso_right k⟩
  · exact anisoTorus_lift_fixes hirr (anisoCoord_ne (n := 5) (by norm_num)) hx
      ⟨single_split_right_aniso_left k, single_split_right_aniso_right k⟩

private theorem inW_flip_flip {P Q : HypPair (Qc F b c)} {x : Fin (2 * 5) → F}
    (h : InW P Q x) : InW P (flipPair Q) x :=
  ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩

theorem zpowers_commute {G₀ : Type} [Group G₀] {a b : G₀} (h : a * b = b * a) :
    ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
  intro x hx y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact ((show Commute a b from h).zpow_zpow k l).eq

theorem commute_of_leviFixBar_of_fixes {P₁ P₂ : HypPair (Qc F b c)} (h₁₂ : P₁.Orth P₂)
    {hQ' : ∃ v, Qc F b c v ≠ 0} {g h : matrixProjectiveDerived (Qc F b c)}
    (hg : g ∈ leviFixBar P₁ P₂)
    (h1 : projLift hQ' h P₁.e = P₁.e) (h2 : projLift hQ' h P₁.f = P₁.f)
    (h3 : projLift hQ' h P₂.e = P₂.e) (h4 : projLift hQ' h P₂.f = P₂.f) :
    g * h = h * g := by
  have hcomm := leviFix_commute_of_fix h₁₂ (projLift_mem_leviFix hQ' hg)
    (Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup (Qc F b c))
      (projLift_mem_orthDerived hQ' h)) h1 h2 h3 h4
  have hcomm' : (⟨projLift hQ' g, projLift_mem_orthDerived hQ' g⟩ : orthDerived (Qc F b c)) * 
      ⟨projLift hQ' h, projLift_mem_orthDerived hQ' h⟩ =
      ⟨projLift hQ' h, projLift_mem_orthDerived hQ' h⟩ *
        ⟨projLift hQ' g, projLift_mem_orthDerived hQ' g⟩ := Subtype.ext hcomm
  have := congrArg (projHom (Qc F b c)) hcomm'
  simpa only [map_mul, projHom_projLift] using this

theorem commute_g0_g2 (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q))
    (hQ' : ∃ v, Qc F b c v ≠ 0) : X.g0 * X.g2 = X.g2 * X.g0 := by
  obtain ⟨h1, h2⟩ := inW_of_orth (P₁ := cPair F b c 0) (P₃ := cPair F b c 2) (P₄ := cPair F b c 3)
    (cPair_orth F b c 0 2 (by decide)) (cPair_orth F b c 0 3 (by decide))
  obtain ⟨h3, h4⟩ := inW_of_orth (P₁ := cPair F b c 1) (P₃ := cPair F b c 2) (P₄ := cPair F b c 3)
    (cPair_orth F b c 1 2 (by decide)) (cPair_orth F b c 1 3 (by decide))
  exact commute_of_leviFixBar_of_fixes (F := F) (hQ' := hQ') (cPair_orth F b c 0 1 (by decide)) X.mem_g0
    (leviFixBar_lift_fixes hQ' X.mem_g2 h1) (leviFixBar_lift_fixes hQ' X.mem_g2 h2)
    (leviFixBar_lift_fixes hQ' X.mem_g2 h3) (leviFixBar_lift_fixes hQ' X.mem_g2 h4)

theorem commute_g0_g3 (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q))
    (hQ' : ∃ v, Qc F b c v ≠ 0) : X.g0 * X.g3 = X.g3 * X.g0 := by
  obtain ⟨h1, h2⟩ := inW_of_orth (P₁ := cPair F b c 0) (P₃ := cPair F b c 2) (P₄ := cPair F b c 3)
    (cPair_orth F b c 0 2 (by decide)) (cPair_orth F b c 0 3 (by decide))
  obtain ⟨h3, h4⟩ := inW_of_orth (P₁ := cPair F b c 1) (P₃ := cPair F b c 2) (P₄ := cPair F b c 3)
    (cPair_orth F b c 1 2 (by decide)) (cPair_orth F b c 1 3 (by decide))
  exact commute_of_leviFixBar_of_fixes (F := F) (hQ' := hQ') (cPair_orth F b c 0 1 (by decide)) X.mem_g0
    (leviFixBar_lift_fixes hQ' X.mem_g3 (inW_flip_flip h1))
    (leviFixBar_lift_fixes hQ' X.mem_g3 (inW_flip_flip h2))
    (leviFixBar_lift_fixes hQ' X.mem_g3 (inW_flip_flip h3))
    (leviFixBar_lift_fixes hQ' X.mem_g3 (inW_flip_flip h4))

theorem commute_g2_g3 (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q)) :
    X.g2 * X.g3 = X.g3 * X.g2 := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus 5 F b c (by norm_num) hirr
  have h := le_centralizer_iff.mp
    (leviFixBar_le_centralizer_flip (cPair_orth F b c 2 3 (by decide)) hQ hT) X.mem_g3
  exact mem_centralizer_iff.mp h X.g2 X.mem_g2

theorem commute_g0_u (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q))
    (hQ' : ∃ v, Qc F b c v ≠ 0) : X.g0 * X.u = X.u * X.g0 := by
  have h0 := anisoTorus_lift_fixes_split (F := F) (b := b) (c := c) hirr (hQ' := hQ') X.mem_u 0
  have h1 := anisoTorus_lift_fixes_split (F := F) (b := b) (c := c) hirr (hQ' := hQ') X.mem_u 1
  exact commute_of_leviFixBar_of_fixes (F := F) (hQ' := hQ') (cPair_orth F b c 0 1 (by decide)) X.mem_g0
    h0.1 h0.2 h1.1 h1.2

theorem commute_g2_u (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q))
    (hQ' : ∃ v, Qc F b c v ≠ 0) : X.g2 * X.u = X.u * X.g2 := by
  have h2 := anisoTorus_lift_fixes_split (F := F) (b := b) (c := c) hirr (hQ' := hQ') X.mem_u 2
  have h3 := anisoTorus_lift_fixes_split (F := F) (b := b) (c := c) hirr (hQ' := hQ') X.mem_u 3
  exact commute_of_leviFixBar_of_fixes (F := F) (hQ' := hQ') (cPair_orth F b c 2 3 (by decide)) X.mem_g2
    h2.1 h2.2 h3.1 h3.2

theorem commute_g3_u (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q))
    (hQ' : ∃ v, Qc F b c v ≠ 0) : X.g3 * X.u = X.u * X.g3 := by
  have h23 := cPair_orth F b c 2 3 (by decide)
  have h2f3 : (cPair F b c 2).Orth (flipPair (cPair F b c 3)) :=
    ⟨h23.ef, h23.ee, h23.ff, h23.fe⟩
  have h2 := anisoTorus_lift_fixes_split (F := F) (b := b) (c := c) hirr (hQ' := hQ') X.mem_u 2
  have h3 := anisoTorus_lift_fixes_split (F := F) (b := b) (c := c) hirr (hQ' := hQ') X.mem_u 3
  exact commute_of_leviFixBar_of_fixes (F := F) (hQ' := hQ') h2f3 X.mem_g3 h2.1 h2.2 h3.2 h3.1

@[expose] noncomputable def bJ (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q)) :
    Subgroup (matrixProjectiveDerived (Qc F b c)) :=
  Subgroup.zpowers X.g0 ⊔ Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3 ⊔ Subgroup.zpowers X.u

theorem bJ_eq_sup (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q)) :
    bJ X = Subgroup.zpowers X.g0 ⊔ Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3 ⊔
      Subgroup.zpowers X.u := rfl

private theorem pow_of_orderOf_eq {G₀ : Type} [Group G₀] {x : G₀} {p : ℕ} (h : orderOf x = p) :
    x ^ p = 1 := by
  rw [← h]; exact pow_orderOf_eq_one x

private theorem zpowers_le_centralizer_zpowers {G₀ : Type} [Group G₀] {a b : G₀}
    (h : a * b = b * a) :
    Subgroup.zpowers a ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G₀) := by
  refine Subgroup.zpowers_le.2 ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (zpowers_commute h a (Subgroup.mem_zpowers a) y hy).symm

theorem isElemAbelian_bJ (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q)) :
    IsElemAbelian q (bJ X) := by
  have hQ' : ∃ v, Qc F b c v ≠ 0 :=
    (isAnisoCoord_coordinateQuadMinus (K := F) (by norm_num) hirr).exists_ne_zero
  have h0 : IsElemAbelian q (Subgroup.zpowers X.g0) :=
    isElemAbelian_zpowers (pow_of_orderOf_eq X.ord_g0)
  have h2 : IsElemAbelian q (Subgroup.zpowers X.g2) :=
    isElemAbelian_zpowers (pow_of_orderOf_eq X.ord_g2)
  have h3 : IsElemAbelian q (Subgroup.zpowers X.g3) :=
    isElemAbelian_zpowers (pow_of_orderOf_eq X.ord_g3)
  have hu : IsElemAbelian q (Subgroup.zpowers X.u) :=
    isElemAbelian_zpowers (pow_of_orderOf_eq X.ord_u)
  have c02 : ∀ a ∈ Subgroup.zpowers X.g0, ∀ b ∈ Subgroup.zpowers X.g2, a * b = b * a :=
    zpowers_commute (commute_g0_g2 X hQ')
  have c03 : ∀ a ∈ Subgroup.zpowers X.g0, ∀ b ∈ Subgroup.zpowers X.g3, a * b = b * a :=
    zpowers_commute (commute_g0_g3 X hQ')
  have c23 : ∀ a ∈ Subgroup.zpowers X.g2, ∀ b ∈ Subgroup.zpowers X.g3, a * b = b * a :=
    zpowers_commute (commute_g2_g3 hirr X)
  have c0u : ∀ a ∈ Subgroup.zpowers X.g0, ∀ b ∈ Subgroup.zpowers X.u, a * b = b * a :=
    zpowers_commute (commute_g0_u hirr X hQ')
  have c2u : ∀ a ∈ Subgroup.zpowers X.g2, ∀ b ∈ Subgroup.zpowers X.u, a * b = b * a :=
    zpowers_commute (commute_g2_u hirr X hQ')
  have c3u : ∀ a ∈ Subgroup.zpowers X.g3, ∀ b ∈ Subgroup.zpowers X.u, a * b = b * a :=
    zpowers_commute (commute_g3_u hirr X hQ')
  have c12_3 : ∀ a ∈ Subgroup.zpowers X.g0 ⊔ Subgroup.zpowers X.g2,
      ∀ b ∈ Subgroup.zpowers X.g3, a * b = b * a := by
    have hsup : Subgroup.zpowers X.g0 ⊔ Subgroup.zpowers X.g2 ≤
        Subgroup.centralizer (Subgroup.zpowers X.g3 : Set _) :=
      sup_le (zpowers_le_centralizer_zpowers (commute_g0_g3 X hQ'))
        (zpowers_le_centralizer_zpowers (commute_g2_g3 hirr X))
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hsup ha) b hb).symm
  have c12_u : ∀ a ∈ Subgroup.zpowers X.g0 ⊔ Subgroup.zpowers X.g2,
      ∀ b ∈ Subgroup.zpowers X.u, a * b = b * a := by
    have hsup : Subgroup.zpowers X.g0 ⊔ Subgroup.zpowers X.g2 ≤
        Subgroup.centralizer (Subgroup.zpowers X.u : Set _) :=
      sup_le (zpowers_le_centralizer_zpowers (commute_g0_u hirr X hQ'))
        (zpowers_le_centralizer_zpowers (commute_g2_u hirr X hQ'))
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hsup ha) b hb).symm
  have c123_u : ∀ a ∈ (Subgroup.zpowers X.g0 ⊔ Subgroup.zpowers X.g2) ⊔
      Subgroup.zpowers X.g3, ∀ b ∈ Subgroup.zpowers X.u, a * b = b * a := by
    have h12 : Subgroup.zpowers X.g0 ⊔ Subgroup.zpowers X.g2 ≤
        Subgroup.centralizer (Subgroup.zpowers X.u : Set _) :=
      sup_le (zpowers_le_centralizer_zpowers (commute_g0_u hirr X hQ'))
        (zpowers_le_centralizer_zpowers (commute_g2_u hirr X hQ'))
    have hsup : (Subgroup.zpowers X.g0 ⊔ Subgroup.zpowers X.g2) ⊔ Subgroup.zpowers X.g3 ≤
        Subgroup.centralizer (Subgroup.zpowers X.u : Set _) :=
      sup_le h12 (zpowers_le_centralizer_zpowers (commute_g3_u hirr X hQ'))
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hsup ha) b hb).symm
  exact (((h0.sup_of_commute h2 c02).sup_of_commute h3 c12_3).sup_of_commute hu c123_u)

theorem leviFixBar_le_rootLeviBar {P₁ P₂ : HypPair (Qc F b c)} :
    leviFixBar P₁ P₂ ≤ rootLeviBar (Qc F b c) P₁ P₂ := by
  rintro _ ⟨Y, hY, rfl⟩
  exact ⟨Y, mem_subgroupOf.mpr (mem_leviFix.mp (mem_subgroupOf.mp hY)).2.1, rfl⟩

theorem mem_rootLeviBar_of_lift {P₁ P₂ : HypPair (Qc F b c)} (hQ' : ∃ v, Qc F b c v ≠ 0)
    {x : matrixProjectiveDerived (Qc F b c)} (hx : projLift hQ' x ∈ rootLevi (Qc F b c) P₁ P₂) :
    x ∈ rootLeviBar (Qc F b c) P₁ P₂ :=
  ⟨⟨projLift hQ' x, projLift_mem_orthDerived hQ' x⟩, mem_subgroupOf.mpr hx,
    projHom_projLift hQ' x⟩

theorem bJ_le_rootLeviBar (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q)) :
    bJ X ≤ rootLeviBar (Qc F b c) (cPair F b c 0) (cPair F b c 1) := by
  have hQ' : ∃ v, Qc F b c v ≠ 0 :=
    (isAnisoCoord_coordinateQuadMinus (K := F) (by norm_num) hirr).exists_ne_zero
  have hO : projLift hQ' X.g2 ∈ TauCeti.QuadraticMap.orthogonalGroup (Qc F b c) :=
    Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup (Qc F b c))
      (projLift_mem_orthDerived hQ' X.g2)
  have hO3 : projLift hQ' X.g3 ∈ TauCeti.QuadraticMap.orthogonalGroup (Qc F b c) :=
    Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup (Qc F b c))
      (projLift_mem_orthDerived hQ' X.g3)
  have hOu : projLift hQ' X.u ∈ TauCeti.QuadraticMap.orthogonalGroup (Qc F b c) :=
    Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup (Qc F b c))
      (projLift_mem_orthDerived hQ' X.u)
  obtain ⟨h20, h2f0⟩ := inW_of_orth (P₁ := cPair F b c 0) (P₃ := cPair F b c 2)
    (P₄ := cPair F b c 3) (cPair_orth F b c 0 2 (by decide)) (cPair_orth F b c 0 3 (by decide))
  obtain ⟨h21, h2f1⟩ := inW_of_orth (P₁ := cPair F b c 1) (P₃ := cPair F b c 2)
    (P₄ := cPair F b c 3) (cPair_orth F b c 1 2 (by decide)) (cPair_orth F b c 1 3 (by decide))
  obtain ⟨h30, h3f0⟩ := inW_of_orth (P₁ := cPair F b c 0) (P₃ := cPair F b c 2)
    (P₄ := cPair F b c 3) (cPair_orth F b c 0 2 (by decide)) (cPair_orth F b c 0 3 (by decide))
  obtain ⟨h31, h3f1⟩ := inW_of_orth (P₁ := cPair F b c 1) (P₃ := cPair F b c 2)
    (P₄ := cPair F b c 3) (cPair_orth F b c 1 2 (by decide)) (cPair_orth F b c 1 3 (by decide))
  have hu0 := anisoTorus_lift_fixes_split (F := F) (b := b) (c := c) hirr (hQ' := hQ') X.mem_u 0
  have hu1 := anisoTorus_lift_fixes_split (F := F) (b := b) (c := c) hirr (hQ' := hQ') X.mem_u 1
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · exact Subgroup.zpowers_le.2 (leviFixBar_le_rootLeviBar X.mem_g0)
  · exact Subgroup.zpowers_le.2 (mem_rootLeviBar_of_lift hQ' (mem_rootLevi_of_fix (P₁ := cPair F b c 0)
      (P₂ := cPair F b c 1) hO
      (leviFixBar_lift_fixes hQ' X.mem_g2 h20) (leviFixBar_lift_fixes hQ' X.mem_g2 h2f0)
      (leviFixBar_lift_fixes hQ' X.mem_g2 h21) (leviFixBar_lift_fixes hQ' X.mem_g2 h2f1)))
  · exact Subgroup.zpowers_le.2 (mem_rootLeviBar_of_lift hQ' (mem_rootLevi_of_fix (P₁ := cPair F b c 0)
      (P₂ := cPair F b c 1) hO3
      (leviFixBar_lift_fixes hQ' X.mem_g3 (inW_flip_flip h30))
      (leviFixBar_lift_fixes hQ' X.mem_g3 (inW_flip_flip h3f0))
      (leviFixBar_lift_fixes hQ' X.mem_g3 (inW_flip_flip h31))
      (leviFixBar_lift_fixes hQ' X.mem_g3 (inW_flip_flip h3f1))))
  · exact Subgroup.zpowers_le.2 (mem_rootLeviBar_of_lift hQ' (mem_rootLevi_of_fix (P₁ := cPair F b c 0)
      (P₂ := cPair F b c 1) hOu hu0.1 hu0.2 hu1.1 hu1.2))

theorem bJ_le_normalizer_rootRadicalBar (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q)) :
    bJ X ≤ Subgroup.normalizer
      (rootRadicalBar (Qc F b c) (cPair F b c 0) (cPair F b c 1) :
        Set (matrixProjectiveDerived (Qc F b c))) :=
  (bJ_le_rootLeviBar hirr X).trans
    (rootLeviBar_le_normalizer (cPair_orth F b c 0 1 (by decide)))

end CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaMinusLD

