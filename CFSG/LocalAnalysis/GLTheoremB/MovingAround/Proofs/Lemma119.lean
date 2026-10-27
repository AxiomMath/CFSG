module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Alpha
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18Comp
public import CFSG.GroupTheory.PrimeCorefreeQuasisimple
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Defs
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut IsLocallyBalanced IsWeaklyLocallyBalanced)
open scoped MatrixGroups

@[expose] def Input22_3_2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p : ℕ), p.Prime → ∀ (B L L₁ : Subgroup Y) (𝓛 : Set (Subgroup Y)),
    IsElemAbelian p B → B ≤ Subgroup.normalizer (L : Set Y) → L₁ ∈ 𝓛 → 2 ≤ CFSG.Open.pRank p B →
    p ∣ Nat.card L → L = sSup 𝓛 → (∀ X ∈ 𝓛, IsComponentOf X L) →
    (∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x) →
    (∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, ∃ b ∈ B, GLBConj b X = X') →
    (∃ b ∈ B, b ≠ 1 ∧ (b ∈ Subgroup.centralizer (L : Set Y) ∨ b ∉ Subgroup.normalizer (L₁ : Set Y))) →
    L = sSup {Z : Subgroup Y | ∃ b ∈ B, b ≠ 1 ∧ (b ∈ Subgroup.centralizer (L : Set Y) ∨
      b ∉ Subgroup.normalizer (L₁ : Set Y)) ∧ Z = GLAPLayer p (L ⊓ Subgroup.centralizer ({b} : Set Y))}

@[expose] def Input18_3_diag : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p : ℕ), p.Prime → ∀ (L : Subgroup Y) (𝓛 : Set (Subgroup Y)) (b : Y),
    orderOf b = p → b ∈ Subgroup.normalizer (L : Set Y) → L = sSup 𝓛 →
    (∀ X ∈ 𝓛, IsComponentOf X L) →
    (∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x) →
    (b ∈ Subgroup.centralizer (L : Set Y) ∨ ∀ X ∈ 𝓛, b ∉ Subgroup.normalizer (X : Set Y)) →
    ∀ Q : Subgroup Y, GLAPComponent p (L ⊓ Subgroup.centralizer ({b} : Set Y)) Q →
      ∃ X ∈ 𝓛, Nonempty ((barOf p Q ⧸ Subgroup.center (barOf p Q)) ≃* (↥X ⧸ Subgroup.center ↥X))

@[expose] def Input23_20_W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K B : Subgroup G),
    GLAPComponent 3 X K → IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) →
    B ≤ X → IsElemAbelian 3 B → CFSG.Open.pRank 3 B = 2 → B ≤ Subgroup.normalizer (K : Set G) →
    (¬ ∀ x ∈ B, InducesInner 3 K x) →
    K ≤ (⨆ (x : G) (_ : x ∈ B ∧ x ≠ 1),
          (GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) ⊔
            GLAPLayer 3 (K ⊓ Subgroup.centralizer ({x} : Set G)))) ⊔ GLAPPrimeCoreOf 3 K ∧
    (∀ x ∈ B, x ≠ 1 → ∀ Q : Subgroup G, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) Q →
      IsLThreeFour (barOf 3 Q ⧸ Subgroup.center (barOf 3 Q)) ∨
        IsAltType 5 (barOf 3 Q ⧸ Subgroup.center (barOf 3 Q)))

@[expose] def Input7_Fi22 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSporType .Fi22 X →
    (∀ φ : MulAut X, IsPGroup 5 (Subgroup.zpowers φ) → φ ∈ innerAut X) ∧
    (∀ A : Subgroup (MulAut X), IsElemAbelian 5 A → CFSG.Open.pRank 5 A ≤ 2)

@[expose] def Input7_L34 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → IsLThreeFour (X ⧸ Subgroup.center X) →
    GLAPPrimeCore 3 X = ⊥ → ∀ A : Subgroup (MulAut X), IsElemAbelian 3 A → CFSG.Open.pRank 3 A ≤ 2

@[expose] def Input_Fi22_centreless : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSporType .Fi22 X → Subgroup.center X = ⊥

@[expose] def Input_order_dvd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime →
    ((p = 5 ∧ IsSporType .Fi22 X) ∨ (p = 3 ∧ IsLThreeFour (X ⧸ Subgroup.center X))) →
      p ∣ Nat.card X

@[expose] def Input_not_LTwoTwentySeven : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsLTwoTwentySeven X →
    ¬ (IsLThreeFour (X ⧸ Subgroup.center X) ∨ IsAltType 5 (X ⧸ Subgroup.center X))

section Generic

variable {G : Type} [Group G]

theorem l119_glaPComponent_of_isSubnormal {p : ℕ} (hp : p.Prime) [Finite G] {X Y K : Subgroup G}
    (hXY : IsSubnormal X Y) (hK : GLAPComponent p X K) : GLAPComponent p Y K := by
  obtain ⟨hKX, hsnKX, hcompX, hminX⟩ := hK
  have hXY' : X ≤ Y := isSubnormal_le' hXY
  have hKY : K ≤ Y := hKX.trans hXY'
  have hsnKY : IsSubnormal K Y := isSubnormal_trans' hsnKX hXY
  refine ⟨hKY, hsnKY, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := Y) p hsnKY
    rwa [barX_self] at this
  · have e : ↥(barX p X K) ≃* ↥(barX p Y K) :=
      (quotEquivBarX hp hKX hsnKX).symm.trans (quotEquivBarX hp hKY hsnKY)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hcompX.2.2
  · intro J hJ hJsnY heq
    have hJK : J ≤ K := hJ.le
    have hJX : IsSubnormal J X := isSubnormal_of_le_of_le hJsnY (hJK.trans hKX) hXY'
    refine hminX J hJ hJX ?_
    show barX p X J = barX p X K
    refine le_antisymm (barX_mono p hJK) ?_
    refine barX_le_of_forall (hJK.trans hKX) (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := Y) (le_of_eq heq.symm) hk (hKY hk)
    refine ⟨j, hj, ?_⟩
    have hmem : j⁻¹ * k ∈ X ⊓ GLAPPrimeCoreOf p Y :=
      ⟨X.mul_mem (X.inv_mem ((hJK.trans hKX) hj)) (hKX hk), hjk⟩
    rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hXY] at hmem
    exact hmem

theorem l119_isSubnormal_sSup_components [Finite G] {𝓛 : Set (Subgroup G)}
    (h𝓛 : ∀ X ∈ 𝓛, IsComponentOf X ⊤) : IsSubnormal (sSup 𝓛) ⊤ := by
  have hXS : ∀ X : Subgroup G, IsComponentOf X ⊤ → ∀ x ∈ X, ∀ s ∈ sSup 𝓛,
      x * s * x⁻¹ ∈ sSup 𝓛 := by
    intro X hXc x hx
    have hle : sSup 𝓛 ≤ (sSup 𝓛).comap (MulAut.conj x).toMonoidHom := by
      refine sSup_le fun Y' hY' => ?_
      intro y hy
      show x * y * x⁻¹ ∈ sSup 𝓛
      by_cases hXY' : X = Y'
      · subst hXY'
        exact le_sSup hY' (X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx))
      · have hc := comp_comm hXc (h𝓛 Y' hY') hXY' hx hy
        have h1 : x * y * x⁻¹ = y := by rw [hc]; group
        rw [h1]
        exact le_sSup hY' hy
    intro s hs
    exact hle hs
  have hXN : ∀ X : Subgroup G, IsComponentOf X ⊤ →
      X ≤ Subgroup.normalizer ((sSup 𝓛 : Subgroup G) : Set G) := by
    intro X hXc x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hXS X hXc x hx h hh
    · intro hh
      have := hXS X hXc x⁻¹ (X.inv_mem hx) _ hh
      simpa [mul_assoc] using this
  have hSE : sSup 𝓛 ≤ compE G := sSup_le fun X hX => le_compE (h𝓛 X hX)
  have hEN : compE G ≤ Subgroup.normalizer ((sSup 𝓛 : Subgroup G) : Set G) := by
    unfold compE
    exact iSup₂_le fun X hXc => hXN X hXc
  have hnormal : ((sSup 𝓛).subgroupOf (compE G)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSE).2 hEN
  exact isSubnormal_trans' (IsSubnormal.step hSE hnormal (IsSubnormal.refl _))
    (isSubnormal_of_normal compE_normal)

end Generic

section Conj

variable {G : Type} [Group G] [Finite G] {p : ℕ} {C H : Subgroup G}

theorem l119_barX_gLBConj {g : G} (hg : g ∈ C) (hH : H ≤ C) :
    barX p C (GLBConj g H) =
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨g, hg⟩) (barX p C H) := by
  ext z
  rw [mem_gLBConj]
  set gC : ↥C := ⟨g, hg⟩ with hgC
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : (c : G) ∈ GLBConj g H := (Subgroup.mem_subgroupOf).1 hc
    rw [mem_gLBConj] at hc'
    refine ⟨⟨g * c * g⁻¹, C.mul_mem (C.mul_mem hg c.2) (C.inv_mem hg)⟩,
      (Subgroup.mem_subgroupOf).2 hc', ?_⟩
    have hcc : (⟨g * c * g⁻¹, C.mul_mem (C.mul_mem hg c.2) (C.inv_mem hg)⟩ : ↥C) =
        gC * c * gC⁻¹ := by
      ext
      simp [hgC]
    rw [hcc, map_mul, map_mul, map_inv]
  · rintro ⟨h, hh, hzh⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥C) z
    have hh' : (h : G) ∈ H := (Subgroup.mem_subgroupOf).1 hh
    have hzh2 : (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) h =
        (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) (gC * c * gC⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      exact hzh
    have hn : h⁻¹ * (gC * c * gC⁻¹) ∈ GLAPPrimeCore p ↥C := QuotientGroup.eq.1 hzh2
    refine ⟨gC⁻¹ * h * gC, ?_, ?_⟩
    · apply (Subgroup.mem_subgroupOf).2
      rw [mem_gLBConj]
      have hconj : g * ((gC⁻¹ * h * gC : ↥C) : G) * g⁻¹ = (h : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgC]
        group
      rw [hconj]
      exact hh'
    · apply QuotientGroup.eq.2
      have key : (gC⁻¹ * h * gC)⁻¹ * c = gC⁻¹ * (h⁻¹ * (gC * c * gC⁻¹)) * (gC⁻¹)⁻¹ := by
        group
      rw [key]
      exact Subgroup.Normal.conj_mem (GLAPPrimeCore.normal p ↥C) _ hn gC⁻¹

end Conj

section Family

variable {G : Type} [Group G] [Finite G] {p : ℕ} {C K : Subgroup G}

theorem l119_isComponent_barX (hK : GLAPComponent p C K) :
    IsComponentOf (barX p C K) ⊤ := hK.2.2.1

theorem l119_conj_component (hK : GLAPComponent p C K) (z : ↥C) :
    IsComponentOf (GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) (barX p C K)) ⊤ :=
  isComponentOf_gLBConj (l119_isComponent_barX hK) _

theorem l119_conj_comm (hK : GLAPComponent p C K) {z z' : ↥C}
    (hne : GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) (barX p C K) ≠
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z') (barX p C K))
    {x y : ↥C ⧸ GLAPPrimeCore p ↥C}
    (hx : x ∈ GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) (barX p C K))
    (hy : y ∈ GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z') (barX p C K)) :
    x * y = y * x :=
  comp_comm (l119_conj_component hK z) (l119_conj_component hK z') hne hx hy

theorem l119_conj_trans (z z' : ↥C) :
    GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) (z⁻¹ * z')) (GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) (barX p C K)) =
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z') (barX p C K) := by
  rw [gLBConj_gLBConj, map_mul, map_inv]
  congr 1
  group

end Family

section Quasisimple

theorem l119_normal_le_center {Z : Type} [Group Z] (hZ : CFSG.Open.IsQuasisimple Z) {W : Subgroup Z}
    [hWn : W.Normal] (hW : W ≠ ⊤) : W ≤ Subgroup.center Z := by
  have hsimple : IsSimpleGroup (Z ⧸ Subgroup.center Z) := hZ.2
  have hnorm : (W.map (QuotientGroup.mk' (Subgroup.center Z))).Normal :=
    hWn.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (W.map (QuotientGroup.mk' (Subgroup.center Z))) with hb | ht
  · intro w hw
    have h1 : QuotientGroup.mk' (Subgroup.center Z) w ∈
        W.map (QuotientGroup.mk' (Subgroup.center Z)) := Subgroup.mem_map_of_mem _ hw
    rw [hb, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff w).1 h1
  · exfalso
    apply hW
    have hcov : ∀ g : Z, ∃ w ∈ W, ∃ c ∈ Subgroup.center Z, g = w * c := by
      intro g
      have hg : QuotientGroup.mk' (Subgroup.center Z) g ∈
          W.map (QuotientGroup.mk' (Subgroup.center Z)) := by rw [ht]; exact Subgroup.mem_top _
      obtain ⟨w, hw, e⟩ := hg
      refine ⟨w, hw, w⁻¹ * g, ?_, by group⟩
      exact (QuotientGroup.eq (s := Subgroup.center Z)).1 e
    have hcomm : ∀ a b : Z ⧸ W, a * b = b * a := by
      intro a b
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      have hx : ∃ c ∈ Subgroup.center Z, (QuotientGroup.mk x : Z ⧸ W) = QuotientGroup.mk c := by
        obtain ⟨w, hw, c, hc, rfl⟩ := hcov x
        refine ⟨c, hc, (QuotientGroup.eq).2 ?_⟩
        have := Subgroup.Normal.conj_mem hWn _ (W.inv_mem hw) c⁻¹
        simpa using this
      have hy : ∃ c ∈ Subgroup.center Z, (QuotientGroup.mk y : Z ⧸ W) = QuotientGroup.mk c := by
        obtain ⟨w, hw, c, hc, rfl⟩ := hcov y
        refine ⟨c, hc, (QuotientGroup.eq).2 ?_⟩
        have := Subgroup.Normal.conj_mem hWn _ (W.inv_mem hw) c⁻¹
        simpa using this
      obtain ⟨c, hc, hxc⟩ := hx
      obtain ⟨d, hd, hyd⟩ := hy
      rw [hxc, hyd, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact (Subgroup.mem_center_iff.1 hc d).symm ▸ (Subgroup.mem_center_iff.1 hd c).symm ▸ rfl
    have htop : ∀ x y : Z, x * y * x⁻¹ * y⁻¹ ∈ W := by
      intro x y
      have h1 : (QuotientGroup.mk' W) (x * y * x⁻¹ * y⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        have hc := hcomm (QuotientGroup.mk' W x) (QuotientGroup.mk' W y)
        calc (QuotientGroup.mk' W x) * (QuotientGroup.mk' W y) * (QuotientGroup.mk' W x)⁻¹ *
              (QuotientGroup.mk' W y)⁻¹
            = ((QuotientGroup.mk' W y) * (QuotientGroup.mk' W x)) * (QuotientGroup.mk' W x)⁻¹ *
              (QuotientGroup.mk' W y)⁻¹ := by rw [hc]
          _ = 1 := by group
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hcomm2 : ⁅(⊤ : Subgroup Z), (⊤ : Subgroup Z)⁆ ≤ W := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      exact htop x y
    have h4 : commutator Z ≤ W := hcomm2
    rw [hZ.1] at h4
    exact top_le_iff.1 h4

end Quasisimple

section Pieces

variable {G : Type} [Group G] [Finite G]

theorem l119_isComponentOf_sSup {𝓛 : Set (Subgroup G)} (h𝓛 : ∀ X ∈ 𝓛, IsComponentOf X ⊤)
    (hc : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x)
    {X : Subgroup G} (hX : X ∈ 𝓛) : IsComponentOf X (sSup 𝓛) := by
  have hXS : X ≤ sSup 𝓛 := le_sSup hX
  have hNorm : sSup 𝓛 ≤ Subgroup.normalizer (X : Set G) := by
    refine sSup_le fun Y hY => ?_
    intro y hy
    by_cases hXY : X = Y
    · subst hXY
      exact Subgroup.le_normalizer hy
    · apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact hc X hX Y hY hXY x hx y hy
  have hsn : IsSubnormal X (sSup 𝓛) :=
    IsSubnormal.step hXS ((Subgroup.normal_subgroupOf_iff_le_normalizer hXS).2 hNorm)
      (IsSubnormal.refl _)
  exact ⟨hXS, hsn, (h𝓛 X hX).2.2⟩

end Pieces

section CentreQuot

theorem l119_center_quot_eq_bot {Z : Type} [Group Z] (hZ : CFSG.Open.IsQuasisimple Z) :
    Subgroup.center (Z ⧸ Subgroup.center Z) = ⊥ := by
  have hsimple : IsSimpleGroup (Z ⧸ Subgroup.center Z) := hZ.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Z ⧸ Subgroup.center Z)) with
    hb | ht
  · exact hb
  · exfalso
    have hq : ∀ x y : Z, QuotientGroup.mk x * (QuotientGroup.mk y : Z ⧸ Subgroup.center Z) =
        QuotientGroup.mk y * QuotientGroup.mk x := by
      intro x y
      have hx : (QuotientGroup.mk x : Z ⧸ Subgroup.center Z) ∈
          Subgroup.center (Z ⧸ Subgroup.center Z) := by
        rw [ht]; exact Subgroup.mem_top _
      exact ((Subgroup.mem_center_iff.1 hx) _).symm
    have hc : ∀ x y : Z, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center Z := by
      intro x y
      rw [← QuotientGroup.eq_one_iff]
      have h1 := hq x y
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      calc (QuotientGroup.mk x : Z ⧸ Subgroup.center Z) * QuotientGroup.mk y *
            (QuotientGroup.mk x)⁻¹ * (QuotientGroup.mk y)⁻¹
          = (QuotientGroup.mk y * QuotientGroup.mk x) * (QuotientGroup.mk x)⁻¹ *
            (QuotientGroup.mk y)⁻¹ := by rw [h1]
        _ = 1 := by group
    have hcomm : ⁅(⊤ : Subgroup Z), (⊤ : Subgroup Z)⁆ ≤ Subgroup.center Z := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      exact hc x y
    have h4 : commutator Z ≤ Subgroup.center Z := hcomm
    rw [hZ.1] at h4
    have hsub : Subsingleton (Z ⧸ Subgroup.center Z) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.eq]
      have : x⁻¹ * y ∈ Subgroup.center Z := h4 (Subgroup.mem_top _)
      exact this
    exact not_subsingleton (Z ⧸ Subgroup.center Z) hsub

theorem l119_center_quot_map {Z : Type} [Group Z] (hZ : CFSG.Open.IsQuasisimple Z)
    {W : Subgroup Z} [W.Normal] (hW : W ≤ Subgroup.center Z) :
    Subgroup.center (Z ⧸ W) = (Subgroup.center Z).map (QuotientGroup.mk' W) := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  constructor
  · intro hx
    have hxc : ∀ g : Z, x⁻¹ * g⁻¹ * x * g ∈ Subgroup.center Z := by
      intro g
      have h1 := (Subgroup.mem_center_iff.1 hx) (QuotientGroup.mk g)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h1
      have h2 : (g * x)⁻¹ * (x * g) ∈ W := QuotientGroup.eq.1 h1
      have h3 : (g * x)⁻¹ * (x * g) = x⁻¹ * g⁻¹ * x * g := by group
      rw [h3] at h2
      exact hW h2
    have hxZ : (QuotientGroup.mk x : Z ⧸ Subgroup.center Z) ∈
        Subgroup.center (Z ⧸ Subgroup.center Z) := by
      rw [Subgroup.mem_center_iff]
      intro g'
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g'
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact QuotientGroup.eq.2 (by
        have h4 := hxc g
        have h5 : (g * x)⁻¹ * (x * g) = x⁻¹ * g⁻¹ * x * g := by group
        rw [h5]
        exact h4)
    rw [l119_center_quot_eq_bot hZ, Subgroup.mem_bot] at hxZ
    exact ⟨x, (QuotientGroup.eq_one_iff x).1 hxZ, rfl⟩
  · rintro ⟨c, hc, hcx⟩
    rw [← hcx, Subgroup.mem_center_iff]
    intro g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
    have hch : h * c = c * h := (Subgroup.mem_center_iff.1 hc h)
    show QuotientGroup.mk h * QuotientGroup.mk c = QuotientGroup.mk c * QuotientGroup.mk h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hch]

theorem l119_center_quot_iso {Z : Type} [Group Z] (hZ : CFSG.Open.IsQuasisimple Z)
    {W : Subgroup Z} [W.Normal] (hW : W ≤ Subgroup.center Z) :
    Nonempty ((Z ⧸ W) ⧸ Subgroup.center (Z ⧸ W) ≃* Z ⧸ Subgroup.center Z) := by
  have e := l119_center_quot_map hZ hW
  exact ⟨(QuotientGroup.quotientMulEquivOfEq e).trans
    (QuotientGroup.quotientQuotientEquivQuotient W (Subgroup.center Z) hW)⟩

end CentreQuot

section BarTransfer

variable {G : Type} [Group G] [Finite G]

theorem l119_isQuasisimple_barOf {p : ℕ} (hp : p.Prime) {X Q : Subgroup G}
    (hQ : GLAPComponent p X Q) : CFSG.Open.IsQuasisimple (↥Q ⧸ GLAPPrimeCore p ↥Q) := by
  have e := quotEquivBarX hp hQ.1 hQ.2.1
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm
    (hQ.2.2.1).2.2

theorem l119_barOf_centre_iso {p : ℕ} (hp : p.Prime) {P : Type} [Group P] [Finite P] {T : Type} [Group T]
    (f : P →* T) {R : Subgroup T} (hR : f.range = R)
    (hP : CFSG.Open.IsQuasisimple (P ⧸ GLAPPrimeCore p P))
    (hR' : CFSG.Open.IsQuasisimple (↥R ⧸ GLAPPrimeCore p ↥R)) :
    Nonempty ((↥R ⧸ GLAPPrimeCore p ↥R) ⧸ Subgroup.center (↥R ⧸ GLAPPrimeCore p ↥R) ≃*
      (P ⧸ GLAPPrimeCore p P) ⧸ Subgroup.center (P ⧸ GLAPPrimeCore p P)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let φ₀ : P →* ↥R := f.codRestrict R (fun x => by
    rw [← hR]; exact MonoidHom.mem_range.2 ⟨x, rfl⟩)
  have hφ₀ : Function.Surjective φ₀ := by
    intro r
    obtain ⟨x, hx⟩ : r.1 ∈ f.range := by rw [hR]; exact r.2
    exact ⟨x, Subtype.ext hx⟩
  let comp : P →* (↥R ⧸ GLAPPrimeCore p ↥R) :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥R)).comp φ₀
  have hcomp : Function.Surjective comp :=
    (QuotientGroup.mk'_surjective _).comp hφ₀
  have hO : GLAPPrimeCore p P ≤ comp.ker := by
    intro x hx
    have hnorm : ((GLAPPrimeCore p P).map φ₀).Normal :=
      Subgroup.Normal.map (GLAPPrimeCore.normal p P) φ₀ hφ₀
    have hdvd : Nat.card ↥((GLAPPrimeCore p P).map φ₀) ∣ Nat.card ↥(GLAPPrimeCore p P) :=
      Subgroup.card_map_dvd (GLAPPrimeCore p P) φ₀
    have hpc : Nat.Coprime p (Nat.card ↥(GLAPPrimeCore p P)) := CFSG.pPrimeCore_coprime_card
    have hcop : Nat.Coprime p (Nat.card ↥((GLAPPrimeCore p P).map φ₀)) :=
      Nat.Coprime.coprime_dvd_right hdvd hpc
    have hmem : φ₀ x ∈ GLAPPrimeCore p ↥R :=
      (CFSG.GroupTheory.le_pPrimeCore_of_normal hnorm hcop) (Subgroup.mem_map_of_mem φ₀ hx)
    exact (QuotientGroup.eq_one_iff (φ₀ x)).2 hmem
  let phib : (P ⧸ GLAPPrimeCore p P) →* (↥R ⧸ GLAPPrimeCore p ↥R) :=
    QuotientGroup.lift (GLAPPrimeCore p P) comp hO
  have hphib : Function.Surjective phib := by
    intro r
    obtain ⟨x, rfl⟩ := hcomp r
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hnt : Nontrivial (↥R ⧸ GLAPPrimeCore p ↥R) := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    have hsub' : Subsingleton ((↥R ⧸ GLAPPrimeCore p ↥R) ⧸ Subgroup.center (↥R ⧸ GLAPPrimeCore p ↥R)) :=
      ⟨fun a b => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
        congr 1
        exact Subsingleton.elim _ _⟩
    haveI := hR'.2.toNontrivial
    exact not_subsingleton _ hsub'
  have hWne : phib.ker ≠ ⊤ := by
    intro hW
    have hall : ∀ r : (↥R ⧸ GLAPPrimeCore p ↥R), r = 1 := by
      intro r
      obtain ⟨x, rfl⟩ := hphib r
      have hx : x ∈ phib.ker := by rw [hW]; exact Subgroup.mem_top _
      exact (MonoidHom.mem_ker.1 hx)
    exact (not_nontrivial_iff_subsingleton.2 ⟨fun a b => by rw [hall a, hall b]⟩) hnt
  have hWc : phib.ker ≤ Subgroup.center (P ⧸ GLAPPrimeCore p P) :=
    l119_normal_le_center hP hWne
  let e1 : (P ⧸ GLAPPrimeCore p P) ⧸ phib.ker ≃* (↥R ⧸ GLAPPrimeCore p ↥R) :=
    QuotientGroup.quotientKerEquivOfSurjective phib hphib
  have e2 := QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) e1
    (Subgroup.map_center_eq e1)
  obtain ⟨e3⟩ := l119_center_quot_iso hP hWc
  exact ⟨e2.symm.trans e3⟩

end BarTransfer

section Lift

variable {G : Type} [Group G] [Finite G]

theorem l119_range_eq {p : ℕ} {C P : Subgroup G} (hPC : P ≤ C) :
    ((QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (Subgroup.inclusion hPC)).range = barX p C P := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Subgroup.inclusion hPC x, (Subgroup.mem_subgroupOf).2 x.2, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c, (Subgroup.mem_subgroupOf).1 hc⟩, rfl⟩

theorem l119_layer_piece {p : ℕ} (hp : p.Prime) {C : Subgroup G} {b : G} (hbC : b ∈ C)
    (hb : IsPGroup p (Subgroup.zpowers b))
    {L : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)} (hL : IsSubnormal L ⊤)
    {Q : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)}
    (hQ : GLAPComponent p (L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩} : Set (↥C ⧸ GLAPPrimeCore p ↥C))) Q) :
    ∃ P : Subgroup G, GLAPComponent p (C ⊓ Subgroup.centralizer ({b} : Set G)) P ∧
      barX p C P = Q ∧
      Nonempty ((↥Q ⧸ GLAPPrimeCore p ↥Q) ⧸ Subgroup.center (↥Q ⧸ GLAPPrimeCore p ↥Q) ≃*
        (↥P ⧸ GLAPPrimeCore p ↥P) ⧸ Subgroup.center (↥P ⧸ GLAPPrimeCore p ↥P)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hsub : IsSubnormal (L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩} : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
      (Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩} :
        Set (↥C ⧸ GLAPPrimeCore p ↥C))) := by
    have h := isSubnormal_inf hL (Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩} : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
    rwa [top_inf_eq] at h
  have hQC : GLAPComponent p (Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩} : Set (↥C ⧸ GLAPPrimeCore p ↥C))) Q :=
    l119_glaPComponent_of_isSubnormal hp hsub hQ
  have hdL : b ∈ Subgroup.normalizer (C : Set G) := Subgroup.le_normalizer hbC
  have hK' : GLAPComponent p (barX p C C ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩} : Set (↥C ⧸ GLAPPrimeCore p ↥C))) Q := by
    rw [barX_self, top_inf_eq]
    exact hQC
  obtain ⟨P, hP, hPQ⟩ := exists_glaPComponent_lift hp hbC le_rfl hdL hb hK'
  refine ⟨P, hP, hPQ, ?_⟩
  have hPC : P ≤ C := hP.1.trans inf_le_left
  have hPq : CFSG.Open.IsQuasisimple (↥P ⧸ GLAPPrimeCore p ↥P) := l119_isQuasisimple_barOf hp hP
  have hQq : CFSG.Open.IsQuasisimple (↥Q ⧸ GLAPPrimeCore p ↥Q) :=
    l119_isQuasisimple_barOf hp hQC
  have hf : ((QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (Subgroup.inclusion hPC)).range = Q :=
    (l119_range_eq hPC).trans hPQ
  obtain ⟨e⟩ := l119_barOf_centre_iso hp _ hf hPq hQq
  exact ⟨e⟩

end Lift

section Transport

theorem l119_isLThreeFour_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsLThreeFour X) : IsLThreeFour Y := by
  obtain ⟨K, hK, hfin, hcard, ⟨f⟩⟩ := h
  exact ⟨K, hK, hfin, hcard, ⟨e.symm.trans f⟩⟩

theorem l119_isSporType_congr {X Y : Type} [Group X] [Group Y] (name : TauCeti.SporadicName)
    (e : X ≃* Y) (h : IsSporType name X) : IsSporType name Y := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

theorem l119_isAltType_congr {X Y : Type} [Group X] [Group Y] (n : ℕ) (e : X ≃* Y)
    (h : IsAltType n X) : IsAltType n Y := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

noncomputable def l119_centerQuot_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    (X ⧸ Subgroup.center X) ≃* (Y ⧸ Subgroup.center Y) :=
  QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e (Subgroup.map_center_eq e)

theorem l119_cg2_eq {G : Type} [Group G] (a b : G) :
    Subgroup.centralizer ({b, a} : Set G) = Subgroup.centralizer ({a} : Set G) ⊓
      Subgroup.centralizer ({b} : Set G) := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · intro h
    exact ⟨fun x hx => h x (Or.inr hx), fun x hx => h x (Or.inl hx)⟩
  · rintro ⟨h1, h2⟩ x hx
    rcases hx with rfl | rfl
    · exact h2 x rfl
    · exact h1 x rfl

noncomputable def l119_gLBConj_equiv {G : Type} [Group G] (g : G) (H : Subgroup G) :
    ↥H ≃* ↥(GLBConj g H) :=
  ((MulAut.conj g⁻¹).subgroupMap H).trans (MulEquiv.refl _)

end Transport

section Rank

variable {G : Type} [Group G]

theorem l119_eq_one_of_pow_of_mem_core {p : ℕ} (hp : p.Prime) [Finite G] {C : Subgroup G}
    {x : ↥C} (hx : x ^ p = 1) (hN : x ∈ GLAPPrimeCore p ↥C) : x = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx
  have hN' : (⟨x, hN⟩ : ↥(GLAPPrimeCore p ↥C)) ∈ (⊤ : Subgroup ↥(GLAPPrimeCore p ↥C)) :=
    Subgroup.mem_top _
  have h2 : orderOf x ∣ Nat.card ↥(GLAPPrimeCore p ↥C) := by
    have := orderOf_dvd_natCard (⟨x, hN⟩ : ↥(GLAPPrimeCore p ↥C))
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCore p ↥C)) := CFSG.pPrimeCore_coprime_card
  have h3 : orderOf x ∣ Nat.gcd p (Nat.card ↥(GLAPPrimeCore p ↥C)) := Nat.dvd_gcd h1 h2
  rw [hcop.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem l119_pRank_image_ge {p : ℕ} (hp : p.Prime) [Finite G] {C S : Subgroup G} (hSC : S ≤ C)
    (hS : IsElemAbelian p S) :
    CFSG.Open.pRank p S ≤ CFSG.Open.pRank p (((S.subgroupOf C).map (QuotientGroup.mk' (GLAPPrimeCore p ↥C))) :
      Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E', hE'S, hE'el, hE'card⟩ := CFSG.SectionRank.exists_pRank hp.one_lt S
  let f : ↥E' →* (↥C ⧸ GLAPPrimeCore p ↥C) :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (Subgroup.inclusion (hE'S.trans hSC))
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (Subgroup.inclusion (hE'S.trans hSC) x : ↥C) ∈ GLAPPrimeCore p ↥C :=
      (QuotientGroup.eq_one_iff _).1 hx
    have hpow : (Subgroup.inclusion (hE'S.trans hSC) x : ↥C) ^ p = 1 := by
      have := hE'el.2 (x : G) x.2
      ext
      simp [this]
    have h1 := l119_eq_one_of_pow_of_mem_core hp hpow hx'
    ext
    simpa using congrArg Subtype.val h1
  have hcomm : ∀ a b : ↥E', a * b = b * a := fun a b => hE'el.1.is_comm.comm a b
  have hpow_all : ∀ a : ↥E', a ^ p = 1 := fun a => by
    ext
    simpa using hE'el.2 a a.2
  have hrange : f.range ≤ ((S.subgroupOf C).map (QuotientGroup.mk' (GLAPPrimeCore p ↥C))) := by
    rintro _ ⟨x, rfl⟩
    refine Subgroup.mem_map_of_mem _ ?_
    exact (Subgroup.mem_subgroupOf).2 (hE'S x.2)
  exact CFSG.SectionRank.le_pRank_of_injective hp.one_lt hcomm hpow_all hE'card f hf hrange

end Rank

section Conjugates

theorem l119_gLBConj_inj {Q : Type} [Group Q] (g : Q) {X Y : Subgroup Q} :
    GLBConj g X = GLBConj g Y ↔ X = Y := by
  constructor
  · intro h
    have h2 := congrArg (GLBConj g⁻¹) h
    rwa [gLBConj_gLBConj, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one, gLBConj_one] at h2
  · intro h
    rw [h]

theorem l119_normalizer_gLBConj_iff {Q : Type} [Group Q] {b g : Q} (hbg : b * g = g * b)
    (H : Subgroup Q) :
    b ∈ Subgroup.normalizer ((GLBConj g H : Subgroup Q) : Set Q) ↔ b ∈ Subgroup.normalizer (H : Set Q) := by
  rw [mem_normalizer_iff_gLBConj_eq, mem_normalizer_iff_gLBConj_eq]
  have e : GLBConj b (GLBConj g H) = GLBConj g (GLBConj b H) := by
    rw [gLBConj_gLBConj, gLBConj_gLBConj, hbg]
  rw [e, l119_gLBConj_inj]

theorem l119_centralizes_gLBConj {Q : Type} [Group Q] {b g : Q} (hbg : b * g = g * b) {H : Subgroup Q}
    (hH : ∀ q ∈ H, b * q = q * b) : ∀ x ∈ GLBConj g H, b * x = x * b := by
  intro x hx
  rw [mem_gLBConj] at hx
  have hq := hH _ hx
  have hgb : g⁻¹ * b = b * g⁻¹ := by
    calc g⁻¹ * b = g⁻¹ * (b * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * b) * g⁻¹ := by rw [hbg]
      _ = b * g⁻¹ := by group
  calc b * x = b * (g⁻¹ * (g * x * g⁻¹) * g) := by group
    _ = (b * g⁻¹) * (g * x * g⁻¹) * g := by group
    _ = (g⁻¹ * b) * (g * x * g⁻¹) * g := by rw [← hgb]
    _ = g⁻¹ * (b * (g * x * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * x * g⁻¹) * b) * g := by rw [hq]
    _ = g⁻¹ * (g * x * g⁻¹) * (b * g) := by group
    _ = g⁻¹ * (g * x * g⁻¹) * (g * b) := by rw [hbg]
    _ = (g⁻¹ * (g * x * g⁻¹) * g) * b := by group
    _ = x * b := by rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]

end Conjugates

section NormBar

variable {G : Type} [Group G] [Finite G]

theorem l119_mem_normalizer_of_bar {p : ℕ} (hp : p.Prime) {a : G} {K : Subgroup G}
    (hK : GLAPComponent p (Cg a) K) (z : ↥(Cg a))
    (hz : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z ∈
      Subgroup.normalizer ((barX p (Cg a) K : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))) :
        Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) :
    (z : G) ∈ Subgroup.normalizer (K : Set G) := by
  have hzC : (z : G) ∈ Cg a := z.2
  have hnorm : (z : G) ∈ Subgroup.normalizer ((Cg a : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hzC
  have hGC : GLBConj (z : G) (Cg a) = Cg a := gLBConj_eq_of_mem_normalizer hnorm
  have hp1 : GLAPComponent p (Cg a) (GLBConj (z : G) K) := by
    have := glaPComponent_gLBConj hK (z : G)
    rwa [hGC] at this
  have hbar : barX p (Cg a) (GLBConj (z : G) K) = barX p (Cg a) K := by
    rw [l119_barX_gLBConj hzC hK.1]
    exact gLBConj_eq_of_mem_normalizer hz
  have heq : GLBConj (z : G) K = K := glaPComponent_unique hp1 hK hbar
  rw [mem_normalizer_iff_gLBConj_eq]
  exact heq

noncomputable def l119_center_bot_quot {X : Type} [Group X] (h : Subgroup.center X = ⊥) :
    (X ⧸ Subgroup.center X) ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

end NormBar

section Misc

variable {G : Type} [Group G]

theorem l119_isPGroup_zpowers {p : ℕ} {x : G} (hx : x ^ p = 1) : IsPGroup p (Subgroup.zpowers x) := by
  rintro ⟨y, hy⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

end Misc

section JStep

variable {G : Type} [Group G] [Finite G]

theorem l119_isElemAbelian_of_le {p : ℕ} {S T : Subgroup G} (h : S ≤ T) (hT : IsElemAbelian p T) :
    IsElemAbelian p S := by
  have hcomm : ∀ a b : ↥S, a * b = b * a := by
    intro a b
    have h1 := hT.1.is_comm.comm (⟨a.1, h a.2⟩ : ↥T) ⟨b.1, h b.2⟩
    have h2 : a.1 * b.1 = b.1 * a.1 := congrArg Subtype.val h1
    exact Subtype.ext h2
  exact ⟨⟨⟨hcomm⟩⟩, fun x hx => hT.2 x (h hx)⟩

theorem l119_isElemAbelian_subgroupOf {p : ℕ} {S : Subgroup G} (hS : IsElemAbelian p S) (C : Subgroup G) :
    IsElemAbelian p (S.subgroupOf C) := by
  have hcomm : ∀ a b : ↥(S.subgroupOf C), a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    have h1 := hS.1.is_comm.comm (⟨(a : G), (Subgroup.mem_subgroupOf).1 a.2⟩ : ↥S)
      ⟨(b : G), (Subgroup.mem_subgroupOf).1 b.2⟩
    have h2 : (a : G) * (b : G) = (b : G) * (a : G) := congrArg Subtype.val h1
    exact h2
  refine ⟨⟨⟨hcomm⟩⟩, fun x hx => ?_⟩
  apply Subtype.ext
  simpa using hS.2 (x : G) ((Subgroup.mem_subgroupOf).1 hx)

end JStep

section Faithful

variable {G : Type} [Group G] [Finite G]

theorem l119_barAut_eq_conj {p : ℕ} {K : Subgroup G} (k : ↥K) :
    CFSG.HardMathSupport.Solomon.LocalBalance.barAut p K
        ⟨(k : G), Subgroup.le_normalizer k.2⟩ =
      MulAut.conj (QuotientGroup.mk k : ↥K ⧸ GLAPPrimeCore p ↥K) := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.conj_apply,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1

theorem l119_centralizes_of_barAut {p : ℕ} (hp : p.Prime) {a x : G} {K : Subgroup G}
    (hK : GLAPComponent p (Cg a) K) (hx : x ∈ Cg a) (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (hbar : CFSG.HardMathSupport.Solomon.LocalBalance.barAut p K ⟨x, hxN⟩ = 1) :
    ∀ q ∈ barX p (Cg a) K, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨x, hx⟩ * q =
      q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨x, hx⟩ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro q hq
  obtain ⟨c, hc, rfl⟩ := hq
  have hcK : (c : G) ∈ K := Subgroup.mem_subgroupOf.1 hc
  have hKC : K ≤ Cg a := hK.1
  have hsnKC : IsSubnormal K (Cg a) := hK.2.1
  let k : ↥K := ⟨(c : G), hcK⟩
  have h1 : CFSG.HardMathSupport.Solomon.LocalBalance.barAut p K ⟨x, hxN⟩
      (QuotientGroup.mk k) = QuotientGroup.mk k := by
    rw [hbar, MulAut.one_apply]
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk] at h1
  have hn := QuotientGroup.eq.1 h1.symm
  have hsub : ∀ y : ↥K, y ∈ GLAPPrimeCore p ↥K →
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) (⟨(y : G), hKC y.2⟩ : ↥(Cg a)) = 1 := by
    intro y hy
    have hyK : (y : G) ∈ GLAPPrimeCoreOf p K := Subgroup.mem_map.2 ⟨y, hy, rfl⟩
    have hyC : (y : G) ∈ GLAPPrimeCoreOf p (Cg a) :=
      glaPPrimeCoreOf_le_of_isSubnormal hp hsnKC hyK
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hyC
    have hzeq : z = (⟨(y : G), hKC y.2⟩ : ↥(Cg a)) := Subtype.ext hzy
    rw [← hzeq]
    exact (QuotientGroup.eq_one_iff z).2 hz
  set x_C : ↥(Cg a) := ⟨x, hx⟩ with hxC
  set c_C : ↥(Cg a) := ⟨(c : G), hKC hcK⟩ with hcC
  have hnC : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) (c_C⁻¹ * (x_C * c_C * x_C⁻¹)) = 1 := by
    have e : (c_C⁻¹ * (x_C * c_C * x_C⁻¹) : ↥(Cg a)) =
        (⟨((k⁻¹ * (K.normalizerMonoidHom ⟨x, hxN⟩ k) : ↥K) : G), hKC (k⁻¹ * _).2⟩ : ↥(Cg a)) := by
      apply Subtype.ext
      simp [hxC, hcC, k, Subgroup.normalizerMonoidHom, mul_assoc]
      exact (mul_assoc _ _ _).symm
    rw [e]
    exact hsub _ hn
  calc QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) x_C * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) c_C
      = QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) (c_C * (c_C⁻¹ * (x_C * c_C * x_C⁻¹)) * x_C) := by
        rw [← map_mul]
        congr 1
        group
    _ = QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) c_C *
        QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) (c_C⁻¹ * (x_C * c_C * x_C⁻¹)) *
        QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) x_C := by
        rw [map_mul, map_mul]
    _ = QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) c_C * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) x_C := by
        rw [hnC, mul_one]

theorem l119_pRank_le_two_of_inj {p : ℕ} (hp : p.Prime) {T : Type} [Group T] [Finite T] {S : Subgroup G}
    (hS : IsElemAbelian p S) (f : ↥S →* T) (hf : Function.Injective f)
    (hT : ∀ A : Subgroup T, IsElemAbelian p A → CFSG.Open.pRank p A ≤ 2) :
    CFSG.Open.pRank p S ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E', hE'S, hE'el, hE'card⟩ := CFSG.SectionRank.exists_pRank hp.one_lt S
  let g : ↥E' →* T := f.comp (Subgroup.inclusion hE'S)
  have hg : Function.Injective g := hf.comp (Subgroup.inclusion_injective hE'S)
  have hS' : IsElemAbelian p (⊤ : Subgroup ↥S) := by
    have hcomm : ∀ a b : ↥S, a * b = b * a := fun a b => hS.1.is_comm.comm a b
    have hcomm' : ∀ a b : ↥(⊤ : Subgroup ↥S), a * b = b * a := fun a b => Subtype.ext (hcomm a.1 b.1)
    refine ⟨⟨⟨hcomm'⟩⟩, fun x _ => ?_⟩
    apply Subtype.ext
    exact hS.2 x.1 x.2
  have hH : g.range ≤ (⊤ : Subgroup ↥S).map f := by
    rintro _ ⟨y, rfl⟩
    exact Subgroup.mem_map_of_mem f (Subgroup.mem_top _)
  have hcomm' : ∀ a b : ↥E', a * b = b * a := fun a b => hE'el.1.is_comm.comm a b
  have hpow' : ∀ a : ↥E', a ^ p = 1 := fun a => by
    apply Subtype.ext
    simpa using hE'el.2 a.1 a.2
  have h1 := CFSG.SectionRank.le_pRank_of_injective hp.one_lt hcomm' hpow' hE'card g hg hH
  exact le_trans h1 (hT _ (CFSG.SectionRank.isElemAbelian_map hS' f))

theorem l119_inducesInner_of_inner {p : ℕ} {x : G} {K : Subgroup G}
    (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (hin : CFSG.HardMathSupport.Solomon.LocalBalance.barAut p K ⟨x, hxN⟩ ∈
      innerAut (barOf p K)) :
    InducesInner p K x := by
  have hin' := hin
  unfold innerAut at hin'
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hin'
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
  have hk := l119_barAut_eq_conj (p := p) k
  refine ⟨(k : G), k.2, ?_⟩
  unfold centBar
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨(⟨(k : G), hkN⟩⁻¹ * ⟨x, hxN⟩), ?_, ?_⟩, trivial⟩
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hk, hy, inv_mul_cancel]
  · rfl

end Faithful

section Final

variable {G : Type} [Group G] [Finite G]

theorem l119_sec11_facts {m p : ℕ} {B M E A : Subgroup G} (hSec : Sec11 G m p B M E A) :
    IsElemAbelian p A ∧ 2 ≤ CFSG.Open.pRank p (E ⊓ A) := by
  obtain ⟨hDDp, -⟩ := hSec.pair
  obtain ⟨-, hDp, hrA0⟩ := hDDp
  obtain ⟨hSCs, -⟩ := hDp
  obtain ⟨hSCp, -⟩ := hSCs
  obtain ⟨-, hAel, -⟩ := hSCp
  exact ⟨hAel, hrA0⟩

end Final

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
