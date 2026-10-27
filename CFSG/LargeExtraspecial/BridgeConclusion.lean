module

public import CFSG.LargeExtraspecial.BridgeNat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

universe u v

namespace CFSG.Open

open CFSG.Open Matrix in
open scoped MatrixGroups in
@[expose] def _root_.CFSG.LargeExtraspecial.Bridge.TimmesfeldConclusion (G : Type u) [Group G]
    (w : ℕ) (Mbar : Type v) [Group Mbar] : Prop :=
    w ≤ 4 ∨
    (Nonempty (G ≃* PSL(w + 2, ZMod 2)) ∨ Nonempty (G ≃* timmesfeldPSU (w + 2))) ∨
    (6 ≤ w ∧ Even w ∧
      ∃ q : QuadraticForm (ZMod 2) (Fin w → ZMod 2), timmesfeldNondegenerate q ∧
        (Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
          Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q))) ∨
    (w = 6 ∧ IsQuasisimple (timmesfeldLayer Mbar) ∧ Nat.card (timmesfeldOddCore Mbar) ≤ 3 ∧
      ∃ t : Mbar, orderOf t = 2 ∧
        ∃ R : Subgroup Mbar, R ≤ Subgroup.centralizer ({t} : Set Mbar) ∧
          (R.subgroupOf (Subgroup.centralizer ({t} : Set Mbar))).Normal ∧
          (frattini (pCoreOf 2 R)).map (pCoreOf 2 R).subtype ≤ Subgroup.zpowers t ∧
          (timmesfeldQuotientIso (pCore 2 R) PSL(3, ZMod 2) ∨
            (∃ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q ∧
              timmesfeldPlusType q ∧ timmesfeldQuotientIso (pCore 2 R) (timmesfeldOmega q)) ∨
            (pCoreOf 2 R = Subgroup.zpowers t ∧
              ∃ q : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2), timmesfeldNondegenerate q ∧
                timmesfeldQuotientIso (pCore 2 R) (timmesfeldOmega q)))) ∨
    (w = 10 ∧ (timmesfeldFStar Mbar).index ≤ 2 ∧
      (Nonempty (timmesfeldFStar Mbar ≃* PSL(6, ZMod 2)) ∨
        Nonempty (timmesfeldFStar Mbar ≃* timmesfeldPSU 6))) ∨
    (w = 11 ∧ Nonempty (Mbar ≃* Blueprint.NativeSporadic.Co2)) ∨
    (w = 12 ∧ Nonempty (Mbar ≃* Blueprint.NativeSporadic.Co1)) ∨
    (IsSimpleGroup Mbar ∧ ∃ t : Mbar, orderOf t = 2 ∧
      timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) ∧
      ((w = 16 ∧ Nat.card (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 17 ∧
          timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar)))
            (Equiv.Perm (Fin 3) × timmesfeldOmegaPlus 4)) ∨
        (w = 28 ∧ Nat.card (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 33 ∧
          timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar)))
            (timmesfeldOmegaPlus 6))))

open CFSG.Open Matrix in
open scoped MatrixGroups in
@[expose] def _root_.CFSG.LargeExtraspecial.Bridge.TimmesfeldOrderConclusion (G : Type u)
    [Group G] (w : ℕ) (Mbar : Type v) [Group Mbar] : Prop :=
    w ≤ 4 ∨
    (Nonempty (G ≃* PSL(w + 2, ZMod 2)) ∨ Nonempty (G ≃* timmesfeldPSU (w + 2))) ∨
    (6 ≤ w ∧ Even w ∧
      ∃ q : QuadraticForm (ZMod 2) (Fin w → ZMod 2), timmesfeldNondegenerate q ∧
        (Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
          Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q))) ∨
    (w = 6 ∧ IsQuasisimple (timmesfeldLayer Mbar) ∧ Nat.card (timmesfeldOddCore Mbar) ≤ 3 ∧
      ∃ t : Mbar, orderOf t = 2 ∧
        ∃ R : Subgroup Mbar, R ≤ Subgroup.centralizer ({t} : Set Mbar) ∧
          (R.subgroupOf (Subgroup.centralizer ({t} : Set Mbar))).Normal ∧
          (frattini (pCoreOf 2 R)).map (pCoreOf 2 R).subtype ≤ Subgroup.zpowers t ∧
          (timmesfeldQuotientIso (pCore 2 R) PSL(3, ZMod 2) ∨
            (∃ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q ∧
              timmesfeldPlusType q ∧ timmesfeldQuotientIso (pCore 2 R) (timmesfeldOmega q)) ∨
            (pCoreOf 2 R = Subgroup.zpowers t ∧
              ∃ q : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2), timmesfeldNondegenerate q ∧
                timmesfeldQuotientIso (pCore 2 R) (timmesfeldOmega q)))) ∨
    (w = 10 ∧ (timmesfeldFStar Mbar).index ≤ 2 ∧
      (Nonempty (timmesfeldFStar Mbar ≃* PSL(6, ZMod 2)) ∨
        Nonempty (timmesfeldFStar Mbar ≃* timmesfeldPSU 6))) ∨
    (w = 11 ∧ IsSimpleGroup Mbar ∧ Nat.card Mbar = timmesfeldOrderCo2) ∨
    (w = 12 ∧ IsSimpleGroup Mbar ∧ Nat.card Mbar = timmesfeldOrderCo1) ∨
    (IsSimpleGroup Mbar ∧ ∃ t : Mbar, orderOf t = 2 ∧
      timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) ∧
      ((w = 16 ∧ Nat.card (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 17 ∧
          timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar)))
            (Equiv.Perm (Fin 3) × timmesfeldOmegaPlus 4)) ∨
        (w = 28 ∧ Nat.card (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 33 ∧
          timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar)))
            (timmesfeldOmegaPlus 6))))

open CFSG.Open Matrix in
@[expose] def _root_.CFSG.LargeExtraspecial.Bridge.TimmesfeldAlt3 (w : ℕ) (Mbar : Type v)
    [Group Mbar] : Prop :=
    (6 ≤ w ∧ Even w ∧
      ∃ q : QuadraticForm (ZMod 2) (Fin w → ZMod 2), timmesfeldNondegenerate q ∧
        (Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
          Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q)))

open CFSG.Open Matrix in
open scoped MatrixGroups in
@[expose] def _root_.CFSG.LargeExtraspecial.Bridge.TimmesfeldAlt4 (w : ℕ) (Mbar : Type v)
    [Group Mbar] : Prop :=
    (w = 6 ∧ IsQuasisimple (timmesfeldLayer Mbar) ∧ Nat.card (timmesfeldOddCore Mbar) ≤ 3 ∧
      ∃ t : Mbar, orderOf t = 2 ∧
        ∃ R : Subgroup Mbar, R ≤ Subgroup.centralizer ({t} : Set Mbar) ∧
          (R.subgroupOf (Subgroup.centralizer ({t} : Set Mbar))).Normal ∧
          (frattini (pCoreOf 2 R)).map (pCoreOf 2 R).subtype ≤ Subgroup.zpowers t ∧
          (timmesfeldQuotientIso (pCore 2 R) PSL(3, ZMod 2) ∨
            (∃ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q ∧
              timmesfeldPlusType q ∧ timmesfeldQuotientIso (pCore 2 R) (timmesfeldOmega q)) ∨
            (pCoreOf 2 R = Subgroup.zpowers t ∧
              ∃ q : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2), timmesfeldNondegenerate q ∧
                timmesfeldQuotientIso (pCore 2 R) (timmesfeldOmega q))))

open CFSG.Open Matrix in
open scoped MatrixGroups in
@[expose] def _root_.CFSG.LargeExtraspecial.Bridge.TimmesfeldAlt5 (w : ℕ) (Mbar : Type v)
    [Group Mbar] : Prop :=
    (w = 10 ∧ (timmesfeldFStar Mbar).index ≤ 2 ∧
      (Nonempty (timmesfeldFStar Mbar ≃* PSL(6, ZMod 2)) ∨
        Nonempty (timmesfeldFStar Mbar ≃* timmesfeldPSU 6)))

open CFSG.Open in
@[expose] def _root_.CFSG.LargeExtraspecial.Bridge.TimmesfeldAlt8 (w : ℕ) (Mbar : Type v)
    [Group Mbar] : Prop :=
    (IsSimpleGroup Mbar ∧ ∃ t : Mbar, orderOf t = 2 ∧
      timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) ∧
      ((w = 16 ∧ Nat.card (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 17 ∧
          timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar)))
            (Equiv.Perm (Fin 3) × timmesfeldOmegaPlus 4)) ∨
        (w = 28 ∧ Nat.card (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 33 ∧
          timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar)))
            (timmesfeldOmegaPlus 6))))

@[expose] def _root_.CFSG.LargeExtraspecial.Bridge.MainFor (G : Type) [Group G] : Prop :=
  ∀ (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (z : G) (_hz : orderOf z = 2)
    (_hext : timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))))
    (w : ℕ)
    (_hw : Nat.card (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) = 2 ^ (1 + 2 * w))
    (Mbar : Type) [Group Mbar]
    (_hMbar : timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) Mbar),
    CFSG.LargeExtraspecial.Bridge.TimmesfeldConclusion G w Mbar

@[expose] def _root_.CFSG.LargeExtraspecial.Bridge.OrderMainFor (G : Type) [Group G] : Prop :=
  ∀ (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (z : G) (_hz : orderOf z = 2)
    (_hext : timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))))
    (w : ℕ)
    (_hw : Nat.card (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) = 2 ^ (1 + 2 * w))
    (Mbar : Type) [Group Mbar]
    (_hMbar : timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) Mbar),
    CFSG.LargeExtraspecial.Bridge.TimmesfeldOrderConclusion G w Mbar

end CFSG.Open

namespace CFSG.LargeExtraspecial.Bridge

open Subgroup CFSG.Open Matrix
open scoped MatrixGroups

@[expose] def MainStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], MainFor G

@[expose] def OrderMainStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], OrderMainFor G

theorem models_of_mainStatement (h : MainStatement) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (z : G) (hz : orderOf z = 2)
    (hext : timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))))
    (w : ℕ)
    (hw : Nat.card (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) = 2 ^ (1 + 2 * w))
    (Mbar : Type) [Group Mbar]
    (hMbar : timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) Mbar) :
    TimmesfeldConclusion G w Mbar :=
  h G hnonab z hz hext w hw Mbar hMbar

theorem order_of_orderMainStatement (h : OrderMainStatement) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (z : G) (hz : orderOf z = 2)
    (hext : timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))))
    (w : ℕ)
    (hw : Nat.card (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) = 2 ^ (1 + 2 * w))
    (Mbar : Type) [Group Mbar]
    (hMbar : timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) Mbar) :
    TimmesfeldOrderConclusion G w Mbar :=
  h G hnonab z hz hext w hw Mbar hMbar

variable {G : Type u} {G' : Type*} [Group G] [Group G'] {Mbar : Type v} {Mbar' : Type*}
  [Group Mbar] [Group Mbar'] {w : ℕ}

theorem timmesfeldConclusion_iff : TimmesfeldConclusion G w Mbar ↔
    w ≤ 4 ∨ (Nonempty (G ≃* PSL(w + 2, ZMod 2)) ∨ Nonempty (G ≃* timmesfeldPSU (w + 2))) ∨
      TimmesfeldAlt3 w Mbar ∨ TimmesfeldAlt4 w Mbar ∨ TimmesfeldAlt5 w Mbar ∨
      (w = 11 ∧ Nonempty (Mbar ≃* CFSG.Blueprint.NativeSporadic.Co2)) ∨
      (w = 12 ∧ Nonempty (Mbar ≃* CFSG.Blueprint.NativeSporadic.Co1)) ∨
      TimmesfeldAlt8 w Mbar :=
  Iff.rfl

theorem timmesfeldOrderConclusion_iff : TimmesfeldOrderConclusion G w Mbar ↔
    w ≤ 4 ∨ (Nonempty (G ≃* PSL(w + 2, ZMod 2)) ∨ Nonempty (G ≃* timmesfeldPSU (w + 2))) ∨
      TimmesfeldAlt3 w Mbar ∨ TimmesfeldAlt4 w Mbar ∨ TimmesfeldAlt5 w Mbar ∨
      (w = 11 ∧ IsSimpleGroup Mbar ∧ Nat.card Mbar = timmesfeldOrderCo2) ∨
      (w = 12 ∧ IsSimpleGroup Mbar ∧ Nat.card Mbar = timmesfeldOrderCo1) ∨
      TimmesfeldAlt8 w Mbar :=
  Iff.rfl

theorem TimmesfeldAlt3.of_mulEquiv (e : Mbar ≃* Mbar') (h : TimmesfeldAlt3 w Mbar) :
    TimmesfeldAlt3 w Mbar' := by
  obtain ⟨h6, he, q, hq, h3⟩ := h
  exact ⟨h6, he, q, hq, h3.imp (fun ⟨f⟩ => ⟨e.symm.trans f⟩) (fun ⟨f⟩ => ⟨e.symm.trans f⟩)⟩

theorem TimmesfeldAlt4.of_mulEquiv (e : Mbar ≃* Mbar') (h : TimmesfeldAlt4 w Mbar) :
    TimmesfeldAlt4 w Mbar' := by
  obtain ⟨h6, hE, hO, t, ht, R, hR, hRn, hΦ, hR'⟩ := h
  have hC := CFSG.Monster.GMS.map_centralizer_singleton e t
  have hz : (zpowers t).map e.toMonoidHom = zpowers (e t) := MonoidHom.map_zpowers _ _
  have hP : (CFSG.Open.pCore 2 R).map (mapEquiv e R).toMonoidHom =
      CFSG.Open.pCore 2 (R.map e.toMonoidHom) := pCore_map_mulEquiv 2 _
  refine ⟨h6, isQuasisimple_of_mulEquiv (equivOfMapEq e (timmesfeldLayer_map e)) hE, ?_,
    e t, by rwa [MulEquiv.orderOf_eq], R.map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rwa [← timmesfeldOddCore_map e, card_map_of_injective e.injective]
  · rw [← hC]
    exact map_mono hR
  · rw [← hC]
    exact normal_subgroupOf_map e hR hRn
  · rw [pCoreOf_map, map_subtype_frattini_map, ← hz]
    exact map_mono hΦ
  · rcases hR' with h | ⟨q, hq, hp, h⟩ | ⟨hR2, q, hq, h⟩
    · left
      rw [← hP]
      exact quotientIso_map h _
    · right; left
      exact ⟨q, hq, hp, by rw [← hP]; exact quotientIso_map h _⟩
    · right; right
      refine ⟨?_, q, hq, by rw [← hP]; exact quotientIso_map h _⟩
      rw [pCoreOf_map, hR2, hz]

theorem TimmesfeldAlt5.of_mulEquiv (e : Mbar ≃* Mbar') (h : TimmesfeldAlt5 w Mbar) :
    TimmesfeldAlt5 w Mbar' := by
  obtain ⟨h10, hidx, h5⟩ := h
  have hF := timmesfeldFStar_map e
  refine ⟨h10, ?_, ?_⟩
  · rwa [← hF, index_map_of_bijective (f := e.toMonoidHom) e.bijective]
  · have f := equivOfMapEq e hF
    exact h5.imp (fun ⟨g⟩ => ⟨f.symm.trans g⟩) (fun ⟨g⟩ => ⟨f.symm.trans g⟩)

theorem TimmesfeldAlt8.of_mulEquiv (e : Mbar ≃* Mbar') (h : TimmesfeldAlt8 w Mbar) :
    TimmesfeldAlt8 w Mbar' := by
  obtain ⟨hs, t, ht, hext, h8⟩ := h
  have c := CFSG.Monster.GMS.centralizerMulEquiv e t
  have hF := timmesfeldFStar_map c
  have f := equivOfMapEq c hF
  refine ⟨(MulEquiv.isSimpleGroup_congr e).mp hs, e t, by rwa [MulEquiv.orderOf_eq],
    timmesfeldIsExtraspecial_of_mulEquiv f hext, ?_⟩
  rcases h8 with ⟨h16, hc, hq⟩ | ⟨h28, hc, hq⟩
  · refine Or.inl ⟨h16, ?_, ?_⟩
    · rw [← hc]
      exact Nat.card_congr f.toEquiv.symm
    · rw [← hF]
      exact quotientIso_map hq c
  · refine Or.inr ⟨h28, ?_, ?_⟩
    · rw [← hc]
      exact Nat.card_congr f.toEquiv.symm
    · rw [← hF]
      exact quotientIso_map hq c

theorem TimmesfeldConclusion.of_mulEquiv_quotient (e : Mbar ≃* Mbar')
    (h : TimmesfeldConclusion G w Mbar) : TimmesfeldConclusion G w Mbar' := by
  rw [timmesfeldConclusion_iff] at h
  rw [timmesfeldConclusion_iff]
  rcases h with h | h | h | h | h | ⟨h11, ⟨f⟩⟩ | ⟨h12, ⟨f⟩⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (h.of_mulEquiv e)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h.of_mulEquiv e))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h.of_mulEquiv e)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h11, ⟨e.symm.trans f⟩⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h12, ⟨e.symm.trans f⟩⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h.of_mulEquiv e)))))))

theorem TimmesfeldConclusion.of_mulEquiv_group (e : G ≃* G')
    (h : TimmesfeldConclusion G w Mbar) : TimmesfeldConclusion G' w Mbar := by
  rw [timmesfeldConclusion_iff] at h
  rw [timmesfeldConclusion_iff]
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (h.imp (fun ⟨f⟩ => ⟨e.symm.trans f⟩) (fun ⟨f⟩ => ⟨e.symm.trans f⟩)))
  · exact Or.inr (Or.inr h)

theorem timmesfeldConclusion_congr (eG : G ≃* G') (eM : Mbar ≃* Mbar') :
    TimmesfeldConclusion G w Mbar ↔ TimmesfeldConclusion G' w Mbar' :=
  ⟨fun h => (h.of_mulEquiv_group eG).of_mulEquiv_quotient eM,
    fun h => (h.of_mulEquiv_group eG.symm).of_mulEquiv_quotient eM.symm⟩

theorem TimmesfeldOrderConclusion.of_mulEquiv_quotient (e : Mbar ≃* Mbar')
    (h : TimmesfeldOrderConclusion G w Mbar) : TimmesfeldOrderConclusion G w Mbar' := by
  rw [timmesfeldOrderConclusion_iff] at h
  rw [timmesfeldOrderConclusion_iff]
  rcases h with h | h | h | h | h | ⟨h11, hs, hc⟩ | ⟨h12, hs, hc⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (h.of_mulEquiv e)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h.of_mulEquiv e))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h.of_mulEquiv e)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h11, ?_, ?_⟩)))))
    · exact (MulEquiv.isSimpleGroup_congr e).mp hs
    · rw [← hc]
      exact Nat.card_congr e.toEquiv.symm
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h12, ?_, ?_⟩))))))
    · exact (MulEquiv.isSimpleGroup_congr e).mp hs
    · rw [← hc]
      exact Nat.card_congr e.toEquiv.symm
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h.of_mulEquiv e)))))))

theorem TimmesfeldOrderConclusion.of_mulEquiv_group (e : G ≃* G')
    (h : TimmesfeldOrderConclusion G w Mbar) : TimmesfeldOrderConclusion G' w Mbar := by
  rw [timmesfeldOrderConclusion_iff] at h
  rw [timmesfeldOrderConclusion_iff]
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (h.imp (fun ⟨f⟩ => ⟨e.symm.trans f⟩) (fun ⟨f⟩ => ⟨e.symm.trans f⟩)))
  · exact Or.inr (Or.inr h)

theorem timmesfeldOrderConclusion_congr (eG : G ≃* G') (eM : Mbar ≃* Mbar') :
    TimmesfeldOrderConclusion G w Mbar ↔ TimmesfeldOrderConclusion G' w Mbar' :=
  ⟨fun h => (h.of_mulEquiv_group eG).of_mulEquiv_quotient eM,
    fun h => (h.of_mulEquiv_group eG.symm).of_mulEquiv_quotient eM.symm⟩

theorem TimmesfeldConclusion.of_width_le_four (h : w ≤ 4) : TimmesfeldConclusion G w Mbar :=
  Or.inl h

theorem TimmesfeldConclusion.of_psl (h : Nonempty (G ≃* PSL(w + 2, ZMod 2))) :
    TimmesfeldConclusion G w Mbar :=
  Or.inr (Or.inl (Or.inl h))

theorem TimmesfeldConclusion.of_psu (h : Nonempty (G ≃* timmesfeldPSU (w + 2))) :
    TimmesfeldConclusion G w Mbar :=
  Or.inr (Or.inl (Or.inr h))

theorem TimmesfeldConclusion.of_alt3 (h : TimmesfeldAlt3 w Mbar) :
    TimmesfeldConclusion G w Mbar :=
  Or.inr (Or.inr (Or.inl h))

theorem TimmesfeldConclusion.of_alt4 (h : TimmesfeldAlt4 w Mbar) :
    TimmesfeldConclusion G w Mbar :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem TimmesfeldConclusion.of_alt5 (h : TimmesfeldAlt5 w Mbar) :
    TimmesfeldConclusion G w Mbar :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem TimmesfeldConclusion.of_fstar_psl (hw : w = 10)
    (hidx : (timmesfeldFStar Mbar).index ≤ 2)
    (h : Nonempty (timmesfeldFStar Mbar ≃* PSL(6, ZMod 2))) : TimmesfeldConclusion G w Mbar :=
  TimmesfeldConclusion.of_alt5 ⟨hw, hidx, Or.inl h⟩

theorem TimmesfeldConclusion.of_fstar_psu (hw : w = 10)
    (hidx : (timmesfeldFStar Mbar).index ≤ 2)
    (h : Nonempty (timmesfeldFStar Mbar ≃* timmesfeldPSU 6)) : TimmesfeldConclusion G w Mbar :=
  TimmesfeldConclusion.of_alt5 ⟨hw, hidx, Or.inr h⟩

theorem TimmesfeldConclusion.of_co2 (hw : w = 11)
    (h : Nonempty (Mbar ≃* CFSG.Blueprint.NativeSporadic.Co2)) : TimmesfeldConclusion G w Mbar :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hw, h⟩)))))

theorem TimmesfeldConclusion.of_co1 (hw : w = 12)
    (h : Nonempty (Mbar ≃* CFSG.Blueprint.NativeSporadic.Co1)) : TimmesfeldConclusion G w Mbar :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hw, h⟩))))))

theorem TimmesfeldConclusion.of_alt8 (h : TimmesfeldAlt8 w Mbar) :
    TimmesfeldConclusion G w Mbar :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

theorem TimmesfeldAlt8.width_eq (h : TimmesfeldAlt8 w Mbar) : w = 16 ∨ w = 28 := by
  obtain ⟨-, -, -, -, ⟨h16, -⟩ | ⟨h28, -⟩⟩ := h
  · exact Or.inl h16
  · exact Or.inr h28

theorem TimmesfeldConclusion.width_eight (h : TimmesfeldConclusion G 8 Mbar) :
    (Nonempty (G ≃* PSL(10, ZMod 2)) ∨ Nonempty (G ≃* timmesfeldPSU 10)) ∨
      TimmesfeldAlt3 8 Mbar := by
  rw [timmesfeldConclusion_iff] at h
  rcases h with h | h | h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
  · omega
  · exact Or.inl h
  · exact Or.inr h
  · omega
  · omega
  · omega
  · omega
  · rcases h.width_eq with h | h <;> omega

end CFSG.LargeExtraspecial.Bridge

namespace CFSG.Open

open CFSG.Open Matrix in
open scoped MatrixGroups in
@[expose] def _root_.CFSG.LargeExtraspecial.Bridge.TimmesfeldPrintedConclusion (G : Type u) [Group G]
    (w : ℕ) (Mbar : Type v) [Group Mbar] : Prop :=
    w ≤ 4 ∨
    (Nonempty (G ≃* PSL(w + 2, ZMod 2)) ∨ Nonempty (G ≃* timmesfeldPSU (w + 2))) ∨
    (6 ≤ w ∧ Even w ∧
      ∃ q : QuadraticForm (ZMod 2) (Fin w → ZMod 2), timmesfeldNondegenerate q ∧
        (Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
          Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q))) ∨
    (w = 6 ∧ IsQuasisimple (timmesfeldLayer Mbar) ∧ Nat.card (timmesfeldOddCore Mbar) ≤ 3 ∧
      ∃ t : Mbar, orderOf t = 2 ∧
        ∃ R : Subgroup Mbar, R ≤ Subgroup.centralizer ({t} : Set Mbar) ∧
          (R.subgroupOf (Subgroup.centralizer ({t} : Set Mbar))).Normal ∧
          (frattini (pCoreOf 2 R)).map (pCoreOf 2 R).subtype ≤ Subgroup.zpowers t ∧
          (timmesfeldQuotientIso (pCore 2 R) PSL(3, ZMod 2) ∨
            (∃ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q ∧
              timmesfeldPlusType q ∧ timmesfeldQuotientIso (pCore 2 R) (timmesfeldOmega q)) ∨
            (pCoreOf 2 R = Subgroup.zpowers t ∧
              ∃ q : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2), timmesfeldNondegenerate q ∧
                timmesfeldQuotientIso (pCore 2 R) (timmesfeldOmega q)))) ∨
    (w = 10 ∧ (timmesfeldFStar Mbar).index ≤ 2 ∧
      (Nonempty (timmesfeldFStar Mbar ≃* PSL(6, ZMod 2)) ∨
        Nonempty (timmesfeldFStar Mbar ≃* timmesfeldPSU 6)) ∧
      ∃ σ : Mbar, σ * σ = 1 ∧
        timmesfeldFStar Mbar ⊔ Subgroup.zpowers σ = ⊤) ∨
    (w = 11 ∧ Nonempty (Mbar ≃* Blueprint.NativeSporadic.Co2)) ∨
    (w = 12 ∧ Nonempty (Mbar ≃* Blueprint.NativeSporadic.Co1)) ∨
    (IsSimpleGroup Mbar ∧ ∃ t : Mbar, orderOf t = 2 ∧
      timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) ∧
      ((w = 16 ∧ Nat.card (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 17 ∧
          timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar)))
            (Equiv.Perm (Fin 3) × timmesfeldOmegaPlus 4)) ∨
        (w = 28 ∧ Nat.card (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 33 ∧
          timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar)))
            (timmesfeldOmegaPlus 6))))

end CFSG.Open

namespace CFSG.LargeExtraspecial.Bridge

open CFSG.Open

theorem TimmesfeldPrintedConclusion.to_legacy {G : Type u} [Group G]
    {w : ℕ} {Mbar : Type v} [Group Mbar]
    (hypothesis : TimmesfeldPrintedConclusion G w Mbar) :
    TimmesfeldConclusion G w Mbar := by
  unfold TimmesfeldPrintedConclusion TimmesfeldConclusion at *
  rcases hypothesis with first | second | third | fourth | fifth | sixth | seventh | eighth
  · exact Or.inl first
  · exact Or.inr (Or.inl second)
  · exact Or.inr (Or.inr (Or.inl third))
  · exact Or.inr (Or.inr (Or.inr (Or.inl fourth)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨fifth.1, fifth.2.1, fifth.2.2.1⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sixth)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl seventh))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr eighth))))))

theorem TimmesfeldConclusion.to_printed_of_alt5_split {G : Type u} [Group G]
    {w : ℕ} {Mbar : Type v} [Group Mbar]
    (hypothesis : TimmesfeldConclusion G w Mbar)
    (split : TimmesfeldAlt5 w Mbar →
      ∃ σ : Mbar, σ * σ = 1 ∧ timmesfeldFStar Mbar ⊔ Subgroup.zpowers σ = ⊤) :
    TimmesfeldPrintedConclusion G w Mbar := by
  unfold TimmesfeldConclusion TimmesfeldPrintedConclusion at *
  rcases hypothesis with first | second | third | fourth | fifth | sixth | seventh | eighth
  · exact Or.inl first
  · exact Or.inr (Or.inl second)
  · exact Or.inr (Or.inr (Or.inl third))
  · exact Or.inr (Or.inr (Or.inr (Or.inl fourth)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨fifth.1, fifth.2.1, fifth.2.2, split fifth⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sixth)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl seventh))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr eighth))))))

@[expose] def PrintedMainFor (G : Type) [Group G] : Prop :=
  ∀ (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (z : G) (_hz : orderOf z = 2)
    (_hext : timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))))
    (w : ℕ)
    (_hw : Nat.card (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) = 2 ^ (1 + 2 * w))
    (Mbar : Type) [Group Mbar]
    (_hMbar : timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) Mbar),
    TimmesfeldPrintedConclusion G w Mbar

@[expose] def Alt5SplitFor (G : Type) [Group G] : Prop :=
  ∀ (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (z : G) (_hz : orderOf z = 2)
    (_hext : timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))))
    (w : ℕ)
    (_hw : Nat.card (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) = 2 ^ (1 + 2 * w))
    (Mbar : Type) [Group Mbar]
    (_hMbar : timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) Mbar),
    TimmesfeldAlt5 w Mbar →
      ∃ σ : Mbar, σ * σ = 1 ∧ timmesfeldFStar Mbar ⊔ Subgroup.zpowers σ = ⊤

@[expose] def PrintedMainStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], PrintedMainFor G

theorem printedMainStatement_of_mainStatement_and_alt5_split
    (legacy : MainStatement)
    (split : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], Alt5SplitFor G) :
    PrintedMainStatement := by
  intro G group finite simple hnonab z hz hext w hw Mbar quotientGroup hMbar
  exact (legacy G hnonab z hz hext w hw Mbar hMbar).to_printed_of_alt5_split
    (split G hnonab z hz hext w hw Mbar hMbar)

end CFSG.LargeExtraspecial.Bridge
