module

import CFSG.Adapters.LieModelSmallOrders
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSL
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWZero
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.M12Cover.CyclicKernel (exists_mul_of_mem_sup_of_commute)

section Swap

variable {Y : Type} [Group Y]

theorem map_conj_mul_eq (H : Subgroup Y) (g h : Y) :
    H.map (MulAut.conj (g * h)).toMonoidHom =
      (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp, Function.comp_apply]
  group

theorem mem_normalizer_iff_map_conj {H : Subgroup Y} {g : Y} :
    g ∈ normalizer (H : Set Y) ↔ H.map (MulAut.conj g).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq

variable [Finite Y]

theorem map_conj_eq_or_eq_of_swap {Kc D : Subgroup Y} (hKc : IsComponent Kc) {s : Y}
    (hDKK : D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom)
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    {P : Subgroup Y} (hP : IsPGroup 2 P) (hPK : P ≤ Kc) (hP2 : 2 < Nat.card P) (y : Y) :
    Kc.map (MulAut.conj y).toMonoidHom = Kc ∨
      Kc.map (MulAut.conj y).toMonoidHom = Kc.map (MulAut.conj s).toMonoidHom := by
  have hK' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj y) hKc
  have hKs := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hKc
  rcases CFSG.LocalCores.distinct_components_commute hK' hKc with h1 | h1
  · exact .inl h1
  rcases CFSG.LocalCores.distinct_components_commute hK' hKs with h2 | h2
  · exact .inr h2
  exfalso
  have hle : Kc.map (MulAut.conj y).toMonoidHom ≤ centralizer (D : Set Y) := by
    have h1' := commutator_eq_bot_iff_le_centralizer.1 h1
    have h2' := commutator_eq_bot_iff_le_centralizer.1 h2
    have hsup : Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ≤
        centralizer (Kc.map (MulAut.conj y).toMonoidHom : Set Y) :=
      sup_le (le_centralizer_iff.1 h1') (le_centralizer_iff.1 h2')
    exact (le_centralizer_iff.2 hsup).trans (centralizer_le hDKK)
  have hcard : Nat.card (P.map (MulAut.conj y).toMonoidHom) = Nat.card P :=
    card_map_of_injective (MulAut.conj y).injective
  have h2 := hsyl _ (hP.map _) ((map_mono hPK).trans hle)
  omega

omit [Finite Y] in
theorem map_conj_swap_of_mem_normalizer {Kc : Subgroup Y} {s : Y}
    (hKt : Kc.map (MulAut.conj s).toMonoidHom ≠ Kc)
    (hor : ∀ y : Y, Kc.map (MulAut.conj y).toMonoidHom = Kc ∨
      Kc.map (MulAut.conj y).toMonoidHom = Kc.map (MulAut.conj s).toMonoidHom)
    {g : Y} (hg : g ∈ normalizer (Kc : Set Y)) :
    (Kc.map (MulAut.conj s).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      Kc.map (MulAut.conj s).toMonoidHom := by
  rw [← map_conj_mul_eq]
  rcases hor (g * s) with h | h
  · exfalso
    apply hKt
    have hg' : Kc.map (MulAut.conj g⁻¹).toMonoidHom = Kc :=
      mem_normalizer_iff_map_conj.1 (inv_mem hg)
    calc Kc.map (MulAut.conj s).toMonoidHom = Kc.map (MulAut.conj (g⁻¹ * (g * s))).toMonoidHom := by
          rw [inv_mul_cancel_left]
      _ = (Kc.map (MulAut.conj (g * s)).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom :=
          map_conj_mul_eq _ _ _
      _ = Kc := by rw [h, hg']
  · exact h

omit [Finite Y] in
theorem map_conj_swap_of_not_mem_normalizer {Kc : Subgroup Y} {s : Y}
    (hKt : Kc.map (MulAut.conj s).toMonoidHom ≠ Kc)
    (hor : ∀ y : Y, Kc.map (MulAut.conj y).toMonoidHom = Kc ∨
      Kc.map (MulAut.conj y).toMonoidHom = Kc.map (MulAut.conj s).toMonoidHom)
    {g : Y} (hg : g ∉ normalizer (Kc : Set Y)) :
    (Kc.map (MulAut.conj s).toMonoidHom).map (MulAut.conj g).toMonoidHom = Kc := by
  have hKg : Kc.map (MulAut.conj g).toMonoidHom = Kc.map (MulAut.conj s).toMonoidHom :=
    (hor g).resolve_left fun h => hg (mem_normalizer_iff_map_conj.2 h)
  rw [← map_conj_mul_eq]
  rcases hor (g * s) with h | h
  · exact h
  · exfalso
    apply hKt
    calc Kc.map (MulAut.conj s).toMonoidHom = Kc.map (MulAut.conj (g⁻¹ * (g * s))).toMonoidHom := by
          rw [inv_mul_cancel_left]
      _ = (Kc.map (MulAut.conj (g * s)).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom :=
          map_conj_mul_eq _ _ _
      _ = (Kc.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by rw [h, hKg]
      _ = Kc.map (MulAut.conj (g⁻¹ * g)).toMonoidHom := (map_conj_mul_eq _ _ _).symm
      _ = Kc := by rw [inv_mul_cancel, map_one]; exact Subgroup.map_id Kc

omit [Finite Y] in
theorem mul_mem_normalizer_iff_of_swap {Kc : Subgroup Y} {s : Y}
    (hKt : Kc.map (MulAut.conj s).toMonoidHom ≠ Kc)
    (hor : ∀ y : Y, Kc.map (MulAut.conj y).toMonoidHom = Kc ∨
      Kc.map (MulAut.conj y).toMonoidHom = Kc.map (MulAut.conj s).toMonoidHom) (g h : Y) :
    g * h ∈ normalizer (Kc : Set Y) ↔
      (g ∈ normalizer (Kc : Set Y) ↔ h ∈ normalizer (Kc : Set Y)) := by
  rw [mem_normalizer_iff_map_conj, map_conj_mul_eq]
  by_cases hh : h ∈ normalizer (Kc : Set Y)
  · rw [mem_normalizer_iff_map_conj.1 hh, ← mem_normalizer_iff_map_conj]
    exact ⟨fun h1 => ⟨fun _ => hh, fun _ => h1⟩, fun h1 => h1.2 hh⟩
  · have hKh : Kc.map (MulAut.conj h).toMonoidHom = Kc.map (MulAut.conj s).toMonoidHom :=
      (hor h).resolve_left fun h' => hh (mem_normalizer_iff_map_conj.2 h')
    rw [hKh]
    by_cases hg : g ∈ normalizer (Kc : Set Y)
    · rw [map_conj_swap_of_mem_normalizer hKt hor hg]
      exact ⟨fun h1 => absurd h1 hKt, fun h1 => absurd (h1.1 hg) hh⟩
    · rw [map_conj_swap_of_not_mem_normalizer hKt hor hg]
      exact ⟨fun _ => ⟨fun h1 => absurd h1 hg, fun h1 => absurd h1 hh⟩, fun _ => rfl⟩

omit [Finite Y] in
theorem commutatorElement_mem_normalizer_of_swap {Kc : Subgroup Y} {s : Y}
    (hKt : Kc.map (MulAut.conj s).toMonoidHom ≠ Kc)
    (hor : ∀ y : Y, Kc.map (MulAut.conj y).toMonoidHom = Kc ∨
      Kc.map (MulAut.conj y).toMonoidHom = Kc.map (MulAut.conj s).toMonoidHom) (g h : Y) :
    g * h * g⁻¹ * h⁻¹ ∈ normalizer (Kc : Set Y) := by
  have hr := mul_mem_normalizer_iff_of_swap hKt hor
  rw [hr, hr, hr, inv_mem_iff, inv_mem_iff]
  by_cases hA : g ∈ normalizer (Kc : Set Y) <;> by_cases hB : h ∈ normalizer (Kc : Set Y) <;>
    simp [hA, hB]

omit [Finite Y] in
theorem le_normalizer_of_perfect_of_swap {Kc : Subgroup Y} {s : Y}
    (hKt : Kc.map (MulAut.conj s).toMonoidHom ≠ Kc)
    (hor : ∀ y : Y, Kc.map (MulAut.conj y).toMonoidHom = Kc ∨
      Kc.map (MulAut.conj y).toMonoidHom = Kc.map (MulAut.conj s).toMonoidHom)
    {P : Subgroup Y} (hP : ⁅P, P⁆ = P) :
    P ≤ normalizer (Kc : Set Y) ∧
      P ≤ normalizer (Kc.map (MulAut.conj s).toMonoidHom : Set Y) := by
  have h1 : P ≤ normalizer (Kc : Set Y) := by
    rw [← hP]
    refine Subgroup.commutator_le.2 fun g _ h _ => ?_
    rw [commutatorElement_def]
    exact commutatorElement_mem_normalizer_of_swap hKt hor g h
  exact ⟨h1, fun p hp =>
    mem_normalizer_iff_map_conj.2 (map_conj_swap_of_mem_normalizer hKt hor (h1 hp))⟩

omit [Finite Y] in
theorem sup_map_conj_eq_of_swap {Kc : Subgroup Y} {s : Y}
    (hKt : Kc.map (MulAut.conj s).toMonoidHom ≠ Kc)
    (hor : ∀ y : Y, Kc.map (MulAut.conj y).toMonoidHom = Kc ∨
      Kc.map (MulAut.conj y).toMonoidHom = Kc.map (MulAut.conj s).toMonoidHom) (g : Y) :
    (Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom := by
  rw [Subgroup.map_sup]
  by_cases hg : g ∈ normalizer (Kc : Set Y)
  · rw [mem_normalizer_iff_map_conj.1 hg, map_conj_swap_of_mem_normalizer hKt hor hg]
  · rw [map_conj_swap_of_not_mem_normalizer hKt hor hg,
      (hor g).resolve_left fun h => hg (mem_normalizer_iff_map_conj.2 h), sup_comm]

theorem centralizer_sup_eq_bot_of_swap (hO : pPrimeCore 2 Y = ⊥) {Kc D : Subgroup Y}
    {s : Y} (hs : orderOf s = 2) (hsD : s ∈ centralizer (D : Set Y))
    (hDKK : D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom)
    (hKt : Kc.map (MulAut.conj s).toMonoidHom ≠ Kc)
    (hor : ∀ y : Y, Kc.map (MulAut.conj y).toMonoidHom = Kc ∨
      Kc.map (MulAut.conj y).toMonoidHom = Kc.map (MulAut.conj s).toMonoidHom)
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2) :
    centralizer ((Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom : Subgroup Y) : Set Y) = ⊥ := by
  set M : Subgroup Y := Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom with hM
  have hMn : M.Normal := ⟨fun m hm g => by
    have h := sup_map_conj_eq_of_swap hKt hor g
    rw [← hM] at h
    rw [← h]
    exact ⟨m, hm, rfl⟩⟩
  have hsN : s ∈ normalizer (M : Set Y) :=
    mem_normalizer_iff_map_conj.2 (sup_map_conj_eq_of_swap hKt hor s)
  have hsC : s ∉ centralizer (M : Set Y) := by
    intro hsC
    apply hKt
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      have h := (mem_centralizer_iff.1 hsC) k (le_sup_left (b := Kc.map _) hk)
      change s * k * s⁻¹ ∈ Kc
      rw [← h, mul_inv_cancel_right]
      exact hk
    · intro hx
      refine ⟨x, hx, ?_⟩
      have h := (mem_centralizer_iff.1 hsC) x (le_sup_left (b := Kc.map _) hx)
      change s * x * s⁻¹ = x
      rw [← h, mul_inv_cancel_right]
  have hCodd := odd_card_centralizer_of_le hDKK hs hsD hsN hsC hsyl
  have hCn : (centralizer (M : Set Y)).Normal := Subgroup.normal_centralizer
  exact CFSG.Walter.eq_bot_of_isSubnormal_of_odd hO hCn.isSubnormal hCodd

theorem perfect_le_sup_of_swap (hO : pPrimeCore 2 Y = ⊥) {Kc D : Subgroup Y}
    {s : Y} (hs : orderOf s = 2) (hsD : s ∈ centralizer (D : Set Y))
    (hDKK : D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom)
    (hKt : Kc.map (MulAut.conj s).toMonoidHom ≠ Kc)
    (hcomm : ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥)
    (hor : ∀ y : Y, Kc.map (MulAut.conj y).toMonoidHom = Kc ∨
      Kc.map (MulAut.conj y).toMonoidHom = Kc.map (MulAut.conj s).toMonoidHom)
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hOut : Group.IsSolvable (Outer Kc))
    (hOut' : Group.IsSolvable (Outer (Kc.map (MulAut.conj s).toMonoidHom)))
    {P : Subgroup Y} (hP : ⁅P, P⁆ = P) : P ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom := by
  set K' : Subgroup Y := Kc.map (MulAut.conj s).toMonoidHom with hK'
  obtain ⟨hPN, hPN'⟩ := le_normalizer_of_perfect_of_swap hKt hor hP
  have h1 := CFSG.SeitzReduction.perfect_le_sup_centralizer hOut hP hPN
  have h2 := CFSG.SeitzReduction.perfect_le_sup_centralizer hOut' hP hPN'
  have hCbot := centralizer_sup_eq_bot_of_swap hO hs hsD hDKK hKt hor hsyl
  have hKK' : K' ≤ centralizer (Kc : Set Y) := by
    rw [commutator_comm] at hcomm
    exact commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hKcK' : Kc ≤ centralizer (K' : Set Y) := commutator_eq_bot_iff_le_centralizer.1 hcomm
  intro p hp
  obtain ⟨k, hk, c, hc, hkc⟩ := exists_mul_of_mem_sup_of_commute
    (fun l hl c hc => mem_centralizer_iff.1 hc l hl) (h1 hp)
  obtain ⟨k', hk', c', hc', hkc'⟩ := exists_mul_of_mem_sup_of_commute
    (fun l hl c hc => mem_centralizer_iff.1 hc l hl) (h2 hp)
  have hkk : k * k' = k' * k := (mem_centralizer_iff.1 (hKcK' hk) k' hk').symm
  set z : Y := k'⁻¹ * c with hz
  have hz1 : z = k⁻¹ * c' := by
    have : k * c = k' * c' := hkc.symm.trans hkc'
    calc z = k'⁻¹ * c := rfl
      _ = k'⁻¹ * (k⁻¹ * (k * c)) := by group
      _ = k'⁻¹ * (k⁻¹ * (k' * c')) := by rw [this]
      _ = k'⁻¹ * k⁻¹ * k' * c' := by group
      _ = k⁻¹ * c' := by
        have : k'⁻¹ * k⁻¹ * k' = k⁻¹ := by
          calc k'⁻¹ * k⁻¹ * k' = (k * k')⁻¹ * k' := by group
            _ = (k' * k)⁻¹ * k' := by rw [hkk]
            _ = k⁻¹ := by group
        rw [this]
  have hzC : z ∈ centralizer ((Kc ⊔ K' : Subgroup Y) : Set Y) := by
    have hzK : z ∈ centralizer (Kc : Set Y) := mul_mem (inv_mem (hKK' hk')) hc
    have hzK' : z ∈ centralizer (K' : Set Y) := by
      rw [hz1]
      exact mul_mem (inv_mem (hKcK' hk)) hc'
    have hle : Kc ⊔ K' ≤ centralizer ((zpowers z : Subgroup Y) : Set Y) := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [centralizer_zpowers_eq, mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.1 hzK) x hx
      · intro x hx
        rw [centralizer_zpowers_eq, mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.1 hzK') x hx
    exact (le_centralizer_iff.1 hle) (mem_zpowers z)
  rw [hCbot, Subgroup.mem_bot] at hzC
  have hck : c = k' := by
    have : k'⁻¹ * c = 1 := hzC
    calc c = k' * (k'⁻¹ * c) := by group
      _ = k' := by rw [this, mul_one]
  rw [hkc, hck]
  exact mul_mem_sup hk hk'

end Swap

section NoSection

variable {Y : Type} [Group Y] [Finite Y]

theorem false_of_lieModel_quotient_of_le_sup {Kc K' P : Subgroup Y}
    (hcomm : ⁅Kc, K'⁆ = ⊥) (hZ' : center K' = ⊥)
    (hA : CFSG.ComponentClassification.CatLeaf.IsAltType Kc)
    (hA' : CFSG.ComponentClassification.CatLeaf.IsAltType K') (hPM : P ≤ Kc ⊔ K')
    {N : Subgroup P} [N.Normal] (hL : LieModel (P ⧸ N) .PSL 3 2 2)
    (hcard : Nat.card (P ⧸ N) = Nat.card Kc) (hcard' : Nat.card (P ⧸ N) = Nat.card K') : False := by
  have hS : IsSimpleGroup (P ⧸ N) := isSimpleGroup_of_lieModel_PSL hL
  have hnotAlt : ¬ CFSG.ComponentClassification.CatLeaf.IsAltType (P ⧸ N) := fun h =>
    CFSG.ComponentClassification.CatLeaf.not_isL34Type_of_isAltType h hL
  have hKK' : Kc ≤ centralizer (K' : Set Y) := commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hK'K : K' ≤ centralizer (Kc : Set Y) := by
    rw [commutator_comm] at hcomm
    exact commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hdec : ∀ p ∈ Kc ⊔ K', ∃ k ∈ Kc, ∃ k' ∈ K', p = k * k' := fun p hp =>
    exists_mul_of_mem_sup_of_commute (fun k hk k' hk' => mem_centralizer_iff.1 (hK'K hk') k hk) hp
  have hPN : P ≤ normalizer (Kc : Set Y) :=
    hPM.trans (sup_le le_normalizer (hK'K.trans (centralizer_le_normalizer _)))
  have hPN' : P ≤ normalizer (K' : Set Y) :=
    hPM.trans (sup_le (hKK'.trans (centralizer_le_normalizer _)) le_normalizer)
  set R : Subgroup P := Kc.subgroupOf P with hR
  have hRn : R.Normal := ⟨fun x hx p => by
    rw [hR, mem_subgroupOf] at hx ⊢
    have h := (mem_normalizer_iff.1 (hPN p.2) x).1 hx
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h⟩
  set φ : P →* P ⧸ N := QuotientGroup.mk' N with hφ
  have hRmap : (R.map φ).Normal := hRn.map φ (QuotientGroup.mk'_surjective N)
  have hcardP : Nat.card P = Nat.card (P ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rcases hS.eq_bot_or_eq_top_of_normal (R.map φ) with hbot | htop
  ·
    have hRN : R ≤ N := by
      have h := (Subgroup.map_eq_bot_iff _).1 hbot
      rwa [hφ, QuotientGroup.ker_mk'] at h
    set α : P →* MulAut K' := K'.normalizerMonoidHom.comp (Subgroup.inclusion hPN') with hα
    have hker : α.ker = R := by
      ext p
      rw [hα, MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
        Subgroup.normalizerMonoidHom_ker, mem_subgroupOf, hR, mem_subgroupOf]
      change (p : Y) ∈ centralizer (K' : Set Y) ↔ (p : Y) ∈ Kc
      constructor
      · intro hpC
        obtain ⟨k, hk, k', hk', hkk'⟩ := hdec p (hPM p.2)
        have hk'C : k' ∈ centralizer (K' : Set Y) := by
          have : k' = k⁻¹ * p := by rw [hkk']; group
          rw [this]
          exact mul_mem (inv_mem (hKK' hk)) hpC
        have hk'Z : (⟨k', hk'⟩ : K') ∈ center K' := by
          rw [mem_center_iff]
          intro y
          exact Subtype.ext ((mem_centralizer_iff.1 hk'C) y y.2)
        rw [hZ', Subgroup.mem_bot] at hk'Z
        have hk'1 : k' = 1 := congrArg Subtype.val hk'Z
        rw [hkk', hk'1, mul_one]
        exact hk
      · intro hpK
        exact hKK' hpK
    have hconj_inj : Function.Injective (MulAut.conj : K' →* MulAut K') := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hxZ : x ∈ center K' := by
        rw [mem_center_iff]
        intro y
        have h := DFunLike.congr_fun hx y
        rw [MulAut.conj_apply, MulAut.one_apply] at h
        calc y * x = (x * y * x⁻¹) * x := by rw [h]
          _ = x * y := by group
      rwa [hZ'] at hxZ
    have hrange : α.range ≤ (MulAut.conj : K' →* MulAut K').range := by
      rintro _ ⟨p, rfl⟩
      obtain ⟨k, hk, k', hk', hkk'⟩ := hdec p (hPM p.2)
      refine ⟨⟨k', hk'⟩, ?_⟩
      ext y
      rw [MulAut.conj_apply, hα, MonoidHom.comp_apply]
      change (k' * y * k'⁻¹ : Y) = p * y * (p : Y)⁻¹
      have hz : k' * (y : Y) * k'⁻¹ ∈ K' := K'.mul_mem (K'.mul_mem hk' y.2) (K'.inv_mem hk')
      have hcomm' : k * (k' * (y : Y) * k'⁻¹) = (k' * (y : Y) * k'⁻¹) * k :=
        ((mem_centralizer_iff.1 (hKK' hk)) _ hz).symm
      rw [hkk']
      calc k' * (y : Y) * k'⁻¹ = (k' * (y : Y) * k'⁻¹) * k * k⁻¹ := by group
        _ = k * (k' * (y : Y) * k'⁻¹) * k⁻¹ := by rw [hcomm']
        _ = k * k' * (y : Y) * (k * k')⁻¹ := by group
    have hcardInn : Nat.card (MulAut.conj : K' →* MulAut K').range = Nat.card K' :=
      (Nat.card_congr (MonoidHom.ofInjective hconj_inj).toEquiv).symm
    have hcardα : Nat.card P = Nat.card α.range * Nat.card α.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv]
    have hkerN : α.ker ≤ N := hker ▸ hRN
    have hrle : Nat.card α.range ≤ Nat.card (P ⧸ N) := by
      rw [hcard', ← hcardInn]
      exact Subgroup.card_le_of_le hrange
    have hSpos : 0 < Nat.card (P ⧸ N) := Nat.card_pos
    have hNpos : 0 < Nat.card N := Nat.card_pos
    have hkpos : 0 < Nat.card α.ker := Nat.card_pos
    have hNle : Nat.card N ≤ Nat.card α.ker := by
      by_contra hlt
      push Not at hlt
      have h1 : Nat.card α.range * Nat.card α.ker < Nat.card (P ⧸ N) * Nat.card N :=
        calc Nat.card α.range * Nat.card α.ker ≤ Nat.card (P ⧸ N) * Nat.card α.ker :=
              Nat.mul_le_mul_right _ hrle
          _ < Nat.card (P ⧸ N) * Nat.card N := Nat.mul_lt_mul_of_pos_left hlt hSpos
      omega
    have hkerEq : α.ker = N := Subgroup.eq_of_le_of_card_ge hkerN hNle
    have hrangeEq : Nat.card α.range = Nat.card (P ⧸ N) := by
      have h := hcardα.symm.trans hcardP
      rw [hkerEq] at h
      exact Nat.eq_of_mul_eq_mul_right hNpos h
    have hrangeInn : α.range = (MulAut.conj : K' →* MulAut K').range :=
      Subgroup.eq_of_le_of_card_ge hrange (by rw [hcardInn, ← hcard', hrangeEq])
    have e : P ⧸ N ≃* K' :=
      (QuotientGroup.quotientMulEquivOfEq hkerEq.symm).trans
        ((QuotientGroup.quotientKerEquivRange α).trans
          ((MulEquiv.subgroupCongr hrangeInn).trans (MonoidHom.ofInjective hconj_inj).symm))
    exact hnotAlt (CFSG.ComponentClassification.CatLeaf.IsAltType.of_mulEquiv e hA')
  ·
    have hsurj : Function.Surjective (φ.comp R.subtype) := by
      intro z
      have hz : z ∈ R.map φ := htop ▸ Subgroup.mem_top z
      obtain ⟨r, hr, rfl⟩ := hz
      exact ⟨⟨r, hr⟩, rfl⟩
    have hRcard : Nat.card (P ⧸ N) ≤ Nat.card R := Nat.card_le_card_of_surjective _ hsurj
    have hRinf : Nat.card R = Nat.card (Kc ⊓ P : Subgroup Y) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective P.subtype_injective]
    have hRK : Nat.card R ≤ Nat.card Kc := by
      rw [hRinf]
      exact Subgroup.card_le_of_le inf_le_left
    have hKP : Kc ≤ P := by
      have hle : Kc ⊓ P ≤ Kc := inf_le_left
      have hEq : Kc ⊓ P = Kc :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [← hRinf]; omega)
      rw [← hEq]
      exact inf_le_right
    have hbij : Function.Bijective (φ.comp R.subtype) :=
      (Nat.bijective_iff_surjective_and_card _).2 ⟨hsurj, by omega⟩
    have e : P ⧸ N ≃* Kc :=
      (MulEquiv.ofBijective _ hbij).symm.trans (Subgroup.subgroupOfEquivOfLe hKP)
    exact hnotAlt (CFSG.ComponentClassification.CatLeaf.IsAltType.of_mulEquiv e hA)

theorem card_of_lieModel_PSL_three_four {X : Type} [Group X] (h : LieModel X .PSL 3 2 2) :
    Nat.card X = 20160 :=
  CFSG.Blueprint.LieModel.card_psl_three_four h

theorem false_of_lieModel_quotient_of_range_le_sup {Q : Type}
    [Group Q] [Finite Q] {Kc K' : Subgroup Y} (hcomm : ⁅Kc, K'⁆ = ⊥) (hZ' : center K' = ⊥)
    (hA : CFSG.ComponentClassification.CatLeaf.IsAltType Kc)
    (hA' : CFSG.ComponentClassification.CatLeaf.IsAltType K') (ψ : Q →* Y)
    (hψ : ψ.range ≤ Kc ⊔ K') (hodd : Odd (Nat.card ψ.ker)) {N : Subgroup Q} [N.Normal]
    (hL : LieModel (Q ⧸ N) .PSL 3 2 2) (hcard : Nat.card (Q ⧸ N) = Nat.card Kc)
    (hcard' : Nat.card (Q ⧸ N) = Nat.card K') : False := by
  have hS : IsSimpleGroup (Q ⧸ N) := isSimpleGroup_of_lieModel_PSL hL
  have hS20160 := card_of_lieModel_PSL_three_four hL
  have hkerN : ψ.ker ≤ N := by
    have hMn : (ψ.ker.map (QuotientGroup.mk' N)).Normal :=
      (MonoidHom.normal_ker ψ).map _ (QuotientGroup.mk'_surjective N)
    rcases hS.eq_bot_or_eq_top_of_normal (ψ.ker.map (QuotientGroup.mk' N)) with h | h
    · have h' := (Subgroup.map_eq_bot_iff _).1 h
      rwa [QuotientGroup.ker_mk'] at h'
    · exfalso
      have hdvd := Subgroup.card_map_dvd ψ.ker (QuotientGroup.mk' N)
      rw [h, Subgroup.card_top, hS20160] at hdvd
      have := Odd.of_dvd_nat hodd hdvd
      revert this
      decide
  set P : Subgroup Y := ψ.range with hP
  set ρ : Q →* P := ψ.rangeRestrict with hρ
  have hρs : Function.Surjective ρ := ψ.rangeRestrict_surjective
  have hρker : ρ.ker = ψ.ker := ψ.ker_rangeRestrict
  set N' : Subgroup P := N.map ρ with hN'
  have hN'n : N'.Normal := Subgroup.Normal.map inferInstance ρ hρs
  have hcompS : Function.Surjective ((QuotientGroup.mk' N').comp ρ) :=
    (QuotientGroup.mk'_surjective N').comp hρs
  have hcompker : ((QuotientGroup.mk' N').comp ρ).ker = N := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hN', Subgroup.comap_map_eq, hρker,
      sup_eq_left.2 hkerN]
  have e : Q ⧸ N ≃* P ⧸ N' :=
    (QuotientGroup.quotientMulEquivOfEq hcompker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hcompS)
  have hL' : LieModel (P ⧸ N') .PSL 3 2 2 := LieType.CurtisTits.lieModel_of_mulEquiv e hL
  have hcardE : Nat.card (P ⧸ N') = Nat.card (Q ⧸ N) := (Nat.card_congr e.toEquiv).symm
  exact false_of_lieModel_quotient_of_le_sup hcomm hZ' hA hA' hψ hL' (hcardE.trans hcard)
    (hcardE.trans hcard')

end NoSection

end CFSG.SeitzReduction.LinearPilot
