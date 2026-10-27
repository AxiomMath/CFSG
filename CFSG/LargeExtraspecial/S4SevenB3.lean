module

public import CFSG.LargeExtraspecial.S4SevenB2
public import CFSG.LargeExtraspecial.S4SevenA6
public import CFSG.LargeExtraspecial.S4SevenB
public import CFSG.LargeExtraspecial.S4SevenC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2
open scoped commutatorElement

universe u

section Abstract

variable {X : Type*} [Group X]

theorem map_conj_le_of_mem_sup {L Y N : Subgroup X} (hLY : L ≤ Y)
    (hYN : Y ≤ normalizer (N : Set X))
    (hNL : ∀ y ∈ Y, N ≤ normalizer ((L.map (MulAut.conj y).toMonoidHom : Subgroup X) : Set X))
    {r : X} (hr : r ∈ N ⊔ Y) : L.map (MulAut.conj r).toMonoidHom ≤ Y := by
  have hr' : r ∈ ((N ⊔ Y : Subgroup X) : Set X) := hr
  rw [coe_mul_of_right_le_normalizer_left N Y hYN] at hr'
  obtain ⟨n, hn, y, hy, rfl⟩ := hr'
  rintro _ ⟨l, hl, rfl⟩
  have hly : y * l * y⁻¹ ∈ L.map (MulAut.conj y).toMonoidHom := ⟨l, hl, rfl⟩
  have h1 := (mem_normalizer_iff.mp (hNL y hy hn) _).mp hly
  obtain ⟨l', hl', he⟩ := h1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he ⊢
  rw [show n * y * l * (n * y)⁻¹ = n * (y * l * y⁻¹) * n⁻¹ by group, ← he]
  exact mul_mem (mul_mem hy (hLY hl')) (inv_mem hy)

variable [Finite X]

theorem le_normalizer_inf_sup_inf {A B N : Subgroup X} (hAN : A ≤ normalizer (N : Set X))
    (hNA : N ≤ normalizer (A : Set X)) :
    A ≤ normalizer (((A ⊓ N) ⊔ (B ⊓ N) : Subgroup X) : Set X) := by
  intro a ha
  refine mem_normalizer_of_conj_le fun p hp => ?_
  have hle : (A ⊓ N) ⊔ (B ⊓ N) ≤ ((A ⊓ N) ⊔ (B ⊓ N)).comap (MulAut.conj a).toMonoidHom := by
    refine sup_le ?_ ?_
    · intro y hy
      obtain ⟨hyA, hyN⟩ := mem_inf.mp hy
      exact mem_sup_left (mem_inf.mpr ⟨mul_mem (mul_mem ha hyA) (inv_mem ha),
        (mem_normalizer_iff.mp (hAN ha) y).mp hyN⟩)
    · intro y hy
      obtain ⟨hyB, hyN⟩ := mem_inf.mp hy
      have hc : a * y * a⁻¹ * y⁻¹ ∈ A ⊓ N := by
        refine mem_inf.mpr ⟨?_, mul_mem ((mem_normalizer_iff.mp (hAN ha) y).mp hyN)
          (inv_mem hyN)⟩
        rw [show a * y * a⁻¹ * y⁻¹ = a * (y * a⁻¹ * y⁻¹) by group]
        exact mul_mem ha ((mem_normalizer_iff.mp (hNA hyN) _).mp (inv_mem ha))
      rw [mem_comap]
      show a * y * a⁻¹ ∈ (A ⊓ N) ⊔ (B ⊓ N)
      rw [show a * y * a⁻¹ = (a * y * a⁻¹ * y⁻¹) * y by group]
      exact mul_mem (mem_sup_left hc) (mem_sup_right (mem_inf.mpr ⟨hyB, hyN⟩))
  exact hle hp

end Abstract

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem timmesfeld_4_7_b (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hcase : SpCase H C ht ht1 hVQ ∨ OmegaCase H C ht ht1 hVQ) {k : S.M}
    (hk : S.ρ k ∈ Rbar S g t)
    (hb : beta H C ht ht1 hVQ (aV ht) (orbV H.conj_mem ht hk) = 1) :
    Rbar S g t = S.Lbar g ⊔ S.Lbar ((k : G) * g) ∧
      Nbar S g t = (S.Lbar g ⊓ Nbar S g t) ⊔ (S.Lbar ((k : G) * g) ⊓ Nbar S g t) ∧
      ⁅Nbar S g t, Nbar S g t⁆ ≤ zpowers t := by
  have haQ := H.conj_mem
  have hne := H.conj_ne
  have hD : DtEqConj S g t := hcase.elim (fun hSp => dtEqConj_of_transitive H ht hSp.transitive)
    (fun hΩ => dtEqConj_of_omegaCase H hNo C hΩ)
  have hpair : NaturalPair (RmodN S g t) (LmodN S g t) (aV ht) :=
    hcase.elim (naturalPair_of_spCase H hNo C) (naturalPair_of_omegaCase H hNo C)
  have hnA : ¬ A6Pair (RmodN S g t) (LmodN S g t) (aV ht) :=
    hcase.elim (not_a6Pair_of_spCase H C) (not_a6Pair_of_omegaCase H C)
  have hNN0 : Nbar S g t = N0bar S g t :=
    (Nbar_eq_N0bar_or hCE H C ht hD hpair).resolve_right fun h => hnA h.1
  have hRN : Rbar S g t ≤ normalizer (Nbar S g t : Set S.O) := by
    intro r hr
    refine mem_normalizer_of_conj_le fun x hx => ?_
    obtain ⟨k', rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
    exact conj_mem_Nbar haQ (commute_of_mem_Rbar haQ hr) hx
  have htk : ∀ {k' : S.M}, S.ρ k' ∈ Rbar S g t → t ∈ S.Lbar ((k' : G) * g) := by
    intro k' hk'
    have := conj_mem_Lbar_mul S k' ht
    rwa [commute_of_mem_Rbar haQ hk', mul_assoc, mul_inv_cancel, mul_one] at this
  have hNL : ∀ r ∈ Rbar S g t, Nbar S g t ≤
      normalizer (((S.Lbar g).map (MulAut.conj r).toMonoidHom : Subgroup S.O) : Set S.O) := by
    intro r hr
    obtain ⟨k', rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
    rw [← Lbar_mul S k']
    exact Nbar_le_normalizer haQ hne (Lbar_mul_mem_Dset (htk hr))
  set r := S.ρ k with hr
  set Y := S.Lbar g ⊔ (S.Lbar g).map (MulAut.conj r).toMonoidHom with hY
  have hLk : S.Lbar ((k : G) * g) = (S.Lbar g).map (MulAut.conj r).toMonoidHom := Lbar_mul S k g
  have hYR : Y ≤ Rbar S g t := sup_le (Lbar_le_Rbar ht) (hLk ▸ Lbar_mul_le_Rbar (htk hk))
  have hgen := (RmodN_eq_closure_of_beta H C ht ht1 hVQ hNo hcase
    (e := resV haQ t ⟨r, hk⟩) ⟨r, hk, fun v => coe_resV_apply haQ _ v⟩ hb).le
  have hR1 := Rbar_le_sup_Nbar H ht hk hgen
  have hN0Y : N0bar S g t ≤ Y := by
    refine iSup₂_le fun k' hk' => ?_
    rw [Lbar_mul S k']
    refine inf_le_left.trans (map_conj_le_of_mem_sup le_sup_left (hYR.trans hRN)
      (fun y hy => hNL y (hYR hy)) ?_)
    have := hR1 hk'
    rwa [sup_comm] at this
  have hRY : Rbar S g t = Y := by
    refine le_antisymm (hR1.trans (sup_le le_rfl ?_)) hYR
    rw [hNN0]
    exact hN0Y
  set P := (S.Lbar g ⊓ Nbar S g t) ⊔ (S.Lbar ((k : G) * g) ⊓ Nbar S g t) with hP
  have hLR := Lbar_le_Rbar ht
  have hLkR : S.Lbar ((k : G) * g) ≤ Rbar S g t := Lbar_mul_le_Rbar (htk hk)
  have hNLg : Nbar S g t ≤ normalizer (S.Lbar g : Set S.O) :=
    Nbar_le_normalizer haQ hne (Lbar_mem_Dset ht)
  have hNLk : Nbar S g t ≤ normalizer (S.Lbar ((k : G) * g) : Set S.O) := hLk ▸ hNL r hk
  have hPR : Rbar S g t ≤ normalizer (P : Set S.O) := by
    rw [hRY]
    refine sup_le (le_normalizer_inf_sup_inf (hLR.trans hRN) hNLg) ?_
    rw [← hLk, hP, sup_comm]
    exact le_normalizer_inf_sup_inf (hLkR.trans hRN) hNLk
  have hNP : Nbar S g t = P := by
    refine le_antisymm ?_ (sup_le inf_le_right inf_le_right)
    rw [hNN0]
    refine iSup₂_le fun k' hk' => ?_
    intro y hy
    obtain ⟨hyL, hyN⟩ := mem_inf.mp hy
    rw [Lbar_mul S k'] at hyL
    obtain ⟨l, hl, rfl⟩ := hyL
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyN ⊢
    have hlN : l ∈ Nbar S g t := by
      have := (mem_normalizer_iff.mp (hRN (inv_mem hk')) _).mp hyN
      rwa [show (S.ρ k')⁻¹ * (S.ρ k' * l * (S.ρ k')⁻¹) * (S.ρ k')⁻¹⁻¹ = l by group] at this
    exact (mem_normalizer_iff.mp (hPR hk') l).mp (mem_sup_left (mem_inf.mpr ⟨hl, hlN⟩))
  have haQk := conj_mem_QG' S k.2 haQ
  have hcomm := commutator_sup_le_inf (A := S.Lbar g ⊓ Nbar S g t)
    (B := S.Lbar ((k : G) * g) ⊓ Nbar S g t)
    (fun a ha a' ha' => Lbar_comm S haQ (mem_inf.mp ha).1 (mem_inf.mp ha').1)
    (fun b hb b' hb' => Lbar_comm S haQk (mem_inf.mp hb).1 (mem_inf.mp hb').1)
    (fun b hb => mem_normalizer_of_conj_le fun a ha => mem_inf.mpr
      ⟨(mem_normalizer_iff.mp (hNLg (mem_inf.mp hb).2) a).mp (mem_inf.mp ha).1,
        (mem_normalizer_iff.mp (hRN (hLkR (mem_inf.mp hb).1)) a).mp (mem_inf.mp ha).2⟩)
    (fun a ha => mem_normalizer_of_conj_le fun b hb => mem_inf.mpr
      ⟨(mem_normalizer_iff.mp (hNLk (mem_inf.mp ha).2) b).mp (mem_inf.mp hb).1,
        (mem_normalizer_iff.mp (hRN (hLR (mem_inf.mp ha).1)) b).mp (mem_inf.mp hb).2⟩)
  refine ⟨hRY.trans (by rw [hLk]), hNP, ?_⟩
  rw [hNP]
  refine hcomm.trans fun y hy => ?_
  obtain ⟨⟨hyL, -⟩, ⟨hyLk, -⟩⟩ := mem_inf.mp hy
  rw [← timmesfeld_4_7_c H C ht ht1 hVQ]
  refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun x hx => ?_, hyL⟩
  have hxY : x ∈ Y := hRY ▸ hx
  have hle : Y ≤ centralizer {y} := by
    refine sup_le (fun l hl => mem_centralizer_singleton_iff.mpr (Lbar_comm S haQ hl hyL)) ?_
    rw [← hLk]
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (Lbar_comm S haQk hl hyLk)
  exact (mem_centralizer_singleton_iff.mp (hle hxY))

end CFSG.LargeExtraspecial.S4
