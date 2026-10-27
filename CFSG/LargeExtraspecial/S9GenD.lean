module

public import CFSG.LargeExtraspecial.S9GenA
public import CFSG.LargeExtraspecial.S8FusA
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
open CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

section NQC

variable {t : S.O} [hN : NQHyp S g t]

@[expose] noncomputable def nConjC (x : S8.CMt S t) : Nbar S g t →* Nbar S g t where
  toFun n := ⟨x * n * (x : S.O)⁻¹, by
    obtain ⟨hxM, hxt⟩ := S8.mem_CMt.mp x.2
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hxM
    have := conj_mem_Nbar hN.conj_mem (k := k) (by rw [hk]; exact hxt) n.2
    rwa [hk] at this⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem coe_nConjC (x : S8.CMt S t) (n : Nbar S g t) :
    ((nConjC x n : Nbar S g t) : S.O) = x * n * (x : S.O)⁻¹ :=
  rfl

@[expose] noncomputable def nqLinC (x : S8.CMt S t) : NQ S g t →ₗ[ZMod 2] NQ S g t :=
  (QuotientGroup.map _ _ (nConjC x) (by
    intro n hn
    rw [mem_comap, mem_subgroupOf] at *
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
    change (x : S.O) * n * (x : S.O)⁻¹ ∈ zpowers t
    have hc := (Commute.zpow_right (S8.mem_CMt.mp x.2).2 k).eq
    rw [← hk, hc, mul_inv_cancel_right]
    exact zpow_mem_zpowers t k)).toAdditive.toZModLinearMap 2

theorem nqLinC_mk (x : S8.CMt S t) (n : Nbar S g t) :
    nqLinC x (nqMk n) = nqMk (nConjC x n) :=
  rfl

theorem nqLinC_comp (x y : S8.CMt S t) (m : NQ S g t) :
    nqLinC x (nqLinC y m) = nqLinC (x * y) m := by
  obtain ⟨n, rfl⟩ := nqMk_surjective m
  show nqMk (nConjC x (nConjC y n)) = nqMk (nConjC (x * y) n)
  congr 1

theorem nqLinC_one (m : NQ S g t) : nqLinC (1 : S8.CMt S t) m = m := by
  obtain ⟨n, rfl⟩ := nqMk_surjective m
  show nqMk (nConjC (1 : S8.CMt S t) n) = nqMk n
  congr 1

variable (S g t) in
@[expose] noncomputable def nqHomC : S8.CMt S t →* (NQ S g t ≃ₗ[ZMod 2] NQ S g t) where
  toFun x := LinearEquiv.ofLinearMap (nqLinC x) (nqLinC x⁻¹)
    (LinearMap.ext fun m => by
      show nqLinC x (nqLinC x⁻¹ m) = m
      rw [nqLinC_comp, mul_inv_cancel, nqLinC_one])
    (LinearMap.ext fun m => by
      show nqLinC x⁻¹ (nqLinC x m) = m
      rw [nqLinC_comp, inv_mul_cancel, nqLinC_one])
  map_one' := LinearEquiv.ext fun m => nqLinC_one m
  map_mul' x y := LinearEquiv.ext fun m => (nqLinC_comp x y m).symm

end NQC

variable (S g) in
@[expose] noncomputable def GamF (t : S.O) : Subgroup S.O :=
  S8.CMt S t ⊓ normalizer (Fbar S g t : Set S.O)

theorem mem_GamF {t x : S.O} :
    x ∈ GamF S g t ↔ (x ∈ S.Mbar ∧ x * t = t * x) ∧ x ∈ normalizer (Fbar S g t : Set S.O) := by
  rw [GamF, mem_inf, S8.mem_CMt]

variable (S g) in
@[expose] noncomputable def fqHom (t : S.O) [NQHyp S g t] :
    GamF S g t →* (nqSub S g t (Fbar S g t) ≃ₗ[ZMod 2] nqSub S g t (Fbar S g t)) :=
  restrictHom ((nqHomC S g t).comp (Subgroup.inclusion inf_le_left)) (nqSub S g t (Fbar S g t))
    (by
      rintro x _ ⟨n, hnF, rfl⟩
      refine ⟨nConjC (Subgroup.inclusion inf_le_left x) n, ?_, rfl⟩
      exact (mem_normalizer_iff.mp (mem_inf.mp x.2).2 _).mp hnF)

theorem coe_fqHom_mk {t : S.O} [NQHyp S g t] (x : GamF S g t) {n : Nbar S g t}
    (hn : (n : S.O) ∈ Fbar S g t) :
    ((fqHom S g t x ⟨nqMk n, ⟨n, hn, rfl⟩⟩ : nqSub S g t (Fbar S g t)) : NQ S g t) =
      nqMk (nConjC (Subgroup.inclusion inf_le_left x) n) :=
  rfl

theorem conj_eq_or_eq_mul_t (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) [hN : NQHyp S g t]
    {y x : S.O} (hy : y ∈ Nbar S g t) (hx : x ∈ Nbar S g t) (hxL : x ∈ S.Lbar g) :
    y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x * t := by
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  rcases S8.eq_one_or_eq_of_mem_zpowers htt (hN.comm y hy x hx) with h | h
  · left
    calc y * x * y⁻¹ = y * x * y⁻¹ * x⁻¹ * x := by group
      _ = x := by rw [h, one_mul]
  · right
    calc y * x * y⁻¹ = y * x * y⁻¹ * x⁻¹ * x := by group
      _ = x * t := by rw [h, Lbar_comm S H.conj_mem ht hxL]

theorem mem_normalizer_Fbar_of_mem_Nbar (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    [NQHyp S g t] (hFN : conjL S g t ⊆ Nbar S g t) {y : S.O} (hy : y ∈ Nbar S g t) :
    y ∈ normalizer (Fbar S g t : Set S.O) := by
  have key : ∀ z ∈ Nbar S g t, ∀ x ∈ Fbar S g t, z * x * z⁻¹ ∈ Fbar S g t := by
    intro z hz x hx
    rcases conj_eq_or_eq_mul_t H ht hz (Fbar_le_of_subset hFN hx) (Fbar_le_Lbar hx) with h | h
    · rw [h]
      exact hx
    · rw [h]
      exact mul_mem hx (self_mem_Fbar ht)
  refine mem_normalizer_iff.mpr fun x => ⟨key y hy x, fun hx => ?_⟩
  have := key y⁻¹ (inv_mem hy) _ hx
  rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at this

theorem mem_normalizer_Fbar_of_mem (t : S.O) {n : S.O} (hnM : n ∈ S.Mbar)
    (hnN : n ∈ normalizer (S.Lbar g : Set S.O)) :
    n ∈ normalizer (Fbar S g t : Set S.O) := by
  refine mem_normalizer_iff.mpr fun x => ⟨conj_mem_Fbar hnM hnN, fun hx => ?_⟩
  have := conj_mem_Fbar (inv_mem hnM) (inv_mem hnN) hx
  rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this

end CFSG.LargeExtraspecial.S9
