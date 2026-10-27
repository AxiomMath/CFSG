module

public import Mathlib.GroupTheory.IsPerfect
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.GroupTheory.PerfectCentralExtensionUnique

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

theorem center_eq_bot_of_ker_eq_center {S Q : Type*} [Group S] [Group Q]
    (hperf : commutator S = ⊤) (Ψ : S →* Q) (hΨ : Function.Surjective Ψ)
    (hk : Ψ.ker = Subgroup.center S) : Subgroup.center Q = ⊥ := by
  haveI : Group.IsPerfect S := ⟨hperf⟩
  let e : (S ⧸ Subgroup.center S) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective Ψ hΨ)
  rw [← Subgroup.map_center_eq e, Group.IsPerfect.center_quotient_center_eq_bot S,
    Subgroup.map_bot]

theorem map_inf_center_le {S Y K : Type*} [Group S] [Group Y] [Group K]
    (hperf : commutator S = ⊤) (Φ : S →* K) (N : Subgroup Y) [N.Normal]
    (Ψ : S →* Y ⧸ N) (hΨ : Function.Surjective Ψ) (hΨk : Ψ.ker = Subgroup.center S)
    (ι : Y →* K) (hι : Function.Injective ι) (hle : ι.range ≤ Φ.range) :
    (ι.range.comap Φ ⊓ Subgroup.center S).map Φ ≤ N.map ι := by
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨hs1, hsZ⟩ := Subgroup.mem_inf.mp hs
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (Subgroup.mem_comap.mp hs1)
  have hyZ : y ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y'
    apply hι
    obtain ⟨s', hs'⟩ :=
      MonoidHom.mem_range.mp (hle (MonoidHom.mem_range.mpr ⟨y', rfl⟩))
    calc ι (y' * y) = ι y' * ι y := map_mul ι y' y
      _ = Φ s' * Φ s := by rw [hy, hs']
      _ = Φ (s' * s) := (map_mul Φ s' s).symm
      _ = Φ (s * s') := by rw [Subgroup.mem_center_iff.mp hsZ s']
      _ = Φ s * Φ s' := map_mul Φ s s'
      _ = ι y * ι y' := by rw [hy, hs']
      _ = ι (y * y') := (map_mul ι y y').symm
  have hyN : y ∈ N := by
    have hmem : QuotientGroup.mk' N y ∈ Subgroup.center (Y ⧸ N) :=
      Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N)
        (Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hyZ)
    rw [center_eq_bot_of_ker_eq_center hperf Ψ hΨ hΨk] at hmem
    rw [QuotientGroup.mk'_apply] at hmem
    exact QuotientGroup.eq_one_iff y |>.mp (Subgroup.mem_bot.mp hmem)
  exact Subgroup.mem_map.mpr ⟨y, hyN, hy⟩

theorem range_le_of_perfect_of_quotient {S Y K : Type} [Group S] [Group Y] [Group K]
    [Finite S] [Finite Y] [Finite K] (hperf : commutator S = ⊤) (Φ : S →* K)
    (hΦ : Φ.ker ≤ Subgroup.center S) (N : Subgroup Y) [N.Normal] (Ψ : S →* Y ⧸ N)
    (hΨ : Function.Surjective Ψ) (hΨk : Ψ.ker = Subgroup.center S) (ι : Y →* K)
    (hι : Function.Injective ι) (hle : ι.range ≤ Φ.range) : Φ.range ≤ ι.range := by
  haveI : Group.IsPerfect S := ⟨hperf⟩
  set S₁ : Subgroup S := ι.range.comap Φ with hS₁
  have hker_le : Φ.ker ≤ S₁ := by
    intro x hx
    rw [hS₁, Subgroup.mem_comap, hx]
    exact ι.range.one_mem
  have hker_le' : Φ.ker ≤ S₁ ⊓ Subgroup.center S := le_inf hker_le hΦ
  have hmap : S₁.map Φ = ι.range := by
    rw [hS₁, Subgroup.map_comap_eq, inf_eq_right.mpr hle]
  have hYS₁ : Nat.card ↥S₁ = Nat.card Y * Nat.card ↥Φ.ker := by
    have h := Subgroup.relIndex_mul_card (H := Φ.ker) (K := S₁)
    rw [show Φ.ker.relIndex S₁ = Nat.card ↥(S₁.map Φ) from Subgroup.relIndex_ker S₁ Φ, hmap,
      inf_eq_left.mpr hker_le] at h
    rw [← h]
    congr 1
    rw [← Subgroup.map_top ι, Subgroup.card_map_of_injective (K := ⊤) (f := ι) hι,
      Subgroup.card_top]
  have hinf : Nat.card ↥(S₁ ⊓ Subgroup.center S) ≤ Nat.card N * Nat.card ↥Φ.ker := by
    have hle' : (S₁ ⊓ Subgroup.center S).map Φ ≤ N.map ι :=
      map_inf_center_le hperf Φ N Ψ hΨ hΨk ι hι hle
    have h := Subgroup.relIndex_mul_card (H := Φ.ker) (K := S₁ ⊓ Subgroup.center S)
    rw [show Φ.ker.relIndex (S₁ ⊓ Subgroup.center S) =
        Nat.card ↥((S₁ ⊓ Subgroup.center S).map Φ) from
        Subgroup.relIndex_ker (S₁ ⊓ Subgroup.center S) Φ,
      inf_eq_left.mpr hker_le'] at h
    rw [← h, ← Subgroup.card_map_of_injective (K := N) (f := ι) hι]
    exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hle')
  have hsupTop : S₁ ⊔ Subgroup.center S = ⊤ := by
    have hnorm : S₁ ≤ Subgroup.normalizer (Subgroup.center S : Set S) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    have hcard := CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := S₁) (K := Subgroup.center S) hnorm
    have hS : Nat.card ↥(Subgroup.center S) * Nat.card (Y ⧸ N) = Nat.card S := by
      rw [← hΨk]
      exact Subgroup.card_ker_mul_card_of_surjective (f := Ψ) hΨ
    have hY : Nat.card Y = Nat.card N * Nat.card (Y ⧸ N) := by
      have h := Subgroup.card_ker_mul_card_of_surjective
        (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      rw [QuotientGroup.ker_mk'] at h
      exact h.symm
    have hEq : Nat.card ↥(S₁ ⊔ Subgroup.center S) * Nat.card ↥(S₁ ⊓ Subgroup.center S) =
        Nat.card S * (Nat.card N * Nat.card ↥Φ.ker) := by
      rw [hcard, hYS₁, hY, ← hS]
      ring
    have hpos : 0 < Nat.card N * Nat.card ↥Φ.ker := Nat.mul_pos Nat.card_pos Nat.card_pos
    refine Subgroup.eq_top_of_le_card (H := S₁ ⊔ Subgroup.center S) ?_
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Nat.card S * (Nat.card N * Nat.card ↥Φ.ker)
        = Nat.card ↥(S₁ ⊔ Subgroup.center S) * Nat.card ↥(S₁ ⊓ Subgroup.center S) := hEq.symm
      _ ≤ Nat.card ↥(S₁ ⊔ Subgroup.center S) * (Nat.card N * Nat.card ↥Φ.ker) :=
          Nat.mul_le_mul_left _ hinf
  have htop : S₁ = ⊤ :=
    eq_top_of_sup_le_center_of_isPerfect (L := S₁) (Z := Subgroup.center S) le_rfl hsupTop
  intro k hk
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hk
  have hs : s ∈ S₁ := htop.symm ▸ Subgroup.mem_top s
  rw [hS₁] at hs
  exact Subgroup.mem_comap.mp hs

end CFSG.GroupTheory
