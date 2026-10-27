module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64Glue

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

@[expose] def BetaFor (X : Type*) [Group X] (β : X) : Prop :=
  orderOf β = 3 ∧
    Nonempty (↥(centralizer ({β} : Set X)) ⧸ fusionOddCore ↥(centralizer ({β} : Set X)) ≃*
      alternatingGroup (Fin 6)) ∧
    fusionOddCoreOf (centralizer ({β} : Set X)) ≤ zpowers β

theorem BetaFor.of_hom {X : Type*} [Group X] [Finite X] {β : X} (hβ : orderOf β = 3)
    (π : ↥(centralizer ({β} : Set X)) →* alternatingGroup (Fin 6)) (hπ : Function.Surjective π)
    (hker : ∀ x, π x = 1 ↔ (x : X) ∈ zpowers β) : BetaFor X β := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hOker : fusionOddCore ↥(centralizer ({β} : Set X)) = π.ker := by
    apply le_antisymm
    · have hNn : (fusionOddCore ↥(centralizer ({β} : Set X))).Normal := fusionOddCore_normal _
      have hMn : ((fusionOddCore ↥(centralizer ({β} : Set X))).map π).Normal :=
        Subgroup.Normal.map hNn π hπ
      have hModd : Odd (Nat.card ((fusionOddCore ↥(centralizer ({β} : Set X))).map π)) :=
        Odd.of_dvd_nat (odd_natCard_fusionOddCore ↥(centralizer ({β} : Set X)))
          (Subgroup.card_map_dvd _ π)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((fusionOddCore ↥(centralizer ({β} : Set X))).map π) with h | h
      · intro x hx
        have hx1 : π x ∈ (fusionOddCore ↥(centralizer ({β} : Set X))).map π := ⟨x, hx, rfl⟩
        rw [h, mem_bot] at hx1
        exact hx1
      · rw [h, Subgroup.card_top] at hModd
        exact absurd even_natCard_alternatingGroup_six (Nat.not_even_iff_odd.2 hModd)
    · have hnormal : π.ker.Normal := MonoidHom.normal_ker π
      have hodd : Odd (Nat.card π.ker) := by
        by_contra hnot
        have h2 : 2 ∣ Nat.card π.ker := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hnot)
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) 2 h2
        have hxβ : ((x : ↥(centralizer ({β} : Set X))) : X) ∈ zpowers β :=
          (hker _).1 (MonoidHom.mem_ker.1 x.2)
        have h3 : orderOf ((x : ↥(centralizer ({β} : Set X))) : X) ∣ 3 :=
          hβ ▸ orderOf_dvd_of_mem_zpowers hxβ
        have h4 : orderOf ((x : ↥(centralizer ({β} : Set X))) : X) = 2 := by
          rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
        rw [h4] at h3
        omega
      exact le_fusionOddCore hodd
  refine ⟨hβ, ⟨?_⟩, ?_⟩
  · exact (QuotientGroup.quotientMulEquivOfEq hOker).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  · rintro _ ⟨y, hy, rfl⟩
    rw [hOker] at hy
    exact (hker y).1 (MonoidHom.mem_ker.1 hy)

theorem BetaFor.map {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y] (e : X ≃* Y) {β : X}
    (h : BetaFor X β) : BetaFor Y (e β) := by
  obtain ⟨h3, ⟨eD⟩, hO⟩ := h
  have hc : centralizer ({e β} : Set Y) = (centralizer ({β} : Set X)).map e.toMonoidHom := by
    ext y
    constructor
    · intro hy
      refine ⟨e.symm y, mem_centralizer_singleton_iff.2 ?_, e.apply_symm_apply y⟩
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact mem_centralizer_singleton_iff.1 hy
    · rintro ⟨x, hx, rfl⟩
      refine mem_centralizer_singleton_iff.2 ?_
      show e x * e β = e β * e x
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hx]
  let f : ↥(centralizer ({β} : Set X)) ≃* ↥(centralizer ({e β} : Set Y)) :=
    ((centralizer ({β} : Set X)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hc.symm)
  have hf : ∀ x : ↥(centralizer ({β} : Set X)),
      ((f x : ↥(centralizer ({e β} : Set Y))) : Y) = e (x : X) := fun x => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact h3
  · have hmap : (fusionOddCore ↥(centralizer ({e β} : Set Y))).map f.symm.toMonoidHom =
        fusionOddCore ↥(centralizer ({β} : Set X)) := map_fusionOddCore_mulEquiv f.symm
    exact ⟨(QuotientGroup.congr _ _ f.symm hmap).trans eD⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : f.symm y ∈ fusionOddCore ↥(centralizer ({β} : Set X)) :=
      map_fusionOddCore_le f.symm ⟨y, hy, rfl⟩
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (hO ⟨f.symm y, hy', rfl⟩)
    have hj' : β ^ j = ((f.symm y : ↥(centralizer ({β} : Set X))) : X) := hj
    have h1 : ((y : ↥(centralizer ({e β} : Set Y))) : Y) =
        e ((f.symm y : ↥(centralizer ({β} : Set X))) : X) := by
      rw [← hf]
      simp
    show ((y : ↥(centralizer ({e β} : Set Y))) : Y) ∈ zpowers (e β)
    rw [h1, ← hj', map_zpow]
    exact zpow_mem (mem_zpowers _) j

theorem BetaFor.conj {X : Type*} [Group X] [Finite X] (g : X) {β : X} (h : BetaFor X β) :
    BetaFor X (g * β * g⁻¹) :=
  BetaFor.map (MulAut.conj g) h

end CFSG.EvenSporadicStandard.Fin76b
