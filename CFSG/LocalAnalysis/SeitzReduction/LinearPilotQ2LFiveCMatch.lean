module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2HR8Kinds

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (oddCoreLift HasBLift)
open CFSG.Quasithin (perfectCore)

section Orders

variable {X : Type*} [Group X]

theorem card_sup_dvd_mul_of_le_centralizer {A B : Subgroup X}
    (hBA : B ≤ centralizer (A : Set X)) : Nat.card (A ⊔ B : Subgroup X) ∣ Nat.card A * Nat.card B := by
  have comm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    (mem_centralizer_iff.1 (hBA b.2)) a a.2
  have hr := MonoidHom.noncommCoprod_range A.subtype B.subtype comm
  rw [range_subtype, range_subtype] at hr
  have h := Subgroup.card_range_dvd (A.subtype.noncommCoprod B.subtype comm)
  rw [hr, Nat.card_prod] at h
  exact h

end Orders

section KMOne

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem card_specialLinearGroup_three_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) = 168 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  classical
  rw [Matrix.card_SL_field, hq]
  decide

theorem not_five_dvd_card_of_perfect_of_swap
    (hset : SeitzSetting G L)
    {K : Type} [Field K] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin 5} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL 5 K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin 5))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDKK : (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤
      Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
        ⟨t, htX⟩)).toMonoidHom)
    (hne : Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
      ⟨t, htX⟩)).toMonoidHom ≠ Kc)
    (hcomm : ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
      ⟨t, htX⟩)).toMonoidHom⁆ = ⊥)
    (hiso : Nonempty (Kc ≃* (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))))
    {P : Subgroup G} (hPX : P ≤ centralizer (X : Set G)) (hP : ⁅P, P⁆ = P) :
    ¬ 5 ∣ Nat.card P := by
  obtain ⟨-, -, hcent, -, hsup, -, -, ⟨φ⟩⟩ := neighbourCore_swap_linear_two hset hK e
    (by norm_num) htC ht hab hX₀ hX₀c hX htX hDe hKc hDKK hne hcomm hiso
  obtain ⟨-, -, ⟨eDb⟩⟩ :=
    nonempty_map_oddCore_mulEquiv_specialLinear_two hK e (by norm_num) htC hab hX₀ hX₀c hX hDe
  obtain ⟨ψ⟩ := hiso
  have h3 : Nat.card (Matrix.SpecialLinearGroup (Fin (5 - 2)) K) = 168 :=
    card_specialLinearGroup_three_of_card_two hK
  have hKhc : Nat.card (oddCoreLift Kc) = 168 := by
    rw [Nat.card_congr ((φ.trans ψ).trans eDb).toEquiv]
    exact h3
  have hKhtc : Nat.card ((oddCoreLift Kc).map
      (MulAut.conj (⟨t, htX⟩ : centralizer (X : Set G))).toMonoidHom) = 168 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (⟨t, htX⟩ : centralizer (X : Set G))).injective,
      hKhc]
  have hP'map : (P.subgroupOf (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype =
      P := by
    rw [subgroupOf_map_subtype, inf_eq_left.2 hPX]
  have hP' : ⁅P.subgroupOf (centralizer (X : Set G)), P.subgroupOf (centralizer (X : Set G))⁆ =
      P.subgroupOf (centralizer (X : Set G)) := by
    apply Subgroup.map_injective (centralizer (X : Set G)).subtype_injective
    rw [map_commutator, hP'map, hP]
  have hle : P.subgroupOf (centralizer (X : Set G)) ≤ oddCoreLift Kc ⊔ (oddCoreLift Kc).map
      (MulAut.conj (⟨t, htX⟩ : centralizer (X : Set G))).toMonoidHom := by
    rw [hsup]
    exact CFSG.Quasithin.le_perfectCore_of_perfect le_top hP'
  have hdvd : Nat.card P ∣ Nat.card (oddCoreLift Kc) * Nat.card ((oddCoreLift Kc).map
      (MulAut.conj (⟨t, htX⟩ : centralizer (X : Set G))).toMonoidHom) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hPX).toEquiv]
    exact (Subgroup.card_dvd_of_le hle).trans (card_sup_dvd_mul_of_le_centralizer hcent)
  rw [hKhc, hKhtc] at hdvd
  intro h5
  have := h5.trans hdvd
  norm_num at this

end KMOne

end CFSG.SeitzReduction.LinearPilot
