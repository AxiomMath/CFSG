module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Elem
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Prod
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup

theorem card_eq_card_map_mul_card_inf {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (X : Subgroup G) : Nat.card X = Nat.card (X.map f) * Nat.card ↥(X ⊓ f.ker) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (f.subgroupMap X).ker
  rw [Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective _ (f.subgroupMap_surjective X)).toEquiv] at h1
  refine h1.trans ?_
  congr 1
  rw [Subgroup.ker_subgroupMap]
  exact Nat.card_congr
    ⟨fun x => ⟨x.1.1, x.1.2, x.2⟩, fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩, fun _ => rfl, fun _ => rfl⟩

theorem nonempty_mulEquiv_map {G P : Type*} [Group G] [Group P] (π : G →* P) {D : Subgroup G}
    (h : D ⊓ π.ker = ⊥) : Nonempty (D ≃* D.map π) := by
  refine ⟨MulEquiv.ofBijective (π.subgroupMap D) ⟨?_, π.subgroupMap_surjective D⟩⟩
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.ker_subgroupMap, Subgroup.subgroupOf_eq_bot,
    disjoint_iff, inf_comm]
  exact h

theorem exists_mul_of_card_sixteen {V : Type} [Group V] [Finite V] (hc : ∀ x y : V, x * y = y * x)
    (hV : Nat.card V = 256) {A B : Subgroup V} (hA : Nat.card A = 16) (hB : Nat.card B = 16)
    (hinf : A ⊓ B = ⊥) (v : V) : ∃ a ∈ A, ∃ b ∈ B, v = a * b := by
  have hcard : Nat.card ↥(A ⊔ B) = 256 := by
    rw [card_sup_of_comm (fun x _ y _ => hc x y) hinf, hA, hB]
  have htop : A ⊔ B = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcard, hV])
  have : B.Normal := ⟨fun n hn g => by
    rw [hc g n, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩
  have hv : v ∈ (↑(A ⊔ B) : Set V) := by rw [htop]; trivial
  rw [Subgroup.mul_normal] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hv
  exact ⟨a, ha, b, hb, hab.symm⟩

variable {V : Type} [Group V] {G : Type*} [Group G]

theorem eq_one_of_fix_both {ρ : G →* MulAut V} (hρ : Function.Injective ρ) {A B : Subgroup V}
    (hdec : ∀ v : V, ∃ a ∈ A, ∃ b ∈ B, v = a * b) {x : G} (hA : ∀ u ∈ A, ρ x u = u)
    (hB : ∀ u ∈ B, ρ x u = u) : x = 1 := by
  apply hρ
  rw [map_one]
  ext v
  obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
  rw [map_mul, hA a ha, hB b hb]
  rfl

@[expose] def actOn (ρ : G →* MulAut V) (D : Subgroup G) (U : Subgroup V)
    (h : ∀ x ∈ D, ∀ v ∈ U, ρ x v ∈ U) : D →* MulAut U :=
  restrictAut (ρ.comp D.subtype) U (fun x u hu => h x x.2 u hu)

theorem actOn_injective {ρ : G →* MulAut V} (hρ : Function.Injective ρ) {A B : Subgroup V}
    (hdec : ∀ v : V, ∃ a ∈ A, ∃ b ∈ B, v = a * b) {D : Subgroup G}
    (h : ∀ x ∈ D, ∀ v ∈ A, ρ x v ∈ A) (htriv : ∀ x ∈ D, ∀ u ∈ B, ρ x u = u) :
    Function.Injective (actOn ρ D A h) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : ∀ u ∈ A, ρ x u = u := fun u hu =>
    congrArg (fun f : MulAut A => ((f ⟨u, hu⟩ : A) : V)) hx
  exact Subtype.ext (eq_one_of_fix_both hρ hdec h1 (htriv x x.2))

@[expose] def vecStab (ρ : G →* MulAut V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, MulAut.mul_apply, hh, hg]
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc ρ g⁻¹ v = ρ g⁻¹ (ρ g v) := by rw [hg]
      _ = v := by
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl

theorem mem_vecStab {ρ : G →* MulAut V} {v : V} {g : G} : g ∈ vecStab ρ v ↔ ρ g v = v :=
  Iff.rfl

theorem commutator_range_eq_self {A P : Type*} [Group A] [Group P] (hA : commutator A = ⊤)
    (f : A →* P) : ⁅f.range, f.range⁆ = f.range := by
  have h : ⁅(⊤ : Subgroup A), ⊤⁆ = ⊤ := hA
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h]

theorem odd_card_fusionOddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.Open.fusionOddCore X)) := by
  have h : CFSG.Open.fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold CFSG.Open.fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
