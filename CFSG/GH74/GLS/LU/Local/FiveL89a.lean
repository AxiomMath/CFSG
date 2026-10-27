module

public import CFSG.GH74.GLS.LU.Local.FiveH12
public import CFSG.GH74.GLS.LU.Local.KStep
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44a

public section

open Subgroup CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

theorem Ez_le_of_card {K : Type} [Group K] [Finite K] (a : K) {M : Subgroup K}
    (hMC : M ≤ centralizer ({a} : Set K)) (hMp : ⁅M, M⁆ = M)
    (hD : Nat.card ↥⁅centralizer ({a} : Set K), centralizer ({a} : Set K)⁆ ≤ Nat.card ↥M) :
    Ez a ≤ M := by
  set D := centralizer ({a} : Set K) with hDdef
  have hMD' : M ≤ ⁅D, D⁆ := by
    calc M = ⁅M, M⁆ := hMp.symm
      _ ≤ ⁅D, D⁆ := Subgroup.commutator_mono hMC hMC
  have hMeq : M = ⁅D, D⁆ := Subgroup.eq_of_le_of_card_ge hMD' hD
  have hP : ⁅Ez a, Ez a⁆ = Ez a := by
    unfold Ez
    rw [← Subgroup.map_commutator, CFSG.LocalCores.layer_perfect]
  have hPD : Ez a ≤ D := Subgroup.map_subtype_le _
  calc Ez a = ⁅Ez a, Ez a⁆ := hP.symm
    _ ≤ ⁅D, D⁆ := Subgroup.commutator_mono hPD hPD
    _ = M := hMeq.symm

theorem commutator_subgroupOf_self {G : Type} [Group G] {L' M : Subgroup G} (hM : M ≤ L')
    (hMp : ⁅M, M⁆ = M) : ⁅M.subgroupOf L', M.subgroupOf L'⁆ = M.subgroupOf L' := by
  apply Subgroup.map_injective L'.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hM, hMp]

theorem sl3_gen {G : Type} [Group G] [Finite G] {L' M₁ M₂ : Subgroup G} {a b : G}
    (hL : Nonempty (SL(3, ZMod 5) ≃* ↥L')) (ha : a ∈ L') (hb : b ∈ L')
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a ≠ b) (hc : a * b = b * a)
    (hM₁ : M₁ ≤ L') (hM₂ : M₂ ≤ L') (hM₁p : ⁅M₁, M₁⁆ = M₁) (hM₂p : ⁅M₂, M₂⁆ = M₂)
    (hM₁a : ∀ m ∈ M₁, m * a = a * m) (hM₂b : ∀ m ∈ M₂, m * b = b * m)
    (F₁ F₂ : Type) [Field F₁] [Finite F₁] [Field F₂] [Finite F₂] (hF₁ : Nat.card F₁ = 5)
    (hF₂ : Nat.card F₂ = 5) (e₁ : SL(2, F₁) ≃* ↥M₁) (e₂ : SL(2, F₂) ≃* ↥M₂) : L' ≤ M₁ ⊔ M₂ := by
  set K := ↥L' with hK
  have hKL : IsLnEps 3 K 1 5 := isLnEps_three_five hL.some
  set a' : K := ⟨a, ha⟩ with ha'
  set b' : K := ⟨b, hb⟩ with hb'
  have ha2' : orderOf a' = 2 := (Subgroup.orderOf_mk a ha).trans ha2
  have hb2' : orderOf b' = 2 := (Subgroup.orderOf_mk b hb).trans hb2
  have hne : a' ≠ b' := fun h => hab (congrArg Subtype.val h)
  have hcomm : a' * b' = b' * a' := Subtype.ext hc
  have hU := isFourSubgroup_zpowers_sup ha2' hb2' hne hcomm
  have h44 := (CFSG.GH74.GLS.IVK.Proofs2.ivk_4_4a K 1 5 1 Nat.prime_five (by norm_num) (by simpa using hKL) _ hU a'
    (Subgroup.mem_sup_left (mem_zpowers a')) b' (Subgroup.mem_sup_right (mem_zpowers b'))
    ha2' hb2' hne).1 (by norm_num)
  have hlayer : ∀ (c : K) (hc2 : orderOf c = 2) (M : Subgroup G) (hM : M ≤ L') (hMp : ⁅M, M⁆ = M)
      (hMc : ∀ m ∈ M, m * (c : G) = (c : G) * m) (F : Type) [Field F] [Finite F] (hF : Nat.card F = 5)
      (e : SL(2, F) ≃* ↥M), Ez c ≤ M.subgroupOf L' := by
    intro c hc2 M hM hMp hMc F _ _ hF e
    refine Ez_le_of_card c ?_ (commutator_subgroupOf_self hM hMp) ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hMc (x : G) hx
      exact Subtype.ext this
    · have h1 := card_derived_centralizer_le hKL c hc2 F hF
      have h2 : Nat.card ↥(M.subgroupOf L') = Nat.card (SL(2, F)) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM).toEquiv]
        exact (Nat.card_congr e.toEquiv).symm
      rw [h2]; exact h1
  have hE₁ := hlayer a' ha2' M₁ hM₁ hM₁p hM₁a F₁ hF₁ e₁
  have hE₂ := hlayer b' hb2' M₂ hM₂ hM₂p hM₂b F₂ hF₂ e₂
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq] at h44
  have h3 : (⊤ : Subgroup K) ≤ M₁.subgroupOf L' ⊔ M₂.subgroupOf L' := by
    rw [← h44]
    exact sup_le_sup hE₁ hE₂
  have h4 := Subgroup.map_mono (f := L'.subtype) h3
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hM₁, Subgroup.map_subgroupOf_eq_of_le hM₂,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h4
  exact h4

end CFSG.GH74.GLS.LU.Local.Five
