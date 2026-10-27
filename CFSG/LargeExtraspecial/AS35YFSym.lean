module

public import CFSG.LargeExtraspecial.AS35YFHub
public import CFSG.LargeExtraspecial.S12InspXSym
public import CFSG.Quasithin.Background.G118S3
public import CFSG.Monster.B.TwoA.Base.SymFiveAut
public import CFSG.LargeExtraspecial.AS35YFOut
public import Certificates.Data.A5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.OuterAutomorphisms

namespace Setting

theorem asc_mem_inner_of_equiv {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y)
    (h : ∀ β : MulAut Y, β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Y)
    (α : MulAut X) : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
  have h1 := h (MulAut.congr ψ α)
  rw [← inner_map_congr ψ] at h1
  obtain ⟨α', hα', he⟩ := h1
  have : α' = α := (MulAut.congr ψ).injective he
  rwa [← this]

theorem asc_card_centralizer_equiv {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y) (x : X) :
    Nat.card (centralizer ({x} : Set X)) = Nat.card (centralizer ({ψ x} : Set Y)) := by
  obtain ⟨e⟩ := asc_nonempty_centralizer_mulEquiv ψ x
  exact Nat.card_congr e.toEquiv

theorem asc_card_centralizer_eq_filter {Y : Type*} [Group Y] [Fintype Y] [DecidableEq Y] (s : Y) :
    Nat.card (centralizer ({s} : Set Y)) = (Finset.univ.filter (fun g => g * s = s * g)).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_centralizer_singleton_iff)

theorem card_centralizer_swap_three :
    Nat.card (centralizer ({swap 0 1} : Set (Perm (Fin 3)))) = 2 := by
  rw [asc_card_centralizer_eq_filter]
  decide

theorem card_centralizer_swap_five :
    Nat.card (centralizer ({swap 0 1} : Set (Perm (Fin 5)))) = 12 := by
  rw [asc_card_centralizer_eq_filter]
  decide

theorem card_centralizer_swap_eq {m : ℕ} {a b c d : Fin m} (hab : a ≠ b) (hcd : c ≠ d) :
    Nat.card (centralizer ({swap a b} : Set (Perm (Fin m)))) =
      Nat.card (centralizer ({swap c d} : Set (Perm (Fin m)))) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_swap hab hcd)
  rw [asc_card_centralizer_equiv (MulAut.conj g) (swap a b), MulAut.conj_apply, hg]

section Generic

variable {Xh : Type*} [Group Xh] {τ : Xh} {𝒜 : Set (MulAut Xh)}

theorem asc_false_of_perm_ge_seven_gen
    (hub : ∀ K : Subgroup Xh, CFSG.IsQuasisimple K → (∀ y ∈ K, y * τ = τ * y) →
      (∀ α ∈ 𝒜, ∀ y ∈ K, α y ∈ K) → False)
    (h𝒜 : ∀ α ∈ 𝒜, α τ = τ) {m : ℕ} (hm : 7 ≤ m) (ψ : Xh ≃* Perm (Fin m)) {a b : Fin m}
    (hab : a ≠ b) (hτ : ψ τ = swap a b) : False := by
  set C : Subgroup (Perm (Fin m)) := centralizer ({ψ τ} : Set (Perm (Fin m))) with hC
  have hK1 : (commutator C).map C.subtype = ⁅C, C⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  let e : commutator C ≃* (⁅C, C⁆ : Subgroup (Perm (Fin m))) :=
    ((commutator C).equivMapOfInjective _ C.subtype_injective).trans
      (MulEquiv.subgroupCongr hK1)
  have hsimp : IsSimpleGroup (⁅C, C⁆ : Subgroup (Perm (Fin m))) := by
    rw [hC, hτ]
    exact S12Insp4.isSimpleGroup_commutator_centralizer_swap hab hm
  have hns : ¬ Group.IsSolvable (⁅C, C⁆ : Subgroup (Perm (Fin m))) := by
    intro hs
    have e' : alternatingGroup {x : Fin m // x ≠ a ∧ x ≠ b} ≃* (⁅C, C⁆ : Subgroup (Perm (Fin m)))
        := by
      rw [hC, hτ]
      exact S12Insp4.commutatorCentralizerSwapEquiv hab hm
    exact S12Insp4.not_isSolvable_alternatingGroup_compl hab hm
      (Group.isSolvable_of_surjective (f := e'.symm.toMonoidHom) e'.symm.surjective)
  exact asc_false_of_centralizer_commutator_hom_simple_equiv hub h𝒜 ψ hns e.toMonoidHom
    e.surjective fun k hk x => by
      rw [MonoidHom.mem_ker, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff] at hk
      rw [hk, one_mul, mul_one]

end Generic

variable {G : Type} [Group G] [Finite G] {S : Setting G}

variable (hst : S.Asc512Standing)
include hst

theorem asc_false_of_inner (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M)
    (hinn : ∀ α : MulAut (S.LbarAsc ⧸ center S.LbarAsc),
      α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner _)
    (h8 : ¬ 8 ∣ Nat.card (centralizer ({QuotientGroup.mk (ascTL htD htM)} :
      Set (S.LbarAsc ⧸ center S.LbarAsc)))) : False := by
  have hle := asc_Pbar_le_Lbar_of_inner hst hP hS htD htM (fun p _ => hinn _)
  have hcard := card_ascPhat_of_le hst hP hS htD htM hle
  have hsub : S.ascPhat g ≤ centralizer ({QuotientGroup.mk (ascTL htD htM)} :
      Set (S.LbarAsc ⧸ center S.LbarAsc)) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (ascPhat_commute hP hS htD htM hy)
  have hdvd := Subgroup.card_dvd_of_le hsub
  rw [hcard] at hdvd
  have h3 := hS.three_le_width
  exact h8 ((pow_dvd_pow 2 (by omega : 3 ≤ 2 * S.width - 3)).trans hdvd)

theorem asc_false_of_perm_three (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M)
    (φ : S.LbarAsc ⧸ center S.LbarAsc ≃* Perm (Fin 3))
    (hφ : ∀ x : S.LbarAsc ⧸ center S.LbarAsc, x ∈ S.EhatAsc ↔ (φ x).IsSwap) : False := by
  refine asc_false_of_inner hst hP hS htD htM (asc_mem_inner_of_equiv φ fun β => ?_) ?_
  · obtain ⟨c, hc⟩ := CFSG.Quasithin.G11.G118.g118_perm_three_aut_inner β
    exact ⟨c, MulEquiv.ext fun x => (hc x).symm⟩
  · obtain ⟨a, b, hab, hτ⟩ : ∃ a b : Fin 3, a ≠ b ∧
        φ (QuotientGroup.mk (ascTL htD htM)) = swap a b :=
      (hφ _).mp ⟨ascTL htD htM, S.ρ_mem_DbarAsc htD htM, rfl⟩
    rw [asc_card_centralizer_equiv φ, hτ,
      card_centralizer_swap_eq hab (by decide : (0 : Fin 3) ≠ 1), card_centralizer_swap_three]
    decide

theorem asc_false_of_perm_five (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M)
    (φ : S.LbarAsc ⧸ center S.LbarAsc ≃* Perm (Fin 5))
    (hφ : ∀ x : S.LbarAsc ⧸ center S.LbarAsc, x ∈ S.EhatAsc ↔ (φ x).IsSwap) : False := by
  refine asc_false_of_inner hst hP hS htD htM (asc_mem_inner_of_equiv φ fun β => ?_) ?_
  · obtain ⟨c, rfl⟩ := CFSG.Monster.B.TwoA.sym5_conj_surjective β
    exact ⟨c, rfl⟩
  · obtain ⟨a, b, hab, hτ⟩ : ∃ a b : Fin 5, a ≠ b ∧
        φ (QuotientGroup.mk (ascTL htD htM)) = swap a b :=
      (hφ _).mp ⟨ascTL htD htM, S.ρ_mem_DbarAsc htD htM, rfl⟩
    rw [asc_card_centralizer_equiv φ, hτ,
      card_centralizer_swap_eq hab (by decide : (0 : Fin 5) ≠ 1), card_centralizer_swap_five]
    decide

end Setting

end CFSG.LargeExtraspecial
