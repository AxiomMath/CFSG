module

public import CFSG.Foundations.Basic

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup

theorem exists_perfect_odd_central_cover {Y T : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    [Group T] (e : Y ⧸ center Y ≃* T) :
    ∃ (E : Type) (_ : Group E) (_ : Finite E) (_ : Group.IsPerfect E) (π : E →* T),
      Function.Surjective π ∧ π.ker ≤ center E ∧ Odd (Nat.card π.ker) ∧
        ∃ a : ℕ, Nat.card (center Y) = 2 ^ a * Nat.card π.ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite T := Finite.of_equiv _ e.toEquiv
  obtain ⟨P⟩ : Nonempty (Sylow 2 (center Y)) := inferInstance
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = (Nat.card (center Y)).factorization 2 := ⟨_, rfl⟩
  set P₂ : Subgroup Y := (P : Subgroup (center Y)).map (center Y).subtype with hP₂def
  have hP₂ : P₂ ≤ center Y := Subgroup.map_subtype_le _
  haveI : P₂.Normal := Subgroup.normal_of_le_center hP₂
  have hcardP : Nat.card P₂ = 2 ^ a := by
    rw [ha, hP₂def, Subgroup.card_subtype]
    exact Sylow.card_eq_multiplicity P
  set φ : Y →* T := e.toMonoidHom.comp (QuotientGroup.mk' (center Y)) with hφdef
  have hφker : φ.ker = center Y := by
    ext x
    rw [hφdef, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  set π : Y ⧸ P₂ →* T := QuotientGroup.lift P₂ φ (fun x hx => by
    rw [hφker]
    exact hP₂ hx) with hπdef
  have hπmk : ∀ y : Y, π (y : Y ⧸ P₂) = φ y := fun y => rfl
  have hπs : Function.Surjective π := by
    intro t
    obtain ⟨y, rfl⟩ := hφs t
    exact ⟨(y : Y ⧸ P₂), hπmk y⟩
  have hπC : π.ker ≤ center (Y ⧸ P₂) := by
    intro q hq
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : y ∈ center Y := by
      rw [← hφker, MonoidHom.mem_ker, ← hπmk]
      exact hq
    rw [Subgroup.mem_center_iff]
    intro g'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hy g]
  have hT0 : 0 < Nat.card T := Nat.card_pos
  have h1 : Nat.card Y = Nat.card T * Nat.card (center Y) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center Y), Nat.card_congr e.toEquiv]
  have h2 : Nat.card Y = Nat.card (Y ⧸ P₂) * Nat.card P₂ :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup P₂
  have h3 : Nat.card (Y ⧸ P₂) = Nat.card T * Nat.card π.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv]
  have hZ : Nat.card (center Y) = 2 ^ a * Nat.card π.ker := by
    rw [← hcardP, mul_comm]
    refine Nat.eq_of_mul_eq_mul_left hT0 ?_
    rw [← h1, h2, h3, mul_assoc]
  have hZ0 : Nat.card (center Y) ≠ 0 := Nat.card_pos.ne'
  have hodd : Odd (Nat.card π.ker) := by
    by_contra hne
    have h2K : 2 ∣ Nat.card π.ker := (Nat.not_odd_iff_even.1 hne).two_dvd
    have hdvd : 2 ^ (a + 1) ∣ Nat.card (center Y) := by
      rw [hZ, pow_succ]
      exact mul_dvd_mul_left _ h2K
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hZ0).1 hdvd
    omega
  exact ⟨Y ⧸ P₂, inferInstance, inferInstance, inferInstance, π, hπs, hπC, hodd, a, hZ⟩

theorem not_dvd_card_center_of_odd_cover_trivial {Y T : Type} [Group Y] [Finite Y] [Group T]
    (hY : CFSG.IsQuasisimple Y) (e : Y ⧸ center Y ≃* T) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* T),
      Function.Surjective π → π.ker ≤ center E → Odd (Nat.card π.ker) → π.ker = ⊥) :
    ¬ r ∣ Nat.card (center Y) := by
  haveI : Group.IsPerfect Y := hY.1
  obtain ⟨E, _, _, _, π, hπ, hC, hodd, a, ha⟩ := exists_perfect_odd_central_cover e
  rw [h E π hπ hC hodd, Subgroup.card_bot, mul_one] at ha
  intro hrZ
  rw [ha] at hrZ
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hrZ))

end CFSG.SectionRank.QTK.CentreFact
