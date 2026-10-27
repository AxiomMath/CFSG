module

public import CFSG.LocalAnalysis.GL83PartI.I713.Chain

public section

namespace GL83.I713

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

variable {p : ℕ}

theorem pRank_top_le_of_coprime_ker {Y Q : Type*} [Group Y] [Finite Y] [Group Q] [Finite Q]
    (hp : p.Prime) (Ψ : Y →* Q) (h : ¬ p ∣ Nat.card Ψ.ker) :
    pRank p (⊤ : Subgroup Y) ≤ pRank p (⊤ : Subgroup Q) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← CFSG.SectionRank.pRank_quotient_eq Ψ.ker h,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (QuotientGroup.quotientKerEquivRange Ψ)]
  exact CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt Ψ.range.subtype
    Ψ.range.subtype_injective

theorem pRank_top_le_one_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (hp : p.Prime) : pRank p (⊤ : Subgroup C) ≤ 1 := by
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup C)
  have hle := card_le_of_isElemAbelian_of_isCyclic hp hE inferInstance
  rw [hcard] at hle
  by_contra h
  have h1 : p ^ 2 ≤ p ^ pRank p (⊤ : Subgroup C) := Nat.pow_le_pow_right hp.pos (by omega)
  have h2 : p < p ^ 2 := by
    have := hp.two_le
    nlinarith
  omega

theorem card_ker_fst {A B : Type*} [Group A] [Group B] :
    Nat.card (MonoidHom.fst A B).ker = Nat.card B :=
  Nat.card_congr
    { toFun := fun x => x.1.2
      invFun := fun b => ⟨(1, b), rfl⟩
      left_inv := fun x => Subtype.ext (Prod.ext (x.2).symm rfl)
      right_inv := fun b => rfl }

theorem pRank_top_le_one_of_prod {A B : Type*} [Group A] [Finite A] [IsCyclic A] [Group B]
    [Finite B] (hp : p.Prime) (hB : ¬ p ∣ Nat.card B) :
    pRank p (⊤ : Subgroup (A × B)) ≤ 1 := by
  refine (pRank_top_le_of_coprime_ker hp (MonoidHom.fst A B) ?_).trans
    (pRank_top_le_one_of_isCyclic hp)
  rwa [card_ker_fst]

theorem not_dvd_card_of_pow_eq_one {N : Type*} [Group N] [Finite N] {ℓ q : ℕ} (hℓ : ℓ.Prime)
    (hq : q.Prime) (hne : ℓ ≠ q) (h : ∀ x : N, x ^ q = 1) : ¬ ℓ ∣ Nat.card N := by
  intro hdvd
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  have hℓq : ℓ ∣ q := hx ▸ orderOf_dvd_of_pow_eq_one (h x)
  exact hne ((Nat.prime_dvd_prime_iff_eq hℓ hq).1 hℓq)

theorem isCyclic_outer_of_ker_eq_inner {C Q : Type*} [Group C] [Group Q] [IsCyclic Q]
    (Θ : MulAut C →* Q) (hker : Θ.ker = inner C) : IsCyclic (Outer C) :=
  isCyclic_of_injective ((QuotientGroup.kerLift Θ).comp
      (QuotientGroup.quotientMulEquivOfEq hker.symm).toMonoidHom)
    ((QuotientGroup.kerLift_injective Θ).comp
      (QuotientGroup.quotientMulEquivOfEq hker.symm).injective)

theorem pRank_outer_le_one_of_ker_cube_quotient {C Q : Type*} [Group C] [Finite C] [Group Q]
    [Finite Q] [IsCyclic Q] (Θ : MulAut C →* Q) {L : Subgroup (MulAut C)} (hker : Θ.ker = L)
    (hle : inner C ≤ L) (hcube : ∀ a : L ⧸ (inner C).subgroupOf L, a ^ 3 = 1) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) : pRank ℓ (⊤ : Subgroup (Outer C)) ≤ 1 := by
  set Ψ : Outer C →* Q := QuotientGroup.lift (inner C) Θ (hker ▸ hle) with hΨ
  have hcube' : ∀ x ∈ Ψ.ker, x ^ 3 = 1 := fun x hx => by
    rw [hΨ, QuotientGroup.ker_lift, hker] at hx
    obtain ⟨α, hα, rfl⟩ := hx
    have h3 := hcube (QuotientGroup.mk ⟨α, hα⟩)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow] at h3
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h3
  have hnd : ¬ ℓ ∣ Nat.card Ψ.ker :=
    not_dvd_card_of_pow_eq_one hℓ Nat.prime_three hℓ3 fun x => Subtype.ext (hcube' x x.2)
  exact (pRank_top_le_of_coprime_ker hℓ Ψ hnd).trans (pRank_top_le_one_of_isCyclic hℓ)

theorem isCyclic_outer_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    [IsCyclic (Outer Y)] : IsCyclic (Outer X) :=
  isCyclic_of_injective (equivalence e).toMonoidHom (equivalence e).injective

end GL83.I713
