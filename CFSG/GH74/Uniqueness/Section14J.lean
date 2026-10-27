module

public import CFSG.GH74.Uniqueness.Bender.SuzukiSubgroup
public import CFSG.GH74.Uniqueness.Section14Lem43

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec14

variable {c : Ctx12 Z M} {n : ℕ} {U : Subgroup X}

theorem conj_U (h12 : Sec12Results Z M) (h : LData c n 2)
    (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X))) :
    ∀ a : X, orderOf a = 2 → a ∉ Z → ∃ g : X, g * a * g⁻¹ ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro a ha haZ
  obtain ⟨h1, -, h3⟩ := h12.l1211 c n 2 h
  have hnc : ¬ IsCentralInvolution a := fun hc => haZ ((h1 a ha).mp hc)
  obtain ⟨u, huD, hu2, hau⟩ := h3 a ha hnc
  obtain ⟨g₁, hg₁⟩ := isConj_iff.mp hau
  have hUD := U_sylow_D h hU
  have hcard : Nat.card (U.subgroupOf c.D) = 2 ^ (Nat.card c.D).factorization 2 := by
    rw [← hUD.card_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUD.le).toEquiv
  have hup : IsPGroup 2 (zpowers (⟨u, huD⟩ : ↥c.D)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hu2, pow_one]
  obtain ⟨d, hd⟩ := exists_conj_mem_of_card_eq hcard hup
  refine ⟨(d : X) * g₁, ?_⟩
  have e : (d : X) * g₁ * a * ((d : X) * g₁)⁻¹ = (d : X) * (g₁ * a * g₁⁻¹) * (d : X)⁻¹ := by group
  rw [e, hg₁]
  exact mem_subgroupOf.mp hd

theorem solvable_range
    (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M) (h : LData c n 2)
    (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X)))
    (hUsq : ∀ u ∈ U, u * u = 1) (f : ↥(centralizer (c.L : Set X)) →* ↥c.L) :
    Group.IsSolvable ↥f.range := by
  have := J_solvable h12 h131 h hU hUsq
  exact Group.isSolvable_of_surjective f.rangeRestrict_surjective

theorem big_U
    (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M) (h : LData c n 2)
    (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X)))
    (hUsq : ∀ u ∈ U, u * u = 1) :
    2 < Nat.card U → ∀ j ∈ centralizer (c.L : Set X), ∀ u ∈ U, j * u * j⁻¹ ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hU2
  obtain ⟨f, hf⟩ := exists_injective_J h12 h131 h
  set J' : Subgroup ↥c.L := f.range with hJ'
  set U' : Subgroup ↥c.L := (U.subgroupOf (centralizer (c.L : Set X))).map f with hU'
  have hU'J' : U' ≤ J' := map_le_range f _
  have hU'sq : ∀ x ∈ U', x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, show y * y = 1 from Subtype.ext (hUsq _ (mem_subgroupOf.mp hy)), map_one]
  have hU'card : Nat.card U' = Nat.card U := by
    rw [card_map_of_injective hf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU.le).toEquiv
  have hno : ∀ A : Subgroup ↥c.L, (∀ j ∈ J', ∀ a ∈ A, j * a * j⁻¹ ∈ A) →
      Odd (Nat.card A) → A = ⊥ := by
    intro A hA hAodd
    by_contra hA1
    have := h.bender.suzuki_odd_normal_card_le_two hA hAodd hA1 hU'J' hU'sq
    omega
  have hJsol := solvable_range h12 h131 h hU hUsq f
  have htop : (⊤ : Subgroup ↥J') ≠ ⊥ := by
    intro htop
    have h1 : Nat.card ↥J' = 1 := by
      rw [← card_top (G := ↥J'), htop, card_bot]
    have h2 : Nat.card U' ≤ Nat.card ↥J' := Subgroup.card_le_of_le hU'J'
    omega
  obtain ⟨B, hBn, hB1, hBab⟩ := Bender.exists_abelian_normal_of_solvable htop
  set B' : Subgroup ↥c.L := B.map J'.subtype with hB'
  have hB'n : ∀ j ∈ J', ∀ x ∈ B', j * x * j⁻¹ ∈ B' := by
    rintro j hj _ ⟨b, hb, rfl⟩
    exact ⟨⟨j, hj⟩ * b * ⟨j, hj⟩⁻¹, hBn.conj_mem b hb ⟨j, hj⟩, by simp⟩
  have hB'ab : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hBab a ha b hb)
  have hB'1 : B' ≠ ⊥ := by
    intro hbot
    apply hB1
    rw [eq_bot_iff]
    intro x hx
    have : (x : ↥c.L) ∈ B' := ⟨x, hx, rfl⟩
    rw [hbot, mem_bot] at this
    rw [mem_bot]
    exact Subtype.ext this
  have hB'2 : IsPGroup 2 B' := by
    have hprime : ∀ {p : ℕ}, p.Prime → p ∣ Nat.card B' → p = 2 := by
      intro p hp hpB
      by_contra hp2
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p ↥B'))
      set Bp : Subgroup ↥c.L := (P : Subgroup ↥B').map B'.subtype with hBp
      have hBpsyl : ABGLocalTools.IsSylowOf p Bp B' := ⟨P, rfl⟩
      have hBpn : ∀ g ∈ B', ∀ x ∈ Bp, g * x * g⁻¹ ∈ Bp := by
        intro g hg x hx
        have hxB := hBpsyl.le hx
        rw [hB'ab g hg x hxB, mul_inv_cancel_right]
        exact hx
      have hBpJ : ∀ j ∈ J', ∀ x ∈ Bp, j * x * j⁻¹ ∈ Bp := by
        intro j hj x hx
        set Bj : Subgroup ↥c.L := Bp.map (MulAut.conj j).toMonoidHom
        have hBjle : Bj ≤ B' := by
          rintro _ ⟨y, hy, rfl⟩
          exact hB'n j hj y (hBpsyl.le hy)
        have hBjsyl : ABGLocalTools.IsSylowOf p Bj B' := by
          apply ABGLocalTools.isSylowOf_of_card hBjle
          rw [← hBpsyl.card_eq]
          exact card_map_of_injective (MulAut.conj j).injective
        have heq := isSylowOf_eq_of_normal hBpsyl hBpn hBjsyl
        have : j * x * j⁻¹ ∈ Bj := ⟨x, hx, by simp⟩
        rwa [heq] at this
      have hBpodd : Odd (Nat.card Bp) := by
        obtain ⟨k, hk⟩ := hBpsyl.isPGroup.exists_card_eq
        rw [hk]
        exact Odd.pow (hp.eq_two_or_odd'.resolve_left hp2)
      have hBp1 : Bp ≠ ⊥ := by
        intro hbot
        have h1 := hBpsyl.card_eq
        rw [hbot, card_bot] at h1
        have : 0 < (Nat.card B').factorization p :=
          hp.factorization_pos_of_dvd Nat.card_pos.ne' hpB
        have := Nat.one_lt_pow this.ne' hp.one_lt
        omega
      exact hBp1 (hno Bp hBpJ hBpodd)
    rw [IsPGroup.iff_card]
    exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (fun hp hpd => hprime hp hpd)⟩
  obtain ⟨Q', hQ'⟩ := hB'2.exists_le_sylow
  obtain ⟨t', hc'⟩ := h.bender.exists_benderCore Q'
  have hNB : normalizer (B' : Set ↥c.L) ≤ Bender.borel (Q' : Subgroup ↥c.L) :=
    Bender.IsStronglyEmbedded.normalizer_le hc'.strong (hQ'.trans (Bender.le_borel _)) hB'2 hB'1
  have hJ'B : J' ≤ Bender.borel (Q' : Subgroup ↥c.L) :=
    (Bender.le_normalizer_of_forall_conj_mem hB'n).trans hNB
  have hU'Q' : U' ≤ (Q' : Subgroup ↥c.L) := by
    have hU'N : U' ≤ normalizer ((Q' : Subgroup ↥c.L) : Set ↥c.L) := hU'J'.trans hJ'B
    have hU'2 : IsPGroup 2 U' := Bender.isPGroup_two_of_sq_eq_one hU'sq
    have h1 : IsPGroup 2 ↥(U' ⊔ (Q' : Subgroup ↥c.L)) :=
      IsPGroup.to_sup_of_normal_right' hU'2 Q'.isPGroup' hU'N
    have h2 := Q'.3 h1 le_sup_right
    rw [← h2]
    exact le_sup_left
  have hU'syl : ABGLocalTools.IsSylowOf 2 U' J' := by
    apply ABGLocalTools.isSylowOf_of_card hU'J'
    rw [hU'card, hU.card_eq, show Nat.card ↥J' = Nat.card (centralizer (c.L : Set X)) from
      (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm]
  have hW : J' ⊓ (Q' : Subgroup ↥c.L) = U' :=
    hU'syl.eq_of_le (le_inf hU'J' hU'Q') inf_le_left (Q'.isPGroup'.to_le inf_le_right)
  have hU'n : ∀ j ∈ J', ∀ u ∈ U', j * u * j⁻¹ ∈ U' := by
    intro j hj u hu
    rw [← hW] at hu ⊢
    obtain ⟨hu1, hu2⟩ := mem_inf.mp hu
    refine mem_inf.mpr ⟨J'.mul_mem (J'.mul_mem hj hu1) (J'.inv_mem hj), ?_⟩
    exact (mem_normalizer_iff.mp (hJ'B hj) u).mp hu2
  intro j hj u hu
  have h1 := hU'n (f ⟨j, hj⟩) ⟨_, rfl⟩ (f ⟨u, hU.le hu⟩) ⟨⟨u, hU.le hu⟩, mem_subgroupOf.mpr hu, rfl⟩
  rw [← map_inv, ← map_mul, ← map_mul] at h1
  obtain ⟨y, hy, hye⟩ := h1
  have := hf hye
  have hy' : y ∈ U.subgroupOf (centralizer (c.L : Set X)) := hy
  rw [this] at hy'
  have h2 := mem_subgroupOf.mp hy'
  simpa using h2

theorem card_J_14
    (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M) (h : LData c n 2)
    (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X)))
    (hUsq : ∀ u ∈ U, u * u = 1) :
    n = 3 → 7 ∣ Nat.card (centralizer (c.L : Set X)) → Nat.card U = 2 →
      Nat.card (centralizer (c.L : Set X)) = 14 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hn3 h7 hU2
  obtain ⟨f, hf⟩ := exists_injective_J h12 h131 h
  have : Group.IsSolvable ↥f.range := solvable_range h12 h131 h hU hUsq f
  have hcard : Nat.card f.range = Nat.card (centralizer (c.L : Set X)) :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have hJ0 : Nat.card (centralizer (c.L : Set X)) ≠ 0 := Nat.card_pos.ne'
  have hv2 : (Nat.card (centralizer (c.L : Set X))).factorization 2 = 1 := by
    have := hU.card_eq
    rw [hU2] at this
    have h2 : (2 : ℕ) ^ 1 = 2 ^ (Nat.card (centralizer (c.L : Set X))).factorization 2 := by
      rw [pow_one]; exact this
    exact (Nat.pow_right_injective le_rfl h2).symm
  have h2 : 2 ∣ Nat.card f.range := by
    rw [hcard]
    exact (Nat.prime_two.dvd_iff_one_le_factorization hJ0).mpr (by omega)
  have h4 : ¬ 4 ∣ Nat.card f.range := by
    rw [hcard]
    intro h4
    have : 2 ≤ (Nat.card (centralizer (c.L : Set X))).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hJ0).mp
        (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact h4)
    omega
  subst hn3
  have := h.bender.suzuki_eight_solvable_card (J := f.range) (hcard ▸ h7) h2 h4
  rw [hcard] at this
  exact this

end Sec14

end CFSG.GH74.Uniqueness
