module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

section Congr

variable {K L : Type*} [Group K] [Group L] {p : ℕ}

theorem isElemAbelian_map_congr (e : K ≃* L) {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
  CFSG.SectionRank.isElemAbelian_map hE _

theorem card_map_congr (e : K ≃* L) (E : Subgroup (MulAut K)) :
    Nat.card (E.map (MulAut.congr e).toMonoidHom) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.congr e).injective

theorem closure_fixed_eq_top_of_map_congr (e : K ≃* L) (E : Subgroup (MulAut K))
    (h : Subgroup.closure
      {l : L | ∃ x ∈ E.map (MulAut.congr e).toMonoidHom, x ≠ 1 ∧ x l = l} = ⊤) :
    Subgroup.closure {k : K | ∃ x ∈ E, x ≠ 1 ∧ x k = k} = ⊤ := by
  rw [eq_top_iff]
  intro k _
  have hle : (⊤ : Subgroup L) ≤
      (Subgroup.closure {k : K | ∃ x ∈ E, x ≠ 1 ∧ x k = k}).map e.toMonoidHom := by
    rw [← h, Subgroup.closure_le]
    rintro l ⟨x, hx, hx1, hxl⟩
    obtain ⟨ε, hε, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨e.symm l, Subgroup.subset_closure ⟨ε, hε, ?_, ?_⟩, by simp⟩
    · rintro rfl
      exact hx1 (map_one _)
    · have h1 : (MulAut.congr e).toMonoidHom ε l = e (ε (e.symm l)) := by
        simp [MulAut.congr_apply]
      rw [h1] at hxl
      exact e.injective (by simpa using hxl)
  obtain ⟨k', hk', hkk⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_top (e k)))
  exact e.injective hkk ▸ hk'

theorem card_outer_eq_of_mulEquiv (e : K ≃* L) : Nat.card (Outer K) = Nat.card (Outer L) :=
  Nat.card_congr (equivalence e).toEquiv

theorem le_range_conj_of_not_dvd_card_outer (hp : p.Prime) (hout : ¬ p ∣ Nat.card (Outer K))
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) :
    E ≤ (MulAut.conj : K →* MulAut K).range := by
  intro x hx
  have hcop : p.Coprime (Nat.card (Outer K)) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hout
  have h1 : QuotientGroup.mk' (inner K) x = 1 :=
    (pow_eq_one_iff_of_coprime hcop).mp
      ⟨by rw [← map_pow, hE.2 x hx, map_one], pow_card_eq_one'⟩
  exact (QuotientGroup.eq_one_iff (N := inner K) x).mp h1

end Congr

section Rank

variable {G : Type*} [Group G] [Finite G]

theorem two_le_openPRank_of_commuting {p : ℕ} (hp : p.Prime) {a b : G} (ha : orderOf a = p)
    (hb : b ^ p = 1) (hab : a * b = b * a) (hne : b ∉ Subgroup.zpowers a) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hap : a ^ p = 1 := ha ▸ pow_orderOf_eq_one a
  set A : Subgroup G := Subgroup.closure ({a, b} : Set G) with hA
  have hcomm : ({a, b} : Set G).Pairwise Commute := by
    intro u hu v hv _
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    exacts [Commute.refl _, hab, hab.symm, Commute.refl _]
  have hmul := Subgroup.isMulCommutative_closure hcomm
  have hel : IsElemAbelian p A := by
    refine ⟨hmul, fun g hg => ?_⟩
    induction hg using Subgroup.closure_induction with
    | mem u hu =>
      rcases hu with rfl | rfl
      exacts [hap, hb]
    | one => exact one_pow p
    | mul u v hu hv ihu ihv =>
      have huv : Commute u v :=
        congrArg Subtype.val (hmul.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
      rw [huv.mul_pow, ihu, ihv, one_mul]
    | inv u hu ihu => rw [inv_pow, ihu, inv_one]
  have hpA : IsPGroup p A := fun w => ⟨1, Subtype.ext (by simpa using hel.2 w w.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hpA
  have hle : Subgroup.zpowers a ≤ A :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hdvd : p ∣ Nat.card A := by
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, ha] at this
  have hne' : Nat.card A ≠ p := by
    intro h
    have heq : Subgroup.zpowers a = A :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, ha, h])
    exact hne (heq ▸ Subgroup.subset_closure (by simp))
  have hm2 : 2 ≤ m := by
    rcases m with _ | _ | m
    · rw [pow_zero] at hm
      rw [hm] at hdvd
      exact absurd (Nat.le_of_dvd one_pos hdvd) (by have := hp.two_le; omega)
    · rw [pow_one] at hm
      exact absurd hm hne'
    · omega
  exact hm2.trans (CFSG.SectionRank.le_pRank hp.one_lt le_top hel hm)

end Rank

end CFSG.AGLEmbedding
