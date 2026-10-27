module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

section Equiv

variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G'] {p : ℕ} [hp : Fact p.Prime]

theorem pRank_centralizer_of_mulEquiv (e : G ≃* G') (y : G) :
    CFSG.Open.pRank p (centralizer ({e y} : Set G')) ≤
      CFSG.Open.pRank p (centralizer ({y} : Set G)) := by
  refine (CFSG.SectionRank.pRank_le_map hp.out.one_lt e.symm.toMonoidHom e.symm.injective _).trans
    (CFSG.SectionRank.pRank_mono hp.out.one_lt ?_)
  rintro _ ⟨g, hg, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply e.injective
  simpa using hg

theorem isMulCommutative_of_map_injective (f : G →* G') (hf : Function.Injective f)
    {P : Subgroup G} (h : IsMulCommutative (P.map f)) : IsMulCommutative P :=
  .of_setLike_mul_comm fun a ha b hb => hf (by
    simpa using setLike_mul_comm (Subgroup.mem_map_of_mem f ha) (Subgroup.mem_map_of_mem f hb))

end Equiv

section Kernel

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K]
  [Finite K]

theorem pRank_le_pRank_inf_ker_add_one (φ : G →* Kˣ) (C : Subgroup G) :
    CFSG.Open.pRank p C ≤ CFSG.Open.pRank p (C ⊓ φ.ker) + 1 := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  obtain ⟨E, hEC, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1 C
  set m := CFSG.Open.pRank p C with hm
  let ψ : E →* Kˣ := φ.comp E.subtype
  have hmul := Subgroup.card_ker_mul_card_range ψ
  haveI := Fintype.ofFinite Kˣ
  have hr : Nat.card ψ.range ≤ p := by
    have h1 : Nat.card ψ.range ≤ Nat.card {a : Kˣ // a ^ p = 1} := by
      refine Nat.card_le_card_of_injective (fun x => ⟨x.1, ?_⟩) ?_
      · obtain ⟨z, hz⟩ := x.2
        rw [← hz]
        change ψ z ^ p = 1
        rw [← map_pow, show z ^ p = 1 from Subtype.ext (hE.2 z z.2), map_one]
      · intro a b hab
        exact Subtype.ext (by simpa using hab)
    have h2 : Nat.card {a : Kˣ // a ^ p = 1} =
        (Finset.univ.filter fun a : Kˣ => a ^ p = 1).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact h1.trans (h2 ▸ IsCyclic.card_pow_eq_one_le hp.out.pos)
  have hr0 : 0 < Nat.card ψ.range := Nat.card_pos
  let F : Subgroup G := ψ.ker.map E.subtype
  have hFE : F ≤ E := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hFker : F ≤ C ⊓ φ.ker := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hEC x.2, hx⟩
  have hFcard : Nat.card F = Nat.card ψ.ker := Subgroup.card_map_of_injective E.subtype_injective
  obtain ⟨j, hj⟩ := exists_card_eq_pow_of_isElemAbelian (crossRank_isElemAbelian_of_le hE hFE)
  have hjle : j ≤ CFSG.Open.pRank p (C ⊓ φ.ker) :=
    CFSG.SectionRank.le_pRank hp1 hFker (crossRank_isElemAbelian_of_le hE hFE) hj
  have hprod : p ^ j * Nat.card ψ.range = p ^ m := by
    rw [← hj, hFcard, hmul, hEcard]
  by_contra hlt
  have hlt' : j + 1 < m := by omega
  have h1 : p ^ (j + 2) ≤ p ^ m := Nat.pow_le_pow_right hp.out.pos (by omega)
  have h2 : p ^ j * Nat.card ψ.range ≤ p ^ j * p := Nat.mul_le_mul_left _ hr
  have h3 : p ^ (j + 2) = p ^ j * p * p := by ring
  have hpj : 0 < p ^ j := pow_pos hp.out.pos j
  have h4 : p ^ j * p < p ^ j * p * p := by
    have := hp.out.two_le
    nlinarith [Nat.mul_pos hpj hp.out.pos]
  omega

end Kernel

section Quotient

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]

theorem exists_pow_eq_one_lift (N : Subgroup H) [N.Normal] (hN : ¬ p ∣ Nat.card N)
    (y : H ⧸ N) (hy : y ^ p = 1) : ∃ z : H, z ^ p = 1 ∧ (z : H ⧸ N) = y := by
  obtain ⟨z₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hzN : z₀ ^ p ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hy
  have hcop : Nat.Coprime (Nat.card N) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hN).symm
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.out.one_lt
  refine ⟨z₀ ^ (Nat.card N * s), ?_, ?_⟩
  · have h1 : ((⟨z₀ ^ p, hzN⟩ : N)) ^ Nat.card N = 1 := pow_card_eq_one'
    have h2 : (z₀ ^ p) ^ Nat.card N = 1 := congrArg Subtype.val h1
    have h3 : (z₀ ^ (Nat.card N * s)) ^ p = ((z₀ ^ p) ^ Nat.card N) ^ s := by
      rw [← pow_mul, ← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [h3, h2, one_pow]
  · rw [QuotientGroup.mk_pow, ← Nat.div_add_mod (Nat.card N * s) p, hs, pow_add, pow_mul, hy,
      one_pow, one_mul, pow_one]

theorem le_pRank_centralizer_quotient (N : Subgroup H) [N.Normal] (hN : ¬ p ∣ Nat.card N)
    {y : H} {F : Subgroup H} (hF : IsElemAbelian p F) {m : ℕ} (hFm : Nat.card F = p ^ m)
    (hFy : ∀ f ∈ F, f * y = y * f) :
    m ≤ CFSG.Open.pRank p (centralizer ({(y : H ⧸ N)} : Set (H ⧸ N))) := by
  have hcop : Nat.Coprime (Nat.card F) (Nat.card N) := by
    rw [hFm]
    exact Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hN)
  have hdisj : Disjoint F N := Subgroup.disjoint_of_coprime_natCard hcop
  let f : F →* H ⧸ N := (QuotientGroup.mk' N).comp F.subtype
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : (a : H)⁻¹ * (b : H) ∈ N := by
      rw [← QuotientGroup.eq]
      exact hab
    have h2 : (a : H)⁻¹ * (b : H) ∈ F := F.mul_mem (F.inv_mem a.2) b.2
    have h3 : (a : H)⁻¹ * (b : H) = 1 := by
      have := (disjoint_iff.1 hdisj)
      have h4 : (a : H)⁻¹ * (b : H) ∈ F ⊓ N := ⟨h2, h1⟩
      rw [this] at h4
      exact h4
    exact Subtype.ext (inv_mul_eq_one.1 h3)
  have hFc := hF.1
  refine CFSG.SectionRank.le_pRank_of_injective hp.out.one_lt
    (fun a b => Subtype.ext (setLike_mul_comm a.2 b.2)) (fun a => Subtype.ext (hF.2 a a.2))
    hFm f hf ?_
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  change (QuotientGroup.mk' N) (a : H) * (y : H ⧸ N) = (y : H ⧸ N) * (QuotientGroup.mk' N) (a : H)
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hFy a a.2]

end Quotient

section Order

variable {K : Type*} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]

theorem exists_order_data (hpK : ¬ p ∣ Nat.card K) :
    ∃ e : ℕ, 0 < e ∧ ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j := by
  set q := Nat.card K with hq
  have hq0 : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hpK
  refine ⟨orderOf (q : ZMod p), ?_, fun j => ?_⟩
  · refine orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p - 1, ?_, ?_⟩)
    · have := hp.out.two_le
      omega
    · exact ZMod.pow_card_sub_one_eq_one hq0
  · have hq1 : 1 ≤ q ^ j := Nat.one_le_pow _ _ Finite.card_pos
    rw [orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq1, Nat.cast_pow,
      Nat.cast_one, sub_eq_zero]

end Order

end CFSG.LocalAnalysis.RankFourTheoremC
