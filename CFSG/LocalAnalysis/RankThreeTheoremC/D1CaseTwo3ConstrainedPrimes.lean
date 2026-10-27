module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedRank
public import CFSG.LocalAnalysis.AGLEmbedding.Extremal
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem d1CtPrimeDvdMulAut {V : Type*} [Group V] [Finite V] {p : ℕ} (hp : p.Prime)
    (hcomm : ∀ a b : V, a * b = b * a) (hpow : ∀ a : V, a ^ p = 1)
    (hcard : Nat.card V = 1 ∨ Nat.card V = p ^ 2) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card (MulAut V)) : q = p ∨ q ∣ p ^ 2 - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn, hV⟩ : ∃ n : ℕ, (n = 0 ∨ n = 2) ∧ Nat.card V = p ^ n := by
    rcases hcard with h | h
    · exact ⟨0, Or.inl rfl, by simpa using h⟩
    · exact ⟨2, Or.inr rfl, h⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hV
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
    CFSG.SectionRank.Ccomm.card_GL_zmod] at hdvd
  rcases hn with rfl | rfl
  · rw [Fin.prod_univ_zero] at hdvd
    exact absurd (Nat.dvd_one.mp hdvd) hq.ne_one
  · rw [Fin.prod_univ_two] at hdvd
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
    · exact Or.inr h
    · rw [sq, ← Nat.mul_sub_one] at h
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq hp).mp h)
      · exact Or.inr (h.trans (Nat.sub_one_dvd_pow_sub_one p 2))

theorem d1CtPrimeDvdMulAutCyclic {Z : Type*} [Group Z] [Finite Z] [IsCyclic Z] {p : ℕ}
    (hp : p.Prime) (hZ : IsPGroup p Z) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card (MulAut Z)) : q = p ∨ q ∣ p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := hZ.exists_card_eq
  rw [IsCyclic.card_mulAut, hm] at hdvd
  rcases m with _ | m
  · rw [pow_zero, Nat.totient_one] at hdvd
    exact absurd (Nat.dvd_one.mp hdvd) hq.ne_one
  · rw [Nat.totient_prime_pow_succ hp] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h))
    · exact Or.inr h

theorem d1CtPrimeDvdOfCritical {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (Q : Subgroup X) [Q.Normal] (hQ : IsPGroup p Q)
    (hQc : Subgroup.centralizer (Q : Set X) ≤ Q) (C : Subgroup Q) (hC : C.Characteristic)
    (hfrat : (frattini C).map C.subtype ≤ (Subgroup.center C).map C.subtype)
    (hcent : Subgroup.centralizer (C : Set Q) = (Subgroup.center C).map C.subtype)
    (hcyc : IsCyclic (Subgroup.center C))
    (hrank : ∀ N : Subgroup X, N.Normal → IsPGroup p N → Open.pRank p N ≤ 2)
    {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Nat.card X) : q = p ∨ q ∣ p ^ 2 - 1 := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hCxn : (C.map Q.subtype).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact top_unique ((Subgroup.normalizer_eq_top Q).symm.le.trans
      (normalizer_le_normalizer_characteristic C hC))
  have hZx := map_map_center_eq_inf_centralizer C
  have hZxn : (((Subgroup.center C).map C.subtype).map Q.subtype).Normal := by
    rw [hZx]
    infer_instance
  have hZC : ((Subgroup.center C).map C.subtype).map Q.subtype ≤ C.map Q.subtype :=
    hZx.le.trans inf_le_left
  have hCQ : C.map Q.subtype ≤ Q := Subgroup.map_subtype_le C
  have hZp : IsPGroup p (((Subgroup.center C).map C.subtype).map Q.subtype) :=
    hQ.to_le (hZC.trans hCQ)
  have hZcyc : IsCyclic (((Subgroup.center C).map C.subtype).map Q.subtype) :=
    (((Subgroup.center C).equivMapOfInjective C.subtype C.subtype_injective).trans
      (((Subgroup.center C).map C.subtype).equivMapOfInjective Q.subtype
        Q.subtype_injective)).isCyclic.mp hcyc
  have hQZ : Q ⊓ Subgroup.centralizer ((C.map Q.subtype : Subgroup X) : Set X) ≤
      ((Subgroup.center C).map C.subtype).map Q.subtype := by
    rintro x ⟨hxQ, hxc⟩
    have hmem : (⟨x, hxQ⟩ : Q) ∈ Subgroup.centralizer (C : Set Q) :=
      Subgroup.mem_centralizer_iff.mpr fun c hc =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxc) _ ⟨c, hc, rfl⟩)
    rw [hcent] at hmem
    exact ⟨_, hmem, rfl⟩
  have hK := isPGroup_centralizer_of_selfCentralizing hp hQ hQc hZC (hZC.trans hCQ) hQZ
  have hfratC : frattini C ≤ Subgroup.center C :=
    (Subgroup.map_le_map_iff_of_injective C.subtype_injective).mp hfrat
  have hCp : IsPGroup p C := hQ.to_subgroup C
  have hcommC : commutator C ≤ Subgroup.center C :=
    (pGroup_commutator_le_frattini p hCp).trans hfratC
  have hpowC : ∀ c : C, c ^ p ∈ Subgroup.center C :=
    fun c => hfratC (pGroup_pow_mem_frattini p hCp c)
  have hCrank : Open.pRank p (⊤ : Subgroup C) ≤ 2 := by
    rw [← pRank_map_of_injective p hp (Q.subtype.comp C.subtype)
      (Q.subtype_injective.comp C.subtype_injective), ← Subgroup.map_map,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hrank _ hCxn (hQ.to_le hCQ)
  have hVcard := card_center_quotient_eq_one_or_sq hp2 hCp hcyc hcommC hpowC hCrank
  let : MulDistribMulAction X Q := MulDistribMulAction.compHom Q (MulAut.conjNormal (H := Q))
  let := characteristic_subgroup_mulDistribMulAction (acting := X) C
  let := characteristic_quotient_mulDistribMulAction (acting := X) (Subgroup.center C)
  have hρ : ∀ x ∈ (MulDistribMulAction.toMulAut X (C ⧸ Subgroup.center C)).ker,
      ∀ c ∈ C.map Q.subtype, c⁻¹ * (x * c * x⁻¹) ∈
        ((Subgroup.center C).map C.subtype).map Q.subtype := by
    rintro x hx _ ⟨q, hq, rfl⟩
    have hfix := congrArg (fun σ : MulAut (C ⧸ Subgroup.center C) =>
      σ (QuotientGroup.mk (⟨q, hq⟩ : C))) (MonoidHom.mem_ker.mp hx)
    change (QuotientGroup.mk (x • (⟨q, hq⟩ : C)) : C ⧸ Subgroup.center C) =
      QuotientGroup.mk ⟨q, hq⟩ at hfix
    exact ⟨_, ⟨_, QuotientGroup.eq.mp hfix.symm, rfl⟩, rfl⟩
  have hL := isPGroup_inf_centralizer_of_displacement hp hK hZp hρ
  let : IsMulCommutative (C ⧸ Subgroup.center C) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommC
  let : CommGroup (C ⧸ Subgroup.center C) := IsMulCommutative.instCommGroup
  have hVcomm : ∀ a b : C ⧸ Subgroup.center C, a * b = b * a := fun a b => mul_comm a b
  have hVpow : ∀ v : C ⧸ Subgroup.center C, v ^ p = 1 := by
    intro v
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center C) v
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hpowC c)
  set Z : Subgroup X := ((Subgroup.center C).map C.subtype).map Q.subtype
  set ρ : X →* MulAut (C ⧸ Subgroup.center C) :=
    MulDistribMulAction.toMulAut X (C ⧸ Subgroup.center C)
  let ψ : X →* MulAut Z := MulAut.conjNormal
  have hψ : ψ.ker ≤ Subgroup.centralizer (Z : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h := congrArg (fun σ : MulAut Z => ((σ ⟨z, hz⟩ : Z) : X)) (MonoidHom.mem_ker.mp hx)
    simp only [ψ, MulAut.conjNormal_apply, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hker : IsPGroup p (ρ.prod ψ).ker := by
    rw [MonoidHom.ker_prod]
    exact hL.to_le (inf_le_inf_left _ hψ)
  obtain ⟨a, ha⟩ := hker.exists_card_eq
  rw [← Subgroup.card_ker_mul_card_range (ρ.prod ψ), ha] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h))
  · have h2 : q ∣ Nat.card (MulAut (C ⧸ Subgroup.center C)) * Nat.card (MulAut Z) := by
      rw [← Nat.card_prod]
      exact h.trans (Subgroup.card_subgroup_dvd_card _)
    rcases (Nat.Prime.dvd_mul hq).mp h2 with h3 | h3
    · exact d1CtPrimeDvdMulAut hp hVcomm hVpow hVcard hq h3
    · rcases d1CtPrimeDvdMulAutCyclic hp hZp hq h3 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr (h4.trans (Nat.sub_one_dvd_pow_sub_one p 2))

theorem _root_.CFSG.AGLEmbedding.D1Extremal.prime_dvd_card_of_hasPrimeConstraint
    {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1Extremal p P M H R) (hcon : HasPrimeConstraint (G := H) p) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card (H ⧸ primeComplementCore (G := H) p)) : q = p ∨ q ∣ p ^ 2 - 1 := by
  have : ((GLBPrimeCore p H).subgroupOf H).Normal := glbPrimeCore_normal p H
  obtain ⟨Q, hQn, hQp, hQc⟩ := exists_selfCentralizing_of_hasPrimeConstraint H hcon
  have : Q.Normal := hQn
  obtain ⟨C, hC, hfrat, -, hcent, hcyc, -⟩ :=
    escaping_primeCore_quotient_normal_pGroup_has_cyclic_critical_quotient p h.prime h.ne_two P
      h.sylow_le h.weakCore_le h.three_le_pRank_inf h.not_le Q hQp
  let e : (H ⧸ (GLBPrimeCore p H).subgroupOf H) ≃* (H ⧸ primeComplementCore (G := H) p) :=
    QuotientGroup.quotientMulEquivOfEq (glbPrimeCore_subgroupOf p H)
  exact d1CtPrimeDvdOfCritical h.prime h.ne_two Q hQp hQc C hC hfrat hcent hcyc
    (fun N _ hNp => escaping_rank_three_primeCore_quotient_normal_primeSubgroup_rank_le_two p
      h.prime P h.sylow_le h.weakCore_le h.three_le_pRank_inf h.not_le N hNp) hq
    (by rwa [Nat.card_congr e.toEquiv])

end CFSG.LocalAnalysis.RankThreeTheoremC
