module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThree
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

theorem IsExtNotation.of_mulEquiv {PA PB : ∀ (V : Type) [Group V], Prop}
    (hPA : ∀ (V V' : Type) [Group V] [Group V'], (V ≃* V') → PA V → PA V')
    (hPB : ∀ (V V' : Type) [Group V] [Group V'], (V ≃* V') → PB V → PB V')
    {X X' : Type} [Group X] [Group X'] (e : X ≃* X') (h : IsExtNotation PA PB X) :
    IsExtNotation PA PB X' := by
  obtain ⟨N, hN, hB, hA, hns⟩ := h
  let N' : Subgroup X' := N.map e.toMonoidHom
  have hN' : N'.Normal := hN.map e.toMonoidHom e.surjective
  refine ⟨N', hN', ?_, ?_, ?_⟩
  · exact hPB ↥N ↥N' (N.equivMapOfInjective e.toMonoidHom e.injective) hB
  · haveI : N.Normal := hN
    haveI : N'.Normal := hN'
    exact hPA (X ⧸ N) (X' ⧸ N') (QuotientGroup.congr N N' e rfl) hA
  · intro hcompl
    obtain ⟨H', hH', hinf, hsup⟩ := hcompl
    apply hns
    let H : Subgroup X := H'.comap e.toMonoidHom
    have hH : H.Normal := hH'.comap e.toMonoidHom
    have hmapN : e.mapSubgroup N = N' := rfl
    have hmapH : e.mapSubgroup H = H' := by
      show Subgroup.map e.toMonoidHom (Subgroup.comap e.toMonoidHom H') = H'
      exact Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective H'
    refine ⟨H, hH, ?_, ?_⟩
    · apply e.mapSubgroup.injective
      rw [OrderIso.map_inf, OrderIso.map_bot, hmapN, hmapH, hinf]
    · apply e.mapSubgroup.injective
      rw [OrderIso.map_sup, OrderIso.map_top, hmapN, hmapH, hsup]

theorem IsQ8D8Type.of_mulEquiv {B B' : Type} [Group B] [Group B'] (e : B ≃* B')
    (h : IsQ8D8Type B) : IsQ8D8Type B' := by
  obtain ⟨Q, E, hQ, hE, hcomm, hsup, hcard⟩ := h
  refine ⟨Q.map e.toMonoidHom, E.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(Q.equivMapOfInjective e.toMonoidHom e.injective).symm.trans hQ.some⟩
  · exact ⟨(E.equivMapOfInjective e.toMonoidHom e.injective).symm.trans hE.some⟩
  · intro q hq r hr
    obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hq
    obtain ⟨r₀, hr₀, rfl⟩ := Subgroup.mem_map.mp hr
    rw [← map_mul, ← map_mul, hcomm q₀ hq₀ r₀ hr₀]
  · rw [← Subgroup.map_sup, hsup,
      Subgroup.map_top_of_surjective (f := e.toMonoidHom) e.surjective]
  · rw [← Subgroup.map_inf Q E e.toMonoidHom e.injective,
      Subgroup.card_map_of_injective e.injective, hcard]

theorem SixThreeOneList.of_mulEquiv {p : ℕ} {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : SixThreeOneList p Y) : SixThreeOneList p Y' := by
  unfold SixThreeOneList at h ⊢
  rcases h with h | h | h | h
  · rcases h with h | h | h | h
    · left; left; exact ⟨e.symm.trans h.some⟩
    · left; right; left; exact ⟨e.symm.trans h.some⟩
    · left; right; right; left; exact ⟨e.symm.trans h.some⟩
    · left; right; right; right; exact (Nat.card_congr e.toEquiv).symm.trans h
  · obtain ⟨hp, h⟩ := h
    refine Or.inr (Or.inl ⟨hp, IsExtNotation.of_mulEquiv ?_ ?_ e h⟩)
    · intro V V' _ _ f ⟨g⟩
      exact ⟨f.symm.trans g⟩
    · intro V V' _ _ f hf
      exact (Nat.card_congr f.toEquiv).symm.trans hf
  · obtain ⟨hp, h⟩ := h
    refine Or.inr (Or.inr (Or.inl ⟨hp, ?_⟩))
    rcases h with h | h | h
    · refine Or.inl (IsExtNotation.of_mulEquiv ?_ ?_ e h)
      · intro V V' _ _ f ⟨g⟩
        exact ⟨f.symm.trans g⟩
      · intro V V' _ _ f hf
        exact (Nat.card_congr f.toEquiv).symm.trans hf
    · refine Or.inr (Or.inl (IsExtNotation.of_mulEquiv ?_ ?_ e h))
      · intro V V' _ _ f ⟨g⟩
        exact ⟨f.symm.trans g⟩
      · intro V V' _ _ f hf
        exact IsQ8D8Type.of_mulEquiv f hf
    · refine Or.inr (Or.inr (IsExtNotation.of_mulEquiv ?_ ?_ e h))
      · intro V V' _ _ f hf
        exact (Nat.card_congr f.toEquiv).symm.trans hf
      · intro V V' _ _ f hf
        exact IsQ8D8Type.of_mulEquiv f hf
  · obtain ⟨hp, h⟩ := h
    refine Or.inr (Or.inr (Or.inr ⟨hp, ?_⟩))
    rcases h with h | h | h | h
    · exact Or.inl ⟨e.symm.trans h.some⟩
    · refine Or.inr (Or.inl (IsExtNotation.of_mulEquiv ?_ ?_ e h))
      · intro V V' _ _ f ⟨g⟩
        exact ⟨f.symm.trans g⟩
      · intro V V' _ _ f hf
        exact IsQ8D8Type.of_mulEquiv f hf
    · refine Or.inr (Or.inr (Or.inl (IsExtNotation.of_mulEquiv ?_ ?_ e h)))
      · intro V V' _ _ f hf
        exact (Nat.card_congr f.toEquiv).symm.trans hf
      · intro V V' _ _ f hf
        exact (Nat.card_congr f.toEquiv).symm.trans hf
    · obtain ⟨W, hW, ⟨f⟩⟩ := h
      exact Or.inr (Or.inr (Or.inr ⟨W, hW, ⟨e.symm.trans f⟩⟩))

theorem eq_oPPrimeHull_of_not_sq_dvd {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {N : Subgroup X} [N.Normal] (hNO : N ≤ oPPrimeHull p ⊤) (hx : ∃ x ∈ N, orderOf x = p)
    (hsq : ¬ p ^ 2 ∣ Nat.card ↥(oPPrimeHull p (⊤ : Subgroup X))) :
    N = oPPrimeHull p ⊤ := by
  have hN : N.Normal := inferInstance
  apply le_antisymm hNO
  change Subgroup.closure {x : X | x ∈ (⊤ : Subgroup X) ∧ ∃ k : ℕ, orderOf x = p ^ k} ≤ N
  rw [Subgroup.closure_le]
  have hSylow_dvd : ∀ S : Sylow p X, Nat.card ↥(S : Subgroup X) ∣ p := by
    intro S
    have hSO : (S : Subgroup X) ≤ oPPrimeHull p ⊤ := by
      intro s hs
      obtain ⟨m, hm⟩ := S.isPGroup'.exists_orderOf_eq_pow (⟨s, hs⟩ : ↥(S : Subgroup X))
      exact Subgroup.subset_closure
        ⟨trivial, ⟨m, (Subgroup.orderOf_coe (⟨s, hs⟩ : ↥(S : Subgroup X))).trans hm⟩⟩
    have hdiv : Nat.card ↥(S : Subgroup X) ∣ Nat.card ↥(oPPrimeHull p (⊤ : Subgroup X)) :=
      Subgroup.card_dvd_of_le hSO
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp S.isPGroup'
    rw [hm] at hdiv
    have hm_le : m ≤ 1 := by
      by_contra h
      push Not at h
      exact hsq (dvd_trans (pow_dvd_pow p h) hdiv)
    rw [hm]
    interval_cases m <;> simp
  obtain ⟨x, hxN, hxord⟩ := hx
  have hzx_p : IsPGroup p ↥(Subgroup.zpowers x) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, hxord, pow_one]⟩
  obtain ⟨S₀, hS₀⟩ := hzx_p.exists_le_sylow
  have hS₀dvd : Nat.card ↥(S₀ : Subgroup X) ∣ p := hSylow_dvd S₀
  have hzx_dvd : Nat.card ↥(Subgroup.zpowers x) ∣ Nat.card ↥(S₀ : Subgroup X) :=
    Subgroup.card_dvd_of_le hS₀
  have hcard_eq : Nat.card ↥(S₀ : Subgroup X) = p := by
    refine Nat.dvd_antisymm hS₀dvd ?_
    rwa [Nat.card_zpowers, hxord] at hzx_dvd
  have hS₀_le_N : (S₀ : Subgroup X) ≤ N := by
    have hzxN : Subgroup.zpowers x ≤ N := Subgroup.zpowers_le.mpr hxN
    have hEq : (S₀ : Subgroup X) = Subgroup.zpowers x := by
      refine (Subgroup.eq_of_le_of_card_ge hS₀ ?_).symm
      rw [hcard_eq, Nat.card_zpowers, hxord]
    rw [hEq]
    exact hzxN
  rintro y ⟨-, k, hk⟩
  have hzy_p : IsPGroup p ↥(Subgroup.zpowers y) := by
    rw [IsPGroup.iff_card]
    exact ⟨k, by rw [Nat.card_zpowers, hk]⟩
  obtain ⟨S, hS⟩ := hzy_p.exists_le_sylow
  have hyS : y ∈ (S : Subgroup X) := hS (Subgroup.mem_zpowers y)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S₀ S
  have hS_le_N : (S : Subgroup X) ≤ N := by
    rw [← hg, Sylow.coe_subgroup_smul]
    intro z hz
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hz
    have hzN : (MulAut.conj g)⁻¹ • z ∈ N := hS₀_le_N hz
    have hz_eq : z = g * ((MulAut.conj g)⁻¹ • z) * g⁻¹ := by
      rw [MulAut.smul_def, MulAut.conj_inv_apply]
      group
    rw [hz_eq]
    exact hN.conj_mem _ hzN g
  exact hS_le_N hyS

theorem eq_of_normal_of_isQuasisimple {X : Type*} [Group X] {O N : Subgroup X} [N.Normal]
    (hNO : N ≤ O) (hq : CFSG.IsQuasisimple ↥O) (hx : ∃ x ∈ N, ∃ y ∈ O, x * y ≠ y * x) :
    N = O := by
  haveI : (N.subgroupOf O).Normal := inferInstance
  have hq' : CFSG.Open.IsQuasisimple ↥O := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq'
    (N.subgroupOf O) with hcent | htop
  · exfalso
    obtain ⟨x, hxN, y, hyO, hxy⟩ := hx
    have hxM : (⟨x, hNO hxN⟩ : ↥O) ∈ N.subgroupOf O := Subgroup.mem_subgroupOf.mpr hxN
    have hcomm := Subgroup.mem_center_iff.mp (hcent hxM) (⟨y, hyO⟩ : ↥O)
    have hcoe := congrArg (fun z : ↥O => (z : X)) hcomm
    exact hxy hcoe.symm
  · exact le_antisymm hNO (Subgroup.subgroupOf_eq_top.mp htop)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C

