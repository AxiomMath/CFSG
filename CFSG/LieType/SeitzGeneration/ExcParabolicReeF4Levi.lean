module

public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersParabolic
public import CFSG.LieType.Ree.LargeReeMinimalBorel
public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration

public section

namespace CFSG.LieType.SeitzGeneration

open scoped Pointwise

theorem index_subgroupOf_dvd_card_of_le_sup {G : Type*} [Group G] {P L V : Subgroup G}
    (hLP : L ≤ P) (hVP : V ≤ P) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hP : P ≤ L ⊔ V) : (L.subgroupOf P).index ∣ Nat.card V := by
  classical
  set H : Subgroup P := V.subgroupOf P with hH
  set x₀ : P ⧸ L.subgroupOf P := ((1 : P) : P ⧸ L.subgroupOf P) with hx₀
  have horb : MulAction.orbit H x₀ = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg : (g : G) ∈ (L : Set G) * (V : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right L V hLV]
      exact hP g.2
    obtain ⟨l, hl, v, hv, hlv⟩ := hg
    have hv' : l * v * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV hl) v).1 hv
    have hl' : (⟨l, hLP hl⟩ : P) ∈ L.subgroupOf P := hl
    set u : P := ⟨l * v * l⁻¹, hVP hv'⟩ with hu
    have huH : u ∈ H := Subgroup.mem_subgroupOf.2 hv'
    have e : g = u * ⟨l, hLP hl⟩ := by
      apply Subtype.ext
      show (g : G) = l * v * l⁻¹ * l
      rw [← hlv]
      group
    refine ⟨⟨u, huH⟩, ?_⟩
    beta_reduce
    rw [e, QuotientGroup.mk_mul_of_mem _ hl', Subgroup.smul_def, hx₀, MulAction.Quotient.smul_mk]
    simp
  have h1 : (MulAction.stabilizer H x₀).index = (L.subgroupOf P).index := by
    rw [MulAction.index_stabilizer, horb, Set.ncard_univ, Subgroup.index_eq_card]
  have h2 : (MulAction.stabilizer H x₀).index ∣ Nat.card H := Subgroup.index_dvd_card _
  have h3 : Nat.card H = Nat.card V := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVP).toEquiv
  rw [← h1, ← h3]
  exact h2

theorem mem_normalizer_inf_of_normalizers {G : Type*} [Group G] {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hH h, hK h]


section Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem reeLocalParabolic_le_normalizer_complement (j : Fin F4.fixedOrbitCount) :
    F4.reeLocalParabolic K a j ≤
      Subgroup.normalizer (F4.reeFixedOrbitComplementUnipotent K a j : Set (ModGL F4.tag K)) :=
  fun _ hx => mem_normalizer_inf_of_normalizers
    (parabolicSubgroup_le_normalizer_parabolicRadical (F4.fixedOrbitSet j)
      (Subgroup.mem_inf.1 hx).2)
    (Subgroup.le_normalizer (Subgroup.mem_inf.1 hx).1)

theorem isPGroup_reeFixedOrbitComplementUnipotent
    (j : Fin F4.fixedOrbitCount) :
    IsPGroup 2 (F4.reeFixedOrbitComplementUnipotent K a j) :=
  (isPGroup_posUnipotent F4.prime F4.tag (K := K)).to_le
    ((reeFixedOrbitComplementUnipotent_le j).trans inf_le_left)


theorem reeLocalParabolic_le_sup_levi (j : Fin F4.fixedOrbitCount) :
    F4.reeLocalParabolic K a j ≤
      (F4.reeLocalBlock K a j ⊔ F4.reeFixedTorus K a) ⊔
        F4.reeFixedOrbitComplementUnipotent K a j := by
  have hB : F4.reeFixedBorel K a ≤ (F4.reeLocalBlock K a j ⊔ F4.reeFixedTorus K a) ⊔
      F4.reeFixedOrbitComplementUnipotent K a j := by
    rw [reeFixedBorel_eq_sup, ← reeFixedOrbitComplementUnipotent_sup j]
    exact sup_le (le_sup_of_le_left le_sup_right) (sup_le le_sup_right
      (le_sup_of_le_left (le_sup_of_le_left (reeFixedOrbitUnipotent_le_reeLocalBlock j))))
  rw [← reeParabolic_singleton j]
  refine sup_le hB ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨k, hk, rfl⟩
  obtain rfl : k = j := hk
  obtain ⟨m, hm, hmn⟩ := exists_mem_reeLocalBlock_mk_eq (K := K) (a := a) k
  have hb : m⁻¹ * canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement k) ∈
      F4.reeFixedBorel K a := QuotientGroup.eq.1 hmn
  have hmem := mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hm)) (hB hb)
  rwa [mul_inv_cancel_left] at hmem

theorem exists_conj_le_levi (j : Fin F4.fixedOrbitCount) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {A : Subgroup (ModGL F4.tag K)}
    (hAP : A ≤ F4.reeLocalParabolic K a j) (hA : IsPGroup p A) :
    ∃ y ∈ F4.reeLocalParabolic K a j, A.map (MulAut.conj y).toMonoidHom ≤
      F4.reeLocalBlock K a j ⊔ F4.reeFixedTorus K a := by
  have := finite_modGL (τ := F4.tag) (K := K)
  have hBP := (reeFixedBorel_lt_reeLocalParabolic (K := K) (a := a) (t := F4) j).le
  have hLP : F4.reeLocalBlock K a j ⊔ F4.reeFixedTorus K a ≤ F4.reeLocalParabolic K a j :=
    sup_le (reeLocalBlock_le j) (reeFixedTorus_le_reeFixedBorel.trans hBP)
  have hVP : F4.reeFixedOrbitComplementUnipotent K a j ≤ F4.reeLocalParabolic K a j :=
    (reeFixedOrbitComplementUnipotent_le j).trans
      (reeFixedPosUnipotent_le_reeFixedBorel.trans hBP)
  have hdvd := index_subgroupOf_dvd_card_of_le_sup hLP hVP
    (hLP.trans (reeLocalParabolic_le_normalizer_complement j)) (reeLocalParabolic_le_sup_levi j)
  refine exists_conj_le_of_not_dvd_index hAP hA fun hp => ?_
  exact not_dvd_card_of_isPGroup (r := 2) (p := p) (Ne.symm hp2)
    (isPGroup_reeFixedOrbitComplementUnipotent j) (hp.trans hdvd)

end Ree

end CFSG.LieType.SeitzGeneration
