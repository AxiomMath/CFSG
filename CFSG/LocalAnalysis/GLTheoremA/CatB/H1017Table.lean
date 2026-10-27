module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017SylowQ
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (sporOrd SporadicOrdersTable)
open scoped commutatorElement Pointwise

theorem isPGroup_of_elemAbelian {X : Type} [Group X] {p : ℕ} {F : Subgroup X}
    (hF : IsElemAbelian p F) : IsPGroup p F := fun g => ⟨1, Subtype.ext (by simpa using hF.2 g g.2)⟩

theorem elemAbelian_card_le_sq_of_cubic {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (h4 : ¬ p ^ 4 ∣ Nat.card X) {x y : X} (hz : ⁅x, y⁆ ≠ 1)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set X)) = p ^ 3)
    (E : Subgroup X) (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (isPGroup_of_elemAbelian hE)
  rw [hm]
  refine Nat.pow_le_pow_right hp.pos ?_
  by_contra hlt
  push Not at hlt
  have hEX : p ^ m ∣ Nat.card X := hm ▸ Subgroup.card_subgroup_dvd_card E
  have hm3 : m = 3 := by
    by_contra hne
    exact h4 ((Nat.pow_dvd_pow p (by omega)).trans hEX)
  subst hm3
  set H := Subgroup.closure ({x, y} : Set X)
  have hXne : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hf : (Nat.card X).factorization p = 3 := by
    apply le_antisymm
    · by_contra h
      push Not at h
      exact h4 ((Nat.pow_dvd_pow p h).trans (Nat.ordProj_dvd _ _))
    · exact (Nat.Prime.pow_dvd_iff_le_factorization hp hXne).1 hEX
  let SE : Sylow p X := Sylow.ofCard E (by rw [hm, hf])
  let SH : Sylow p X := Sylow.ofCard H (by rw [hcard, hf])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X SH SE
  have hmem : ∀ w ∈ H, g * w * g⁻¹ ∈ E := fun w hw => by
    have h1 : (MulAut.conj g) • w ∈ (MulAut.conj g) • H := Subgroup.smul_mem_pointwise_smul _ _ _ hw
    have h2 : ((g • SH : Sylow p X) : Subgroup X) = (MulAut.conj g) • H := Sylow.coe_subgroup_smul
    rw [← h2, hg] at h1
    exact h1
  apply hz
  have hx := hmem x (Subgroup.subset_closure (by simp))
  have hy := hmem y (Subgroup.subset_closure (by simp))
  have hc := congrArg Subtype.val (hE.1.1.comm ⟨_, hx⟩ ⟨_, hy⟩)
  simp only [Subgroup.coe_mul] at hc
  rw [commutatorElement_eq_one_iff_mul_comm]
  have : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
    calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := hc
      _ = g * (y * x) * g⁻¹ := by group
  simpa using this

theorem twoRankLe_two_of_bound {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) {X : Type}
    [Group X] (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hb : ∀ E : Subgroup X, IsElemAbelian p E → Nat.card E ≤ p ^ 2) : TwoRankLe p s 2 := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := hX
  let φ : K ≃* X := e.trans b.symm
  exact glaTwoLocalRank_le_of_card_le hp fun R E _ _ _ hE => by
    have h := hb (E.map φ.toMonoidHom) (isElemAbelian_map' _ hE)
    rwa [Subgroup.card_map_of_injective φ.injective] at h

theorem twoRankLe_two_of_cubic {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) {X : Type}
    [Group X] [Finite X] (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (h4 : ¬ p ^ 4 ∣ Nat.card X) {x y : X} (hz : ⁅x, y⁆ ≠ 1)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set X)) = p ^ 3) : TwoRankLe p s 2 :=
  twoRankLe_two_of_bound hp hX (elemAbelian_card_le_sq_of_cubic hp h4 hz hcard)

theorem twoRankLe_two_of_order (hOrd : SporadicOrdersTable) {s : TauCeti.SporadicName} {p : ℕ}
    (hp : p.Prime) (h : ¬ p ^ 3 ∣ sporOrd s) : TwoRankLe p s 2 := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  have hK : Nat.card K = sporOrd s := (Nat.card_congr e.toEquiv).trans (hOrd s)
  haveI : Fact p.Prime := ⟨hp⟩
  exact glaTwoLocalRank_le_of_card_le hp fun R E _ _ _ hE => by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (isPGroup_of_elemAbelian hE)
    rw [hm]
    refine Nat.pow_le_pow_right hp.pos ?_
    by_contra hlt
    push Not at hlt
    apply h
    rw [← hK]
    exact (Nat.pow_dvd_pow p (by omega)).trans (hm ▸ Subgroup.card_subgroup_dvd_card E)

structure I1017CubicRows : Prop where
  m12 : TwoRankLe 3 .M12 2
  m24 : TwoRankLe 3 .M24 2
  j2 : TwoRankLe 3 .J2 2
  j4three : TwoRankLe 3 .J4 2
  j4eleven : TwoRankLe 11 .J4 2
  hs : TwoRankLe 5 .HS 2
  mclfive : TwoRankLe 5 .McL 2
  hethree : TwoRankLe 3 .He 2
  heseven : TwoRankLe 7 .He 2
  ruthree : TwoRankLe 3 .Ru 2
  rufive : TwoRankLe 5 .Ru 2
  on : TwoRankLe 7 .ONan 2
  co2 : TwoRankLe 5 .Co2 2
  co3 : TwoRankLe 5 .Co3 2
  fi24 : TwoRankLe 7 .Fi24Prime 2
  th : TwoRankLe 5 .Th 2

structure I1017HardRows : Prop where
  j3 : TwoRankLe 3 .J3 2
  mclthree : TwoRankLe 3 .McL 2
  co1 : TwoRankLe 5 .Co1 2
  hn : TwoRankLe 5 .HN 2
  ly : TwoRankLe 5 .Ly 2
  b : TwoRankLe 5 .B 2
  mseven : TwoRankLe 7 .M 2
  mthirteen : TwoRankLe 13 .M 2

theorem prime_mem_of_dvd_prod {p : ℕ} (hp : p.Prime) :
    ∀ L : List (ℕ × ℕ), (∀ x ∈ L, x.1.Prime) → p ∣ (L.map fun x => x.1 ^ x.2).prod →
      p ∈ L.map Prod.fst
  | [], _, h => absurd (Nat.le_of_dvd one_pos (by simpa using h)) (by have := hp.two_le; omega)
  | x :: L, hL, h => by
    rw [List.map_cons, List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · have := (Nat.prime_dvd_prime_iff_eq hp (hL x (List.mem_cons_self))).1
        (hp.dvd_of_dvd_pow h1)
      simp [this]
    · exact List.mem_cons_of_mem _ (prime_mem_of_dvd_prod hp L
        (fun y hy => hL y (List.mem_cons_of_mem _ hy)) h1)

@[expose] def table3Names : List TauCeti.SporadicName :=
  [.ONan, .HN, .Ly, .Co1, .Co2, .Co3, .Fi22, .Fi23, .Fi24Prime, .B, .Th, .M, .Suz]

theorem table_cases (hOrd : SporadicOrdersTable) (hc : I1017CubicRows) (hh : I1017HardRows)
    (s : TauCeti.SporadicName) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (p = 3 ∧ s ∈ table3Names) ∨ (p = 5 ∧ s = .M) ∨ TwoRankLe p s 2 := by
  by_cases hd : p ^ 3 ∣ sporOrd s
  swap
  · exact Or.inr (Or.inr (twoRankLe_two_of_order hOrd hp hd))
  have hpd : p ∣ sporOrd s := (dvd_pow_self p (by norm_num)).trans hd
  cases s with
  | M11 =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 4), (3, 2), (5, 1), (11, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 4), (3, 2), (5, 1), (11, 1)]).prod = sporOrd .M11 by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | M12 =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 6), (3, 3), (5, 1), (11, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 6), (3, 3), (5, 1), (11, 1)]).prod = sporOrd .M12 by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inr (Or.inr hc.m12)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | M22 =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 7), (3, 2), (5, 1), (7, 1), (11, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 7), (3, 2), (5, 1), (7, 1), (11, 1)]).prod = sporOrd .M22 by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | M23 =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (23, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (23, 1)]).prod = sporOrd .M23 by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | M24 =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 10), (3, 3), (5, 1), (7, 1), (11, 1), (23, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 10), (3, 3), (5, 1), (7, 1), (11, 1), (23, 1)]).prod = sporOrd .M24 by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inr (Or.inr hc.m24)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | J1 =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (19, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (19, 1)]).prod = sporOrd .J1 by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | J2 =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 7), (3, 3), (5, 2), (7, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 7), (3, 3), (5, 2), (7, 1)]).prod = sporOrd .J2 by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inr (Or.inr hc.j2)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | J3 =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 7), (3, 5), (5, 1), (17, 1), (19, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 7), (3, 5), (5, 1), (17, 1), (19, 1)]).prod = sporOrd .J3 by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inr (Or.inr hh.j3)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | J4 =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 21), (3, 3), (5, 1), (7, 1), (11, 3), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 21), (3, 3), (5, 1), (7, 1), (11, 3), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1)]).prod = sporOrd .J4 by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inr (Or.inr hc.j4three)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact Or.inr (Or.inr hc.j4eleven)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | HS =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 9), (3, 2), (5, 3), (7, 1), (11, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 9), (3, 2), (5, 3), (7, 1), (11, 1)]).prod = sporOrd .HS by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact Or.inr (Or.inr hc.hs)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | McL =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 7), (3, 6), (5, 3), (7, 1), (11, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 7), (3, 6), (5, 3), (7, 1), (11, 1)]).prod = sporOrd .McL by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inr (Or.inr hh.mclthree)
    · exact Or.inr (Or.inr hc.mclfive)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | He =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 10), (3, 3), (5, 2), (7, 3), (17, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 10), (3, 3), (5, 2), (7, 3), (17, 1)]).prod = sporOrd .He by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inr (Or.inr hc.hethree)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact Or.inr (Or.inr hc.heseven)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | Ru =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 14), (3, 3), (5, 3), (7, 1), (13, 1), (29, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 14), (3, 3), (5, 3), (7, 1), (13, 1), (29, 1)]).prod = sporOrd .Ru by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inr (Or.inr hc.ruthree)
    · exact Or.inr (Or.inr hc.rufive)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | Suz =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 13), (3, 7), (5, 2), (7, 1), (11, 1), (13, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 13), (3, 7), (5, 2), (7, 1), (11, 1), (13, 1)]).prod = sporOrd .Suz by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inl ⟨rfl, by decide⟩
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | ONan =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 9), (3, 4), (5, 1), (7, 3), (11, 1), (19, 1), (31, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 9), (3, 4), (5, 1), (7, 3), (11, 1), (19, 1), (31, 1)]).prod = sporOrd .ONan by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inl ⟨rfl, by decide⟩
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact Or.inr (Or.inr hc.on)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | Co1 =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 21), (3, 9), (5, 4), (7, 2), (11, 1), (13, 1), (23, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 21), (3, 9), (5, 4), (7, 2), (11, 1), (13, 1), (23, 1)]).prod = sporOrd .Co1 by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inl ⟨rfl, by decide⟩
    · exact Or.inr (Or.inr hh.co1)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | Co2 =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 18), (3, 6), (5, 3), (7, 1), (11, 1), (23, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 18), (3, 6), (5, 3), (7, 1), (11, 1), (23, 1)]).prod = sporOrd .Co2 by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inl ⟨rfl, by decide⟩
    · exact Or.inr (Or.inr hc.co2)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | Co3 =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 10), (3, 7), (5, 3), (7, 1), (11, 1), (23, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 10), (3, 7), (5, 3), (7, 1), (11, 1), (23, 1)]).prod = sporOrd .Co3 by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inl ⟨rfl, by decide⟩
    · exact Or.inr (Or.inr hc.co3)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | Fi22 =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 17), (3, 9), (5, 2), (7, 1), (11, 1), (13, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 17), (3, 9), (5, 2), (7, 1), (11, 1), (13, 1)]).prod = sporOrd .Fi22 by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inl ⟨rfl, by decide⟩
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | Fi23 =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 18), (3, 13), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (23, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 18), (3, 13), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (23, 1)]).prod = sporOrd .Fi23 by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inl ⟨rfl, by decide⟩
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | Fi24Prime =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 21), (3, 16), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 21), (3, 16), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1)]).prod = sporOrd .Fi24Prime by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inl ⟨rfl, by decide⟩
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact Or.inr (Or.inr hc.fi24)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | HN =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 14), (3, 6), (5, 6), (7, 1), (11, 1), (19, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 14), (3, 6), (5, 6), (7, 1), (11, 1), (19, 1)]).prod = sporOrd .HN by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inl ⟨rfl, by decide⟩
    · exact Or.inr (Or.inr hh.hn)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | Ly =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 8), (3, 7), (5, 6), (7, 1), (11, 1), (31, 1), (37, 1), (67, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 8), (3, 7), (5, 6), (7, 1), (11, 1), (31, 1), (37, 1), (67, 1)]).prod = sporOrd .Ly by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inl ⟨rfl, by decide⟩
    · exact Or.inr (Or.inr hh.ly)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | Th =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 15), (3, 10), (5, 3), (7, 2), (13, 1), (19, 1), (31, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 15), (3, 10), (5, 3), (7, 2), (13, 1), (19, 1), (31, 1)]).prod = sporOrd .Th by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inl ⟨rfl, by decide⟩
    · exact Or.inr (Or.inr hc.th)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | B =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 41), (3, 13), (5, 6), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (47, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 41), (3, 13), (5, 6), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (47, 1)]).prod = sporOrd .B by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inl ⟨rfl, by decide⟩
    · exact Or.inr (Or.inr hh.b)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
  | M =>
    have hmem := prime_mem_of_dvd_prod hp [(2, 46), (3, 20), (5, 9), (7, 6), (11, 2), (13, 3), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (47, 1), (59, 1), (71, 1)] (by norm_num)
      (by rw [show (List.map (fun x : ℕ × ℕ => x.1 ^ x.2) [(2, 46), (3, 20), (5, 9), (7, 6), (11, 2), (13, 3), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (47, 1), (59, 1), (71, 1)]).prod = sporOrd .M by
        norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]]; exact hpd)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hp2
    · exact Or.inl ⟨rfl, by decide⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr hh.mseven)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact Or.inr (Or.inr hh.mthirteen)
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])
    · exact absurd hd (by norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster])

theorem i1017TableFact_of_rows (hOrd : SporadicOrdersTable) (hc : I1017CubicRows)
    (hh : I1017HardRows) : I1017TableFact := by
  intro K _ _ p hp hp2 hcat h3
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | sporadic s =>
    rcases table_cases hOrd hc hh s hp hp2 with ⟨rfl, hs⟩ | ⟨rfl, rfl⟩ | hrow
    · exact Or.inl ⟨rfl, ⟨_, ⟨s, hs, rfl⟩, ⟨e⟩⟩⟩
    · exact Or.inr ⟨rfl, ⟨_, rfl, ⟨e⟩⟩⟩
    · have := hrow K ⟨_, rfl, ⟨e⟩⟩
      omega
  | _ => exact absurd hi (by simp [S8.isSporIndex])

end CFSG.LocalAnalysis.GLTheoremA.H1017
