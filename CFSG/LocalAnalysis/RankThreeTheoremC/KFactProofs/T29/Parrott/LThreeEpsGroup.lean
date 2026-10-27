module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Split
public import CFSG.Quasithin.Background.A318PL3Core

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup

section NPC

theorem hasNormalPComplement_of_fix_omega {K : Type*} [Group K] [Finite K] {p : ℕ}
    [hp : Fact p.Prime] (hodd : p ≠ 2)
    (hfix : ∀ Q : Subgroup K, IsPGroup p Q → ∀ n ∈ normalizer (Q : Set K), ∀ x ∈ Q, x ^ p = 1 →
      n * x * n⁻¹ = x) : CFSG.HasNormalPComplement p K := by
  rw [CFSG.GroupTheory.hasNormalPComplement_iff_isPGroup_automizer]
  intro Q hQ
  apply CFSG.SectionRank.Ccomm.isPGroup_of_coprime_eq_one
  intro a ha
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective a
  set C : Subgroup (Subgroup.normalizer (Q : Set K)) :=
    (Subgroup.centralizer (Q : Set K)).subgroupOf (Subgroup.normalizer (Q : Set K)) with hC
  have hker : (Q.normalizerMonoidHom).ker = C := Subgroup.normalizerMonoidHom_ker Q
  have : C.Normal := by rw [← hker]; infer_instance
  let ψ : (Subgroup.normalizer (Q : Set K)) ⧸ C →* MulAut Q :=
    QuotientGroup.lift C Q.normalizerMonoidHom (by rw [← hker])
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : Q.normalizerMonoidHom m = 1 := hx
    rw [QuotientGroup.eq_one_iff, ← hker]
    exact h1
  have hψn : ψ (QuotientGroup.mk n) = Q.normalizerMonoidHom n := rfl
  have hcop : (orderOf (Q.normalizerMonoidHom n)).Coprime p := by
    rw [← hψn, orderOf_injective ψ hψ]
    exact ha
  have hα : Q.normalizerMonoidHom n = 1 := by
    refine CFSG.HardMathSupport.Timmesfeld.ComponentBalance.mulAut_eq_one_of_coprime_of_fix_omega
      hodd hQ hcop ?_
    intro x hx
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hfix Q hQ n n.2 x x.2 (by rw [← Subgroup.coe_pow, hx, Subgroup.coe_one])
  rw [QuotientGroup.eq_one_iff]
  have hnC : n ∈ C := by rw [← hker]; exact hα
  exact hnC

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem {Q : Subgroup G} {g : G}
    (hg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) : g ∈ normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨q, hq, rfl⟩
    exact hg q hq
  · rw [Nat.card_congr (Subgroup.equivMapOfInjective Q (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv]
    exact le_rfl

theorem le_normalizer_and_mem_of_elemAbelian {Q : Subgroup G} (hQ : IsElemAbelian 3 Q)
    (hmax : ∀ g : G, g ^ 3 = 1 → (∀ q ∈ Q, q * g = g * q) → g ∈ Q)
    (hN : ∀ g ∈ normalizer (Q : Set G), ∀ q ∈ Q, g * q * g⁻¹ = q)
    (P : Sylow 3 G) (hQP : Q ≤ P) :
    (P : Subgroup G) ≤ normalizer (Q : Set G) ∧ ∀ g ∈ (P : Subgroup G), g ^ 3 = 1 → g ∈ Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R : Subgroup G := (P : Subgroup G) ⊓ normalizer (Q : Set G) with hR
  have hRQ : ∀ r ∈ R, r ^ 3 = 1 → r ∈ Q := by
    intro r hr hr3
    refine hmax r hr3 fun q hq => ?_
    have h1 := hN r (Subgroup.mem_inf.1 hr).2 q hq
    calc q * r = r * q * r⁻¹ * r := by rw [h1]
      _ = r * q := by group
  have hQR : Q ≤ R := le_inf hQP Subgroup.le_normalizer
  suffices hRP : R = P by
    refine ⟨fun g hg => ?_, fun g hg hg3 => hRQ g (hRP ▸ hg) hg3⟩
    rw [← hRP] at hg
    exact (Subgroup.mem_inf.1 hg).2
  haveI hnil : Group.IsNilpotent ↥(P : Subgroup G) := P.isPGroup'.isNilpotent
  have hnc := (normalizerCondition_iff_only_full_group_self_normalizing.1
    (normalizerCondition_of_isNilpotent (G := ↥(P : Subgroup G)))) (R.subgroupOf P)
  have hself : normalizer ((R.subgroupOf P : Subgroup ↥(P : Subgroup G)) :
      Set ↥(P : Subgroup G)) = R.subgroupOf P := by
    refine le_antisymm (fun n hn => ?_) Subgroup.le_normalizer
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.2 ⟨n.2, mem_normalizer_of_conj_mem fun q hq => ?_⟩
    have hqR : (⟨q, hQP hq⟩ : ↥(P : Subgroup G)) ∈ R.subgroupOf P :=
      Subgroup.mem_subgroupOf.2 (hQR hq)
    have h1 := (Subgroup.mem_normalizer_iff.1 hn ⟨q, hQP hq⟩).1 hqR
    rw [Subgroup.mem_subgroupOf] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    refine hRQ _ h1 ?_
    rw [conj_pow, hQ.2 q hq, mul_one, mul_inv_cancel]
  have htop := hnc hself
  exact le_antisymm inf_le_left (Subgroup.subgroupOf_eq_top.1 htop)

theorem hasNormalPComplement_of_elemAbelian {Q : Subgroup G} (hQ : IsElemAbelian 3 Q)
    (hmax : ∀ g : G, g ^ 3 = 1 → (∀ q ∈ Q, q * g = g * q) → g ∈ Q)
    (hN : ∀ g ∈ normalizer (Q : Set G), ∀ q ∈ Q, g * q * g⁻¹ = q) :
    CFSG.HasNormalPComplement 3 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQp : IsPGroup 3 Q := fun q => ⟨1, Subtype.ext (by simpa using hQ.2 q q.2)⟩
  obtain ⟨P, hQP⟩ := hQp.exists_le_sylow
  obtain ⟨hPN, hPQ⟩ := le_normalizer_and_mem_of_elemAbelian hQ hmax hN P hQP
  have hcube : ∀ m q : G, q ^ 3 = 1 → (m * q * m⁻¹) ^ 3 = 1 := fun m q hq => by
    rw [conj_pow, hq, mul_one, mul_inv_cancel]
  have hQC : ∀ q ∈ Q, q ∈ centralizer ((P : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 := hN r (hPN hr) q hq
    calc r * q = r * q * r⁻¹ * r := by group
      _ = q * r := by rw [h1]
  have hNPQ : ∀ m ∈ normalizer ((P : Subgroup G) : Set G), ∀ q ∈ Q, m * q * m⁻¹ = q := by
    intro m hm q hq
    refine hN m (mem_normalizer_of_conj_mem fun q' hq' => ?_) q hq
    exact hPQ _ ((Subgroup.mem_normalizer_iff.1 hm q').1 (hQP hq')) (hcube m q' (hQ.2 q' hq'))
  apply hasNormalPComplement_of_fix_omega (p := 3) (by norm_num)
  intro H hH n hn x hx hx3
  obtain ⟨P₀, hHP₀⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P
  have hconj : ∀ u ∈ H, g * u * g⁻¹ ∈ (P : Subgroup G) := by
    intro u hu
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨u, hHP₀ hu, rfl⟩
  have hnx : n * x * n⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hn x).1 hx
  have hx'Q : g * x * g⁻¹ ∈ Q := hPQ _ (hconj x hx) (hcube g x hx3)
  have hy'Q : g * (n * x * n⁻¹) * g⁻¹ ∈ Q :=
    hPQ _ (hconj _ hnx) (hcube g _ (hcube n x hx3))
  set n' := g * n * g⁻¹ with hn'
  have hy'eq : n'⁻¹⁻¹ * (g * x * g⁻¹) * n'⁻¹ = g * (n * x * n⁻¹) * g⁻¹ := by
    rw [hn']
    group
  obtain ⟨m, hm, hmeq⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer P (g * x * g⁻¹) n'⁻¹
    (hQC _ hx'Q) (by rw [hy'eq]; exact hQC _ hy'Q)
  have h1 := hNPQ m⁻¹ (inv_mem hm) _ hx'Q
  rw [inv_inv] at h1
  rw [hy'eq, h1] at hmeq
  calc n * x * n⁻¹ = g⁻¹ * (g * (n * x * n⁻¹) * g⁻¹) * g := by group
    _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hmeq]
    _ = x := by group

end NPC

section Cyclic

variable {G : Type*} [Group G]

theorem false_of_conj_inv {A : Subgroup G} (hA : IsCyclic ↥A) {w g : G}
    (hw : w ∈ normalizer (A : Set G)) (hg : g ∈ normalizer (A : Set G))
    (hw3 : ∀ a ∈ A, w ^ 3 * a * (w ^ 3)⁻¹ = a) (hwA : ∃ a ∈ A, w * a * w⁻¹ ≠ a)
    (hgw : ∀ a ∈ A, (g * w * g⁻¹) * a * (g * w * g⁻¹)⁻¹ = w⁻¹ * a * w) : False := by
  obtain ⟨a₀, ha₀⟩ := hA.exists_generator
  have hga₀ : g * (a₀ : G) * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hg _).1 a₀.2
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (ha₀ ⟨_, hga₀⟩)
  have hm' : (a₀ : G) ^ m = g * (a₀ : G) * g⁻¹ := by
    have := congrArg Subtype.val hm
    simpa using this
  have hpow : ∀ b ∈ A, g * b * g⁻¹ = b ^ m := by
    intro b hb
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (ha₀ ⟨b, hb⟩)
    have hj' : (a₀ : G) ^ j = b := by
      have := congrArg Subtype.val hj
      simpa using this
    rw [← hj', ← zpow_mul, mul_comm, zpow_mul, hm', conj_zpow]
  have hinv : ∀ b ∈ A, w * b * w⁻¹ = w⁻¹ * b * w := by
    intro b hb
    have hb' : g⁻¹ * b * g ∈ A := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) b).1 hb
      simpa using this
    have hwb' : w * (g⁻¹ * b * g) * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hw _).1 hb'
    have e1 : g * (w * (g⁻¹ * b * g) * w⁻¹) * g⁻¹ = w⁻¹ * b * w := by
      rw [← hgw b hb]
      group
    have e2 : g * (w * (g⁻¹ * b * g) * w⁻¹) * g⁻¹ = w * b * w⁻¹ := by
      rw [hpow _ hwb', conj_zpow, ← hpow _ hb']
      group
    rw [← e2, e1]
  obtain ⟨a, ha, hwa⟩ := hwA
  apply hwa
  have h2 : Commute (w ^ 2) a := by
    have e : w * (w * a * w⁻¹) = a * w := by
      rw [hinv a ha, mul_assoc, mul_inv_cancel_left]
    show w ^ 2 * a = a * w ^ 2
    calc w ^ 2 * a = w * (w * a * w⁻¹) * w := by rw [pow_two]; simp [mul_assoc]
      _ = a * w * w := by rw [e]
      _ = a * w ^ 2 := by rw [pow_two, mul_assoc]
  have h3 : Commute (w ^ 3) a := by
    show w ^ 3 * a = a * w ^ 3
    calc w ^ 3 * a = w ^ 3 * a * (w ^ 3)⁻¹ * w ^ 3 := (inv_mul_cancel_right _ _).symm
      _ = a * w ^ 3 := by rw [hw3 a ha]
  have hc : Commute (w ^ 3 * (w ^ 2)⁻¹) a := h3.mul_left h2.inv_left
  have hw' : w ^ 3 * (w ^ 2)⁻¹ = w := by group
  rw [hw'] at hc
  calc w * a * w⁻¹ = a * w * w⁻¹ := by rw [hc.eq]
    _ = a := mul_inv_cancel_right a w

end Cyclic

section Rank

variable {X : Type} [Group X] [Finite X]

theorem three_le_of_pair {L : Subgroup X} {x a b : X} (hx3 : x ^ 3 = 1) (hxL : x ∉ L)
    (haL : a ∈ L) (hbL : b ∈ L) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb : b ∉ zpowers a) (hxa : a * x = x * a) (hxb : b * x = x * b) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hel : ∀ c : X, c ^ 3 = 1 → IsElemAbelian 3 (zpowers c) := fun c hc => by
    rw [Subgroup.zpowers_eq_closure]
    refine IsElemAbelian.closure_of_commute (fun u hu v hv => ?_) (fun u hu => ?_)
    · rw [Set.mem_singleton_iff] at hu hv
      rw [hu, hv]
    · rw [Set.mem_singleton_iff] at hu
      rw [hu, hc]
  have hcomm : ∀ u ∈ zpowers a, ∀ v ∈ zpowers b, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact ((Commute.zpow_left hab i).zpow_right j).eq
  have hE : IsElemAbelian 3 (zpowers a ⊔ zpowers b) := (hel a ha3).sup_of_commute (hel b hb3) hcomm
  have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hE9 : Nat.card ↥(zpowers a ⊔ zpowers b) = 9 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers a) hb3 hb
      (fun u hu => hcomm u hu b (Subgroup.mem_zpowers b)), Nat.card_zpowers, hord]
  have hEL : zpowers a ⊔ zpowers b ≤ L := sup_le (zpowers_le.2 haL) (zpowers_le.2 hbL)
  have hEC : zpowers a ⊔ zpowers b ≤ centralizer ({x} : Set X) :=
    sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hxa))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 hxb))
  exact three_le_of_E9 hE hE9 hx3 (fun h => hxL (hEL h))
    (fun e he => mem_centralizer_singleton_iff.1 (hEC he))

theorem three_le_of_mem_normal_card_three {N : Subgroup X} [N.Normal] (hN : Nat.card N = 3)
    {x : X} (hx : x ∈ N) (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X)) := by
  obtain ⟨E, hE, hE27⟩ := exists_elemAbelian_27 hX
  have hEC : E ≤ centralizer ({x} : Set X) := by
    intro a ha
    have h1 := CFSG.Quasithin.A318P.commute_of_card_three hN (m := a) (k := 1)
      (by rw [pow_one]; exact hE.2 a ha) hx
    rw [mem_centralizer_singleton_iff]
    calc a * x = a * x * a⁻¹ * a := (inv_mul_cancel_right _ _).symm
      _ = x * a := by rw [h1]
  exact CFSG.SectionRank.le_pRank (by norm_num) hEC hE (by rw [hE27]; norm_num)

end Rank

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
