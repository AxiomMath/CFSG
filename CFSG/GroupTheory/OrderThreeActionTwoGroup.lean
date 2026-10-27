module

public import Mathlib.GroupTheory.PGroup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type} [Group G]

theorem card_inf_centralizer_eq_one_or_four_or_sixteen {Q : Subgroup G} [Finite ↥Q] {c : G}
    (hcardQ : Nat.card Q = 16)
    (hcN : c ∈ Subgroup.normalizer (Q : Set G)) (hc3 : orderOf c = 3) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({c} : Set G)) = 1 ∨
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({c} : Set G)) = 4 ∨
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({c} : Set G)) = 16 := by
  classical
  let A : Subgroup G := Subgroup.zpowers c
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := Subgroup.zpowers_le.mpr hcN
  letI : Subgroup.Normalizes A Q := ⟨hAQ⟩
  have hAcard : Nat.card ↥A = 3 := by
    rw [show A = Subgroup.zpowers c from rfl, Nat.card_zpowers, hc3]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 ↥A := IsPGroup.of_card (n := 1) (by simpa using hAcard)
  have hmod := hA3.card_modEq_card_fixedPoints (↥Q)
  let C : Subgroup G := Q ⊓ Subgroup.centralizer ({c} : Set G)
  have hCeq : (MulAction.fixedPoints ↥A ↥Q) = (fixedPointSubgroup ↥A ↥Q : Set ↥Q) := rfl
  have hCsub : fixedPointSubgroup ↥A ↥Q = C.subgroupOf Q := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hx ⟨c, Subgroup.mem_zpowers c⟩
      have h' : c * (x : G) * c⁻¹ = (x : G) := by
        simpa using congrArg Subtype.val h
      calc (x : G) * c = (c * (x : G) * c⁻¹) * c := by rw [h']
        _ = c * (x : G) := by group
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_inf] at hx
      intro a
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.2
      apply Subtype.ext
      have hxc : (x : G) * c = c * (x : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hx.2
      change (a : G) * (x : G) * (a : G)⁻¹ = (x : G)
      rw [← hn]
      have hcomm : Commute (c ^ n) (x : G) :=
        (show Commute c (x : G) from hxc.symm).zpow_left n
      calc c ^ n * (x : G) * (c ^ n)⁻¹ = ((x : G) * c ^ n) * (c ^ n)⁻¹ := by
            rw [hcomm]
        _ = (x : G) := by group
  have hcardC : Nat.card ↥(MulAction.fixedPoints ↥A ↥Q) = Nat.card ↥C := by
    rw [hCeq]
    change Nat.card ↥(fixedPointSubgroup ↥A ↥Q) = Nat.card ↥C
    rw [hCsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ Q)).toEquiv
  rw [hcardC] at hmod
  have hmod' : Nat.card ↥C ≡ 1 [MOD 3] := by
    rw [hcardQ] at hmod
    exact hmod.symm.trans (by decide : 16 ≡ 1 [MOD 3])
  have hdvd : Nat.card ↥C ∣ 16 := hcardQ ▸ Subgroup.card_dvd_of_le (inf_le_left : C ≤ Q)
  have hmem : Nat.card ↥C ∈ Nat.divisors 16 := by simp [hdvd]
  have h16 : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
  rw [h16] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h2 | h4 | h8 | h16
  · exact Or.inl h1
  · rw [h2] at hmod'
    exact absurd hmod' (by decide)
  · exact Or.inr (Or.inl h4)
  · rw [h8] at hmod'
    exact absurd hmod' (by decide)
  · exact Or.inr (Or.inr h16)

theorem le_normalizer_inf_centralizer_of_commutator_mem {Q L : Subgroup G}
    (hQab : IsMulCommutative ↥Q)
    (hQN : L ≤ Subgroup.normalizer (Q : Set G)) {c : G}
    (hcC : ∀ l ∈ L, ⁅c, l⁆ ∈ Q) :
    L ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer ({c} : Set G)) : Set G) := by
  classical
  let C : Subgroup G := Q ⊓ Subgroup.centralizer ({c} : Set G)
  have hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hQab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hconj_mem : ∀ m ∈ L, ∀ x ∈ C, m * x * m⁻¹ ∈ C := by
    intro m hm x hx
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
    have hmxQ : m * x * m⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hQN hm) x).mp hxQ
    refine Subgroup.mem_inf.mpr ⟨hmxQ, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
    have step1 : c * (m * x * m⁻¹) * c⁻¹ =
        (c * m * c⁻¹) * (c * x * c⁻¹) * (c * m * c⁻¹)⁻¹ := by group
    have step3 : (⁅c, m⁆ * m) * x * (⁅c, m⁆ * m)⁻¹ =
        ⁅c, m⁆ * (m * x * m⁻¹) * ⁅c, m⁆⁻¹ := by group
    have hcx : c * x * c⁻¹ = x := by
      rw [show c * x = x * c from hxC.symm]
      group
    have hcm : c * m * c⁻¹ = ⁅c, m⁆ * m := by
      rw [commutatorElement_def]; group
    have hmc_mem : ⁅c, m⁆ ∈ Q := hcC m hm
    have h2 : (c * m * c⁻¹) * (c * x * c⁻¹) * (c * m * c⁻¹)⁻¹ =
        (⁅c, m⁆ * m) * x * (⁅c, m⁆ * m)⁻¹ := by rw [hcm, hcx]
    have h4 : ⁅c, m⁆ * (m * x * m⁻¹) * ⁅c, m⁆⁻¹ = m * x * m⁻¹ := by
      rw [hQcomm ⁅c, m⁆ hmc_mem (m * x * m⁻¹) hmxQ]
      group
    have hmain : c * (m * x * m⁻¹) * c⁻¹ = m * x * m⁻¹ :=
      step1.trans (h2.trans (step3.trans h4))
    have hcomm_y : c * (m * x * m⁻¹) = (m * x * m⁻¹) * c := by
      calc c * (m * x * m⁻¹) = (c * (m * x * m⁻¹) * c⁻¹) * c := by group
        _ = (m * x * m⁻¹) * c := by rw [hmain]
    exact hcomm_y.symm
  intro l hl
  change l ∈ Subgroup.normalizer (C : Set G)
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨?_, ?_⟩
  · exact hconj_mem l hl x
  · intro hx
    have h := hconj_mem l⁻¹ (L.inv_mem hl) (l * x * l⁻¹) hx
    simpa [C, mul_assoc] using h

theorem relIndex_sup_eq_three_of_not_le {A B : Subgroup G}
    (hcardB : Nat.card B = 3) (hBA : B ≤ Subgroup.normalizer (A : Set G))
    (hnot : ¬ B ≤ A) : A.relIndex (A ⊔ B) = 3 := by
  have hsup : A.relIndex (A ⊔ B) = A.relIndex B := by
    letI := Subgroup.normal_subgroupOf_of_le_normalizer hBA
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBA
    rw [sup_comm]
    exact (Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient B A hBA).toEquiv).symm
  have hinf : A.relIndex B = (A ⊓ B).relIndex B :=
    (Subgroup.inf_relIndex_right (H := A) (K := B)).symm
  have hdvd : (A ⊓ B).relIndex B ∣ 3 := by
    rw [← hcardB]
    exact Subgroup.relIndex_dvd_card (H := A ⊓ B) (K := B)
  have hne : (A ⊓ B).relIndex B ≠ 1 := by
    intro hone
    have hle : B ≤ A ⊓ B := Subgroup.relIndex_eq_one.mp hone
    exact hnot (hle.trans inf_le_left)
  rw [hsup, hinf]
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact absurd h1 hne
  · exact h3

theorem exists_mem_of_card_eq_nine_of_four_lines [Finite G] (hG : Nat.card G = 9)
    {H1 H2 H3 H4 : Subgroup G}
    (h1 : Nat.card H1 = 3) (h2 : Nat.card H2 = 3)
    (h3 : Nat.card H3 = 3) (h4 : Nat.card H4 = 3)
    (hdist : H1 ≠ H2 ∧ H1 ≠ H3 ∧ H1 ≠ H4 ∧ H2 ≠ H3 ∧ H2 ≠ H4 ∧ H3 ≠ H4) :
    ∀ g : G, g ∈ H1 ∨ g ∈ H2 ∨ g ∈ H3 ∨ g ∈ H4 := by
  classical
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := hdist
  have hcard_inf : ∀ {H K : Subgroup G}, Nat.card H = 3 → Nat.card K = 3 →
      H ≠ K → H ⊓ K = ⊥ := by
    intro H K hH hK hne
    have hdvd : Nat.card ↥(H ⊓ K) ∣ 3 := by
      rw [← hH]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdvd with h | h
    · exact (H ⊓ K).eq_bot_of_card_eq h
    · exfalso
      apply hne
      have hH' : H ⊓ K = H := by
        apply Subgroup.eq_of_le_of_card_ge inf_le_left
        rw [h, hH]
      have hK' : H ⊓ K = K := by
        apply Subgroup.eq_of_le_of_card_ge inf_le_right
        rw [h, hK]
      exact hH'.symm.trans hK'
  have hdisj : ∀ {H K : Subgroup G}, Nat.card H = 3 → Nat.card K = 3 →
      H ≠ K → Disjoint ((H : Set G) \ {1}) ((K : Set G) \ {1}) := by
    intro H K hH hK hne
    rw [Set.disjoint_left]
    intro x hx hx'
    have hxbot : x ∈ H ⊓ K := ⟨hx.1, hx'.1⟩
    have hbot : H ⊓ K = ⊥ := hcard_inf hH hK hne
    have hx1 : x = 1 := by simpa [hbot] using hxbot
    exact hx.2 hx1
  let A1 : Set G := (H1 : Set G) \ {1}
  let A2 : Set G := (H2 : Set G) \ {1}
  let A3 : Set G := (H3 : Set G) \ {1}
  let A4 : Set G := (H4 : Set G) \ {1}
  have hA1 : A1.ncard = 2 := by
    dsimp only [A1]
    rw [Set.ncard_sdiff_singleton_of_mem H1.one_mem]
    change Nat.card H1 - 1 = 2
    rw [h1]
  have hA2 : A2.ncard = 2 := by
    dsimp only [A2]
    rw [Set.ncard_sdiff_singleton_of_mem H2.one_mem]
    change Nat.card H2 - 1 = 2
    rw [h2]
  have hA3 : A3.ncard = 2 := by
    dsimp only [A3]
    rw [Set.ncard_sdiff_singleton_of_mem H3.one_mem]
    change Nat.card H3 - 1 = 2
    rw [h3]
  have hA4 : A4.ncard = 2 := by
    dsimp only [A4]
    rw [Set.ncard_sdiff_singleton_of_mem H4.one_mem]
    change Nat.card H4 - 1 = 2
    rw [h4]
  have hA12 : Disjoint A1 A2 := by
    simpa only [A1, A2] using hdisj h1 h2 h12
  have hA13 : Disjoint A1 A3 := by
    simpa only [A1, A3] using hdisj h1 h3 h13
  have hA14 : Disjoint A1 A4 := by
    simpa only [A1, A4] using hdisj h1 h4 h14
  have hA23 : Disjoint A2 A3 := by
    simpa only [A2, A3] using hdisj h2 h3 h23
  have hA24 : Disjoint A2 A4 := by
    simpa only [A2, A4] using hdisj h2 h4 h24
  have hA34 : Disjoint A3 A4 := by
    simpa only [A3, A4] using hdisj h3 h4 h34
  let U : Set G := A1 ∪ A2 ∪ A3 ∪ A4
  have hA123 : Disjoint (A1 ∪ A2) A3 := by
    rw [Set.disjoint_union_left]
    exact ⟨hA13, hA23⟩
  have hA1234 : Disjoint (A1 ∪ A2 ∪ A3) A4 := by
    rw [Set.disjoint_union_left, Set.disjoint_union_left]
    exact ⟨⟨hA14, hA24⟩, hA34⟩
  have hU : U.ncard = 8 := by
    rw [show U = (A1 ∪ A2 ∪ A3) ∪ A4 from rfl]
    rw [Set.ncard_union_eq hA1234]
    rw [Set.ncard_union_eq hA123]
    rw [Set.ncard_union_eq hA12]
    rw [hA1, hA2, hA3, hA4]
  have h1U : (1 : G) ∉ U := by
    simp [U, A1, A2, A3, A4]
  have hcover : insert (1 : G) U = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ, hG, Set.ncard_insert_of_notMem h1U, hU]
  have hmem : ∀ g : G, g ∈ U → g ∈ H1 ∨ g ∈ H2 ∨ g ∈ H3 ∨ g ∈ H4 := by
    intro g hg
    simp only [U, A1, A2, A3, A4, Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff] at hg
    rcases hg with ((hg1 | hg2) | hg3) | hg4
    · exact Or.inl hg1.1
    · exact Or.inr (Or.inl hg2.1)
    · exact Or.inr (Or.inr (Or.inl hg3.1))
    · exact Or.inr (Or.inr (Or.inr hg4.1))
  intro g
  have hg : g ∈ insert (1 : G) U := by
    rw [hcover]
    exact Set.mem_univ g
  rcases Set.mem_insert_iff.mp hg with hg1 | hgU
  · rw [hg1]
    exact Or.inl H1.one_mem
  · exact hmem g hgU

theorem mem_of_commutator_mem_of_fixedPointFree {Q A : Subgroup G}
    (hQab : IsMulCommutative ↥Q)
    (hQ2 : ∀ q ∈ Q, q * q = 1)
    {x : G} (hxNQ : x ∈ Subgroup.normalizer (Q : Set G))
    (hx3 : orderOf x = 3)
    (hfix : ∀ q ∈ Q, x * q * x⁻¹ = q → q = 1)
    (hAQ : A ≤ Q)
    (hxNA : x ∈ Subgroup.normalizer (A : Set G))
    {q : G} (hqQ : q ∈ Q) (hcomm : ⁅x, q⁆ ∈ A) : q ∈ A := by
  classical
  have hQcomm : ∀ {u v : G}, u ∈ Q → v ∈ Q → u * v = v * u :=
    fun hu hv => congrArg Subtype.val (hQab.is_comm.comm ⟨_, hu⟩ ⟨_, hv⟩)
  let a : G := ⁅x, q⁆
  have haA : a ∈ A := hcomm
  have haQ : a ∈ Q := hAQ haA
  have hq1eq : x * q * x⁻¹ = a * q := by
    dsimp [a]
    rw [commutatorElement_def]
    group
  let c : G := x * a * x⁻¹
  have hcA : c ∈ A := (Subgroup.mem_normalizer_iff.mp hxNA a).mp haA
  have hcQ : c ∈ Q := hAQ hcA
  let q1 : G := x * q * x⁻¹
  have hq1Q : q1 ∈ Q := by
    dsimp [q1]
    exact (Subgroup.mem_normalizer_iff.mp hxNQ q).mp hqQ
  let q2 : G := x * q1 * x⁻¹
  have hq2Q : q2 ∈ Q := by
    dsimp [q2]
    exact (Subgroup.mem_normalizer_iff.mp hxNQ q1).mp hq1Q
  let q' : G := q * q1 * q2
  have hq'Q : q' ∈ Q := by
    dsimp [q']
    exact Q.mul_mem (Q.mul_mem hqQ hq1Q) hq2Q
  have hq1 : q1 = a * q := hq1eq
  have hq2 : q2 = c * q1 := by
    dsimp [q2, c]
    conv_lhs => rw [hq1]
    dsimp [q1]
    group
  have hx3pow : x ^ 3 = 1 := by
    rw [← hx3]
    exact pow_orderOf_eq_one x
  have hx3' : x * (x * x) = 1 := by simpa [pow_three] using hx3pow
  have hxinv3 : (x⁻¹ * x⁻¹) * x⁻¹ = 1 := by
    simpa using congrArg Inv.inv hx3'
  have hq3 : x * q2 * x⁻¹ = q := by
    dsimp [q2, q1]
    calc
      x * (x * (x * q * x⁻¹) * x⁻¹) * x⁻¹ =
          (x * (x * x)) * q * ((x⁻¹ * x⁻¹) * x⁻¹) := by group
      _ = q := by rw [hx3', hxinv3]; group
  have hfixed : x * q' * x⁻¹ = q' := by
    calc
      x * q' * x⁻¹ = q1 * q2 * (x * q2 * x⁻¹) := by
        dsimp [q', q1, q2]
        group
      _ = q1 * q2 * q := by rw [hq3]
      _ = q * q1 * q2 := by
        rw [mul_assoc, hQcomm hq2Q hqQ, ← mul_assoc, hQcomm hq1Q hqQ]
  have hq'1 : q' = 1 := hfix q' hq'Q hfixed
  have hq'form : q' = q * (a * q) * (c * (a * q)) := by
    dsimp [q']
    rw [hq2, hq1]
  have hmemL : q * (a * q) * (c * (a * q)) ∈ Q :=
    Q.mul_mem (Q.mul_mem hqQ (Q.mul_mem haQ hqQ))
      (Q.mul_mem hcQ (Q.mul_mem haQ hqQ))
  have hsub : (⟨q * (a * q) * (c * (a * q)), hmemL⟩ : ↥Q) =
      (⟨q * c, Q.mul_mem hqQ hcQ⟩ : ↥Q) := by
    haveI : IsMulCommutative ↥Q := hQab
    letI : CommGroup ↥Q := IsMulCommutative.instCommGroup
    change (⟨q, hqQ⟩ : ↥Q) * (⟨a, haQ⟩ * ⟨q, hqQ⟩) *
        (⟨c, hcQ⟩ * (⟨a, haQ⟩ * ⟨q, hqQ⟩)) =
      (⟨q, hqQ⟩ : ↥Q) * ⟨c, hcQ⟩
    have hqsq : (⟨q, hqQ⟩ : ↥Q) * ⟨q, hqQ⟩ = 1 := Subtype.ext (hQ2 q hqQ)
    have hasq : (⟨a, haQ⟩ : ↥Q) * ⟨a, haQ⟩ = 1 := Subtype.ext (hQ2 a haQ)
    calc
      (⟨q, hqQ⟩ : ↥Q) * (⟨a, haQ⟩ * ⟨q, hqQ⟩) *
          (⟨c, hcQ⟩ * (⟨a, haQ⟩ * ⟨q, hqQ⟩)) =
          ((⟨q, hqQ⟩ : ↥Q) * ⟨q, hqQ⟩) *
            ((⟨a, haQ⟩ : ↥Q) * ⟨a, haQ⟩) *
            ((⟨q, hqQ⟩ : ↥Q) * ⟨c, hcQ⟩) := by ac_rfl
      _ = (⟨q, hqQ⟩ : ↥Q) * ⟨c, hcQ⟩ := by rw [hqsq, hasq]; simp
  have hq'c : q' = q * c := by
    rw [hq'form]
    exact congrArg Subtype.val hsub
  have hqc : q * c = 1 := by rw [← hq'c, hq'1]
  have hq_eq : q = c⁻¹ := (inv_eq_of_mul_eq_one_left hqc).symm
  rw [hq_eq]
  exact A.inv_mem hcA

theorem exists_orderOf_eq_three_of_not_le_of_relIndex_nine [Finite G] {K S R : Subgroup G}
    (hrel : S.relIndex K = 9) (hSnorm : (S.subgroupOf K).Normal)
    (hRK : R ≤ K) (hRnotS : ¬ R ≤ S) (hS2 : IsPGroup 2 S) :
    ∃ r ∈ R, orderOf r = 3 ∧ r ∉ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : (S.subgroupOf K).Normal := hSnorm
  let π : ↥K →* (↥K ⧸ S.subgroupOf K) := QuotientGroup.mk' (S.subgroupOf K)
  have hRnotSub : ¬ R.subgroupOf K ≤ S.subgroupOf K := by
    intro hle
    apply hRnotS
    intro r hr
    have hxK : (⟨r, hRK hr⟩ : ↥K) ∈ R.subgroupOf K := Subgroup.mem_subgroupOf.mpr hr
    exact Subgroup.mem_subgroupOf.mp (hle hxK)
  obtain ⟨x, hxR, hxS⟩ := SetLike.not_le_iff_exists.mp hRnotSub
  have hxK : (x : G) ∈ K := x.2
  have hyR : (x : G) ∈ R := Subgroup.mem_subgroupOf.mp hxR
  have hyS : (x : G) ∉ S := fun h => hxS (Subgroup.mem_subgroupOf.mpr h)
  have hπne : π x ≠ 1 := by
    intro h1
    exact hxS ((QuotientGroup.eq_one_iff (N := S.subgroupOf K) x).mp h1)
  have hcardQ : Nat.card (↥K ⧸ S.subgroupOf K) = 9 := hrel
  have hmdvd : orderOf (π x) ∣ 9 := by
    have := orderOf_dvd_natCard (π x)
    rwa [hcardQ] at this
  have hmne : orderOf (π x) ≠ 1 := by
    intro h
    exact hπne (orderOf_eq_one_iff.mp h)
  have hm : orderOf (π x) = 3 ∨ orderOf (π x) = 9 := by
    have hmem : orderOf (π x) ∈ Nat.divisors 9 := by
      rw [Nat.mem_divisors]
      exact ⟨hmdvd, by norm_num⟩
    have h9 : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [h9] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · exact absurd h hmne
    · exact Or.inl h
    · exact Or.inr h
  let z : G := (x : G) ^ (orderOf (π x) / 3)
  have hzR : z ∈ R := R.pow_mem hyR _
  have hzK : z ∈ K := hRK hzR
  have hzpow : π ⟨z, hzK⟩ = (π x) ^ (orderOf (π x) / 3) := by
    dsimp [z]
    rw [show (⟨(x : G) ^ (orderOf (π x) / 3), hzK⟩ : ↥K) =
        x ^ (orderOf (π x) / 3) from Subtype.ext rfl, map_pow]
  have hπz3 : orderOf (π ⟨z, hzK⟩) = 3 := by
    rw [hzpow]
    rcases hm with hm | hm
    · simpa [hm]
    · rw [orderOf_pow, hm]
      norm_num
  have hπzne : π ⟨z, hzK⟩ ≠ 1 := by
    intro h1
    have hord : orderOf (π ⟨z, hzK⟩) = 1 := by rw [h1]; simp
    rw [hπz3] at hord
    norm_num at hord
  have hznS : z ∉ S := by
    intro hzS
    have h1 : π ⟨z, hzK⟩ = 1 := by
      simpa [π, QuotientGroup.mk'_apply] using
        ((QuotientGroup.eq_one_iff (N := S.subgroupOf K) ⟨z, hzK⟩).mpr
          (Subgroup.mem_subgroupOf.mpr hzS))
    exact hπzne h1
  have hz3S : z ^ 3 ∈ S := by
    have h1 : π ⟨z ^ 3, K.pow_mem hzK 3⟩ = 1 := by
      rw [show (⟨z ^ 3, K.pow_mem hzK 3⟩ : ↥K) = ⟨z, hzK⟩ ^ 3 from Subtype.ext rfl,
        map_pow]
      rw [← hπz3]
      exact pow_orderOf_eq_one _
    exact Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (N := S.subgroupOf K) ⟨z ^ 3, K.pow_mem hzK 3⟩).mp h1)
  have h3dvdn : 3 ∣ orderOf z := by
    have h := orderOf_map_dvd π ⟨z, hzK⟩
    rw [hπz3, Subgroup.orderOf_mk] at h
    exact h
  obtain ⟨b, hb⟩ := hS2.exists_orderOf_eq_pow ⟨z ^ 3, hz3S⟩
  rw [Subgroup.orderOf_mk] at hb
  have hqord : orderOf (z ^ 3) = orderOf z / 3 := by
    rw [orderOf_pow, Nat.gcd_eq_right h3dvdn]
  have hb' : orderOf z / 3 = 2 ^ b := by rw [← hqord, hb]
  refine ⟨z ^ (orderOf z / 3), R.pow_mem hzR _,
    orderOf_pow_orderOf_div (orderOf_pos z).ne' h3dvdn, ?_⟩
  intro hrS
  have hdvd : 3 ∣ Nat.card S := by
    have h := orderOf_dvd_natCard
      (⟨z ^ (orderOf z / 3), hrS⟩ : ↥S)
    rw [Subgroup.orderOf_mk, orderOf_pow_orderOf_div (orderOf_pos z).ne' h3dvdn] at h
    exact h
  obtain ⟨nS, hnS⟩ := hS2.exists_card_eq
  rw [hnS] at hdvd
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)

theorem mem_normalizer_of_conjugator_mod [Finite G] {K L Q S : Subgroup G}
    (hSL : S ≤ L) (hKN : K ≤ Subgroup.normalizer (S : Set G))
    (hQS : Q ≤ S) {x g : G} (hxK : x ∈ K)
    (hconj : ∀ l ∈ L, x * l * x⁻¹ * (g * l * g⁻¹)⁻¹ ∈ Q) :
    g ∈ Subgroup.normalizer (S : Set G) := by
  classical
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : S.map (MulAut.conj g).toMonoidHom ≤ S := by
    rintro _ ⟨s, hs, rfl⟩
    change g * s * g⁻¹ ∈ S
    have hsL : s ∈ L := hSL hs
    have hq := hconj s hsL
    have hA : x * s * x⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hKN hxK) s).mp hs
    have hqS : x * s * x⁻¹ * (g * s * g⁻¹)⁻¹ ∈ S := hQS hq
    have hB : g * s * g⁻¹ =
        (x * s * x⁻¹ * (g * s * g⁻¹)⁻¹)⁻¹ * (x * s * x⁻¹) := by group
    rw [hB]
    exact S.mul_mem (S.inv_mem hqS) hA
  have hcard : Nat.card ↥(S.map (MulAut.conj g).toMonoidHom) = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)

theorem fixedPointFree_of_inf_centralizer_eq_bot {Q : Subgroup G} {c : G}
    (h : Q ⊓ Subgroup.centralizer ({c} : Set G) = ⊥) :
    ∀ q ∈ Q, c * q * c⁻¹ = q → q = 1 := by
  intro q hq hfix
  have hqC : q ∈ Q ⊓ Subgroup.centralizer ({c} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hq, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc q * c = (c * q * c⁻¹) * c := by rw [hfix]
      _ = c * q := by group
  simpa [h] using hqC

end CFSG.GroupTheory
