module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113a
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma104a
public import CFSG.RankThree.PartTwo.KFacts.KS10L27Aut
public import CFSG.Dihedral.Glauberman.DicksonMaxExist

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open scoped MatrixGroups Pointwise

namespace Lemma113c

variable {G : Type} [Group G] [Finite G]

theorem mem_centerOf_iff {Q : Subgroup G} {x : G} :
    x ∈ centerOf Q ↔ x ∈ Q ∧ ∀ q ∈ Q, q * x = x * q := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine ⟨y.2, fun q hq => ?_⟩
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hy) ⟨q, hq⟩)
  · rintro ⟨hxQ, hc⟩
    refine Subgroup.mem_map.2 ⟨⟨x, hxQ⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g.1 g.2)

theorem mem_of_central_order_three {Q E : Subgroup G} (hE : IsSCp 3 ⊤ E) (hEQ : E ≤ Q)
    {z : G} (hzc : ∀ q ∈ Q, q * z = z * q) (hz3 : z ^ 3 = 1) : z ∈ E := by
  have hzE : IsElemAbelian 3 (Subgroup.zpowers z) := l113_isElemAbelian_zpowers hz3
  have hcent : E ≤ Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
    intro c hc
    exact l113_mem_centralizer_zpowers (hzc c (hEQ hc)).symm
  have hsup := isElemAbelian_sup_of_commute hE.2.1 hzE hcent
  have heq := hE.2.2 (E ⊔ Subgroup.zpowers z) le_top hsup le_sup_left
  have hzmem : z ∈ E ⊔ Subgroup.zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  rw [heq] at hzmem
  exact hzmem

theorem omegaOne_centerOf_le {Q E A : Subgroup G} (hEmax : IsSCp 3 ⊤ E) (hEQ : E ≤ Q)
    (hAmax : IsSCp 3 ⊤ A) (hAQ : A ≤ Q) :
    omegaOne 3 (centerOf Q) ≤ E ⊓ A := by
  unfold omegaOne
  rw [Subgroup.closure_le]
  rintro x ⟨hx, hx3⟩
  obtain ⟨hxQ, hc⟩ := mem_centerOf_iff.1 hx
  exact ⟨mem_of_central_order_three hEmax hEQ hc hx3,
    mem_of_central_order_three hAmax hAQ hc hx3⟩

theorem exists_central_order_three [Fact (Nat.Prime 3)] {Q P : Subgroup G} (hQ : IsPGroup 3 ↥Q)
    (hPQ : P ≤ Q) (hPn : ∀ q ∈ Q, ∀ p ∈ P, q * p * q⁻¹ ∈ P) (hPbot : P ≠ ⊥) :
    ∃ z ∈ P, z ^ 3 = 1 ∧ z ≠ 1 ∧ ∀ q ∈ Q, q * z = z * q := by
  classical
  let P' : Subgroup ↥Q := P.subgroupOf Q
  have hP'n : P'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ P := hn
    have := hPn g.1 g.2 n hn'
    exact this
  have hP'ne : P' ≠ ⊥ := by
    intro h
    apply hPbot
    ext x
    constructor
    · intro hx
      have : (⟨x, hPQ hx⟩ : ↥Q) ∈ P' := Subgroup.mem_subgroupOf.2 hx
      rw [h, Subgroup.mem_bot] at this
      have hx0 : x = 1 := congrArg Subtype.val this
      simp [hx0]
    · intro hx
      rw [Subgroup.mem_bot] at hx
      simp [hx]
  haveI : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hP'ne
  set K0 : Subgroup ↥Q := P' ⊓ Subgroup.center ↥Q with hK0def
  have hK0p : IsPGroup 3 ↥K0 := hQ.to_subgroup K0
  have h1 : 1 < Nat.card ↥K0 := (Subgroup.one_lt_card_iff_ne_bot K0).2 hcen
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).1 hK0p
  have hn1 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    omega
  have hdvd : 3 ∣ Nat.card ↥K0 := by
    rw [hn]
    exact dvd_pow_self 3 hn1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K0) 3 hdvd
  have hxK : (x : ↥Q) ∈ K0 := x.2
  obtain ⟨hxP', hxZ⟩ := Subgroup.mem_inf.1 hxK
  have hx3K : x ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hx]
  have hx3 : ((x : ↥Q) : G) ^ 3 = 1 := by
    have := congrArg (fun y : ↥K0 => ((y : ↥Q) : G)) hx3K
    simpa using this
  refine ⟨((x : ↥Q) : G), Subgroup.mem_subgroupOf.1 hxP', hx3, ?_, ?_⟩
  · intro h
    have h1' : x = 1 := Subtype.ext (Subtype.ext h)
    rw [h1', orderOf_one] at hx
    exact absurd hx (by norm_num)
  · intro q hq
    have hz := (Subgroup.mem_center_iff.1 hxZ) ⟨q, hq⟩
    exact congrArg Subtype.val hz

theorem pRank_inter_eq_two [Fact (Nat.Prime 3)] {E A : Subgroup G} (hEmax : IsSCp 3 ⊤ E)
    (hAmax : IsSCp 3 ⊤ A) (hE4 : CFSG.Open.pRank 3 E = 4) (hA3 : CFSG.Open.pRank 3 A = 3)
    (h2 : 2 ≤ CFSG.Open.pRank 3 (E ⊓ A)) : CFSG.Open.pRank 3 (E ⊓ A) = 2 := by
  refine le_antisymm ?_ h2
  by_contra hlt
  have hge : 3 ≤ CFSG.Open.pRank 3 (E ⊓ A) := by omega
  obtain ⟨V, hVle, hVel, hVc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (E ⊓ A)
  have hV27 : 3 ^ 3 ≤ Nat.card V := by
    rw [hVc]
    exact Nat.pow_le_pow_right (by norm_num) hge
  have hAc : Nat.card A = 3 ^ 3 := by
    rw [l113_card_eq_pow_pRank hAmax.2.1, hA3]
  have hVA : V ≤ A := hVle.trans inf_le_right
  have hVeqA : V = A := Subgroup.eq_of_le_of_card_ge hVA (by rw [hAc]; exact hV27)
  have hAE : A ≤ E := by
    rw [← hVeqA]
    exact hVle.trans inf_le_left
  have hEA : E = A := hAmax.2.2 E le_top hEmax.2.1 hAE
  have : CFSG.Open.pRank 3 E = CFSG.Open.pRank 3 A := by rw [hEA]
  omega

theorem omegaOne_centerOf_eq [Fact (Nat.Prime 3)] {Q E A P : Subgroup G} {e : G}
    (hEmax : IsSCp 3 ⊤ E) (hAmax : IsSCp 3 ⊤ A) (hEQ : E ≤ Q) (hAQ : A ≤ Q)
    (hQ : IsPGroup 3 ↥Q) (hrk : CFSG.Open.pRank 3 (E ⊓ A) = 2)
    (he : e ∈ E ⊓ A) (he1 : e ≠ 1) (hePc : ∀ q ∈ Q, q * e = e * q)
    (hPQ : P ≤ Q) (hPn : ∀ q ∈ Q, ∀ p ∈ P, q * p * q⁻¹ ∈ P) (hPbot : P ≠ ⊥) (heP : e ∉ P) :
    omegaOne 3 (centerOf Q) = E ⊓ A := by
  apply le_antisymm (omegaOne_centerOf_le hEmax hEQ hAmax hAQ)
  obtain ⟨z, hzP, hz3, hz1, hzc⟩ := exists_central_order_three hQ hPQ hPn hPbot
  have hzQ : z ∈ Q := hPQ hzP
  have he3 : e ^ 3 = 1 := hEmax.2.1.2 e he.1
  have heQ : e ∈ Q := hEQ he.1
  have hzZ : z ∈ omegaOne 3 (centerOf Q) :=
    Subgroup.subset_closure ⟨mem_centerOf_iff.2 ⟨hzQ, hzc⟩, hz3⟩
  have heZ : e ∈ omegaOne 3 (centerOf Q) :=
    Subgroup.subset_closure ⟨mem_centerOf_iff.2 ⟨heQ, hePc⟩, he3⟩
  have hze : z ∈ E ⊓ A := omegaOne_centerOf_le hEmax hEQ hAmax hAQ hzZ
  have hcard_e : Nat.card (Subgroup.zpowers e) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime he3 he1]
  have hz_ne_e : z ∉ Subgroup.zpowers e := by
    intro hz
    have hle : Subgroup.zpowers z ≤ Subgroup.zpowers e := Subgroup.zpowers_le.2 hz
    have hcard_z : Nat.card (Subgroup.zpowers z) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1]
    have heq : Subgroup.zpowers z = Subgroup.zpowers e :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard_z, hcard_e])
    have heP' : e ∈ P := by
      have hmem : e ∈ Subgroup.zpowers z := by
        rw [heq]
        exact Subgroup.mem_zpowers e
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hmem
      exact P.zpow_mem hzP k
    exact heP heP'
  have hcomm_ez : e * z = z * e := hzc e heQ
  have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    exact l113_mem_centralizer_zpowers hcomm_ez
  have hcardH : Nat.card (Subgroup.zpowers e ⊔ Subgroup.zpowers z : Subgroup G) = 3 * 3 := by
    rw [l113_card_sup_zpowers (Subgroup.zpowers e) hz3 hz1 hz_ne_e hnorm, hcard_e]
  have hEAel : IsElemAbelian 3 (E ⊓ A) := isElemAbelian_of_le' hEmax.2.1 inf_le_left
  have hcard_EA : Nat.card (E ⊓ A : Subgroup G) = 3 * 3 := by
    rw [l113_card_eq_pow_pRank hEAel, hrk]
    norm_num
  have hHle : Subgroup.zpowers e ⊔ Subgroup.zpowers z ≤ E ⊓ A :=
    sup_le (Subgroup.zpowers_le.2 he.1 |> fun _ => by
      exact Subgroup.zpowers_le.2 he) (Subgroup.zpowers_le.2 hze)
  have hEA_eq : Subgroup.zpowers e ⊔ Subgroup.zpowers z = E ⊓ A :=
    Subgroup.eq_of_le_of_card_ge hHle (by rw [hcard_EA, hcardH])
  have hHZ : Subgroup.zpowers e ⊔ Subgroup.zpowers z ≤ omegaOne 3 (centerOf Q) :=
    sup_le (Subgroup.zpowers_le.2 heZ) (Subgroup.zpowers_le.2 hzZ)
  rw [← hEA_eq]
  exact hHZ

theorem le_M_of_centre {M Q E A : Subgroup G} (hU : IsUniquenessTwoLocal 3 E M)
    (hZ : omegaOne 3 (centerOf Q) = E ⊓ A) (hrk : CFSG.Open.pRank 3 (E ⊓ A) = 2) : Q ≤ M := by
  have hcentQ : omegaOne 3 (centerOf Q) ≤ Subgroup.centralizer (Q : Set G) := by
    unfold omegaOne
    rw [Subgroup.closure_le]
    rintro x ⟨hx, _⟩
    obtain ⟨hxQ, hc⟩ := mem_centerOf_iff.1 hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro q hq
    exact hc q hq
  have hQZ : Q ≤ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) := by
    intro q hq
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ omegaOne 3 (centerOf Q) := by rw [hZ]; exact hz
    have := Subgroup.mem_centralizer_iff.1 (hcentQ hz') q (by simpa using hq)
    exact this.symm
  have hGLB : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ GLBCore 3 2 E :=
    le_sSup ⟨E ⊓ A, inf_le_left, le_of_eq hrk.symm, rfl⟩
  exact (hQZ.trans hGLB).trans hU.clause_d

section Product

variable {Y : Type} [Group Y]

open Classical in
theorem product_structure [Finite Y] [Fact (Nat.Prime 3)] (𝒮 : Finset (Subgroup Y)) :
    (∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ≠ T → ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) →
    (∀ S ∈ 𝒮, ∀ z ∈ S, (∀ s ∈ S, s * z = z * s) → z = 1) →
    (∀ S ∈ 𝒮, ∃ E : Subgroup Y, E ≤ S ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      ∃ m : ℕ, Nat.card S = 27 * m ∧ ¬ 3 ∣ m) →
    (∀ z ∈ 𝒮.sup id, (∀ g ∈ 𝒮.sup id, g * z = z * g) → z = 1) ∧
    ∃ E : Subgroup Y, E ≤ 𝒮.sup id ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ^ 𝒮.card ∧
      ∃ m : ℕ, Nat.card (𝒮.sup id : Subgroup Y) = 27 ^ 𝒮.card * m ∧ ¬ 3 ∣ m := by
  induction 𝒮 using Finset.induction_on with
  | empty =>
    intro _ _ _
    have hbot : IsElemAbelian 3 (⊥ : Subgroup Y) := by
      have h1 : ∀ x : (⊥ : Subgroup Y), (x : Y) = 1 := fun x => Subgroup.mem_bot.1 x.2
      exact ⟨⟨⟨fun x y => Subtype.ext (by simp [h1 x, h1 y])⟩⟩, fun x hx => by
        rw [Subgroup.mem_bot.1 hx, one_pow]⟩
    refine ⟨fun z hz _ => ?_, ⊥, bot_le, hbot, by simp, 1, by simp, by norm_num⟩
    rw [Finset.sup_empty, Subgroup.mem_bot] at hz
    exact hz
  | insert S 𝒮' hS ih =>
    intro hcomm hcen hsyl
    simp only [Finset.sup_insert, id_eq]
    have hcomm' : ∀ S' ∈ 𝒮', ∀ T ∈ 𝒮', S' ≠ T → ∀ s ∈ S', ∀ t ∈ T, s * t = t * s :=
      fun S' h1 T h2 hne => hcomm S' (Finset.mem_insert_of_mem h1) T (Finset.mem_insert_of_mem h2) hne
    have hcen' : ∀ S' ∈ 𝒮', ∀ z ∈ S', (∀ s ∈ S', s * z = z * s) → z = 1 :=
      fun S' h1 => hcen S' (Finset.mem_insert_of_mem h1)
    have hsyl' : ∀ S' ∈ 𝒮', ∃ E : Subgroup Y, E ≤ S' ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
        ∃ m : ℕ, Nat.card S' = 27 * m ∧ ¬ 3 ∣ m :=
      fun S' h1 => hsyl S' (Finset.mem_insert_of_mem h1)
    obtain ⟨ihcen, E', hE'le, hE'el, hE'card, m', hm'card, hm'⟩ := ih hcomm' hcen' hsyl'
    have hSY : (𝒮'.sup id : Subgroup Y) ≤ Subgroup.centralizer (S : Set Y) := by
      refine Finset.sup_le ?_
      intro T hT
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hne : S ≠ T := fun h => hS (h ▸ hT)
      exact hcomm S (Finset.mem_insert_self S 𝒮') T (Finset.mem_insert_of_mem hT) hne s hs t ht
    have hSYc : ∀ s ∈ S, ∀ y ∈ (𝒮'.sup id : Subgroup Y), s * y = y * s := fun s hs y hy =>
      Subgroup.mem_centralizer_iff.1 (hSY hy) s hs
    have hSY' : S ≤ Subgroup.centralizer ((𝒮'.sup id : Subgroup Y) : Set Y) := fun s hs =>
      Subgroup.mem_centralizer_iff.2 (fun h hh => (hSYc s hs h hh).symm)
    have hinf : S ⊓ (𝒮'.sup id : Subgroup Y) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxS, hxY⟩
      rw [Subgroup.mem_bot]
      exact hcen S (Finset.mem_insert_self S 𝒮') x hxS (fun s hs => hSYc s hs x hxY)
    have hnorm : (𝒮'.sup id : Subgroup Y) ≤ Subgroup.normalizer (S : Set Y) :=
      hSY.trans (Subgroup.centralizer_le_normalizer (S : Set Y))
    have hcard_join : Nat.card (S ⊔ 𝒮'.sup id : Subgroup Y) =
        Nat.card S * Nat.card (𝒮'.sup id : Subgroup Y) := by
      have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hnorm
      rw [hinf, Subgroup.card_bot, mul_one] at h
      exact h
    have hcenNew : ∀ z ∈ S ⊔ 𝒮'.sup id, (∀ g ∈ S ⊔ 𝒮'.sup id, g * z = z * g) → z = 1 := by
      intro z hz hzc
      obtain ⟨s, hs, y, hy, rfl⟩ := exists_mul_of_mem_sup hSY' hz
      have hyc : ∀ t ∈ (𝒮'.sup id : Subgroup Y), y * t = t * y := by
        intro t ht
        have h1 : t * (s * y) = s * y * t := hzc t (Subgroup.mem_sup_right ht)
        have hst : s * t = t * s := hSYc s hs t ht
        have h2 : s * (y * t) = s * (t * y) := by
          calc s * (y * t) = s * y * t := by group
            _ = t * (s * y) := h1.symm
            _ = t * s * y := by group
            _ = s * t * y := by rw [hst.symm]
            _ = s * (t * y) := by group
        exact mul_left_cancel h2
      have hy1 : y = 1 := ihcen y hy (fun g hg => (hyc g hg).symm)
      subst hy1
      have hsc : ∀ g ∈ S, g * s = s * g := by
        intro g hg
        have := hzc g (Subgroup.mem_sup_left hg)
        simpa using this
      have hs1 : s = 1 := hcen S (Finset.mem_insert_self S 𝒮') s hs hsc
      simp [hs1]
    obtain ⟨E_S, hESle, hESel, hEScard, m_S, hmS, hmS'⟩ := hsyl S (Finset.mem_insert_self S 𝒮')
    have hES' : E_S ≤ Subgroup.centralizer (E' : Set Y) := fun s hs =>
      Subgroup.mem_centralizer_iff.2 (fun h hh => (hSYc s (hESle hs) h (hE'le hh)).symm)
    have hEel : IsElemAbelian 3 (E_S ⊔ E') := isElemAbelian_sup_of_commute hESel hE'el hES'
    have hEinf : E_S ⊓ E' = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxS, hxE⟩
      rw [Subgroup.mem_bot]
      have hxS' : x ∈ S ⊓ (𝒮'.sup id : Subgroup Y) := ⟨hESle hxS, hE'le hxE⟩
      rw [hinf] at hxS'
      exact hxS'
    have hE'norm : E' ≤ Subgroup.normalizer (E_S : Set Y) := by
      intro y hy
      refine Subgroup.centralizer_le_normalizer (E_S : Set Y) ?_
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact hSYc s (hESle hs) y (hE'le hy)
    have hcardEE : Nat.card (E_S ⊔ E' : Subgroup Y) = Nat.card E_S * Nat.card E' := by
      have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hE'norm
      rw [hEinf, Subgroup.card_bot, mul_one] at h
      exact h
    refine ⟨hcenNew, E_S ⊔ E', sup_le_sup hESle hE'le, hEel, ?_, m_S * m', ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hS, pow_succ, hcardEE, hEScard, hE'card, mul_comm]
    · rw [hcard_join, hmS, hm'card, Finset.card_insert_of_notMem hS, pow_succ]
      ring
    · intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h1 | h1
      · exact hmS' h1
      · exact hm' h1

end Product

section Psl2

open CFSG.GorensteinWalter

private theorem three_part_of_9828 {c k : ℕ} (hn : 9828 = 3 ^ k * c) (hc : ¬ 3 ∣ c) : k = 3 := by
  have hk : k < 9 := by
    by_contra h
    push Not at h
    have h1 : 3 ^ 9 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0] at hn
        norm_num at hn
      · exact h0
    have h2 : 3 ^ k ≤ 9828 := by
      calc 3 ^ k ≤ 3 ^ k * c := Nat.le_mul_of_pos_right _ hcpos
        _ = 9828 := hn.symm
    norm_num at h1
    omega
  interval_cases k <;> norm_num at hn <;> omega

theorem isElemAbelian_map_of_injective {H K : Type} [Group H] [Group K] {p : ℕ}
    {A : Subgroup H} (f : H →* K) (hf : Function.Injective f) (hA : IsElemAbelian p A) :
    IsElemAbelian p (A.map f) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.1 y.2
    have hcomm : a * b = b * a := congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    show (x : K) * (y : K) = (y : K) * (x : K)
    rw [← hax, ← hby, ← map_mul, ← map_mul, hcomm]
  · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 hx
    show (x : K) ^ p = 1
    rw [← hax, ← map_pow, hA.2 a ha, map_one]

theorem psl2_27_centre {H : Type} [Group H] (e : H ≃* PSL2 (GaloisField 3 3)) :
    ∀ z : H, (∀ s : H, s * z = z * s) → z = 1 := by
  intro z hz
  have hmem : e z ∈ Subgroup.center (PSL2 (GaloisField 3 3)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨s, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hz s]
  rw [psl2_center_eq_bot, Subgroup.mem_bot] at hmem
  exact e.injective (by rw [hmem, map_one])

theorem psl2_27_card {H : Type} [Group H] (e : H ≃* PSL2 (GaloisField 3 3)) :
    Nat.card H = 27 * 364 := by
  rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.KFacts.card_psl2_27]

theorem psl2_27_sylow {H : Type} [Group H] (e : H ≃* PSL2 (GaloisField 3 3)) :
    ∃ E : Subgroup H, IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : Nat.card (GaloisField 3 3) = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  let T : Sylow 3 (PSL2 (GaloisField 3 3)) := default
  let T' : Subgroup (PSL2 (GaloisField 3 3)) := T
  have hTel : IsElemAbelian 3 T' := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => CFSG.Glauberman.Dickson.psl2_pow_eq_one_of_mem_sylow hF T hx⟩
    exact CFSG.Glauberman.Dickson.psl2_mul_comm_of_mem_sylow hF T x.2 y.2
  have hcard_T : Nat.card T' = 3 ^ 3 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).1 T.isPGroup'
    have hidx := Subgroup.card_eq_card_quotient_mul_card_subgroup T'
    have hcop : Nat.Coprime (Nat.card ↥T') T'.index := Sylow.card_coprime_index T
    have hne : T' ≠ ⊥ := by
      have hdvd : 3 ∣ Nat.card (PSL2 (GaloisField 3 3)) := by
        rw [CFSG.RankThree.PartTwo.KFacts.card_psl2_27]
        norm_num
      exact Sylow.ne_bot_of_dvd_card T hdvd
    have hk1 : k ≠ 0 := by
      rintro rfl
      apply hne
      rw [← Subgroup.card_eq_one, hk, pow_zero]
    have hc : ¬ 3 ∣ T'.index := by
      intro h
      have h3 : 3 ∣ Nat.card ↥T' := by
        rw [hk]
        exact dvd_pow_self 3 hk1
      have h1 : 3 ∣ Nat.gcd (Nat.card ↥T') T'.index := Nat.dvd_gcd h3 h
      rw [Nat.Coprime.gcd_eq_one hcop] at h1
      norm_num at h1
    have h9828 : (9828 : ℕ) = 3 ^ k * T'.index := by
      rw [← CFSG.RankThree.PartTwo.KFacts.card_psl2_27, hidx, hk, mul_comm]
      rfl
    have hk3 := three_part_of_9828 h9828 hc
    rw [hk, hk3]
  refine ⟨T'.map e.symm.toMonoidHom, isElemAbelian_map_of_injective _ e.symm.injective hTel, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective, hcard_T]
  norm_num

end Psl2

abbrev Y0X {G : Type} [Group G] (X : Subgroup G) : Type := ↥X ⧸ GLAPPrimeCore 3 ↥X

theorem pow_three_eq_of_mul {i j a b : ℕ} (h : 3 ^ i * a = 3 ^ j * b) (ha : ¬ 3 ∣ a)
    (hb : ¬ 3 ∣ b) : i = j := by
  have ha0 : a ≠ 0 := fun h0 => ha (by rw [h0]; exact dvd_zero 3)
  have hb0 : b ≠ 0 := fun h0 => hb (by rw [h0]; exact dvd_zero 3)
  have := congrArg (padicValNat 3) h
  rw [padicValNat.mul (pow_ne_zero _ (by norm_num)) ha0,
    padicValNat.mul (pow_ne_zero _ (by norm_num)) hb0,
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd ha,
    padicValNat.eq_zero_of_not_dvd hb] at this
  omega

theorem relIndex_not_three_dvd {Y : Type} [Group Y] [Finite Y] {N Q : Subgroup Y} [N.Normal]
    {k : ℕ} (hY : Nat.card Y = Nat.card Q * k) (hk : ¬ 3 ∣ k) : ¬ 3 ∣ Q.relIndex N := by
  have hQN : Q ≤ Subgroup.normalizer (N : Set Y) := by
    rw [Subgroup.normalizer_eq_top N]
    exact le_top
  have hc1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hQN
  have hc2 := Subgroup.relIndex_mul_card (H := Q) (K := N)
  have hdvd : Nat.card ↥(N ⊔ Q) ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card _
  have hcpos : 0 < Nat.card ↥(Q ⊓ N : Subgroup Y) := Nat.card_pos
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hJ : Nat.card ↥(N ⊔ Q) = Nat.card Q * Q.relIndex N := by
    have h1 : Nat.card ↥(N ⊔ Q) * Nat.card ↥(N ⊓ Q) = Nat.card N * Nat.card Q := hc1
    have h2 : Q.relIndex N * Nat.card ↥(Q ⊓ N) = Nat.card N := hc2
    have hinf : (N ⊓ Q : Subgroup Y) = Q ⊓ N := inf_comm N Q
    rw [hinf] at h1
    have hpos : 0 < Nat.card ↥(Q ⊓ N : Subgroup Y) := hcpos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, ← h2]
    ring
  rw [hJ, hY] at hdvd
  have hk' : Q.relIndex N ∣ k := by
    have := Nat.dvd_of_mul_dvd_mul_left hQpos hdvd
    exact this
  exact fun h => hk (h.trans hk')

theorem isElemAbelian_of_sylow_conj {H : Type} [Group H] [Finite H] [Fact (Nat.Prime 3)]
    {P E : Subgroup H} (hE : IsElemAbelian 3 E) (hPp : IsPGroup 3 P)
    (hPidx : ¬ 3 ∣ P.index) (hEidx : ¬ 3 ∣ E.index) : IsElemAbelian 3 P := by
  have hEp : IsPGroup 3 E := isPGroup_of_isElemAbelian' hE
  let P1 : Sylow 3 H := hPp.toSylow hPidx
  let P2 : Sylow 3 H := hEp.toSylow hEidx
  have hmem : P1 ∈ MulAction.orbit H P2 := by
    rw [Sylow.orbit_eq_top]
    exact Set.mem_univ _
  obtain ⟨g, hg⟩ := hmem
  have hcoe : (P : Subgroup H) = MulAut.conj g • (E : Subgroup H) := by
    have := congrArg (fun S : Sylow 3 H => (S : Subgroup H)) hg
    simp only at this
    rw [Sylow.coe_subgroup_smul] at this
    exact this.symm
  rw [hcoe, Subgroup.pointwise_smul_def]
  exact isElemAbelian_map_of_injective _ (MulAut.conj g).injective hE

theorem isSylowIn_card_index {X Q : Subgroup G} (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥) :
    ∃ k : ℕ, Nat.card ↥X = Nat.card ↥Q * k ∧ ¬ 3 ∣ k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQX : Q ≤ X := hQ.1
  have hQ'p : IsPGroup 3 ↥(Q.subgroupOf X) :=
    hQ.2.1.of_injective (Subgroup.subgroupOfEquivOfLe hQX).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQX).injective
  obtain ⟨R, hR⟩ := hQ'p.exists_le_sylow
  have hRX : (R : Subgroup ↥X).map X.subtype ≤ X := Subgroup.map_subtype_le _
  have hRmap : (R : Subgroup ↥X).map X.subtype = Q := by
    apply hQ.2.2 _ hRX
    · exact R.isPGroup'.map X.subtype
    · intro q hq
      exact Subgroup.mem_map.2 ⟨⟨q, hQX hq⟩, hR (Subgroup.mem_subgroupOf.2 hq), rfl⟩
  have hcardR : Nat.card ↥(R : Subgroup ↥X) = Nat.card ↥Q := by
    have h1 : Nat.card ↥((R : Subgroup ↥X).map X.subtype) = Nat.card ↥(R : Subgroup ↥X) :=
      Subgroup.card_map_of_injective X.subtype_injective
    rw [hRmap] at h1
    exact h1.symm
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 3)).1 hQ.2.1
  have hj1 : j ≠ 0 := by
    rintro rfl
    apply hQ1
    rw [← Subgroup.card_eq_one, hj, pow_zero]
  have hdiv : 3 ∣ Nat.card ↥(R : Subgroup ↥X) := by
    rw [hcardR, hj]
    exact dvd_pow_self 3 hj1
  have hcop := Sylow.card_coprime_index R
  have hk : ¬ 3 ∣ (R : Subgroup ↥X).index := by
    intro h
    have h1 : 3 ∣ Nat.gcd (Nat.card ↥(R : Subgroup ↥X)) (R : Subgroup ↥X).index :=
      Nat.dvd_gcd hdiv h
    rw [Nat.Coprime.gcd_eq_one hcop] at h1
    norm_num at h1
  refine ⟨(R : Subgroup ↥X).index, ?_, hk⟩
  rw [← hcardR, Subgroup.card_mul_index]

theorem core_inf_eq_bot {X : Subgroup G} {P : Subgroup ↥X} (hP : IsPGroup 3 ↥P) :
    GLAPPrimeCore 3 ↥X ⊓ P = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥X)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥X
  have hnd : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥X) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop
  have hp : IsPGroup 3 ↥(GLAPPrimeCore 3 ↥X ⊓ P) := hP.to_le inf_le_right
  obtain ⟨t, ht⟩ := (IsPGroup.iff_card (p := 3)).1 hp
  have hdvd : Nat.card ↥(GLAPPrimeCore 3 ↥X ⊓ P) ∣ Nat.card ↥(GLAPPrimeCore 3 ↥X) :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [ht] at hdvd
  have ht0 : t = 0 := by
    by_contra h
    exact hnd ((dvd_pow_self 3 h).trans hdvd)
  rw [ht0, pow_zero] at ht
  exact Subgroup.card_eq_one.1 ht

theorem quot_injective {X Q : Subgroup G} (hQX : Q ≤ X) (hQp : IsPGroup 3 ↥Q) :
    Function.Injective
      ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp (Q.subgroupOf X).subtype) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 ↥(Q.subgroupOf X) :=
    hQp.of_injective (Subgroup.subgroupOfEquivOfLe hQX).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQX).injective
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx1 : ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) (x : ↥X)) = 1 := hx
  have hxN : (x : ↥X) ∈ GLAPPrimeCore 3 ↥X := (QuotientGroup.eq_one_iff _).1 hx1
  have hmem : (x : ↥X) ∈ GLAPPrimeCore 3 ↥X ⊓ Q.subgroupOf X := ⟨hxN, x.2⟩
  rw [core_inf_eq_bot hP, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem quotient_card_factor {X Q : Subgroup G} (hQp : IsPGroup 3 ↥Q) {kX : ℕ}
    (hX : Nat.card ↥X = Nat.card ↥Q * kX) (hk : ¬ 3 ∣ kX) :
    ∃ k : ℕ, Nat.card (↥X ⧸ GLAPPrimeCore 3 ↥X) = Nat.card ↥Q * k ∧ ¬ 3 ∣ k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcopN : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥X)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥X
  have hnd : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥X) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcopN
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥X)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 3)).1 hQp
  have hcop : Nat.Coprime (Nat.card (GLAPPrimeCore 3 ↥X)) (Nat.card ↥Q) := by
    rw [hj]
    exact Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd).symm
  have hdvd : Nat.card (GLAPPrimeCore 3 ↥X) ∣ kX := by
    have h1 : Nat.card (GLAPPrimeCore 3 ↥X) ∣ Nat.card ↥Q * kX :=
      ⟨Nat.card (↥X ⧸ GLAPPrimeCore 3 ↥X), by rw [← hX, hsplit, mul_comm]⟩
    exact hcop.dvd_of_dvd_mul_left h1
  obtain ⟨k, hk'⟩ := hdvd
  refine ⟨k, ?_, ?_⟩
  · have hpos : 0 < Nat.card (GLAPPrimeCore 3 ↥X) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [mul_comm (Nat.card (GLAPPrimeCore 3 ↥X)), ← hsplit, hX, hk']
    ring
  · intro h
    apply hk
    rw [hk']
    exact Dvd.dvd.mul_left h _

section Layer

variable {G : Type} [Group G] [Finite G]

theorem coe_mem_core_iff {X : Subgroup G} (y : ↥X) :
    (y : G) ∈ GLAPPrimeCoreOf 3 X ↔ y ∈ GLAPPrimeCore 3 ↥X :=
  Subgroup.mem_map_iff_mem X.subtype_injective

theorem barX_eq_bot_of_le_core {X N : Subgroup G} (hNX : N ≤ X)
    (hN : N ≤ GLAPPrimeCoreOf 3 X) : barX 3 X N = ⊥ := by
  unfold barX
  rw [eq_bot_iff]
  rintro _ ⟨k, hk, rfl⟩
  rw [Subgroup.mem_bot]
  have hkN : (k : G) ∈ N := hk
  exact (QuotientGroup.eq_one_iff k).2 ((coe_mem_core_iff k).1 (hN hkN))

noncomputable def cY (X : Subgroup G) (g : ↥X) :
    (↥X ⧸ GLAPPrimeCore 3 ↥X) →* (↥X ⧸ GLAPPrimeCore 3 ↥X) :=
  QuotientGroup.map (GLAPPrimeCore 3 ↥X) (GLAPPrimeCore 3 ↥X) (MulAut.conj g⁻¹).toMonoidHom
    (by
      intro x hx
      exact CFSG.HardMathSupport.Solomon.LocalBalance.map_gLAPPrimeCore_le 3
        (MulAut.conj g⁻¹) ⟨x, hx, rfl⟩)

theorem cY_mk (X : Subgroup G) (g k : ↥X) :
    cY X g (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) k) =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (g⁻¹ * k * g) := by
  show QuotientGroup.mk' _ (g⁻¹ * k * g⁻¹⁻¹) = _
  rw [inv_inv]

theorem barX_map_cY (X K : Subgroup G) (g : ↥X) :
    (barX 3 X K).map (cY X g) = barX 3 X (GLBConj (g : G) K) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hw
    refine Subgroup.mem_map.2 ⟨g⁻¹ * k * g, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, mem_gLBConj]
      have hkK : (k : G) ∈ K := hk
      have e1 : (g : G) * (((g⁻¹ * k * g : ↥X)) : G) * (g : G)⁻¹ = (k : G) := by
        simp [mul_assoc]
      rw [e1]
      exact hkK
    · rw [cY_mk]
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    rw [Subgroup.mem_subgroupOf, mem_gLBConj] at hw
    refine Subgroup.mem_map.2 ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (g * w * g⁻¹),
      Subgroup.mem_map.2 ⟨g * w * g⁻¹, ?_, rfl⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hw
    · rw [cY_mk]
      congr 1
      group

theorem barX_comm_of_ne {X L L' : Subgroup G} (hL : GLAPComponent 3 X L)
    (hL' : GLAPComponent 3 X L') (hne : L ≠ L') :
    ∀ s ∈ barX 3 X L, ∀ t ∈ barX 3 X L', s * t = t * s := by
  have hcomm : ⁅barX 3 X L, barX 3 X L'⁆ = ⊥ := by
    rw [← barX_commutator 3 hL.1 hL'.1]
    exact barX_eq_bot_of_le_core
      ((commutator_le_of_le' hL.1 hL'.1)) (CFSG.HardMathSupport.Solomon.LocalBalance.commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hL hL' hne)
  intro s hs t ht
  have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  exact (Subgroup.mem_centralizer_iff.1 (hc hs) t ht).symm

theorem cY_injective (X : Subgroup G) (g : ↥X) : Function.Injective (cY X g) := by
  intro a b h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥X) a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥X) b
  rw [cY_mk, cY_mk] at h
  have h' := QuotientGroup.eq.1 h
  refine QuotientGroup.eq.2 ?_
  have hc := (inferInstance : (GLAPPrimeCore 3 ↥X).Normal).conj_mem _ h' g
  convert hc using 1
  group

theorem barX_isLTwoTwentySeven {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (hI : IsLTwoTwentySeven (barOf 3 L)) : IsLTwoTwentySeven ↥(barX 3 X L) := by
  obtain ⟨e⟩ := hI
  exact ⟨(CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barXEquiv Nat.prime_three
    hL.2.1).symm.trans e⟩

theorem subgroup_psl2_facts {Y : Type} [Group Y] [Finite Y] {S : Subgroup Y}
    (hS : IsLTwoTwentySeven ↥S) :
    (∀ z ∈ S, (∀ s ∈ S, s * z = z * s) → z = 1) ∧
      ∃ E : Subgroup Y, E ≤ S ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
        ∃ m : ℕ, Nat.card S = 27 * m ∧ ¬ 3 ∣ m := by
  obtain ⟨e⟩ := hS
  refine ⟨fun z hz hcomm => ?_, ?_⟩
  · have := psl2_27_centre e ⟨z, hz⟩ (fun s => Subtype.ext (hcomm s.1 s.2))
    exact congrArg Subtype.val this
  · obtain ⟨E, hE, hEc⟩ := psl2_27_sylow e
    refine ⟨E.map S.subtype, Subgroup.map_subtype_le E, isElemAbelian_map_of_injective _
      Subtype.val_injective hE, ?_, 364, ?_, by norm_num⟩
    · rw [Subgroup.card_map_of_injective Subtype.val_injective, hEc]
    · rw [psl2_27_card e]

theorem glaPComponent_conj_mem {X K : Subgroup G} (hK : GLAPComponent 3 X K) (g : ↥X) :
    GLAPComponent 3 X (GLBConj (g : G) K) := by
  have h := CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_gLBConj (g : G) hK
  have hX : GLBConj (g : G) X = X :=
    gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer g.2)
  rw [hX] at h
  exact h

theorem cY_comp (X : Subgroup G) (g h : ↥X) (w : ↥X ⧸ GLAPPrimeCore 3 ↥X) :
    cY X g (cY X h w) = cY X (h * g) w := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥X) w
  rw [cY_mk, cY_mk, cY_mk]
  congr 1
  group

open Classical in
noncomputable def conjFin (X K : Subgroup G) : Finset (Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
  (Set.finite_range (fun g : ↥X => (barX 3 X K).map (cY X g))).toFinset

theorem mem_conjFin {X K : Subgroup G} {S : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)} :
    S ∈ conjFin X K ↔ ∃ g : ↥X, (barX 3 X K).map (cY X g) = S := by
  unfold conjFin
  rw [Set.Finite.mem_toFinset, Set.mem_range]

noncomputable def Ybar (X K : Subgroup G) : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X) :=
  (conjFin X K).sup id

theorem Ybar_comap_le (X K : Subgroup G) (g : ↥X) :
    Ybar X K ≤ (Ybar X K).comap (cY X g) := by
  unfold Ybar
  refine Finset.sup_le ?_
  intro S hS
  obtain ⟨h, rfl⟩ := mem_conjFin.1 hS
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
  rw [Subgroup.mem_comap, cY_comp]
  have hmem : cY X (h * g) w ∈ (barX 3 X K).map (cY X (h * g)) :=
    Subgroup.mem_map.2 ⟨w, hw, rfl⟩
  exact Finset.le_sup (f := id) (mem_conjFin.2 ⟨h * g, rfl⟩) hmem

theorem Ybar_normal (X K : Subgroup G) : (Ybar X K).Normal := by
  refine ⟨fun n hn y => ?_⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥X) y
  have key : ∀ m : ↥X ⧸ GLAPPrimeCore 3 ↥X, QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) h * m *
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) h)⁻¹ = cY X h⁻¹ m := by
    intro m
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥X) m
    rw [cY_mk, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  rw [key]
  exact Ybar_comap_le X K h⁻¹ hn

theorem conjFin_isLTwoTwentySeven {X K : Subgroup G} (hK : GLAPComponent 3 X K)
    (hKI : IsLTwoTwentySeven (barOf 3 K)) {S : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)}
    (hS : S ∈ conjFin X K) : IsLTwoTwentySeven ↥S := by
  obtain ⟨g, rfl⟩ := mem_conjFin.1 hS
  obtain ⟨e⟩ := barX_isLTwoTwentySeven hK hKI
  exact ⟨((Subgroup.equivMapOfInjective _ (cY X g) (cY_injective X g)).symm).trans e⟩

theorem conjFin_comm {X K : Subgroup G} (hK : GLAPComponent 3 X K) :
    ∀ S ∈ conjFin X K, ∀ T ∈ conjFin X K, S ≠ T → ∀ s ∈ S, ∀ t ∈ T, s * t = t * s := by
  intro S hS T hT hne s hs t ht
  obtain ⟨g, rfl⟩ := mem_conjFin.1 hS
  obtain ⟨g', rfl⟩ := mem_conjFin.1 hT
  have hs' : s ∈ barX 3 X (GLBConj (g : G) K) := by
    rw [← barX_map_cY]
    exact hs
  have ht' : t ∈ barX 3 X (GLBConj (g' : G) K) := by
    rw [← barX_map_cY]
    exact ht
  have hL : GLBConj (g : G) K ≠ GLBConj (g' : G) K := by
    intro h
    apply hne
    rw [barX_map_cY, barX_map_cY, h]
  exact barX_comm_of_ne (glaPComponent_conj_mem hK g) (glaPComponent_conj_mem hK g') hL s hs' t ht'

theorem layer_product {X K : Subgroup G} (hK : GLAPComponent 3 X K)
    (hKI : IsLTwoTwentySeven (barOf 3 K)) :
    (∀ z ∈ Ybar X K, (∀ g ∈ Ybar X K, g * z = z * g) → z = 1) ∧
      ∃ E : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), E ≤ Ybar X K ∧ IsElemAbelian 3 E ∧
        Nat.card E = 27 ^ (conjFin X K).card ∧
        ∃ m : ℕ, Nat.card (Ybar X K) = 27 ^ (conjFin X K).card * m ∧ ¬ 3 ∣ m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl : ∀ S ∈ conjFin X K, ∃ E : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), E ≤ S ∧
      IsElemAbelian 3 E ∧ Nat.card E = 27 ∧ ∃ m : ℕ, Nat.card S = 27 * m ∧ ¬ 3 ∣ m := by
    intro S hS
    exact (subgroup_psl2_facts (conjFin_isLTwoTwentySeven hK hKI hS)).2
  have hcen : ∀ S ∈ conjFin X K, ∀ z ∈ S, (∀ s ∈ S, s * z = z * s) → z = 1 := by
    intro S hS
    exact (subgroup_psl2_facts (conjFin_isLTwoTwentySeven hK hKI hS)).1
  exact product_structure (conjFin X K) (conjFin_comm hK) hcen hsyl

end Layer

theorem not_mem_core_of_order_three {X : Subgroup G} {e : G} (heX : e ∈ X) (he1 : e ≠ 1)
    (he3 : e ^ 3 = 1) : (⟨e, heX⟩ : ↥X) ∉ GLAPPrimeCore 3 ↥X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hmem
  let xc : ↥(GLAPPrimeCore 3 ↥X) := ⟨⟨e, heX⟩, hmem⟩
  have hxc3 : xc ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa using he3
  have hxc1 : xc ≠ 1 := by
    intro h
    apply he1
    have h' : (⟨e, heX⟩ : ↥X) = 1 := congrArg Subtype.val h
    exact congrArg (fun z : ↥X => (z : G)) h'
  have hord : orderOf xc = 3 := orderOf_eq_prime hxc3 hxc1
  have hdvd := orderOf_dvd_natCard xc
  rw [hord] at hdvd
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥X)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥X
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop hdvd

theorem normal_elem_of_layer {X K Q : Subgroup G} (hK : GLAPComponent 3 X K)
    (hKI : IsLTwoTwentySeven (barOf 3 K)) (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥) :
    ∃ P : Subgroup G, P ≤ Q ∧ (∀ q ∈ Q, ∀ n ∈ P, q * n * q⁻¹ ∈ P) ∧
      IsElemAbelian 3 P ∧ Nat.card ↥P = 27 ^ (conjFin X K).card ∧
      ∀ e : G, e ∈ X → (∀ x ∈ X, e * x = x * e) → e ^ 3 = 1 → e ≠ 1 → e ∉ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQX : Q ≤ X := hQ.1
  have hQp : IsPGroup 3 ↥Q := hQ.2.1
  have hQ'p : IsPGroup 3 ↥(Q.subgroupOf X) :=
    hQp.of_injective (Subgroup.subgroupOfEquivOfLe hQX).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQX).injective
  haveI hYn : (Ybar X K).Normal := Ybar_normal X K
  set φ := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)).comp (Q.subgroupOf X).subtype with hφdef
  have hφinj : Function.Injective φ := quot_injective hQX hQp
  have hQbp : IsPGroup 3 ↥φ.range := hQ'p.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨kX, hX, hkX⟩ := isSylowIn_card_index hQ hQ1
  obtain ⟨k, hY, hk⟩ := quotient_card_factor hQp hX hkX
  have hQbcard : Nat.card ↥φ.range = Nat.card ↥Q :=
    ((Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm.trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQX).toEquiv))
  have hYQb : Nat.card (↥X ⧸ GLAPPrimeCore 3 ↥X) = Nat.card ↥φ.range * k := by
    rw [hQbcard, hY]
  have hrel : ¬ 3 ∣ φ.range.relIndex (Ybar X K) := relIndex_not_three_dvd hYQb hk
  obtain ⟨-, E, hEle, hEel, hEcard, m, hmcard, hm⟩ := layer_product hK hKI
  have hrelmul := Subgroup.relIndex_mul_card (H := φ.range) (K := Ybar X K)
  set I : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X) := φ.range ⊓ Ybar X K with hIdef
  have hIp : IsPGroup 3 ↥I := hQbp.to_le inf_le_left
  obtain ⟨i, hi⟩ := (IsPGroup.iff_card (p := 3)).1 hIp
  have hr3 : (27 : ℕ) ^ (conjFin X K).card = 3 ^ (3 * (conjFin X K).card) := by
    rw [pow_mul]
    norm_num
  have hYbcard : Nat.card ↥(Ybar X K) = 3 ^ (3 * (conjFin X K).card) * m := by
    rw [hmcard, hr3]
  have heq : 3 ^ i * φ.range.relIndex (Ybar X K) = 3 ^ (3 * (conjFin X K).card) * m := by
    rw [← hi, ← hYbcard, ← hrelmul]
    ring
  have hi3 : i = 3 * (conjFin X K).card := pow_three_eq_of_mul heq hrel hm
  have hIcard : Nat.card ↥I = 27 ^ (conjFin X K).card := by
    rw [hi, hi3, hr3]
  have hEsub : IsElemAbelian 3 (E.subgroupOf (Ybar X K)) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => Subtype.ext (hEel.2 _ (Subgroup.mem_subgroupOf.1 hx))⟩
    have hx' : ((x : ↥(Ybar X K)) : Y0X X) ∈ E := Subgroup.mem_subgroupOf.1 x.2
    have hy' : ((y : ↥(Ybar X K)) : Y0X X) ∈ E := Subgroup.mem_subgroupOf.1 y.2
    have hcomm : ((x : ↥(Ybar X K)) : Y0X X) * ((y : ↥(Ybar X K)) : Y0X X) =
        ((y : ↥(Ybar X K)) : Y0X X) * ((x : ↥(Ybar X K)) : Y0X X) :=
      congrArg Subtype.val (hEel.1.is_comm.comm ⟨_, hx'⟩ ⟨_, hy'⟩)
    exact Subtype.ext (Subtype.ext hcomm)
  have hIcard' : Nat.card ↥(I.subgroupOf (Ybar X K)) = 3 ^ (3 * (conjFin X K).card) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : I ≤ Ybar X K)).toEquiv, hIcard,
      hr3]
  have hEcard' : Nat.card ↥(E.subgroupOf (Ybar X K)) = 3 ^ (3 * (conjFin X K).card) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEle).toEquiv, hEcard, hr3]
  have hIidx : ¬ 3 ∣ (I.subgroupOf (Ybar X K)).index := by
    have h1 := Subgroup.card_mul_index (I.subgroupOf (Ybar X K))
    rw [hIcard', hYbcard] at h1
    have h2 := Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : (0 : ℕ) < 3) _) h1
    rw [h2]
    exact hm
  have hEidx : ¬ 3 ∣ (E.subgroupOf (Ybar X K)).index := by
    have h1 := Subgroup.card_mul_index (E.subgroupOf (Ybar X K))
    rw [hEcard', hYbcard] at h1
    have h2 := Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : (0 : ℕ) < 3) _) h1
    rw [h2]
    exact hm
  have hIp' : IsPGroup 3 ↥(I.subgroupOf (Ybar X K)) :=
    hIp.of_injective (Subgroup.subgroupOfEquivOfLe (inf_le_right : I ≤ Ybar X K)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : I ≤ Ybar X K)).injective
  have hIsub : IsElemAbelian 3 (I.subgroupOf (Ybar X K)) :=
    isElemAbelian_of_sylow_conj hEsub hIp' hIidx hEidx
  have hIcomm : ∀ u ∈ I, ∀ v ∈ I, u * v = v * u := by
    intro u hu v hv
    have hu' : (⟨u, hu.2⟩ : ↥(Ybar X K)) ∈ I.subgroupOf (Ybar X K) :=
      Subgroup.mem_subgroupOf.2 hu
    have hv' : (⟨v, hv.2⟩ : ↥(Ybar X K)) ∈ I.subgroupOf (Ybar X K) :=
      Subgroup.mem_subgroupOf.2 hv
    exact congrArg (fun z : ↥(I.subgroupOf (Ybar X K)) => ((z : ↥(Ybar X K)) : Y0X X))
      (hIsub.1.is_comm.comm ⟨⟨u, hu.2⟩, hu'⟩ ⟨⟨v, hv.2⟩, hv'⟩)
  have hIexp : ∀ u ∈ I, u ^ 3 = 1 := by
    intro u hu
    have hu' : (⟨u, hu.2⟩ : ↥(Ybar X K)) ∈ I.subgroupOf (Ybar X K) :=
      Subgroup.mem_subgroupOf.2 hu
    have h1 := hIsub.2 _ hu'
    exact congrArg (fun z : ↥(Ybar X K) => ((z : ↥(Ybar X K)) : Y0X X)) h1
  set A' : Subgroup ↥(Q.subgroupOf X) := (Ybar X K).comap φ with hA'
  have hmapA' : A'.map φ = I := by
    rw [hA', Subgroup.map_comap_eq]
  have hA'card : Nat.card ↥A' = 27 ^ (conjFin X K).card := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective A' φ hφinj).toEquiv, hmapA', hIcard]
  have hφA : ∀ x ∈ A', φ x ∈ I := fun x hx => ⟨MonoidHom.mem_range.2 ⟨x, rfl⟩, hx⟩
  have hA'el : IsElemAbelian 3 A' := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hφinj
      have h1 := hIcomm (φ u) (hφA u u.2) (φ v) (hφA v v.2)
      simpa [map_mul] using h1
    · apply hφinj
      rw [map_pow, map_one]
      exact hIexp _ (hφA x hx)
  let ι : ↥(Q.subgroupOf X) →* G := X.subtype.comp (Q.subgroupOf X).subtype
  have hι : Function.Injective ι := X.subtype_injective.comp Subtype.val_injective
  refine ⟨A'.map ι, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact Subgroup.mem_subgroupOf.1 x.2
  · intro q hq n hn
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hn
    have hqX : (⟨q, hQX hq⟩ : ↥X) ∈ Q.subgroupOf X := Subgroup.mem_subgroupOf.2 hq
    let qq : ↥(Q.subgroupOf X) := ⟨⟨q, hQX hq⟩, hqX⟩
    have hw : qq * x * qq⁻¹ ∈ A' := by
      rw [hA', Subgroup.mem_comap]
      have hx' : φ x ∈ Ybar X K := hx
      have hc := (inferInstance : (Ybar X K).Normal).conj_mem _ hx' (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨q, hQX hq⟩ : ↥X))
      convert hc using 1
      rw [hφdef, MonoidHom.comp_apply, MonoidHom.comp_apply]
      simp only [map_mul, map_inv]
      rfl
    refine Subgroup.mem_map.2 ⟨qq * x * qq⁻¹, hw, ?_⟩
    simp [ι, qq, map_mul, map_inv]
  · exact isElemAbelian_map_of_injective ι hι hA'el
  · rw [← hA'card]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective A' ι hι).toEquiv).symm
  ·
    intro e heX heC he3 he1 hePmem
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 hePmem
    have hxX : ((x : ↥(Q.subgroupOf X)) : ↥X) = ⟨e, heX⟩ := Subtype.ext hxe
    have hz : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨e, heX⟩ : ↥X) ∈ Ybar X K := by
      rw [← hxX]
      exact hx
    have hcen : ∀ g ∈ Ybar X K, g * QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨e, heX⟩ : ↥X) =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨e, heX⟩ : ↥X) * g := by
      intro g _
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥X) g
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (heC y.1 y.2).symm
    have hz1 := (layer_product hK hKI).1 _ hz hcen
    exact not_mem_core_of_order_three heX he1 he3 ((QuotientGroup.eq_one_iff _).1 hz1)

theorem layer_card_le_one {X K Q M : Subgroup G} {a : G} (hK : GLAPComponent 3 X K)
    (hKI : IsLTwoTwentySeven (barOf 3 K)) (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥) (hQM : Q ≤ M)
    (ha : a ∈ Q)
    (h0 : ∀ E1 : Subgroup G, E1 ≤ M → IsElemAbelian 3 E1 → 5 ≤ CFSG.Open.pRank 3 E1 →
      a ∉ Subgroup.normalizer (E1 : Set G)) :
    (conjFin X K).card ≤ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hPQ, hPn, hPel, hPcard, -⟩ := normal_elem_of_layer hK hKI hQ hQ1
  have hlt := l113_normal_rank_lt_five ha h0 hPn (hPQ.trans hQM) hPel
  have hpr : CFSG.Open.pRank 3 P = 3 * (conjFin X K).card := by
    apply l113_pRank_eq hPel
    rw [hPcard, pow_mul]
    norm_num
  omega

theorem glbConj_eq_of_layer {X K Q M : Subgroup G} {a : G} (hK : GLAPComponent 3 X K)
    (hKI : IsLTwoTwentySeven (barOf 3 K)) (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥) (hQM : Q ≤ M)
    (ha : a ∈ Q)
    (h0 : ∀ E1 : Subgroup G, E1 ≤ M → IsElemAbelian 3 E1 → 5 ≤ CFSG.Open.pRank 3 E1 →
      a ∉ Subgroup.normalizer (E1 : Set G))
    (g : ↥X) : GLBConj (g : G) K = K := by
  have hcard := layer_card_le_one hK hKI hQ hQ1 hQM ha h0
  have hmem1 : (barX 3 X K).map (cY X 1) ∈ conjFin X K := mem_conjFin.2 ⟨1, rfl⟩
  have hmemg : (barX 3 X K).map (cY X g) ∈ conjFin X K := mem_conjFin.2 ⟨g, rfl⟩
  have heq := Finset.card_le_one.1 hcard _ hmemg _ hmem1
  rw [barX_map_cY, barX_map_cY] at heq
  simp only [Subgroup.coe_one, gLBConj_one] at heq
  exact glaPComponent_unique (glaPComponent_conj_mem hK g) hK heq

theorem le_normalizer_of_layer {X K Q M : Subgroup G} {a : G} (hK : GLAPComponent 3 X K)
    (hKI : IsLTwoTwentySeven (barOf 3 K)) (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥) (hQM : Q ≤ M)
    (ha : a ∈ Q)
    (h0 : ∀ E1 : Subgroup G, E1 ≤ M → IsElemAbelian 3 E1 → 5 ≤ CFSG.Open.pRank 3 E1 →
      a ∉ Subgroup.normalizer (E1 : Set G)) :
    X ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  exact glbConj_eq_of_layer hK hKI hQ hQ1 hQM ha h0 ⟨g, hg⟩

theorem claim113A_clauses_123 {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q)
    (h0 : ∀ E1 : Subgroup G, E1 ≤ M → IsElemAbelian 3 E1 → 5 ≤ CFSG.Open.pRank 3 E1 →
      a ∉ Subgroup.normalizer (E1 : Set G)) :
    omegaOne 3 (centerOf Q) = E ⊓ A ∧ Q ≤ M ∧ Cg e ≤ Subgroup.normalizer (K : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDD : IsDDpStar 3 M E A := h.pair
  have hEmax : IsSCp 3 ⊤ E := (lemma104_ii_holds h.toSec10Fails hDD).1
  have hAmax : IsSCp 3 ⊤ A := (lemma104_ii_holds h.toSec10Fails hDD).2
  have hQX : Q ≤ Cg e := h.hQ.1.1
  have hQp : IsPGroup 3 ↥Q := h.hQ.1.2.1
  have hEQ : E ≤ Q := le_trans le_sup_left h.hQ.2
  have hAQ : A ≤ Q := le_trans le_sup_right h.hQ.2
  have hrk : CFSG.Open.pRank 3 (E ⊓ A) = 2 :=
    pRank_inter_eq_two hEmax hAmax h.h4 h.h3 hDD.1.2.2
  have hee : e ∈ E := (Subgroup.mem_inf.1 h.he.1).1
  have he1 : e ≠ 1 := h.he.2
  have he3 : e ^ 3 = 1 := hEmax.2.1.2 e hee
  have hXe : ∀ x ∈ Cg e, e * x = x * e := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 hx) e (Set.mem_singleton e)
  have heCg : e ∈ Cg e := Subgroup.mem_centralizer_iff.2 (fun x hx => by
    rw [Set.mem_singleton_iff.1 hx])
  have hePc : ∀ q ∈ Q, q * e = e * q := fun q hq => (hXe q (hQX hq)).symm
  have hQ1 : Q ≠ ⊥ := by
    intro hbot
    apply he1
    have hemem : e ∈ Q := hEQ hee
    rw [hbot, Subgroup.mem_bot] at hemem
    exact hemem
  obtain ⟨P, hPQ, hPn, hPel, hPcard, hePnot⟩ := normal_elem_of_layer h.hK.1 h.hK.2 h.hQ.1 hQ1
  have hPne : P ≠ ⊥ := by
    intro hP
    have hr : 0 < (conjFin (Cg e) K).card :=
      Finset.card_pos.2 ⟨_, mem_conjFin.2 ⟨1, rfl⟩⟩
    rw [hP, Subgroup.card_bot] at hPcard
    have := Nat.one_lt_pow hr.ne' (by norm_num : 1 < 27)
    omega
  have hZ : omegaOne 3 (centerOf Q) = E ⊓ A :=
    omegaOne_centerOf_eq hEmax hAmax hEQ hAQ hQp hrk h.he.1 he1 hePc hPQ hPn hPne
      (hePnot e heCg hXe he3 he1)
  have hU : IsUniquenessTwoLocal 3 E M := hDD.1.1.2
  have hQM : Q ≤ M := le_M_of_centre hU hZ hrk
  have ha : a ∈ Q := hAQ h.ha.1
  exact ⟨hZ, hQM, le_normalizer_of_layer h.hK.1 h.hK.2 h.hQ.1 hQ1 hQM ha h0⟩

end Lemma113c

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
