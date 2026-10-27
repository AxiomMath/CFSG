module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen
import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Quot
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpComp
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Hat

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

namespace Gen

theorem exists_prime_ge_five_dvd_card {Y : Type*} [Group Y] [Finite Y]
    (h : ¬ Group.IsSolvable Y) : ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ Nat.card Y := by
  by_contra hcon
  push Not at hcon
  apply h
  have hn : Nat.card Y ≠ 0 := Nat.card_pos.ne'
  have hpf : ∀ r : ℕ, r.Prime → r ∣ Nat.card Y → r = 2 ∨ r = 3 := by
    intro r hr hrd
    by_contra hne
    push Not at hne
    have h5 : 5 ≤ r := by
      have h2 := hr.two_le
      have h4 : r ≠ 4 := by
        rintro rfl
        exact absurd hr (by norm_num)
      omega
    exact hcon r hr h5 hrd
  have hcard : Nat.card Y =
      2 ^ (Nat.card Y).factorization 2 * 3 ^ (Nat.card Y).factorization 3 := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Finsupp.prod_of_support_subset _ (s := {2, 3}) ?_ _ (fun _ _ => pow_zero _),
      Finset.prod_pair (by norm_num)]
    intro r hr
    rw [Nat.support_factorization] at hr
    have := hpf r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
    simpa using this
  have := Fintype.ofFinite Y
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])

theorem two_dvd_card_quot {A : Type*} [Group A] {L : Subgroup A} [Finite L]
    (hq : IsQuasisimple ↥L) : 2 ∣ Nat.card (↥L ⧸ center ↥L) := by
  obtain ⟨-, hsimple, ⟨a, b, hab⟩⟩ := hq
  have hnotodd : ¬ Odd (Nat.card (↥L ⧸ center ↥L)) := by
    intro hodd
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have := hsimple
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a b)
  exact even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnotodd)

theorem exists_two_element_not_center {A : Type*} [Group A] {L : Subgroup A} [Finite L]
    (hq : IsQuasisimple ↥L) :
    ∃ t : ↥L, t ∉ center ↥L ∧ ∃ k : ℕ, orderOf t = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  have hPz : (P : Subgroup ↥L) ≤ center ↥L := by
    intro t ht
    by_contra hnc
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') ⟨t, ht⟩
    exact hcon t hnc k (by simpa using hk)
  have h1 : (center ↥L).index ∣ (P : Subgroup ↥L).index := Subgroup.index_dvd_of_le hPz
  have h2 : ¬ 2 ∣ (P : Subgroup ↥L).index := P.not_dvd_index
  have h3 : 2 ∣ (center ↥L).index := two_dvd_card_quot hq
  exact h2 (h3.trans h1)


theorem comm_of_ne_components {A : Type*} [Group A] [Finite A] {K L : Subgroup A}
    (hK : IsComponent K) (hL : IsComponent L) (hne : K ≠ L) : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a := by
  intro a ha b hb
  rcases CFSG.LocalCores.distinct_components_commute hK hL with h | h
  · exact absurd h hne
  · have hmem : ⁅a, b⁆ ∈ ⁅K, L⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem

theorem mem_zpowers_of_orderOf_dvd {X : Type*} [Group X] [Finite X] [IsCyclic X] {x y : X}
    (h : orderOf x ∣ orderOf y) : x ∈ Subgroup.zpowers y := by
  obtain ⟨k, hk⟩ := h
  have hk0 : k ≠ 0 := by
    rintro rfl
    have := orderOf_pos y
    omega
  have hkd : k ∣ orderOf y := ⟨orderOf x, by rw [hk, mul_comm]⟩
  have hord : orderOf (y ^ k) = orderOf x := by
    rw [orderOf_pow_of_dvd hk0 hkd, hk, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]
  have heq : Subgroup.zpowers x = Subgroup.zpowers (y ^ k) :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hord])
  have hx : x ∈ Subgroup.zpowers (y ^ k) := by
    rw [← heq]
    exact Subgroup.mem_zpowers x
  exact (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) k)) hx

theorem isPGroup_closure_pair {A : Type*} [Group A] {a b : A} {i j : ℕ} (ha : orderOf a = 2 ^ i)
    (hb : orderOf b = 2 ^ j) (hab : a * b = b * a) :
    IsPGroup 2 ↥(Subgroup.closure ({a, b} : Set A)) ∧
      ∀ x ∈ Subgroup.closure ({a, b} : Set A), ∀ y ∈ Subgroup.closure ({a, b} : Set A),
        x * y = y * x := by
  have hpair : ({a, b} : Set A).Pairwise Commute := by
    intro x hx y hy hxy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact absurd rfl hxy
    · rw [Set.mem_singleton_iff.mp hy]; exact hab
    · rw [Set.mem_singleton_iff.mp hx]; exact hab.symm
    · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]
  have := Subgroup.isMulCommutative_closure hpair
  have hcomm : ∀ x ∈ Subgroup.closure ({a, b} : Set A), ∀ y ∈ Subgroup.closure ({a, b} : Set A),
      x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm
      (⟨x, hx⟩ : Subgroup.closure ({a, b} : Set A)) ⟨y, hy⟩)
  refine ⟨?_, hcomm⟩
  have hpow : ∀ g ∈ Subgroup.closure ({a, b} : Set A), ∃ m : ℕ, g ^ (2 ^ m) = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨i, by rw [← ha]; exact pow_orderOf_eq_one _⟩
      · rw [Set.mem_singleton_iff.mp hx]; exact ⟨j, by rw [← hb]; exact pow_orderOf_eq_one _⟩
    | one => exact ⟨0, by simp⟩
    | mul x y hx hy hx1 hy1 =>
      obtain ⟨m₁, h₁⟩ := hx1
      obtain ⟨m₂, h₂⟩ := hy1
      refine ⟨m₁ + m₂, ?_⟩
      rw [(Commute.mul_pow (hcomm x hx y hy) _)]
      have e1 : x ^ 2 ^ (m₁ + m₂) = 1 := by
        rw [pow_add, pow_mul, h₁, one_pow]
      have e2 : y ^ 2 ^ (m₁ + m₂) = 1 := by
        rw [add_comm, pow_add, pow_mul, h₂, one_pow]
      rw [e1, e2, one_mul]
    | inv x hx hx1 =>
      obtain ⟨m, hm⟩ := hx1
      exact ⟨m, by rw [inv_pow, hm, inv_one]⟩
  intro g
  obtain ⟨m, hm⟩ := hpow g.1 g.2
  exact ⟨m, Subtype.ext (by simpa using hm)⟩


theorem exists_distinct_involutions {A : Type*} [Group A] {X : Subgroup A} [Finite X]
    (hX2 : IsPGroup 2 ↥X) (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hnc : ¬ IsCyclic ↥X) :
    ∃ a ∈ X, ∃ b ∈ X, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b := by
  by_contra hcon
  push Not at hcon
  apply hnc
  let _ : CommGroup ↥X :=
    { (inferInstance : Group ↥X) with mul_comm := fun a b => Subtype.ext (hXc a a.2 b b.2) }
  refine CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_abelian_two_group_cyclic ↥X hX2 ?_
  intro first second _
  have h1 : orderOf ((first.1 : ↥X) : A) = 2 := by rw [Subgroup.orderOf_coe]; exact first.2
  have h2 : orderOf ((second.1 : ↥X) : A) = 2 := by rw [Subgroup.orderOf_coe]; exact second.2
  exact Subtype.ext (Subtype.ext (hcon _ first.1.2 _ second.1.2 h1 h2))

theorem exists_isFourSubgroup_le {A : Type} [Group A] {X : Subgroup A} [Finite X]
    (hX2 : IsPGroup 2 ↥X) (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hnc : ¬ IsCyclic ↥X) :
    ∃ U : Subgroup A, IVK.IsFourSubgroup U ∧ U ≤ X := by
  obtain ⟨a, ha, b, hb, ha2, hb2, hab⟩ := exists_distinct_involutions hX2 hXc hnc
  have hsq : ∀ {c : A}, orderOf c = 2 → c * c = 1 := fun {c} hc => by
    have := pow_orderOf_eq_one c
    rwa [hc, pow_two] at this
  have hne1 : ∀ {c : A}, orderOf c = 2 → c ≠ 1 := fun {c} hc h => by
    rw [h, orderOf_one] at hc
    exact absurd hc (by norm_num)
  obtain ⟨V, hV⟩ := hat_exists_isFourSubgroup_of_involutions (G := ↥X) (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    (Subtype.ext (hsq ha2)) (Subtype.ext (hsq hb2)) (Subtype.ext (hXc a ha b hb))
    (fun h => hne1 ha2 (congrArg Subtype.val h)) (fun h => hne1 hb2 (congrArg Subtype.val h))
    (fun h => hab (congrArg Subtype.val h))
  exact ⟨V.map X.subtype, hat_isFourSubgroup_map hV X.subtype X.subtype_injective,
    Subgroup.map_subtype_le V⟩


theorem conj_mem_pPrimeCoreOf {A : Type} [Group A] {C : Subgroup A} {o c : A}
    (ho : o ∈ pPrimeCoreOf 2 C) (hc : c ∈ C) : c * o * c⁻¹ ∈ pPrimeCoreOf 2 C := by
  obtain ⟨hoC, ho'⟩ := IVK812.mem_pPrimeCoreOf_iff.mp ho
  refine IVK812.mem_pPrimeCoreOf_iff.mpr ⟨C.mul_mem (C.mul_mem hc hoC) (C.inv_mem hc), ?_⟩
  have := (CFSG.pPrimeCore_normal (p := 2) (G := ↥C)).conj_mem _ ho' ⟨c, hc⟩
  exact this

end Gen

section Frame

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem AFrame.eq_one_of_central_odd_prime (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J) {c : A}
    (hcJ : c ∈ J) (hcz : ∀ k ∈ J, k * c = c * k) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcp : c ^ p = 1) : c = 1 := by
  have hmem := Gen.mem_pPrimeCore_two_of_commuting_conjugates hp hp2 hcp
    (Gen.commute_conj_of_central_in_component hJ hcJ hcz)
  rw [hfr.core, Subgroup.mem_bot] at hmem
  exact hmem

theorem AFrame.isPGroup_center_two (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J) :
    IsPGroup 2 ↥(center ↥J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : Nat.card (center ↥J) ≠ 0 := Nat.card_pos.ne'
  have hu : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card (center ↥J) → d = 2 := by
    intro d hd hdvd
    by_contra hd2
    have := Fact.mk hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥J)) d hdvd
    have hxd : ((x : ↥J) : A) ^ d = 1 := by
      have := pow_orderOf_eq_one ((x : ↥J) : A)
      rwa [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx] at this
    have hc : ((x : ↥J) : A) = 1 :=
      hfr.eq_one_of_central_odd_prime hJ (x : ↥J).2
        (fun k hk => congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨k, hk⟩)) hd hd2 hxd
    have hx1 : x = 1 := Subtype.ext (Subtype.ext hc)
    rw [hx1, orderOf_one] at hx
    exact hd.one_lt.ne hx
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hn hu)

theorem AFrame.false_of_comp_cent_four (hfr : AFrame A zb Sb Vb) {U K : Subgroup A}
    (hU : IVK.IsFourSubgroup U) (hK : IsComponent K) (hKU : K ≤ centralizer (U : Set A)) :
    False := by
  obtain ⟨-, hqns⟩ := Gen.quasisimple_quot hK.1
  obtain ⟨r, hr, hr5, hrd⟩ := Gen.exists_prime_ge_five_dvd_card hqns
  have hrK : r ∣ Nat.card ↥K := hrd.trans (Subgroup.card_quotient_dvd_card _)
  have := Fact.mk hr
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) r hrK
  have hxr : orderOf ((x : ↥K) : A) = r := by rw [Subgroup.orderOf_coe]; exact hx
  have hxO := hfr.four U hU r hr hr5 _ (hKU (x : ↥K).2) hxr
  set O : Subgroup A := pPrimeCoreOf 2 (centralizer (U : Set A)) with hO
  have hNle : K ⊓ O ≤ K := inf_le_left
  have hNn : ((K ⊓ O).subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨hnK, hnO⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hn)
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · exact K.mul_mem (K.mul_mem g.2 hnK) (K.inv_mem g.2)
    · exact Gen.conj_mem_pPrimeCoreOf hnO (hKU g.2)
  rcases quasisimple_normal_le_center_or_eq hK.1 hNle hNn with hz | hall
  ·
    have hxN : ((x : ↥K) : A) ∈ K ⊓ O := Subgroup.mem_inf.mpr ⟨(x : ↥K).2, hxO⟩
    have hxz := Subgroup.mem_inf.mp (hz hxN)
    have hxc : (x : ↥K) ∈ center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxz.2) g.1 g.2)
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (hfr.isPGroup_center_two hK) ⟨x, hxc⟩
    rw [Subgroup.orderOf_mk, hx] at hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hk
      exact hr.one_lt.ne' hk
    have h2r : 2 ∣ r := hk ▸ dvd_pow_self 2 hk0
    rcases (Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h2r with h2
    omega
  ·
    have hKO : K ≤ O := by
      rw [← hall]
      exact inf_le_right
    have hodd : Nat.Coprime 2 (Nat.card O) := by
      rw [hO, pPrimeCoreOf,
        Subgroup.card_map_of_injective (centralizer (U : Set A)).subtype_injective]
      exact CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥(centralizer (U : Set A)))
    have h2K : 2 ∣ Nat.card ↥K :=
      (Gen.two_dvd_card_quot hK.1).trans (Subgroup.card_quotient_dvd_card _)
    have h2O : 2 ∣ Nat.card O := h2K.trans (Subgroup.card_dvd_of_le hKO)
    exact absurd (Nat.dvd_gcd (dvd_refl 2) h2O) (by rw [hodd]; norm_num)

theorem AFrame.comp_unique_of_four (hfr : AFrame A zb Sb Vb) {J U : Subgroup A}
    (hJ : IsComponent J) (hUJ : U ≤ J) (hU : IVK.IsFourSubgroup U) :
    ∀ K : Subgroup A, IsComponent K → K = J := by
  intro K hK
  by_contra hne
  refine hfr.false_of_comp_cent_four hU hK ?_
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact Gen.comm_of_ne_components hJ hK (Ne.symm hne) u (hUJ hu) k hk

theorem AFrame.comps_le_two (hfr : AFrame A zb Sb Vb) {K₁ K₂ K₃ : Subgroup A}
    (h₁ : IsComponent K₁) (h₂ : IsComponent K₂) (h₃ : IsComponent K₃) :
    K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h12, h13, h23⟩ := hcon
  have c12 := Gen.comm_of_ne_components h₁ h₂ h12
  have c13 := Gen.comm_of_ne_components h₁ h₃ h13
  have c23 := Gen.comm_of_ne_components h₂ h₃ h23
  obtain ⟨t₂, ht₂, i, hi⟩ := Gen.exists_two_element_not_center h₂.1
  obtain ⟨t₃, ht₃, j, hj⟩ := Gen.exists_two_element_not_center h₃.1
  have haK : (t₂ : A) ∈ K₂ := t₂.2
  have hbK : (t₃ : A) ∈ K₃ := t₃.2
  have hai : orderOf (t₂ : A) = 2 ^ i := by rw [Subgroup.orderOf_coe]; exact hi
  have hbj : orderOf (t₃ : A) = 2 ^ j := by rw [Subgroup.orderOf_coe]; exact hj
  obtain ⟨hX2, hXc⟩ := Gen.isPGroup_closure_pair hai hbj (c23 _ haK _ hbK)
  set X : Subgroup A := Subgroup.closure ({(t₂ : A), (t₃ : A)} : Set A) with hX
  have haX : (t₂ : A) ∈ X := Subgroup.subset_closure (by simp)
  have hbX : (t₃ : A) ∈ X := Subgroup.subset_closure (by simp)
  have hXK : ∀ x ∈ X, ∀ k ∈ K₁, k * x = x * k := by
    have hle : X ≤ centralizer (K₁ : Set A) := by
      refine (Subgroup.closure_le _).mpr ?_
      intro y hy
      rcases hy with rfl | hy
      · exact Subgroup.mem_centralizer_iff.mpr fun k hk => c12 k hk _ haK
      · rw [Set.mem_singleton_iff.mp hy]
        exact Subgroup.mem_centralizer_iff.mpr fun k hk => c13 k hk _ hbK
    exact fun x hx k hk => Subgroup.mem_centralizer_iff.mp (hle hx) k hk
  have hnc : ¬ IsCyclic ↥X := by
    intro hcyc
    rcases le_total i j with hij | hji
    · have hdvd : orderOf (⟨(t₂ : A), haX⟩ : ↥X) ∣ orderOf (⟨(t₃ : A), hbX⟩ : ↥X) := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hai, hbj]
        exact pow_dvd_pow 2 hij
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Gen.mem_zpowers_of_orderOf_dvd hdvd)
      have hmem : (t₂ : A) ∈ K₃ := by
        have h := congrArg Subtype.val hn
        simp only [Subgroup.coe_zpow] at h
        rw [← h]
        exact Subgroup.zpow_mem _ hbK n
      apply ht₂
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (c23 g.1 g.2 _ hmem)
    · have hdvd : orderOf (⟨(t₃ : A), hbX⟩ : ↥X) ∣ orderOf (⟨(t₂ : A), haX⟩ : ↥X) := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hai, hbj]
        exact pow_dvd_pow 2 hji
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Gen.mem_zpowers_of_orderOf_dvd hdvd)
      have hmem : (t₃ : A) ∈ K₂ := by
        have h := congrArg Subtype.val hn
        simp only [Subgroup.coe_zpow] at h
        rw [← h]
        exact Subgroup.zpow_mem _ haK n
      apply ht₃
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (c23 _ hmem g.1 g.2).symm
  obtain ⟨U, hU4, hUX⟩ := Gen.exists_isFourSubgroup_le hX2 hXc hnc
  refine hfr.false_of_comp_cent_four hU4 h₁ fun k hk => ?_
  exact Subgroup.mem_centralizer_iff.mpr fun u hu => (hXK u (hUX hu) k hk).symm

end Frame

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
