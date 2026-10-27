module

public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.CGT.PushingUpLit.LIT.Foote.TightAux

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace QBlock

variable {K : Subgroup G}

@[expose] def topHom (K : Subgroup G) : ↥K →* ↥K ⧸ pCore 2 ↥K := QuotientGroup.mk' (pCore 2 ↥K)

omit [Finite G] in
theorem mem_oTwoIn_iff {k : G} (hk : k ∈ K) : k ∈ oTwoIn K ↔ (⟨k, hk⟩ : ↥K) ∈ pCore 2 ↥K := by
  rw [oTwoIn_eq_map]
  exact Subgroup.mem_map_iff_mem (f := K.subtype) K.subtype_injective (x := ⟨k, hk⟩)

omit [Finite G] in
theorem topHom_eq_one_iff {g : ↥K} : topHom K g = 1 ↔ (g : G) ∈ oTwoIn K := by
  rw [topHom, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_oTwoIn_iff g.2]

omit [Finite G] in
theorem topHom_surjective : Function.Surjective (topHom K) := QuotientGroup.mk'_surjective _

theorem oTwoIn_le_centralizer (h : QBlock K) :
    oTwoIn K ≤ Subgroup.centralizer (blockU K : Set G) := fun r hr =>
  Subgroup.mem_centralizer_iff.2 fun u hu => blockU_comm_of_short h.short u hu r hr

theorem commutator_mem (h : QBlock K) {a b : G} (ha : a ∈ K) (hb : b ∈ K) : ⁅a, b⁆ ∈ K := by
  have := Subgroup.commutator_mem_commutator ha hb
  rwa [h.perfect] at this

theorem topHom_commutator (h : QBlock K) {a b : G} (ha : a ∈ K) (hb : b ∈ K) :
    topHom K ⟨⁅a, b⁆, h.commutator_mem ha hb⟩ = ⁅topHom K ⟨a, ha⟩, topHom K ⟨b, hb⟩⁆ := by
  have : (⟨⁅a, b⁆, h.commutator_mem ha hb⟩ : ↥K) = ⁅(⟨a, ha⟩ : ↥K), ⟨b, hb⟩⁆ := rfl
  rw [this, map_commutatorElement]

theorem mem_oTwoIn_of_commutator_le (h : QBlock K) {k : G} (hk : k ∈ K)
    (hk2 : ∃ n : ℕ, k ^ 2 ^ n = 1) (hc : ∀ g ∈ K, ⁅k, g⁆ ∈ oTwoIn K) : k ∈ oTwoIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q : ↥K ⧸ pCore 2 ↥K := topHom K ⟨k, hk⟩ with hq
  have hqc : ∀ x : ↥K ⧸ pCore 2 ↥K, x * q = q * x := by
    intro x
    obtain ⟨g, rfl⟩ := topHom_surjective x
    have h1 : topHom K ⟨⁅k, (g : G)⁆, h.commutator_mem hk g.2⟩ = 1 :=
      topHom_eq_one_iff.2 (hc g g.2)
    rw [h.topHom_commutator hk g.2] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  have hqpow : ∃ n : ℕ, q ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hk2
    refine ⟨n, ?_⟩
    rw [hq, ← map_pow]
    have : (⟨k, hk⟩ : ↥K) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn)
    rw [this, map_one]
  have hzp : IsPGroup 2 (Subgroup.zpowers q) := by
    obtain ⟨n, hn⟩ := hqpow
    have : orderOf q ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 this
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hzn : (Subgroup.zpowers q).Normal := ⟨fun x hx g => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hcm : Commute g q := hqc g
    rw [(hcm.zpow_right i).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers q i⟩
  have hle := BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hzn hzp
  rw [pCore_quotient_pCore_eq_bot] at hle
  have hq1 : q = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers q))
  exact topHom_eq_one_iff.1 hq1

theorem normal_inf_centralizer (_h : QBlock K) :
    ((K ⊓ Subgroup.centralizer (blockU K : Set G)).subgroupOf K).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using conj_mem_inf_centralizer (le_normalizer_blockU K) g g.2 n hn⟩

theorem commutator_centralizer_le (h : QBlock K) :
    ⁅K ⊓ Subgroup.centralizer (blockU K : Set G), K⁆ ≤ oTwoIn K := by
  have hCn := h.normal_inf_centralizer
  have hNn :
      (((K ⊓ Subgroup.centralizer (blockU K : Set G)).subgroupOf K).map (topHom K)).Normal :=
    hCn.map (topHom K) topHom_surjective
  rcases LocalCores.quasisimple_normal_subgroups h.quasisimple hNn with htop | hcen
  · exfalso
    have hKC : K ≤ Subgroup.centralizer (blockU K : Set G) := by
      intro g hg
      have hmem : topHom K ⟨g, hg⟩ ∈
          ((K ⊓ Subgroup.centralizer (blockU K : Set G)).subgroupOf K).map (topHom K) := by
        rw [htop]
        trivial
      obtain ⟨c, hc, hcg⟩ := hmem
      have hn : (⟨g, hg⟩ : ↥K) = c * (c⁻¹ * ⟨g, hg⟩) := by group
      have hmem2 : ((c⁻¹ * ⟨g, hg⟩ : ↥K) : G) ∈ oTwoIn K := by
        rw [← topHom_eq_one_iff, map_mul, map_inv, hcg]
        simp
      have hcC : (c : G) ∈ Subgroup.centralizer (blockU K : Set G) := (Subgroup.mem_inf.1 hc).2
      have := Subgroup.mul_mem _ hcC (h.oTwoIn_le_centralizer hmem2)
      have e : g = (c : G) * ((c⁻¹ * ⟨g, hg⟩ : ↥K) : G) := congrArg Subtype.val hn
      rw [e]
      exact this
    have hcom : ⁅K, blockU K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hKC
    rw [Subgroup.commutator_comm, h.blockU_stable] at hcom
    exact blockU_ne_bot_of_short h.short hcom
  · refine Subgroup.commutator_le.2 fun c hc g hg => ?_
    have hc1 : c ∈ K := (Subgroup.mem_inf.1 hc).1
    have hcN : topHom K ⟨c, hc1⟩ ∈ Subgroup.center (↥K ⧸ pCore 2 ↥K) :=
      hcen ⟨⟨c, hc1⟩, Subgroup.mem_subgroupOf.2 hc, rfl⟩
    have h1 : topHom K ⟨⁅c, g⁆, h.commutator_mem hc1 hg⟩ = 1 := by
      rw [h.topHom_commutator hc1 hg]
      exact commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_center_iff.1 hcN (topHom K ⟨g, hg⟩)).symm
    exact topHom_eq_one_iff.1 h1

theorem le_of_map_top (h : QBlock K) {A : Subgroup G} (hAK : A ≤ K)
    (hKA : K ≤ Subgroup.normalizer (A : Set G))
    (htop : (A.subgroupOf K).map (topHom K) = ⊤) : K ≤ A := by
  have hnorm : (A.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).2 hKA
  refine noTwoQuot_of_short h.short A (fun g hg n hn => ?_) (fun g hg => ?_)
  · exact (Subgroup.mem_normalizer_iff.1 (hKA hg) n).1 hn
  · have hmem : topHom K ⟨g, hg⟩ ∈ (A.subgroupOf K).map (topHom K) := by
      rw [htop]
      trivial
    obtain ⟨a, ha, hag⟩ := hmem
    set n : ↥K := a⁻¹ * ⟨g, hg⟩ with hn
    have hnO : n ∈ pCore 2 ↥K := by
      have : topHom K n = 1 := by rw [hn, map_mul, map_inv, hag]; simp
      exact (QuotientGroup.eq_one_iff n).1 this
    obtain ⟨e, he⟩ := (pCore_isPGroup (p := 2) (G := ↥K)) ⟨n, hnO⟩
    have he' : n ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    refine ⟨e, ?_⟩
    have hgn : (⟨g, hg⟩ : ↥K) = a * n := by rw [hn]; group
    have h1 : QuotientGroup.mk' (A.subgroupOf K) ((⟨g, hg⟩ : ↥K) ^ 2 ^ e) = 1 := by
      have hA1 : QuotientGroup.mk' (A.subgroupOf K) a = 1 := (QuotientGroup.eq_one_iff a).2 ha
      rw [map_pow, hgn, map_mul, hA1, one_mul, ← map_pow, he', map_one]
    have := (QuotientGroup.eq_one_iff _).1 h1
    simpa [Subgroup.mem_subgroupOf] using this

theorem blockU_le_of_normal (h : QBlock K) {A : Subgroup G} (hAK : A ≤ K)
    (hKA : K ≤ Subgroup.normalizer (A : Set G))
    (hA : ¬ A ≤ Subgroup.centralizer (K : Set G)) : blockU K ≤ A := by
  have hAn : (A.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).2 hKA
  have hNn := hAn.map (topHom K) topHom_surjective
  rcases LocalCores.quasisimple_normal_subgroups h.quasisimple hNn with htop | hcen
  · exact (blockU_le K).trans (h.le_of_map_top hAK hKA htop)
  · have hV'O : ⁅A, K⁆ ≤ oTwoIn K := by
      refine Subgroup.commutator_le.2 fun a ha g hg => ?_
      have hmem : topHom K ⟨a, hAK ha⟩ ∈ Subgroup.center (↥K ⧸ pCore 2 ↥K) :=
        hcen ⟨⟨a, hAK ha⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
      have h1 : topHom K ⟨⁅a, g⁆, h.commutator_mem (hAK ha) hg⟩ = 1 := by
        rw [h.topHom_commutator (hAK ha) hg]
        exact commutatorElement_eq_one_iff_mul_comm.2
          (Subgroup.mem_center_iff.1 hmem (topHom K ⟨g, hg⟩)).symm
      exact topHom_eq_one_iff.1 h1
    have hKV : K ≤ Subgroup.normalizer ((⁅A, K⁆ : Subgroup G) : Set G) :=
      Subgroup.normalizer_commutator_ge_right A K
    have hV2 : IsPGroup 2 (⁅A, K⁆ : Subgroup G) := (isPGroup_oTwoIn K).to_le hV'O
    have hVA : ⁅A, K⁆ ≤ A := Subgroup.le_normalizer_iff_commutator_le_left.1 hKA
    have hne : ⁅⁅A, K⁆, K⁆ ≠ ⊥ := by
      intro hb
      apply hA
      have h1 : ⁅⁅K, A⁆, K⁆ = ⊥ := by
        rw [Subgroup.commutator_comm K A]
        exact hb
      have h2 : ⁅⁅K, K⁆, A⁆ = ⊥ :=
        Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := K) (H₂ := K) (H₃ := A) h1 hb
      rw [h.perfect, Subgroup.commutator_comm] at h2
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2
    have hle : ⁅⁅A, K⁆, K⁆ ≤ oTwoIn K :=
      (Subgroup.le_normalizer_iff_commutator_le_left.1 hKV).trans hV'O
    have heq := SixThree.commutator_eq_U h.short hV2 hKV hle hne
    show ⁅oTwoIn K, K⁆ ≤ A
    rw [← heq]
    exact (Subgroup.le_normalizer_iff_commutator_le_left.1 hKV).trans hVA

theorem exists_involution_lift (h : QBlock K) :
    ∃ j ∈ K, (∃ n : ℕ, j ^ 2 ^ n = 1) ∧ j ∉ oTwoIn K ∧ j * j ∈ oTwoIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQnt : Nontrivial (↥K ⧸ pCore 2 ↥K) := by
    have : Nontrivial ((↥K ⧸ pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ pCore 2 ↥K)) :=
      h.quasisimple.2.1.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center (↥K ⧸ pCore 2 ↥K))).nontrivial
  have hQperf : Group.IsPerfect (↥K ⧸ pCore 2 ↥K) := h.quasisimple.1
  have h4 : 4 ∣ Nat.card (↥K ⧸ pCore 2 ↥K) := four_dvd_card_of_perfect
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥K ⧸ pCore 2 ↥K) 2
    (dvd_trans (by norm_num) h4)
  obtain ⟨k₁, rfl⟩ := topHom_surjective q
  have hq2 : topHom K k₁ ^ 2 = 1 := by
    have := pow_orderOf_eq_one (topHom K k₁)
    rwa [hq] at this
  have hq1 : topHom K k₁ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hq
    omega
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k₁).ne'
  have hqm : topHom K (k₁ ^ m) = topHom K k₁ := by
    obtain ⟨t, rfl⟩ := hm
    rw [map_pow, pow_succ, pow_mul, hq2, one_pow, one_mul]
  refine ⟨((k₁ ^ m : ↥K) : G), (k₁ ^ m).2, ⟨a, ?_⟩, ?_, ?_⟩
  · have : (k₁ ^ m) ^ 2 ^ a = 1 := by
      rw [← pow_mul, mul_comm, ← hord]
      exact pow_orderOf_eq_one _
    simpa using congrArg Subtype.val this
  · intro hO
    exact hq1 (hqm ▸ topHom_eq_one_iff.2 hO)
  · have : topHom K (k₁ ^ m * k₁ ^ m) = 1 := by
      rw [map_mul, hqm, ← pow_two, hq2]
    exact topHom_eq_one_iff.1 this

theorem le_closure_twoElements (h : QBlock K) :
    K ≤ Subgroup.closure {j | j ∈ K ∧ (∃ n : ℕ, j ^ 2 ^ n = 1) ∧
      j * j ∈ Subgroup.centralizer (blockU K : Set G)} := by
  set S : Set G := {j | j ∈ K ∧ (∃ n : ℕ, j ^ 2 ^ n = 1) ∧
      j * j ∈ Subgroup.centralizer (blockU K : Set G)} with hS
  set X := Subgroup.closure S with hX
  have hXK : X ≤ K := (Subgroup.closure_le K).2 fun j hj => hj.1
  have hconjS : ∀ k ∈ K, ∀ j ∈ S, k * j * k⁻¹ ∈ S := by
    rintro k hk j ⟨hjK, ⟨n, hn⟩, hj2⟩
    refine ⟨K.mul_mem (K.mul_mem hk hjK) (K.inv_mem hk), ⟨n, ?_⟩, ?_⟩
    · rw [conj_pow, hn]
      group
    · have e : k * j * k⁻¹ * (k * j * k⁻¹) = k * (j * j) * k⁻¹ := by group
      rw [e]
      exact (conj_mem_inf_centralizer (le_normalizer_blockU K) k hk (j * j)
        ⟨K.mul_mem hjK hjK, hj2⟩).2
  have hconjX : ∀ k ∈ K, ∀ x ∈ X, k * x * k⁻¹ ∈ X := by
    intro k hk x hx
    induction hx using Subgroup.closure_induction with
    | mem s hs => exact Subgroup.subset_closure (hconjS k hk s hs)
    | one => simp
    | mul a b _ _ ha hb =>
      have e : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  have hKX : K ≤ Subgroup.normalizer (X : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconjX k hk x, fun hx => ?_⟩
    have := hconjX k⁻¹ (K.inv_mem hk) _ hx
    simpa [mul_assoc] using this
  have hXn : (X.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).2 hKX
  have hNn := hXn.map (topHom K) topHom_surjective
  rcases LocalCores.quasisimple_normal_subgroups h.quasisimple hNn with htop | hcen
  · exact h.le_of_map_top hXK hKX htop
  · exfalso
    obtain ⟨j, hjK, hj2, hjO, hjj⟩ := h.exists_involution_lift
    have hjS : j ∈ S := ⟨hjK, hj2, h.oTwoIn_le_centralizer hjj⟩
    have hjX : j ∈ X := Subgroup.subset_closure hjS
    have hmem : topHom K ⟨j, hjK⟩ ∈ Subgroup.center (↥K ⧸ pCore 2 ↥K) :=
      hcen ⟨⟨j, hjK⟩, Subgroup.mem_subgroupOf.2 hjX, rfl⟩
    apply hjO
    refine h.mem_oTwoIn_of_commutator_le hjK hj2 fun g hg => ?_
    have h1 : topHom K ⟨⁅j, g⁆, h.commutator_mem hjK hg⟩ = 1 := by
      rw [h.topHom_commutator hjK hg]
      exact commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_center_iff.1 hmem (topHom K ⟨g, hg⟩)).symm
    exact topHom_eq_one_iff.1 h1

end QBlock

end CFSG.CGT.PushingUpLit.LIT.Foote
