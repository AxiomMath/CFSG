module

public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2
public import CFSG.RankThree.PartTwo.KFacts.K426Kit
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSixCount
import CFSG.CharacterTheory.Burnside
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.RankThree.PartTwo.KFacts.K426

variable {G : Type*} [Group G] [Finite G]

private theorem cycleType_aux (m : Multiset ℕ) (h2 : ∀ n ∈ m, 2 ≤ n) (hsum : m.sum ≤ 6)
    (hpar : Even (m.sum + Multiset.card m)) :
    (∀ b ∈ m, b ∣ 3) ∨ (∀ b ∈ m, b ∣ 4) ∨ (∀ b ∈ m, b ∣ 5) := by
  have hcard : Multiset.card m ≤ 3 := by
    have h := Multiset.card_nsmul_le_sum h2
    rw [smul_eq_mul] at h
    omega
  interval_cases hc : Multiset.card m
  · obtain rfl := Multiset.card_eq_zero.1 hc
    simp
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 hc
    have ha : 2 ≤ a := h2 a (Multiset.mem_singleton_self a)
    have ha6 : a ≤ 6 := by simpa using hsum
    have hpar' : (a + 1) % 2 = 0 := by simpa [Nat.even_iff] using hpar
    interval_cases a <;> simp_all
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 hc
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, forall_eq, Multiset.sum_cons, Multiset.sum_singleton,
      Multiset.card_cons, Multiset.card_singleton] at h2 hsum hpar ⊢
    rw [Nat.even_iff] at hpar
    have ha := h2.1
    have hb := h2.2
    have ha' : a ≤ 4 := by omega
    have hb' : b ≤ 4 := by omega
    interval_cases a <;> interval_cases b <;> simp_all <;> omega
  · obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.1 hc
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, forall_eq, Multiset.sum_cons, Multiset.sum_singleton,
      Multiset.card_cons, Multiset.card_singleton] at h2 hsum hpar ⊢
    rw [Nat.even_iff] at hpar
    omega

private theorem alt6_pow (σ : Equiv.Perm (Fin 6)) (hσ : Equiv.Perm.sign σ = 1) :
    σ ^ 3 = 1 ∨ σ ^ 4 = 1 ∨ σ ^ 5 = 1 := by
  have h2 : ∀ n ∈ σ.cycleType, 2 ≤ n := fun n hn => Equiv.Perm.two_le_of_mem_cycleType hn
  have hsum : σ.cycleType.sum ≤ 6 := by
    rw [Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  have hpar : Even (σ.cycleType.sum + Multiset.card σ.cycleType) := by
    rw [Equiv.Perm.sign_of_cycleType] at hσ
    exact (neg_one_pow_eq_one_iff_even (by decide)).1 hσ
  have key : ∀ N : ℕ, (∀ b ∈ σ.cycleType, b ∣ N) → σ ^ N = 1 := fun N h => by
    rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType]
    exact Multiset.lcm_dvd.2 h
  rcases cycleType_aux _ h2 hsum hpar with h | h | h
  · exact Or.inl (key 3 h)
  · exact Or.inr (Or.inl (key 4 h))
  · exact Or.inr (Or.inr (key 5 h))

private theorem nontrivial_of_isQuasisimple {K : Type*} [Group K] (h : CFSG.Open.IsQuasisimple K) :
    Nontrivial K := by
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := h.2
  exact (QuotientGroup.mk_surjective (s := Subgroup.center K)).nontrivial

private theorem false_of_isQuasisimple_of_isSolvable {K : Type*} [Group K]
    (h : CFSG.Open.IsQuasisimple K) (hs : Group.IsSolvable K) : False := by
  haveI := nontrivial_of_isQuasisimple h
  haveI : Group.IsPerfect K := ⟨h.1⟩
  exact Group.IsPerfect.not_isSolvable K hs

theorem card_of_isHatSix {X : Type*} [Group X] [Finite X] (h : IsHatSix X) : Nat.card X = 1080 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hc,
    Nat.card_congr e.toEquiv, card_A6]

theorem false_of_isHatSix_of_card_lt {C K : Subgroup G} (hK : K ≤ C) (h : IsHatSix ↥K)
    (hC : Nat.card C < 1080) : False := by
  have h1 := Subgroup.card_dvd_of_le hK
  rw [card_of_isHatSix h] at h1
  exact absurd (Nat.le_of_dvd Nat.card_pos h1) (by omega)

theorem false_of_isHatSix_of_not_five {C K : Subgroup G} (hK : K ≤ C) (h : IsHatSix ↥K ∨
    Nonempty (↥K ≃* alternatingGroup (Fin 6))) (hC : ¬ 5 ∣ Nat.card C) : False := by
  apply hC
  have h5 : 5 ∣ Nat.card K := by
    rcases h with h | h
    · rw [card_of_isHatSix h]; norm_num
    · obtain ⟨e⟩ := h
      rw [Nat.card_congr e.toEquiv, card_A6]; norm_num
  exact h5.trans (Subgroup.card_dvd_of_le hK)

theorem false_of_component_of_solvable {C K : Subgroup G} (hK : IsComponentOf K C)
    (hC : IsSolvable ↥C) : False := by
  haveI : Group.IsSolvable ↥C := hC
  haveI : Group.IsSolvable ↥K := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hK.1) (Subgroup.inclusion_injective hK.1)
  exact false_of_isQuasisimple_of_isSolvable hK.2.2 inferInstance

theorem false_of_component_of_card_two_three {C K : Subgroup G} (hK : IsComponentOf K C) {a b : ℕ}
    (hC : Nat.card C = 2 ^ a * 3 ^ b) : False := by
  refine false_of_component_of_solvable hK ?_
  haveI : Fintype ↥C := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hC])

theorem mem_of_isSubnormal_of_coprime {C K : Subgroup G} (hK : IsSubnormal K C) {g : G}
    (hg : g ∈ C) (hco : Nat.Coprime (orderOf g) (K.relIndex C)) : g ∈ K := by
  induction hK with
  | refl => exact hg
  | @step H M C hHM hn hMC ih =>
    have hrel : H.relIndex M * M.relIndex C = H.relIndex C :=
      Subgroup.relIndex_mul_relIndex H M C hHM hMC.le
    have hgM : g ∈ M :=
      ih hg (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ hrel) hco)
    have hco2 : Nat.Coprime (orderOf g) (H.relIndex M) :=
      Nat.Coprime.coprime_dvd_right (Dvd.intro _ hrel) hco
    haveI := hn
    set x : M := ⟨g, hgM⟩ with hx
    have h1 : orderOf (QuotientGroup.mk x : M ⧸ H.subgroupOf M) ∣ orderOf g := by
      rw [← Subgroup.orderOf_mk g hgM]
      exact orderOf_map_dvd (QuotientGroup.mk' (H.subgroupOf M)) x
    have h2 : orderOf (QuotientGroup.mk x : M ⧸ H.subgroupOf M) ∣ H.relIndex M := by
      have := orderOf_dvd_natCard (QuotientGroup.mk x : M ⧸ H.subgroupOf M)
      rwa [← Subgroup.index_eq_card] at this
    have h3 : orderOf (QuotientGroup.mk x : M ⧸ H.subgroupOf M) = 1 :=
      Nat.eq_one_of_dvd_coprimes hco2 h1 h2
    exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 h3)

theorem orderOf_of_isHatSix {X : Type*} [Group X] [Finite X] (h : IsHatSix X) (g : X)
    (hg : Nat.Coprime (orderOf g) 3) :
    orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 4 ∨ orderOf g = 5 := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  have hz3 : ∀ z ∈ Subgroup.center X, z ^ 3 = 1 := by
    intro z hz
    have h3 := pow_card_eq_one' (G := Subgroup.center X) (x := ⟨z, hz⟩)
    rw [hZ] at h3
    exact congrArg Subtype.val h3
  have key : ∀ k : ℕ, (e (QuotientGroup.mk g)) ^ k = 1 → orderOf g ∣ k := by
    intro k hk
    have h1 : (QuotientGroup.mk g : X ⧸ Subgroup.center X) ^ k = 1 := by
      rw [← e.map_eq_one_iff, map_pow]; exact hk
    have h2 : g ^ k ∈ Subgroup.center X := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact h1
    have h3 : orderOf g ∣ k * 3 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul]
      exact hz3 _ h2
    exact hg.dvd_of_dvd_mul_right h3
  have hσ := (e (QuotientGroup.mk g)).2
  rcases alt6_pow _ (Equiv.Perm.mem_alternatingGroup.1 hσ) with h3 | h4 | h5
  · have := key 3 (Subtype.ext (by simpa using h3))
    exact Or.inl (hg.eq_one_of_dvd this)
  · have := key 4 (Subtype.ext (by simpa using h4))
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).1 (by simpa using this)
    interval_cases k <;> simp_all
  · have := key 5 (Subtype.ext (by simpa using h5))
    rcases (Nat.dvd_prime Nat.prime_five).1 this with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))

theorem false_of_isHatSix_of_elem {C K : Subgroup G} (hK : IsComponentOf K C) (h : IsHatSix ↥K)
    {g : G} (hg : g ∈ C) (hco : Nat.Coprime (orderOf g) (K.relIndex C))
    (h3 : Nat.Coprime (orderOf g) 3)
    (hord : orderOf g ≠ 1 ∧ orderOf g ≠ 2 ∧ orderOf g ≠ 4 ∧ orderOf g ≠ 5) : False := by
  have hgK : g ∈ K := mem_of_isSubnormal_of_coprime hK.2.1 hg hco
  have h4 := orderOf_of_isHatSix h ⟨g, hgK⟩ (by rwa [Subgroup.orderOf_mk])
  rw [Subgroup.orderOf_mk] at h4
  omega

theorem false_of_isHatSix_of_noA6 {C K : Subgroup G} (hK : K ≤ C) (h : IsHatSix ↥K)
    (hC : NoA6 C) : False := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  exact hC K hK (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))

theorem false_of_alt6_of_noA6 {C K : Subgroup G} (hK : K ≤ C)
    (h : Nonempty (↥K ≃* alternatingGroup (Fin 6))) (hC : NoA6 C) : False := by
  obtain ⟨e⟩ := h
  exact hC K hK e.toMonoidHom e.surjective

theorem false_of_component_of_selfCentralizing {C K R : Subgroup G} (hK : IsComponentOf K C)
    (hRC : R ≤ C) (hRn : (R.subgroupOf C).Normal) (hR : IsPGroup 3 R)
    (hcen : C ⊓ Subgroup.centralizer (R : Set G) ≤ R) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKC := hK.1
  have hcomp : CFSG.Open.IsComponentOf (K.subgroupOf C) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have h1 := hK.2.1.comap C.subtype
      rwa [show C.comap C.subtype = ⊤ from Subgroup.subgroupOf_self C] at h1
    · exact CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC) hK.2.2
  have hR' : IsPGroup 3 ↥(R.subgroupOf C) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRC).symm
  haveI : Group.IsNilpotent ↥(R.subgroupOf C) := hR'.isNilpotent
  have hRsub : IsSubnormal (R.subgroupOf C) ⊤ := IsSubnormal.of_mathlib hRn.isSubnormal
  have hbot := CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal
    (K.subgroupOf C) (R.subgroupOf C) hcomp hRsub
  have hKR : K ≤ R := by
    intro k hk
    apply hcen
    refine ⟨hKC hk, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
    have hmem := Subgroup.commutator_mem_commutator
      (show (⟨k, hKC hk⟩ : ↥C) ∈ K.subgroupOf C from hk)
      (show (⟨r, hRC hr⟩ : ↥C) ∈ R.subgroupOf C from hr)
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact (congrArg Subtype.val hmem).symm
  haveI : Group.IsNilpotent ↥K := (hR.to_le hKR).isNilpotent
  exact false_of_isQuasisimple_of_isSolvable hK.2.2 inferInstance

theorem component_eq_of_normal_simple {C K N : Subgroup G} (hK : IsComponentOf K C)
    (hNC : N ≤ C) (hNn : (N.subgroupOf C).Normal) (hN : IsSimpleGroup ↥N)
    (hperf : ∀ H : Subgroup G, H ≤ C → commutator ↥H = ⊤ → H ≤ N) : K = N := by
  have hKN : K ≤ N := hperf K hK.1 hK.2.2.1
  have h1 := hK.2.1.inf_of_le hNC
  rw [inf_eq_left.2 hKN] at h1
  rcases h1.eq_bot_or_eq_of_isSimpleGroup hN with h2 | h2
  · exfalso
    haveI := nontrivial_of_isQuasisimple hK.2.2
    exact (K.nontrivial_iff_ne_bot.1 inferInstance) h2
  · exact h2

theorem false_of_isHatSix_of_five_gen {C K : Subgroup G} (hK : IsComponentOf K C) (h : IsHatSix ↥K)
    (h25 : ¬ 25 ∣ Nat.card C) {T : Set G} (hTC : T ⊆ C) (hT5 : ∀ g ∈ T, orderOf g = 5)
    (hbig : 1080 < Nat.card (Subgroup.closure T)) : False := by
  have hcardK : Nat.card K = 1080 := card_of_isHatSix h
  have hmul : Nat.card C = 1080 * K.relIndex C := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.1).toEquiv, hcardK] at h1
    exact h1.symm
  have h5 : ¬ 5 ∣ K.relIndex C := by
    rintro ⟨m, hm⟩
    apply h25
    rw [hmul, hm]
    exact ⟨216 * m, by ring⟩
  have hTK : T ⊆ K := by
    intro g hg
    refine mem_of_isSubnormal_of_coprime hK.2.1 (hTC hg) ?_
    rw [hT5 g hg]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5
  have h6 : Nat.card (Subgroup.closure T) ≤ Nat.card K :=
    Subgroup.card_le_of_le ((Subgroup.closure_le K).2 hTK)
  omega

theorem false_of_alt6_of_five_gen {C K : Subgroup G} (hK : IsComponentOf K C)
    (h : Nonempty (↥K ≃* alternatingGroup (Fin 6))) (h25 : ¬ 25 ∣ Nat.card C) {T : Set G}
    (hTC : T ⊆ C) (hT5 : ∀ g ∈ T, orderOf g = 5)
    (hbig : 360 < Nat.card (Subgroup.closure T)) : False := by
  have hcardK : Nat.card K = 360 := by
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, card_A6]
  have hmul : Nat.card C = 360 * K.relIndex C := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.1).toEquiv, hcardK] at h1
    exact h1.symm
  have h5 : ¬ 5 ∣ K.relIndex C := by
    rintro ⟨m, hm⟩
    apply h25
    rw [hmul, hm]
    exact ⟨72 * m, by ring⟩
  have hTK : T ⊆ K := by
    intro g hg
    refine mem_of_isSubnormal_of_coprime hK.2.1 (hTC hg) ?_
    rw [hT5 g hg]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5
  have h6 : Nat.card (Subgroup.closure T) ≤ Nat.card K :=
    Subgroup.card_le_of_le ((Subgroup.closure_le K).2 hTK)
  omega

private theorem not_index_three_of_perfect_crit {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] (H : Subgroup X) (hH : H.index = 3) : False := by
  have hcard : Nat.card (X ⧸ H) = 3 := by rw [← Subgroup.index_eq_card]; exact hH
  haveI : Finite (X ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI hsolv : Group.IsSolvable (Equiv.Perm (X ⧸ H)) :=
    Equiv.Perm.isSolvable (by rw [hcard]; norm_num)
  let φ : X →* Equiv.Perm (X ⧸ H) := MulAction.toPermHom X (X ⧸ H)
  let P : Subgroup (Equiv.Perm (X ⧸ H)) := Subgroup.map φ ⊤
  haveI : Group.IsPerfect P := Group.IsPerfect.map (H := ⊤) φ
  haveI : Group.IsSolvable P :=
    Group.isSolvable_of_isSolvable_injective (f := P.subtype) (Subgroup.subtype_injective P)
  obtain ⟨k, hk⟩ : ∃ k : X, k ∉ H := by
    by_contra hcon
    have htop : H = ⊤ := eq_top_iff.2 fun k _ => by
      by_contra hk
      exact hcon ⟨k, hk⟩
    rw [htop, Subgroup.index_top] at hH
    exact absurd hH (by norm_num)
  have hφk : φ k ≠ 1 := by
    intro h1
    have h2 := congrArg (fun σ : Equiv.Perm (X ⧸ H) => σ (QuotientGroup.mk (1 : X))) h1
    simp only [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.one_apply] at h2
    change (QuotientGroup.mk (k * 1) : X ⧸ H) = QuotientGroup.mk 1 at h2
    rw [QuotientGroup.eq] at h2
    apply hk
    simpa using h2
  haveI : Nontrivial P :=
    ⟨⟨⟨φ k, k, Subgroup.mem_top k, rfl⟩, 1, fun h => hφk (congrArg Subtype.val h)⟩⟩
  exact Group.IsPerfect.not_isSolvable P inferInstance

theorem false_of_isHatSix_of_card_sub {K H : Subgroup G} (h : IsHatSix ↥K) (hHK : H ≤ K)
    (hH : Nat.card H = 360) : False := by
  haveI : Group.IsPerfect ↥K := ⟨h.1⟩
  have hcardK : Nat.card K = 1080 := card_of_isHatSix h
  have hHk : Nat.card (H.subgroupOf K) = 360 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv]
    exact hH
  have hidx : (H.subgroupOf K).index = 3 := by
    have h1 := Subgroup.card_mul_index (H.subgroupOf K)
    rw [hHk, hcardK] at h1
    omega
  exact not_index_three_of_perfect_crit (H.subgroupOf K) hidx

theorem false_of_isHatSix_of_threePrime_gen {C K : Subgroup G} (hK : IsComponentOf K C)
    (h : IsHatSix ↥K) {k : ℕ} (hC : Nat.card C = 3 ^ k * 1080) {T : Set G} (hTC : T ⊆ C)
    (hT3 : ∀ g ∈ T, Nat.Coprime (orderOf g) 3) (h360 : Nat.card (Subgroup.closure T) = 360) :
    False := by
  have hcardK : Nat.card K = 1080 := card_of_isHatSix h
  have hmul : Nat.card C = 1080 * K.relIndex C := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.1).toEquiv, hcardK] at h1
    exact h1.symm
  have hrel : K.relIndex C = 3 ^ k := by
    rw [hC] at hmul
    omega
  have hTK : T ⊆ K := by
    intro g hg
    refine mem_of_isSubnormal_of_coprime hK.2.1 (hTC hg) ?_
    rw [hrel]
    exact Nat.Coprime.pow_right k (hT3 g hg)
  exact false_of_isHatSix_of_card_sub h ((Subgroup.closure_le K).2 hTK) h360

private theorem isSubnormal_eq_or_le_center_crit {X : Type*} [Group X] {A B : Subgroup X}
    (h : CFSG.Open.IsSubnormal A B) (hB : CFSG.IsQuasisimple ↥B) :
    A = B ∨ A ≤ (Subgroup.center ↥B).map B.subtype := by
  induction h with
  | refl A => exact Or.inl rfl
  | step hAM hn _ ih =>
    rename_i A M
    rcases ih hB with hMB | hM
    · subst hMB
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hB hn with h | h
      · exact Or.inl (le_antisymm hAM (Subgroup.subgroupOf_eq_top.mp h))
      · refine Or.inr fun x hx => ⟨⟨x, hAM hx⟩, h ?_, rfl⟩
        exact hx
    · exact Or.inr (hAM.trans hM)

private theorem not_isQuasisimple_of_le_comm_crit {X : Type*} [Group X] {K A : Subgroup X}
    (hK : CFSG.Open.IsQuasisimple ↥K)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hKA : K ≤ A) : False := by
  have htop : Subgroup.center ↥K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hA _ (hKA y.2) _ (hKA x.2))
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK
  apply hab
  have h1 : ∀ z : ↥K ⧸ Subgroup.center ↥K, z = 1 := by
    intro z
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    rw [QuotientGroup.eq_one_iff, htop]
    trivial
  rw [h1 a, h1 b]

theorem component_eq_of_normal_quasisimple {C K N : Subgroup G} (hK : IsComponentOf K C)
    (hNC : N ≤ C) (hNn : (N.subgroupOf C).Normal) (hN : IsQuasisimple ↥N)
    (hperf : ∀ H : Subgroup G, H ≤ C → commutator ↥H = ⊤ → H ≤ N) : K = N := by
  have hKN : K ≤ N := hperf K hK.1 hK.2.2.1
  have h1 := hK.2.1.inf_of_le hNC
  rw [inf_eq_left.2 hKN] at h1
  rcases isSubnormal_eq_or_le_center_crit h1 hN with h2 | h2
  · exact h2
  · exfalso
    refine not_isQuasisimple_of_le_comm_crit hK.2.2
      (A := (Subgroup.center ↥N).map N.subtype) ?_ h2
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, -, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha b).symm

private theorem isComponentOf_map_conj_crit {C K : Subgroup G} (hK : IsComponentOf K C) {c : G}
    (hc : c ∈ C) : IsComponentOf (K.map (MulAut.conj c).toMonoidHom) C := by
  have hC : C.map (MulAut.conj c).toMonoidHom = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact C.mul_mem (C.mul_mem hc hy) (C.inv_mem hc)
    · intro hx
      refine ⟨c⁻¹ * x * c, C.mul_mem (C.mul_mem (C.inv_mem hc) hx) hc, ?_⟩
      simp [mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hC]
    exact Subgroup.map_mono hK.1
  · have := hK.2.1.map (MulAut.conj c).toMonoidHom
    rwa [hC] at this
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (K.equivMapOfInjective _ (MulAut.conj c).injective).symm hK.2.2

private theorem mul_comm_of_components_ne_crit {C K L : Subgroup G} (hK : IsComponentOf K C)
    (hL : IsComponentOf L C) (hne : K ≠ L) {a b : G} (ha : a ∈ K) (hb : b ∈ L) :
    a * b = b * a := by
  have hcomp : ∀ {X : Subgroup G}, IsComponentOf X C → IsComponentOf (X.subgroupOf C) ⊤ := by
    intro X hX
    refine ⟨le_top, ?_, CFSG.Open.IsQuasisimple.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hX.1) hX.2.2⟩
    have h1 := hX.2.1.comap C.subtype
    rwa [show C.comap C.subtype = ⊤ from Subgroup.subgroupOf_self C] at h1
  have hne' : K.subgroupOf C ≠ L.subgroupOf C := by
    intro h
    apply hne
    have h' := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hK.1, inf_eq_left.mpr hL.1] at h'
  have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hcomp hK) (hcomp hL)
    hne'
  have hmem := Subgroup.commutator_mem_commutator
    (show (⟨a, hK.1 ha⟩ : ↥C) ∈ K.subgroupOf C from ha)
    (show (⟨b, hL.1 hb⟩ : ↥C) ∈ L.subgroupOf C from hb)
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact congrArg Subtype.val hmem

private theorem dvd_of_pow_mem_normalizer_crit {K : Subgroup G} {v : G} {p : ℕ} (hp : p.Prime)
    (hvp : orderOf v = p) (hv : v ∉ Subgroup.normalizer (K : Set G)) {k : ℕ}
    (hk : v ^ k ∈ Subgroup.normalizer (K : Set G)) : p ∣ k := by
  by_contra hpk
  apply hv
  have hcop : Nat.Coprime k (orderOf v) := by
    rw [hvp]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hpk).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Subgroup.pow_mem _ hk m

private theorem mem_map_conj_iff_crit (K : Subgroup G) (c x : G) :
    x ∈ K.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * x * c ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

private theorem cube_of_map_crit {K : Subgroup G} (φ : G ≃* G)
    (hZ3 : ∀ z : G, z ∈ K → (∀ k ∈ K, k * z = z * k) → z ^ 3 = 1) :
    ∀ z : G, z ∈ K.map φ.toMonoidHom → (∀ k ∈ K.map φ.toMonoidHom, k * z = z * k) →
      z ^ 3 = 1 := by
  intro z hz hc
  obtain ⟨y, hy, rfl⟩ := hz
  have h1 : y ^ 3 = 1 := hZ3 y hy fun k hk =>
    φ.injective (by simpa using hc (φ k) ⟨k, hk, rfl⟩)
  calc (φ.toMonoidHom y) ^ 3 = φ.toMonoidHom (y ^ 3) := (map_pow _ y 3).symm
    _ = 1 := by rw [h1, map_one]

private theorem false_of_not_normalizes_crit {C K : Subgroup G} (hK : IsComponentOf K C)
    (hZ3 : ∀ z : G, z ∈ K → (∀ k ∈ K, k * z = z * k) → z ^ 3 = 1)
    {u : G} (huK : u ∈ K) (hu5 : orderOf u = 5)
    {v : G} (hv : v ∈ C) {p : ℕ} (hp : p.Prime) (hvp : orderOf v = p)
    (hvN : v ∉ Subgroup.normalizer (K : Set G)) (h5p : ¬ 5 ^ p ∣ Nat.card C) : False := by
  set Ki : ℕ → Subgroup G := fun i => K.map (MulAut.conj (v ^ i)).toMonoidHom with hKi_def
  set ui : ℕ → G := fun i => v ^ i * u * (v ^ i)⁻¹
  have hKi : ∀ i, IsComponentOf (Ki i) C := fun i =>
    isComponentOf_map_conj_crit hK (C.pow_mem hv i)
  have hui_eq : ∀ i, ui i = (MulAut.conj (v ^ i)).toMonoidHom u := fun i => rfl
  have hmem : ∀ i, ui i ∈ Ki i := fun i => ⟨u, huK, (hui_eq i).symm⟩
  have hord : ∀ i, orderOf (ui i) = 5 := by
    intro i
    rw [hui_eq i, orderOf_injective _ (MulAut.conj (v ^ i)).injective u, hu5]
  have hne : ∀ i j : ℕ, i < p → j < p → Ki i = Ki j → i = j := by
    intro i j hi hj hij
    wlog hle : i ≤ j generalizing i j
    · exact (this j i hj hi hij.symm (by omega)).symm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hN : v ^ d ∈ Subgroup.normalizer (K : Set G) := by
      rw [Subgroup.mem_normalizer_iff'']
      intro h
      have h1 := SetLike.ext_iff.1 hij (v ^ i * h * (v ^ i)⁻¹)
      simp only [hKi_def] at h1
      rw [mem_map_conj_iff_crit, mem_map_conj_iff_crit] at h1
      have e1 : (v ^ i)⁻¹ * (v ^ i * h * (v ^ i)⁻¹) * v ^ i = h := by group
      have e2 : (v ^ (i + d))⁻¹ * (v ^ i * h * (v ^ i)⁻¹) * v ^ (i + d) =
          (v ^ d)⁻¹ * h * v ^ d := by
        rw [pow_add]; group
      rw [e1, e2] at h1
      exact h1
    have hd := dvd_of_pow_mem_normalizer_crit hp hvp hvN hN
    have : d = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  set H : Fin p → Subgroup G := fun i => Subgroup.zpowers (ui i) with hH_def
  have hHle : ∀ i : Fin p, H i ≤ Ki i := fun i => (Subgroup.zpowers_le).2 (hmem i)
  have hKne : ∀ i j : Fin p, i ≠ j → Ki i ≠ Ki j := fun i j hij h =>
    hij (Fin.ext (hne i j i.2 j.2 h))
  have hcommK : ∀ i j : Fin p, i ≠ j → ∀ x ∈ Ki i, ∀ y ∈ Ki j, x * y = y * x :=
    fun i j hij x hx y hy => mul_comm_of_components_ne_crit (hKi i) (hKi j) (hKne i j hij) hx hy
  have hcomm : Pairwise fun i j : Fin p => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y :=
    fun i j hij x y hx hy => hcommK i j hij x (hHle i hx) y (hHle j hy)
  have hind : iSupIndep H := by
    rw [iSupIndep_def]
    intro i
    rw [Subgroup.disjoint_def]
    intro x hxH hxS
    have hxK : x ∈ Ki i := hHle i hxH
    have hxcen : x ∈ Subgroup.centralizer (Ki i : Set G) := by
      refine (iSup₂_le (fun j hj => ?_) :
        (⨆ (j : Fin p) (_ : j ≠ i), H j) ≤ Subgroup.centralizer (Ki i : Set G)) hxS
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact hcommK i j (Ne.symm hj) k hk y (hHle j hy)
    have hx3 : x ^ 3 = 1 :=
      cube_of_map_crit (MulAut.conj (v ^ (i : ℕ))) hZ3 x hxK
        (fun k hk => Subgroup.mem_centralizer_iff.1 hxcen k hk)
    have hx5 : x ^ 5 = 1 := by
      have := orderOf_dvd_of_mem_zpowers hxH
      rw [hord i] at this
      exact orderOf_dvd_iff_pow_eq_one.1 this
    have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have h2 : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one hx5
    have h3 : orderOf x ∣ Nat.gcd 3 5 := Nat.dvd_gcd h1 h2
    have h4 : orderOf x = 1 := Nat.dvd_one.1 (by simpa using h3)
    exact orderOf_eq_one_iff.1 h4
  have hcardH : ∀ i : Fin p, Nat.card (H i) = 5 := fun i => by
    simp only [hH_def]
    rw [Nat.card_zpowers, hord]
  have hrange_le : (Subgroup.noncommPiCoprod hcomm).range ≤ C := by
    rw [Subgroup.noncommPiCoprod_range]
    exact iSup_le fun i => (hHle i).trans (hKi i).1
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  have hcard : Nat.card ((i : Fin p) → H i) = 5 ^ p := by
    rw [Nat.card_pi]
    simp [hcardH]
  apply h5p
  rw [← hcard, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Subgroup.card_dvd_of_le hrange_le

private theorem data_of_hatSix_or_alt6_crit {X : Type*} [Group X] [Finite X]
    (h : IsHatSix X ∨ Nonempty (X ≃* alternatingGroup (Fin 6))) :
    5 ∣ Nat.card X ∧ (∀ z ∈ Subgroup.center X, z ^ 3 = 1) ∧
      Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6)) := by
  rcases h with h | h
  · refine ⟨by rw [card_of_isHatSix h]; norm_num, ?_, h.2.2⟩
    obtain ⟨-, hZ, -⟩ := h
    intro z hz
    have h3 := pow_card_eq_one' (G := Subgroup.center X) (x := ⟨z, hz⟩)
    rw [hZ] at h3
    exact congrArg Subtype.val h3
  · obtain ⟨e⟩ := h
    have hcen : Subgroup.center X = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hz' : e z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨y, rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
      rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hz'
      exact Subgroup.mem_bot.2 (e.injective (by rw [hz', map_one]))
    refine ⟨by rw [Nat.card_congr e.toEquiv, card_A6]; norm_num, ?_, ?_⟩
    · intro z hz
      rw [hcen, Subgroup.mem_bot] at hz
      rw [hz, one_pow]
    · exact ⟨(QuotientGroup.quotientMulEquivOfEq hcen).trans
        (QuotientGroup.quotientBot.trans e)⟩

private theorem mulAut_alt6_eq_one_crit {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {β : MulAut (alternatingGroup (Fin 6))} (hβ : β ^ p = 1) : β = 1 := by
  have hdvd : orderOf β ∣ p := orderOf_dvd_of_pow_eq_one hβ
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
  · exact orderOf_eq_one_iff.1 h1
  · exfalso
    haveI : Finite (MulAut (alternatingGroup (Fin 6))) :=
      Finite.of_injective
        (fun f : MulAut (alternatingGroup (Fin 6)) =>
          (f : alternatingGroup (Fin 6) → alternatingGroup (Fin 6))) DFunLike.coe_injective
    have hpA : p ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := h1 ▸ orderOf_dvd_natCard β
    have hcen : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
      alternatingGroup.center_eq_bot (by simp)
    have hinj : Function.Injective
        (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))) := by
      intro a b hab
      have hc : a⁻¹ * b ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 := congrArg (fun φ : MulAut (alternatingGroup (Fin 6)) => φ g) hab
        simp only [MulAut.conj_apply] at h1
        calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
          _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
          _ = a⁻¹ * b * g := by group
      rw [hcen, Subgroup.mem_bot, inv_mul_eq_one] at hc
      exact hc
    have h360 : 360 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
      have := Subgroup.card_dvd_of_injective _ hinj
      rwa [card_A6] at this
    have hle :=
      CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
    obtain ⟨k, hk⟩ := h360
    have hpos := Nat.card_pos (α := MulAut (alternatingGroup (Fin 6)))
    have h4320 : p ∣ 4320 := by
      have hk4 : k ≤ 4 := by omega
      have hk0 : 0 < k := by omega
      refine hpA.trans ?_
      rw [hk]
      interval_cases k <;> norm_num
    have hc : Nat.Coprime p 4320 := by
      have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 (by omega)
      have h3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
      have h5 : Nat.Coprime p 5 := (Nat.coprime_primes hp Nat.prime_five).2 (by omega)
      have : (4320 : ℕ) = 2 ^ 5 * 3 ^ 3 * 5 := by norm_num
      rw [this]
      exact ((h2.pow_right 5).mul_right (h3.pow_right 3)).mul_right h5
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc h4320)

private noncomputable def autCenterQuotCrit (K : Type*) [Group K] :
    MulAut K →* MulAut (K ⧸ Subgroup.center K) where
  toFun β := QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) β
    (Subgroup.map_center_eq β)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' β γ := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x => rfl

private theorem eq_one_of_autCenterQuot_eq_one_crit {X : Type*} [Group X]
    (hX : commutator X = ⊤) (α : MulAut X) (hα : autCenterQuotCrit X α = 1) : α = 1 := by
  have hα' : ∀ x : X, x⁻¹ * α x ∈ Subgroup.center X := by
    intro x
    have h1 := congrArg
      (fun γ : MulAut (X ⧸ Subgroup.center X) => γ (x : X ⧸ Subgroup.center X)) hα
    exact QuotientGroup.eq.1 h1.symm
  let δ : X →* Subgroup.center X :=
    { toFun := fun x => ⟨x⁻¹ * α x, hα' x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [map_mul]
        have hx := Subgroup.mem_center_iff.1 (hα' x)
        calc (x * y)⁻¹ * (α x * α y) = y⁻¹ * (x⁻¹ * α x) * α y := by group
          _ = (x⁻¹ * α x) * (y⁻¹ * α y) := by rw [hx y⁻¹]; group }
  have hcomm : commutator X ≤ δ.ker := by
    rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.1 (δ b).2 (δ a))
  ext x
  have hx : x ∈ δ.ker := hcomm (hX ▸ Subgroup.mem_top x)
  rw [MonoidHom.mem_ker] at hx
  have h1 : x⁻¹ * α x = 1 := congrArg Subtype.val hx
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.1 h1).symm

private theorem le_centralizer_of_normalizes_crit {K : Subgroup G} (hperf : commutator ↥K = ⊤)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6)) {v : G} {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hvp : orderOf v = p)
    (hvN : v ∈ Subgroup.normalizer (K : Set G)) : K ≤ Subgroup.centralizer ({v} : Set G) := by
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨v, hvN⟩ with hα
  have hαp : α ^ p = 1 := by
    rw [hα, ← map_pow]
    have : (⟨v, hvN⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← hvp]
      exact pow_orderOf_eq_one v
    rw [this, map_one]
  have hβ : (MulAut.congr e (autCenterQuotCrit ↥K α)) ^ p = 1 := by
    rw [← map_pow, ← map_pow, hαp, map_one, map_one]
  have h1 := mulAut_alt6_eq_one_crit hp hp7 hβ
  have h2 : autCenterQuotCrit ↥K α = 1 :=
    (MulAut.congr e).injective (h1.trans (map_one (MulAut.congr e)).symm)
  have h3 : α = 1 := eq_one_of_autCenterQuot_eq_one_crit hperf α h2
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have h4 := congrArg (fun γ : MulAut ↥K => (γ ⟨x, hx⟩ : G)) h3
  simp only [hα, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h4
  exact mul_inv_eq_iff_eq_mul.1 h4

theorem false_of_component_of_prime_elem {C K : Subgroup G} (hK : IsComponentOf K C)
    (h : IsHatSix ↥K ∨ Nonempty (↥K ≃* alternatingGroup (Fin 6))) {v : G} (hv : v ∈ C) {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hvp : orderOf v = p) (h5p : ¬ 5 ^ p ∣ Nat.card C)
    (h5 : ¬ 5 ∣ Nat.card (Subgroup.centralizer ({v} : Set G))) : False := by
  obtain ⟨h5K, hZ3, ⟨e⟩⟩ := data_of_hatSix_or_alt6_crit h
  by_cases hvN : v ∈ Subgroup.normalizer (K : Set G)
  · exact h5 (h5K.trans (Subgroup.card_dvd_of_le
      (le_centralizer_of_normalizes_crit hK.2.2.1 e hp hp7 hvp hvN)))
  · haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 5 h5K
    refine false_of_not_normalizes_crit hK ?_ u.2 (by rw [Subgroup.orderOf_coe]; exact hu) hv hp
      hvp hvN h5p
    intro z hz hc
    have := hZ3 ⟨z, hz⟩ (Subgroup.mem_center_iff.2 fun k => Subtype.ext (hc k k.2))
    exact congrArg Subtype.val this

end CFSG.HardMathSupport.Solomon.Coordinator
