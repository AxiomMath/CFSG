module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Conj

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem exists_two_element_pow {H : Type*} [Group H] (f : G →* H) {x : G} {k : ℕ}
    (hx : f x ^ (2 ^ k) = 1) : ∃ y ∈ zpowers x, (∃ j : ℕ, y ^ (2 ^ j) = 1) ∧ f y = f x := by
  set n := orderOf x with hn
  have hn0 : n ≠ 0 := (orderOf_pos x).ne'
  set a := n.factorization 2
  set m := n / 2 ^ a
  have hnm : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hm : Nat.Coprime 2 m := Nat.coprime_ordCompl Nat.prime_two hn0
  have hfx : orderOf (f x) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hx
  have hcop : Nat.Coprime m (orderOf (f x)) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hfx
    rw [hi]
    exact hm.symm.pow_right i
  obtain ⟨m', hm'⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨x ^ (m * m'), pow_mem (mem_zpowers x) _, ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul, show m * m' * 2 ^ a = (2 ^ a * m) * m' by ring, hnm, pow_mul,
      pow_orderOf_eq_one, one_pow]
  · rw [map_pow, pow_mul, hm']

omit [Finite G] in
theorem zpowers_commutator_mem {K O : Subgroup G} {t : G} (htK : t ∈ normalizer (K : Set G))
    (htO : t ∈ normalizer (O : Set G)) (hc : ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ O) :
    ∀ x ∈ zpowers t, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ O := by
  let S : Subgroup G :=
    { carrier := {x | x ∈ normalizer (K : Set G) ∧ x ∈ normalizer (O : Set G) ∧
        ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ O}
      mul_mem' := by
        rintro x y ⟨hxK, hxO, hx⟩ ⟨hyK, hyO, hy⟩
        refine ⟨mul_mem hxK hyK, mul_mem hxO hyO, fun k hk => ?_⟩
        have h1 : x * (y * k * y⁻¹ * k⁻¹) * x⁻¹ ∈ O :=
          (mem_normalizer_iff.mp hxO _).mp (hy k hk)
        have h2 : x * y * k * (x * y)⁻¹ * k⁻¹ =
            (x * (y * k * y⁻¹ * k⁻¹) * x⁻¹) * (x * k * x⁻¹ * k⁻¹) := by group
        rw [h2]
        exact mul_mem h1 (hx k hk)
      one_mem' := ⟨one_mem _, one_mem _, fun k _ => by simp⟩
      inv_mem' := by
        rintro x ⟨hxK, hxO, hx⟩
        refine ⟨inv_mem hxK, inv_mem hxO, fun k hk => ?_⟩
        have hk' : x⁻¹ * k * x⁻¹⁻¹ ∈ K := (mem_normalizer_iff.mp (inv_mem hxK) k).mp hk
        rw [inv_inv] at hk'
        have h1 := hx _ hk'
        have h2 : x * (x⁻¹ * k * x) * x⁻¹ * (x⁻¹ * k * x)⁻¹ = (x⁻¹ * k * x * k⁻¹)⁻¹ := by group
        rw [h2] at h1
        have := inv_mem h1
        rw [inv_inv] at this
        rw [inv_inv]
        exact this }
  have hle : zpowers t ≤ S := (zpowers_le).mpr ⟨htK, htO, hc⟩
  exact fun x hx => (hle hx).2.2

omit [Finite G] in
theorem inf_normalizer_le_normalizer_inf (X Y : Subgroup G) :
    normalizer (X : Set G) ⊓ normalizer (Y : Set G) ≤
      normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  intro n hn
  obtain ⟨hX, hY⟩ := mem_inf.mp hn
  rw [mem_normalizer_iff] at hX hY ⊢
  intro y
  rw [mem_inf, mem_inf, hX y, hY y]

omit [Finite G] in
theorem mem_of_two_element_of_le_sup_of_le {K A O : Subgroup G} (hKA : K ≤ A)
    (hAK : A ≤ normalizer (K : Set G)) (hO : Odd (Nat.card O)) (hKO : K ≤ normalizer (O : Set G))
    (hOA : O ≤ normalizer (A : Set G)) {x : G} (hx : x ∈ K ⊔ O) {k : ℕ}
    (hxk : x ^ (2 ^ k) = 1) : x ∈ K := by
  have hxA : x ∈ A := mem_of_two_element_of_le_sup hKA hO hKO hOA hx hxk
  have hx' : x ∈ (K : Set G) * O := by
    rw [← coe_mul_of_left_le_normalizer_right K O hKO]
    exact hx
  obtain ⟨y, hy, o, ho, rfl⟩ := Set.mem_mul.mp hx'
  have hoA : o ∈ A := by
    have : o = y⁻¹ * (y * o) := by group
    rw [this]
    exact mul_mem (inv_mem (hKA hy)) hxA
  have hx'' : y * o ∈ K ⊔ (O ⊓ A) := mul_mem (mem_sup_left hy) (mem_sup_right ⟨ho, hoA⟩)
  refine mem_of_two_element_of_le_sup le_rfl
    (hO.of_dvd_nat (card_dvd_of_le inf_le_left)) ?_ (inf_le_right.trans hAK) hx'' hxk
  exact (le_inf hKO (hKA.trans le_normalizer)).trans (inf_normalizer_le_normalizer_inf O A)

omit [Finite G] in
theorem normalizer_le_normalizer_oUpperTwoPrime [Finite G] (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (oUpperTwoPrime X : Set G) := by
  intro g hg
  have hle : (oUpperTwoPrime X).map (MulAut.conj g).toMonoidHom ≤ oUpperTwoPrime X := by
    rw [oUpperTwoPrime, MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, ⟨hxX, j, hj⟩, rfl⟩
    refine subset_closure ⟨(mem_normalizer_iff.mp hg x).mp hxX, j, ?_⟩
    show (g * x * g⁻¹) ^ (2 ^ j) = 1
    rw [conj_pow, hj, mul_one, mul_inv_cancel]
  exact mem_normalizer_iff_map_conj_eq.mpr
    (eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective]))

omit [Finite G] in
theorem oUpperTwoPrime_le (X : Subgroup G) : oUpperTwoPrime X ≤ X :=
  (closure_le X).mpr fun _ hx => hx.1

theorem odd_card_quotient_of_oUpperTwoPrime_le {X N : Subgroup G}
    [(N.subgroupOf X).Normal] (h2 : oUpperTwoPrime X ≤ N) :
    Odd (Nat.card (X ⧸ N.subgroupOf X)) := by
  by_contra hev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2
    (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
  obtain ⟨y, -, ⟨j, hj⟩, hy⟩ := exists_two_element_pow (QuotientGroup.mk' (N.subgroupOf X))
    (k := 1) (by rw [pow_one, ← hz, pow_orderOf_eq_one])
  have hyN : (y : G) ∈ oUpperTwoPrime X :=
    subset_closure ⟨y.2, j, by simpa using congrArg Subtype.val hj⟩
  have h1 : QuotientGroup.mk' (N.subgroupOf X) y = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (h2 hyN)
  rw [hy] at h1
  rw [h1, orderOf_one] at hz
  norm_num at hz

theorem le_oUpperTwoPrime_sup_oddCoreIn {K : Subgroup G} (hs : IsSemisimpleQ K) :
    K ≤ oUpperTwoPrime K ⊔ oddCoreIn K := by
  set N := oUpperTwoPrime K ⊔ oddCoreIn K with hN
  have hNK : N ≤ K := sup_le (oUpperTwoPrime_le K) (oddCoreIn_le K)
  have hNn : (N.subgroupOf K).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hNK]
    intro g hg
    have h1 := normalizer_le_normalizer_oUpperTwoPrime K (le_normalizer hg)
    have h2 := normalIn_le_normalizer (oddCoreIn_normalIn K) hg
    rw [mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [Subgroup.map_sup, h1, h2]
  by_contra hle
  set Kb := K ⧸ N.subgroupOf K
  have hnt : Nontrivial Kb := by
    rw [QuotientGroup.nontrivial_iff]
    intro h
    apply hle
    intro x hx
    have : (⟨x, hx⟩ : K) ∈ N.subgroupOf K := h ▸ mem_top _
    exact this
  have hodd : Odd (Nat.card Kb) := odd_card_quotient_of_oUpperTwoPrime_le le_sup_left
  have hle' : CFSG.Assembly.oddCore K ≤ N.subgroupOf K := by
    rw [← oddCoreIn_subgroupOf]
    exact subgroupOf_mono K le_sup_right
  let f : K ⧸ CFSG.Assembly.oddCore K →* Kb :=
    QuotientGroup.map _ _ (MonoidHom.id K) hle'
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
    exact ⟨QuotientGroup.mk' _ x, rfl⟩
  have hlay : CFSG.layer Kb = ⊤ := layer_eq_top_of_surjective f hf hs
  have hlay' : CFSG.layer Kb ≠ ⊥ := by
    rw [hlay]
    exact top_ne_bot
  exact not_isSolvable_of_layer_ne_bot (M := ⊤) le_top hlay'
    (by
      have := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
      exact Group.isSolvable_of_isSolvable_injective (f := (⊤ : Subgroup Kb).subtype)
        (⊤ : Subgroup Kb).subtype_injective)

theorem aschbacherThm5IsSemisimple_of_layer_eq_top {Y : Type*} [Group Y] [Finite Y]
    {X : Subgroup Y} (hX : CFSG.layer X = ⊤) (hne : X ≠ ⊥) :
    CFSG.Open.aschbacherThm5IsSemisimple X := by
  classical
  set S : Finset (Subgroup X) := (Set.toFinite {C : Subgroup X | CFSG.IsComponent C}).toFinset
  set e := S.equivFin
  have hmem : ∀ i : Fin S.card, CFSG.IsComponent (e.symm i : Subgroup X) := by
    intro i
    have h := (e.symm i).2
    simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at h
    exact h
  refine ⟨S.card, fun i => (e.symm i : Subgroup X).map X.subtype, ?_, fun i => ⟨map_subtype_le _,
    ?_⟩, fun i j hij x hx y hy => ?_, ?_⟩
  ·
    rw [Finset.card_pos]
    by_contra hS
    rw [Finset.not_nonempty_iff_eq_empty] at hS
    apply hne
    have hbot : CFSG.layer X = ⊥ := by
      refine CFSG.LocalCores.layer_eq_bot_of_forall fun C hC => ?_
      have : C ∈ S := by simpa [S] using hC
      rw [hS] at this
      exact absurd this (Finset.notMem_empty _)
    rw [hX] at hbot
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx⟩ : X) ∈ (⊤ : Subgroup X) := mem_top _
    rw [hbot, mem_bot] at this
    simpa using congrArg Subtype.val this
  ·
    have hq := (hmem i).1
    have hq' := CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((e.symm i : Subgroup X).equivMapOfInjective X.subtype X.subtype_injective) hq
    exact ⟨hq'.1.commutator_eq_top, hq'.2.1⟩
  ·
    have hne' : (e.symm i : Subgroup X) ≠ (e.symm j : Subgroup X) := fun h =>
      hij (e.symm.injective (Subtype.ext h))
    rcases CFSG.LocalCores.distinct_components_commute (hmem i) (hmem j) with h | h
    · exact absurd h hne'
    · obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      have := (commutator_eq_bot_iff_le_centralizer.mp h) hx'
      have := mem_centralizer_iff.mp this y' hy'
      simp only [coe_subtype]
      exact (congrArg Subtype.val this).symm
  ·
    apply le_antisymm (iSup_le fun i => map_subtype_le _)
    have hle : CFSG.layer X ≤ ⨆ i, (e.symm i : Subgroup X) := by
      refine sSup_le fun C hC => ?_
      have hCS : C ∈ S := by simpa [S] using hC
      exact le_iSup_of_le (e ⟨C, hCS⟩) (by simp)
    rw [hX] at hle
    intro x hx
    have h1 : (⟨x, hx⟩ : X) ∈ ⨆ i, (e.symm i : Subgroup X) := hle (mem_top _)
    have h2 := mem_map_of_mem X.subtype h1
    rw [Subgroup.map_iSup] at h2
    exact h2

omit [Finite G] in
theorem isSubnormal_subgroupOf_of_normalIn {Y D M : Subgroup G} (h1 : NormalIn Y D)
    (h2 : NormalIn D M) : (Y.subgroupOf M).IsSubnormal := by
  have hYM : Y ≤ M := h1.1.trans h2.1
  refine IsSubnormal.step _ (D.subgroupOf M) (subgroupOf_mono M h1.1) h2.2.isSubnormal ?_
  rw [normal_subgroupOf_iff_le_normalizer (subgroupOf_mono M h1.1),
    ← subgroupOf_normalizer_eq hYM]
  exact subgroupOf_mono M (normalIn_le_normalizer h1)

section TypeZero

variable {G : Type} [Group G] [Finite G]

theorem coversLayer_rightConjugate_iff {X A : Subgroup G} {g : G} :
    CoversLayer (rightConjugate X g) (rightConjugate A g) ↔ CoversLayer X A := by
  unfold CoversLayer
  rw [twoPrimeLayerIn_rightConjugate, oddCoreIn_rightConjugate]
  have hC : centralizer (rightConjugate X g : Set G) =
      rightConjugate (centralizer (X : Set G)) g :=
    (AschbacherTheorem3.rightConjugate_centralizer X g).symm
  rw [hC, ← AschbacherTheorem3.rightConjugate_inf, rightConjugate, rightConjugate,
    rightConjugate, ← Subgroup.map_sup]
  exact map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective

end TypeZero

end CFSG.ComponentClassification.Asc75T4
