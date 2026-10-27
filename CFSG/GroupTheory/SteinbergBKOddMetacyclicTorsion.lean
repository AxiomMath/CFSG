module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_10

public section

namespace CFSG.GroupTheory.SteinbergBK

universe u

variable {p : ℕ} [hp : Fact p.Prime]

theorem isMetacyclic_quotient {P : Type*} [Group P] (hP : IsMetacyclic P) (K : Subgroup P)
    [K.Normal] : IsMetacyclic (P ⧸ K) := by
  obtain ⟨N, hN, hNc, hPN⟩ := hP
  have hN' : (N.map (QuotientGroup.mk' K)).Normal := hN.map _ (QuotientGroup.mk'_surjective K)
  refine ⟨N.map (QuotientGroup.mk' K), hN', ?_, ?_⟩
  · exact isCyclic_of_surjective ((QuotientGroup.mk' K).subgroupMap N)
      ((QuotientGroup.mk' K).subgroupMap_surjective N)
  · let ψ : P →* (P ⧸ K) ⧸ N.map (QuotientGroup.mk' K) :=
      (QuotientGroup.mk' _).comp (QuotientGroup.mk' K)
    have hle : N ≤ ψ.ker := fun n hn => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact Subgroup.mem_map_of_mem _ hn
    refine isCyclic_of_surjective (QuotientGroup.lift N ψ hle) fun y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K x
    exact ⟨QuotientGroup.mk g, rfl⟩

theorem isMetacyclic_subgroup {P : Type*} [Group P] (hP : IsMetacyclic P) (Q : Subgroup P) :
    IsMetacyclic Q ∧ IsCyclic (commutator Q) := by
  obtain ⟨N, hN, hNc, hPN⟩ := hP
  let f : Q →* P ⧸ N := (QuotientGroup.mk' N).comp Q.subtype
  have hker : f.ker = N.subgroupOf Q := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hNQc : IsCyclic (N.subgroupOf Q) := by
    have h1 : IsCyclic ↥(N ⊓ Q) := Subgroup.isCyclic_of_le inf_le_left
    rw [← Subgroup.subgroupOf_map_subtype] at h1
    exact ((N.subgroupOf Q).equivMapOfInjective Q.subtype Q.subtype_injective).isCyclic.mpr h1
  have hquot : IsCyclic (Q ⧸ N.subgroupOf Q) :=
    ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivRange f)).isCyclic.mpr inferInstance
  have hNQn : (N.subgroupOf Q).Normal := Subgroup.Normal.subgroupOf hN Q
  refine ⟨⟨N.subgroupOf Q, hNQn, hNQc, hquot⟩, ?_⟩
  have hcomm : IsMulCommutative (Q ⧸ N.subgroupOf Q) := by
    let _ := IsCyclic.commGroup (α := Q ⧸ N.subgroupOf Q)
    infer_instance
  have hle : commutator Q ≤ N.subgroupOf Q := by
    have h := Abelianization.commutator_subset_ker (QuotientGroup.mk' (N.subgroupOf Q))
    rwa [QuotientGroup.ker_mk'] at h
  exact Subgroup.isCyclic_of_le hle

theorem card_omega₁_le {P : Type*} [Group P] [Finite P] (hodd : p ≠ 2) (hP : IsPGroup p P)
    (hmeta : IsMetacyclic P) : Nat.card (omega₁ (G := P) (p := p)) ≤ p ^ 2 := by
  by_cases hcyc : IsCyclic P
  · have : IsMulCommutative P := ⟨⟨fun a b => IsCyclic.commGroup.mul_comm a b⟩⟩
    have helem := IsElementaryAbelian.omega₁_of_isMulCommutative (p := p) P
    have hexp := IsElementaryAbelian.exponent_dvd_p p (omega₁ (G := P) (p := p))
    rw [IsCyclic.exponent_eq_card] at hexp
    calc Nat.card (omega₁ (G := P) (p := p)) ≤ p := Nat.le_of_dvd hp.out.pos hexp
      _ ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  · have : Fact (IsPGroup p P) := ⟨hP⟩
    exact (CFSG.lemma_4_10 hodd hmeta hcyc).1.le

theorem card_torsion_le (hodd : p ≠ 2) (n : ℕ) :
    ∀ (P : Type u) [Group P] [Finite P], IsPGroup p P → IsMetacyclic P →
      Nat.card {x : P | x ^ p ^ n = 1} ≤ p ^ (2 * n) := by
  induction n with
  | zero =>
    intro P _ _ _ _
    have h : {x : P | x ^ p ^ 0 = 1} = {1} := by
      ext x
      simp
    rw [h, Nat.card_unique]
    simp
  | succ n ih =>
    intro P _ _ hP hmeta
    set K := omega₁ (G := P) (p := p) with hKdef
    have : K.Characteristic := omega₁_characteristic P
    have : K.Normal := inferInstance
    have hK := card_omega₁_le hodd hP hmeta
    have hsub : {x : P | x ^ p ^ (n + 1) = 1} ⊆
        (QuotientGroup.mk : P → P ⧸ K) ⁻¹' {y : P ⧸ K | y ^ p ^ n = 1} := by
      intro x hx
      change (x : P ⧸ K) ^ p ^ n = 1
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      apply Subgroup.subset_closure
      change (x ^ p ^ n) ^ p ^ 1 = 1
      rw [← pow_mul, pow_one, ← pow_succ]
      exact hx
    have hcard := QuotientGroup.card_preimage_mk K {y : P ⧸ K | y ^ p ^ n = 1}
    have hIH := ih (P ⧸ K) (hP.to_quotient K) (isMetacyclic_quotient hmeta K)
    calc Nat.card {x : P | x ^ p ^ (n + 1) = 1}
        ≤ Nat.card ((QuotientGroup.mk : P → P ⧸ K) ⁻¹' {y : P ⧸ K | y ^ p ^ n = 1}) :=
          Nat.card_mono (Set.toFinite _) hsub
      _ = Nat.card K * Nat.card {y : P ⧸ K | y ^ p ^ n = 1} := hcard
      _ ≤ p ^ 2 * p ^ (2 * n) := Nat.mul_le_mul hK hIH
      _ = p ^ (2 * (n + 1)) := by ring

theorem odd_metacyclic_torsion_counts (hodd : Odd p) {P : Type u}
    [Group P] [Finite P] (hP : IsPGroup p P) (C : Subgroup P) [hCn : C.Normal] (hC : IsCyclic C)
    (hPC : IsCyclic (P ⧸ C)) :
    (∀ n : ℕ, Set.ncard {x : P | x ^ p ^ n = 1} ≤ p ^ (2 * n)) ∧
      (∀ Q : Subgroup P, IsMetacyclic Q ∧ IsCyclic (commutator Q)) ∧
      (¬ IsCyclic P → ∃ T : Subgroup P, (T : Set P) = {x | x ^ p = 1} ∧ T.Characteristic ∧
        IsElementaryAbelian p T ∧ Nat.card T = p ^ 2 ∧
        Subgroup.closure {x : P | orderOf x = p} = T) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ Q : Subgroup P,
        Nonempty (Q ≃* Multiplicative (ZMod (p ^ n)) × Multiplicative (ZMod (p ^ n))) →
          (Q : Set P) = {x | x ^ p ^ n = 1} ∧ Q.Characteristic ∧
          ∀ Q' : Subgroup P,
            Nonempty (Q' ≃* Multiplicative (ZMod (p ^ n)) × Multiplicative (ZMod (p ^ n))) →
              Q' = Q) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hodd even_two
  have hmeta : IsMetacyclic P := ⟨C, hCn, hC, hPC⟩
  have htors : ∀ n : ℕ, Set.ncard {x : P | x ^ p ^ n = 1} ≤ p ^ (2 * n) := fun n => by
    rw [← Nat.card_coe_set_eq]
    exact card_torsion_le hp2 n P hP hmeta
  refine ⟨htors, fun Q => isMetacyclic_subgroup hmeta Q, fun hncyc => ?_, fun n hn Q hQ => ?_⟩
  ·
    have : Fact (IsPGroup p P) := ⟨hP⟩
    obtain ⟨hcard, helem⟩ := CFSG.lemma_4_10 hp2 hmeta hncyc
    have hset : ((omega₁ (G := P) (p := p) : Subgroup P) : Set P) = {x | x ^ p = 1} := by
      ext x
      refine ⟨fun hx => elemPow_eq_one_of_isElementaryAbelian x hx, fun hx => ?_⟩
      apply Subgroup.subset_closure
      change x ^ p ^ 1 = 1
      rwa [pow_one]
    refine ⟨omega₁ (G := P) (p := p), hset, omega₁_characteristic P, helem, hcard, ?_⟩
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr fun x hx => ?_
      rw [hset]
      change x ^ p = 1
      rw [← hx]
      exact pow_orderOf_eq_one x
    · refine (Subgroup.closure_le _).mpr fun x hx => ?_
      change x ^ p ^ 1 = 1 at hx
      rw [pow_one] at hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact one_mem _
      · exact Subgroup.subset_closure (orderOf_eq_prime hx hx1)
  ·
    have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
    have hcardZ : Nat.card (Multiplicative (ZMod (p ^ n))) = p ^ n := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    have hE : ∀ y : Multiplicative (ZMod (p ^ n)) × Multiplicative (ZMod (p ^ n)),
        y ^ p ^ n = 1 := fun y => by
      have h1 : y.1 ^ Nat.card (Multiplicative (ZMod (p ^ n))) = 1 := pow_card_eq_one'
      have h2 : y.2 ^ Nat.card (Multiplicative (ZMod (p ^ n))) = 1 := pow_card_eq_one'
      rw [hcardZ] at h1 h2
      exact Prod.ext (by rw [Prod.pow_fst, h1, Prod.fst_one]) (by rw [Prod.pow_snd, h2,
        Prod.snd_one])
    have hset : ∀ Q' : Subgroup P,
        Nonempty (Q' ≃* Multiplicative (ZMod (p ^ n)) × Multiplicative (ZMod (p ^ n))) →
          (Q' : Set P) = {x | x ^ p ^ n = 1} := by
      rintro Q' ⟨e⟩
      have hsub : (Q' : Set P) ⊆ {x | x ^ p ^ n = 1} := fun x hx => by
        have h := congrArg Subtype.val (e.injective (show e (⟨x, hx⟩ ^ p ^ n) = e 1 by
          rw [map_pow, hE, map_one]))
        simpa using h
      have hQ'card : Nat.card Q' = p ^ (2 * n) := by
        rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card,
          Fintype.card_multiplicative, ZMod.card, two_mul, pow_add]
      refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
      rw [← Nat.card_coe_set_eq (Q' : Set P)]
      change Set.ncard {x : P | x ^ p ^ n = 1} ≤ Nat.card Q'
      rw [hQ'card]
      exact htors n
    have hQset := hset Q hQ
    have huniq : ∀ Q' : Subgroup P,
        Nonempty (Q' ≃* Multiplicative (ZMod (p ^ n)) × Multiplicative (ZMod (p ^ n))) →
          Q' = Q := fun Q' hQ' => SetLike.coe_injective ((hset Q' hQ').trans hQset.symm)
    refine ⟨hQset, Subgroup.characteristic_iff_map_eq.mpr fun φ => huniq _ ?_, huniq⟩
    obtain ⟨e⟩ := hQ
    exact ⟨(Q.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans e⟩

end CFSG.GroupTheory.SteinbergBK
