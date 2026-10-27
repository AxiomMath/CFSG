module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerActiveCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreTwoComponents
public import CFSG.LocalAnalysis.StandardType.GGPumpupQuot

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup

variable {H : Type*} [Group H]

theorem map_mem_normalizer {G' : Type*} [Group G'] (f : H →* G') {L : Subgroup H} {g : H}
    (hg : g ∈ normalizer (L : Set H)) : f g ∈ normalizer ((L.map f : Subgroup G') : Set G') := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (L.map f).map (MulAut.conj (f g)).toMonoidHom = L.map f
  rw [map_conj_eq_conjugate, ← map_inv, ← map_conjugate, ← map_conj_eq_conjugate]
  congr 1
  exact mem_normalizer_iff_map_conj_eq.mp hg

theorem commutator_isSubnormal {L A : Subgroup H} (hL : L.IsSubnormal)
    (hA : A ≤ normalizer (L : Set H)) : (⁅L, A⁆ : Subgroup H).IsSubnormal :=
  IsSubnormal.step _ L (commutator_le_left_of_le_normalizer hA) hL
    ((normal_subgroupOf_iff_le_normalizer (commutator_le_left_of_le_normalizer hA)).mpr
      (le_normalizer_commutator L A))

theorem eq_of_le_of_map_eq {p : ℕ} {L J : Subgroup H} (hL : IsPComponent p L) (hJL : J ≤ L)
    (hJ : J.IsSubnormal)
    (hmap : J.map (QuotientGroup.mk' (pPrimeCore p H)) =
      L.map (QuotientGroup.mk' (pPrimeCore p H))) : J = L := by
  obtain ⟨K, -, -, hLK, hmin⟩ := hL
  by_contra hne
  exact hmin J (lt_of_le_of_ne hJL hne) hJ (hmap.trans hLK)

variable [Finite H]

theorem odd_fixed_core_active_two_component {t : H} (ht : orderOf t = 2) {D : Subgroup H}
    (hDC : D ≤ centralizer ({t} : Set H))
    (hDn : (D.subgroupOf (centralizer ({t} : Set H))).Normal) (hDodd : Odd (Nat.card D))
    {L : Subgroup H} (hL : IsPComponent 2 L)
    (hLD : ¬ ⁅L, D⁆ ≤ (pPrimeCore 2 L).map L.subtype) :
    D ≤ normalizer (L : Set H) ∧ t ∈ normalizer (L : Set H) ∧ ⁅L, D⁆ = L ∧
      ⁅L, zpowers t⁆ = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hRodd : Odd (Nat.card (pPrimeCore 2 H)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hDL := odd_fixed_core_normalizes_two_components ht hDC hDn hDodd L hL
  have hDLt := odd_fixed_core_normalizes_two_components ht hDC hDn hDodd _
    (isPComponent_conjugate hL t)
  obtain ⟨hDbC, hDbn⟩ := map_normal_centralizer hRodd htt hDC hDn
  have hDbodd : Odd (Nat.card (D.map (QuotientGroup.mk' (pPrimeCore 2 H)))) :=
    hDodd.of_dvd_nat (Subgroup.card_map_dvd D _)
  have htb : QuotientGroup.mk' (pPrimeCore 2 H) t * QuotientGroup.mk' (pPrimeCore 2 H) t = 1 := by
    rw [← map_mul, htt, map_one]
  obtain ⟨K, hK, hLsub, hLK, -⟩ := id hL
  have hDbK : D.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤ normalizer (K : Set _) := by
    rw [← hLK]
    intro x hx
    obtain ⟨d, hd, rfl⟩ := mem_map.mp hx
    exact map_mem_normalizer _ (hDL hd)
  have hDbKt : D.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤
      normalizer (conjugate K (QuotientGroup.mk' (pPrimeCore 2 H) t) : Set _) := by
    rw [← hLK, ← map_conjugate]
    intro x hx
    obtain ⟨d, hd, rfl⟩ := mem_map.mp hx
    exact map_mem_normalizer _ (hDLt hd)
  have heven : Even (Nat.card (K ⧸ center K)) := by
    have : IsSimpleGroup (K ⧸ center K) := hK.1.2.1
    exact (SimpleEvenOrder.nonabelian_simple_even hK.1.2.2).1
  have hne : ⁅K, D.map (QuotientGroup.mk' (pPrimeCore 2 H))⁆ ≠ ⊥ := by
    intro hbot
    apply hLD
    rw [← hLK, ← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 L hLsub,
      subgroupOf_map_subtype]
    exact le_inf hbot (commutator_le_left_of_le_normalizer hDL)
  obtain ⟨htK, hKD, hKt⟩ := active_component htb hDbC hDbn hDbodd hK heven hDbK hDbKt hne
  have htL : t ∈ normalizer (L : Set H) := mem_normalizer_of_map hL (by rw [hLK]; exact htK)
  have htLz : zpowers t ≤ normalizer (L : Set H) := zpowers_le.mpr htL
  refine ⟨hDL, htL, ?_, ?_⟩
  · apply eq_of_le_of_map_eq hL (commutator_le_left_of_le_normalizer hDL)
      (commutator_isSubnormal hLsub hDL)
    rw [map_commutator, hLK, hKD]
  · apply eq_of_le_of_map_eq hL (commutator_le_left_of_le_normalizer htLz)
      (commutator_isSubnormal hLsub htLz)
    rw [map_commutator, hLK, MonoidHom.map_zpowers, hKt]

end CFSG.ComponentClassification.UnbalancedLayer

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

theorem target_stable_of_central_actor
    {C : Type} [Group C] [Finite C] {a q s : C} {R : Subgroup C}
    (hsaq : s = a * q) (hscent : s ∈ Subgroup.center C)
    (hqlayer : q ∈ pLayer C 2) (hR : IsPComponent 2 R) :
    conjugate R a = R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haq : a = s * q⁻¹ := by simp [hsaq, mul_assoc]
  have haNorm : a ∈ normalizer (R : Set C) := by
    rw [haq]
    exact mul_mem (Subgroup.center_le_normalizer R hscent)
      (inv_mem (CFSG.StandardType.GGPumpup.pLayer_le_normalizer hR hqlayer))
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem haNorm)


theorem target_stable_fixed_component
    {C : Type} [Group C] [Finite C] {a q s : C} {Tq R : Subgroup C}
    (hsaq : s = a * q) (hscent : s ∈ Subgroup.center C)
    (hqlayer : q ∈ pLayer C 2)
    (hR : IsPComponent 2 R)
    (hTq_le : Tq ≤ (R ⊔ conjugate R a) ⊓ Subgroup.centralizer ({a} : Set C))
    (hTq_pc : IsPComponent 2 (Tq.subgroupOf
      ((R ⊔ conjugate R a) ⊓ Subgroup.centralizer ({a} : Set C)))) :
    conjugate R a = R ∧ Tq ≤ R ⊓ Subgroup.centralizer ({a} : Set C) ∧
      IsPComponent 2 (Tq.subgroupOf (R ⊓ Subgroup.centralizer ({a} : Set C))) := by
  have hRa : conjugate R a = R :=
    target_stable_of_central_actor hsaq hscent hqlayer hR
  have hTqR : Tq ≤ R := by
    have hle : Tq ≤ R ⊔ conjugate R a := hTq_le.trans inf_le_left
    simpa [hRa, sup_idem] using hle
  have hTqC : Tq ≤ Subgroup.centralizer ({a} : Set C) := hTq_le.trans inf_le_right
  have hTqRC : Tq ≤ R ⊓ Subgroup.centralizer ({a} : Set C) := le_inf hTqR hTqC
  have hX : (R ⊔ conjugate R a) ⊓ Subgroup.centralizer ({a} : Set C) =
      R ⊓ Subgroup.centralizer ({a} : Set C) := by
    rw [hRa, sup_idem]
  have hpc : IsPComponent 2 (Tq.subgroupOf
      (R ⊓ Subgroup.centralizer ({a} : Set C))) := by
    rw [hX] at hTq_pc
    exact hTq_pc
  exact ⟨hRa, hTqRC, hpc⟩


theorem target_stable_from_fixed_component
    {C : Type} [Group C] [Finite C] {a q s : C} {Tq R : Subgroup C}
    (hsaq : s = a * q) (hscent : s ∈ Subgroup.center C)
    (hqTq : q ∈ Tq) (hTq_layer : Tq ≤ pLayer C 2)
    (hR : IsPComponent 2 R)
    (hTq_le : Tq ≤ (R ⊔ conjugate R a) ⊓ Subgroup.centralizer ({a} : Set C))
    (hTq_pc : IsPComponent 2 (Tq.subgroupOf
      ((R ⊔ conjugate R a) ⊓ Subgroup.centralizer ({a} : Set C)))) :
    conjugate R a = R ∧ Tq ≤ R ⊓ Subgroup.centralizer ({a} : Set C) ∧
      IsPComponent 2 (Tq.subgroupOf (R ⊓ Subgroup.centralizer ({a} : Set C))) :=
  target_stable_fixed_component hsaq hscent (hTq_layer hqTq) hR hTq_le hTq_pc

end CFSG.ComponentClassification.GrSLit
