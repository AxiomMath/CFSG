module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBSharedCore
public import CFSG.CharacterTheory.Semidihedral.StructureTransport
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup
open scoped commutatorElement Pointwise

variable {H : Type*} [Group H]

@[expose] def coreActionKernel (J : Subgroup H) : Subgroup H where
  carrier := {g | g ∈ normalizer (J : Set H) ∧
    ∀ j ∈ J, j⁻¹ * g⁻¹ * j * g ∈ (pPrimeCore 2 J).map J.subtype}
  one_mem' := ⟨one_mem _, fun j _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hgN, hg⟩ ⟨hhN, hh⟩
    refine ⟨mul_mem hgN hhN, fun j hj => ?_⟩
    have hO := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J (pPrimeCore 2 J)
      (inv_mem hhN)
    have h1 := (mem_normalizer_iff.mp hO _).mp (hg j hj)
    rw [inv_inv] at h1
    rw [show j⁻¹ * (g * h)⁻¹ * j * (g * h) =
      (j⁻¹ * h⁻¹ * j * h) * (h⁻¹ * (j⁻¹ * g⁻¹ * j * g) * h) by group]
    exact mul_mem (hh j hj) h1
  inv_mem' := by
    rintro g ⟨hgN, hg⟩
    refine ⟨inv_mem hgN, fun j hj => ?_⟩
    have h1 := inv_mem (hg _ ((mem_normalizer_iff.mp hgN j).mp hj))
    rwa [show ((g * j * g⁻¹)⁻¹ * g⁻¹ * (g * j * g⁻¹) * g)⁻¹ = j⁻¹ * g⁻¹⁻¹ * j * g⁻¹ by
      group] at h1

theorem mem_coreActionKernel {J : Subgroup H} {g : H} :
    g ∈ coreActionKernel J ↔ g ∈ normalizer (J : Set H) ∧
      ∀ j ∈ J, j⁻¹ * g⁻¹ * j * g ∈ (pPrimeCore 2 J).map J.subtype :=
  Iff.rfl

variable [Finite H]

theorem eq_bot_of_le_two_group_of_le_odd {X P O : Subgroup H} (hP : IsPGroup 2 P)
    (hO : Odd (Nat.card O)) (hXP : X ≤ P) (hXO : X ≤ O) : X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (hP.to_le hXP).exists_card_eq
  have hdvd : Nat.card X ∣ Nat.card O := Subgroup.card_dvd_of_le hXO
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact card_eq_one.mp hk
  · exfalso
    rw [hk] at hdvd
    exact (Nat.not_even_iff_odd.mpr hO)
      (even_iff_two_dvd.mpr ((dvd_pow_self 2 k.succ_ne_zero).trans hdvd))

omit [Finite H] in
theorem pRank_two_le_one_of_card_sylow_le {A : Type*} [Group A] [Finite A]
    (h : ∀ T : Sylow 2 A, Nat.card T ≤ 2) : pRank 2 A ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold pRank
  apply csSup_le'
  rintro r ⟨E, hE, hcard⟩
  obtain ⟨T, hT⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  have h1 : 2 ^ r ≤ Nat.card T := by
    rw [← hcard]
    exact card_le_of_le hT
  have h2 := h T
  by_contra hr
  have h4 : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at h4
  omega

theorem semidihedral_action_kernel_exact_two_component_list {J L : Subgroup H} (hJL : J ≠ L)
    (hJ : IsPComponent 2 J) (hL : IsPComponent 2 L) (hLQ : L ≤ coreActionKernel J)
    (hLn : (L.subgroupOf (coreActionKernel J)).Normal) {P : Subgroup H}
    (hPQ : P ≤ coreActionKernel J)
    (hPsyl : ∃ S : Sylow 2 (coreActionKernel J),
      (S : Subgroup (coreActionKernel J)) = P.subgroupOf (coreActionKernel J))
    {r : ℕ} (hr : 3 ≤ r)
    (hDQ : Nonempty ((P ⊓ L : Subgroup H) ≃* QuaternionGroup (2 ^ (r - 2))))
    (hidx : (P ⊓ L).relIndex P = 2) {e : ℕ} (he : 4 ≤ e)
    (hPSD : Nonempty (P ≃* Open.SemidihedralGroup e)) :
    {M : Subgroup H | IsPComponent 2 M} = {J, L} ∧ pLayer H 2 = J ⊔ L ∧
      ((J ⊔ L : Subgroup H) : Set H) = (J : Set H) * L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eD⟩ := hDQ
  obtain ⟨fP⟩ := hPSD
  have hm : 0 < 2 ^ (r - 2) := Nat.two_pow_pos _
  have hm2 : 2 ≤ 2 ^ (r - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hQN : coreActionKernel J ≤ normalizer (L : Set H) :=
    (normal_subgroupOf_iff_le_normalizer hLQ).mp hLn
  have hPN : P ≤ normalizer (L : Set H) := hPQ.trans hQN
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := e) (by
    rw [Nat.card_congr fP.toEquiv, (CFSG.Semidihedral.normal_form e he).2.1])
  set z : H := ((eD.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))))) : H)
    with hzdef
  have hzD : z ∈ P ⊓ L := (eD.symm _).2
  have hzP : z ∈ P := (mem_inf.mp hzD).1
  have hz2 : orderOf z = 2 := by
    rw [hzdef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact (CFSG.Semidihedral.QuaternionAutomorphismLifting.unique_involution _ hm _).2 rfl
  have hzuniq : ∀ x ∈ P ⊓ L, orderOf x = 2 → x = z := by
    intro x hx hx2
    have h1 : orderOf (eD ⟨x, hx⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx2]
    have h2 := (CFSG.Semidihedral.QuaternionAutomorphismLifting.unique_involution _ hm _).1 h1
    rw [hzdef, ← h2, MulEquiv.symm_apply_apply]
  have hZD : ∀ x ∈ P ⊓ L, x ∈ centralizer ((P ⊓ L : Subgroup H) : Set H) → x ∈ zpowers z := by
    intro x hx hxc
    have hcen : eD ⟨x, hx⟩ ∈ center (QuaternionGroup (2 ^ (r - 2))) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := eD.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_iff.mp hxc y y.2)
    rcases ((CFSG.GroupTheory.quaternion_centralizers hm2).2.2.1 _).mp hcen with h | h
    · have hx1 : (⟨x, hx⟩ : (P ⊓ L : Subgroup H)) = 1 := by
        rw [← eD.map_eq_one_iff, h, QuaternionGroup.one_def]
      rw [show x = 1 from congrArg Subtype.val hx1]
      exact one_mem _
    · have hxz : x = z := by
        rw [hzdef, ← h, MulEquiv.symm_apply_apply]
      rw [hxz]
      exact mem_zpowers z
  have hzcen : (⟨z, hzP⟩ : P) ∈ center P := by
    rw [mem_center_iff]
    intro p
    apply Subtype.ext
    have hpz : (p : H) * z * (p : H)⁻¹ ∈ P ⊓ L :=
      mem_inf.mpr ⟨mul_mem (mul_mem p.2 hzP) (inv_mem p.2),
        (mem_normalizer_iff.mp (hPN p.2) z).mp (mem_inf.mp hzD).2⟩
    have hpz2 : orderOf ((p : H) * z * (p : H)⁻¹) = 2 := by
      have h := MulEquiv.orderOf_eq (MulAut.conj (p : H)) z
      rw [MulAut.conj_apply] at h
      rw [h, hz2]
    have hpzz := hzuniq _ hpz hpz2
    change (p : H) * z = z * p
    calc (p : H) * z = ((p : H) * z * (p : H)⁻¹) * p := by group
      _ = z * p := by rw [hpzz]
  have hcenP : center P = zpowers (⟨z, hzP⟩ : P) := by
    symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr hzcen)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz2,
      (CFSG.Semidihedral.supplied_index_two_and_element_structure e he fP.symm).2.1]
  have hCPD : ∀ x ∈ P, x ∈ centralizer ((P ⊓ L : Subgroup H) : Set H) → x ∈ P ⊓ L := by
    intro x hxP hxc
    by_contra hxD
    have hidx' : ((P ⊓ L).subgroupOf P).index = 2 := hidx
    have hxcen : (⟨x, hxP⟩ : P) ∈ center P := by
      rw [mem_center_iff]
      intro p
      apply Subtype.ext
      change (p : H) * x = x * p
      by_cases hpD : (p : H) ∈ P ⊓ L
      · exact mem_centralizer_iff.mp hxc p hpD
      · have hpx : p * (⟨x, hxP⟩ : P)⁻¹ ∈ (P ⊓ L).subgroupOf P := by
          rw [mul_mem_iff_of_index_two hidx']
          refine iff_of_false hpD fun h => hxD ?_
          have h' := inv_mem (mem_subgroupOf.mp h)
          simpa using h'
        have hd : (p : H) * x⁻¹ ∈ P ⊓ L := hpx
        have hdx := mem_centralizer_iff.mp hxc _ hd
        calc (p : H) * x = (p * x⁻¹) * x * x := by group
          _ = x * (p * x⁻¹) * x := by rw [hdx]
          _ = x * p := by group
    rw [hcenP] at hxcen
    apply hxD
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hxcen
    have hxk : x = z ^ k := by
      have h := congrArg Subtype.val hk
      simpa using h.symm
    rw [hxk]
    exact zpow_mem hzD k
  have hthird : ∀ K : Subgroup H, IsPComponent 2 K → K ≠ J → K ≠ L → False := by
    intro K hK hKJ hKL
    have hKQ : ∀ K' : Subgroup H, IsPComponent 2 K' → K' ≠ J → K' ≤ coreActionKernel J := by
      intro K' hK' hK'J g hg
      obtain ⟨-, hrest⟩ :=
        CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two J K' hJ hK'
      obtain ⟨hK'N, -, hcore, -⟩ := hrest (Ne.symm hK'J)
      refine ⟨hK'N hg, fun j hj => ?_⟩
      have hmem : j⁻¹ * g⁻¹ * j * g ∈ ⁅J, K'⁆ := by
        rw [show j⁻¹ * g⁻¹ * j * g = ⁅j⁻¹, g⁻¹⁆ by rw [commutatorElement_def, inv_inv, inv_inv]]
        exact commutator_mem_commutator (inv_mem hj) (inv_mem hg)
      exact (mem_inf.mp (hcore hmem)).1
    have hKQ' := hKQ K hK hKJ
    obtain ⟨S₀, hS₀⟩ := hPsyl
    let RK : Sylow 2 K := default
    set R : Subgroup H := (RK : Subgroup K).map K.subtype with hRdef
    have hRK : R ≤ K := map_subtype_le _
    have hR2 : IsPGroup 2 (R.subgroupOf (coreActionKernel J)) :=
      (RK.isPGroup'.map K.subtype).comap_of_injective _ (coreActionKernel J).subtype_injective
    obtain ⟨S, hRS⟩ := hR2.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (coreActionKernel J) S₀ S
    set q : H := (g : H) with hqdef
    have hqQ : q ∈ coreActionKernel J := g.2
    have hRP : conjugate R q ≤ P := by
      intro x hx
      rw [mem_conjugate_iff] at hx
      have h1 : (⟨q * x * q⁻¹, hKQ' (hRK hx)⟩ : coreActionKernel J) ∈ (S : Subgroup _) :=
        hRS (show _ ∈ R.subgroupOf (coreActionKernel J) from hx)
      rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
        MulAut.inv_def, MulAut.conj_symm_apply, hS₀, mem_subgroupOf] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rwa [show q⁻¹ * (q * x * q⁻¹) * q = x by group] at h1
    have hK₁ : IsPComponent 2 (conjugate K q) := isPComponent_conjugate hK q
    have hK₁L : conjugate K q ≠ L := by
      intro h
      apply hKL
      rw [← conjugate_conjugate_inv K q, h, conjugate_eq_of_mem_normalizer (inv_mem (hQN hqQ))]
    obtain ⟨-, hrestL⟩ :=
      CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ L hK₁ hL
    obtain ⟨-, -, hcoreL, -⟩ := hrestL hK₁L
    have hLodd : Odd (Nat.card ((pPrimeCore 2 L).map L.subtype)) := by
      rw [card_map_of_injective L.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hRD : ⁅conjugate R q, P ⊓ L⁆ = ⊥ := by
      refine eq_bot_of_le_two_group_of_le_odd hP2 hLodd ?_ ?_
      · rw [commutator_le]
        intro a ha b hb
        have hbP := (mem_inf.mp hb).1
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem (hRP ha) hbP) (inv_mem (hRP ha))) (inv_mem hbP)
      · exact (commutator_mono (map_mono hRK) inf_le_right).trans (hcoreL.trans inf_le_right)
    have hRz : conjugate R q ≤ zpowers z := by
      intro x hx
      have hxc : x ∈ centralizer ((P ⊓ L : Subgroup H) : Set H) :=
        commutator_eq_bot_iff_le_centralizer.mp hRD hx
      exact hZD x (hCPD x (hRP hx) hxc) hxc
    have hRcard : Nat.card R ≤ 2 := by
      have h1 : Nat.card (conjugate R q) = Nat.card R := by
        unfold conjugate
        exact card_map_of_injective (MulAut.conj q⁻¹).injective
      rw [← h1]
      calc Nat.card (conjugate R q) ≤ Nat.card (zpowers z) := card_le_of_le hRz
        _ = 2 := by rw [Nat.card_zpowers, hz2]
    have hRKcard : Nat.card R = 2 ^ (Nat.card K).factorization 2 := by
      rw [hRdef, card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity]
    have hT : ∀ T : Sylow 2 (K ⧸ pPrimeCore 2 K), Nat.card T ≤ 2 := by
      intro T
      rw [Sylow.card_eq_multiplicity]
      have hdvd : Nat.card (K ⧸ pPrimeCore 2 K) ∣ Nat.card K := card_quotient_dvd_card _
      have hle : (Nat.card (K ⧸ pPrimeCore 2 K)).factorization 2 ≤ (Nat.card K).factorization 2 :=
        (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hdvd 2
      calc 2 ^ (Nat.card (K ⧸ pPrimeCore 2 K)).factorization 2
          ≤ 2 ^ (Nat.card K).factorization 2 := Nat.pow_le_pow_right (by norm_num) hle
        _ = Nat.card R := hRKcard.symm
        _ ≤ 2 := hRcard
    have hA := CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 K hK
    obtain ⟨-, -, -, hquat⟩ :=
      LocalAnalysis.ComponentInitial.quasisimple_rank_one_unique_central_involution hA
        (pRank_two_le_one_of_card_sylow_le hT)
    let T : Sylow 2 (K ⧸ pPrimeCore 2 K) := default
    obtain ⟨r', hr', ⟨eT⟩⟩ := hquat T
    have : NeZero (2 ^ (r' - 2)) := ⟨by positivity⟩
    have h8 : 8 ≤ Nat.card T := by
      rw [Nat.card_congr eT.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      have : 2 ≤ 2 ^ (r' - 2) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (r' - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have := hT T
    omega
  have hset : {M : Subgroup H | IsPComponent 2 M} = {J, L} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hM
      by_contra hne
      push Not at hne
      exact hthird M hM hne.1 hne.2
    · rintro (rfl | rfl)
      · exact hJ
      · exact hL
  refine ⟨hset, ?_, ?_⟩
  · rw [pLayer, hset, sSup_pair]
  · obtain ⟨-, hrest⟩ :=
      CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two J L hJ hL
    obtain ⟨-, hJNL, -, -⟩ := hrest hJL
    exact coe_mul_of_left_le_normalizer_right J L hJNL

end CFSG.ComponentClassification.UnbalancedLayer
