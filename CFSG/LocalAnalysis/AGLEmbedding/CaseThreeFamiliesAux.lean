module

public import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponents
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {X : Type*} [Group X] [Finite X] {K : Subgroup X}

omit [Finite X] in
theorem normal_of_forall_isComponentOf_eq (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup X, IsComponentOf L ⊤ → L = K) : K.Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [← huniq _ ((ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) K).mpr hK)]
  exact ⟨n, hn, rfl⟩

omit [Finite X] in
theorem mem_map_center_of_mem_of_mem_centralizer {c : X} (hcK : c ∈ K)
    (hc : c ∈ Subgroup.centralizer (K : Set X)) : c ∈ (Subgroup.center K).map K.subtype :=
  ⟨⟨c, hcK⟩, Subgroup.mem_center_iff.mpr fun k =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp hc k k.2), rfl⟩

theorem mem_of_mem_centralizer_of_orderOf_eq {p : ℕ} [Fact p.Prime] (R : Sylow p X)
    (hKn : K.Normal)
    (hR : ∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = p → c ∈ K)
    {c : X} (hc : c ∈ Subgroup.centralizer (K : Set X)) (hcp : orderOf c = p) : c ∈ K := by
  have : K.Normal := hKn
  have hZ : IsPGroup p (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hcp, pow_one])
  obtain ⟨S, hS⟩ := hZ.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X R S
  have hcS : c ∈ ((g • R : Sylow p X) : Subgroup X) := hS (Subgroup.mem_zpowers c)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    ← map_inv, MulAut.conj_apply, inv_inv] at hcS
  have hord : orderOf (g⁻¹ * c * g) = p := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) c
    rwa [MulAut.conj_apply, inv_inv, hcp] at h
  have hd := hR _ ⟨hcS, (inferInstance : (Subgroup.centralizer (K : Set X)).Normal).conj_mem'
    c hc g⟩ hord
  simpa [mul_assoc] using hKn.conj_mem _ hd g

theorem isPGroup_centralizer_of_forall_mem {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hcore : primeComplementCore (G := X) p = ⊥) (hKn : K.Normal)
    (hmem : ∀ c ∈ Subgroup.centralizer (K : Set X), orderOf c = p → c ∈ K) :
    IsPGroup p (Subgroup.centralizer (K : Set X)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : K.Normal := hKn
  set C := Subgroup.centralizer (K : Set X)
  have hall : ∀ t : C, orderOf t = p → t ∈ Subgroup.center C := by
    intro t ht
    have htK : (t : X) ∈ K := hmem t t.2 (by rwa [Subgroup.orderOf_coe])
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp g.2 t htK).symm
  obtain ⟨N, hNn, hNcop, k, hk⟩ := (GroupTheory.frobenius_normal_p_complement (G := C) p).1.2
    (isPGroup_automizer_of_forall_orderOf_eq_mem_center hodd hall)
  have hsub : IsSubnormal (N.map C.subtype) ⊤ := by
    refine IsSubnormal.step (Subgroup.map_subtype_le N) ?_
      (IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤))
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    exact hNn
  have hbot := eq_bot_of_isSubnormal_of_coprime hcore hsub (by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hNcop.symm)
  rw [Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective] at hbot
  rw [hbot, Subgroup.index_bot] at hk
  exact IsPGroup.of_card hk

theorem centralizer_eq_bot_of_forall_mem {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hcore : primeComplementCore (G := X) p = ⊥) (hKn : K.Normal)
    (hmem : ∀ c ∈ Subgroup.centralizer (K : Set X), orderOf c = p → c ∈ K)
    (hZ : Subgroup.center K = ⊥) : Subgroup.centralizer (K : Set X) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  obtain ⟨c, hcC, hcp, -⟩ := exists_mem_centralizer_orderOf_eq
    (isPGroup_centralizer_of_forall_mem hp hodd hcore hKn hmem) hne
  have hcZ := mem_map_center_of_mem_of_mem_centralizer (hmem c hcC hcp) hcC
  rw [hZ, Subgroup.map_bot, Subgroup.mem_bot] at hcZ
  rw [hcZ, orderOf_one] at hcp
  exact hp.one_lt.ne hcp

theorem isCyclic_centralizer_of_forall_mem {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hcore : primeComplementCore (G := X) p = ⊥) (hKn : K.Normal)
    (hmem : ∀ c ∈ Subgroup.centralizer (K : Set X), orderOf c = p → c ∈ K)
    (hZ : IsCyclic ((Subgroup.center K).map K.subtype)) :
    IsCyclic (Subgroup.centralizer (K : Set X)) := by
  by_contra hnc
  obtain ⟨F, hFC, hF, hFcard⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp
    (two_le_pRank_of_isPGroup_not_isCyclic hp hodd
      (isPGroup_centralizer_of_forall_mem hp hodd hcore hKn hmem) hnc)
  have hFZ : F ≤ (Subgroup.center K).map K.subtype := by
    intro x hx
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hF.2 x hx)) with h1 | h1
    · rw [orderOf_eq_one_iff.mp h1]
      exact Subgroup.one_mem _
    · exact mem_map_center_of_mem_of_mem_centralizer (hmem x (hFC hx) h1) (hFC hx)
  have : IsCyclic F := Subgroup.isCyclic_of_le hFZ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F)
  have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos (by
    rw [← hFcard, ← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (hF.2 g g.2)))
  nlinarith [hp.two_le]

end CFSG.AGLEmbedding
