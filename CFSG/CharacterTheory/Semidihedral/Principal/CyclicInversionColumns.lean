module

public import CFSG.CharacterTheory.Semidihedral.Principal.NormThreeGram
public import CFSG.CharacterTheory.Semidihedral.Principal.LinearTwistBlocks
public import CFSG.CharacterTheory.Semidihedral.Principal.SectionConstancy
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralCharacterFamily
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u

namespace CyclicInversion

variable {G : Type u} [Group G]

theorem le_centralizer_of_isCyclic (W : Subgroup G) [IsCyclic W] :
    W ≤ Subgroup.centralizer (W : Set G) := by
  let : CommGroup W := IsCyclic.commGroup
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : W) ⟨x, hx⟩)

variable [Fintype G] {p : ℕ} [Fact p.Prime]

omit [Fintype G] [Fact p.Prime] in
theorem sylow_le_centralizer (W : Sylow p G) [IsCyclic (W : Subgroup G)] :
    (W : Subgroup G) ≤ Subgroup.centralizer (W : Set G) :=
  le_centralizer_of_isCyclic (W : Subgroup G)

noncomputable abbrev centralizerSylow (W : Sylow p G) [IsCyclic (W : Subgroup G)] :
    Sylow p (Subgroup.centralizer (W : Set G)) :=
  W.subtype (sylow_le_centralizer W)

theorem exists_centralizer_normal_complement (W : Sylow p G) [IsCyclic (W : Subgroup G)] :
    ∃ (N : Subgroup (Subgroup.centralizer (W : Set G))) (_ : N.Normal),
      Nat.Coprime p (Nat.card N) ∧ IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N) := by
  apply CFSG.exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer p
    (centralizerSylow W)
  intro s hs
  have hsW : (s : G) ∈ (W : Subgroup G) := by
    have hs' : s ∈ ((centralizerSylow W : Sylow p _) :
        Subgroup (Subgroup.centralizer (W : Set G))) := hs
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hs'
    exact hs'
  have hcenter : s ∈ Subgroup.center (Subgroup.centralizer (W : Set G)) := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp k.2 _ hsW).symm
  exact ⟨Subgroup.le_normalizer hs, fun n _ => Subgroup.mem_center_iff.mp hcenter n⟩

section Complement

variable (W : Sylow p G) [IsCyclic (W : Subgroup G)]
  (N : Subgroup (Subgroup.centralizer (W : Set G))) [N.Normal]

omit [Fintype G] [Fact p.Prime] [IsCyclic (W : Subgroup G)] in
theorem mem_complement_iff (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N))
    (k : Subgroup.centralizer (W : Set G)) : k ∈ N ↔ Nat.Coprime p (orderOf k) := by
  constructor
  · intro hk
    have h := orderOf_dvd_natCard (⟨k, hk⟩ : N)
    rw [Subgroup.orderOf_mk] at h
    exact Nat.Coprime.coprime_dvd_right h hcop
  · intro hk
    obtain ⟨n, hn⟩ := hpq (QuotientGroup.mk k)
    have h1 : orderOf (QuotientGroup.mk k : Subgroup.centralizer (W : Set G) ⧸ N) ∣ p ^ n :=
      orderOf_dvd_of_pow_eq_one hn
    have h2 : orderOf (QuotientGroup.mk k : Subgroup.centralizer (W : Set G) ⧸ N) ∣ orderOf k :=
      orderOf_map_dvd (QuotientGroup.mk' N) k
    have h3 : Nat.Coprime (orderOf (QuotientGroup.mk k : Subgroup.centralizer (W : Set G) ⧸ N))
        (orderOf k) := Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left n hk)
    exact (QuotientGroup.eq_one_iff k).mp (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h3 h2))

theorem card_mul_card_complement (a : ℕ) (hWcard : Nat.card W = p ^ a)
    (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N)) :
    Nat.card ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))) * Nat.card N =
      Nat.card (Subgroup.centralizer (W : Set G)) := by
  have hp : p.Prime := Fact.out
  have hS : Nat.card ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))) = p ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (sylow_le_centralizer W)).toEquiv]
    exact hWcard
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hpq
  have hK := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [hb] at hK
  have hfactor : (Nat.card (Subgroup.centralizer (W : Set G))).factorization p = b := by
    rw [hK, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) Nat.card_pos.ne',
      Finsupp.add_apply, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop),
      add_zero]
  have hsylow := (centralizerSylow W).card_eq_multiplicity
  rw [hfactor] at hsylow
  have hsylow' : Nat.card ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))) =
      p ^ b := hsylow
  rw [hK, hsylow']

theorem isComplement'_complement (a : ℕ) (hWcard : Nat.card W = p ^ a)
    (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N)) :
    ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N := by
  apply Subgroup.isComplement'_of_coprime (card_mul_card_complement W N a hWcard hcop hpq)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (sylow_le_centralizer W)).toEquiv, hWcard]
  exact Nat.Coprime.pow_left a hcop

@[expose] noncomputable def complementProjection
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N) :
    Subgroup.centralizer (W : Set G) →* (W : Subgroup G) :=
  (Subgroup.subgroupOfEquivOfLe (sylow_le_centralizer W)).toMonoidHom.comp
    (hcomp.QuotientMulEquiv.toMonoidHom.comp (QuotientGroup.mk' N))

omit [Fintype G] [Fact p.Prime] in
theorem complementProjection_of_mem
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (k : Subgroup.centralizer (W : Set G)) (hk : (k : G) ∈ (W : Subgroup G)) :
    ((complementProjection W N hcomp k : (W : Subgroup G)) : G) = k := by
  have hk' : k ∈ (W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G)) := hk
  have hmk : (QuotientGroup.mk' N k : Subgroup.centralizer (W : Set G) ⧸ N) =
      hcomp.QuotientMulEquiv.symm ⟨k, hk'⟩ := by
    rw [Subgroup.IsComplement'.QuotientMulEquiv_symm_apply]
    rfl
  change (((Subgroup.subgroupOfEquivOfLe (sylow_le_centralizer W))
    (hcomp.QuotientMulEquiv (QuotientGroup.mk' N k)) : (W : Subgroup G)) : G) = k
  rw [hmk, MulEquiv.apply_symm_apply]
  rfl

omit [Fintype G] [Fact p.Prime] in
theorem complementProjection_of_mem_complement
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (k : Subgroup.centralizer (W : Set G)) (hk : k ∈ N) :
    complementProjection W N hcomp k = 1 := by
  change (Subgroup.subgroupOfEquivOfLe (sylow_le_centralizer W))
    (hcomp.QuotientMulEquiv (QuotientGroup.mk' N k)) = 1
  rw [show QuotientGroup.mk' N k = 1 from (QuotientGroup.eq_one_iff k).mpr hk, map_one, map_one]

omit [Fintype G] [Fact p.Prime] [IsCyclic (W : Subgroup G)] in
theorem mem_map_complement_iff (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N)) (g : G) :
    g ∈ N.map (Subgroup.centralizer (W : Set G)).subtype ↔
      g ∈ Subgroup.centralizer (W : Set G) ∧ Nat.Coprime p (orderOf g) := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.2, ?_⟩
    rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
    exact (mem_complement_iff W N hcop hpq k).mp hk
  · rintro ⟨hg, hcp⟩
    refine ⟨⟨g, hg⟩, (mem_complement_iff W N hcop hpq _).mpr ?_, rfl⟩
    rwa [Subgroup.orderOf_mk]

omit [Fintype G] [Fact p.Prime] [IsCyclic (W : Subgroup G)] [N.Normal] in
theorem card_map_complement :
    Nat.card (N.map (Subgroup.centralizer (W : Set G)).subtype) = Nat.card N :=
  Nat.card_congr (Subgroup.equivMapOfInjective N _ (Subgroup.subtype_injective _)).toEquiv.symm

omit [Fintype G] [Fact p.Prime] [IsCyclic (W : Subgroup G)] in
theorem inf_map_complement (a : ℕ) (hWcard : Nat.card W = p ^ a)
    (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N)) :
    (W : Subgroup G) ⊓ N.map (Subgroup.centralizer (W : Set G)).subtype = ⊥ := by
  rw [eq_bot_iff]
  intro g ⟨hgW, hgJ⟩
  have hcp := ((mem_map_complement_iff W N hcop hpq g).mp hgJ).2
  have hdvd : orderOf g ∣ p ^ a := by
    rw [← hWcard]
    exact Subgroup.orderOf_dvd_natCard _ hgW
  have h1 : orderOf g = 1 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left hdvd (Nat.Coprime.pow_left a hcp)) dvd_rfl
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)

omit [Fintype G] [Fact p.Prime] [N.Normal] in
theorem sup_map_complement
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N) :
    (W : Subgroup G) ⊔ N.map (Subgroup.centralizer (W : Set G)).subtype =
      Subgroup.centralizer (W : Set G) := by
  have h := congrArg (Subgroup.map (Subgroup.centralizer (W : Set G)).subtype) hcomp.sup_eq_top
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  rwa [inf_of_le_left (sylow_le_centralizer W)] at h

omit [Fintype G] [Fact p.Prime] [IsCyclic (W : Subgroup G)] in
theorem map_complement_normalized (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N)) (h : G)
    (hN : h ∈ Subgroup.normalizer (W : Set G)) (j : G)
    (hj : j ∈ N.map (Subgroup.centralizer (W : Set G)).subtype) :
    h * j * h⁻¹ ∈ N.map (Subgroup.centralizer (W : Set G)).subtype := by
  rw [mem_map_complement_iff W N hcop hpq] at hj ⊢
  refine ⟨(centralizer_conjugation_mem_iff (W : Subgroup G) h j hN).mpr hj.1, ?_⟩
  have hord := (MulAut.conj h).orderOf_eq j
  change orderOf (h * j * h⁻¹) = orderOf j at hord
  rw [hord]
  exact hj.2

omit [Fintype G] [Fact p.Prime] [IsCyclic (W : Subgroup G)] in
theorem map_complement_characteristic (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N)) :
    ((N.map (Subgroup.centralizer (W : Set G)).subtype).subgroupOf
      (Subgroup.centralizer (W : Set G))).Characteristic := by
  have hJ : (N.map (Subgroup.centralizer (W : Set G)).subtype).subgroupOf
      (Subgroup.centralizer (W : Set G)) = N :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) N
  rw [hJ, Subgroup.characteristic_iff_comap_eq]
  intro φ
  ext k
  rw [Subgroup.mem_comap, mem_complement_iff W N hcop hpq, mem_complement_iff W N hcop hpq]
  change Nat.Coprime p (orderOf (φ k)) ↔ _
  rw [MulEquiv.orderOf_eq]

end Complement

omit [Fintype G] in
theorem inverts_of_mem_normalizer (W : Subgroup G) [IsCyclic W] (hp2 : p ≠ 2) (a : ℕ)
    (hWcard : Nat.card W = p ^ a)
    (hindex : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (h : G) (hN : h ∈ Subgroup.normalizer (W : Set G))
    (hC : h ∉ Subgroup.centralizer (W : Set G)) (w : G) (hw : w ∈ W) : h * w * h⁻¹ = w⁻¹ := by
  have hp : p.Prime := Fact.out
  let σ : W →* W :=
    { toFun := fun x => ⟨h * x * h⁻¹, (Subgroup.mem_normalizer_iff.mp hN x).mp x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hσ : ∀ x : W, ((σ x : W) : G) = h * x * h⁻¹ := fun x => rfl
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ
  have hsq : h ^ 2 ∈ Subgroup.centralizer (W : Set G) := by
    have := Subgroup.sq_mem_of_index_two hindex (⟨h, hN⟩ : Subgroup.normalizer (W : Set G))
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have hσσ : ∀ x : W, σ (σ x) = x := by
    intro x
    apply Subtype.ext
    rw [hσ, hσ]
    have hc := Subgroup.mem_centralizer_iff.mp hsq x x.2
    calc h * (h * (x : G) * h⁻¹) * h⁻¹ = h ^ 2 * (x : G) * (h ^ 2)⁻¹ := by
          rw [pow_two, mul_inv_rev]; group
      _ = x := by rw [← hc]; group
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := W)
  have hgord : orderOf g = p ^ a := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hWcard]
  have hgpow : g ^ (m * m - 1) = 1 := by
    have h1 := hσσ g
    rw [hm, hm, ← zpow_mul] at h1
    rw [zpow_sub, h1, zpow_one, mul_inv_cancel]
  have hdvd : ((p : ℤ) ^ a) ∣ (m - 1) * (m + 1) := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr hgpow
    rw [hgord, Nat.cast_pow] at this
    have heq : (m - 1) * (m + 1) = m * m - 1 := by ring
    rwa [heq]
  have hxpow : ∀ x : W, x ^ ((p : ℤ) ^ a) = 1 := by
    intro x
    rw [← Nat.cast_pow, zpow_natCast, ← hWcard]
    exact pow_card_eq_one'
  have hnot : ¬ ((p : ℤ) ∣ m - 1 ∧ (p : ℤ) ∣ m + 1) := by
    rintro ⟨h1, h2⟩
    have h3 : (p : ℤ) ∣ 2 := by
      have := dvd_sub h2 h1
      rwa [show m + 1 - (m - 1) = 2 by ring] at this
    have h4 : p ∣ 2 := by exact_mod_cast h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)
  have hprimeZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hdiv : (p : ℤ) ∣ m - 1
  · exfalso
    have hcop : IsCoprime ((p : ℤ) ^ a) (m + 1) :=
      IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hprimeZ).mpr fun h2 => hnot ⟨hdiv, h2⟩)
    have hm1 : ((p : ℤ) ^ a) ∣ m - 1 := hcop.dvd_of_dvd_mul_right hdvd
    apply hC
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hfix : σ ⟨x, hx⟩ = ⟨x, hx⟩ := by
      rw [hm]
      obtain ⟨k, hk⟩ := hm1
      rw [show m = 1 + (p : ℤ) ^ a * k by rw [← hk]; ring, zpow_add, zpow_one, zpow_mul,
        hxpow, one_zpow, mul_one]
    have hval := congrArg Subtype.val hfix
    rw [hσ] at hval
    calc x * h = h * x * h⁻¹ * h := by rw [hval]
      _ = h * x := by group
  · have hcop : IsCoprime ((p : ℤ) ^ a) (m - 1) :=
      IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hprimeZ).mpr hdiv)
    have hm1 : ((p : ℤ) ^ a) ∣ m + 1 := hcop.dvd_of_dvd_mul_left hdvd
    have hinv : σ ⟨w, hw⟩ = (⟨w, hw⟩ : W)⁻¹ := by
      rw [hm]
      obtain ⟨k, hk⟩ := hm1
      rw [show m = -1 + (p : ℤ) ^ a * k by rw [← hk]; ring, zpow_add, zpow_neg_one, zpow_mul,
        hxpow, one_zpow, mul_one]
    have hval := congrArg Subtype.val hinv
    rw [hσ] at hval
    exact hval

section Linear

omit [Fintype G] [Fact p.Prime] in
theorem finrank_eq_one_of_forall_scalar (data : FiniteComplexRepresentation G)
    (hirr : data.IsIrreducible)
    (hscalar : ∀ g, ∃ c : ℂ, data.representation g = c • (1 : Module.End ℂ data.vector)) :
    Module.finrank ℂ data.vector = 1 := by
  let : data.representation.IsIrreducible := hirr
  let : Nontrivial data.representation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) data.representation.asModule
  let : Nontrivial data.vector := data.representation.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : data.vector)
  let line : Subrepresentation data.representation :=
    { toSubmodule := ℂ ∙ v
      apply_mem_toSubmodule := fun g x hx => by
        obtain ⟨c, hc⟩ := hscalar g
        rw [hc]
        exact Submodule.smul_mem _ c hx }
  have hne : line ≠ ⊥ := by
    intro hbot
    have hmem : v ∈ line.toSubmodule := Submodule.mem_span_singleton_self v
    rw [hbot] at hmem
    exact hv hmem
  have htop : line = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top line).resolve_left hne
  have hspan : (ℂ ∙ v) = ⊤ := congrArg Subrepresentation.toSubmodule htop
  rw [← finrank_top ℂ data.vector, ← hspan, finrank_span_singleton hv]

omit [Fintype G] [Fact p.Prime] in
theorem representation_eq_character_smul_of_finrank_one (data : FiniteComplexRepresentation G)
    (hdim : Module.finrank ℂ data.vector = 1) (g : G) :
    data.representation g = data.character g • (1 : Module.End ℂ data.vector) := by
  obtain ⟨c, hc, -⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (data.representation g)
  have htrace : data.character g = c := by
    change LinearMap.trace ℂ _ (data.representation g) = c
    rw [hc, map_smul, LinearMap.trace_id, hdim, Nat.cast_one, smul_eq_mul, mul_one]
  rw [hc, htrace]
  rfl

end Linear

section Blocks

variable (W : Sylow p G) [IsCyclic (W : Subgroup G)]
  (N : Subgroup (Subgroup.centralizer (W : Set G))) [N.Normal]

noncomputable abbrev sylowInclusion :
    (W : Subgroup G) →* Subgroup.centralizer (W : Set G) :=
  Subgroup.inclusion (sylow_le_centralizer W)

omit [Fintype G] [Fact p.Prime] in
theorem complementProjection_eq_one_iff
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (k : Subgroup.centralizer (W : Set G)) :
    complementProjection W N hcomp k = 1 ↔ k ∈ N := by
  constructor
  · intro h
    change (Subgroup.subgroupOfEquivOfLe (sylow_le_centralizer W))
      (hcomp.QuotientMulEquiv (QuotientGroup.mk' N k)) = 1 at h
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff] at h
    exact (QuotientGroup.eq_one_iff k).mp h
  · exact complementProjection_of_mem_complement W N hcomp k

omit [Fintype G] [Fact p.Prime] in
theorem complementProjection_inclusion
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (w : (W : Subgroup G)) : complementProjection W N hcomp (sylowInclusion W w) = w :=
  Subtype.ext (complementProjection_of_mem W N hcomp _ w.2)

omit [Fintype G] [Fact p.Prime] in
theorem inv_inclusion_projection_mul_mem
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (k : Subgroup.centralizer (W : Set G)) :
    (sylowInclusion W (complementProjection W N hcomp k))⁻¹ * k ∈ N := by
  rw [← complementProjection_eq_one_iff W N hcomp, map_mul, map_inv,
    complementProjection_inclusion, inv_mul_cancel]

omit [Fintype G] [Fact p.Prime] in
theorem sylowInclusion_mem_center (w : (W : Subgroup G)) :
    sylowInclusion W w ∈ Subgroup.center (Subgroup.centralizer (W : Set G)) := by
  rw [Subgroup.mem_center_iff]
  intro k
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp k.2 _ w.2).symm

theorem principal_local_block_iff (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (W : Set G)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N))
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (θ : localBasis.index) :
    θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal ↔
      ∃ μ : (W : Subgroup G) →* ℂˣ, ∀ k, (localBasis.representation θ).character k =
        μ (complementProjection W N hcomp k) := by
  rw [(CFSG.LyonsUnitaryFour.normal_p_complement_principal_block localBasis ideal p localPrincipal
    hlocalPrincipal N hcop hpq).1 θ]
  constructor
  · intro hker
    have hsplit : ∀ k, (localBasis.representation θ).representation k =
        (localBasis.representation θ).representation
          (sylowInclusion W (complementProjection W N hcomp k)) := by
      intro k
      have hn := hker (inv_inclusion_projection_mul_mem W N hcomp k)
      rw [MonoidHom.mem_ker] at hn
      conv_lhs => rw [show k = sylowInclusion W (complementProjection W N hcomp k) *
        ((sylowInclusion W (complementProjection W N hcomp k))⁻¹ * k) by group]
      rw [map_mul, hn, mul_one]
    have hscalar : ∀ k, ∃ c : ℂ, (localBasis.representation θ).representation k =
        c • (1 : Module.End ℂ (localBasis.representation θ).vector) := by
      intro k
      let : (localBasis.representation θ).representation.IsIrreducible := localBasis.irreducible θ
      rw [hsplit k]
      exact irreducible_central_element_is_scalar _ _ (sylowInclusion_mem_center W _)
    have hdim := finrank_eq_one_of_forall_scalar _ (localBasis.irreducible θ) hscalar
    have hdeg : (localBasis.representation θ).character 1 = 1 := by
      rw [FiniteComplexRepresentation.character, Representation.char_one, hdim, Nat.cast_one]
    refine ⟨(degreeOneCharacterUnits (localBasis.representation θ) hdeg).comp (sylowInclusion W),
      fun k => ?_⟩
    rw [MonoidHom.comp_apply, degreeOneCharacterUnits_val]
    change LinearMap.trace ℂ _ ((localBasis.representation θ).representation k) =
      LinearMap.trace ℂ _ ((localBasis.representation θ).representation
        (sylowInclusion W (complementProjection W N hcomp k)))
    rw [hsplit k]
  · rintro ⟨μ, hμ⟩
    have hdeg : (localBasis.representation θ).character 1 = 1 := by
      rw [hμ, map_one, map_one, Units.val_one]
    have hdim : Module.finrank ℂ (localBasis.representation θ).vector = 1 := by
      have h := hdeg
      rw [FiniteComplexRepresentation.character, Representation.char_one] at h
      exact_mod_cast h
    intro n hn
    rw [MonoidHom.mem_ker, representation_eq_character_smul_of_finrank_one _ hdim, hμ,
      complementProjection_of_mem_complement W N hcomp n hn, map_one, Units.val_one, one_smul]

theorem brauer_fiber_principal_iff (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (W : Set G)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (θ : localBasis.index) :
    brauerNormalizerCharacterResidueHom ideal p (W : Subgroup G) W.isPGroup'
        (Subgroup.centralizer (W : Set G)) le_rfl (Subgroup.centralizer_le_normalizer _)
        localBasis θ = centralCharacterResidueHom basis ideal principal ↔
      θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal := by
  have hiff := fun (ambientLabel : basis.index) himage =>
    brauerNormalizer_principal_block_iff basis ideal p (W : Subgroup G) W.isPGroup'
      (Subgroup.centralizer (W : Set G)) (sylow_le_centralizer W) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis principal hprincipal localPrincipal
      hlocalPrincipal θ ambientLabel himage
  constructor
  · intro himage
    have h := (hiff principal himage).mp (sameCoefficientBlock_refl basis _ principal)
    exact (coefficientBlock_mem_iff _ _ _ _).mpr (sameCoefficientBlock_symm _ _ h)
  · intro hθ
    obtain ⟨label, himage⟩ := brauerNormalizer_block_image_exists basis ideal p
      (W : Subgroup G) W.isPGroup' (Subgroup.centralizer (W : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) localBasis θ
    have hsame := (hiff label himage).mpr
      (sameCoefficientBlock_symm _ _ ((coefficientBlock_mem_iff _ _ _ _).mp hθ))
    rw [himage]
    exact (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal label principal).mp
      hsame

end Blocks

section Average

omit [Fintype G] [Fact p.Prime] in
theorem projection_normalSubgroupCharacterSupport {C : Type*} [Group C] [Fintype C]
    (basisC : FiniteIrreducibleCharacterBasis C) (R : Subgroup C) [R.Normal]
    (f : C → ℂ) (hclass : ∀ x c : C, f (c * x * c⁻¹) = f x) (x : C) :
    characterSubsetProjection basisC (normalSubgroupCharacterSupport basisC R) f x =
      (Nat.card R : ℂ)⁻¹ * ∑ r : R, f (x * r) := by
  let cardUnit : ℂˣ := Units.mk0 (Nat.card R) (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [characterSubsetProjection_convolution basisC _ f hclass,
    ← normalSubgroupAverage_eq_characterSubsetIdempotent basisC R cardUnit rfl]
  change ∑ member : C,
    ((↑(cardUnit⁻¹) : ℂ) *
      (∑ element : R, MonoidAlgebra.single element.val 1 : MonoidAlgebra ℂ C).coeff member) *
        f (x * member) = _
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ r : R, (∑ member : C, (↑(cardUnit⁻¹) : ℂ) *
      (MonoidAlgebra.single r.val 1).coeff member * f (x * member)) =
        (↑(cardUnit⁻¹) : ℂ) * f (x * r) := by
    intro r
    simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [Finset.sum_eq_single r.val]
    · simp only [ite_true, mul_one]
    · intro member _ hne
      simp only [ite_eq_right (Ne.symm hne), mul_zero, zero_mul]
    · simp
  simp_rw [hterm]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1

end Average

section Generator

variable (W : Sylow p G) [IsCyclic (W : Subgroup G)]
  (N : Subgroup (Subgroup.centralizer (W : Set G))) [N.Normal]

omit [Fintype G] [Fact p.Prime] [IsCyclic (W : Subgroup G)] [N.Normal] in
theorem centralizer_zpowers_eq {w : G} (hgen : Subgroup.zpowers w = (W : Subgroup G)) :
    Subgroup.centralizer (Subgroup.zpowers w : Set G) = Subgroup.centralizer (W : Set G) := by
  rw [hgen]
  rfl

noncomputable abbrev generatorComplement (w : G) :
    Subgroup (Subgroup.centralizer (Subgroup.zpowers w : Set G)) :=
  (N.map (Subgroup.centralizer (W : Set G)).subtype).subgroupOf
    (Subgroup.centralizer (Subgroup.zpowers w : Set G))

omit [Fintype G] [Fact p.Prime] [IsCyclic (W : Subgroup G)] in
theorem generatorComplement_normal (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N)) {w : G}
    (hgen : Subgroup.zpowers w = (W : Subgroup G)) : (generatorComplement W N w).Normal := by
  constructor
  intro n hn c
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hc : (c : G) ∈ Subgroup.centralizer (W : Set G) := by
    rw [← centralizer_zpowers_eq W hgen]
    exact c.2
  exact map_complement_normalized W N hcop hpq c (Subgroup.centralizer_le_normalizer _ hc) n hn

omit [Fintype G] [Fact p.Prime] [IsCyclic (W : Subgroup G)] [N.Normal] in
theorem card_generatorComplement {w : G} (hgen : Subgroup.zpowers w = (W : Subgroup G)) :
    Nat.card (generatorComplement W N w) = Nat.card N := by
  have hle : N.map (Subgroup.centralizer (W : Set G)).subtype ≤
      Subgroup.centralizer (Subgroup.zpowers w : Set G) := by
    rw [centralizer_zpowers_eq W hgen]
    exact Subgroup.map_subtype_le N
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_map_complement]

omit [IsCyclic (W : Subgroup G)] in
theorem generatorComplement_quotient (a : ℕ) (hWcard : Nat.card W = p ^ a)
    [IsCyclic (W : Subgroup G)] (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N)) {w : G}
    (hgen : Subgroup.zpowers w = (W : Subgroup G)) :
    @IsPGroup p (Subgroup.centralizer (Subgroup.zpowers w : Set G) ⧸ generatorComplement W N w)
      (@QuotientGroup.Quotient.group _ _ _ (generatorComplement_normal W N hcop hpq hgen)) := by
  let := generatorComplement_normal W N hcop hpq hgen
  apply IsPGroup.of_card (n := a)
  have hK := Subgroup.card_eq_card_quotient_mul_card_subgroup (generatorComplement W N w)
  have hCw : Nat.card (Subgroup.centralizer (Subgroup.zpowers w : Set G)) =
      p ^ a * Nat.card N := by
    rw [centralizer_zpowers_eq W hgen, ← card_mul_card_complement W N a hWcard hcop hpq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sylow_le_centralizer W)).toEquiv, hWcard]
  rw [hCw, card_generatorComplement W N hgen] at hK
  exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos hK).symm

end Generator

section Sections

variable (W : Sylow p G) [IsCyclic (W : Subgroup G)]
  (N : Subgroup (Subgroup.centralizer (W : Set G))) [N.Normal]

omit [Fintype G] [Fact p.Prime] [IsCyclic (W : Subgroup G)] [N.Normal] in
theorem orderOf_dvd_of_zpowers_eq (a : ℕ) (hWcard : Nat.card W = p ^ a) {w : G}
    (hgen : Subgroup.zpowers w = (W : Subgroup G)) : orderOf w ∣ p ^ a := by
  rw [← Nat.card_zpowers, hgen, hWcard]

omit [Fact p.Prime] [IsCyclic (W : Subgroup G)] [N.Normal] in
theorem sum_generatorComplement {w : G} (hgen : Subgroup.zpowers w = (W : Subgroup G))
    (f : G → ℂ) :
    ∑ r : generatorComplement W N w,
        f ((r : Subgroup.centralizer (Subgroup.zpowers w : Set G)) : G) =
      ∑ n : N, f ((n : Subgroup.centralizer (W : Set G)) : G) := by
  have hle : N.map (Subgroup.centralizer (W : Set G)).subtype ≤
      Subgroup.centralizer (Subgroup.zpowers w : Set G) := by
    rw [centralizer_zpowers_eq W hgen]
    exact Subgroup.map_subtype_le N
  calc ∑ r : generatorComplement W N w,
        f ((r : Subgroup.centralizer (Subgroup.zpowers w : Set G)) : G) =
      ∑ j : N.map (Subgroup.centralizer (W : Set G)).subtype, f (j : G) :=
        Fintype.sum_equiv (Subgroup.subgroupOfEquivOfLe hle).toEquiv _ _ (fun _ => rfl)
    _ = ∑ n : N, f ((n : Subgroup.centralizer (W : Set G)) : G) :=
        (Fintype.sum_equiv (Subgroup.equivMapOfInjective N _
          (Subgroup.subtype_injective _)).toEquiv _ _ (fun _ => rfl)).symm

theorem generator_section_sum (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (a : ℕ)
    (hWcard : Nat.card W = p ^ a) (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N)) {w : G}
    (hgen : Subgroup.zpowers w = (W : Subgroup G)) (χ : basis.index) :
    ∑ n : N, (basis.representation χ).character
        (w⁻¹ * ((n : Subgroup.centralizer (W : Set G)) : G)) =
      (Nat.card N : ℂ) * characterSubsetProjection basis
        (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
        (basis.representation χ).character w⁻¹ := by
  have hw := orderOf_dvd_of_zpowers_eq W a hWcard hgen
  let := generatorComplement_normal W N hcop hpq hgen
  obtain ⟨localBasis⟩ :=
    finiteIrreducibleCharacterBasis_exists (G := Subgroup.centralizer (Subgroup.zpowers w : Set G))
  obtain ⟨lp, hlp⟩ := finiteIrreducibleCharacterBasis_contains_irreducible localBasis
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hlp
  have h1 := principal_local_section_projection_character basis ideal p principal hprincipal w a
    hw localBasis lp hlp 1 (by rw [Subgroup.coe_one, orderOf_one]; exact Nat.coprime_one_right p) χ
  have hblock := CFSG.LyonsUnitaryFour.principal_block_eq_normalSubgroupCharacterSupport localBasis
    ideal p lp hlp (generatorComplement W N w)
    (by rw [card_generatorComplement W N hgen]; exact hcop)
    (generatorComplement_quotient W N a hWcard hcop hpq hgen)
  rw [QuotientGroup.ker_mk'] at hblock
  rw [hblock, projection_normalSubgroupCharacterSupport localBasis _ _
    (fun x c => Representation.char_conj _ x.val c.val)] at h1
  simp only [mul_one, Subgroup.coe_inv] at h1
  have hsum := sum_generatorComplement W N hgen
    (fun g => (basis.representation χ).character (w⁻¹ * g))
  change (Nat.card (generatorComplement W N w) : ℂ)⁻¹ * ∑ r : generatorComplement W N w,
    (basis.representation χ).character (w⁻¹ * ((r : Subgroup.centralizer
      (Subgroup.zpowers w : Set G)) : G)) = _ at h1
  rw [hsum, card_generatorComplement W N hgen] at h1
  rw [← h1, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]

theorem generator_section_constant (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (a : ℕ)
    (hWcard : Nat.card W = p ^ a) (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N)) {w : G}
    (hgen : Subgroup.zpowers w = (W : Subgroup G)) {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) (v : G)
    (hv : v ∈ N.map (Subgroup.centralizer (W : Set G)).subtype) :
    (basis.representation χ).character (w * v) = (basis.representation χ).character w := by
  have hw := orderOf_dvd_of_zpowers_eq W a hWcard hgen
  let := generatorComplement_normal W N hcop hpq hgen
  have hvC : v ∈ Subgroup.centralizer (Subgroup.zpowers w : Set G) := by
    rw [centralizer_zpowers_eq W hgen]
    exact Subgroup.map_subtype_le N hv
  exact principal_character_section_constant_of_normal_complement basis ideal p principal
    hprincipal hw (generatorComplement W N w)
    (by rw [card_generatorComplement W N hgen]; exact hcop)
    (generatorComplement_quotient W N a hWcard hcop hpq hgen) hχ
    (y := ⟨v, hvC⟩) (by rw [Subgroup.mem_subgroupOf]; exact hv)

omit [Fact p.Prime] [N.Normal] in
theorem sum_centralizer
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (f : Subgroup.centralizer (W : Set G) → ℂ) :
    ∑ k, f k = ∑ w : (W : Subgroup G), ∑ n : N, f (sylowInclusion W w * n) := by
  rw [← Fintype.sum_bijective _ hcomp (fun x => f (x.1.1 * x.2.1)) f (fun _ => rfl),
    Fintype.sum_prod_type]
  exact Fintype.sum_equiv (Subgroup.subgroupOfEquivOfLe (sylow_le_centralizer W)).toEquiv _ _
    (fun _ => rfl)

end Sections

section Coefficients

variable (W : Sylow p G) [IsCyclic (W : Subgroup G)]
  (N : Subgroup (Subgroup.centralizer (W : Set G))) [N.Normal]

omit [N.Normal] in
theorem zpowers_eq_of_ne_one (a : ℕ) (hWcard : Nat.card W = p ^ a)
    (lam : (W : Subgroup G) →* ℂˣ) (hlam : lam ^ p = 1) (w : (W : Subgroup G)) (hw : lam w ≠ 1) :
    Subgroup.zpowers (w : G) = (W : Subgroup G) := by
  have hp : p.Prime := Fact.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (W : Subgroup G))
  have hgord : orderOf g = p ^ a := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hWcard]
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr (hg w))
  have hpk : ¬ p ∣ k := by
    rintro ⟨j, rfl⟩
    apply hw
    rw [← hk, map_pow, pow_mul]
    have hgp : lam g ^ p = 1 := by
      rw [← MonoidHom.pow_apply, hlam, MonoidHom.one_apply]
    rw [hgp, one_pow]
  have hcop : Nat.Coprime (orderOf g) k := by
    rw [hgord]
    exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpk)
  have hword : orderOf (w : G) = p ^ a := by
    rw [Subgroup.orderOf_coe, ← hk, hcop.orderOf_pow, hgord]
  apply Subgroup.eq_of_le_of_card_ge
  · exact (Subgroup.zpowers_le).mpr w.2
  · rw [Nat.card_zpowers, hword, hWcard]

@[expose] noncomputable def inversionColumn
    (π : Subgroup.centralizer (W : Set G) →* (W : Subgroup G))
    (lam : (W : Subgroup G) →* ℂˣ) : G → ℂ :=
  inducedFunction (Subgroup.centralizer (W : Set G)) (fun k => 1 - (lam (π k) : ℂ))

omit [Fact p.Prime] in
theorem inversionColumn_pairing
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (lam : (W : Subgroup G) →* ℂˣ) (χ : G → ℂ) (hχ : ∀ x c : G, χ (c * x * c⁻¹) = χ x) :
    characterPairing (inversionColumn W (complementProjection W N hcomp) lam) χ =
      (Nat.card (Subgroup.centralizer (W : Set G)) : ℂ)⁻¹ * ∑ w : (W : Subgroup G),
        (1 - (lam w : ℂ)) *
          ∑ n : N, χ ((w : G)⁻¹ * ((n : Subgroup.centralizer (W : Set G)) : G)) := by
  rw [inversionColumn, characterPairing_inducedFunction_left _ _ χ hχ]
  unfold characterPairing
  congr 1
  rw [sum_centralizer W N hcomp]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.mul_sum]
  have hterm : ∀ n : N, (1 - (lam (complementProjection W N hcomp (sylowInclusion W w * n)) : ℂ)) *
      χ (((sylowInclusion W w * n)⁻¹ : Subgroup.centralizer (W : Set G)) : G) =
      (1 - (lam w : ℂ)) * χ ((w : G)⁻¹ * ((n⁻¹ : N) : Subgroup.centralizer (W : Set G))) := by
    intro n
    rw [map_mul, complementProjection_inclusion,
      complementProjection_of_mem_complement W N hcomp n n.2, mul_one]
    congr 2
    have hc : (w : G) * ((n : Subgroup.centralizer (W : Set G)) : G) =
        ((n : Subgroup.centralizer (W : Set G)) : G) * w :=
      Subgroup.mem_centralizer_iff.mp (n : Subgroup.centralizer (W : Set G)).2 w w.2
    change ((w : G) * ((n : Subgroup.centralizer (W : Set G)) : G))⁻¹ =
      (w : G)⁻¹ * ((n : Subgroup.centralizer (W : Set G)) : G)⁻¹
    rw [hc, mul_inv_rev]
  rw [Finset.sum_congr rfl fun n _ => hterm n]
  exact Fintype.sum_equiv (Equiv.inv N) _ _ (fun _ => rfl)

omit [IsCyclic (W : Subgroup G)] in
theorem card_centralizer_eq (a : ℕ) (hWcard : Nat.card W = p ^ a) [IsCyclic (W : Subgroup G)]
    (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N)) :
    (Nat.card (Subgroup.centralizer (W : Set G)) : ℂ) = (p : ℂ) ^ a * Nat.card N := by
  rw [← card_mul_card_complement W N a hWcard hcop hpq,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sylow_le_centralizer W)).toEquiv, hWcard]
  push_cast
  rfl

theorem inversionColumn_pairing_projection (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (a : ℕ)
    (hWcard : Nat.card W = p ^ a) (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N))
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (lam : (W : Subgroup G) →* ℂˣ) (hlam : lam ^ p = 1) (χ : basis.index) :
    characterPairing (inversionColumn W (complementProjection W N hcomp) lam)
        (basis.representation χ).character =
      ((p : ℂ) ^ a)⁻¹ * ∑ w : (W : Subgroup G), (1 - (lam w : ℂ)) *
        characterSubsetProjection basis
          (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
          (basis.representation χ).character (w : G)⁻¹ := by
  rw [inversionColumn_pairing W N hcomp lam _ (fun x c => Representation.char_conj _ x c),
    card_centralizer_eq W N a hWcard hcop hpq]
  have hN : (Nat.card N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hterm : ∀ w : (W : Subgroup G), (1 - (lam w : ℂ)) * ∑ n : N,
      (basis.representation χ).character
        ((w : G)⁻¹ * ((n : Subgroup.centralizer (W : Set G)) : G)) =
      (Nat.card N : ℂ) * ((1 - (lam w : ℂ)) * characterSubsetProjection basis
          (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
          (basis.representation χ).character (w : G)⁻¹) := by
    intro w
    by_cases hw : lam w = 1
    · rw [hw, Units.val_one, sub_self, zero_mul, zero_mul, mul_zero]
    · rw [generator_section_sum W N basis ideal principal hprincipal a hWcard hcop hpq
        (zpowers_eq_of_ne_one W a hWcard lam hlam w hw) χ]
      ring
  rw [Finset.sum_congr rfl fun w _ => hterm w, ← Finset.mul_sum, mul_inv, mul_assoc,
    ← mul_assoc (Nat.card N : ℂ)⁻¹, inv_mul_cancel₀ hN, one_mul]

theorem inversionColumn_pairing_mem (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (a : ℕ)
    (hWcard : Nat.card W = p ^ a) (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N))
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (lam : (W : Subgroup G) →* ℂˣ) (hlam : lam ^ p = 1) {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) (v : G)
    (hv : v ∈ N.map (Subgroup.centralizer (W : Set G)).subtype) :
    characterPairing (inversionColumn W (complementProjection W N hcomp) lam)
        (basis.representation χ).character =
      ((p : ℂ) ^ a)⁻¹ * ∑ w : (W : Subgroup G),
        (basis.representation χ).character ((w : G) * v) * (1 - starRingEnd ℂ (lam w : ℂ)) := by
  have hp : p.Prime := Fact.out
  rw [inversionColumn_pairing_projection W N basis ideal principal hprincipal a hWcard hcop hpq
    hcomp lam hlam χ]
  congr 1
  simp_rw [characterSubsetProjection_character basis _ χ hχ]
  rw [← Fintype.sum_equiv (Equiv.inv (W : Subgroup G)) _ _ (fun _ => rfl)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hroot : (lam w : ℂ) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hlam, MonoidHom.one_apply,
      Units.val_one]
  have hconj : starRingEnd ℂ (lam w : ℂ) = (lam w⁻¹ : ℂ) := by
    rw [CFSG.TwoRankLowerBound.Helpers.complex_root_conjugate_inverse hroot hp.ne_zero, map_inv,
      Units.val_inv_eq_inv_val]
  simp only [Equiv.inv_apply, inv_inv, Subgroup.coe_inv]
  rw [hconj]
  by_cases hw : lam w = 1
  · have hw' : lam w⁻¹ = 1 := by rw [map_inv, hw, inv_one]
    rw [hw', Units.val_one, sub_self, mul_zero, zero_mul]
  · have hw' : lam w⁻¹ ≠ 1 := by
      rw [map_inv]
      exact fun h => hw (inv_eq_one.mp h)
    rw [generator_section_constant W N basis ideal principal hprincipal a hWcard hcop hpq
      (zpowers_eq_of_ne_one W a hWcard lam hlam w hw) hχ v hv]
    ring

theorem inversionColumn_pairing_not_mem (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (a : ℕ)
    (hWcard : Nat.card W = p ^ a) (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N))
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (lam : (W : Subgroup G) →* ℂˣ) (hlam : lam ^ p = 1) {χ : basis.index}
    (hχ : χ ∉ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) :
    characterPairing (inversionColumn W (complementProjection W N hcomp) lam)
        (basis.representation χ).character = 0 := by
  rw [inversionColumn_pairing_projection W N basis ideal principal hprincipal a hWcard hcop hpq
    hcomp lam hlam χ]
  simp_rw [characterSubsetProjection_character_not_mem basis _ χ hχ]
  simp

omit [Fact p.Prime] [IsCyclic (W : Subgroup G)] in
theorem sum_linear_character (a : ℕ) (hWcard : Nat.card W = p ^ a)
    (nu : (W : Subgroup G) →* ℂˣ) :
    ∑ w : (W : Subgroup G), (nu w : ℂ) = if nu = 1 then (p : ℂ) ^ a else 0 := by
  split_ifs with h
  · subst h
    simp only [MonoidHom.one_apply, Units.val_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [← Nat.card_eq_fintype_card, hWcard]
    push_cast
    rfl
  · apply sum_hom_units_eq_zero ((Units.coeHom ℂ).comp nu)
    intro h1
    apply h
    ext w
    have := congrArg (fun f => f w) h1
    simpa using this

theorem inversionColumn_pairing_one (a : ℕ) (hWcard : Nat.card W = p ^ a)
    (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N))
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (lam : (W : Subgroup G) →* ℂˣ) (hlam1 : lam ≠ 1) :
    characterPairing (inversionColumn W (complementProjection W N hcomp) lam) 1 = 1 := by
  have hp : p.Prime := Fact.out
  rw [inversionColumn_pairing W N hcomp lam 1 (fun _ _ => rfl),
    card_centralizer_eq W N a hWcard hcop hpq]
  have hinner : ∀ w : (W : Subgroup G), (1 - (lam w : ℂ)) * ∑ n : N,
      (1 : G → ℂ) ((w : G)⁻¹ * ((n : Subgroup.centralizer (W : Set G)) : G)) =
      (Nat.card N : ℂ) * (1 - (lam w : ℂ)) := by
    intro w
    simp only [Pi.one_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
    ring
  rw [Finset.sum_congr rfl fun w _ => hinner w, ← Finset.mul_sum, Finset.sum_sub_distrib,
    sum_linear_character W a hWcard lam, ite_eq_right hlam1]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, sub_zero]
  rw [← Nat.card_eq_fintype_card, hWcard]
  have hN : (Nat.card N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hP : ((p : ℂ) ^ a) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  push_cast
  field_simp

omit [Fact p.Prime] [IsCyclic (W : Subgroup G)] [N.Normal] in
theorem inversionColumn_one (π : Subgroup.centralizer (W : Set G) →* (W : Subgroup G))
    (lam : (W : Subgroup G) →* ℂˣ) : inversionColumn W π lam 1 = 0 := by
  unfold inversionColumn inducedFunction
  rw [Finset.sum_eq_zero, mul_zero]
  intro c _
  split_ifs with h
  · have h1 : (⟨c⁻¹ * 1 * c, h⟩ : Subgroup.centralizer (W : Set G)) = 1 := Subtype.ext (by simp)
    change (1 : ℂ) - (lam (π ⟨c⁻¹ * 1 * c, h⟩) : ℂ) = 0
    rw [h1, map_one, map_one, Units.val_one, sub_self]
  · rfl

end Coefficients

section Integrality

omit [Fact p.Prime] in
theorem character_pairing_nat (basis : FiniteIrreducibleCharacterBasis G)
    (data : FiniteComplexRepresentation G) (θ : basis.index) :
    ∃ m : ℕ, characterPairing data.character (basis.representation θ).character = m := by
  obtain ⟨size, summand, hirr, hsum⟩ :=
    finiteComplexRepresentation_exists_irreducible_character_sum data
  have hfun : data.character = fun g => ∑ k, (1 : ℂ) * (summand k).character g := by
    funext g
    simp only [one_mul]
    exact hsum g
  refine ⟨(Finset.univ.filter fun k => (summand k).character =
    (basis.representation θ).character).card, ?_⟩
  rw [hfun, characterPairing_expansion_left]
  simp only [one_mul]
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [characterPairing_irreducible _ _ (hirr k) (basis.irreducible θ)]
  split_ifs <;> simp

omit [Fact p.Prime] in
theorem inducedFunction_sub (K : Subgroup G) (f g : K → ℂ) :
    inducedFunction K (f - g) = inducedFunction K f - inducedFunction K g := by
  funext x
  unfold inducedFunction
  rw [Pi.sub_apply, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

omit [Fact p.Prime] in
theorem inversionColumn_pairing_int (basis : FiniteIrreducibleCharacterBasis G)
    (W : Sylow p G) (π : Subgroup.centralizer (W : Set G) →* (W : Subgroup G))
    (lam : (W : Subgroup G) →* ℂˣ) (θ : basis.index) :
    ∃ z : ℤ, characterPairing (inversionColumn W π lam) (basis.representation θ).character = z := by
  let K := Subgroup.centralizer (W : Set G)
  let linear : K →* ℂ := (Units.coeHom ℂ).comp (lam.comp π)
  let data₁ := coinducedFiniteComplexRepresentation K (principalFiniteComplexRepresentation K)
  let data₂ := coinducedFiniteComplexRepresentation K
    ({ vector := ℂ, representation := scalarHomRepresentation linear } :
      FiniteComplexRepresentation K)
  have hT : inversionColumn W π lam = data₁.character - data₂.character := by
    funext g
    rw [Pi.sub_apply, coinducedFiniteComplexRepresentation_character,
      coinducedFiniteComplexRepresentation_character,
      principalFiniteComplexRepresentation_character]
    have hlin : ({ vector := ℂ, representation := scalarHomRepresentation linear } :
        FiniteComplexRepresentation K).character = linear :=
      scalarHomRepresentation_character linear
    rw [hlin, ← Pi.sub_apply (inducedFunction K 1) (inducedFunction K linear) g,
      ← inducedFunction_sub]
    rfl
  obtain ⟨m₁, hm₁⟩ := character_pairing_nat basis data₁ θ
  obtain ⟨m₂, hm₂⟩ := character_pairing_nat basis data₂ θ
  refine ⟨(m₁ : ℤ) - m₂, ?_⟩
  rw [hT, characterPairing_sub_left, hm₁, hm₂]
  push_cast
  rfl

end Integrality

section Support

variable (W : Sylow p G) [IsCyclic (W : Subgroup G)]
  (N : Subgroup (Subgroup.centralizer (W : Set G))) [N.Normal]

theorem inversionColumn_support (a : ℕ) (hWcard : Nat.card W = p ^ a)
    (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N))
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (lam : (W : Subgroup G) →* ℂˣ) (hlam : lam ^ p = 1) (g : G)
    (hg : inversionColumn W (complementProjection W N hcomp) lam g ≠ 0) (x y : G)
    (hxy : x * y = g) (hcomm : Commute x y) (hx : ∃ e : ℕ, orderOf x = p ^ e)
    (hy : ¬ p ∣ orderOf y) :
    ∃ w ∈ (W : Subgroup G), Subgroup.zpowers w = (W : Subgroup G) ∧ IsConj x w := by
  have hp : p.Prime := Fact.out
  obtain ⟨c, -, hc⟩ : ∃ c ∈ (Finset.univ : Finset G),
      (if hmem : c⁻¹ * g * c ∈ Subgroup.centralizer (W : Set G) then
        1 - (lam (complementProjection W N hcomp ⟨c⁻¹ * g * c, hmem⟩) : ℂ) else 0) ≠ 0 := by
    by_contra! hall
    apply hg
    unfold inversionColumn inducedFunction
    rw [Finset.sum_eq_zero (fun c _ => hall c (Finset.mem_univ c)), mul_zero]
  by_cases hmem : c⁻¹ * g * c ∈ Subgroup.centralizer (W : Set G)
  swap
  · rw [dite_eq_right hmem] at hc
    exact absurd rfl hc
  rw [dite_eq_left hmem] at hc
  set k : Subgroup.centralizer (W : Set G) := ⟨c⁻¹ * g * c, hmem⟩ with hk
  have hne : lam (complementProjection W N hcomp k) ≠ 1 := by
    intro h1
    apply hc
    rw [h1, Units.val_one, sub_self]
  set w := complementProjection W N hcomp k with hw
  have hgen := zpowers_eq_of_ne_one W a hWcard lam hlam w hne
  set n := (sylowInclusion W w)⁻¹ * k with hn
  have hnN : n ∈ N := inv_inclusion_projection_mul_mem W N hcomp k
  have hkdecomp : c⁻¹ * g * c = (w : G) * ((n : Subgroup.centralizer (W : Set G)) : G) := by
    change ((k : Subgroup.centralizer (W : Set G)) : G) = _
    rw [hn]
    simp
  obtain ⟨e, he⟩ := hx
  have h1 : orderOf (c⁻¹ * x * c) ∣ p ^ e := by
    have := (MulAut.conj c⁻¹).orderOf_eq x
    change orderOf (c⁻¹ * x * c⁻¹⁻¹) = orderOf x at this
    rw [inv_inv] at this
    rw [this, he]
  have h2 : Nat.Coprime p (orderOf (c⁻¹ * y * c)) := by
    have := (MulAut.conj c⁻¹).orderOf_eq y
    change orderOf (c⁻¹ * y * c⁻¹⁻¹) = orderOf y at this
    rw [inv_inv] at this
    rw [this]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hy
  have h3 : Commute (c⁻¹ * x * c) (c⁻¹ * y * c) := by
    have := hcomm.map (MulAut.conj c⁻¹).toMonoidHom
    simpa using this
  have h4 : orderOf (w : G) ∣ p ^ a := by
    rw [Subgroup.orderOf_coe, ← hWcard]
    exact orderOf_dvd_natCard w
  have h5 : Nat.Coprime p (orderOf ((n : Subgroup.centralizer (W : Set G)) : G)) := by
    rw [Subgroup.orderOf_coe]
    exact (mem_complement_iff W N hcop hpq n).mp hnN
  have h6 : Commute (w : G) ((n : Subgroup.centralizer (W : Set G)) : G) :=
    Subgroup.mem_centralizer_iff.mp (n : Subgroup.centralizer (W : Set G)).2 w w.2
  have hprod : (c⁻¹ * x * c) * (c⁻¹ * y * c) =
      (w : G) * ((n : Subgroup.centralizer (W : Set G)) : G) := by
    rw [← hkdecomp, ← hxy]
    group
  obtain ⟨hxw, -⟩ := CFSG.LyonsUnitaryFour.primary_factorization_unique h1 h2 h3 h4 h5 h6 hprod
  refine ⟨w, w.2, hgen, ?_⟩
  rw [isConj_iff]
  exact ⟨c⁻¹, by rw [inv_inv]; exact hxw⟩

end Support

section Mackey

omit [Fintype G] [Fact p.Prime] in
theorem sylow_mul_comm (W : Sylow p G) [IsCyclic (W : Subgroup G)] (x y : (W : Subgroup G)) :
    x * y = y * x :=
  Subtype.ext (Subgroup.mem_centralizer_iff.mp (sylow_le_centralizer W y.2) x x.2)

omit [Fintype G] [Fact p.Prime] in
theorem mem_normalizer_of_conj_generator (W : Subgroup G) {w w' c : G}
    (hw : Subgroup.zpowers w = W) (hw' : Subgroup.zpowers w' = W) (hconj : c⁻¹ * w * c = w') :
    c ∈ Subgroup.normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hcw : c * w' * c⁻¹ = w := by rw [← hconj]; group
  constructor
  · intro hh
    rw [← hw'] at hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← conj_zpow, hcw, ← hw]
    exact Subgroup.zpow_mem_zpowers w j
  · intro hh
    rw [← hw] at hh
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hh' : h = c⁻¹ * w ^ j * c := by rw [hj]; group
    rw [hh', show c⁻¹ * w ^ j * c = c⁻¹ * w ^ j * c⁻¹⁻¹ by rw [inv_inv], ← conj_zpow, inv_inv,
      hconj, ← hw']
    exact Subgroup.zpow_mem_zpowers w' j

omit [Fintype G] [Fact p.Prime] in
theorem card_normalizer_eq (W : Subgroup G)
    (hindex : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2) :
    Nat.card (Subgroup.normalizer (W : Set G)) =
      2 * Nat.card (Subgroup.centralizer (W : Set G)) := by
  have h := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (W : Set G))
    (K := Subgroup.normalizer (W : Set G))
  rw [hindex, inf_of_le_left (Subgroup.centralizer_le_normalizer (W : Set G))] at h
  exact h.symm

omit [Fact p.Prime] in
theorem card_normalizer_sdiff (W : Subgroup G)
    (hindex : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2) :
    (Finset.univ.filter (fun c : G => c ∈ Subgroup.normalizer (W : Set G) ∧
      c ∉ Subgroup.centralizer (W : Set G))).card =
      Nat.card (Subgroup.centralizer (W : Set G)) := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun c : G => c ∈ Subgroup.normalizer (W : Set G)))
    (fun c => c ∈ Subgroup.centralizer (W : Set G))
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have hK : (Finset.univ.filter (fun c : G => c ∈ Subgroup.normalizer (W : Set G) ∧
      c ∈ Subgroup.centralizer (W : Set G))).card =
      Nat.card (Subgroup.centralizer (W : Set G)) := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight fun c =>
      ⟨fun h => h.2, fun h => ⟨Subgroup.centralizer_le_normalizer (W : Set G) h, h⟩⟩
  have hH : (Finset.univ.filter (fun c : G => c ∈ Subgroup.normalizer (W : Set G))).card =
      Nat.card (Subgroup.normalizer (W : Set G)) := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  rw [hK, hH, card_normalizer_eq W hindex] at hsplit
  omega

theorem inversionColumn_apply_generator (W : Sylow p G) [IsCyclic (W : Subgroup G)]
    (N : Subgroup (Subgroup.centralizer (W : Set G))) [N.Normal] (hp2 : p ≠ 2) (a : ℕ)
    (hWcard : Nat.card W = p ^ a)
    (hindex : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N))
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (mu : (W : Subgroup G) →* ℂˣ) (hmu : mu ^ p = 1) (k : Subgroup.centralizer (W : Set G))
    (hk : Subgroup.zpowers ((complementProjection W N hcomp k : (W : Subgroup G)) : G) =
      (W : Subgroup G)) :
    inversionColumn W (complementProjection W N hcomp) mu (k : G) =
      (1 - (mu (complementProjection W N hcomp k) : ℂ)) +
        (1 - (mu (complementProjection W N hcomp k)⁻¹ : ℂ)) := by
  have hp : p.Prime := Fact.out
  set π := complementProjection W N hcomp with hπ
  set w := π k with hw
  set n₀ : Subgroup.centralizer (W : Set G) := (sylowInclusion W w)⁻¹ * k with hn₀
  have hn₀N : n₀ ∈ N := inv_inclusion_projection_mul_mem W N hcomp k
  have hn₀J : (n₀ : G) ∈ N.map (Subgroup.centralizer (W : Set G)).subtype := ⟨n₀, hn₀N, rfl⟩
  have hkG : (k : G) = (w : G) * (n₀ : G) := by
    rw [hn₀]
    simp
  have hwn : Commute (w : G) (n₀ : G) :=
    Subgroup.mem_centralizer_iff.mp n₀.2 w w.2
  have hvalue : ∀ c : G, (if hmem : c⁻¹ * (k : G) * c ∈ Subgroup.centralizer (W : Set G) then
      1 - (mu (π ⟨c⁻¹ * k * c, hmem⟩) : ℂ) else 0) =
      (if c ∈ Subgroup.centralizer (W : Set G) then 1 - (mu w : ℂ) else 0) +
        (if c ∈ Subgroup.normalizer (W : Set G) ∧ c ∉ Subgroup.centralizer (W : Set G) then
          1 - (mu w⁻¹ : ℂ) else 0) := by
    intro c
    by_cases hcK : c ∈ Subgroup.centralizer (W : Set G)
    · have hmem : c⁻¹ * (k : G) * c ∈ Subgroup.centralizer (W : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hcK) k.2) hcK
      rw [dite_eq_left hmem, ite_eq_left hcK, ite_eq_right (fun h => h.2 hcK), add_zero]
      have hkk : (⟨c⁻¹ * k * c, hmem⟩ : Subgroup.centralizer (W : Set G)) =
          (⟨c, hcK⟩ : Subgroup.centralizer (W : Set G))⁻¹ * k * ⟨c, hcK⟩ := rfl
      have hπc : π ((⟨c, hcK⟩ : Subgroup.centralizer (W : Set G))⁻¹ * k * ⟨c, hcK⟩) = π k := by
        rw [map_mul, map_mul, map_inv, sylow_mul_comm W _ (π ⟨c, hcK⟩), ← mul_assoc,
          mul_inv_cancel, one_mul]
      rw [hkk, hπc]
    · by_cases hcH : c ∈ Subgroup.normalizer (W : Set G)
      · have hcinvH : c⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hcH
        have hcinvK : c⁻¹ ∉ Subgroup.centralizer (W : Set G) := fun h => hcK (by
          simpa using Subgroup.inv_mem _ h)
        have hmem : c⁻¹ * (k : G) * c ∈ Subgroup.centralizer (W : Set G) := by
          have := (centralizer_conjugation_mem_iff (W : Subgroup G) c⁻¹ k hcinvH).mpr k.2
          simpa using this
        rw [dite_eq_left hmem, ite_eq_right hcK, ite_eq_left ⟨hcH, hcK⟩, zero_add]
        have hinv : c⁻¹ * (w : G) * c = (w : G)⁻¹ := by
          have := inverts_of_mem_normalizer (W : Subgroup G) hp2 a hWcard hindex c⁻¹ hcinvH
            hcinvK w w.2
          simpa using this
        have hn₁J : c⁻¹ * (n₀ : G) * c ∈ N.map (Subgroup.centralizer (W : Set G)).subtype := by
          have := map_complement_normalized W N hcop hpq c⁻¹ hcinvH n₀ hn₀J
          simpa using this
        obtain ⟨n₁, hn₁N, hn₁⟩ := hn₁J
        have hkk : (⟨c⁻¹ * k * c, hmem⟩ : Subgroup.centralizer (W : Set G)) =
            sylowInclusion W w⁻¹ * n₁ := by
          apply Subtype.ext
          change c⁻¹ * (k : G) * c = (w : G)⁻¹ * (n₁ : G)
          rw [show (n₁ : G) = c⁻¹ * (n₀ : G) * c from hn₁, hkG, ← hinv]
          group
        rw [hkk, map_mul, complementProjection_inclusion,
          complementProjection_of_mem_complement W N hcomp n₁ hn₁N, mul_one]
      · rw [ite_eq_right hcK, ite_eq_right (fun h => hcH h.1), add_zero]
        by_cases hmem : c⁻¹ * (k : G) * c ∈ Subgroup.centralizer (W : Set G)
        · rw [dite_eq_left hmem]
          by_contra hne
          have hne' : mu (π ⟨c⁻¹ * k * c, hmem⟩) ≠ 1 := fun h =>
            hne (by rw [h, Units.val_one, sub_self])
          set w' := π ⟨c⁻¹ * k * c, hmem⟩ with hw'
          have hgen' := zpowers_eq_of_ne_one W a hWcard mu hmu w' hne'
          set n' : Subgroup.centralizer (W : Set G) :=
            (sylowInclusion W w')⁻¹ * ⟨c⁻¹ * k * c, hmem⟩ with hn'
          have hn'N : n' ∈ N := inv_inclusion_projection_mul_mem W N hcomp _
          have h1 : orderOf (c⁻¹ * (w : G) * c) ∣ p ^ a := by
            have := (MulAut.conj c⁻¹).orderOf_eq (w : G)
            change orderOf (c⁻¹ * (w : G) * c⁻¹⁻¹) = orderOf (w : G) at this
            rw [inv_inv] at this
            rw [this, Subgroup.orderOf_coe, ← hWcard]
            exact orderOf_dvd_natCard w
          have h2 : Nat.Coprime p (orderOf (c⁻¹ * (n₀ : G) * c)) := by
            have := (MulAut.conj c⁻¹).orderOf_eq (n₀ : G)
            change orderOf (c⁻¹ * (n₀ : G) * c⁻¹⁻¹) = orderOf (n₀ : G) at this
            rw [inv_inv] at this
            rw [this, Subgroup.orderOf_coe]
            exact (mem_complement_iff W N hcop hpq n₀).mp hn₀N
          have h3 : Commute (c⁻¹ * (w : G) * c) (c⁻¹ * (n₀ : G) * c) := by
            have := hwn.map (MulAut.conj c⁻¹).toMonoidHom
            simpa using this
          have h4 : orderOf (w' : G) ∣ p ^ a := by
            rw [Subgroup.orderOf_coe, ← hWcard]
            exact orderOf_dvd_natCard w'
          have h5 : Nat.Coprime p (orderOf ((n' : Subgroup.centralizer (W : Set G)) : G)) := by
            rw [Subgroup.orderOf_coe]
            exact (mem_complement_iff W N hcop hpq n').mp hn'N
          have h6 : Commute (w' : G) ((n' : Subgroup.centralizer (W : Set G)) : G) :=
            Subgroup.mem_centralizer_iff.mp n'.2 w' w'.2
          have hprod : (c⁻¹ * (w : G) * c) * (c⁻¹ * (n₀ : G) * c) =
              (w' : G) * ((n' : Subgroup.centralizer (W : Set G)) : G) := by
            have hrhs : (w' : G) * ((n' : Subgroup.centralizer (W : Set G)) : G) =
                c⁻¹ * (k : G) * c := by
              rw [hn']
              simp
            rw [hrhs, hkG]
            group
          obtain ⟨hpart, -⟩ :=
            CFSG.LyonsUnitaryFour.primary_factorization_unique h1 h2 h3 h4 h5 h6 hprod
          exact hcH (mem_normalizer_of_conj_generator (W : Subgroup G) hk hgen' hpart)
        · rw [dite_eq_right hmem]
  unfold inversionColumn inducedFunction
  rw [Finset.sum_congr rfl fun c _ => hvalue c, Finset.sum_add_distrib]
  have hs1 : ∑ c : G, (if c ∈ Subgroup.centralizer (W : Set G) then 1 - (mu w : ℂ) else 0) =
      (Nat.card (Subgroup.centralizer (W : Set G)) : ℂ) * (1 - (mu w : ℂ)) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have hs2 : ∑ c : G, (if c ∈ Subgroup.normalizer (W : Set G) ∧
      c ∉ Subgroup.centralizer (W : Set G) then 1 - (mu w⁻¹ : ℂ) else 0) =
      (Nat.card (Subgroup.centralizer (W : Set G)) : ℂ) * (1 - (mu w⁻¹ : ℂ)) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcard := card_normalizer_sdiff (W : Subgroup G) hindex
    exact_mod_cast (by convert hcard using 2 :
      (Finset.univ.filter (fun c : G => c ∈ Subgroup.normalizer (W : Set G) ∧
        c ∉ Subgroup.centralizer (W : Set G))).card = Nat.card (Subgroup.centralizer (W : Set G)))
  rw [hs1, hs2, ← mul_add, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]

theorem inversionColumn_gram (W : Sylow p G) [IsCyclic (W : Subgroup G)]
    (N : Subgroup (Subgroup.centralizer (W : Set G))) [N.Normal] (hp2 : p ≠ 2) (a : ℕ)
    (hWcard : Nat.card W = p ^ a)
    (hindex : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N))
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (lam mu : (W : Subgroup G) →* ℂˣ) (hlam : lam ^ p = 1) (hmu : mu ^ p = 1)
    (hlam1 : lam ≠ 1) (hmu1 : mu ≠ 1) :
    characterPairing (inversionColumn W (complementProjection W N hcomp) lam)
        (inversionColumn W (complementProjection W N hcomp) mu) =
      2 + (if lam = mu then 1 else 0) + (if lam * mu = 1 then 1 else 0) := by
  have hp : p.Prime := Fact.out
  set π := complementProjection W N hcomp with hπ
  have hclass : ∀ x c : G, inversionColumn W π mu (c * x * c⁻¹) = inversionColumn W π mu x :=
    fun x c => inducedFunction_conjugate _ _ x c
  rw [inversionColumn, characterPairing_inducedFunction_left _ _ _ hclass]
  unfold characterPairing
  rw [sum_centralizer W N hcomp, card_centralizer_eq W N a hWcard hcop hpq]
  have hterm : ∀ w : (W : Subgroup G), ∑ n : N, (1 - (lam (π (sylowInclusion W w * n)) : ℂ)) *
      inversionColumn W π mu (((sylowInclusion W w * n)⁻¹ : Subgroup.centralizer (W : Set G)) : G) =
      (Nat.card N : ℂ) * ((1 - (lam w : ℂ)) * (2 - (mu w⁻¹ : ℂ) - (mu w : ℂ))) := by
    intro w
    have hπwn : ∀ n : N, π (sylowInclusion W w * n) = w := fun n => by
      rw [map_mul, complementProjection_inclusion,
        complementProjection_of_mem_complement W N hcomp n n.2, mul_one]
    have hn : ∀ n : N, (1 - (lam (π (sylowInclusion W w * n)) : ℂ)) *
        inversionColumn W π mu
          (((sylowInclusion W w * n)⁻¹ : Subgroup.centralizer (W : Set G)) : G) =
        (1 - (lam w : ℂ)) * (2 - (mu w⁻¹ : ℂ) - (mu w : ℂ)) := by
      intro n
      rw [hπwn n]
      by_cases hw : lam w = 1
      · rw [hw, Units.val_one, sub_self, zero_mul, zero_mul]
      · have hgen := zpowers_eq_of_ne_one W a hWcard lam hlam w hw
        have hπinv : π ((sylowInclusion W w * n)⁻¹) = w⁻¹ := by rw [map_inv, hπwn n]
        have hgen' : Subgroup.zpowers ((π ((sylowInclusion W w * n)⁻¹) : (W : Subgroup G)) : G) =
            (W : Subgroup G) := by
          rw [hπinv, Subgroup.coe_inv, Subgroup.zpowers_inv, hgen]
        rw [inversionColumn_apply_generator W N hp2 a hWcard hindex hcop hpq hcomp mu hmu _
          hgen', hπinv, inv_inv]
        ring
    rw [Finset.sum_congr rfl fun n _ => hn n, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card]
  rw [Finset.sum_congr rfl fun w _ => hterm w, ← Finset.mul_sum]
  have hexpand : ∀ w : (W : Subgroup G), (1 - (lam w : ℂ)) * (2 - (mu w⁻¹ : ℂ) - (mu w : ℂ)) =
      2 * ((1 : (W : Subgroup G) →* ℂˣ) w : ℂ) - ((mu⁻¹ : (W : Subgroup G) →* ℂˣ) w : ℂ) -
        (mu w : ℂ) - 2 * (lam w : ℂ) + ((lam * mu⁻¹ : (W : Subgroup G) →* ℂˣ) w : ℂ) +
          ((lam * mu : (W : Subgroup G) →* ℂˣ) w : ℂ) := by
    intro w
    simp only [MonoidHom.one_apply, Units.val_one, MonoidHom.mul_apply, MonoidHom.inv_apply,
      Units.val_mul, map_inv, Units.val_inv_eq_inv_val]
    ring
  rw [Finset.sum_congr rfl fun w _ => hexpand w]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_linear_character W a hWcard 1, sum_linear_character W a hWcard mu⁻¹,
    sum_linear_character W a hWcard mu, sum_linear_character W a hWcard lam,
    sum_linear_character W a hWcard (lam * mu⁻¹), sum_linear_character W a hWcard (lam * mu)]
  have hmuinv : mu⁻¹ ≠ 1 := by
    intro h
    apply hmu1
    ext w
    have := congrArg (fun f : (W : Subgroup G) →* ℂˣ => (f w : ℂ)) h
    simpa using this
  have hcond : lam * mu⁻¹ = 1 ↔ lam = mu := by
    constructor
    · intro h
      ext w
      have := congrArg (fun f : (W : Subgroup G) →* ℂˣ => (f w : ℂ)) h
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
        Units.val_inv_eq_inv_val, MonoidHom.one_apply, Units.val_one] at this
      exact (mul_inv_eq_one₀ (Units.ne_zero _)).mp this
    · rintro rfl
      ext w
      simp
  rw [ite_eq_left rfl, ite_eq_right hmuinv, ite_eq_right hmu1, ite_eq_right hlam1]
  have hN : (Nat.card N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hP : ((p : ℂ) ^ a) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  by_cases h1 : lam = mu
  · rw [ite_eq_left (hcond.mpr h1), ite_eq_left h1]
    split_ifs <;> field_simp <;> ring
  · rw [ite_eq_right (mt hcond.mp h1), ite_eq_right h1]
    split_ifs <;> field_simp <;> ring

end Mackey

section Reality

omit [Fact p.Prime] in
theorem exists_conj_label (basis : FiniteIrreducibleCharacterBasis G) (θ : basis.index) :
    ∃ θ' : basis.index, ∀ g, (basis.representation θ').character g =
      starRingEnd ℂ ((basis.representation θ).character g) := by
  let data : FiniteComplexRepresentation G :=
    { vector := Module.Dual ℂ (basis.representation θ).vector
      representation := (basis.representation θ).representation.dual }
  have hchar : ∀ g, data.character g = (basis.representation θ).character g⁻¹ :=
    fun g => Representation.char_dual _ g
  have hnorm : characterPairing data.character data.character = 1 := by
    have h := characterPairing_irreducible (basis.representation θ) (basis.representation θ)
      (basis.irreducible θ) (basis.irreducible θ)
    rw [ite_eq_left rfl] at h
    rw [← h]
    unfold characterPairing
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hchar, hchar, inv_inv, mul_comm]
  obtain ⟨θ', hθ'⟩ := character_norm_one_basis_character basis data hnorm
  refine ⟨θ', fun g => ?_⟩
  rw [hθ', hchar, finite_character_conjugate_inverse]

variable (W : Sylow p G) [IsCyclic (W : Subgroup G)]
  (N : Subgroup (Subgroup.centralizer (W : Set G))) [N.Normal]

omit [Fintype G] [Fact p.Prime] [IsCyclic (W : Subgroup G)] [N.Normal] in
theorem exists_mem_normalizer_not_mem_centralizer
    (hindex : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2) :
    ∃ x ∈ Subgroup.normalizer (W : Set G), x ∉ Subgroup.centralizer (W : Set G) := by
  by_contra! h
  have hle : Subgroup.normalizer (W : Set G) ≤ Subgroup.centralizer (W : Set G) := h
  rw [Subgroup.relIndex_eq_one.mpr hle] at hindex
  exact absurd hindex (by decide)

theorem inversionColumn_pairing_conj (basis : FiniteIrreducibleCharacterBasis G) (hp2 : p ≠ 2)
    (a : ℕ) (hWcard : Nat.card W = p ^ a)
    (hindex : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N))
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (lam : (W : Subgroup G) →* ℂˣ) (θ θ' : basis.index)
    (hθ' : ∀ g, (basis.representation θ').character g =
      starRingEnd ℂ ((basis.representation θ).character g)) :
    characterPairing (inversionColumn W (complementProjection W N hcomp) lam)
        (basis.representation θ').character =
      characterPairing (inversionColumn W (complementProjection W N hcomp) lam)
        (basis.representation θ).character := by
  obtain ⟨x, hxH, hxK⟩ := exists_mem_normalizer_not_mem_centralizer W hindex
  rw [inversionColumn_pairing W N hcomp lam _ (fun g c => Representation.char_conj _ g c),
    inversionColumn_pairing W N hcomp lam _ (fun g c => Representation.char_conj _ g c)]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  have hconjN : ∀ n : N, x * ((n : Subgroup.centralizer (W : Set G)) : G) * x⁻¹ ∈
      N.map (Subgroup.centralizer (W : Set G)).subtype := fun n =>
    map_complement_normalized W N hcop hpq x hxH _ ⟨n, n.2, rfl⟩
  have hconjN' : ∀ n : N, x⁻¹ * ((n : Subgroup.centralizer (W : Set G)) : G) * x⁻¹⁻¹ ∈
      N.map (Subgroup.centralizer (W : Set G)).subtype := fun n =>
    map_complement_normalized W N hcop hpq x⁻¹ (Subgroup.inv_mem _ hxH) _ ⟨n, n.2, rfl⟩
  let toN : ∀ g : G, g ∈ N.map (Subgroup.centralizer (W : Set G)).subtype → N := fun g hg =>
    ⟨⟨g, ((mem_map_complement_iff W N hcop hpq g).mp hg).1⟩, by
      obtain ⟨n, hn, rfl⟩ := hg
      exact hn⟩
  let conjN : N ≃ N :=
    { toFun := fun n => toN _ (hconjN n)
      invFun := fun n => toN _ (hconjN' n)
      left_inv := fun n => by
        apply Subtype.ext
        apply Subtype.ext
        change x⁻¹ * (x * ((n : Subgroup.centralizer (W : Set G)) : G) * x⁻¹) * x⁻¹⁻¹ = _
        group
      right_inv := fun n => by
        apply Subtype.ext
        apply Subtype.ext
        change x * (x⁻¹ * ((n : Subgroup.centralizer (W : Set G)) : G) * x⁻¹⁻¹) * x⁻¹ = _
        group }
  have hinvw : x * (w : G) * x⁻¹ = (w : G)⁻¹ :=
    inverts_of_mem_normalizer (W : Subgroup G) hp2 a hWcard hindex x hxH hxK w w.2
  have hstep1 : ∀ n : N, (basis.representation θ').character
      ((w : G)⁻¹ * ((n : Subgroup.centralizer (W : Set G)) : G)) =
      (basis.representation θ).character
        ((w : G) * ((n⁻¹ : N) : Subgroup.centralizer (W : Set G))) := by
    intro n
    rw [hθ', finite_character_conjugate_inverse]
    have hc : (w : G) * ((n : Subgroup.centralizer (W : Set G)) : G) =
        ((n : Subgroup.centralizer (W : Set G)) : G) * w :=
      Subgroup.mem_centralizer_iff.mp (n : Subgroup.centralizer (W : Set G)).2 w w.2
    congr 1
    change ((w : G)⁻¹ * ((n : Subgroup.centralizer (W : Set G)) : G))⁻¹ =
      (w : G) * ((n : Subgroup.centralizer (W : Set G)) : G)⁻¹
    rw [mul_inv_rev, inv_inv]
    have hc' : ((n : Subgroup.centralizer (W : Set G)) : G)⁻¹ * w =
        w * ((n : Subgroup.centralizer (W : Set G)) : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hc, mul_inv_cancel_right]
    exact hc'
  have hstep2 : ∀ n : N, (basis.representation θ).character
      ((w : G) * ((n : Subgroup.centralizer (W : Set G)) : G)) =
      (basis.representation θ).character
        ((w : G)⁻¹ * ((conjN n : Subgroup.centralizer (W : Set G)) : G)) := by
    intro n
    have h := Representation.char_conj (basis.representation θ).representation
      ((w : G) * ((n : Subgroup.centralizer (W : Set G)) : G)) x
    change (basis.representation θ).representation.character _ =
      (basis.representation θ).representation.character _
    rw [← h]
    congr 1
    change x * ((w : G) * ((n : Subgroup.centralizer (W : Set G)) : G)) * x⁻¹ =
      (w : G)⁻¹ * (x * ((n : Subgroup.centralizer (W : Set G)) : G) * x⁻¹)
    rw [← hinvw]
    group
  rw [Finset.sum_congr rfl fun n _ => hstep1 n,
    Fintype.sum_equiv (Equiv.inv N) (fun n => (basis.representation θ).character
      ((w : G) * ((n⁻¹ : N) : Subgroup.centralizer (W : Set G))))
      (fun n => (basis.representation θ).character
        ((w : G) * ((n : Subgroup.centralizer (W : Set G)) : G))) (fun n => by simp),
    Finset.sum_congr rfl fun n _ => hstep2 n]
  exact Fintype.sum_equiv conjN _ _ (fun _ => rfl)

end Reality

section Decomposition

omit [Fact p.Prime] in
theorem norm_three_pair_decomposition (basis : FiniteIrreducibleCharacterBasis G)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (B : Finset basis.index) (T : Fin 2 → G → ℂ)
    (hclass : ∀ i, ∀ x c : G, T i (c * x * c⁻¹) = T i x) (c : Fin 2 → basis.index → ℤ)
    (hc : ∀ i θ, characterPairing (T i) (basis.representation θ).character = c i θ)
    (hone : ∀ i, c i principal = 1) (hnorm : ∀ i, ∑ θ, c i θ ^ 2 = 3)
    (hgram : ∑ θ, c 0 θ * c 1 θ = 2) (hdeg : ∀ i, T i 1 = 0)
    (hB : ∀ i θ, c i θ ≠ 0 → θ ∈ B)
    (hconj : ∀ i θ θ', (∀ g, (basis.representation θ').character g =
      starRingEnd ℂ ((basis.representation θ).character g)) → c i θ' = c i θ)
    (hreg : ∀ i (g : G), ¬ p ∣ orderOf g → T i g = 0) :
    ∃ (ρ τ₁ τ₂ : basis.index) (δ : ℤ), (δ = 1 ∨ δ = -1) ∧
      ρ ∈ B ∧ τ₁ ∈ B ∧ τ₂ ∈ B ∧
      ρ ≠ principal ∧ τ₁ ≠ principal ∧ τ₂ ≠ principal ∧ ρ ≠ τ₁ ∧ ρ ≠ τ₂ ∧ τ₁ ≠ τ₂ ∧
      (∀ g, starRingEnd ℂ ((basis.representation ρ).character g) =
        (basis.representation ρ).character g) ∧
      (∀ g, starRingEnd ℂ ((basis.representation τ₁).character g) =
        (basis.representation τ₁).character g) ∧
      (∀ g, starRingEnd ℂ ((basis.representation τ₂).character g) =
        (basis.representation τ₂).character g) ∧
      (∀ g, T 0 g = 1 + δ * (basis.representation ρ).character g -
        δ * (basis.representation τ₁).character g) ∧
      (∀ g, T 1 g = 1 + δ * (basis.representation ρ).character g -
        δ * (basis.representation τ₂).character g) ∧
      (Module.finrank ℂ (basis.representation τ₁).vector : ℤ) =
        Module.finrank ℂ (basis.representation ρ).vector + δ ∧
      (Module.finrank ℂ (basis.representation τ₂).vector : ℤ) =
        Module.finrank ℂ (basis.representation ρ).vector + δ ∧
      0 < (Module.finrank ℂ (basis.representation ρ).vector : ℤ) + δ ∧
      ∀ g : G, ¬ p ∣ orderOf g →
        (basis.representation τ₁).character g = (basis.representation ρ).character g + δ ∧
        (basis.representation τ₂).character g = (basis.representation ρ).character g + δ := by
  have hexp : ∀ i g, T i g = ∑ θ, (c i θ : ℂ) * (basis.representation θ).character g := by
    intro i g
    rw [finiteIrreducibleCharacterBasis_reconstruction basis (T i) (hclass i) g]
    exact Finset.sum_congr rfl fun θ _ => by rw [hc i θ]
  let d : basis.index → ℤ := fun θ => Module.finrank ℂ (basis.representation θ).vector
  have hdpos : ∀ θ, 0 < d θ := fun θ => by
    have h := irreducible_character_degree_ne_zero _ (basis.irreducible θ)
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    have : Module.finrank ℂ (basis.representation θ).vector ≠ 0 := by exact_mod_cast h
    simp only [d]
    omega
  have hdo : d principal = 1 := by
    have h := congrFun hprincipal 1
    rw [FiniteComplexRepresentation.character, Representation.char_one, Pi.one_apply] at h
    simp only [d]
    exact_mod_cast h
  have hdeg' : ∀ i, ∑ θ, d θ * c i θ = 0 := by
    intro i
    have h := hexp i 1
    rw [hdeg i] at h
    have h' : ((∑ θ, d θ * c i θ : ℤ) : ℂ) = 0 := by
      push_cast
      rw [h]
      refine Finset.sum_congr rfl fun θ _ => ?_
      simp only [d, FiniteComplexRepresentation.character, Representation.char_one]
      push_cast
      ring
    exact_mod_cast h'
  obtain ⟨ρ, hρo, b, hbinj, hbne, δ, hδ, hv⟩ :=
    CFSG.Semidihedral.Principal.integral_norm_three_degree_zero_gram_family_common_coordinate
      (I := Fin 2) (by simp) principal d hdpos hdo c hone hnorm hdeg' (by
        intro i j hij
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · exact hgram
        · rw [← hgram]
          exact Finset.sum_congr rfl fun θ _ => mul_comm _ _
        · exact absurd rfl hij)
  have hval : ∀ i θ, c i θ = (if θ = principal then 1 else 0) + δ * (if θ = ρ then 1 else 0) -
      δ * (if θ = b i then 1 else 0) := by
    intro i θ
    rw [(hv i).1]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  have hcρ : ∀ i, c i ρ = δ := by
    intro i
    rw [hval, ite_eq_right hρo, ite_eq_left rfl, ite_eq_right (fun h => (hbne i).2 h.symm)]
    ring
  have hcb : ∀ i, c i (b i) = -δ := by
    intro i
    rw [hval, ite_eq_right (hbne i).1, ite_eq_right (hbne i).2, ite_eq_left rfl]
    ring
  have hδne : δ ≠ 0 := by rcases hδ with h | h <;> omega
  have hsupp : ∀ i x, c i x ≠ 0 ↔ x = principal ∨ x = ρ ∨ x = b i := fun i => (hv i).2.2.2
  have hconj_ne_principal : ∀ θ θ', (∀ g, (basis.representation θ').character g =
      starRingEnd ℂ ((basis.representation θ).character g)) → θ ≠ principal →
      θ' ≠ principal := by
    intro θ θ' hθ' hθ heq
    apply hθ
    apply basis.distinct
    change (basis.representation θ).character = (basis.representation principal).character
    funext g
    have h := hθ' g
    rw [heq, hprincipal, Pi.one_apply] at h
    rw [hprincipal, Pi.one_apply]
    have h2 := congrArg (starRingEnd ℂ) h
    rw [map_one, Complex.conj_conj] at h2
    exact h2.symm
  have hb01 : b 0 ≠ b 1 := fun h => absurd (hbinj h) (by decide)
  obtain ⟨ρ', hρ'⟩ := exists_conj_label basis ρ
  have hρreal : ρ' = ρ := by
    have h0 := (hsupp 0 ρ').mp (by rw [hconj 0 ρ ρ' hρ', hcρ]; exact hδne)
    have h1 := (hsupp 1 ρ').mp (by rw [hconj 1 ρ ρ' hρ', hcρ]; exact hδne)
    have hne := hconj_ne_principal ρ ρ' hρ' hρo
    rcases h0 with h0 | h0 | h0
    · exact absurd h0 hne
    · exact h0
    · rcases h1 with h1 | h1 | h1
      · exact absurd h1 hne
      · exact h1
      · exact absurd (h0.symm.trans h1) hb01
  have hρconj : ∀ g, starRingEnd ℂ ((basis.representation ρ).character g) =
      (basis.representation ρ).character g := fun g => by
    rw [← hρ' g, hρreal]
  have hbreal : ∀ i, ∀ g, starRingEnd ℂ ((basis.representation (b i)).character g) =
      (basis.representation (b i)).character g := by
    intro i
    obtain ⟨b', hb'⟩ := exists_conj_label basis (b i)
    have hb'eq : b' = b i := by
      have h := (hsupp i b').mp (by
        rw [hconj i (b i) b' hb', hcb]
        exact neg_ne_zero.mpr hδne)
      have hne := hconj_ne_principal (b i) b' hb' (hbne i).1
      rcases h with h | h | h
      · exact absurd h hne
      · exfalso
        apply (hbne i).2
        apply basis.distinct
        change (basis.representation (b i)).character = (basis.representation ρ).character
        funext g
        have h2 := hb' g
        rw [h] at h2
        rw [← Complex.conj_conj ((basis.representation (b i)).character g), ← h2, hρconj]
      · exact h
    intro g
    rw [← hb' g, hb'eq]
  have hTval : ∀ i g, T i g = 1 + δ * (basis.representation ρ).character g -
      δ * (basis.representation (b i)).character g := by
    intro i g
    rw [hexp i g]
    simp_rw [hval i]
    push_cast
    simp only [add_mul, sub_mul, ite_mul, one_mul, zero_mul, mul_assoc, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, hprincipal, Pi.one_apply]
  have hregval : ∀ i g, ¬ p ∣ orderOf g → (basis.representation (b i)).character g =
      (basis.representation ρ).character g + δ := by
    intro i g hg
    have h := hreg i g hg
    rw [hTval] at h
    rcases hδ with rfl | rfl
    · push_cast at h ⊢
      linear_combination -h
    · push_cast at h ⊢
      linear_combination h
  refine ⟨ρ, b 0, b 1, δ, hδ, ?_, ?_, ?_, hρo, (hbne 0).1, (hbne 1).1, fun h => (hbne 0).2 h.symm,
    fun h => (hbne 1).2 h.symm, hb01, hρconj, hbreal 0, hbreal 1, hTval 0, hTval 1,
    (hv 0).2.1, (hv 1).2.1, (hv 0).2.2.1, fun g hg => ⟨hregval 0 g hg, hregval 1 g hg⟩⟩
  · exact hB 0 ρ (by rw [hcρ]; exact hδne)
  · exact hB 0 (b 0) (by rw [hcb]; exact neg_ne_zero.mpr hδne)
  · exact hB 1 (b 1) (by rw [hcb]; exact neg_ne_zero.mpr hδne)

end Decomposition

section LinearPair

omit [Fintype G] in
theorem exists_linear_pair (W : Sylow p G) [IsCyclic (W : Subgroup G)] (hp5 : 5 ≤ p) (a : ℕ)
    (ha : 1 ≤ a) (hWcard : Nat.card W = p ^ a) :
    ∃ lam₁ lam₂ : (W : Subgroup G) →* ℂˣ, orderOf lam₁ = p ∧ orderOf lam₂ = p ∧
      lam₂ ≠ lam₁ ∧ lam₂ ≠ lam₁⁻¹ := by
  have hp : p.Prime := Fact.out
  have hcard : Nat.card ((W : Subgroup G) →* ℂˣ) = p ^ a := by
    let : CommGroup (W : Subgroup G) := IsCyclic.commGroup
    have : Finite (W : Subgroup G) := Nat.finite_of_card_ne_zero (by
      rw [hWcard]
      exact pow_ne_zero a hp.ne_zero)
    have : NeZero ((Nat.card (W : Subgroup G) : ℕ) : ℂ) :=
      ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
    obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self (W : Subgroup G) ℂ
    exact (Nat.card_congr e.toEquiv).trans hWcard
  have : Finite ((W : Subgroup G) →* ℂˣ) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero a hp.ne_zero)
  obtain ⟨lam₁, hlam₁⟩ := exists_prime_orderOf_dvd_card' p (G := (W : Subgroup G) →* ℂˣ) (by
    rw [hcard]
    exact dvd_pow_self p (by omega))
  have hcop2 : Nat.Coprime (orderOf lam₁) 2 := by
    rw [hlam₁]
    exact (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  refine ⟨lam₁, lam₁ ^ 2, hlam₁, by rw [hcop2.orderOf_pow, hlam₁], ?_, ?_⟩
  · intro h
    have h1 : lam₁ = 1 := by
      rw [pow_two] at h
      exact mul_eq_left.mp h
    rw [h1, orderOf_one] at hlam₁
    exact hp.one_lt.ne hlam₁
  · intro h
    have h3 : lam₁ ^ 3 = 1 := by
      rw [pow_succ, h]
      exact inv_mul_cancel lam₁
    have hdvd := orderOf_dvd_of_pow_eq_one h3
    rw [hlam₁] at hdvd
    have := Nat.le_of_dvd (by decide) hdvd
    omega

end LinearPair

section Expansion

theorem exists_label_of_linear {C : Type*} [Group C] [Fintype C]
    (basisC : FiniteIrreducibleCharacterBasis C) (χ : C →* ℂˣ) :
    ∃ θ, ∀ c, (basisC.representation θ).character c = χ c := by
  let linear : C →* ℂ := (Units.coeHom ℂ).comp χ
  let data : FiniteComplexRepresentation C :=
    { vector := ℂ, representation := scalarHomRepresentation linear }
  obtain ⟨θ, hθ⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisC data
    (representation_complex_line_isIrreducible _)
  refine ⟨θ, fun c => ?_⟩
  rw [hθ]
  exact congrFun (scalarHomRepresentation_character linear) c

omit [Fact p.Prime] in
theorem characterPairing_eq_sum_coefficients (basis : FiniteIrreducibleCharacterBasis G)
    (T U : G → ℂ) (hT : ∀ x g : G, T (g * x * g⁻¹) = T x)
    (hU : ∀ x g : G, U (g * x * g⁻¹) = U x) (c d : basis.index → ℤ)
    (hc : ∀ θ, characterPairing T (basis.representation θ).character = c θ)
    (hd : ∀ θ, characterPairing U (basis.representation θ).character = d θ) :
    characterPairing T U = ((∑ θ, c θ * d θ : ℤ) : ℂ) := by
  have hTexp : T = fun g => ∑ θ, (c θ : ℂ) * (basis.representation θ).character g := by
    funext g
    rw [finiteIrreducibleCharacterBasis_reconstruction basis T hT g]
    exact Finset.sum_congr rfl fun θ _ => by rw [hc θ]
  have hUexp : U = fun g => ∑ θ, (d θ : ℂ) * (basis.representation θ).character g := by
    funext g
    rw [finiteIrreducibleCharacterBasis_reconstruction basis U hU g]
    exact Finset.sum_congr rfl fun θ _ => by rw [hd θ]
  rw [hTexp, characterPairing_expansion_left, hUexp]
  simp_rw [characterPairing_expansion_right]
  push_cast
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [Finset.sum_eq_single θ]
  · rw [characterPairing_irreducible _ _ (basis.irreducible θ) (basis.irreducible θ),
      ite_eq_left rfl]
    ring
  · intro η _ hη
    rw [characterPairing_irreducible _ _ (basis.irreducible θ) (basis.irreducible η),
      ite_eq_right (fun h => hη (basis.distinct h).symm)]
    ring
  · intro h
    exact absurd (Finset.mem_univ θ) h

omit [Fact p.Prime] in
theorem mem_coefficientVirtualLattice (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) (T : G → ℂ) (hT : ∀ x g : G, T (g * x * g⁻¹) = T x)
    (c : basis.index → ℤ) (hc : ∀ θ, characterPairing T (basis.representation θ).character = c θ)
    (hB : ∀ θ, θ ∉ B → c θ = 0) : T ∈ coefficientVirtualLattice basis B := by
  have hTexp : T = ∑ θ, c θ • (basis.representation θ).character := by
    funext g
    rw [Finset.sum_apply, finiteIrreducibleCharacterBasis_reconstruction basis T hT g]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [hc θ, Pi.smul_apply, zsmul_eq_mul]
  rw [hTexp]
  refine Submodule.sum_mem _ fun θ _ => ?_
  by_cases hθ : θ ∈ B
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨θ, hθ, rfl⟩)
  · rw [hB θ hθ, zero_smul]
    exact Submodule.zero_mem _

end Expansion

section Columns

variable (W : Sylow p G) [IsCyclic (W : Subgroup G)]
  (N : Subgroup (Subgroup.centralizer (W : Set G))) [N.Normal]

theorem column_properties (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (hp2 : p ≠ 2) (a : ℕ)
    (hWcard : Nat.card W = p ^ a)
    (hindex : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (hcop : Nat.Coprime p (Nat.card N))
    (hpq : IsPGroup p (Subgroup.centralizer (W : Set G) ⧸ N))
    (hcomp : ((W : Subgroup G).subgroupOf (Subgroup.centralizer (W : Set G))).IsComplement' N)
    (lam : (W : Subgroup G) →* ℂˣ) (hlam : orderOf lam = p) :
    inversionColumn W (complementProjection W N hcomp) lam ∈ coefficientVirtualLattice basis
        (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) ∧
      (∀ g : G, inversionColumn W (complementProjection W N hcomp) lam g ≠ 0 →
        ∀ x y : G, x * y = g → Commute x y → (∃ e : ℕ, orderOf x = p ^ e) → ¬ p ∣ orderOf y →
          ∃ w ∈ (W : Subgroup G), Subgroup.zpowers w = (W : Subgroup G) ∧ IsConj x w) ∧
      characterPairing (inversionColumn W (complementProjection W N hcomp) lam)
        (inversionColumn W (complementProjection W N hcomp) lam) = 3 ∧
      characterPairing (inversionColumn W (complementProjection W N hcomp) lam)
        (basis.representation principal).character = 1 ∧
      ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ∀ v ∈ Subgroup.centralizer (W : Set G), ¬ p ∣ orderOf v →
          characterPairing (inversionColumn W (complementProjection W N hcomp) lam)
              (basis.representation χ).character =
            ((p : ℂ) ^ a)⁻¹ * ∑ w : (W : Subgroup G),
              (basis.representation χ).character ((w : G) * v) *
                (1 - starRingEnd ℂ (lam w : ℂ)) := by
  have hp : p.Prime := Fact.out
  have hlamp : lam ^ p = 1 := by
    have h := pow_orderOf_eq_one lam
    rwa [hlam] at h
  have hlam1 : lam ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hlam
    exact hp.one_lt.ne hlam
  have hlamsq : lam * lam ≠ 1 := by
    intro h
    have h2 : lam ^ 2 = 1 := by
      rw [pow_two]
      exact h
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    rw [hlam] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  refine ⟨?_, inversionColumn_support W N a hWcard hcop hpq hcomp lam hlamp, ?_, ?_, ?_⟩
  · choose c hc using fun θ =>
      inversionColumn_pairing_int basis W (complementProjection W N hcomp) lam θ
    refine mem_coefficientVirtualLattice basis _ _ (fun x g => inducedFunction_conjugate _ _ x g)
      c hc fun θ hθ => ?_
    have h := inversionColumn_pairing_not_mem W N basis ideal principal hprincipal a hWcard hcop
      hpq hcomp lam hlamp hθ
    rw [hc θ] at h
    exact_mod_cast h
  · rw [inversionColumn_gram W N hp2 a hWcard hindex hcop hpq hcomp lam lam hlamp hlamp hlam1
      hlam1, ite_eq_left rfl, ite_eq_right hlamsq]
    norm_num
  · rw [hprincipal]
    exact inversionColumn_pairing_one W N a hWcard hcop hpq hcomp lam hlam1
  · intro χ hχ v hvK hv
    exact inversionColumn_pairing_mem W N basis ideal principal hprincipal a hWcard hcop hpq hcomp
      lam hlamp hχ v ((mem_map_complement_iff W N hcop hpq v).mpr
        ⟨hvK, (Nat.Prime.coprime_iff_not_dvd hp).mpr hv⟩)

end Columns

end CyclicInversion

open CyclicInversion

theorem cyclic_odd_sylow_inversion_normalizer_two_generator_supported_principal_columns
    {G : Type u} [Group G] [Fintype G] (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a : ℕ) (ha : 1 ≤ a)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (W : Sylow p G) [IsCyclic (W : Subgroup G)] (hWcard : Nat.card W = p ^ a)
    (hindex : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (W : Set G)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1) :
    ∃ (J : Subgroup G) (π : Subgroup.centralizer (W : Set G) →* (W : Subgroup G)),
      J ≤ Subgroup.centralizer (W : Set G) ∧
      (J.subgroupOf (Subgroup.centralizer (W : Set G))).Characteristic ∧
      Nat.Coprime p (Nat.card J) ∧
      (W : Subgroup G) ⊔ J = Subgroup.centralizer (W : Set G) ∧ (W : Subgroup G) ⊓ J = ⊥ ∧
      (∀ w ∈ (W : Subgroup G), ∀ j ∈ J, w * j = j * w) ∧
      (∀ h ∈ Subgroup.normalizer (W : Set G), ∀ j ∈ J, h * j * h⁻¹ ∈ J) ∧
      (∀ k : Subgroup.centralizer (W : Set G), (k : G) ∈ (W : Subgroup G) → (π k : G) = k) ∧
      (∀ k : Subgroup.centralizer (W : Set G), (k : G) ∈ J → π k = 1) ∧
      (∃ h ∈ Subgroup.normalizer (W : Set G), h ∉ Subgroup.centralizer (W : Set G)) ∧
      (∀ h ∈ Subgroup.normalizer (W : Set G), h ∉ Subgroup.centralizer (W : Set G) →
        ∀ w ∈ (W : Subgroup G), h * w * h⁻¹ = w⁻¹) ∧
      (∀ θ : localBasis.index,
        brauerNormalizerCharacterResidueHom ideal p (W : Subgroup G) W.isPGroup'
            (Subgroup.centralizer (W : Set G)) le_rfl (Subgroup.centralizer_le_normalizer _)
            localBasis θ = centralCharacterResidueHom basis ideal principal ↔
          θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal) ∧
      (∀ θ : localBasis.index,
        θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal ↔
          ∃ μ : (W : Subgroup G) →* ℂˣ,
            ∀ k, (localBasis.representation θ).character k = μ (π k)) ∧
      (∀ μ : (W : Subgroup G) →* ℂˣ,
        ∃ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
          ∀ k, (localBasis.representation θ).character k = μ (π k)) ∧
      (∃ lam₁ lam₂ : (W : Subgroup G) →* ℂˣ, orderOf lam₁ = p ∧ orderOf lam₂ = p ∧
        lam₂ ≠ lam₁ ∧ lam₂ ≠ lam₁⁻¹) ∧
      ∀ lam₁ lam₂ : (W : Subgroup G) →* ℂˣ, orderOf lam₁ = p → orderOf lam₂ = p →
        lam₂ ≠ lam₁ → lam₂ ≠ lam₁⁻¹ →
        (∀ lam ∈ [lam₁, lam₂],
          inversionColumn W π lam ∈ coefficientVirtualLattice basis
            (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) ∧
          (∀ g : G, inversionColumn W π lam g ≠ 0 → ∀ x y : G, x * y = g → Commute x y →
            (∃ e : ℕ, orderOf x = p ^ e) → ¬ p ∣ orderOf y →
              ∃ w ∈ (W : Subgroup G), Subgroup.zpowers w = (W : Subgroup G) ∧ IsConj x w) ∧
          characterPairing (inversionColumn W π lam) (inversionColumn W π lam) = 3 ∧
          characterPairing (inversionColumn W π lam)
            (basis.representation principal).character = 1 ∧
          ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
            ∀ v ∈ Subgroup.centralizer (W : Set G), ¬ p ∣ orderOf v →
              characterPairing (inversionColumn W π lam) (basis.representation χ).character =
                ((p : ℂ) ^ a)⁻¹ * ∑ w : (W : Subgroup G),
                  (basis.representation χ).character ((w : G) * v) *
                    (1 - starRingEnd ℂ (lam w : ℂ))) ∧
        characterPairing (inversionColumn W π lam₁) (inversionColumn W π lam₂) = 2 ∧
        ∃ (ρ τ₁ τ₂ : basis.index) (δ : ℤ), (δ = 1 ∨ δ = -1) ∧
          ρ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
          τ₁ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
          τ₂ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
          ρ ≠ principal ∧ τ₁ ≠ principal ∧ τ₂ ≠ principal ∧ ρ ≠ τ₁ ∧ ρ ≠ τ₂ ∧ τ₁ ≠ τ₂ ∧
          (∀ g, starRingEnd ℂ ((basis.representation ρ).character g) =
            (basis.representation ρ).character g) ∧
          (∀ g, starRingEnd ℂ ((basis.representation τ₁).character g) =
            (basis.representation τ₁).character g) ∧
          (∀ g, starRingEnd ℂ ((basis.representation τ₂).character g) =
            (basis.representation τ₂).character g) ∧
          (∀ g, inversionColumn W π lam₁ g = 1 + δ * (basis.representation ρ).character g -
            δ * (basis.representation τ₁).character g) ∧
          (∀ g, inversionColumn W π lam₂ g = 1 + δ * (basis.representation ρ).character g -
            δ * (basis.representation τ₂).character g) ∧
          (Module.finrank ℂ (basis.representation τ₁).vector : ℤ) =
            Module.finrank ℂ (basis.representation ρ).vector + δ ∧
          (Module.finrank ℂ (basis.representation τ₂).vector : ℤ) =
            Module.finrank ℂ (basis.representation ρ).vector + δ ∧
          0 < (Module.finrank ℂ (basis.representation ρ).vector : ℤ) + δ ∧
          ∀ g : G, ¬ p ∣ orderOf g →
            (basis.representation τ₁).character g = (basis.representation ρ).character g + δ ∧
            (basis.representation τ₂).character g = (basis.representation ρ).character g + δ := by
  have hpp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨N, hNn, hcop, hpq⟩ := exists_centralizer_normal_complement W
  have hcomp := isComplement'_complement W N a hWcard hcop hpq
  have hJmem : ∀ k : Subgroup.centralizer (W : Set G),
      (k : G) ∈ N.map (Subgroup.centralizer (W : Set G)).subtype → k ∈ N := by
    rintro k ⟨n, hn, hnk⟩
    rwa [← (Subtype.ext hnk : n = k)]
  have hb₀ := principal_local_block_iff W N ideal localBasis localPrincipal hlocalPrincipal hcop
    hpq hcomp
  refine ⟨N.map (Subgroup.centralizer (W : Set G)).subtype, complementProjection W N hcomp,
    Subgroup.map_subtype_le N, map_complement_characteristic W N hcop hpq,
    by rw [card_map_complement]; exact hcop, sup_map_complement W N hcomp,
    inf_map_complement W N a hWcard hcop hpq,
    fun w hw j hj => Subgroup.mem_centralizer_iff.mp (Subgroup.map_subtype_le N hj) w hw,
    fun h hh j hj => map_complement_normalized W N hcop hpq h hh j hj,
    fun k hk => complementProjection_of_mem W N hcomp k hk,
    fun k hk => complementProjection_of_mem_complement W N hcomp k (hJmem k hk),
    exists_mem_normalizer_not_mem_centralizer W hindex,
    fun h hh hK w hw =>
      inverts_of_mem_normalizer (W : Subgroup G) hp2 a hWcard hindex h hh hK w hw,
    brauer_fiber_principal_iff W basis ideal principal hprincipal localBasis localPrincipal
      hlocalPrincipal, hb₀, fun μ => ?_, exists_linear_pair W hp a ha hWcard, ?_⟩
  · obtain ⟨θ, hθ⟩ := exists_label_of_linear localBasis (μ.comp (complementProjection W N hcomp))
    exact ⟨θ, (hb₀ θ).mpr ⟨μ, hθ⟩, hθ⟩
  intro lam₁ lam₂ h1 h2 h3 h4
  have hcolumn := fun lam hlam => column_properties W N basis ideal principal hprincipal hp2 a
    hWcard hindex hcop hpq hcomp lam hlam
  have hlamord : ∀ i : Fin 2, orderOf (![lam₁, lam₂] i) = p := by
    intro i
    fin_cases i
    exacts [h1, h2]
  have hlamp : ∀ i : Fin 2, ![lam₁, lam₂] i ^ p = 1 := fun i => by
    have h := pow_orderOf_eq_one (![lam₁, lam₂] i)
    rwa [hlamord i] at h
  have hlam1 : ∀ i : Fin 2, ![lam₁, lam₂] i ≠ 1 := fun i h => by
    have h' := hlamord i
    rw [h, orderOf_one] at h'
    exact hpp.one_lt.ne h'
  have hgram12 : characterPairing (inversionColumn W (complementProjection W N hcomp) lam₁)
      (inversionColumn W (complementProjection W N hcomp) lam₂) = 2 := by
    have hprod : lam₁ * lam₂ ≠ 1 := by
      intro h
      apply h4
      ext w
      have hw := congrArg (fun f : (W : Subgroup G) →* ℂˣ => (f w : ℂ)) h
      simp only [MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one] at hw
      simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
      exact eq_inv_of_mul_eq_one_right hw
    rw [inversionColumn_gram W N hp2 a hWcard hindex hcop hpq hcomp lam₁ lam₂ (hlamp 0) (hlamp 1)
      (hlam1 0) (hlam1 1), ite_eq_right (Ne.symm h3), ite_eq_right hprod]
    norm_num
  refine ⟨fun lam hlam => ?_, hgram12, ?_⟩
  · simp only [List.mem_cons] at hlam
    rcases hlam with rfl | rfl | hnil
    · exact hcolumn _ h1
    · exact hcolumn _ h2
    · exact absurd hnil List.not_mem_nil
  let T : Fin 2 → G → ℂ := fun i =>
    inversionColumn W (complementProjection W N hcomp) (![lam₁, lam₂] i)
  have hclass : ∀ i, ∀ x c : G, T i (c * x * c⁻¹) = T i x :=
    fun i x c => inducedFunction_conjugate _ _ x c
  choose c hc using fun (i : Fin 2) (θ : basis.index) =>
    inversionColumn_pairing_int basis W (complementProjection W N hcomp) (![lam₁, lam₂] i) θ
  have hpair : ∀ i j, characterPairing (T i) (T j) = ((∑ θ, c i θ * c j θ : ℤ) : ℂ) :=
    fun i j => characterPairing_eq_sum_coefficients basis (T i) (T j) (hclass i) (hclass j)
      (c i) (c j) (hc i) (hc j)
  have hone : ∀ i, c i principal = 1 := by
    intro i
    have h := (hc i principal).symm.trans (hcolumn _ (hlamord i)).2.2.2.1
    exact_mod_cast h
  have hnorm : ∀ i, ∑ θ, c i θ ^ 2 = 3 := by
    intro i
    have h := (hpair i i).symm.trans (hcolumn _ (hlamord i)).2.2.1
    simp_rw [pow_two]
    exact_mod_cast h
  have hgram : ∑ θ, c 0 θ * c 1 θ = 2 := by
    have h := (hpair 0 1).symm.trans hgram12
    exact_mod_cast h
  have hB : ∀ i θ, c i θ ≠ 0 →
      θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    intro i θ hne
    by_contra hθ
    apply hne
    have h := inversionColumn_pairing_not_mem W N basis ideal principal hprincipal a hWcard hcop
      hpq hcomp (![lam₁, lam₂] i) (hlamp i) hθ
    rw [hc i θ] at h
    exact_mod_cast h
  have hconj : ∀ i θ θ', (∀ g, (basis.representation θ').character g =
      starRingEnd ℂ ((basis.representation θ).character g)) → c i θ' = c i θ := by
    intro i θ θ' hθ'
    have h := inversionColumn_pairing_conj W N basis hp2 a hWcard hindex hcop hpq hcomp
      (![lam₁, lam₂] i) θ θ' hθ'
    rw [hc i θ, hc i θ'] at h
    exact_mod_cast h
  have hreg : ∀ i (g : G), ¬ p ∣ orderOf g → T i g = 0 := by
    intro i g hg
    by_contra hne
    obtain ⟨w, -, hgen, hw⟩ := inversionColumn_support W N a hWcard hcop hpq hcomp
      (![lam₁, lam₂] i) (hlamp i) g hne 1 g (one_mul g) (Commute.one_left g)
      ⟨0, by rw [orderOf_one, pow_zero]⟩ hg
    rw [isConj_one_right.mp hw, Subgroup.zpowers_one_eq_bot] at hgen
    have hcard := hWcard
    rw [← hgen, Subgroup.card_bot] at hcard
    have hlt : 1 < p ^ a := Nat.one_lt_pow (by omega) hpp.one_lt
    omega
  obtain ⟨ρ, τ₁, τ₂, δ, hδ, hρB, hτ₁B, hτ₂B, hρo, hτ₁o, hτ₂o, hρτ₁, hρτ₂, hτ₁τ₂, hρr, hτ₁r, hτ₂r,
      hT₁, hT₂, hd₁, hd₂, hpos, hregval⟩ :=
    norm_three_pair_decomposition basis principal hprincipal
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) T hclass c hc hone
      hnorm hgram (fun i => inversionColumn_one W _ _) hB hconj hreg
  exact ⟨ρ, τ₁, τ₂, δ, hδ, hρB, hτ₁B, hτ₂B, hρo, hτ₁o, hτ₂o, hρτ₁, hρτ₂, hτ₁τ₂, hρr, hτ₁r, hτ₂r,
    hT₁, hT₂, hd₁, hd₂, hpos, hregval⟩

end CFSG.Semidihedral.Principal
