module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Representations.TypeIWitnessSupportingFrobenius
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel
import CFSG.FeitThompson.OddOrder.SupportingComplementCyclicOrderBound
import CFSG.FeitThompson.OddOrder.PConfigAlignDerivedComplement
import CFSG.FeitThompson.OddOrder.FrobeniusKernelContainsRoots
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.OddFrobeniusComplementCyclicSylows
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.AlphaCoreNormalHall
import CFSG.FeitThompson.Local.SplitKernelRemovalExponentAbelianSylow
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy
import CFSG.FeitThompson.Foundations.NilpotentHomImageNilpotent
import CFSG.FeitThompson.Representations.ConjugationTransportsDadeSignalizers

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise CFSG.FeitThompson.Prep05

section Aux

variable {X : Type*} [Group X]

theorem conj_ne_one_iff {g z : X} : g⁻¹ * z * g ≠ 1 ↔ z ≠ 1 := by
  refine not_congr ⟨fun h => ?_, fun h => by rw [h]; group⟩
  have h2 : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
  rw [h] at h2
  simpa using h2.symm

theorem conj_smul_mono {A B : Subgroup X} (h : A ≤ B) (g : X) :
    MulAut.conj g • A ≤ MulAut.conj g • B :=
  fun _ hy => mem_conj_smul_iff.2 (h (mem_conj_smul_iff.1 hy))

theorem exponent_map_subtype (K : Subgroup X) (S : Subgroup ↥K) :
    Monoid.exponent ↥(S.map K.subtype) = Monoid.exponent ↥S :=
  (Monoid.exponent_eq_of_mulEquiv
    (Subgroup.equivMapOfInjective S K.subtype K.subtype_injective)).symm

theorem exponent_conj_smul (g : X) (S : Subgroup X) :
    Monoid.exponent ↥(MulAut.conj g • S) = Monoid.exponent ↥S :=
  (Monoid.exponent_eq_of_mulEquiv (Subgroup.equivSMul (MulAut.conj g) S)).symm

theorem exponent_subgroupOf {A L : Subgroup X} (h : A ≤ L) :
    Monoid.exponent ↥(A.subgroupOf L) = Monoid.exponent ↥A :=
  Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h)

theorem isMulCommutative_map_subtype (K : Subgroup X) {S : Subgroup ↥K}
    (h : IsMulCommutative ↥S) : IsMulCommutative ↥(S.map K.subtype) :=
  isMulCommutative_of_mulEquiv
    (Subgroup.equivMapOfInjective S K.subtype K.subtype_injective).symm

theorem isHallSubgroup_compl_primeFactors_of_isComplement' {H E : Subgroup X}
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥E)) (h : H.IsComplement' E) :
    IsHallSubgroup (((Nat.card ↥H).primeFactors : Set ℕ)ᶜ) E := by
  refine isHallSubgroup_iff.2 ⟨isPiNumber_iff.2 fun q hq hmem => ?_, ?_⟩
  · have h1 : q ∣ Nat.card ↥H := (Nat.mem_primeFactors.1 hmem).2.1
    have h2 : q ∣ Nat.card ↥E := (Nat.mem_primeFactors.1 hq).2.1
    exact (Nat.mem_primeFactors.1 hq).1.one_lt.ne'
      (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h1 h2))
  · rw [compl_compl, h.index_eq_card]
    exact isPiNumber_iff.2 fun _ hq => hq

theorem inf_centralizer_singleton_eq_bot_of_conj {H : Subgroup X} (hH : H.Normal) {g z : X}
    (h : H ⊓ centralizer ({g⁻¹ * z * g} : Set X) = ⊥) :
    H ⊓ centralizer ({z} : Set X) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_
  have hyz : y * z = z * y := mem_centralizer_singleton_iff.1 hy.2
  have hmem : g⁻¹ * y * g ∈ H ⊓ centralizer ({g⁻¹ * z * g} : Set X) := by
    refine ⟨by simpa [mul_assoc] using hH.conj_mem y hy.1 g⁻¹,
      mem_centralizer_singleton_iff.2 ?_⟩
    calc g⁻¹ * y * g * (g⁻¹ * z * g) = g⁻¹ * (y * z) * g := by group
      _ = g⁻¹ * (z * y) * g := by rw [hyz]
      _ = g⁻¹ * z * g * (g⁻¹ * y * g) := by group
  rw [h] at hmem
  have h1 : g⁻¹ * y * g = 1 := hmem
  have h2 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rw [h1] at h2
  simpa using h2.symm

theorem inf_centralizer_le_conj_smul {H U U₁ : Subgroup X} (hH : H.Normal)
    (hcent : ∀ h ∈ H, h ≠ 1 → U ⊓ centralizer ({h} : Set X) ≤ U₁) (g : X) {z : X}
    (hz : z ∈ H) (hz1 : z ≠ 1) :
    (MulAut.conj g • U) ⊓ centralizer ({z} : Set X) ≤ MulAut.conj g • U₁ := by
  intro y hy
  have hyU : g⁻¹ * y * g ∈ U := mem_conj_smul_iff.1 hy.1
  have hyz : y * z = z * y := mem_centralizer_singleton_iff.1 hy.2
  have hzH : g⁻¹ * z * g ∈ H := by simpa [mul_assoc] using hH.conj_mem z hz g⁻¹
  refine mem_conj_smul_iff.2
    (hcent _ hzH (conj_ne_one_iff.2 hz1) ⟨hyU, mem_centralizer_singleton_iff.2 ?_⟩)
  calc g⁻¹ * y * g * (g⁻¹ * z * g) = g⁻¹ * (y * z) * g := by group
    _ = g⁻¹ * (z * y) * g := by rw [hyz]
    _ = g⁻¹ * z * g * (g⁻¹ * y * g) := by group

theorem exists_exponent_eq_and_isMulCommutative_of_isComplement' [Finite X] [Group.IsSolvable X]
    {U D : Subgroup X} (hU : IsFrobeniusType X U) (hD : (hallCore X).IsComplement' D) :
    ∃ D₀ ≤ D, ∃ D₁ ≤ D, Monoid.exponent ↥D₀ = Monoid.exponent ↥D ∧
      (∀ d ∈ D₀, d ≠ 1 → hallCore X ⊓ centralizer {d} = ⊥) ∧
      IsMulCommutative ↥D₁ ∧
      ∀ k ∈ hallCore X, k ≠ 1 → D ⊓ centralizer {k} ≤ D₁ := by
  obtain ⟨E₀, hE₀U, hexp, hfree⟩ := hU.exists_exponent_eq
  obtain ⟨E₁, hE₁U, -, hcomm, hcent⟩ := hU.exists_abelian_normal
  have hcopD : Nat.Coprime (Nat.card ↥(hallCore X)) (Nat.card ↥D) := by
    rw [← hD.symm.index_eq_card]; exact coprime_natCard_index_hallCore
  obtain ⟨g, hg⟩ := exists_conj_smul_eq_of_isHallSubgroup
    (isHallSubgroup_compl_primeFactors_of_isComplement' hU.coprime_card hU.isComplement')
    (isHallSubgroup_compl_primeFactors_of_isComplement' hcopD hD)
  have hcomm' : IsMulCommutative ↥(MulAut.conj g • E₁) := by
    letI := hcomm; exact isMulCommutative_conj_smul g E₁
  refine ⟨MulAut.conj g • E₀, (conj_smul_mono hE₀U g).trans (le_of_eq hg),
    MulAut.conj g • E₁, (conj_smul_mono hE₁U g).trans (le_of_eq hg), ?_, ?_, hcomm', ?_⟩
  · rw [exponent_conj_smul, hexp, ← hg, exponent_conj_smul]
  · intro d hd hd1
    exact inf_centralizer_singleton_eq_bot_of_conj hallCore_normal (g := g)
      (hfree _ (mem_conj_smul_iff.1 hd) (conj_ne_one_iff.2 hd1))
  · intro k hk hk1
    rw [← hg]
    exact inf_centralizer_le_conj_smul hallCore_normal hcent g hk hk1

theorem not_isCyclic_of_elementaryAbelianPRank_eq_two {p : ℕ} [Finite X]
    (hp : p.Prime) (h : elementaryAbelianPRank p X = 2) : ¬ IsCyclic X := by
  have hmem : 2 ∈ elementaryAbelianRanks p X :=
    h ▸ elementaryAbelianPRank_mem_elementaryAbelianRanks hp.one_lt
  obtain ⟨A, hcomm, hexp, hcard⟩ := (mem_elementaryAbelianRanks_iff_exists_subgroup hp).1 hmem
  exact not_isCyclic_of_isElementaryAbelian_of_natCard_eq_pow hp
    (isElementaryAbelian_iff.2 ⟨hcomm, hexp⟩) hcard le_rfl

theorem three_le_of_one_lt_of_odd {n : ℕ} (h1 : 1 < n) (hodd : Odd n) : 3 ≤ n := by
  rw [Nat.odd_iff] at hodd; omega

end Aux

section HallCore

variable {G : Type*} [Group G]

theorem hallCoreOf_eq_hallCoreIn (M : Subgroup G) :
    hallCoreOf M = CFSG.FeitThompson.Prep09.hallCoreIn M := (rfl)

theorem subgroupOf_hallCoreOf (M : Subgroup G) :
    (hallCoreOf M).subgroupOf M = hallCore ↥M := by
  rw [hallCoreOf_eq]
  exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

theorem relIndex_hallCoreOf (M : Subgroup G) :
    (hallCoreOf M).relIndex M = (hallCore ↥M).index := by
  rw [Subgroup.relIndex, subgroupOf_hallCoreOf]

theorem natCard_hallCoreOf (M : Subgroup G) :
    Nat.card ↥(hallCoreOf M) = Nat.card ↥(hallCore ↥M) := by
  rw [hallCoreOf_eq, Subgroup.card_subtype]

theorem normal_subgroupOf_hallCoreOf (M : Subgroup G) : ((hallCoreOf M).subgroupOf M).Normal := by
  rw [subgroupOf_hallCoreOf]; exact hallCore_normal

theorem le_normalizer_hallCoreOf (M : Subgroup G) :
    M ≤ normalizer ((hallCoreOf M : Subgroup G) : Set G) := by
  rw [hallCoreOf_eq]; exact le_normalizer_map_subtype_hallCore M

theorem isNilpotent_hallCoreOf [Finite G] (M : Subgroup G) :
    Group.IsNilpotent ↥(hallCoreOf M) := by
  rw [hallCoreOf_eq]; exact isNilpotent_map _ _

theorem hallCoreOf_ne_bot [Finite G] {M : Subgroup G} (hMI : IsTypeI M) : hallCoreOf M ≠ ⊥ := by
  intro hbot
  refine hMI.hallCore_ne_bot ?_
  rw [← subgroupOf_hallCoreOf M, hbot]
  simp

theorem coprime_natCard_relIndex_hallCoreOf [Finite G] (M : Subgroup G) :
    Nat.Coprime (Nat.card ↥(hallCoreOf M)) ((hallCoreOf M).relIndex M) := by
  rw [natCard_hallCoreOf, relIndex_hallCoreOf]
  exact coprime_natCard_index_hallCore

theorem coprime_natCard_index_hallCoreOf [Finite G] {M : Subgroup G}
    (hS : sigmaCore M = hallCoreOf M) :
    Nat.Coprime (Nat.card ↥(hallCoreOf M)) (hallCoreOf M).index := by
  rw [← Subgroup.relIndex_mul_index (hallCoreOf_le M)]
  refine Nat.Coprime.mul_right (coprime_natCard_relIndex_hallCoreOf M) ?_
  rw [Nat.coprime_iff_gcd_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
  intro q hq hdvd
  rw [Nat.dvd_gcd_iff] at hdvd
  have hmem : q ∈ (Nat.card ↥(sigmaCore M)).primeFactors := by
    rw [hS]; exact Nat.mem_primeFactors.2 ⟨hq, hdvd.1, Nat.card_pos.ne'⟩
  exact not_dvd_index_of_mem_sigmaPrimes
    (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) q hmem) hdvd.2

theorem inf_centralizer_singleton_eq_bot_of_isFixedPointFreeOn {A B : Subgroup G}
    (h : IsFixedPointFreeOn A B) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    A ⊓ centralizer ({b} : Set G) = ⊥ := by
  have h' := h b hb hb1
  rwa [centralizerIn_eq, centralizer_coe_zpowers] at h'

theorem isFixedPointFreeOn_of_inf_centralizer_singleton_eq_bot {A B : Subgroup G}
    (h : ∀ b ∈ B, b ≠ 1 → A ⊓ centralizer ({b} : Set G) = ⊥) : IsFixedPointFreeOn A B := by
  intro b hb hb1
  rw [centralizerIn_eq, centralizer_coe_zpowers]
  exact h b hb hb1

end HallCore

section Node

variable {G : Type*} [Group G] [Finite G]

theorem exists_witnesses {M D : Subgroup G} (hMI : IsTypeI M) [Group.IsSolvable ↥M]
    (hDM : D ≤ M) (hsd : FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) D) :
    ∃ D₀ ≤ D, ∃ D₁ ≤ D, Monoid.exponent ↥D₀ = Monoid.exponent ↥D ∧
      IsFixedPointFreeOn (hallCoreOf M) D₀ ∧ IsMulCommutative ↥D₁ ∧
      ∀ k ∈ hallCoreOf M, k ≠ 1 → centralizerIn D (zpowers k) ≤ D₁ := by
  obtain ⟨U, hU, -⟩ := hMI.exists_isFrobeniusType
  have hcompl : (hallCore ↥M).IsComplement' (D.subgroupOf M) := by
    rw [← subgroupOf_hallCoreOf M]
    exact isComplement'_subgroupOf_of_coe_mul_coe_eq hsd.coe_eq_mul.symm hsd.inf_eq_bot
  obtain ⟨D₀', hD₀', D₁', hD₁', hexp, hfree, hcomm, hcent⟩ :=
    exists_exponent_eq_and_isMulCommutative_of_isComplement' hU hcompl
  have hmapD : ∀ {S : Subgroup ↥M}, S ≤ D.subgroupOf M → S.map M.subtype ≤ D := by
    intro S hS
    refine (Subgroup.map_mono hS).trans ?_
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  refine ⟨D₀'.map M.subtype, hmapD hD₀', D₁'.map M.subtype, hmapD hD₁', ?_, ?_,
    isMulCommutative_map_subtype M hcomm, ?_⟩
  · rw [exponent_map_subtype, hexp, exponent_subgroupOf hDM]
  · intro d hd hd1
    obtain ⟨d', hd'mem, rfl⟩ := hd
    rw [centralizerIn_eq, centralizer_coe_zpowers]
    have key := hfree d' hd'mem (fun hc => hd1 (by rw [hc]; rfl))
    rw [← subgroupOf_hallCoreOf M] at key
    exact (inf_centralizer_singleton_subgroupOf_eq_bot_iff (hallCoreOf_le M) d').1 key
  · intro k hk hk1 y hy
    rw [centralizerIn_eq, centralizer_coe_zpowers] at hy
    have hyM : y ∈ M := hDM hy.1
    have hkM : k ∈ M := hallCoreOf_le M hk
    have hk' : (⟨k, hkM⟩ : ↥M) ∈ hallCore ↥M := by
      rw [← subgroupOf_hallCoreOf M]; exact mem_subgroupOf.2 hk
    have hk1' : (⟨k, hkM⟩ : ↥M) ≠ 1 := fun hc => hk1 (by simpa using Subtype.ext_iff.1 hc)
    have hcomm' : y * k = k * y := mem_centralizer_singleton_iff.1 hy.2
    exact ⟨⟨y, hyM⟩,
      hcent _ hk' hk1' ⟨mem_subgroupOf.2 hy.1,
        mem_centralizer_singleton_iff.2 (Subtype.ext hcomm')⟩, rfl⟩

theorem pow_two_le_natCard_of_elementaryAbelianPRank_eq_two {p : ℕ} {P A : Subgroup G}
    (hp : p.Prime) (hrank : elementaryAbelianPRank p ↥P = 2) (hPA : P ≤ A) :
    p ^ 2 ≤ Nat.card ↥A := by
  have hmem : 2 ∈ elementaryAbelianRanks p ↥P :=
    hrank ▸ elementaryAbelianPRank_mem_elementaryAbelianRanks hp.one_lt
  obtain ⟨B, -, -, hcard⟩ := (mem_elementaryAbelianRanks_iff_exists_subgroup hp).1 hmem
  have hdvd : p ^ 2 ∣ Nat.card ↥A := by
    rw [← hcard, ← Subgroup.card_subtype P B]
    exact Subgroup.card_dvd_of_le ((Subgroup.map_subtype_le _).trans hPA)
  exact Nat.le_of_dvd Nat.card_pos hdvd

theorem not_isFixedPointFree_of_elementaryAbelianPRank_eq_two {M K P B : Subgroup G} {p : ℕ}
    (hodd : Odd (Nat.card G)) (hp : p.Prime) (hKM : K ≤ M) (hKnorm : (K.subgroupOf M).Normal)
    (hK : K ≠ ⊥) (hKnil : Group.IsNilpotent ↥K) (hpK : ¬ p ∣ Nat.card ↥K)
    (hPM : P ≤ M) (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p)
    (hrank : elementaryAbelianPRank p ↥P = 2)
    (hmul : (K : Set G) * (B : Set G) = (M : Set G)) (hdisj : K ⊓ B = ⊥)
    (hfree : ∀ b ∈ B, b ≠ 1 → K ⊓ centralizer ({b} : Set G) = ⊥) : False := by
  have := Fact.mk hp
  have hModd : Odd (Nat.card ↥M) := hodd.of_dvd_nat M.card_subgroup_dvd_card
  set K' : Subgroup ↥M := K.subgroupOf M with hK'
  set B' : Subgroup ↥M := B.subgroupOf M with hB'
  have hcompl : K'.IsComplement' B' := isComplement'_subgroupOf_of_coe_mul_coe_eq hmul hdisj
  have _ : K'.Normal := hKnorm
  have _ : Group.IsNilpotent ↥K' :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hKM)).2 hKnil
  have _ : Group.IsSolvable ↥K' := by infer_instance
  have hK'bot : K' ≠ ⊥ := by
    rw [hK', Ne, Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.2 hKM]
    exact hK
  have hfree' : ∀ u ∈ B', u ≠ 1 → K' ⊓ centralizer ({u} : Set ↥M) = ⊥ := by
    intro u hu hu1
    exact (inf_centralizer_singleton_subgroupOf_eq_bot_iff hKM u).2
      (hfree (u : G) (mem_subgroupOf.1 hu) fun hc => hu1 (Subtype.ext hc))
  have hcardK' : Nat.card ↥K' = Nat.card ↥K := natCard_subgroupOf_of_le hKM
  have hfactB : (Nat.card ↥B').factorization p = (Nat.card ↥M).factorization p := by
    have hmulcard : Nat.card ↥K' * Nat.card ↥B' = Nat.card ↥M := hcompl.card_mul_card
    have h0 : (Nat.card ↥K').factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by rwa [hcardK'])
    have hEq := congrArg (fun n : ℕ => n.factorization p) hmulcard
    simp only [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      h0] at hEq
    simpa using hEq
  obtain ⟨S⟩ : Nonempty (Sylow p ↥B') := inferInstance
  have hScard : Nat.card ↥(S : Subgroup ↥B') = p ^ (Nat.card ↥M).factorization p := by
    rw [S.card_eq_multiplicity, hfactB]
  have hScyc : IsCyclic ↥(S : Subgroup ↥B') :=
    isCyclic_sylow_of_free_complement (L := ↥M) (H := K') (E := B') hModd hK'bot hfree' hp _
      S.card_eq_multiplicity
  set Q : Subgroup ↥M := (S : Subgroup ↥B').map B'.subtype with hQ
  have hQcard : Nat.card ↥Q = p ^ (Nat.card ↥M).factorization p := by
    rw [hQ, Subgroup.card_subtype, hScard]
  have hPcard' : Nat.card ↥(P.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
    rw [natCard_subgroupOf_of_le hPM, hPcard]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥M)
    (Sylow.ofCard Q hQcard) (Sylow.ofCard (P.subgroupOf M) hPcard')
  have hgeq : MulAut.conj g • Q = P.subgroupOf M := by
    have h := congrArg (fun S : Sylow p ↥M => (S : Subgroup ↥M)) hg
    simp only [Sylow.coe_ofCard] at h
    exact h
  have hPcyc : IsCyclic ↥P := by
    refine (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hPM)).1 ?_
    refine (MulEquiv.isCyclic (hgeq ▸ Subgroup.equivSMul (MulAut.conj g) Q)).1 ?_
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective _ B'.subtype B'.subtype_injective)).1 hScyc
  exact not_isCyclic_of_elementaryAbelianPRank_eq_two (X := ↥P) hp hrank hPcyc

end Node

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson.Prep05

universe u

theorem FPF_type_i_supporting_group_configuration
    (hdade : Statements.FTS_type_I_dade_support.{u}) :
    Statements.FPF_type_i_supporting_group_configuration.{u} := by
  intro G _ _ hG p hp hsmall M N hM hN hMI hNI hpK P hPcomm hPsyl hrank hPsig x hxP hxord
    hCK hnorm hnotle
  have hG' : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hSM, -⟩ := hdade G hG' M hM hMI
  obtain ⟨hSN, -⟩ := hdade G hG' N hN hNI
  rw [← hallCoreOf_eq_hallCoreIn] at hSM hSN
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hx1 : x ≠ 1 := by
    intro h; rw [h, orderOf_one] at hxord; exact hp.one_lt.ne' hxord.symm
  have hPbot : P ≠ ⊥ := fun hbot => hx1 (by rw [hbot] at hxP; simpa using hxP)
  have hPp : IsPGroup p ↥P := IsPGroup.of_card hPsyl.2
  obtain ⟨hPH, ⟨E, hEN, hEbot, hEsd, hEfree⟩, hMsd, -⟩ :=
    FPF_type_i_witness_supporting_frobenius hdade G hG p hp hsmall M N hM hN hMI hNI
      P hPsyl.1 hPcomm hPp hrank hPsig x hxP hxord hnorm hnotle
  obtain ⟨D₀, hD₀, D₁, hD₁, hexp, hD₀free, hD₁comm, hD₁cent⟩ :=
    exists_witnesses hMI inf_le_left hMsd
  have hCKx : hallCoreOf M ⊓ centralizer ({x} : Set G) ≠ ⊥ := by
    intro hbot
    refine hCK ?_
    rw [centralizerIn_eq, centralizer_coe_zpowers, hbot]
    exact bot_le
  have hDJ : M ⊓ N ≤ hallCoreOf N := by
    have _ := hMsolv
    have _ : ((hallCoreOf M).subgroupOf M).Normal := normal_subgroupOf_hallCoreOf M
    have _ : ((hallCoreOf N).subgroupOf N).Normal := normal_subgroupOf_hallCoreOf N
    refine le_of_inf_centralizer_ne_bot_of_mem_sylow (E := E) rfl (hallCoreOf_le M)
      (hallCoreOf_ne_bot hMI) (coprime_natCard_relIndex_hallCoreOf M) hMsd.coe_eq_mul.symm
      hMsd.inf_eq_bot (hallCoreOf_le N) (isNilpotent_hallCoreOf N)
      (coprime_natCard_relIndex_hallCoreOf N) hEsd.coe_eq_mul.symm hEsd.inf_eq_bot
      (fun e he he1 => inf_centralizer_singleton_eq_bot_of_isFixedPointFreeOn hEfree he he1)
      hD₀ hexp
      (fun d hd hd1 => inf_centralizer_singleton_eq_bot_of_isFixedPointFreeOn hD₀free hd hd1)
      hD₁comm ?_ hp hpK hPsyl.1 hPsyl.2 hPbot hPH hxP hx1 hCKx
    intro k hk hk1
    have h := hD₁cent k hk hk1
    rwa [centralizerIn_eq, centralizer_coe_zpowers] at h
  have hEcyc := frobenius_complement_isCyclic_and_two_mul_natCard_le (π := _) hG.odd_natCard hp
    (isNilpotent_hallCoreOf N) (hallCoreOf_le N) (normal_subgroupOf_hallCoreOf N)
    (isHallSubgroup_subgroupOf_primeFactors (hallCoreOf_le N)
      (coprime_natCard_relIndex_hallCoreOf N))
    hEN (isComplement'_subgroupOf_of_coe_mul_coe_eq hEsd.coe_eq_mul.symm hEsd.inf_eq_bot)
    (fun y hy hy1 => inf_centralizer_singleton_eq_bot_of_isFixedPointFreeOn hEfree hy hy1)
    hDJ hPsyl.1 hPsyl.2 hPH hrank hxP hxord hnorm
  have hpdvd : p ∣ Nat.card G := hxord ▸ orderOf_dvd_natCard x
  have hp3 : 3 ≤ p := three_le_of_one_lt_of_odd hp.one_lt (hG.odd_natCard.of_dvd_nat hpdvd)
  have hEodd : Odd (Nat.card ↥E) := hG.odd_natCard.of_dvd_nat E.card_subgroup_dvd_card
  have hE3 : 3 ≤ Nat.card ↥E :=
    three_le_of_one_lt_of_odd ((E.one_lt_card_iff_ne_bot).2 hEbot) hEodd
  refine ⟨hallCoreOf_ne_bot hMI, hallCoreOf_ne_bot hNI, isNilpotent_hallCoreOf M,
    isNilpotent_hallCoreOf N, le_normalizer_hallCoreOf M, le_normalizer_hallCoreOf N,
    coprime_natCard_index_hallCoreOf hSM, coprime_natCard_index_hallCoreOf hSN, hMsolv, hPH,
    hMsd, hDJ, ⟨D₀, D₁, hD₀, hD₁, hexp, hD₀free, hD₁comm, hD₁cent⟩,
    ⟨E, hEN, hEbot, hEcyc.1, hEsd, hEfree, hE3, hEcyc.2.1, hEcyc.2.2⟩, hp3,
    pow_two_le_natCard_of_elementaryAbelianPRank_eq_two hp hrank hPH, ?_⟩
  rintro ⟨B, hBM, hBsd, hBfree⟩
  exact not_isFixedPointFree_of_elementaryAbelianPRank_eq_two hG.odd_natCard hp
    (hallCoreOf_le M) (normal_subgroupOf_hallCoreOf M) (hallCoreOf_ne_bot hMI)
    (isNilpotent_hallCoreOf M) hpK hPsyl.1 hPsyl.2 hrank hBsd.coe_eq_mul.symm hBsd.inf_eq_bot
    (fun b hb hb1 => inf_centralizer_singleton_eq_bot_of_isFixedPointFreeOn hBfree hb hb1)

end CFSG.FeitThompson.Proofs
