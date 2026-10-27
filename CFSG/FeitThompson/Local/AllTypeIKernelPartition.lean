module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.AllTypeIPacketCover
import CFSG.FeitThompson.Local.AllTypeICoreCentralizerControl
import CFSG.FeitThompson.Representations.TypeISupportingGroupConfiguration
import CFSG.FeitThompson.Local.CommonPrimeFixedCoreFittingEnvelope
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson.Prep05
open CFSG.FeitThompson.Prep09 (coreFixedSet centIn)

universe u

variable {G : Type u} [Group G]

theorem isConjugateSubgroup_iff_smul {X Y : Subgroup G} :
    IsConjugateSubgroup X Y ↔ ∃ g : G, MulAut.conj g • X = Y := by
  simp only [IsConjugateSubgroup, Subgroup.pointwise_smul_def]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, hg.symm⟩, fun ⟨g, hg⟩ => ⟨g, hg.symm⟩⟩

theorem isConjugateSubgroup_symm {X Y : Subgroup G} (h : IsConjugateSubgroup X Y) :
    IsConjugateSubgroup Y X := by
  obtain ⟨g, hg⟩ := isConjugateSubgroup_iff_smul.1 h
  refine isConjugateSubgroup_iff_smul.2 ⟨g⁻¹, ?_⟩
  rw [← hg, smul_smul, ← map_mul]
  simp

theorem isConjugateSubgroup_trans {X Y Z : Subgroup G} (h : IsConjugateSubgroup X Y)
    (h' : IsConjugateSubgroup Y Z) : IsConjugateSubgroup X Z := by
  obtain ⟨g, hg⟩ := isConjugateSubgroup_iff_smul.1 h
  obtain ⟨g', hg'⟩ := isConjugateSubgroup_iff_smul.1 h'
  refine isConjugateSubgroup_iff_smul.2 ⟨g' * g, ?_⟩
  rw [← hg', ← hg, smul_smul, ← map_mul]

def coatomConjSetoid (G : Type u) [Group G] : Setoid {M : Subgroup G // IsCoatom M} where
  r X Y := IsConjugateSubgroup (X : Subgroup G) (Y : Subgroup G)
  iseqv :=
    { refl := fun X => isConjugateSubgroup_refl (X : Subgroup G)
      symm := isConjugateSubgroup_symm
      trans := isConjugateSubgroup_trans }

theorem coatomConjSetoid_rel_iff {X Y : {M : Subgroup G // IsCoatom M}} :
    (coatomConjSetoid G) X Y ↔ IsConjugateSubgroup (X : Subgroup G) (Y : Subgroup G) := Iff.rfl

noncomputable def coatomRepSub (G : Type u) [Group G] [Finite G] :
    Fin (Nat.card (Quotient (coatomConjSetoid G))) → {M : Subgroup G // IsCoatom M} :=
  fun i => Quotient.out ((Finite.equivFin (Quotient (coatomConjSetoid G))).symm i)

noncomputable def coatomRep (G : Type u) [Group G] [Finite G] :
    Fin (Nat.card (Quotient (coatomConjSetoid G))) → Subgroup G :=
  fun i => (coatomRepSub G i : Subgroup G)

theorem isCoatom_coatomRep [Finite G] (i : Fin (Nat.card (Quotient (coatomConjSetoid G)))) :
    IsCoatom (coatomRep G i) := (coatomRepSub G i).2

theorem mk_coatomRepSub [Finite G] (i : Fin (Nat.card (Quotient (coatomConjSetoid G)))) :
    Quotient.mk (coatomConjSetoid G) (coatomRepSub G i) =
      (Finite.equivFin (Quotient (coatomConjSetoid G))).symm i := Quotient.out_eq _

theorem isConjugateSubgroup_coatomRep_iff [Finite G] {M : Subgroup G} (hM : IsCoatom M)
    (i : Fin (Nat.card (Quotient (coatomConjSetoid G)))) :
    IsConjugateSubgroup (coatomRep G i) M ↔
      i = (Finite.equivFin (Quotient (coatomConjSetoid G)))
        (Quotient.mk (coatomConjSetoid G) ⟨M, hM⟩) := by
  constructor
  · intro h
    have hq : Quotient.mk (coatomConjSetoid G) (coatomRepSub G i) =
        Quotient.mk (coatomConjSetoid G) ⟨M, hM⟩ := Quotient.sound h
    rw [mk_coatomRepSub] at hq
    rw [← hq]; simp
  · intro h
    have hq : Quotient.mk (coatomConjSetoid G) (coatomRepSub G i) =
        Quotient.mk (coatomConjSetoid G) ⟨M, hM⟩ := by
      rw [mk_coatomRepSub, h]; simp
    exact Quotient.exact hq

theorem existsUnique_isConjugateSubgroup_coatomRep [Finite G] {M : Subgroup G} (hM : IsCoatom M) :
    ∃! i : Fin (Nat.card (Quotient (coatomConjSetoid G))),
      IsConjugateSubgroup (coatomRep G i) M :=
  ⟨_, (isConjugateSubgroup_coatomRep_iff hM _).2 rfl,
    fun j hj => (isConjugateSubgroup_coatomRep_iff hM j).1 hj⟩

theorem coatomRep_injective [Finite G] : Function.Injective (coatomRep G) := fun i j hij =>
  (existsUnique_isConjugateSubgroup_coatomRep (isCoatom_coatomRep j)).unique
    (by rw [hij]; exact isConjugateSubgroup_refl _) (isConjugateSubgroup_refl _)

theorem existsUnique_mem_range_coatomRep [Finite G] {M : Subgroup G} (hM : IsCoatom M) :
    ∃! T, T ∈ Set.range (coatomRep G) ∧
      ∃ g : G, Subgroup.map (MulAut.conj g : G ≃* G) M = T := by
  obtain ⟨i, hi, huniq⟩ := existsUnique_isConjugateSubgroup_coatomRep hM
  refine ⟨coatomRep G i, ⟨⟨i, rfl⟩, ?_⟩, ?_⟩
  · obtain ⟨g, hg⟩ := isConjugateSubgroup_symm hi
    exact ⟨g, hg.symm⟩
  · rintro T ⟨⟨j, rfl⟩, g, hg⟩
    rw [huniq j (isConjugateSubgroup_symm ⟨g, hg.symm⟩)]

theorem zero_lt_card_quotient_coatomConjSetoid (G : Type u) [Group G] [Finite G] [Nontrivial G] :
    0 < Nat.card (Quotient (coatomConjSetoid G)) := by
  obtain ⟨M, hM, -⟩ := exists_isCoatom_ge_of_ne_top (bot_ne_top (α := Subgroup G))
  have : Nonempty (Quotient (coatomConjSetoid G)) := ⟨Quotient.mk _ ⟨M, hM⟩⟩
  exact Nat.card_pos

theorem conj_mem_sdiff_hallCoreOf {M : Subgroup G} {l : G} (hl : l ∈ M) {x : G}
    (hx : x ∈ (hallCoreOf M : Set G) \ {1}) :
    l * x * l⁻¹ ∈ (hallCoreOf M : Set G) \ {1} := by
  have hnorm := le_normalizer_hallCoreOf M hl
  rw [Subgroup.mem_set_normalizer_iff] at hnorm
  refine ⟨(hnorm x).1 hx.1, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro hc
  apply hx.2
  have hx1 : x = l⁻¹ * (l * x * l⁻¹) * l := by group
  rw [hc] at hx1
  simp only [mul_one, inv_mul_cancel] at hx1
  simpa using hx1

theorem mem_coreFixedSet_of_mem_hallCoreOf {M : Subgroup G} {a : G}
    (ha : a ∈ hallCoreOf M) (ha1 : a ≠ 1) : a ∈ coreFixedSet (hallCoreOf M) M := by
  refine ⟨hallCoreOf_le M ha, ha1, fun hbot => ?_⟩
  have hself : a ∈ centIn (hallCoreOf M) {a} :=
    ⟨ha, by simp [Subgroup.mem_centralizer_singleton_iff]⟩
  rw [hbot] at hself
  exact ha1 (by simpa using hself)

theorem mem_of_conj_mem_sdiff_hallCoreOf [Finite G] {M : Subgroup G}
    (hfus : ∀ a ∈ coreFixedSet (hallCoreOf M) M, ∀ b ∈ coreFixedSet (hallCoreOf M) M,
      (∃ g : G, g⁻¹ * a * g = b) → ∃ m ∈ M, m⁻¹ * a * m = b)
    (hcen : ∀ h ∈ (hallCoreOf M : Set G) \ {1}, centralizer ({h} : Set G) ≤ M)
    {a g : G} (ha : a ∈ (hallCoreOf M : Set G) \ {1})
    (hga : g * a * g⁻¹ ∈ (hallCoreOf M : Set G) \ {1}) : g ∈ M := by
  obtain ⟨haH, ha1⟩ := ha
  simp only [Set.mem_singleton_iff] at ha1
  have haA : a ∈ coreFixedSet (hallCoreOf M) M := mem_coreFixedSet_of_mem_hallCoreOf haH ha1
  obtain ⟨hbH, hb1⟩ := hga
  simp only [Set.mem_singleton_iff] at hb1
  have hbA : (g * a * g⁻¹) ∈ coreFixedSet (hallCoreOf M) M :=
    mem_coreFixedSet_of_mem_hallCoreOf hbH hb1
  obtain ⟨m, hm, hmeq⟩ := hfus a haA _ hbA ⟨g⁻¹, by group⟩
  have hcent : m * g ∈ centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hkey : a = (m * g) * a * (m * g)⁻¹ := by
      rw [mul_inv_rev]
      calc a = m * (m⁻¹ * a * m) * m⁻¹ := by group
        _ = m * (g * a * g⁻¹) * m⁻¹ := by rw [hmeq]
        _ = m * g * a * (g⁻¹ * m⁻¹) := by group
    calc (m * g) * a = ((m * g) * a * (m * g)⁻¹) * (m * g) := by group
      _ = a * (m * g) := by rw [← hkey]
  have hmgM : m * g ∈ M := hcen a ⟨haH, by simpa using ha1⟩ hcent
  have hg : g = m⁻¹ * (m * g) := by group
  rw [hg]
  exact mul_mem (inv_mem hm) hmgM

theorem isTIWithNormalizer_hallCoreOf_sdiff [Finite G] {M : Subgroup G}
    (hne : hallCoreOf M ≠ ⊥)
    (hfus : ∀ a ∈ coreFixedSet (hallCoreOf M) M, ∀ b ∈ coreFixedSet (hallCoreOf M) M,
      (∃ g : G, g⁻¹ * a * g = b) → ∃ m ∈ M, m⁻¹ * a * m = b)
    (hcen : ∀ h ∈ (hallCoreOf M : Set G) \ {1}, centralizer ({h} : Set G) ≤ M) :
    IsTIWithNormalizer ((hallCoreOf M : Set G) \ {1}) M := by
  obtain ⟨⟨x₀, hx₀⟩, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hx₀D : x₀ ∈ (hallCoreOf M : Set G) \ {1} := ⟨hx₀, by simpa using hx₀1⟩
  refine ⟨⟨x₀, hx₀D⟩, by simp, ?_, ?_⟩
  · refine le_antisymm (fun g hg => ?_) (fun l hl => ?_)
    · rw [Subgroup.mem_set_normalizer_iff] at hg
      exact mem_of_conj_mem_sdiff_hallCoreOf hfus hcen hx₀D ((hg x₀).1 hx₀D)
    · rw [Subgroup.mem_set_normalizer_iff]
      intro y
      refine ⟨fun hy => conj_mem_sdiff_hallCoreOf hl hy, fun hy => ?_⟩
      have := conj_mem_sdiff_hallCoreOf (inv_mem hl) hy
      simpa [mul_assoc] using this
  · intro g hg
    rw [Set.disjoint_left]
    rintro z hz ⟨y, hy, rfl⟩
    refine hg (mem_of_conj_mem_sdiff_hallCoreOf hfus hcen hy ?_)
    simpa [MulAut.conj] using hz

theorem conjSet_eq_image_conj (D : Set G) (g : G) : conjSet D g = MulAut.conj g⁻¹ '' D := by
  refine Set.image_congr' fun x => ?_
  simp [MulAut.conj]

theorem conjSet_eq_or_disjoint {D : Set G} {L : Subgroup G} (hTI : IsTIWithNormalizer D L)
    (g h : G) : conjSet D g = conjSet D h ∨ Disjoint (conjSet D g) (conjSet D h) := by
  by_cases hgh : g * h⁻¹ ∈ L
  · left
    have hD : MulAut.conj (g * h⁻¹) '' D = D := hTI.conj_image_eq_of_mem hgh
    have hcomp : ((MulAut.conj h⁻¹ : G ≃* G) : G → G)
        = (MulAut.conj g⁻¹ : G ≃* G) ∘ (MulAut.conj (g * h⁻¹) : G ≃* G) := by
      funext x
      simp only [Function.comp_apply, MulAut.conj_apply, mul_inv_rev, inv_inv]
      group
    rw [conjSet_eq_image_conj, conjSet_eq_image_conj, hcomp, Set.image_comp, hD]
  · right
    rw [conjSet_eq_image_conj, conjSet_eq_image_conj]
    refine hTI.disjoint_conj_image_conj_image ?_
    simpa using hgh

theorem relIndex_eq_natCard_of_isInternalSemidirectProduct [Finite G] {L H E : Subgroup G}
    (h : FreeCore.IsInternalSemidirectProduct L H E) : H.relIndex L = Nat.card ↥E := by
  have hc := isComplement'_subgroupOf_of_isInternalSemidirectProduct h
  rw [Subgroup.relIndex, hc.symm.index_eq_card]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.right_le).toEquiv

theorem coprime_natCard_hallCoreOf_complement [Finite G] {L E : Subgroup G}
    (h : FreeCore.IsInternalSemidirectProduct L (hallCoreOf L) E) :
    Nat.Coprime (Nat.card ↥(hallCoreOf L)) (Nat.card ↥E) := by
  rw [← relIndex_eq_natCard_of_isInternalSemidirectProduct h]
  exact coprime_natCard_relIndex_hallCoreOf L

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

universe u

theorem FPF_all_type_I_kernel_partition
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FPF_type_I_frobenius.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u}) :
    _root_.CFSG.FeitThompson.Statements.FPF_all_type_I_kernel_partition.{u} := by
  intro G _ _ hG hallI
  have hfin : Fintype G := Fintype.ofFinite G
  have hG05 : IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG06 : _root_.CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG09 : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hsimple := hG.isSimpleGroup
  have hallI06 : ∀ M ∈ _root_.CFSG.FeitThompson.Prep06.maximalSubgroups G,
      IsTypeI M := fun M hM => hallI M hM
  set L := coatomRep G
  have hLco : ∀ i, IsCoatom (L i) := fun i => isCoatom_coatomRep i
  have hsub : Set.range L ⊆
      _root_.CFSG.FeitThompson.Prep06.maximalSubgroups G := by
    rintro T ⟨i, rfl⟩; exact hLco i
  have htrans : ∀ M ∈ _root_.CFSG.FeitThompson.Prep06.maximalSubgroups G,
      ∃! T, T ∈ Set.range L ∧ ∃ g : G, Subgroup.map (MulAut.conj g : G ≃* G) M = T :=
    fun M hM => existsUnique_mem_range_coatomRep hM
  obtain ⟨-, hdisjD, hunion, hcop, -, hprime⟩ :=
    FTS_all_type_I_packet_cover h₁ h₂ h₃ h₄ h₅ h₆ G hG06 hallI06 (Set.range L) hsub htrans
  have hcc := FTS_all_type_I_core_centralizer_control h₂ h₆ G hG06 hallI06
  have hdelta : ∀ i, _root_.CFSG.FeitThompson.Prep06.sigDelta (L i)
      = conjClosure ((hallCoreOf (L i) : Set G) \ {1}) := fun i => (hcc (L i) (hLco i)).2
  have hfrob : ∀ i, ∃ E : Subgroup G, E ≤ L i ∧ E ≠ ⊥ ∧
      FreeCore.IsInternalSemidirectProduct (L i) (hallCoreOf (L i)) E ∧
      IsFixedPointFreeOn (hallCoreOf (L i)) E := fun i =>
    h₂ G hG05 (L i) (hLco i) (hallI (L i) (hLco i))
  have hSH : ∀ i, sigmaCore (L i) = hallCoreOf (L i) := fun i =>
    (h₆ G hG09 (L i) (hLco i) (hallI (L i) (hLco i))).1
  have hne : ∀ i, hallCoreOf (L i) ≠ ⊥ := fun i => hallCoreOf_ne_bot (hallI (L i) (hLco i))
  have hneD : ∀ i, ((hallCoreOf (L i) : Set G) \ {1}).Nonempty := by
    intro i
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (hne i)
    exact ⟨x, hx, by simpa using hx1⟩
  have hTI : ∀ i, IsTIWithNormalizer ((hallCoreOf (L i) : Set G) \ {1}) (L i) := fun i =>
    isTIWithNormalizer_hallCoreOf_sdiff (hne i)
      (h₆ G hG09 (L i) (hLco i) (hallI (L i) (hLco i))).2.2.1
      (fun h hh => ((hcc (L i) (hLco i)).1 h hh).1)
  have hcopH : ∀ i j, i ≠ j →
      Nat.Coprime (Nat.card ↥(hallCoreOf (L i))) (Nat.card ↥(hallCoreOf (L j))) := by
    intro i j hij
    have hne' : L i ≠ L j := fun hc => hij (coatomRep_injective hc)
    have hc := hcop (L i) ⟨i, rfl⟩ (L j) ⟨j, rfl⟩ hne'
    rwa [hSH i, hSH j] at hc
  have hk0 : 0 < Nat.card (Quotient (coatomConjSetoid G)) := by
    have : Nontrivial G := hsimple.toNontrivial
    exact zero_lt_card_quotient_coatomConjSetoid G
  have hk : 2 ≤ Nat.card (Quotient (coatomConjSetoid G)) := by
    by_contra hk2
    have hk1 : Nat.card (Quotient (coatomConjSetoid G)) = 1 := by omega
    set i₀ : Fin (Nat.card (Quotient (coatomConjSetoid G))) := ⟨0, by omega⟩
    obtain ⟨E, -, hEne, hsd, -⟩ := hfrob i₀
    obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEne
    have hEcard : Nat.card ↥E ≠ 1 := fun hc => he1 (by
      have : Subsingleton ↥E := (Nat.card_eq_one_iff_unique.1 hc).1
      exact Subsingleton.elim _ _)
    obtain ⟨r, hr, hrE⟩ := Nat.exists_prime_and_dvd hEcard
    have hrG : r ∣ Nat.card G := hrE.trans (Subgroup.card_subgroup_dvd_card E)
    obtain ⟨T, ⟨j, rfl⟩, hrT⟩ := hprime r (Nat.mem_primeFactors.2 ⟨hr, hrG, Nat.card_pos.ne'⟩)
    have hji : j = i₀ := Fin.ext (by have := j.2; omega)
    rw [hji, hSH i₀] at hrT
    exact hr.one_lt.ne'
      (Nat.eq_one_of_dvd_coprimes (coprime_natCard_hallCoreOf_complement hsd) hrT hrE)
  refine ⟨_, hk, L, hLco, fun M hM => existsUnique_isConjugateSubgroup_coatomRep hM, hne,
    hfrob, hTI, hcopH, ?_, ?_, ?_⟩
  ·
    intro i g
    obtain ⟨x, hx⟩ := hneD i
    exact ⟨g⁻¹ * x * g, x, hx, rfl⟩
  ·
    intro i j g h hne'
    by_cases hij : i = j
    · subst hij
      rcases conjSet_eq_or_disjoint (hTI i) g h with heq | hd
      · exact absurd heq hne'
      · exact hd
    · have hLij : L i ≠ L j := fun hc => hij (coatomRep_injective hc)
      have hd := hdisjD (L i) ⟨i, rfl⟩ (L j) ⟨j, rfl⟩ hLij
      rw [hdelta i, hdelta j] at hd
      rw [Set.disjoint_iff_inter_eq_empty]
      refine Set.eq_empty_of_subset_empty ?_
      rw [← hd]
      exact Set.inter_subset_inter (Set.subset_iUnion _ g) (Set.subset_iUnion _ h)
  ·
    rw [← hunion, Set.biUnion_range]
    exact Set.iUnion_congr fun i => (hdelta i).symm

end

end CFSG.FeitThompson.Proofs
