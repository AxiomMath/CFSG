module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Representations.TypeThreeFourScalarCoordinateIndexCollapse
import CFSG.FeitThompson.Representations.IndexCollapseSupport
import CFSG.FeitThompson.Representations.TypeIIIToVCoherenceFrobeniusPartner
public import CFSG.FeitThompson.Representations.PTypeChiefCoreFamilyCoherent
import CFSG.FeitThompson.OddOrder.NilpotentProperSubgroupNormalClosure
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsOfPGroups
import CFSG.FeitThompson.Local.PrimeCentralizerTransitiveHyperplanes
public import CFSG.FeitThompson.Representations.CyclicTIIsometryExistence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup CFSG.FeitThompson.Prep06

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

theorem isTypeIII_of_isCyclic {G : Type u} [Group G] [Finite G] (hG : IsMinimalOddSimple G)
    {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hcyc : IsCyclic ↥U) : IsTypeIII M := by
  rcases htype with h | h
  · exact h
  · exfalso
    obtain ⟨-, hnab, -⟩ := h.clauses_of_isWitnessedPConfiguration_of_minimalSimple
      hG.simple hG.nonabelian hG.odd hG.solvable hM hc
    exact hnab hcyc.isMulCommutative

theorem commutator_le_frattini_of_isNilpotent {P : Type*} [Group P] [Group.IsNilpotent P] :
    commutator P ≤ frattini P := by
  refine le_iInf₂ fun D hD => ?_
  have hD' : IsCoatom D := hD
  have := normal_of_isCoatom_of_isNilpotent hD'
  have := isSimpleGroup_quotient_of_isCoatom hD'
  have : IsCyclic (P ⧸ D) := inferInstance
  have hab : IsMulCommutative (P ⧸ D) := IsCyclic.isMulCommutative
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le).1 hab

theorem isCyclic_of_ker_le_commutator {P Q : Type*} [Group P] [Group Q] [Finite P]
    [Group.IsNilpotent P] (f : P →* Q) [IsCyclic f.range] (hker : f.ker ≤ commutator P) :
    IsCyclic P := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := f.range)
  obtain ⟨x, hx⟩ := g.2
  have hsup : zpowers x ⊔ frattini P = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hg ⟨f y, y, rfl⟩)
    have hmem : (x ^ k)⁻¹ * y ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hx]
      have := congrArg Subtype.val hk
      simp only [SubgroupClass.coe_zpow] at this
      rw [this, inv_mul_cancel]
    have hy : y = x ^ k * ((x ^ k)⁻¹ * y) := by group
    rw [hy]
    exact mul_mem (mem_sup_left (mem_zpowers_iff.2 ⟨k, rfl⟩))
      (mem_sup_right ((hker.trans commutator_le_frattini_of_isNilpotent) hmem))
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨x, frattini_nongenerating hsup⟩

theorem exists_pow_eq_conj_of_mem_normalizer {G : Type*} [Group G] {E : Subgroup G} [Finite E]
    [IsCyclic E] {x : G} (hx : x ∈ normalizer (E : Set G)) :
    ∃ m : ℕ, ∀ y ∈ E, x⁻¹ * y * x = y ^ m := by
  classical
  have _ : Fintype E := Fintype.ofFinite _
  let σ : E →* E :=
    { toFun := fun y => ⟨x⁻¹ * y * x, (mem_normalizer_iff''.1 hx y).1 y.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  obtain ⟨m, hm⟩ := σ.map_cyclic
  have hn : (0 : ℤ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  refine ⟨(m % Fintype.card E).toNat, fun y hy => ?_⟩
  have h1 := congrArg Subtype.val (hm ⟨y, hy⟩)
  have h2 := zpow_mod_card (⟨y, hy⟩ : E) m
  rw [← Int.toNat_of_nonneg (Int.emod_nonneg m hn.ne'), zpow_natCast] at h2
  rw [← h2] at h1
  simpa [σ] using h1

open scoped Classical in
theorem lt_and_one_lt_relIndex_and_dvd
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₄ : CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    {G : Type u} [Group G] [Fintype G] (hG : IsMinimalOddSimple G)
    {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    Nat.card W₂ < Nat.card W₁ ∧
      1 < (U ⊓ centralizer ((Prep06.hallCoreIn M : Subgroup G) : Set G)).relIndex U ∧
      Nat.card W₁ ∣ (U ⊓ centralizer ((Prep06.hallCoreIn M : Subgroup G) : Set G)).relIndex U - 1 := by
  have hodd := hG.odd
  have : Fintype ↑(Irr ↥(W₁.subgroupOf M)) := Fintype.ofFinite _
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  have : Fintype ↑(Irr ↥W₂) := Fintype.ofFinite _
  have h := hc.isPrimeCyclicTIHyp_subgroupOf hodd
  have hKn : (derivedOf M).Normal := h.normal
  obtain ⟨σ, hσ⟩ := h.exists_isCyclicTIIsometry
  set w : ↑(Irr ↥(W₁.subgroupOf M)) → ↑(Irr ↥(W₂.subgroupOf M)) →
      ↥(classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)) :=
    fun i j => h.isCyclicTIPair.basisProdIrr (i, j) with hw
  set l : ↑(Irr ↥(W₁.subgroupOf M)) → ↥M → ℂ := fun i => h.inflateLeft i with hl
  have hrowD : IsRowData M W₁ W₂ σ w l := by
    refine { isometry := hσ, prod := ?_, infl := ?_ }
    · intro i j x y z hz
      rw [hw, h.isCyclicTIPair.coe_basisProdIrr_apply]
      have h6 := h.isCyclicTIPair.prodChar_apply_mul (i : ↥(W₁.subgroupOf M) → ℂ)
        (j : ↥(W₂.subgroupOf M) → ℂ) x.2 y.2
      convert h6 using 2
      exact Subtype.ext hz
    · intro i k v z hz
      subst hz
      exact h.inflateLeft_apply_mul i k.2 v.2
  set sg : ↑(Irr ↥(W₂.subgroupOf M)) → ℂ := fun j => h.primeTISign σ j with hsg
  set mu : ↑(Irr ↥(W₁.subgroupOf M)) → ↑(Irr ↥(W₂.subgroupOf M)) → ↥M → ℂ :=
    fun i j => h.primeTIirr σ i j with hmu
  have hsetup : IsRowSetup M W₁ W₂ σ w l sg mu := by
    refine { toIsRowData := hrowD, sign := ?_, mu_zero_mem := ?_, mu_eq := ?_ }
    · intro j; exact h.primeTISign_eq_one_or_eq_neg_one j
    · intro j
      have h4 := h.primeTIirr_principal_left_mem_Irr hσ j
      rw [h.primeTIirr_principal_left] at h4
      exact h4
    · intro i j
      change h.primeTIirr σ i j = _
      rw [h.primeTIirr_eq_mul i j, h.primeTIirr_principal_left]
  have hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ := CrossedRowData.isCyclicTIPair_sup hodd hc
  obtain ⟨ω, hω⟩ := hW.exists_isCyclicTIIsometry
  have heta := isEtaSetup_basisProdIrr hW hω
  obtain ⟨-, hlt⟩ := CFSG.FeitThompson.Proofs.FPF_type_iii_iv_principal_row_projection h₁ h₂ h₃ h₄ h₅
    G hG M U W₁ W₂ hM htype hc σ w l sg mu hsetup ω _ _ heta
  obtain ⟨d', n', dsign, -, -, -, -, -, hdeg, hsign, hdn⟩ :=
    (CFSG.FeitThompson.Proofs.FPF_type_iii_v_local_character_constants h₅ G hG M U W₁ W₂ hM
      (by tauto) hc).2.2 σ w l sg mu hsetup
  obtain ⟨-, hu1, hqu, -⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_row_degree_and_kernel h₁ h₅ G hG M U W₁ W₂ hM htype hc
      σ w l sg mu hsetup d' n' dsign hdeg hsign hdn
  exact ⟨hlt, hu1, hqu⟩

set_option maxHeartbeats 1000000 in
theorem relIndex_centralizer_hallCoreIn_eq_of_isScalarCoreConfig
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₄ : CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    {G : Type u} [Group G] [Fintype G] (hG : IsMinimalOddSimple G)
    {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) {p : ℕ} {K : Subgroup ↥M} {A : Set ↥M}
    {Eline : ZMod (Nat.card W₁) →
      Subgroup (↥(hallCore ↥M) ⧸ (⊥ : Subgroup ↥M).subgroupOf (hallCore ↥M))}
    (hcfg : ScalarCoreCoherence.IsScalarCoreConfig p (Nat.card W₁) K (hallCore ↥M)
      (U.subgroupOf M) (W₁.subgroupOf M) ⊥ Eline A)
    (hp : p = Nat.card W₂) :
    (U ⊓ centralizer ((Prep06.hallCoreIn M : Subgroup G) : Set G)).relIndex U
      = (lineFixer (hallCore ↥M) ⊥ (U.subgroupOf M) (Eline 0)).relIndex (U.subgroupOf M) := by
  have hNZ : NeZero (Nat.card W₁) := ⟨Nat.card_pos.ne'⟩
  have hf := hallCoreQuotBotHom_injective M
  have hUM : U ≤ M := hc.le_M_E
  set f := hallCoreQuotBotHom M with hfdef
  set E : Fin (Nat.card W₁) → Subgroup G :=
    fun i => (Eline (ZMod.finEquiv _ i)).map f with hEdef
  have hEH : ∀ i, E i ≤ Prep06.hallCoreIn M := fun i =>
    (Subgroup.map_le_range f _).trans (range_hallCoreQuotBotHom M).le
  have hcomap : ∀ i, (E i).comap f = Eline (ZMod.finEquiv _ i) := fun i =>
    Subgroup.comap_map_eq_self_of_injective hf _
  have hnorm : ∀ i, U ≤ normalizer ((E i : Subgroup G) : Set G) := by
    intro i u hu
    rw [FreeCore.mem_normalizer_iff_map]
    have h1 := hcfg.map_U_Eline ⟨u, hUM hu⟩ (Subgroup.mem_subgroupOf.2 hu) (ZMod.finEquiv _ i)
    have h2 := congrArg (Subgroup.map f) h1
    rw [show ((conjQuotientAut (hallCore ↥M) ⊥ (⟨u, hUM hu⟩ : ↥M) : MulEquiv _ _) : _ →* _)
        = (conjQuotientAut (hallCore ↥M) ⊥ (⟨u, hUM hu⟩ : ↥M) : MulEquiv _ _).toMonoidHom
        from rfl, map_hallCoreQuotBotHom_map_conjQuotientAut] at h2
    exact h2
  obtain ⟨b', hb'B, hBgen, hbE⟩ := hcfg.exists_gen_B
  set a := (lineFixer (hallCore ↥M) ⊥ (U.subgroupOf M) (Eline 0)).relIndex (U.subgroupOf M)
  refine CFSG.FeitThompson.Proofs.FPF_type_iii_iv_scalar_coordinate_index_collapse h₁ h₂ h₃ h₄ h₅
    G hG M U W₁ W₂ hM htype hc E a ((b' : G))⁻¹ hEH ?_ ?_ ?_ hnorm ?_ ?_ ?_
    hcfg.one_lt_relIndex_lineFixer ?_
  · intro i
    rw [Subgroup.card_map_of_injective hf, hcfg.card_Eline, hp]
  · rw [← range_hallCoreQuotBotHom, MonoidHom.range_eq_map, ← hcfg.iSup_Eline,
      Subgroup.map_iSup]
    exact (ZMod.finEquiv (Nat.card W₁)).toEquiv.iSup_comp (g := fun j => (Eline j).map f)
  · intro i
    have hind := (hcfg.indep_Eline.comp (ZMod.finEquiv (Nat.card W₁)).injective)
    have hdisj := disjoint_iff.1 ((iSupIndep_def.1 hind) i)
    rw [hEdef]
    simp only
    rw [← map_biSup, ← Subgroup.map_inf_eq _ _ f hf]
    have h2 : Eline ((ZMod.finEquiv _) i) ⊓
        ⨆ j ∈ ({i}ᶜ : Set (Fin (Nat.card W₁))), Eline ((ZMod.finEquiv _) j) = ⊥ := hdisj
    rw [h2, Subgroup.map_bot]
  · refine ⟨inv_mem (Subgroup.mem_subgroupOf.1 hb'B), ?_⟩
    rw [Subgroup.zpowers_inv]
    have := MonoidHom.map_zpowers M.subtype b'
    rw [← hBgen, Subgroup.map_subgroupOf_eq_of_le hc.le_M_W₁] at this
    exact this.symm
  · intro i
    rw [inv_inv]
    have h1 := congrArg (Subgroup.map f) (hbE (ZMod.finEquiv _ i))
    rw [show ((conjQuotientAut (hallCore ↥M) ⊥ b' : MulEquiv _ _) : _ →* _)
        = (conjQuotientAut (hallCore ↥M) ⊥ b' : MulEquiv _ _).toMonoidHom
        from rfl, map_hallCoreQuotBotHom_map_conjQuotientAut] at h1
    have h3 : ZMod.finEquiv (Nat.card W₁) (i + 1) = ZMod.finEquiv (Nat.card W₁) i + 1 := by
      simp
    rw [hEdef]
    simp only
    rw [h3, ← h1]
    rfl
  · intro i x hx
    have _ : Fact (Nat.card W₂).Prime := ⟨hp ▸ hcfg.p_prime⟩
    have hcardE : Nat.card (E i) = Nat.card W₂ := by
      rw [Subgroup.card_map_of_injective hf, hcfg.card_Eline, hp]
    have _ : Finite (E i) := Nat.finite_of_card_ne_zero (by rw [hcardE]; exact Nat.card_pos.ne')
    have _ : IsCyclic (E i) := isCyclic_of_prime_card hcardE
    exact exists_pow_eq_conj_of_mem_normalizer (hnorm i hx)
  · intro i
    have h1 := lineFixer_comap_hallCoreQuotBotHom (U := U) (hEH i)
    rw [hcomap] at h1
    rw [← Subgroup.relIndex_subgroupOf hUM, ← h1, hcfg.relIndex_lineFixer_eq]

theorem isCyclic_of_isCyclic_factorLinearImage
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    {G : Type u} [Group G] [Fintype G] (hG : IsMinimalOddSimple G)
    {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) {p : ℕ} {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V]
    (e : (↥(hallCore ↥M) ⧸ (⊥ : Subgroup ↥M).subgroupOf (hallCore ↥M)) ≃* Multiplicative V)
    (hA : IsCyclic
      (ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) ⊥ (U.subgroupOf M) e)) :
    IsCyclic U := by
  classical
  have hUM : U ≤ M := hc.le_M_E
  have hnil : Group.IsNilpotent U := hc.isNilpotent_E
  set f : ↥U →* _ := (ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) ⊥ e).comp
    (Subgroup.inclusion hUM) with hf
  have hle : f.range ≤
      ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) ⊥ (U.subgroupOf M) e := by
    rintro _ ⟨x, rfl⟩
    exact ChiefFactorFaithfulImage.factorLinearAut_mem_factorLinearImage p e
      (Subgroup.mem_subgroupOf.2 x.2)
  have : IsCyclic f.range := Subgroup.isCyclic_of_le hle
  refine isCyclic_of_ker_le_commutator f ?_
  intro x hx
  rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply,
    ChiefFactorFaithfulImage.factorLinearAut_eq_one_iff, ← conjQuotientAut_eq_factorConjAut] at hx
  have hmem : Subgroup.inclusion hUM x ∈ chiefActionKer (hallCore ↥M) ⊥ (U.subgroupOf M) :=
    (mem_chiefActionKer_iff_mem_ker _ _ _).2 ⟨Subgroup.mem_subgroupOf.2 x.2, hx⟩
  rw [OrientedCoreFamily.chiefActionKer_bot] at hmem
  have hxG : (x : G) ∈ U ⊓ centralizer ((Prep06.hallCoreIn M : Subgroup G) : Set G) := by
    refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    obtain ⟨g', hg', rfl⟩ := hg
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hmem.2 g' hg')
  rw [(h₁ G hG M U W₁ W₂ hM htype hc).2.2.2.2.2.1] at hxG
  rw [commutator_eq_subgroupOf_commutator]
  exact Subgroup.mem_subgroupOf.2 hxG

private theorem cyclic_and_lt_residual
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₄ : CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
      ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
        IsWitnessedPConfiguration M U W₁ W₂ →
        IsCyclic ↥U ∧ Nat.card W₂ < Nat.card W₁ := by
  classical
  intro G _ _ hG M U W₁ W₂ hM htype hc
  obtain ⟨hlt, hu1, hqu⟩ := lt_and_one_lt_relIndex_and_dvd h₁ h₂ h₃ h₄ h₅ hG hM htype hc
  refine ⟨?_, hlt⟩
  have hcfg0 := isPtypeCoreConfig_bot_of_typeIII_IV h₁ h₃ h₅ hG hM htype hc
  have hsolv := hcfg0.isSolvable_M
  have hcfg := hcfg0.isPTypeConfig
  have hq : Nat.card (W₁.subgroupOf M) = Nat.card W₁ := natCard_subgroupOf_eq_of_le hc.le_M_W₁
  have hfq := Fact.mk (hq ▸ hcfg.prime_natCard_B : (Nat.card W₁).Prime)
  obtain ⟨b, hbB, hb1, hbgen⟩ := exists_zpowers_eq_of_prime_natCard hcfg.prime_natCard_B
  have hchief := hcfg0.isChiefFactor
  have hHn : (hallCore ↥M).Normal := hchief.normal_num
  have hCU := hcfg0.centralizer_le_H0
  have hs := hcfg.isFaithfulImageSetup hq hchief hCU hbB hb1
  obtain ⟨p, d, hp, -, ⟨e⟩⟩ :=
    ChiefFactorLinearAction.exists_prime_nonempty_mulEquiv_of_isChiefFactor hchief
  have hfp := Fact.mk hp
  have hdq : d = Nat.card W₁ := by
    have h := hs.finrank_eq p e hp
    rwa [Module.finrank_fin_fun] at h
  subst hdq
  obtain ⟨hD, hDA, hDb⟩ : ∃ D : PrimeDimLinearSetup p (Nat.card W₁)
      (Fin (Nat.card W₁) → ZMod p),
      D.A = ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) ⊥ (U.subgroupOf M) e ∧
        D.b = ChiefFactorFaithfulImage.factorLinearAut p (hallCore ↥M) ⊥ e b :=
    ⟨hcfg.linearModel hq hchief hCU hbB hb1 e,
      hcfg.linearModel_A hq hchief hCU hbB hb1 e, hcfg.linearModel_b hq hchief hCU hbB hb1 e⟩
  rcases hD.xor_actsReducibly_isIrreducible with ⟨hred, -⟩ | ⟨hirr, -⟩
  ·
    exfalso
    obtain ⟨Sys, hSysA, hSysb⟩ := hD.exists_scalarLineSystem hred
    have hscal := isScalarCoreConfig_of_scalarLineSystem hcfg hcfg0.odd_natCard_M hq hchief hCU
      hbB hb1 hbgen e Sys (by rw [hSysA, hDA]) (by rw [hSysb, hDb]) hcfg0.A_subset_subgroupOf
      hcfg0.A_invariant hcfg0.centralizer_subset_A_subgroupOf
    have hpW : p = Nat.card W₂ := by
      have hHcard : Nat.card (↥(hallCore ↥M) ⧸ (⊥ : Subgroup ↥M).subgroupOf (hallCore ↥M))
          = Nat.card (Prep06.hallCoreIn M) := by
        rw [← range_hallCoreQuotBotHom, MonoidHom.range_eq_map,
          Subgroup.card_map_of_injective (hallCoreQuotBotHom_injective M), Subgroup.card_top]
      have h1 := hscal.card_quotient
      rw [hHcard, (h₁ G hG M U W₁ W₂ hM htype hc).2.1] at h1
      exact (Nat.pow_left_injective hfq.out.ne_zero h1).symm
    have hueq := relIndex_centralizer_hallCoreIn_eq_of_isScalarCoreConfig h₁ h₂ h₃ h₄ h₅ hG hM
      htype hc hscal hpW
    have hadvd := hscal.relIndex_lineFixer_dvd_sub_one' 0
    rw [← hueq] at hadvd
    have hple := Nat.le_of_dvd (by have := hp.two_le; omega) hadvd
    have hqle := Nat.le_of_dvd (by omega) hqu
    omega
  ·
    have hab : IsMulCommutative
        (ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) ⊥ (U.subgroupOf M) e) :=
      hDA ▸ hD.isMulCommutative_A
    have hirr' : (linearGroupRep
        (ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) ⊥ (U.subgroupOf M) e)).IsIrreducible :=
      hDA ▸ hirr
    have hcyc : IsCyclic
        (ChiefFactorFaithfulImage.factorLinearImage p (hallCore ↥M) ⊥ (U.subgroupOf M) e) :=
      isCyclic_of_isMulCommutative_of_isIrreducible (p := p)
    exact isCyclic_of_isCyclic_factorLinearImage h₁ hG hM htype hc e hcyc

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson

universe u

theorem FPF_type_iii_iv_inner_complement_cyclic
    (h₁ : Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₂ : Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₃ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₄ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₅ : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_type_iii_iv_inner_complement_cyclic.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc
  obtain ⟨hcyc, hlt⟩ := cyclic_and_lt_residual h₁ h₂ h₃ h₄ h₅ G hG M U W₁ W₂ hM htype hc
  exact ⟨hcyc, hlt, isTypeIII_of_isCyclic hG hM htype hc hcyc⟩

end CFSG.FeitThompson.Proofs

end
