module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDTarget
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HeldLift
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingle

public section

namespace CFSG.ComponentClassification.GrSLit.HeDiag

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem ker_mulAut_conj (Q : Type*) [Group Q] :
    (MulAut.conj : Q →* MulAut Q).ker = center Q := by
  ext x
  rw [MonoidHom.mem_ker, mem_center_iff]
  constructor
  · intro h g
    have h1 := congrArg (fun φ : MulAut Q => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * x = x * g * x⁻¹ * x := by rw [h1]
      _ = x * g := by group
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h g, mul_inv_cancel_right]

omit [Finite X] in
theorem heldQuotConj_of_mem {K : Subgroup X} {k : X} (hk : k ∈ K) :
    GrS4.heldQuotConj K ⟨k, le_normalizer hk⟩ =
      MulAut.conj (((⟨k, hk⟩ : ↥K)) : ↥K ⧸ pPrimeCore 2 ↥K) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    change ((LocalAnalysis.ComponentInitial.normalizerConjHom K ⟨k, le_normalizer hk⟩ x : ↥K) :
      ↥K ⧸ pPrimeCore 2 ↥K) = _
    rw [MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1

omit [Finite X] in
theorem heldQuotConj_eq_one_iff {K : Subgroup X} (n : ↥(normalizer (K : Set X))) :
    GrS4.heldQuotConj K n = 1 ↔ (n : X) ∈ coreActionKernel K := by
  have hO : ∀ y : ↥K, (y : X) ∈ (pPrimeCore 2 ↥K).map K.subtype ↔ y ∈ pPrimeCore 2 ↥K :=
    fun y => ⟨fun ⟨z, hz, hzy⟩ => Subtype.ext hzy ▸ hz, fun h => ⟨y, h, rfl⟩⟩
  have hact : ∀ (m : ↥(normalizer (K : Set X))) (j : ↥K),
      GrS4.heldQuotConj K m (j : ↥K ⧸ pPrimeCore 2 ↥K) =
        ((⟨m * j * (m : X)⁻¹, (mem_normalizer_iff.mp m.2 j).mp j.2⟩ : ↥K) :
          ↥K ⧸ pPrimeCore 2 ↥K) := fun m j => rfl
  constructor
  · intro h
    refine mem_coreActionKernel.mpr ⟨n.2, fun j hj => ?_⟩
    have h1 : GrS4.heldQuotConj K n⁻¹ = 1 := by rw [map_inv, h, inv_one]
    have h2 := congrArg (fun φ => φ ((⟨j, hj⟩ : ↥K) : ↥K ⧸ pPrimeCore 2 ↥K)) h1
    simp only [MulAut.one_apply] at h2
    rw [hact, eq_comm, QuotientGroup.eq] at h2
    have h3 := (hO _).mpr h2
    convert h3 using 1
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    group
  · intro h
    ext q
    induction q using QuotientGroup.induction_on with
    | H j =>
      rw [hact, MulAut.one_apply, QuotientGroup.eq, ← hO]
      have hj' : (n : X) * j * (n : X)⁻¹ ∈ K := (mem_normalizer_iff.mp n.2 j).mp j.2
      have h1 := (mem_coreActionKernel.mp h).2 _ hj'
      convert h1 using 1
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group

theorem nonempty_equiv_held_of_surjective {L₀ I : Type}
    [Group L₀] [Finite L₀] [Group I] [Finite I] [hIs : IsSimpleGroup I]
    (hInab : ∃ x y : I, x * y ≠ y * x) (g : L₀ →* I) (hg : Function.Surjective g)
    (e : L₀ ⧸ pPrimeCore 2 L₀ ≃* Blueprint.NativeSporadic.He) :
    Nonempty (I ≃* Blueprint.NativeSporadic.He) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 L₀) with hπ
  have : IsSimpleGroup (L₀ ⧸ pPrimeCore 2 L₀) :=
    @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.He.isSimpleGroup_He e
  have hN₀ : g.ker ≤ pPrimeCore 2 L₀ := by
    have hnorm : (g.ker.map π).Normal :=
      (MonoidHom.normal_ker g).map π (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (g.ker.map π) with h | h
    · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
    · exfalso
      have hO : (pPrimeCore 2 L₀).map g = ⊤ := by
        refine eq_top_iff.mpr fun y _ => ?_
        obtain ⟨l, rfl⟩ := hg y
        have h1 : π l ∈ g.ker.map π := by rw [h]; exact mem_top _
        obtain ⟨n, hn, hnl⟩ := h1
        have h2 : n⁻¹ * l ∈ pPrimeCore 2 L₀ := by
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
          change (π n)⁻¹ * π l = 1
          rw [hnl, inv_mul_cancel]
        refine ⟨n⁻¹ * l, h2, ?_⟩
        rw [map_mul, map_inv, MonoidHom.mem_ker.mp hn, inv_one, one_mul]
      have hodd : Odd (Nat.card I) := by
        have h1 := card_map_dvd (pPrimeCore 2 L₀) g
        rw [hO, card_top] at h1
        exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h1
      obtain ⟨x, y, hxy⟩ := hInab
      exact hxy ((IsSimpleGroup.comm_iff_isSolvable).mpr (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd) x y)
  set φ : L₀ ⧸ g.ker →* L₀ ⧸ pPrimeCore 2 L₀ :=
    QuotientGroup.map g.ker (pPrimeCore 2 L₀) (MonoidHom.id _) (by simpa using hN₀) with hφ
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 L₀) q
    exact ⟨(l : L₀ ⧸ g.ker), rfl⟩
  let eL : L₀ ⧸ g.ker ≃* I := QuotientGroup.quotientKerEquivOfSurjective g hg
  have : IsSimpleGroup (L₀ ⧸ g.ker) := @MulEquiv.isSimpleGroup _ _ _ _ hIs eL
  have hφi : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨u, v, huv⟩ := exists_mul_ne_held
      apply huv
      obtain ⟨u', hu'⟩ := hφs (e.symm u)
      obtain ⟨v', hv'⟩ := hφs (e.symm v)
      have hu : φ u' = 1 := MonoidHom.mem_ker.mp (h ▸ mem_top u')
      have hv : φ v' = 1 := MonoidHom.mem_ker.mp (h ▸ mem_top v')
      rw [hu] at hu'
      rw [hv] at hv'
      rw [← e.apply_symm_apply u, ← e.apply_symm_apply v, ← hu', ← hv']
  exact ⟨(eL.symm.trans (MulEquiv.ofBijective φ ⟨hφi, hφs⟩)).trans e⟩

theorem exists_fixed_preimage {K : Subgroup X} {a : X} (haa : a * a = 1)
    (hKK' : ⁅K, conjugate K a⁆ ≤ oddIn K)
    (hK'NK : conjugate K a ≤ normalizer (K : Set X))
    (hK'ker : conjugate K a ≤ coreActionKernel K) (hOker : oddIn K ≤ coreActionKernel K)
    (k : ↥K) : ∃ c ∈ (K ⊔ conjugate K a) ⊓ centralizer ({a} : Set X),
      ∀ hc : c ∈ normalizer (K : Set X),
        GrS4.heldQuotConj K ⟨c, hc⟩ = MulAut.conj (k : ↥K ⧸ pPrimeCore 2 ↥K) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hk₂ : a * k * a⁻¹ ∈ conjugate K a := by
    rw [mem_conjugate_iff, hai]
    simpa only [mul_assoc, haa, mul_one, ← mul_assoc a a, one_mul] using k.2
  have h1 : ((k : X) * (a * k * a⁻¹))⁻¹ * (a * ((k : X) * (a * k * a⁻¹)) * a⁻¹) ∈
      (pPrimeCore 2 ↥K).map K.subtype := by
    have h2 : a * ((k : X) * (a * k * a⁻¹)) * a⁻¹ = a * k * a⁻¹ * k := by
      simp only [hai, mul_assoc, haa, mul_one]
    have h3 : ((k : X) * (a * k * a⁻¹))⁻¹ * (a * k * a⁻¹ * k) =
        ⁅(a * k * a⁻¹)⁻¹, (k : X)⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    have h4 : ⁅(a * k * a⁻¹)⁻¹, (k : X)⁻¹⁆ ∈ ⁅K, conjugate K a⁆ := by
      rw [Subgroup.commutator_comm]
      exact commutator_mem_commutator (inv_mem hk₂) (inv_mem k.2)
    rw [h2, h3]
    exact hKK' h4
  obtain ⟨o, ho, hco⟩ := GrS4.exists_commute_mul_mem (odd_card_map_pPrimeCore K) haa h1
  have hoK : o ∈ K := map_subtype_le _ ho
  refine ⟨(k : X) * (a * k * a⁻¹) * o, mem_inf.mpr ⟨mul_mem (mul_mem (mem_sup_left k.2)
    (mem_sup_right hk₂)) (mem_sup_left hoK), mem_centralizer_singleton_iff.mpr hco.symm⟩,
    fun hc => ?_⟩
  have h5 : (⟨(k : X) * (a * k * a⁻¹) * o, hc⟩ : ↥(normalizer (K : Set X))) =
      ⟨k, le_normalizer k.2⟩ * ⟨a * k * a⁻¹, hK'NK hk₂⟩ * ⟨o, le_normalizer hoK⟩ := rfl
  rw [h5, map_mul, map_mul, heldQuotConj_of_mem k.2,
    (heldQuotConj_eq_one_iff ⟨_, hK'NK hk₂⟩).mpr (hK'ker hk₂),
    (heldQuotConj_eq_one_iff ⟨o, le_normalizer hoK⟩).mpr (hOker ho), mul_one, mul_one]

omit [Finite X] in
theorem heldQuotConj_mem_range {K K' : Subgroup X} (hK'NK : K' ≤ normalizer (K : Set X))
    (hK'ker : K' ≤ coreActionKernel K) {y : X} (hy : y ∈ K ⊔ K')
    (hyN : y ∈ normalizer (K : Set X)) :
    GrS4.heldQuotConj K ⟨y, hyN⟩ ∈ (MulAut.conj : ↥K ⧸ pPrimeCore 2 ↥K →* _).range := by
  have hy' : y ∈ ((K ⊔ K' : Subgroup X) : Set X) := hy
  rw [coe_mul_of_right_le_normalizer_left K K' hK'NK] at hy'
  obtain ⟨k, hk, k', hk', rfl⟩ := hy'
  have h1 : (⟨k * k', hyN⟩ : ↥(normalizer (K : Set X))) =
      ⟨k, le_normalizer hk⟩ * ⟨k', hK'NK hk'⟩ := rfl
  rw [h1, map_mul, heldQuotConj_of_mem hk,
    (heldQuotConj_eq_one_iff ⟨k', hK'NK hk'⟩).mpr (hK'ker hk'), mul_one]
  exact ⟨_, rfl⟩

theorem held_equiv_of_moved (hMult : TBLit.HeldTrivialMultiplier)
    {M K L : Subgroup X} {a : X} (ha : orderOf a = 2) (haM : a ∈ M) (hKM : K ≤ M)
    (hKc : IsPComponent 2 (K.subgroupOf M)) (hKa : conjugate K a ≠ K)
    (hLa : L ≤ centralizer ({a} : Set X))
    (hLca : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X))))
    (hLKK : L ≤ K ⊔ conjugate K a)
    (hLc : IsPComponent 2 (L.subgroupOf ((K ⊔ conjugate K a) ⊓ centralizer ({a} : Set X))))
    (e : L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) :
    Nonempty (K ⧸ pPrimeCore 2 K ≃* Blueprint.NativeSporadic.He) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hK'M : conjugate K a ≤ M := conjugate_le_of_mem hKM haM
  have hK'c : IsPComponent 2 ((conjugate K a).subgroupOf M) :=
    isPComponent_conjugate_subgroupOf haM hKc
  have hne : K ≠ conjugate K a := fun h => hKa h.symm
  have hKK' : ⁅K, conjugate K a⁆ ≤ oddIn K ⊓ oddIn (conjugate K a) :=
    GrS5.commutator_le_inf_oddIn hKM hK'M hKc hK'c hne
  have hK'NK : conjugate K a ≤ normalizer (K : Set X) :=
    (GrS5.commutator_le_of_ne hKM hK'M hKc hK'c hne).2
  have hK'ker : conjugate K a ≤ coreActionKernel K := by
    intro y hy
    refine mem_coreActionKernel.mpr ⟨hK'NK hy, fun j hj => ?_⟩
    have h1 := (mem_inf.mp (hKK' (commutator_mem_commutator (inv_mem hj) (inv_mem hy)))).1
    rwa [commutatorElement_def, inv_inv, inv_inv] at h1
  have hOker : oddIn K ≤ coreActionKernel K := by
    intro o ho
    have hoK : o ∈ K := map_subtype_le _ ho
    refine mem_coreActionKernel.mpr ⟨le_normalizer hoK, fun j hj => ?_⟩
    have h1 := GrS4.conj_mem_oddIn_of_mem_normalizer (le_normalizer (inv_mem hj)) (inv_mem ho)
    rw [inv_inv] at h1
    exact mul_mem h1 ho
  have hNK : K ⊔ conjugate K a ≤ normalizer (K : Set X) := sup_le le_normalizer hK'NK
  obtain ⟨-, -, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K M hKM).mp hKc
  let eI : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃*
      ↥(MulAut.conj : ↥K ⧸ pPrimeCore 2 ↥K →* _).range :=
    (QuotientGroup.quotientMulEquivOfEq (ker_mulAut_conj _).symm).trans
      (QuotientGroup.quotientKerEquivRange _)
  have hIs : IsSimpleGroup ↥(MulAut.conj : ↥K ⧸ pPrimeCore 2 ↥K →* _).range :=
    @MulEquiv.isSimpleGroup _ _ _ _ hq.2.1 eI.symm
  have hInab : ∃ x y : ↥(MulAut.conj : ↥K ⧸ pPrimeCore 2 ↥K →* _).range, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hq.2.2
    exact ⟨eI x, eI y, fun h => hxy (eI.injective (by rw [map_mul, map_mul, h]))⟩
  have hLC : L ≤ (K ⊔ conjugate K a) ⊓ centralizer ({a} : Set X) := le_inf hLKK hLa
  have hCN : (K ⊔ conjugate K a) ⊓ centralizer ({a} : Set X) ≤ normalizer (K : Set X) :=
    inf_le_left.trans hNK
  let g := ((GrS4.heldQuotConj K).comp (inclusion hCN)).codRestrict
    (MulAut.conj : ↥K ⧸ pPrimeCore 2 ↥K →* _).range
    (fun c => heldQuotConj_mem_range hK'NK hK'ker (mem_inf.mp c.2).1 (hCN c.2))
  have hgs : Function.Surjective g := by
    rintro ⟨_, q, rfl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) q
    obtain ⟨c, hc, hcq⟩ := exists_fixed_preimage haa (hKK'.trans inf_le_left) hK'NK hK'ker hOker k
    exact ⟨⟨c, hc⟩, Subtype.ext (hcq (hCN hc))⟩
  have hsub : (L.subgroupOf ((K ⊔ conjugate K a) ⊓ centralizer ({a} : Set X))).IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L _ hLC).mp hLc).1
  have hLM : L ≤ M := hLKK.trans (sup_le hKM hK'M)
  have hLnot : ¬ L ≤ coreActionKernel K := fun h =>
    Single.not_le_coreActionKernel_of_diagonal hLa hLca hLM hKM hK'M (hLKK.trans hNK)
      (hLKK.trans (sup_le (GrS5.commutator_le_of_ne hK'M hKM hK'c hKc hne.symm).2
        le_normalizer))
      (GSLit.map_pPrimeCore_le_of_isPComponent hKM hKc)
      (GSLit.map_pPrimeCore_le_of_isPComponent hK'M hK'c) (hLKK.trans le_sup_left) haa
      (Or.inl h)
  have hLg : (L.subgroupOf ((K ⊔ conjugate K a) ⊓ centralizer ({a} : Set X))).map g = ⊤ := by
    rcases (hsub.map hgs).eq_bot_or_top_of_isSimpleGroup hIs with h | h
    · exfalso
      apply hLnot
      intro l hl
      have h1 : g ⟨l, hLC hl⟩ ∈
          (L.subgroupOf ((K ⊔ conjugate K a) ⊓ centralizer ({a} : Set X))).map g :=
        mem_map_of_mem _ hl
      rw [h, mem_bot] at h1
      have h2 : GrS4.heldQuotConj K ⟨l, hCN (hLC hl)⟩ = 1 := congrArg Subtype.val h1
      exact (heldQuotConj_eq_one_iff _).mp h2
    · exact h
  have hgLs : Function.Surjective (g.comp (inclusion hLC)) := by
    intro y
    have hy : y ∈ (L.subgroupOf ((K ⊔ conjugate K a) ⊓ centralizer ({a} : Set X))).map g := by
      rw [hLg]; exact mem_top y
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨⟨c, hc⟩, rfl⟩
  obtain ⟨eIHe⟩ := nonempty_equiv_held_of_surjective hInab _ hgLs e
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_fusionZStar ↥K
  exact held_equiv_of_isPComponent hMult hKM hKc ⟨eZ.symm.trans (eI.trans eIHe)⟩

end CFSG.ComponentClassification.GrSLit.HeDiag
