module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnClause

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

set_option linter.unusedSectionVars false


@[expose] def TwE6ConnFixed (n : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀)
    (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) → S.D.Φ = twistHom TwistTag.E6 L Fr →
    ((3 : ℕ) : L) ≠ 0 → 3 ∣ S.D.q + 1 → S.D.q ≠ 2 →
    ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
    (kernelRoots (rootCharHom a)).ncard = n →
    ∀ x ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)),
      S.D.step x = x → ∃ t, S.D.step t = t ∧ (∀ s ∈ torusGroup Tag.E6 L, s * t = t * s) ∧
        ∃ r ∈ ⨆ (i : KernelComponent (rootCharHom a))
          (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
            rationalComponent S.ρ S.Γ (rootCharHom a) i, x = t * r

section Core

variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem step_eq_of_mem_Γ (S : LangSetup Tag.E6 L p₀) {x : ModGL Tag.E6 L} (hx : x ∈ S.Γ) :
    S.D.step x = x := by
  have hΓ : S.Γ ≤ S.D.model := by
    refine Subgroup.commutator_le.2 fun g hg h hh => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  exact (S.D.mem_model.1 (hΓ hx)).2

theorem mem_adjointGroup_of_mem_Γ (S : LangSetup Tag.E6 L p₀) {x : ModGL Tag.E6 L}
    (hx : x ∈ S.Γ) : x ∈ adjointGroup Tag.E6 L := by
  have hΓ : S.Γ ≤ S.D.model := by
    refine Subgroup.commutator_le.2 fun g hg h hh => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  exact (S.D.mem_model.1 (hΓ hx)).1

theorem rationalComponent_le_Γ (S : LangSetup Tag.E6 L p₀) {a : Fin Tag.E6.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ S.Γ := by
  have h : ⁅rationalSpan S.ρ S.Γ (rootCharHom a) i, rationalSpan S.ρ S.Γ (rootCharHom a) i⁆ ≤
      rationalSpan S.ρ S.Γ (rootCharHom a) i := by
    refine Subgroup.commutator_le.2 fun g hg h hh => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  exact h.trans inf_le_right

theorem langGen_of_fixed {N : Set ℕ}
    (hN : ∀ n ∈ N, TwE6ConnFixed n) (hNsub : ∀ n ∈ N, n = 22 ∨ n = 30 ∨ n = 40)
    (S : LangSetup Tag.E6 L p₀) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr) (h3 : ((3 : ℕ) : L) ≠ 0) (h3q : 3 ∣ S.D.q + 1)
    (hq2 : S.D.q ≠ 2) {a b : Fin Tag.E6.rank → Lˣ} (haT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ 3 = 1) (hk : (kernelRoots (rootCharHom a)).ncard ∈ N) :
    S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} ≤
      (⨆ (i : KernelComponent (rootCharHom a))
        (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
          rationalComponent S.ρ S.Γ (rootCharHom a) i) ⊔
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} ⊓
          Subgroup.centralizer {rootDiagUnit Tag.E6 b}) := by
  intro x hx
  obtain ⟨hxΓ, hxa⟩ := Subgroup.mem_inf.1 hx
  have hstab := e6_stab_le_kernelReflectionGroup_of_conn a hap (by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact hNsub _ hk)
  have hxM : x ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := by
    have h1 : x ∈ toralCentralizer Tag.E6 L a :=
      Subgroup.mem_inf.2 ⟨mem_adjointGroup_of_mem_Γ S hxΓ, hxa⟩
    rw [toralCentralizer_eq_toralRootGroup_of_stabilizer_le Tag.E6 L a hstab] at h1
    exact h1
  have hxF := step_eq_of_mem_Γ S hxΓ
  obtain ⟨t, htF, htc, r, hr, hxt⟩ := hN _ hk L p₀ S Fr hFr hΦ h3 h3q hq2 a haT hap
    (by rfl) x hxM hxF
  have hrΓ : r ∈ S.Γ := by
    have hle : (⨆ (i : KernelComponent (rootCharHom a))
        (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
          rationalComponent S.ρ S.Γ (rootCharHom a) i) ≤ S.Γ :=
      iSup₂_le fun i _ => rationalComponent_le_Γ S i
    exact hle hr
  have htΓ : t ∈ S.Γ := by
    have : t = x * r⁻¹ := by rw [hxt]; group
    rw [this]
    exact mul_mem hxΓ (inv_mem hrΓ)
  have hta : t ∈ Subgroup.centralizer ({rootDiagUnit Tag.E6 a} : Set (ModGL Tag.E6 L)) :=
    Subgroup.mem_centralizer_singleton_iff.2 (htc _ (rootDiagUnit_mem_torusGroup a)).symm
  have htb : t ∈ Subgroup.centralizer ({rootDiagUnit Tag.E6 b} : Set (ModGL Tag.E6 L)) :=
    Subgroup.mem_centralizer_singleton_iff.2 (htc _ (rootDiagUnit_mem_torusGroup b)).symm
  rw [hxt]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_inf.2
    ⟨Subgroup.mem_inf.2 ⟨htΓ, hta⟩, htb⟩)) (Subgroup.mem_sup_left hr)

end Core

section Final

open CFSG.LieType.Seitz


theorem twE6_fixedPoints_le_of_fixed {N : Set ℕ} (hN : ∀ n ∈ N, TwE6ConnFixed n)
    (hNsub : ∀ n ∈ N, n = 22 ∨ n = 30 ∨ n = 40) {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} {q : ℕ} {E : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hcube : TwE6Cube K σ q E) {f : MulAut (twistedE6RootGroup K σ)} (hfE : f ∈ E) (hf1 : f ≠ 1)
    {h : twistedE6InndiagGL K σ} (hh : twistedE6InndiagConj K σ h = f)
    (hdim : ∃ n ∈ N, twE6MatFixDim K σ h = 6 + n) {e : MulAut (twistedE6RootGroup K σ)}
    (heE : e ∈ E) (hne : e ∉ Subgroup.zpowers f) :
    fixedPoints (Subgroup.zpowers f) ≤
      sSup {J | CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))} ⊔
        fixedPoints (Subgroup.zpowers f ⊔ Subgroup.zpowers e) := by
  classical
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega) hcube.three_dvd
    omega
  have hf3 : f ^ 3 = 1 := hcube.elemAbelian.2 f hfE
  have hinj := twE6_conj_injective K σ q hcube.frob hcube.card_field hq2
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hf1 (hh.symm.trans (map_one _))
  have hh3 : h ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hh, map_one]
    exact hf3
  have he1 : e ≠ 1 := fun h' => hne (h' ▸ one_mem _)
  obtain ⟨h', hh', -, hh'3⟩ := exists_matrix_lift_of_mem K σ q hcube.frob hcube.card_field hq2
    hcube.elemAbelian hcube.le_inndiag heE he1
  have hcomm : h * h' = h' * h := by
    apply hinj
    rw [map_mul, map_mul, hh, hh']
    exact congrArg Subtype.val (hcube.elemAbelian.1.is_comm.comm ⟨f, hfE⟩ ⟨e, heE⟩)
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨hp, ff, hf, hqf⟩ := prime_ringChar_and_eq_pow_of_card_sq K q hcube.card_field hq2
  have hK' : Nat.card K = (ringChar K ^ ff) ^ 2 := by rw [← hqf]; exact hcube.card_field
  have hσ' : ∀ c, σ c = c ^ (ringChar K ^ ff) := by intro c; rw [← hqf]; exact hcube.frob c
  have hpℓ : 3 ≠ ringChar K := fun h' => hcube.char_ne_three h'.symm
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hp hf Nat.prime_three (by norm_num) hpℓ
  have hdim3 : twE6MatFixDim K σ h = 28 ∨ twE6MatFixDim K σ h = 36 ∨
      twE6MatFixDim K σ h = 46 := by
    obtain ⟨n, hn, hn'⟩ := hdim
    rcases hNsub n hn with rfl | rfl | rfl <;> omega
  obtain ⟨S, a, b, ι, Fr, hDq, hFr, hΦ, haT, hbT, hap, hbp, ha1, hinjι, hrange, hca, hcb, hker⟩ :=
    exists_langSetup_pair_of_inndiag_twE6 hp hf hK' σ hσ' hcube.char_ne_three hp₀ hp₀ℓ hq₀ h h'
      hcomm hh3 hh'3 hh1 hdim3
  have hL3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne hp Nat.prime_three hK' hpℓ
  have h3q' : 3 ∣ S.D.q + 1 := by rw [hDq, ← hqf]; exact hcube.three_dvd
  have hFr' : ∀ c, Fr c = c ^ S.D.q := fun c => by rw [hDq]; exact hFr c
  have hk : (kernelRoots (rootCharHom a)).ncard ∈ N := by
    obtain ⟨n, hn, hn'⟩ := hdim
    have : (kernelRoots (rootCharHom a)).ncard = n := by omega
    rwa [this]
  have hq2' : S.D.q ≠ 2 := by rw [hDq, ← hqf]; exact hcube.ne_two
  have hcore := langGen_of_fixed hN hNsub S Fr hFr' hΦ hL3 h3q' hq2' haT hap hk (b := b)
  have hcompfix : (fixedPoints (Subgroup.zpowers f)).map ι =
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} := by
    rw [← hh, ← fixSubgroup_eq_fixedPoints, map_fixSubgroup_eq_of_conj ι hinjι _ _ hca, hrange]
  have hcomp : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      CFSG.Open.IsComponentOf ((rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι)
        (fixedPoints (Subgroup.zpowers f)) := by
    intro i hq
    have hCd : S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} ≤ ι.range := fun x hx => by
      rw [hrange]
      exact (Subgroup.mem_inf.1 hx).1
    have hcomapfix : (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}).comap ι =
        fixedPoints (Subgroup.zpowers f) := by
      rw [← hcompfix]
      exact Subgroup.comap_map_eq_self_of_injective hinjι _
    have hcompR : CFSG.Open.IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}) := by
      obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S haT i
      exact ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub, open_isQuasisimple hq⟩
    have := isComponentOf_comap_of_injective ι hinjι (hcompR.1.trans hCd) hCd hcompR
    rwa [hcomapfix] at this
  set comps : Subgroup (twistedE6RootGroup K σ) :=
    sSup {J | CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))} with hcomps
  have hA : (⨆ (i : KernelComponent (rootCharHom a))
        (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
          rationalComponent S.ρ S.Γ (rootCharHom a) i) ≤ comps.map ι := by
    refine iSup₂_le fun i hi => ?_
    have hRle : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ ι.range := by
      rw [hrange]
      exact rationalComponent_le_Γ S i
    calc rationalComponent S.ρ S.Γ (rootCharHom a) i =
        ((rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι).map ι :=
          (Subgroup.map_comap_eq_self hRle).symm
      _ ≤ comps.map ι := Subgroup.map_mono (le_sSup (hcomp i hi))
  have hB : S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} ⊓
      Subgroup.centralizer {rootDiagUnit Tag.E6 b} ≤
        (fixedPoints (Subgroup.zpowers f ⊔ Subgroup.zpowers e)).map ι := by
    intro y hy
    obtain ⟨hyΓa, hyb⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨hyΓ, hya⟩ := Subgroup.mem_inf.1 hyΓa
    rw [← hrange] at hyΓ
    obtain ⟨c, rfl⟩ := hyΓ
    refine ⟨c, ?_, rfl⟩
    have hfc : f c = c := by
      apply hinjι
      rw [← hh, hca c]
      have := Subgroup.mem_centralizer_singleton_iff.1 hya
      rw [← this]
      group
    have hec : e c = c := by
      apply hinjι
      rw [← hh', hcb c]
      have := Subgroup.mem_centralizer_singleton_iff.1 hyb
      rw [← this]
      group
    rw [SetLike.mem_coe, mem_fixedPoints]
    intro φ hφ
    have hle : Subgroup.zpowers f ⊔ Subgroup.zpowers e ≤
        MulAction.stabilizer (MulAut (twistedE6RootGroup K σ)) c :=
      sup_le (Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hfc))
        (Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hec))
    exact MulAction.mem_stabilizer_iff.1 (hle hφ)
  intro c hc
  have hic : ι c ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} := by
    rw [← hcompfix]
    exact ⟨c, hc, rfl⟩
  have h1 := hcore hic
  have h2 : ι c ∈ (comps ⊔ fixedPoints (Subgroup.zpowers f ⊔ Subgroup.zpowers e)).map ι := by
    rw [Subgroup.map_sup]
    exact (sup_le_sup hA hB) h1
  obtain ⟨c', hc', hcc'⟩ := h2
  rw [hinjι hcc'] at hc'
  exact hc'

theorem twE6LineGenAt_of_fixed {N : Set ℕ} (hN : ∀ n ∈ N, TwE6ConnFixed n)
    (hNsub : ∀ n ∈ N, n = 22 ∨ n = 30 ∨ n = 40) {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} {q : ℕ} {E : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hcube : TwE6Cube K σ q E) {f : MulAut (twistedE6RootGroup K σ)} (hfE : f ∈ E) (hf1 : f ≠ 1)
    {h : twistedE6InndiagGL K σ} (hh : twistedE6InndiagConj K σ h = f)
    (hdim : ∃ n ∈ N, twE6MatFixDim K σ h = 6 + n) : TwE6LineGenAt K σ E f := by
  obtain ⟨e, heE, hne⟩ := exists_mem_not_mem_zpowers (E := E) hcube.card_E
    (hcube.elemAbelian.2 f hfE)
  refine (twE6_fixedPoints_le_of_fixed hN hNsub hcube hfE hf1 hh hdim heE hne).trans
    (sup_le_sup_left ?_ _)
  exact le_iSup₂_of_le (f := fun (F : Subgroup (MulAut (twistedE6RootGroup K σ)))
      (_ : F ≤ E ∧ F.relIndex E = 3 ∧ f ∈ F) => fixedPoints F)
    (Subgroup.zpowers f ⊔ Subgroup.zpowers e)
    ⟨sup_le (Subgroup.zpowers_le.2 hfE) (Subgroup.zpowers_le.2 heE),
      relIndex_zpowers_sup_zpowers hcube.elemAbelian hcube.card_E hfE heE hf1 hne,
      Subgroup.mem_sup_left (Subgroup.mem_zpowers f)⟩ le_rfl

end Final

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
