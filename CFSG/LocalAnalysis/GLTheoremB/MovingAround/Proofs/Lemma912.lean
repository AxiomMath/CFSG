module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911TypeProof
public import CFSG.LocalAnalysis.GLTheoremB.Input20_1Proof
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CatalogSchreier
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBInputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

namespace Lemma912

section AlphaStar

variable {G : Type} [Group G] [Finite G]

@[expose] def JPredStar (p : ℕ) (M J : Subgroup G) : Prop :=
  p = 3 ∧ J ≤ M ∧ IsSubnormal J M ∧ ⁅J, J⁆ = J ∧
    Nonempty ((↥J ⧸ CFSG.pCore 2 ↥J) ≃* alternatingGroup (Fin 7))

omit [Finite G] in
theorem alphaStarOf_le (p : ℕ) (M : Subgroup G) : alphaStarOf p M ≤ M :=
  sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 M) (iSup₂_le fun _ hJ => hJ.2.1)

omit [Finite G] in
theorem JPredStar.gLBConj {p : ℕ} {M J : Subgroup G} (h : JPredStar p M J) {g : G} (hg : g ∈ M) :
    JPredStar p M (GLBConj g J) := by
  obtain ⟨hp3, hJM, hsn, hperf, hA7⟩ := h
  have hgn : g ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer hg
  have hM : GLBConj g M = M := mem_normalizer_iff_gLBConj_eq.1 hgn
  refine ⟨hp3, ?_, ?_, ?_, ?_⟩
  · calc GLBConj g J ≤ GLBConj g M := Subgroup.map_mono hJM
      _ = M := hM
  · have := isSubnormal_gLBConj hsn g
    rwa [hM] at this
  · have h1 := Subgroup.map_commutator (H₁ := J) (H₂ := J) (MulAut.conj g⁻¹).toMonoidHom
    change GLBConj g ⁅J, J⁆ = ⁅GLBConj g J, GLBConj g J⁆ at h1
    rw [← h1, hperf]
  · obtain ⟨f⟩ := hA7
    have hpc : (CFSG.pCore 2 ↥J).map (conjEquiv g J).toMonoidHom =
        CFSG.pCore 2 ↥(GLBConj g J) :=
      CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (conjEquiv g J)
    exact ⟨(QuotientGroup.congr _ _ (conjEquiv g J) hpc).symm.trans f⟩

omit [Finite G] in
theorem le_normalizer_alphaStarOf (p : ℕ) (M : Subgroup G) :
    M ≤ Subgroup.normalizer (alphaStarOf p M : Set G) := by
  have key : ∀ g ∈ M, GLBConj g (alphaStarOf p M) ≤ alphaStarOf p M := by
    intro g hg
    have hgn : g ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer hg
    have hM : GLBConj g M = M := mem_normalizer_iff_gLBConj_eq.1 hgn
    unfold alphaStarOf
    simp only [GLBConj, Subgroup.map_sup, Subgroup.map_iSup]
    refine sup_le_sup ?_ ?_
    · have := le_normalizer_pCoreOf 2 M hg
      exact (mem_normalizer_iff_gLBConj_eq.1 this).le
    · refine iSup₂_le fun J hJ => ?_
      obtain ⟨hp3, hJM, hsn, hperf, hA7⟩ := hJ
      refine le_iSup₂_of_le (GLBConj g J) ⟨hp3, ?_, ?_, ?_, ?_⟩ le_rfl
      · calc GLBConj g J ≤ GLBConj g M := Subgroup.map_mono hJM
          _ = M := hM
      · have := isSubnormal_gLBConj hsn g
        rwa [hM] at this
      · have h1 := Subgroup.map_commutator (H₁ := J) (H₂ := J) (MulAut.conj g⁻¹).toMonoidHom
        change GLBConj g ⁅J, J⁆ = ⁅GLBConj g J, GLBConj g J⁆ at h1
        rw [← h1, hperf]
      · obtain ⟨f⟩ := hA7
        have hpc : (CFSG.pCore 2 ↥J).map (conjEquiv g J).toMonoidHom =
            CFSG.pCore 2 ↥(GLBConj g J) :=
          CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (conjEquiv g J)
        exact ⟨(QuotientGroup.congr _ _ (conjEquiv g J) hpc).symm.trans f⟩
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (key g hg) ?_
  have h2 := gLBConj_mono g (key g⁻¹ (inv_mem hg))
  rwa [gLBConj_gLBConj_inv] at h2

theorem alt7_isQuasisimple : CFSG.Open.IsQuasisimple ↥(alternatingGroup (Fin 7)) := by
  have h5 : 5 ≤ Nat.card (Fin 7) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have h4 : 4 ≤ Nat.card (Fin 7) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  refine ⟨commutator_alternatingGroup_eq_top h5, ?_⟩
  have hc : Subgroup.center ↥(alternatingGroup (Fin 7)) = ⊥ :=
    alternatingGroup.center_eq_bot h4
  exact (((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup_congr).2
    S7.isSimple_Alt7

end AlphaStar

section Statements

@[expose] def Lemma912S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B M : Subgroup G, IsBOneMax p B → IsPreUniquenessTwoLocal p B M → p = 3 →
      ∀ b ∈ B, b ≠ 1 → ∀ J : Subgroup G,
        IsTwoPrimeComp (alphaStarOf p M ⊓ Subgroup.centralizer ({b} : Set G)) J →
          ∃ S : Subgroup G, IsPGroup 2 S ∧ B ≤ Subgroup.normalizer (S : Set G) ∧
            S ≤ bConjJoin B J ∧ bConjJoin B J ≤ ⨆ j ∈ bConjJoin B J, GLBConj j S

end Statements

section Main

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem lemma912TypeWeak :
    ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
      ∀ B M : Subgroup G, IsBOneMax p B → IsPreUniquenessTwoLocal p B M → p = 3 →
        ∀ b ∈ B, b ≠ 1 → ∀ J : Subgroup G,
          IsTwoPrimeComp (alphaStarOf p M ⊓ Subgroup.centralizer ({b} : Set G)) J →
            Nonempty (((↥J ⧸ CFSG.pCore 2 ↥J) ⧸ Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) ≃*
              ↥(alternatingGroup (Fin 7))) := by
  intro G _ _ m p hSt B M hB hM hp3 b hb hb1 J hJX
  have hp := hSt.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set X := alphaStarOf p M ⊓ C with hX
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hSt hB hM
  have hbM : b ∈ M := hBM hb
  have hb3 : b ^ 3 = 1 := by
    have := hB.1.1.2 b hb
    rwa [hp3] at this
  have hJle : J ≤ X := hJX.1
  have hJM : J ≤ M := hJle.trans (inf_le_left.trans (alphaStarOf_le p M))
  have hXM : X ≤ M := inf_le_left.trans (alphaStarOf_le p M)
  set N : Subgroup ↥M := CFSG.pCore 2 ↥M with hN
  set π : ↥M →* ↥M ⧸ N := QuotientGroup.mk' N with hπ
  have hNcard : IsPGroup 2 ↥N := by
    rw [hN]
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hNG : (pCoreOf 2 M).subgroupOf M = N := by
    show (Subgroup.map M.subtype (CFSG.Open.pCore 2 ↥M)).comap M.subtype = N
    rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective, hN]
  set ℒ : Set (Subgroup (↥M ⧸ N)) :=
    (fun J' : Subgroup G => (J'.subgroupOf M).map π) '' {J' | JPredStar p M J'} with hℒ
  have hLdata : LData ℒ := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨J', hJ', rfl⟩
      obtain ⟨hp3', hJ'M, hsn, hperf, hhat⟩ := hJ'
      refine ⟨le_top, ?_, ?_⟩
      · have h1 := isSubnormal_comap' M.subtype hsn
        rw [show M.comap M.subtype = ⊤ from Subgroup.subgroupOf_self M] at h1
        have h2 := isSubnormal_map' π h1
        rwa [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N)] at h2
      · have e1 := quotEquivTwoImage hJ'M hsn
        obtain ⟨f⟩ := hhat
        have hq : CFSG.Open.IsQuasisimple (↥J' ⧸ CFSG.pCore 2 ↥J') :=
          CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv f.symm alt7_isQuasisimple
        exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e1 hq
    · rintro _ ⟨J', hJ', rfl⟩
      obtain ⟨hp3', hJ'M, hsn, hperf, hhat⟩ := hJ'
      exact nonempty_quot_center_alt7_of_equiv (quotEquivTwoImage hJ'M hsn) (Or.inl hhat)
  set bt : ↥M ⧸ N := π ⟨b, hbM⟩ with hbt
  have hbt3 : bt ^ 3 = 1 := by
    rw [hbt, ← map_pow]
    have : (⟨b, hbM⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [this, map_one]
  have hbℒ : ∀ L ∈ ℒ, L.map (MulAut.conj bt).toMonoidHom ∈ ℒ := by
    rintro _ ⟨J', hJ', rfl⟩
    refine ⟨GLBConj b⁻¹ J', JPredStar.gLBConj hJ' (M.inv_mem hbM), ?_⟩
    show ((GLBConj b⁻¹ J').subgroupOf M).map π = ((J'.subgroupOf M).map π).map _
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : b⁻¹ * (y : G) * b⁻¹⁻¹ ∈ J' := (mem_gLBConj).1 ((Subgroup.mem_subgroupOf).1 hy)
      refine ⟨π ⟨b⁻¹ * (y : G) * b⁻¹⁻¹, M.mul_mem (M.mul_mem (M.inv_mem hbM) y.2)
        (M.inv_mem (M.inv_mem hbM))⟩, ⟨_, (Subgroup.mem_subgroupOf).2 hy', rfl⟩, ?_⟩
      show bt * π ⟨b⁻¹ * (y : G) * b⁻¹⁻¹, _⟩ * bt⁻¹ = π y
      rw [hbt, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show b * (b⁻¹ * (y : G) * b⁻¹⁻¹) * b⁻¹ = y
      group
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      have hw' : (w : G) ∈ J' := (Subgroup.mem_subgroupOf).1 hw
      refine ⟨⟨b * (w : G) * b⁻¹, M.mul_mem (M.mul_mem hbM w.2) (M.inv_mem hbM)⟩, ?_, ?_⟩
      · refine (Subgroup.mem_subgroupOf).2 ((mem_gLBConj).2 ?_)
        have : b⁻¹ * (b * (w : G) * b⁻¹) * b⁻¹⁻¹ = w := by group
        rw [this]
        exact hw'
      · show π ⟨b * (w : G) * b⁻¹, _⟩ = bt * π w * bt⁻¹
        rw [hbt, ← map_inv, ← map_mul, ← map_mul]
        try rfl
  have hαℒ : ((alphaStarOf p M).subgroupOf M).map π ≤ sSup ℒ := by
    have hα : alphaStarOf p M = pCoreOf 2 M ⊔ ⨆ x : {J' : Subgroup G // JPredStar p M J'}, x.1 := by
      unfold alphaStarOf
      rw [iSup_subtype']
      try rfl
    have hle1 : (⨆ x : {J' : Subgroup G // JPredStar p M J'}, x.1) ≤ M :=
      iSup_le fun x => x.2.2.1
    have hle2 : pCoreOf 2 M ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
    rw [hα, Subgroup.subgroupOf_sup hle2 hle1, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [hNG]
      exact (QuotientGroup.map_mk'_self N).le.trans bot_le
    · refine le_trans (Subgroup.map_mono (subgroupOf_iSup_le _ fun x => x.2.2.1)) ?_
      rw [Subgroup.map_iSup]
      exact iSup_le fun x => le_sSup ⟨x.1, x.2, rfl⟩
  set ι : ↥J →* ↥M ⧸ N := π.comp (Subgroup.inclusion hJM) with hι
  have hιr : ι.range = (J.subgroupOf M).map π := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j, hJM j.2⟩, (Subgroup.mem_subgroupOf).2 j.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, (Subgroup.mem_subgroupOf).1 hy⟩, rfl⟩
  have hJα : J ≤ alphaStarOf p M := hJle.trans inf_le_left
  have hιE : ι.range ≤ sSup ℒ := by
    rw [hιr]
    refine le_trans (Subgroup.map_mono ?_) hαℒ
    intro y hy
    exact hJα ((Subgroup.mem_subgroupOf).1 hy)
  have hιb : ι.range ≤ Subgroup.centralizer ({bt} : Set (↥M ⧸ N)) := by
    rw [hιr]
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hbt, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hyJ : (y : G) ∈ J := (Subgroup.mem_subgroupOf).1 hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (hJle hyJ).2
  have hℒα : sSup ℒ ≤ ((alphaStarOf p M).subgroupOf M).map π := by
    refine sSup_le ?_
    rintro _ ⟨J', hJ', rfl⟩
    refine Subgroup.map_mono ?_
    intro w hw
    have hw' : (w : G) ∈ J' := (Subgroup.mem_subgroupOf).1 hw
    refine (Subgroup.mem_subgroupOf).2 ?_
    have : J' ≤ alphaStarOf p M := by
      unfold alphaStarOf
      exact le_sup_of_le_right (le_iSup₂_of_le J' hJ' le_rfl)
    exact this hw'
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian' hB.1.1
  have hbz : IsPGroup p (Subgroup.zpowers b) := hBp.to_le ((Subgroup.zpowers_le).2 hb)
  have hVp : ¬ p ∣ Nat.card (pCoreOf 2 M) := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).exists_card_eq
    rw [hk]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1
      (Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hSt.ne_two))
  have hlift : sSup ℒ ⊓ Subgroup.centralizer ({bt} : Set (↥M ⧸ N)) = (X.subgroupOf M).map π := by
    refine le_antisymm ?_ ?_
    · rintro z ⟨hzE, hzC⟩
      obtain ⟨y, hy, rfl⟩ := hℒα hzE
      have hyα : (y : G) ∈ alphaStarOf p M := (Subgroup.mem_subgroupOf).1 hy
      have hcomm : π y * bt = bt * π y := Subgroup.mem_centralizer_singleton_iff.1 hzC
      have hc0 : π (⟨b, hbM⟩ * y * ⟨b, hbM⟩⁻¹ * y⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hbt]
        have : bt * π y = π y * bt := hcomm.symm
        rw [this]
        group
      have hc0N : (⟨b, hbM⟩ * y * ⟨b, hbM⟩⁻¹ * y⁻¹ : ↥M) ∈ N := (QuotientGroup.eq_one_iff _).1 hc0
      rw [← hNG] at hc0N
      have hc0V : b * (y : G) * b⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 M := (Subgroup.mem_subgroupOf).1 hc0N
      obtain ⟨v, hv, hxv⟩ := exists_mul_mem_centralizer (p := p) (d := b) (x := (y : G))
        (V := pCoreOf 2 M) hbz hVp (le_normalizer_pCoreOf 2 M hbM)
        (le_normalizer_pCoreOf 2 M y.2) hc0V
      have hvM : v ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hv
      have hVα : pCoreOf 2 M ≤ alphaStarOf p M := by
        unfold alphaStarOf
        exact le_sup_left
      have hyvX : (y : G) * v ∈ X :=
        ⟨(alphaStarOf p M).mul_mem hyα (hVα hv), hxv⟩
      refine ⟨⟨(y : G) * v, M.mul_mem y.2 hvM⟩, (Subgroup.mem_subgroupOf).2 hyvX, ?_⟩
      have hvN : (⟨v, hvM⟩ : ↥M) ∈ N := by
        rw [← hNG]
        exact (Subgroup.mem_subgroupOf).2 hv
      have : (⟨(y : G) * v, M.mul_mem y.2 hvM⟩ : ↥M) = y * ⟨v, hvM⟩ := Subtype.ext rfl
      have hπv : π ⟨v, hvM⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hvN
      rw [this, map_mul, hπv, mul_one]
    · rintro _ ⟨y, hy, rfl⟩
      have hyX : (y : G) ∈ X := (Subgroup.mem_subgroupOf).1 hy
      refine ⟨hαℒ ⟨y, (Subgroup.mem_subgroupOf).2 hyX.1, rfl⟩, ?_⟩
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rw [hbt, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 hyX.2
  have hperf : commutator ↥J = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hJX.2.2.1)
  have hO2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥J) := by
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hker : ι.ker ≤ CFSG.pCore 2 ↥J := by
    intro j hj
    have hj1 : π ⟨(j : G), hJM j.2⟩ = 1 := hj
    have hjN : (⟨(j : G), hJM j.2⟩ : ↥M) ∈ N := (QuotientGroup.eq_one_iff _).1 hj1
    rw [← hNG] at hjN
    have hjP : (j : G) ∈ pCoreOf 2 M := (Subgroup.mem_subgroupOf).1 hjN
    rw [mem_pCore_two_iff]
    have := pCoreOf_inf_le (r := 2) M J ⟨hjP, j.2⟩
    rwa [inf_eq_right.2 hJM] at this
  have hq : CFSG.Open.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivTwoImage hJle hJX.2.1).symm hJX.2.2.2.2.2
  have hsn : IsSubnormal ι.range (sSup ℒ ⊓ Subgroup.centralizer ({bt} : Set (↥M ⧸ N))) := by
    rw [hιr, hlift]
    exact isSubnormal_map' π (isSubnormal_comap' M.subtype hJX.2.1)
  exact hLdata.exists_equiv_alt7 hbt3 hbℒ ι hιE hιb hsn hperf (CFSG.pCore 2 ↥J) hO2 hker hq

theorem lemma912S_of_typeWeak : Lemma912S := by
  have hT := lemma912TypeWeak
  intro G _ _ m p hSt B M hB hM hp3 b hb hb1 J hJX
  have hp := hSt.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set X := alphaStarOf p M ⊓ C with hX
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hSt hB hM
  have hBC : B ≤ C := le_centralizer_of_mem hB.1.1 hb
  have hH₀X : M ⊓ C ≤ Subgroup.normalizer (X : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_gLBConj_eq, hX, gLBConj_inf,
      mem_normalizer_iff_gLBConj_eq.1 (le_normalizer_alphaStarOf p M hg.1),
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg.2)]
  have hBX : B ≤ Subgroup.normalizer (X : Set G) := fun x hx => hH₀X ⟨hBM hx, hBC hx⟩
  have hJle : J ≤ X := hJX.1
  have hJ3 := hT G m p hSt B M hB hM hp3 b hb hb1 J hJX
  set N : Subgroup ↥X := CFSG.pCore 2 ↥X with hN
  have hchar : N.Characteristic := by
    rw [hN]
    exact CFSG.LieType.BorelTits.pCore_characteristic 2
  have hN2 : IsPGroup 2 ↥N := by
    rw [hN]
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  let ρ : ↥B →* MulAut ↥X := X.normalizerMonoidHom.comp (Subgroup.inclusion hBX)
  have hρ : ∀ (x : ↥B) (q : ↥X), (((ρ x) q : ↥X) : G) = (x : G) * q * (x : G)⁻¹ := fun x q =>
    X.normalizerMonoidHom_apply_apply_coe (Subgroup.inclusion hBX x) q
  have hρN : ∀ x : ↥B, N.map (ρ x).toMonoidHom = N := fun x =>
    Subgroup.characteristic_iff_map_eq.1 hchar (ρ x)
  have hΓ : IsPGroup 3 ↥B := hp3 ▸ isPGroup_of_isElemAbelian' hB.1.1
  set Jq : Subgroup ↥X := J.subgroupOf X with hJq
  have hJp : ⁅Jq, Jq⁆ = Jq := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, hJq, Subgroup.map_subgroupOf_eq_of_le hJle]
    exact hJX.2.2.1
  have hA7 : Nonempty ((↥(Jq.map (QuotientGroup.mk' N)) ⧸
      Subgroup.center ↥(Jq.map (QuotientGroup.mk' N))) ≃* ↥(alternatingGroup (Fin 7))) :=
    nonempty_quot_center_alt7_transport (quotEquivTwoImage hJle hJX.2.1) hJ3
  obtain ⟨SQ, hSQ2, hSQJ, hSQinv, hSQgen⟩ :=
    exists_invariant_two_subgroup_of_quot hΓ ρ N hN2 hρN hJp hJX.2.2.2 hA7
  set JstQ : Subgroup ↥X := ⨆ x : ↥B, Jq.map (ρ x).toMonoidHom with hJstQ
  have hmapJ : ∀ x : ↥B, (Jq.map (ρ x).toMonoidHom).map X.subtype = GLBConj ((x : G)⁻¹) J := by
    intro x
    ext z
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      rw [mem_gLBConj]
      have hq' : (q : G) ∈ J := (Subgroup.mem_subgroupOf).1 hq
      show (x : G)⁻¹ * (((ρ x) q : ↥X) : G) * (x : G)⁻¹⁻¹ ∈ J
      rw [hρ]
      have : (x : G)⁻¹ * ((x : G) * (q : G) * (x : G)⁻¹) * (x : G)⁻¹⁻¹ = (q : G) := by group
      rw [this]
      exact hq'
    · intro hz
      rw [mem_gLBConj] at hz
      have hzX : (x : G)⁻¹ * z * (x : G)⁻¹⁻¹ ∈ X := hJle hz
      have hzX' : z ∈ X := by
        have := (Subgroup.mem_normalizer_iff.1 (hBX x.2) ((x : G)⁻¹ * z * (x : G)⁻¹⁻¹)).1 hzX
        simpa [mul_assoc] using this
      refine ⟨ρ x ⟨(x : G)⁻¹ * z * (x : G)⁻¹⁻¹, hzX⟩, ⟨⟨(x : G)⁻¹ * z * (x : G)⁻¹⁻¹, hzX⟩,
        (Subgroup.mem_subgroupOf).2 hz, rfl⟩, ?_⟩
      show (((ρ x) ⟨(x : G)⁻¹ * z * (x : G)⁻¹⁻¹, hzX⟩ : ↥X) : G) = z
      rw [hρ]
      group
  have hJst : JstQ.map X.subtype = bConjJoin B J := by
    rw [hJstQ, Subgroup.map_iSup]
    refine le_antisymm (iSup_le fun x => ?_) ?_
    · rw [hmapJ]
      exact le_iSup₂_of_le ((x : G)⁻¹) (B.inv_mem x.2) le_rfl
    · refine iSup₂_le fun g hg => ?_
      refine le_iSup_of_le ⟨g⁻¹, B.inv_mem hg⟩ ?_
      rw [hmapJ]
      show GLBConj g J ≤ GLBConj ((g⁻¹ : G)⁻¹) J
      rw [inv_inv]
  refine ⟨SQ.map X.subtype, hSQ2.map _, ?_, ?_, ?_⟩
  ·
    have key : ∀ g ∈ B, ∀ z ∈ SQ.map X.subtype, g * z * g⁻¹ ∈ SQ.map X.subtype := by
      rintro g hg _ ⟨sq, hsq, rfl⟩
      refine ⟨ρ ⟨g, hg⟩ sq, hSQinv ⟨g, hg⟩ ⟨sq, hsq, rfl⟩, ?_⟩
      show (((ρ ⟨g, hg⟩) sq : ↥X) : G) = g * (sq : G) * g⁻¹
      rw [hρ]
    intro g hg
    refine Subgroup.mem_normalizer_iff.2 fun z => ⟨key g hg z, fun hz => ?_⟩
    have := key g⁻¹ (B.inv_mem hg) _ hz
    simpa [mul_assoc] using this
  · rw [← hJst]
    exact Subgroup.map_mono hSQJ
  · rw [← hJst]
    refine (Subgroup.map_mono hSQgen).trans ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun y => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hy => ?_
    have hyJ : (y : G) ∈ JstQ.map X.subtype := ⟨y, hy, rfl⟩
    refine le_trans ?_ (le_iSup₂_of_le ((y : G)⁻¹) ((JstQ.map X.subtype).inv_mem hyJ) le_rfl)
    rintro _ ⟨_, ⟨sq, hsq, rfl⟩, rfl⟩
    show (y : G) * (sq : G) * (y : G)⁻¹ ∈ GLBConj ((y : G)⁻¹) (SQ.map X.subtype)
    rw [mem_gLBConj]
    have : (y : G)⁻¹ * ((y : G) * (sq : G) * (y : G)⁻¹) * (y : G)⁻¹⁻¹ = (sq : G) := by group
    rw [this]
    exact ⟨sq, hsq, rfl⟩

theorem lemma912S_proved : Lemma912S := lemma912S_of_typeWeak

theorem lemma912_of_S (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hS : Lemma912S)
    (i20 : Input20_1) (i11 : Input11_6) (l23 : Lemma23) : Lemma912 := by
  intro G _ _ m p hSt B M hB hM hp3 b hb hb1 J hJX
  have hp := hSt.prime
  have hp2 := hSt.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have := hSt.simple
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set X := alphaStarOf p M ⊓ C with hX
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hSt hB hM
  have hBC : B ≤ C := le_centralizer_of_mem hB.1.1 hb
  have hCtop : C ≠ ⊤ := centralizer_singleton_ne_top hSt hb1
  have hXC : X ≤ C := inf_le_right
  set H₀ := M ⊓ C with hH₀
  have hXH₀ : X ≤ H₀ := inf_le_inf_right C (alphaStarOf_le p M)
  have hH₀X : H₀ ≤ Subgroup.normalizer (X : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_gLBConj_eq, hX, gLBConj_inf,
      mem_normalizer_iff_gLBConj_eq.1 (le_normalizer_alphaStarOf p M hg.1),
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg.2)]
  have hBX : B ≤ Subgroup.normalizer (X : Set G) := fun x hx => hH₀X ⟨hBM hx, hBC hx⟩
  have hJH₀ : IsSubnormal J H₀ :=
    isSubnormal_trans' hJX.2.1 (IsSubnormal.step hXH₀
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hXH₀).2 hH₀X) (IsSubnormal.refl H₀))
  obtain ⟨S, hS2, hBS, hSJ, hJS⟩ := hS G m p hSt B M hB hM hp3 b hb hb1 J hJX
  set Js := bConjJoin B J with hJs
  have hJsC : Js ≤ C := (bConjJoin_le hBX hJX.1).trans hXC
  have hSC : S ≤ C := hSJ.trans hJsC
  have hJsperf : ⁅Js, Js⁆ = Js := bConjJoin_perfect hJX.2.2.1
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hπ
  have hQcore : GLAPPrimeCore p (↥C ⧸ GLAPPrimeCore p ↥C) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hQ : CFSG.Open.IsKGroup (↥C ⧸ GLAPPrimeCore p ↥C) :=
    isKGroup_quotient' (isKGroup_of_isKProper hSt.kProper hCtop) _
  have hOut : ∀ K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C), IsComponentOf K ⊤ →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) :=
    fun K hK => outer_solvable_of_component hSch hQ hK
  obtain ⟨hSF, hSN⟩ := barX_two_subgroup_props i20 i11 l23 hSt hB hCtop hBC hSC hS2 hBS
  have hYperf : ⁅barX p C Js, barX p C Js⁆ = barX p C Js := barX_perfect p hJsC hJsperf
  have hYS : barX p C Js ≤ ⨆ y ∈ barX p C Js, GLBConj y (barX p C S) :=
    (barX_mono p hJS).trans (barX_iSup_conj_le p hJsC hSC)
  have hYN : ∀ K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C), IsComponentOf K ⊤ →
      barX p C Js ≤ Subgroup.normalizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := fun K hK =>
    le_of_le_iSup_conj (F := fun K' => Subgroup.normalizer (K' : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
      (fun g K' => gLBConj_normalizer g K') hYS
      (fun y _ => hSN _ (isComponentOf_gLBConj hK y⁻¹))
  have : (CFSG.Open.pCore p (↥C ⧸ GLAPPrimeCore p ↥C)).Normal :=
    CFSG.LieType.BorelTits.pCore_normal p
  have hYF : barX p C Js ≤ Subgroup.centralizer
      (CFSG.Open.pCore p (↥C ⧸ GLAPPrimeCore p ↥C) : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    le_of_le_iSup_conj
      (F := fun K' => Subgroup.centralizer (K' : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
      (fun g K' => gLBConj_centralizer g K') hYS
      (fun y _ => by rw [gLBConj_eq_of_normal]; exact hSF)
  have hYE : barX p C Js ≤ CFSG.ComponentClassification.Layer.subgroup
      (↥C ⧸ GLAPPrimeCore p ↥C) :=
    le_layer_of_perfect hp hQcore hOut hYperf hYF hYN
  have hB' : IsSCp p ⊤ (B.subgroupOf C) := isSCp_subgroupOf (l23 G m p hSt B hB) hBC
  have hrank : GLATwoLocalRank p ↥C ≤ CFSG.Open.pRank p (B.subgroupOf C) := by
    refine (glaTwoLocalRank_subgroup_le hp.one_lt C).trans ?_
    rw [hSt.rank_eq]
    refine CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB'.2.1 ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv, hSt.card_eq hB]
  set 𝒦 : Set (Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) := {K | ∃ L : Subgroup G,
    GLAPComponent p C L ∧ IsStronglyLocallyOneBalanced p B b L ∧ barX p C L = K} with h𝒦
  have h𝒦c : ∀ K ∈ 𝒦, IsComponentOf K ⊤ := by
    rintro _ ⟨L, hL, -, rfl⟩
    exact hL.2.2.1
  have hSK : ∀ K ∈ 𝒦, barX p C S ≤
      Subgroup.centralizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    rintro _ ⟨L, hL, hbal, rfl⟩
    have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
      le_normalizer_of_input11_6 i11 hSt.kProper hp hp2 hCtop hBC hSC (l23 G m p hSt B hB)
        hrank hS2 hBS hL
    have hcomm : ⁅L, S⁆ ≤ GLAPPrimeCoreOf p L :=
      hbal S (le_inf hSL hSC) (coprime_card_of_isPGroup_two hp hp2 hS2)
        (fun g hg => hBS hg.1)
    refine barX_le_centralizer fun s hs t ht _ _ => ?_
    have h3 : s * t * s⁻¹ * t⁻¹ ∈ ⁅S, L⁆ := Subgroup.commutator_mem_commutator hs ht
    rw [Subgroup.commutator_comm] at h3
    exact glaPPrimeCoreOf_le_of_isSubnormal hp hL.2.1 (hcomm h3)
  have hYK : ∀ K ∈ 𝒦, barX p C Js ≤
      Subgroup.centralizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    intro K hK
    refine le_of_le_iSup_conj
      (F := fun K' => Subgroup.centralizer (K' : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
      (fun g K' => gLBConj_centralizer g K') hYS (fun y hy => ?_)
    have hyn : y⁻¹ ∈ Subgroup.normalizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
      Subgroup.inv_mem _ (hYN K (h𝒦c K hK) hy)
    rw [mem_normalizer_iff_gLBConj_eq.1 hyn]
    exact hSK K hK
  have hYΛ := le_layer_diff_of_perfect 𝒦 h𝒦c hYperf hYE hYK
  have hlam : lambdaOf p B b ≤ M := lambdaOf_le_of_isPreUniquenessTwoLocal hM hb hb1
  have hΛ' : (⨆ K ∈ {K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C) | IsComponentOf K ⊤ ∧ K ∉ 𝒦}, K) ≤
      barX p C H₀ := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq C hK.1
    have hbal : ¬ IsStronglyLocallyOneBalanced p B b L := fun h => hK.2 ⟨L, hL, h, rfl⟩
    have hLM : L ≤ M := (le_sSup ⟨hL, hbal⟩ : L ≤ lambdaOf p B b).trans hlam
    exact barX_mono p (le_inf hLM hL.1)
  have hJbar : IsSubnormal (barX p C J) ⊤ :=
    isSubnormal_trans'
      (isSubnormal_of_le_of_le (isSubnormal_barX p hJH₀)
        ((barX_mono p (le_bConjJoin B J)).trans hYΛ) hΛ')
      (isSubnormal_iSup_components _ (fun K hK => hK.1))
  set P : Subgroup G := ((barX p C J).comap π).map C.subtype with hP
  have hPC : IsSubnormal P C := isSubnormal_preimage_barX p hJbar
  have hJP : J ≤ P := by
    intro j hj
    have hjC : j ∈ C := hXC (hJX.1 hj)
    exact ⟨⟨j, hjC⟩, ⟨⟨j, hjC⟩, (Subgroup.mem_subgroupOf).2 hj, rfl⟩, rfl⟩
  have hPH₀ : P ≤ H₀ := by
    rintro _ ⟨c, ⟨c', hc', hcc'⟩, rfl⟩
    have hker : c'⁻¹ * c ∈ GLAPPrimeCore p ↥C := QuotientGroup.eq.1 hcc'
    have hK0M : ((c'⁻¹ * c : ↥C) : G) ∈ M := lemma91_i hSt hB hM hb ⟨_, hker, rfl⟩
    have hc'M : (c' : G) ∈ M := alphaStarOf_le p M (hJX.1 ((Subgroup.mem_subgroupOf).1 hc')).1
    refine ⟨?_, c.2⟩
    have : (c : G) = (c' : G) * ((c'⁻¹ * c : ↥C) : G) := by simp
    rw [Subgroup.coe_subtype, this]
    exact M.mul_mem hc'M hK0M
  have hJC : IsSubnormal J C :=
    isSubnormal_trans' (isSubnormal_of_le_of_le hJH₀ hJP hPH₀) hPC
  exact isTwoPrimeComp_of_le hJX hXC hJC

end Main

end Lemma912

theorem lemma912_of_inputs (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (i11 : Input11_6) :
    Lemma912Statement :=
  Lemma912.lemma912_of_S hSch Lemma912.lemma912S_proved input20_1_proved i11 lemma23_proved

section Certified

theorem lemma912_certified (i11 : Input11_6) : Lemma912Statement :=
  lemma912_of_inputs CFSG.AGLEmbedding.kFactCatalogSchreier i11

end Certified

section Holds

theorem lemma912_holds
    : Lemma912Statement :=
  lemma912_certified CFSG.HardMathSupport.Timmesfeld.Coordinator.input11_6_holds

end Holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
