module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma911ATL
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911SWeak
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Tools

variable {G : Type*} [Group G]

omit [Group G] in
theorem subgroupOf_iSup_le {ι : Sort*} [Group G] {M : Subgroup G} (K : ι → Subgroup G)
    (hK : ∀ i, K i ≤ M) : (⨆ i, K i).subgroupOf M ≤ ⨆ i, (K i).subgroupOf M := by
  have hle : (⨆ i, K i) ≤ M := iSup_le hK
  rw [← Subgroup.map_le_map_iff_of_injective M.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_iSup]
  exact iSup_mono fun i => (Subgroup.map_subgroupOf_eq_of_le (hK i)).ge

@[expose] def JPred (p : ℕ) (M J : Subgroup G) : Prop :=
  p = 3 ∧ J ≤ M ∧ IsSubnormal J M ∧ ⁅J, J⁆ = J ∧ IsHatSeven (↥J ⧸ CFSG.pCore 2 ↥J)

omit [Group G] in
theorem JPred.gLBConj [Group G] {p : ℕ} {M J : Subgroup G} (h : JPred p M J) {g : G} (hg : g ∈ M) :
    JPred p M (GLBConj g J) := by
  obtain ⟨hp3, hJM, hsn, hperf, hhat⟩ := h
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
  · have hpc : (CFSG.pCore 2 ↥J).map (conjEquiv g J).toMonoidHom =
        CFSG.pCore 2 ↥(GLBConj g J) := by
      exact CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (conjEquiv g J)
    exact IsHatSeven.of_mulEquiv (QuotientGroup.congr _ _ (conjEquiv g J) hpc) hhat

end Tools

section Main

variable {G : Type} [Group G] [Finite G]

theorem lemma911TypeWeak : Lemma911TypeWeak := by
  intro G _ _ m p hSt B M hB hM hp3 b hb hb1 J hJX
  have hp := hSt.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set X := alphaOf p M ⊓ C with hX
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hSt hB hM
  have hbM : b ∈ M := hBM hb
  have hb3 : b ^ 3 = 1 := by
    have := hB.1.1.2 b hb
    rwa [hp3] at this
  have hJle : J ≤ X := hJX.1
  have hJM : J ≤ M := hJle.trans (inf_le_left.trans (alphaOf_le p M))
  have hXM : X ≤ M := inf_le_left.trans (alphaOf_le p M)
  set N : Subgroup ↥M := CFSG.pCore 2 ↥M with hN
  set π : ↥M →* ↥M ⧸ N := QuotientGroup.mk' N with hπ
  have hNcard : IsPGroup 2 ↥N := by
    rw [hN]
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hNG : (pCoreOf 2 M).subgroupOf M = N := by
    show (Subgroup.map M.subtype (CFSG.Open.pCore 2 ↥M)).comap M.subtype = N
    rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective, hN]
  set ℒ : Set (Subgroup (↥M ⧸ N)) :=
    (fun J' : Subgroup G => (J'.subgroupOf M).map π) '' {J' | JPred p M J'} with hℒ
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
        obtain ⟨f⟩ := hhat.2.2
        have hq : CFSG.Open.IsQuasisimple (↥J' ⧸ CFSG.pCore 2 ↥J') :=
          ⟨hhat.1, f.isSimpleGroup_congr.2 S7.isSimple_Alt7⟩
        exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e1 hq
    · rintro _ ⟨J', hJ', rfl⟩
      obtain ⟨hp3', hJ'M, hsn, hperf, hhat⟩ := hJ'
      exact nonempty_quot_center_alt7_of_equiv (quotEquivTwoImage hJ'M hsn) (Or.inr hhat)
  set bt : ↥M ⧸ N := π ⟨b, hbM⟩ with hbt
  have hbt3 : bt ^ 3 = 1 := by
    rw [hbt, ← map_pow]
    have : (⟨b, hbM⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [this, map_one]
  have hbℒ : ∀ L ∈ ℒ, L.map (MulAut.conj bt).toMonoidHom ∈ ℒ := by
    rintro _ ⟨J', hJ', rfl⟩
    refine ⟨GLBConj b⁻¹ J', JPred.gLBConj hJ' (M.inv_mem hbM), ?_⟩
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
  have hαℒ : ((alphaOf p M).subgroupOf M).map π ≤ sSup ℒ := by
    have hα : alphaOf p M = pCoreOf 2 M ⊔ ⨆ x : {J' : Subgroup G // JPred p M J'}, x.1 := by
      unfold alphaOf
      rw [iSup_subtype']
      try rfl
    have hle1 : (⨆ x : {J' : Subgroup G // JPred p M J'}, x.1) ≤ M :=
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
  have hJα : J ≤ alphaOf p M := hJle.trans inf_le_left
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
  have hℒα : sSup ℒ ≤ ((alphaOf p M).subgroupOf M).map π := by
    refine sSup_le ?_
    rintro _ ⟨J', hJ', rfl⟩
    refine Subgroup.map_mono ?_
    intro w hw
    have hw' : (w : G) ∈ J' := (Subgroup.mem_subgroupOf).1 hw
    refine (Subgroup.mem_subgroupOf).2 ?_
    have : J' ≤ alphaOf p M := by
      unfold alphaOf
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
      have hyα : (y : G) ∈ alphaOf p M := (Subgroup.mem_subgroupOf).1 hy
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
      have hVα : pCoreOf 2 M ≤ alphaOf p M := by
        unfold alphaOf
        exact le_sup_left
      have hyvX : (y : G) * v ∈ X :=
        ⟨(alphaOf p M).mul_mem hyα (hVα hv), hxv⟩
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

theorem lemma911S_proved : Lemma911S := lemma911S_of_typeWeak lemma911TypeWeak

end Main

end CFSG.LocalAnalysis.GLTheoremB
