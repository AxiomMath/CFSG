module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om8

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks QuadraticMap Polynomial
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

namespace OmEngine

variable {F V : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {n p q : ℕ} {Ã : Subgroup ↥(orthDerived Q)}

theorem exists_block_representation [Fintype ↥(orthImage Ã)]
    (hQ : (polarBilin Q).Nondegenerate) (hn : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hÃe : IsElemAbelian p Ã)
    (hÃmax : CFSG.Open.pRank p (⊤ : Subgroup ↥(orthDerived Q)) ≤ CFSG.Open.pRank p Ã)
    (hÃ3 : 3 ≤ CFSG.Open.pRank p Ã)
    (hreg : 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ∨
      (CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n = 2 ∧ ∃ ℓ : ℕ,
        Module.finrank F V = 2 * ℓ ∧ Odd ℓ ∧ 5 ≤ ℓ ∧
        ℓ - 1 ≤ CFSG.Open.pRank p Ã)) :
    ∃ (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1),
      (∀ D, blockEnd (orthImage Ã) hp (cast_prime_ne_zero hp hp2)
        (isElemAbelian_orthImage hÃe) t ht D ∈ orthDerived Q) ∧
      CFSG.Open.pRank p (orthDerived Q) ≤ CFSG.Open.pRank p (orthImage Ã) ∧
      (∀ D, blockEnd (orthImage Ã) hp (cast_prime_ne_zero hp hp2)
        (isElemAbelian_orthImage hÃe) t ht D ∈ orthImage Ã) ∧
      3 ≤ (nonBotBlocks (orthImage Ã) p).card := by
  classical
  have hpF : (p : F) ≠ 0 := cast_prime_ne_zero hp hp2
  have hAe : IsElemAbelian p (orthImage Ã) := isElemAbelian_orthImage hÃe
  haveI : IsMulCommutative ↥(orthImage Ã) := hAe.1
  obtain ⟨t, ht⟩ := HypBlocks.exists_blockRep (orthImage Ã) hp
  have hQinv : ∀ a : ↥(orthImage Ã), ∀ v : V, Q ((a : V ≃ₗ[F] V) v) = Q v :=
    fun a => quadratic_orthImage (Ã := Ã) a
  have hB : ∀ a : ↥(orthImage Ã), ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v :=
    fun a => polar_orthImage (Ã := Ã) a
  have hT3 := exists_isTotallyIsotropic_of_regime hQ hn hp hp2 hÃe hÃ3 hreg t ht
  have hmemH : ∀ D, blockEnd (orthImage Ã) hp hpF hAe t ht D ∈ orthDerived Q := fun D =>
    blockEnd_mem_orthDerived (orthImage Ã) hp hpF hp2 hAe hQ hQinv t ht D hT3
  have hmaxH : CFSG.Open.pRank p (orthDerived Q) ≤ CFSG.Open.pRank p (orthImage Ã) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (orthDerived Q),
      pRank_orthImage (Ã := Ã) hp]
    exact hÃmax
  have hmemA : ∀ D, blockEnd (orthImage Ã) hp hpF hAe t ht D ∈ orthImage Ã := fun D =>
    HypBlocks.blockEnd_mem_of_pRank_le (orthImage Ã) hp hpF hAe t ht (orthImage_le Ã)
      hmaxH hmemH D
  have hcount : 3 ≤ (nonBotBlocks (orthImage Ã) p).card := by
    have h1 : 3 ≤ CFSG.Open.pRank p (orthImage Ã) := by
      rw [pRank_orthImage (Ã := Ã) hp]; exact hÃ3
    exact le_trans h1 (pRank_le_card_ne_bot_blockSpace (orthImage Ã) hp hpF hAe t ht)
  exact ⟨t, ht, hmemH, hmaxH, hmemA, hcount⟩

theorem exists_blocks_setup [Fintype ↥(orthImage Ã)]
    (hQ : (polarBilin Q).Nondegenerate) (hn : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hreg : 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ∨
      (CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n = 2 ∧ ∃ ℓ : ℕ,
        Module.finrank F V = 2 * ℓ ∧ Odd ℓ ∧ 5 ≤ ℓ ∧
        ℓ - 1 ≤ CFSG.Open.pRank p Ã))
    (hÃe : IsElemAbelian p Ã) (hÃ3 : 3 ≤ CFSG.Open.pRank p Ã)
    (hpF : (p : F) ≠ 0) (hAe : IsElemAbelian p (orthImage Ã))
    (hQinv : ∀ a : ↥(orthImage Ã), ∀ v : V, Q ((a : V ≃ₗ[F] V) v) = Q v)
    (hB : ∀ a : ↥(orthImage Ã), ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v)
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1)
    (hcount : 3 ≤ (nonBotBlocks (orthImage Ã) p).card) :
    ∃ D E G : Hyperplane (orthImage Ã) p, ∃ Zv : Submodule F V,
      D ∈ nonBotBlocks (orthImage Ã) p ∧ E ∈ nonBotBlocks (orthImage Ã) p ∧
      G ∈ nonBotBlocks (orthImage Ã) p ∧ D ≠ E ∧ G ≠ D ∧ G ≠ E ∧
      8 ≤ Module.finrank F ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) ∧
      (3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ∨
        ∃ ℓ : ℕ, Module.finrank F V = 2 * ℓ ∧ Odd ℓ ∧ 5 ≤ ℓ ∧
          Module.finrank F ↥(blockSpace (orthImage Ã) D.1) = 2 ∧
          Module.finrank F ↥(blockSpace (orthImage Ã) E.1) = 2) ∧
      blockSpace (orthImage Ã) G.1 ≠ ⊥ ∧
      orderOf (blockEnd (orthImage Ã) hp hpF hAe t ht G) = p ∧
      blockEnd (orthImage Ã) hp hpF hAe t ht G ∈
        supportedFixedDerived Q (blockEnd (orthImage Ã) hp hpF hAe t ht D) ∧
      Zv = LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe D) ⊓
        LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe E) ∧
      Module.finrank F ↥Zv =
        Module.finrank F V - Module.finrank F ↥(blockSpace (orthImage Ã) D.1) -
          Module.finrank F ↥(blockSpace (orthImage Ã) E.1) ∧
      blockSpace (orthImage Ã) G.1 ≤ Zv := by
  classical
  obtain ⟨D, E, hDS, hES, hDE, hfixD, - , hregD⟩ : ∃ D E : Hyperplane (orthImage Ã) p,
      D ∈ nonBotBlocks (orthImage Ã) p ∧ E ∈ nonBotBlocks (orthImage Ã) p ∧ D ≠ E ∧
      8 ≤ Module.finrank F ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) ∧
      4 ≤ Module.finrank F ↥(fixedSpace
        (blockEnd (orthImage Ã) hp hpF hAe t ht D * blockEnd (orthImage Ã) hp hpF hAe t ht E)) ∧
      (3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ∨
        ∃ ℓ : ℕ, Module.finrank F V = 2 * ℓ ∧ Odd ℓ ∧ 5 ≤ ℓ ∧
          Module.finrank F ↥(blockSpace (orthImage Ã) D.1) = 2 ∧
          Module.finrank F ↥(blockSpace (orthImage Ã) E.1) = 2) := by
    rcases hreg with hm0 | ⟨hm2, ℓ, hdim, hodd, h5, hℓp⟩
    · obtain ⟨D, E, hDS, hES, hDE, hfixD, hfixmul⟩ :=
        exists_blocks_regimeI (orthImage Ã) hQ hp hpF hp2 hAe hB t ht hn hm0 hcount
      exact ⟨D, E, hDS, hES, hDE, hfixD, hfixmul, Or.inl hm0⟩
    · have hℓ : ℓ - 1 ≤ (nonBotBlocks (orthImage Ã) p).card := by
        have h1 : ℓ - 1 ≤ CFSG.Open.pRank p (orthImage Ã) := by
          rw [pRank_orthImage (Ã := Ã) hp]; exact hℓp
        exact le_trans h1 (pRank_le_card_ne_bot_blockSpace (orthImage Ã) hp hpF hAe t ht)
      obtain ⟨D, E, hDS, hES, hDE, hdD, hdE, hfixD, hfixmul⟩ :=
        exists_blocks_regimeII (orthImage Ã) hQ hp hpF hp2 hAe hB t ht ℓ hdim h5 hℓ
      exact ⟨D, E, hDS, hES, hDE, hfixD, le_trans (by norm_num) hfixmul,
        Or.inr ⟨ℓ, hdim, hodd, h5, hdD, hdE⟩⟩
  set xD : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht D with hxDdef
  set xE : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht E with hxEdef
  obtain ⟨G, hGS, hGD, hGE⟩ :=
    exists_mem_ne_of_three_le_card (S := nonBotBlocks (orthImage Ã) p) hDS hES hDE hcount
  have hGne : blockSpace (orthImage Ã) G.1 ≠ ⊥ := (mem_nonBotBlocks (orthImage Ã) p).mp hGS
  set xG : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht G with hxGdef
  have hxGord : orderOf xG = p := orderOf_blockEnd (orthImage Ã) hp hpF hAe t ht hGne
  have hxGJ : xG ∈ supportedFixedDerived Q xD :=
    blockEnd_mem_supportedFixedDerived (orthImage Ã) hp hpF hp2 hAe hQinv hQ hB t ht
      (Ne.symm hGD) hfixD
  let Zv : Submodule F V := LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe D) ⊓
    LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe E)
  have hDleKerE : blockSpace (orthImage Ã) D.1 ≤
      LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe E) := by
    intro v hv
    rw [LinearMap.mem_ker]
    exact projBlock_apply_of_mem_block (orthImage Ã) hp hpF hAe (D := E) (E := D)
      hDE hv
  have hsupker : LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe D) ⊔
      LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe E) = ⊤ := by
    have hsupD : blockSpace (orthImage Ã) D.1 ⊔
        LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe D) = ⊤ :=
      codisjoint_iff.mp (isCompl_blockSpace_ker (orthImage Ã) hp hpF hAe D).codisjoint
    rw [eq_top_iff, ← hsupD]
    exact sup_le (hDleKerE.trans le_sup_right) le_sup_left
  have hZvdim : Module.finrank F ↥Zv =
      Module.finrank F V - Module.finrank F ↥(blockSpace (orthImage Ã) D.1) -
        Module.finrank F ↥(blockSpace (orthImage Ã) E.1) := by
    have hZeq : Zv = LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe D) ⊓
        LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe E) := rfl
    rw [hZeq]
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe D))
      (LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe E))
    have hDker := finrank_ker_projBlock_add_finrank_blockSpace (orthImage Ã) hp hpF hAe D
    have hEker := finrank_ker_projBlock_add_finrank_blockSpace (orthImage Ã) hp hpF hAe E
    rw [hsupker, finrank_top] at h1
    omega
  have hGleZv : blockSpace (orthImage Ã) G.1 ≤ Zv := by
    intro v hv
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker]
      exact projBlock_apply_of_mem_block (orthImage Ã) hp hpF hAe (D := D) (E := G) hGD hv
    · rw [LinearMap.mem_ker]
      exact projBlock_apply_of_mem_block (orthImage Ã) hp hpF hAe (D := E) (E := G) hGE hv
  exact ⟨D, E, G, Zv, hDS, hES, hGS, hDE, hGD, hGE, hfixD, hregD, hGne, hxGord, hxGJ,
    rfl, hZvdim, hGleZv⟩


theorem exists_pComponent [Fintype ↥(orthImage Ã)]
    (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0)
    (hAe : IsElemAbelian p (orthImage Ã))
    (hQinv : ∀ a : ↥(orthImage Ã), ∀ v : V, Q ((a : V ≃ₗ[F] V) v) = Q v)
    (hB : ∀ a : ↥(orthImage Ã), ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v)
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1)
    {D E : Hyperplane (orthImage Ã) p} (hDE : D ≠ E)
    (hDS : D ∈ nonBotBlocks (orthImage Ã) p) (hES : E ∈ nonBotBlocks (orthImage Ã) p)
    (hfixD : 8 ≤ Module.finrank F ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)))
    (hxDH : blockEnd (orthImage Ã) hp hpF hAe t ht D ∈ orthDerived Q)
    (hxEH : blockEnd (orthImage Ã) hp hpF hAe t ht E ∈ orthDerived Q)
    (hxDA : blockEnd (orthImage Ã) hp hpF hAe t ht D ∈ orthImage Ã)
    (hxEA : blockEnd (orthImage Ã) hp hpF hAe t ht E ∈ orthImage Ã) :
    ∃ (xDK xEK : ↥(orthDerived Q)) (DK EK J : Subgroup ↥(orthDerived Q)),
      xDK = ⟨blockEnd (orthImage Ã) hp hpF hAe t ht D, hxDH⟩ ∧
      xEK = ⟨blockEnd (orthImage Ã) hp hpF hAe t ht E, hxEH⟩ ∧
      DK = Subgroup.zpowers xDK ∧
      EK = Subgroup.closure ({xDK, xEK} : Set ↥(orthDerived Q)) ∧
      J = (supportedFixedDerived Q (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subgroupOf
        (orthDerived Q) ∧
      OddOrderIsometry Q p (blockEnd (orthImage Ã) hp hpF hAe t ht D) ∧
      DK ≤ EK ∧ EK ≤ Ã ∧ Nat.card DK = p ∧
      Nat.card EK = p ^ 2 ∧ xEK ∈ J ∧
      blockEnd (orthImage Ã) hp hpF hAe t ht E ∈
        supportedFixedDerived Q (blockEnd (orthImage Ã) hp hpF hAe t ht D) ∧
      orderOf xEK = p ∧
      J ≤ Subgroup.centralizer (DK : Set ↥(orthDerived Q)) ∧
      GLAPComponent p (Subgroup.centralizer (DK : Set ↥(orthDerived Q))) J ∧
      Ã ≤ Subgroup.normalizer (J : Set ↥(orthDerived Q)) := by
  classical
  haveI : IsMulCommutative ↥(orthImage Ã) := hAe.1
  set xD : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht D with hxDdef
  set xE : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht E with hxEdef
  let xDK : ↥(orthDerived Q) := ⟨xD, hxDH⟩
  let xEK : ↥(orthDerived Q) := ⟨xE, hxEH⟩
  have hcomap : (orthImage Ã).comap (orthDerived Q).subtype = Ã := by
    rw [orthImage, Subgroup.comap_map_eq_self_of_injective (orthDerived Q).subtype_injective]
  have hxDKÃ : xDK ∈ Ã := by
    rw [← hcomap]
    exact Subgroup.mem_comap.mpr hxDA
  have hxEKÃ : xEK ∈ Ã := by
    rw [← hcomap]
    exact Subgroup.mem_comap.mpr hxEA
  let DK : Subgroup ↥(orthDerived Q) := Subgroup.zpowers xDK
  let EK : Subgroup ↥(orthDerived Q) :=
    Subgroup.closure ({xDK, xEK} : Set ↥(orthDerived Q))
  have hDKcard : Nat.card DK = p :=
    card_zpowers_orthDerived (Ã := Ã) hp hpF hAe t ht
      ((mem_nonBotBlocks (orthImage Ã) p).mp hDS) hxDH
  have hEKcard : Nat.card EK = p ^ 2 :=
    card_closure_pair_orthDerived (Ã := Ã) hp hpF hAe t ht hDE
      ((mem_nonBotBlocks (orthImage Ã) p).mp hDS) ((mem_nonBotBlocks (orthImage Ã) p).mp hES)
      hxDA hxEA hxDH hxEH
  have hDKEK : DK ≤ EK :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hEKÃ : EK ≤ Ã := by
    refine (Subgroup.closure_le _).mpr ?_
    intro z hz
    rcases hz with rfl | rfl
    · exact hxDKÃ
    · exact hxEKÃ
  let J : Subgroup ↥(orthDerived Q) := (supportedFixedDerived Q xD).subgroupOf (orthDerived Q)
  have hxodd : OddOrderIsometry Q p xD :=
    blockEnd_oddOrderIsometry (orthImage Ã) hp hpF hAe hQ hQinv t ht D
  have hxEJ : xE ∈ supportedFixedDerived Q xD :=
    blockEnd_mem_supportedFixedDerived (orthImage Ã) hp hpF hp2 hAe hQinv hQ hB t ht hDE hfixD
  have hxEKJ : xEK ∈ J := by
    change xEK ∈ (supportedFixedDerived Q xD).subgroupOf (orthDerived Q)
    exact Subgroup.mem_subgroupOf.mpr hxEJ
  have hordxE : orderOf xEK = p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_blockEnd (orthImage Ã) hp hpF hAe t ht
      ((mem_nonBotBlocks (orthImage Ã) p).mp hES)
  have hpxJ : p ∣ Nat.card J := by
    have h := Subgroup.orderOf_dvd_natCard J hxEKJ
    rwa [hordxE] at h
  have hJle : J ≤ Subgroup.centralizer (DK : Set ↥(orthDerived Q)) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hjSFD : (j : V ≃ₗ[F] V) ∈ supportedFixedDerived Q xD :=
      Subgroup.mem_subgroupOf.mp hj
    have hcomm : Commute (j : V ≃ₗ[F] V) xD := commute_of_mem_supportedFixedDerived hjSFD
    apply Subtype.ext
    show (((xDK ^ n : ↥(orthDerived Q)) : V ≃ₗ[F] V)) * (j : V ≃ₗ[F] V) =
      (j : V ≃ₗ[F] V) * (((xDK ^ n : ↥(orthDerived Q)) : V ≃ₗ[F] V))
    have hcoe : (((xDK ^ n : ↥(orthDerived Q)) : V ≃ₗ[F] V)) = xD ^ n := by
      change (orthDerived Q).subtype (xDK ^ n) = xD ^ n
      rw [map_zpow]
      rfl
    rw [hcoe]
    exact (hcomm.symm.zpow_left n).eq
  have hJnorm : (J.subgroupOf (Subgroup.centralizer (DK : Set ↥(orthDerived Q)))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hnSFD : (n : V ≃ₗ[F] V) ∈ supportedFixedDerived Q xD :=
      Subgroup.mem_subgroupOf.mp hn
    have hmemcent : (g : ↥(orthDerived Q)) ∈ Subgroup.centralizer (DK : Set ↥(orthDerived Q)) :=
      g.2
    have hgy : xDK * g.val = g.val * xDK :=
      Subgroup.mem_centralizer_iff.mp hmemcent xDK (Subgroup.mem_zpowers xDK)
    have hval : xD * (g.val : V ≃ₗ[F] V) = (g.val : V ≃ₗ[F] V) * xD := by
      have := congrArg Subtype.val hgy
      simpa [xDK] using this
    have hgcent : (g.val : V ≃ₗ[F] V) ∈ isometryCentralizer Q xD := by
      refine mem_isometryCentralizer.mpr ⟨fun v => ?_, fun v => ?_⟩
      · exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
          (orthDerived_le_orthogonalGroup_of_commutator Q g.val.2)) v
      · change ((g.val : V ≃ₗ[F] V) * xD) v = xD ((g.val : V ≃ₗ[F] V) v)
        rw [show ((g.val : V ≃ₗ[F] V) * xD) = xD * (g.val : V ≃ₗ[F] V) from hval.symm]
        rfl
    exact hxodd.conj_mem_supportedFixedDerived hgcent hnSFD
  have hJcomp : GLAPComponent p (Subgroup.centralizer (DK : Set ↥(orthDerived Q))) J := by
    have hJq : CFSG.IsQuasisimple ↥J := by
      have hsixD : 6 ≤ Module.finrank F ↥(fixedSpace xD) := by
        have h := finrank_fixedSpace_blockEnd (orthImage Ã) hp hpF hAe t ht D
        omega
      have hSFq : CFSG.IsQuasisimple ↥(supportedFixedDerived Q xD) :=
        isQuasisimple_supportedFixedDerived_of_six_le hxodd (by
          have := CharP.cast_eq_zero F 2
          simpa using this) hsixD
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hxodd.supportedFixedDerived_le_orthDerived).symm hSFq
    have hJqOpen : CFSG.Open.IsQuasisimple ↥J :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hJq)
    exact CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp hJqOpen hpxJ hJle hJnorm
  have hÃN : Ã ≤ Subgroup.normalizer (J : Set ↥(orthDerived Q)) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha j hj
    have haSFD : (a : V ≃ₗ[F] V) ∈ isometryCentralizer Q xD := by
      refine mem_isometryCentralizer.mpr ⟨fun v => ?_, fun v => ?_⟩
      · exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
          (orthDerived_le_orthogonalGroup_of_commutator Q a.2)) v
      · have haA : (a : V ≃ₗ[F] V) ∈ orthImage Ã := subtype_mem_orthImage_iff.mp ha
        have hcommA : ((⟨(a : V ≃ₗ[F] V), haA⟩ : ↥(orthImage Ã)) : V ≃ₗ[F] V) *
            xD = xD * ((⟨(a : V ≃ₗ[F] V), haA⟩ : ↥(orthImage Ã)) : V ≃ₗ[F] V) := by
          have h := mul_comm' (⟨(a : V ≃ₗ[F] V), haA⟩ : ↥(orthImage Ã))
            (⟨xD, hxDA⟩ : ↥(orthImage Ã))
          simpa using congrArg Subtype.val h
        exact LinearEquiv.congr_fun hcommA v
    have hjSFD : (j : V ≃ₗ[F] V) ∈ supportedFixedDerived Q xD :=
      Subgroup.mem_subgroupOf.mp hj
    rw [Subgroup.mem_subgroupOf]
    exact hxodd.conj_mem_supportedFixedDerived haSFD hjSFD
  exact ⟨xDK, xEK, DK, EK, J, rfl, rfl, rfl, rfl, rfl, hxodd, hDKEK, hEKÃ, hDKcard,
    hEKcard, hxEKJ, hxEJ, hordxE, hJle, hJcomp, hÃN⟩

end OmEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
