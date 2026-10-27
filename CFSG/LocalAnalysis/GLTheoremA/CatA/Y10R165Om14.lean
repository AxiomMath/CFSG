module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om13

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks QuadraticMap Polynomial
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

namespace OmEngine

variable {F V : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {n p q : ℕ}
  {Ã : Subgroup ↥(orthDerived Q)}

private theorem thirdBlock_mem_orthDerived_of_odd [Fintype ↥(orthImage Ã)]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0) (hAe : IsElemAbelian p (orthImage Ã))
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1)
    {D : Hyperplane (orthImage Ã) p}
    {xE' : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) ≃ₗ[F]
      ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))}
    (hxE'odd : OddOrderIsometry
      (Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype) p xE')
    (hZeven : Even (Module.finrank F ↥(fixedSpace xE')))
    (hZcases : Module.finrank F ↥(fixedSpace xE') = 4 ∨
      6 ≤ Module.finrank F ↥(fixedSpace xE'))
    (hns : Module.finrank F ↥(fixedSpace xE') = 4 →
      ∀ U : Submodule F ↥(fixedSpace xE'), Module.finrank F U = 2 →
        ∃ u ∈ U, ((Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype)).comp
          (fixedSpace xE').subtype u ≠ 0)
    {xGZ : ↥(fixedSpace xE') ≃ₗ[F] ↥(fixedSpace xE')}
    (hxGZodd : OddOrderIsometry
      ((Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype).comp
        (fixedSpace xE').subtype) p xGZ)
    (hxGZne : xGZ ≠ 1) :
    xGZ ∈ orthDerived ((Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype).comp
        (fixedSpace xE').subtype) ∧
      p ∣ Nat.card ↥(supportedFixedDerived
        (Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype) xE') := by
  let xD : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht D
  have hxGZmem : xGZ ∈ orthDerived
      ((Q.comp (fixedSpace xD).subtype).comp (fixedSpace xE').subtype) :=
    mem_orthDerived_of_odd_of_dim (W := ↥(fixedSpace xE'))
      (Q := (Q.comp (fixedSpace xD).subtype).comp (fixedSpace xE').subtype)
      hxE'odd.polarBilin_fixed_nondegenerate hp hp2 hxGZodd hxGZne hZeven hZcases hns
  have hxGZord : orderOf xGZ = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hxGZodd.pow_eq_one hxGZne
  refine ⟨hxGZmem, ?_⟩
  rw [Nat.card_congr (supportedFixedDerivedEquiv hxE'odd).toEquiv]
  have h := Subgroup.orderOf_dvd_natCard (orthDerived
    ((Q.comp (fixedSpace xD).subtype).comp (fixedSpace xE').subtype)) hxGZmem
  rwa [hxGZord] at h

private theorem mem_isometryCentralizer_of_centralizes [Fintype ↥(orthImage Ã)]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hAe : IsElemAbelian p (orthImage Ã))
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1)
    {D E : Hyperplane (orthImage Ã) p}
    {xEK : ↥(orthDerived Q)}
    (hxodd : OddOrderIsometry Q p (blockEnd (orthImage Ã) hp hpF hAe t ht D))
    {xE' : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) ≃ₗ[F]
      ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))}
    (hxE'coe : ∀ z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)),
      ((xE' z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) =
        blockEnd (orthImage Ã) hp hpF hAe t ht E (z : V))
    {J : Subgroup ↥(orthDerived Q)}
    (hJdef : J = (supportedFixedDerived Q (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subgroupOf
      (orthDerived Q))
    {Φ : ↥J →* (↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) ≃ₗ[F]
      ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)))}
    (hΦ_apply : ∀ (y : ↥J) (w : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))),
      ((Φ y w : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) =
        ((y : ↥(orthDerived Q)) : V ≃ₗ[F] V) (w : V))
    {EK : Subgroup ↥(orthDerived Q)}
    (hxEH : blockEnd (orthImage Ã) hp hpF hAe t ht E ∈ orthDerived Q)
    (hxEKdef : xEK = ⟨blockEnd (orthImage Ã) hp hpF hAe t ht E, hxEH⟩)
    (hxEK_mem : xEK ∈ EK) (y : ↥J)
    (hy : (y : ↥(orthDerived Q)) ∈ Subgroup.centralizer (EK : Set ↥(orthDerived Q))) :
    Φ y ∈ isometryCentralizer
      (Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype) xE' := by
  let xD : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht D
  let xE : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht E
  refine mem_isometryCentralizer.mpr ⟨fun w => ?_, fun w => ?_⟩
  · show Q ((Φ y w : ↥(fixedSpace xD)) : V) = Q (w : V)
    rw [hΦ_apply y w]
    have hyJ : (y : ↥(orthDerived Q)) ∈ (supportedFixedDerived Q xD).subgroupOf
        (orthDerived Q) := by
      rw [← hJdef]
      exact y.2
    have hySFD : ((y : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈ supportedFixedDerived Q xD :=
      (Subgroup.mem_subgroupOf (H := supportedFixedDerived Q xD)).mp hyJ
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (orthDerived_le_orthogonalGroup (hxodd.supportedFixedDerived_le_orthDerived hySFD))
      (w : V)
  · apply Subtype.ext
    show ((Φ y (xE' w) : ↥(fixedSpace xD)) : V) = ((xE' (Φ y w) : ↥(fixedSpace xD)) : V)
    rw [hΦ_apply y (xE' w), hxE'coe, hxE'coe, hΦ_apply y w]
    have hy_comm : Commute ((y : ↥(orthDerived Q)) : V ≃ₗ[F] V) xE := by
      have h := Subgroup.mem_centralizer_iff.mp hy xEK hxEK_mem
      have h' := (congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) h).symm
      rw [hxEKdef] at h'
      show ((y : ↥(orthDerived Q)) : V ≃ₗ[F] V) * xE =
        xE * ((y : ↥(orthDerived Q)) : V ≃ₗ[F] V)
      dsimp only [xE]
      exact h'
    rw [← LinearEquiv.mul_apply, hy_comm.eq, LinearEquiv.mul_apply]

private theorem layer_ne_bot_of_restriction [Fintype ↥(orthImage Ã)]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hAe : IsElemAbelian p (orthImage Ã))
    (hQ : (polarBilin Q).Nondegenerate) (h2 : (2 : F) = 0)
    (hQinv : ∀ a : ↥(orthImage Ã), ∀ v : V, Q ((a : V ≃ₗ[F] V) v) = Q v)
    (hB : ∀ a : ↥(orthImage Ã), ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v)
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1)
    {D E G : Hyperplane (orthImage Ã) p} (hDE : D ≠ E) (hGE : G ≠ E)
    (hxodd : OddOrderIsometry Q p (blockEnd (orthImage Ã) hp hpF hAe t ht D))
    (hxGord : orderOf (blockEnd (orthImage Ã) hp hpF hAe t ht G) = p)
    (hxGJ : blockEnd (orthImage Ã) hp hpF hAe t ht G ∈
      supportedFixedDerived Q (blockEnd (orthImage Ã) hp hpF hAe t ht D))
    (hxGH : blockEnd (orthImage Ã) hp hpF hAe t ht G ∈ orthDerived Q)
    {xE' : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) ≃ₗ[F]
      ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))}
    (hxE'coe : ∀ z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)),
      ((xE' z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) =
        blockEnd (orthImage Ã) hp hpF hAe t ht E (z : V))
    (hxE'odd : OddOrderIsometry
      (Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype) p xE')
    (hZcases : Module.finrank F ↥(fixedSpace xE') = 4 ∨
      6 ≤ Module.finrank F ↥(fixedSpace xE'))
    (hnotplus : Module.finrank F ↥(fixedSpace xE') = 4 →
      ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
        ((Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype).comp
          (fixedSpace xE').subtype))
    (hxGquad : ∀ v : V, Q (blockEnd (orthImage Ã) hp hpF hAe t ht G v) = Q v)
    (hcommGD : Commute (blockEnd (orthImage Ã) hp hpF hAe t ht G)
      (blockEnd (orthImage Ã) hp hpF hAe t ht D))
    (hcommEG : Commute (blockEnd (orthImage Ã) hp hpF hAe t ht E)
      (blockEnd (orthImage Ã) hp hpF hAe t ht G))
    {xGZ : ↥(fixedSpace xE') ≃ₗ[F] ↥(fixedSpace xE')}
    (hxGZcoe : ∀ z : ↥(fixedSpace xE'),
      ((xGZ z : ↥(fixedSpace xE')) : V) = blockEnd (orthImage Ã) hp hpF hAe t ht G (z : V))
    (hxGZmem : xGZ ∈ orthDerived
      ((Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype).comp
        (fixedSpace xE').subtype))
    {xDK xEK : ↥(orthDerived Q)} {DK EK : Subgroup ↥(orthDerived Q)}
    (hxDH : blockEnd (orthImage Ã) hp hpF hAe t ht D ∈ orthDerived Q)
    (hxEH : blockEnd (orthImage Ã) hp hpF hAe t ht E ∈ orthDerived Q)
    (hxDKdef : xDK = ⟨blockEnd (orthImage Ã) hp hpF hAe t ht D, hxDH⟩)
    (hxEKdef : xEK = ⟨blockEnd (orthImage Ã) hp hpF hAe t ht E, hxEH⟩)
    (hDKdef : DK = Subgroup.zpowers xDK)
    (hEKdef : EK = Subgroup.closure ({xDK, xEK} : Set ↥(orthDerived Q)))
    (hJle : (supportedFixedDerived Q (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subgroupOf
        (orthDerived Q) ≤ Subgroup.centralizer (DK : Set ↥(orthDerived Q))) :
    GLAPLayer p ((supportedFixedDerived Q (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subgroupOf
        (orthDerived Q) ⊓ Subgroup.centralizer (EK : Set ↥(orthDerived Q))) ≠ ⊥ := by
  classical
  let xD : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht D
  let xE : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht E
  let J : Subgroup ↥(orthDerived Q) := (supportedFixedDerived Q xD).subgroupOf (orthDerived Q)
  let xG : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht G
  obtain ⟨Φ, hΦdef, hΦinj, hΦrange, L'SFD, hL'SFDdef, hL'SFDq, L'J, hL'Jdef, hL'Jmap,
    L, hLdef, hLq, hLqOpen, hLcard, hLleJ⟩ :=
    exists_layer hxodd hxE'odd h2 hZcases hnotplus
  obtain ⟨xGW', hxGW'coe, hxGW'SFD⟩ :=
    exists_restriction_mem_supportedFixedDerived hcommEG hcommGD hxGquad
      (fun v => blockEnd_sub_mem_blockSpace hp hpF hAe t ht G v)
      (fun v hv => blockEnd_apply_of_mem_block (orthImage Ã) hp hpF hAe t ht
        (D := E) (E := G) hGE hv) hxE'coe hxE'odd hxGZcoe hxGZmem
  let xGJ : ↥J := ⟨⟨xG, hxGH⟩, hxGJ⟩
  have hΦxG : Φ xGJ = xGW' := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [hxGW'coe, hΦdef]
    rfl
  have hxGJ_mem : xGJ ∈ L'J := by
    rw [hL'Jdef, Subgroup.mem_comap, hΦxG, hL'SFDdef]
    exact hxGW'SFD
  have hxGJ_ord : orderOf xGJ = p := by
    rw [← Subgroup.orderOf_coe xGJ]
    rw [show ((xGJ : ↥J) : ↥(orthDerived Q)) = ⟨xG, hxGH⟩ from rfl]
    rw [← Subgroup.orderOf_coe (⟨xG, hxGH⟩ : ↥(orthDerived Q))]
    exact hxGord
  have hpdvdL'J : p ∣ Nat.card ↥L'J := by
    have h := Subgroup.orderOf_dvd_natCard L'J hxGJ_mem
    rwa [hxGJ_ord] at h
  have hpdvdL : p ∣ Nat.card ↥L := by
    rw [hLcard]
    exact hpdvdL'J
  have hJmem : ∀ j : ↥J, ((j : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈
      supportedFixedDerived Q xD := by
    intro j
    have h : (j : ↥(orthDerived Q)) ∈ (supportedFixedDerived Q xD).subgroupOf (orthDerived Q) := by
      change (j : ↥(orthDerived Q)) ∈ J
      exact j.2
    exact (Subgroup.mem_subgroupOf (H := supportedFixedDerived Q xD)).mp h
  have hΦ_apply : ∀ (j : ↥J) (w : ↥(fixedSpace xD)),
      ((Φ j w : ↥(fixedSpace xD)) : V) = ((j : ↥(orthDerived Q)) : V ≃ₗ[F] V) (w : V) := by
    intro j w
    rw [hΦdef]
    rfl
  have hL'J_cent : ∀ j : ↥J, j ∈ L'J →
      Φ j ∈ isometryCentralizer (Q.comp (fixedSpace xD).subtype) xE' := by
    intro j hj
    have hjSFD : Φ j ∈ supportedFixedDerived (Q.comp (fixedSpace xD).subtype) xE' := by
      rw [← hL'SFDdef]
      rwa [hL'Jdef, Subgroup.mem_comap] at hj
    exact supportedFixedDerived_le_isometryCentralizer hjSFD
  have hLleCent :=
    layer_le_centralizer (D := D) (E := E) hp hpF hAe hQ hQinv hB t ht hDE hxE'coe hJmem
      hΦ_apply hL'J_cent hLdef hxDH hxEH hxDKdef hxEKdef hJle
      (by rw [hDKdef]; exact Subgroup.mem_zpowers xDK) hEKdef
  have hxEK_mem : xEK ∈ EK := by
    rw [hEKdef]
    exact Subgroup.subset_closure (by simp)
  have hΦ_cent := mem_isometryCentralizer_of_centralizes hp hpF hAe t ht hxodd
    hxE'coe (by rfl) hΦ_apply hxEH hxEKdef hxEK_mem
  have hlayer :=
    layer_normal hp hxE'odd hL'SFDdef hL'Jdef (fun j hj => by
      rw [hL'Jdef, Subgroup.mem_comap] at hj
      exact hj) (fun y hy => hΦ_cent y hy) hLdef hLqOpen hpdvdL hLleJ hLleCent
  simpa only [J, xD] using hlayer


theorem concl165_of_restriction [Fintype ↥(orthImage Ã)]
    (hQ : (polarBilin Q).Nondegenerate) (hn : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0) (h2 : (2 : F) = 0)
    (hAe : IsElemAbelian p (orthImage Ã))
    (hQinv : ∀ a : ↥(orthImage Ã), ∀ v : V, Q ((a : V ≃ₗ[F] V) v) = Q v)
    (hB : ∀ a : ↥(orthImage Ã), ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v)
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1)
    {D E G : Hyperplane (orthImage Ã) p}
    (hDS : D ∈ nonBotBlocks (orthImage Ã) p) (hES : E ∈ nonBotBlocks (orthImage Ã) p)
    (hDE : D ≠ E) (hGD : G ≠ D) (hGE : G ≠ E)
    (hfixD : 8 ≤ Module.finrank F ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)))
    (hregD : 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ∨
      ∃ ℓ : ℕ, Module.finrank F V = 2 * ℓ ∧ Odd ℓ ∧ 5 ≤ ℓ ∧
        Module.finrank F ↥(blockSpace (orthImage Ã) D.1) = 2 ∧
        Module.finrank F ↥(blockSpace (orthImage Ã) E.1) = 2)
    (hGne : blockSpace (orthImage Ã) G.1 ≠ ⊥)
    (hxGord : orderOf (blockEnd (orthImage Ã) hp hpF hAe t ht G) = p)
    (hxGJ : blockEnd (orthImage Ã) hp hpF hAe t ht G ∈
      supportedFixedDerived Q (blockEnd (orthImage Ã) hp hpF hAe t ht D))
    {Zv : Submodule F V}
    (hZvdef : Zv = LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe D) ⊓
      LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe E))
    (hZvdim : Module.finrank F ↥Zv =
      Module.finrank F V - Module.finrank F ↥(blockSpace (orthImage Ã) D.1) -
        Module.finrank F ↥(blockSpace (orthImage Ã) E.1))
    (hxodd : OddOrderIsometry Q p (blockEnd (orthImage Ã) hp hpF hAe t ht D))
    (hxEJ : blockEnd (orthImage Ã) hp hpF hAe t ht E ∈
      supportedFixedDerived Q (blockEnd (orthImage Ã) hp hpF hAe t ht D))
    {xDK xEK : ↥(orthDerived Q)} {DK EK J : Subgroup ↥(orthDerived Q)}
    (hxDH : blockEnd (orthImage Ã) hp hpF hAe t ht D ∈ orthDerived Q)
    (hxEH : blockEnd (orthImage Ã) hp hpF hAe t ht E ∈ orthDerived Q)
    (hxDKdef : xDK = ⟨blockEnd (orthImage Ã) hp hpF hAe t ht D, hxDH⟩)
    (hxEKdef : xEK = ⟨blockEnd (orthImage Ã) hp hpF hAe t ht E, hxEH⟩)
    (hDKdef : DK = Subgroup.zpowers xDK)
    (hEKdef : EK = Subgroup.closure ({xDK, xEK} : Set ↥(orthDerived Q)))
    (hJdef : J = (supportedFixedDerived Q (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subgroupOf
      (orthDerived Q))
    (hJle : J ≤ Subgroup.centralizer (DK : Set ↥(orthDerived Q)))
    (hJcomp : GLAPComponent p (Subgroup.centralizer (DK : Set ↥(orthDerived Q))) J)
    (hÃN : Ã ≤ Subgroup.normalizer (J : Set ↥(orthDerived Q)))
    {FK : Subgroup ↥(orthDerived Q)}
    (hFKe : IsElemAbelian q FK) (hF3 : 3 ≤ CFSG.Open.pRank q FK)
    (hFcent : FK ≤ Subgroup.centralizer (DK : Set ↥(orthDerived Q)))
    (hFJN : FK ≤ Subgroup.normalizer (J : Set ↥(orthDerived Q)))
    (hDKEK : DK ≤ EK) (hEKÃ : EK ≤ Ã) (hDKcard : Nat.card DK = p)
    (hEKcard : Nat.card EK = p ^ 2)
    (hxGH : blockEnd (orthImage Ã) hp hpF hAe t ht G ∈ orthDerived Q)
    (hxEpow : blockEnd (orthImage Ã) hp hpF hAe t ht E ^ p = 1)
    (hxGpow : blockEnd (orthImage Ã) hp hpF hAe t ht G ^ p = 1) :
    Concl165 ↥(orthDerived Q) p q Ã := by
  classical
  subst J
  let xD : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht D
  let xE : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht E
  let J : Subgroup ↥(orthDerived Q) := (supportedFixedDerived Q xD).subgroupOf (orthDerived Q)
  let xG : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht G
  have hxEsupp : blockEnd (orthImage Ã) hp hpF hAe t ht E ∈
      supportedBlock Q (blockEnd (orthImage Ã) hp hpF hAe t ht D) (X - 1) :=
    supportedFixedDerived_le_supportedBlock hxEJ
  obtain ⟨xE', hxE'coe, hxE'odd⟩ :=
    exists_restriction_fixed hp hpF hxodd hxEpow hxEsupp
  obtain ⟨hVG_le_Zmap, hZmap, hZdim⟩ :=
    map_fixedSpace_eq_common_fixed (D := D) (E := E) (G := G) hp hpF hAe t ht hGD hGE hxE'coe hZvdef
  obtain ⟨hZge, hZeven, hZcases⟩ :=
    four_le_finrank_fixedSpace (D := D) (E := E) (G := G) hQ hn hp hp2 hpF h2 hAe hB t ht
      hDE hGD hGE hGne hZvdim hregD hxE'odd hZdim
  have hxGquad : ∀ v : V, Q (xG v) = Q v :=
    blockEnd_quadratic (orthImage Ã) hp hpF hAe Q hQinv t ht G
  have hcommGD : Commute xG xD := blockEnd_commute_of_ne (orthImage Ã) hp hpF hAe t ht hGD
  have hcommEG : Commute xE xG := blockEnd_commute_of_ne (orthImage Ã) hp hpF hAe t ht hGE.symm
  obtain ⟨xGW, hxGWcoe, xGZ, hxGZcoe, hxGZodd⟩ :=
    exists_restriction_third_block hp hpF hxE'coe hxE'odd hxGquad hxGpow hcommGD hcommEG
  obtain ⟨hnotplus, hns⟩ :=
    not_isPlusType_and_anisotropic_of_finrank_eq_four (D := D) (E := E) (G := G) hQ hn hp hp2 hpF
      h2 hAe hB t ht hDE hGD hGE hGne hZvdim hregD hxE'odd hZdim hVG_le_Zmap hxGZcoe hxGZodd
  have hxGZne : xGZ ≠ 1 :=
    ne_one_of_restriction (D := D) (E := E) (G := G) hp hpF hAe t ht hGD hGne hVG_le_Zmap hxGZcoe
  obtain ⟨hxGZmem, hpdvdL'⟩ :=
    thirdBlock_mem_orthDerived_of_odd hp hp2 hpF hAe t ht hxE'odd hZeven hZcases hns
      hxGZodd hxGZne
  have hlayer :=
    layer_ne_bot_of_restriction hp hpF hAe hQ h2 hQinv hB t ht hDE hGE hxodd hxGord hxGJ hxGH
      hxE'coe hxE'odd hZcases hnotplus hxGquad hcommGD hcommEG hxGZcoe hxGZmem hxDH hxEH
      hxDKdef hxEKdef hDKdef hEKdef hJle
  exact ⟨DK, EK, FK, J, hDKEK, hEKÃ, hDKcard, hEKcard, hJcomp, hÃN, hlayer,
    hFcent, hFKe, hFJN, hF3⟩


theorem concl165_of_blocks
    (hT : OmTorusThree)
    (hQ : (polarBilin Q).Nondegenerate) (hn : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hqdiv : q ∣ 2 ^ n - 1 ∨ q ∣ 2 ^ n + 1)
    (hÃe : IsElemAbelian p Ã)
    (hÃmax : CFSG.Open.pRank p (⊤ : Subgroup ↥(orthDerived Q)) ≤ CFSG.Open.pRank p Ã)
    (hÃ3 : 3 ≤ CFSG.Open.pRank p Ã)
    (hreg : 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ∨
      (CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n = 2 ∧ ∃ ℓ : ℕ,
        Module.finrank F V = 2 * ℓ ∧ Odd ℓ ∧ 5 ≤ ℓ ∧
        ℓ - 1 ≤ CFSG.Open.pRank p Ã)) :
    Concl165 ↥(orthDerived Q) p q Ã := by
  classical
  letI : Fintype ↥(orthImage Ã) := Fintype.ofFinite ↥(orthImage Ã)
  have hpF : (p : F) ≠ 0 := cast_prime_ne_zero hp hp2
  have h2 : (2 : F) = 0 := by
    have := CharP.cast_eq_zero F 2
    simpa using this
  have hAe : IsElemAbelian p (orthImage Ã) := isElemAbelian_orthImage hÃe
  have hQinv : ∀ a : ↥(orthImage Ã), ∀ v : V, Q ((a : V ≃ₗ[F] V) v) = Q v :=
    fun a => quadratic_orthImage (Ã := Ã) a
  have hB : ∀ a : ↥(orthImage Ã), ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v :=
    fun a => polar_orthImage (Ã := Ã) a
  obtain ⟨t, ht, hmemH, - , hmemA, hcount⟩ :=
    exists_block_representation hQ hn hp hp2 hÃe hÃmax hÃ3 hreg
  obtain ⟨D, E, G, Zv, hDS, hES, hGS, hDE, hGD, hGE, hfixD, hregD, hGne,
    hxGord, hxGJ, hZvdef, hZvdim, hGleZv⟩ :=
    exists_blocks_setup hQ hn hp hp2 hreg hÃe hÃ3 hpF hAe hQinv hB t ht hcount
  obtain ⟨xDK, xEK, DK, EK, J, hxDKdef, hxEKdef, hDKdef, hEKdef, hJdef, hxodd,
    hDKEK, hEKÃ, hDKcard, hEKcard, hxEKJ, hxEJ, hordxE, hJle, hJcomp, hÃN⟩ :=
    exists_pComponent (D := D) (E := E) hQ hp hp2 hpF hAe hQinv hB t ht hDE hDS hES hfixD
      (hmemH D) (hmemH E) (hmemA D) (hmemA E)
  subst J
  let xD : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht D
  let xE : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht E
  let J : Subgroup ↥(orthDerived Q) := (supportedFixedDerived Q xD).subgroupOf (orthDerived Q)
  let xG : V ≃ₗ[F] V := blockEnd (orthImage Ã) hp hpF hAe t ht G
  have hxEpow : xE ^ p = 1 := blockEnd_pow (orthImage Ã) hp hpF hAe t ht E
  have hxGpow : xG ^ p = 1 := blockEnd_pow (orthImage Ã) hp hpF hAe t ht G
  have hxEsupp : xE ∈ supportedBlock Q xD (X - 1) :=
    supportedFixedDerived_le_supportedBlock hxEJ
  let J : Subgroup ↥(orthDerived Q) := (supportedFixedDerived Q xD).subgroupOf (orthDerived Q)
  let eJ : ↥J ≃* ↥(orthDerived (Q.comp (fixedSpace xD).subtype)) :=
    (Subgroup.subgroupOfEquivOfLe hxodd.supportedFixedDerived_le_orthDerived).trans
      (supportedFixedDerivedEquiv hxodd)
  obtain ⟨FK, hFKe, hF3, hFcent, hFJN⟩ :=
    exists_qTorus hT hn hq hq2 hqdiv hxodd hfixD J eJ DK hJle
  exact concl165_of_restriction hQ hn hp hp2 hpF h2 hAe hQinv hB t ht hDS hES hDE hGD hGE
    hfixD hregD hGne hxGord hxGJ hZvdef hZvdim hxodd hxEJ (hmemH D) (hmemH E) hxDKdef hxEKdef
    hDKdef hEKdef (hJdef := rfl) hJle hJcomp hÃN hFKe hF3 hFcent hFJN hDKEK hEKÃ hDKcard
    hEKcard (hmemH G) (blockEnd_pow (orthImage Ã) hp hpF hAe t ht E)
    (blockEnd_pow (orthImage Ã) hp hpF hAe t ht G)

end OmEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
