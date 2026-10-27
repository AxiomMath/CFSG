module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthFCArith
public import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Comp
import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Image

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFC

open Polynomial Module QuadraticMap CFSG.Open CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.HardMathSupport.Dickson.Bal207.Uni
  CFSG.HardMathSupport.Dickson.I271 Matrix
open CFSG.ComponentClassification.OuterAutomorphisms (congr_conj)

@[expose] def OrthInnerCases : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], (Nat.card F = 2 ∨ Nat.card F = 8) →
    ∀ (d : ℕ), 0 < d → ∀ (Q : QuadraticForm F (Fin d → F)), (polarBilin Q).Nondegenerate →
      (∃ U : Submodule F (Fin d → F), finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0) →
      ∀ (n : ℕ), d = 2 * n → 4 ≤ n → (IsPlusType Q ↔ Even n) →
        ∀ x : orthDerived Q, orderOf x = 3 →
          ∀ L : Subgroup (ProjOrthDerived Q),
            CFSG.Open.IsComponentOf L
              (Subgroup.centralizer ({piOrth Q x} : Set (ProjOrthDerived Q))) →
            (((X ^ 2 + X + 1 : F[X]) ∈
                primaryFactors (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap ∧
              2 ≤ primaryMultiplicity (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap
                (X ^ 2 + X + 1) ∧
              L = componentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (X ^ 2 + X + 1)) ∨
            (∃ i : TauCeti.ValidLieTypeIndex, FixedIdx i.1 ∧
              Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie i).Group)))

@[expose] def OrthBlockFrame : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K B J : Subgroup Y), IsSCp 3 ⊤ B →
    ∀ (hBK : B ≤ Subgroup.normalizer (K : Set Y)),
      Nat.Coprime 3 (Nat.card (Subgroup.center ↥K)) →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2], (Nat.card F = 2 ∨ Nat.card F = 8) →
        ∀ (d : ℕ) (hd : 0 < d) (Q : QuadraticForm F (Fin d → F)), (polarBilin Q).Nondegenerate →
          (∃ U : Submodule F (Fin d → F), finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0) →
          (∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 →
            g.val.right = 1 ∧ ∃ a : Fˣ, g.val.left = GeneralLinearGroup.scalar (Fin d) a) →
          ∀ e : (↥K ⧸ Subgroup.center ↥K) ≃* ProjOrthDerived Q,
            (∀ b : ↥B, MulAut.congr (coordBridge Q hd).symm (uniAut e ⟨b, hBK b.2⟩) ∈
              matrixProjectiveImage Q) →
            ∀ x : orthDerived Q, orderOf x = 3 →
              (X ^ 2 + X + 1 : F[X]) ∈
                primaryFactors (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap →
              3 ≤ primaryMultiplicity (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap
                (X ^ 2 + X + 1) →
              ¬(primaryMultiplicity (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap
                (X ^ 2 + X + 1) = 3 ∧ Nat.card F = 2) →
              (J.comap K.subtype).map (uniMap e) =
                componentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (X ^ 2 + X + 1) →
              ∀ (a : Y) (haB : a ∈ B), uniAut e ⟨a, hBK haB⟩ = MulAut.conj (piOrth Q x) →
              FirstClaim.BlockFrame e B J hBK

@[expose] def OrthFieldComps : Prop :=
  ∀ (S : Type) [Group S] (t : StatedLieTag) (n : ℕ), (t = .POmegaPlus ∨ t = .POmegaMinus) →
    5 ≤ n → StatedClassicalModel S t n 2 3 → ∀ β : MulAut S, β ^ 3 = 1 →
      (∀ a : S, MulAut.conj a ≠ β) →
        PerfectInLayer β ∧ ∃ J : Subgroup S,
          (∀ L : Subgroup S,
            CFSG.Open.IsComponentOf L (Solomon.Coordinator.fixSubgroup β) → L = J) ∧
          Subgroup.center ↥J = ⊥ ∧ StatedClassicalModel ↥J t n 2 1

@[expose] def OrthTwoInner : Prop :=
  ∀ (S : Type) [Group S] (t : StatedLieTag) (n : ℕ), (t = .POmegaPlus ∨ t = .POmegaMinus) →
    5 ≤ n → StatedClassicalModel S t n 2 1 → ∀ β : MulAut S, β ^ 3 = 1 →
      ∃ s : S, MulAut.conj s = β

theorem uniAut_pow_three {Y : Type} [Group Y] {K B : Subgroup Y} {S : Type} [Group S]
    (hB : IsSCp 3 ⊤ B) (hBK : B ≤ Subgroup.normalizer (K : Set Y))
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* S) {a : Y} (haB : a ∈ B) :
    uniAut e ⟨a, hBK haB⟩ ^ 3 = 1 := by
  have h3 : (⟨a, hBK haB⟩ : ↥(Subgroup.normalizer (K : Set Y))) ^ 3 = 1 :=
    Subtype.ext (hB.2.1.2 a haB)
  rw [← map_pow, h3, map_one]

theorem uniAut_ne_one {G : ∀ (S : Type) [Group S], MulAut S → Prop} {Y : Type} [Group Y]
    [Finite Y] {K B A : Subgroup Y} (ctx : Bal207PlusCtx G 3 K B A) {S : Type} [Group S]
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* S) {a : Y} (haA : a ∈ A) (ha1 : a ≠ 1) :
    uniAut e ⟨a, ctx.norm (ctx.le haA)⟩ ≠ 1 := fun h1 =>
  not_mem_centralizer_of_inf_eq_bot ctx.disj haA ha1
    (mem_centralizer_of_uniAut_eq_one e ctx.comp.2.2.1 (ctx.norm (ctx.le haA)) h1)

theorem card_componentImage_dvd {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V) (x : V ≃ₗ[F] V) (h : F[X]) :
    Nat.card (componentImage Q x h) ∣ Nat.card (specialBlock Q x h) := by
  refine (Subgroup.card_map_dvd _ _).trans ?_
  exact Subgroup.card_comap_dvd_of_injective _ _ (orthDerived Q).subtype_injective

theorem false_of_small_block {Y : Type} [Group Y] {K J : Subgroup Y} {F : Type} [Field F]
    [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V]
    (hF : Nat.card F = 2 ∨ Nat.card F = 8) (e : (↥K ⧸ Subgroup.center ↥K) ≃* ProjOrthDerived Q)
    (hJK : J ≤ K) {x : orthDerived Q} (hx3 : orderOf x = 3)
    (hmem : (X ^ 2 + X + 1 : F[X]) ∈ primaryFactors (x : V ≃ₗ[F] V).toLinearMap)
    (hL : (J.comap K.subtype).map (uniMap e) =
      componentImage Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1))
    (hbad : primaryMultiplicity (x : V ≃ₗ[F] V).toLinearMap (X ^ 2 + X + 1) = 2 ∨
      (primaryMultiplicity (x : V ≃ₗ[F] V).toLinearMap (X ^ 2 + X + 1) = 3 ∧ Nat.card F = 2))
    (hJFC : IsLieQuot ↥J IsSpFirstClaimIdx) : False := by
  classical
  have : Finite V := Module.finite_of_finite F
  have : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hpl : (3 : ℕ) ≠ ringChar F := by
    rw [ringChar.eq F 2]
    norm_num
  have hx := oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQ x hx3
  obtain ⟨f, hf, hFf⟩ := OrthFix.exists_exp hF
  obtain ⟨dd, hdd, ⟨eJ⟩⟩ := hJFC
  have h15 := FirstClaim.two_pow_dvd_card_of_isSpFirstClaimIdx dd hdd
  rw [← Nat.card_congr eJ.toEquiv] at h15
  have h1 := FirstClaim.card_centerQuot_dvd_card_image e hJK
  rw [hL] at h1
  have h2 := card_componentImage_dvd Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)
  have h3 : 2 ^ 15 ∣ Nat.card (specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)) :=
    h15.trans (h1.trans h2)
  have hv := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h3
  rw [OrthFix.factorization_two_card_specialBlock hx hmem hFf] at hv
  rcases hbad with hm | ⟨hm, hF2⟩
  · rw [hm] at hv
    rcases hf with rfl | rfl <;> norm_num at hv
  · rw [hm] at hv
    rcases hf with rfl | rfl
    · norm_num at hv
    · rw [hF2] at hFf
      norm_num at hFf

theorem uniAut_refl {Y : Type} [Group Y] {K : Subgroup Y}
    (g : ↥(Subgroup.normalizer (K : Set Y))) :
    uniAut (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)) g = actHom K g :=
  MulEquiv.ext fun _ => rfl

theorem orthFC_inner (hC : OrthInnerCases) (hD : OrthBlockFrame)
    {G : ∀ (S : Type) [Group S], MulAut S → Prop} {Y : Type} [Group Y] [Finite Y]
    {K B A : Subgroup Y} (ctx : Bal207PlusCtx G 3 K B A) (hIH : Bal207PlusIH G A)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥K)))
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ∨ Nat.card F = 8)
    {d : ℕ} (hd : 0 < d) {Q : QuadraticForm F (Fin d → F)} (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule F (Fin d → F), finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {n : ℕ} (hdn : d = 2 * n) (h4 : 4 ≤ n) (hV : IsPlusType Q ↔ Even n)
    (hker : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 →
      g.val.right = 1 ∧ ∃ a : Fˣ, g.val.left = GeneralLinearGroup.scalar (Fin d) a)
    (htop : matrixProjectiveImage Q = ⊤) (e : (↥K ⧸ Subgroup.center ↥K) ≃* ProjOrthDerived Q)
    (hlayS : ∀ s : ↥K ⧸ Subgroup.center ↥K, s ^ 3 = 1 → PerfectInLayer (MulAut.conj s))
    {a : Y} (haA : a ∈ A) (ha1 : a ≠ 1) {s : ↥K ⧸ Subgroup.center ↥K}
    (hs : actHom K ⟨a, ctx.norm (ctx.le haA)⟩ = MulAut.conj s)
    {J : Subgroup Y} (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set Y)) J)
    (hcomp : CFSG.Open.IsComponentOf J (K ⊓ Subgroup.centralizer ({a} : Set Y)))
    (hBJ : B ≤ Subgroup.normalizer (J : Set Y)) (hJFC : IsLieQuot ↥J IsSpFirstClaimIdx) :
    IsStronglyLocallyOneBalanced 3 B a J := by
  classical
  have haB : a ∈ B := ctx.le haA
  have hBK : B ≤ Subgroup.normalizer (K : Set Y) := ctx.norm
  have hKq : CFSG.Open.IsQuasisimple ↥K := ctx.comp.2.2
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  haveI : NeZero d := ⟨hd.ne'⟩
  have hS := KCOrthogonalD4.conj_injective_projOrthDerived Q hQ hT
  have hat : uniAut e ⟨a, hBK haB⟩ = MulAut.conj (e s) := by
    show MulAut.congr e (actHom K ⟨a, hBK haB⟩) = _
    rw [hs, congr_conj]
  have hβ3 := uniAut_pow_three ctx.scp hBK e haB
  have hβ1 := uniAut_ne_one ctx e haA ha1
  have ht3 : (e s) ^ 3 = 1 := by
    apply hS
    rw [map_pow, map_one, ← hat]
    exact hβ3
  have ht1 : e s ≠ 1 := fun h => hβ1 (by rw [hat, h, map_one])
  have hs3 : s ^ 3 = 1 := e.injective (by rw [map_pow, map_one]; exact ht3)
  have hlay : PerfectInLayer (MulAut.conj (e s)) :=
    LieSemisimple.perfectInLayer_of_congr e.symm _
      (by rw [congr_conj, MulEquiv.symm_apply_apply]; exact hlayS s hs3)
  obtain ⟨x, hx, hx3⟩ := OrthFix.exists_lift_orderOf_three hQ (orderOf_eq_prime ht3 ht1)
  have hat' : uniAut e ⟨a, hBK haB⟩ = MulAut.conj (piOrth Q x) := by rw [hat, hx]
  have hlay' : PerfectInLayer (uniAut e ⟨a, hBK haB⟩) := by
    rw [hat', hx]
    exact hlay
  obtain ⟨-, hJc, -⟩ := uni_component e Nat.prime_three hKq hZ (hBK haB) hlay' hJ
  rw [hat', OrthFix.fixSubgroup_conj_eq_centralizer] at hJc
  rcases hC F hF d hd Q hQ hT n hdn h4 hV x hx3 _ hJc with ⟨hmem, hm2, hL⟩ | ⟨i, hi, ⟨eL⟩⟩
  · by_cases hbad :
      primaryMultiplicity (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap (X ^ 2 + X + 1) = 2 ∨
      (primaryMultiplicity (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap (X ^ 2 + X + 1) = 3 ∧
        Nat.card F = 2)
    · exact (false_of_small_block hQ hF e hJK hx3 hmem hL hbad hJFC).elim
    · have hne2 : primaryMultiplicity (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap
          (X ^ 2 + X + 1) ≠ 2 := fun h2 => hbad (Or.inl h2)
      have h3 : 3 ≤ primaryMultiplicity (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap
          (X ^ 2 + X + 1) := by omega
      have hE : ∀ b : ↥B, MulAut.congr (coordBridge Q hd).symm (uniAut e ⟨b, hBK b.2⟩) ∈
          matrixProjectiveImage Q := fun b => by
        rw [htop]
        exact Subgroup.mem_top _
      exact FirstClaim.isStronglyLocallyOneBalanced_of_blockFrame ctx.scp hBK hZ e hcomp.2.2 hJK hBJ
        (hD Y K B J ctx.scp hBK hZ F hF d hd Q hQ hT hker e hE x hx3 hmem h3
          (fun h => hbad (Or.inr h)) hL a haB hat')
  · obtain ⟨eψ⟩ := FirstClaim.nonempty_centerQuot_of_image e hJK hcomp.2.2.1 (MulEquiv.refl _)
    exact Glue.stronglyLocallyOneBalanced_of_ih ctx hIH haA ha1 hJ hcomp.2.2 hBJ
      (Glue.bal207PlusHyp_of_isLieQuot (Glue.isLieQuot_subgroupOf (hJ.1.trans inf_le_right)
        (isLieQuot_bal207_of_fixed ⟨i, hi, ⟨eψ.trans eL⟩⟩ hJFC)))

theorem orthFC_outer (hField : OrthFieldComps)
    {G : ∀ (S : Type) [Group S], MulAut S → Prop} {Y : Type} [Group Y] [Finite Y]
    {K B A : Subgroup Y} (ctx : Bal207PlusCtx G 3 K B A) (hIH : Bal207PlusIH G A)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥K)))
    {S : Type} [Group S] (e : (↥K ⧸ Subgroup.center ↥K) ≃* S)
    {t : StatedLieTag} {n : ℕ} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (hn : 5 ≤ n)
    (hP : (t = .POmegaPlus ∧ Even n) ∨ (t = .POmegaMinus ∧ Odd n))
    (hM : StatedClassicalModel S t n 2 3) {a : Y} (haA : a ∈ A)
    (hout : ∀ s : S, MulAut.conj s ≠ uniAut e ⟨a, ctx.norm (ctx.le haA)⟩)
    {J : Subgroup Y} (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set Y)) J)
    (hcomp : CFSG.Open.IsComponentOf J (K ⊓ Subgroup.centralizer ({a} : Set Y)))
    (hBJ : B ≤ Subgroup.normalizer (J : Set Y)) (ha1 : a ≠ 1) :
    IsStronglyLocallyOneBalanced 3 B a J := by
  classical
  have haB : a ∈ B := ctx.le haA
  have hBK : B ≤ Subgroup.normalizer (K : Set Y) := ctx.norm
  have hKq : CFSG.Open.IsQuasisimple ↥K := ctx.comp.2.2
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hβ3 := uniAut_pow_three ctx.scp hBK e haB
  obtain ⟨hlay, J', hJ'u, hJ'Z, hJ'M⟩ :=
    hField S t n ht hn hM (uniAut e ⟨a, hBK haB⟩) hβ3 (fun s => (hout s))
  obtain ⟨-, hJc, -⟩ := uni_component e Nat.prime_three hKq hZ (hBK haB) hlay hJ
  have hJJ' := hJ'u _ hJc
  obtain ⟨eψ⟩ := FirstClaim.nonempty_centerQuot_of_image e hJK hcomp.2.2.1
    (MulEquiv.subgroupCongr hJJ')
  have eZ : (↥J' ⧸ Subgroup.center ↥J') ≃* ↥J' :=
    (QuotientGroup.quotientMulEquivOfEq hJ'Z).trans QuotientGroup.quotientBot
  obtain ⟨dd, hdd, ⟨eJ'⟩⟩ : ∃ dd : TauCeti.ValidLieTypeIndex,
      (Bal207Index 3 dd.1 ∧ ¬ IsG2EightIndex dd.1) ∧
        Nonempty (↥J' ≃* (TauCeti.CFSGIndex.lie dd).Group) := by
    rcases hP with ⟨rfl, hev⟩ | ⟨rfl, hodd⟩
    · exact bal207Index_of_model_plus hJ'M hev (by obtain ⟨k, hk⟩ := hev; omega)
    · exact bal207Index_of_model_minus hJ'M hodd hn
  exact Glue.stronglyLocallyOneBalanced_of_ih ctx hIH haA ha1 hJ hcomp.2.2 hBJ
    (Glue.bal207PlusHyp_of_isLieQuot (Glue.isLieQuot_subgroupOf (hJ.1.trans inf_le_right)
      ⟨dd, hdd, ⟨eψ.trans (eZ.trans eJ')⟩⟩))

end CFSG.HardMathSupport.Dickson.Bal207.OrthFC

end
