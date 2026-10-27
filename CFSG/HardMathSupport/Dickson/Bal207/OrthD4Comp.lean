module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Semilin
public import CFSG.HardMathSupport.Dickson.Bal207.OrthFam
import CFSG.HardMathSupport.Dickson.Bal207.OrthFCCases
import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Image
import CFSG.HardMathSupport.Dickson.Bal207.OrthInnerField
import CFSG.HardMathSupport.Dickson.Bal207.OrthEightBasic
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaPlus
import CFSG.LargeExtraspecial.A2ModOrd
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFix

open Polynomial Module QuadraticMap CFSG.Open CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.HardMathSupport.Dickson.Bal207.Uni
  CFSG.HardMathSupport.Dickson.I271
open CFSG.GroupTheory.WeirSylow (IsPlusType nonempty_isometry_quadPlus)
open CFSG.ComponentClassification.CatFC (omegaPlus_isPlusType)

theorem factorization_two_ordD_two {n : ℕ} (hn : 1 ≤ n) :
    (ordD n 2).factorization 2 = n * (n - 1) ∧ (ordTwistedD n 2).factorization 2 = n * (n - 1) := by
  have hP : Odd (∏ i ∈ Finset.Icc 1 (n - 1), (2 ^ (2 * i) - 1 : ℕ)) :=
    Finset.prod_induction _ Odd (fun _ _ h₁ h₂ => h₁.mul h₂) odd_one fun i hi =>
      Nat.Even.sub_odd Nat.one_le_two_pow
        ((Nat.even_pow' (by have := (Finset.mem_Icc.mp hi).1; omega)).mpr even_two) odd_one
  have hE : Even (2 ^ n : ℕ) := (Nat.even_pow' (by omega)).mpr even_two
  refine ⟨factorization_two_of_eq
      (u := (2 ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (2 ^ (2 * i) - 1))
      (by rw [CFSG.LargeExtraspecial.A2Mod.Ord.ordD_two_eq hn, mul_assoc])
      ((Nat.Even.sub_odd Nat.one_le_two_pow hE odd_one).mul hP),
    factorization_two_of_eq
      (u := (2 ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (2 ^ (2 * i) - 1))
      (by rw [CFSG.LargeExtraspecial.A2Mod.Ord.ordTwistedD_two_eq hn, mul_assoc])
      (hE.add_one.mul hP)⟩

theorem mul_sub_one_ne_thirty_six (n : ℕ) : n * (n - 1) ≠ 36 := by
  intro h
  have hn8 : n < 8 := by
    by_contra hge
    push Not at hge
    have : 8 * 7 ≤ n * (n - 1) := Nat.mul_le_mul hge (by omega)
    omega
  interval_cases n <;> omega

theorem center_eq_bot_of_mulEquiv_of_eq_bot {G H : Type*} [Group G] [Group H] (E : G ≃* H)
    (h : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : E z ∈ Subgroup.center H := Subgroup.mem_center_iff.mpr fun y => by
    obtain ⟨w, rfl⟩ := E.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w]
  rw [h, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact E.injective (h1.trans (map_one E).symm)

theorem exists_centerQuot_mulEquiv {J P : Type*} [Group J] [Group P] (φ : J →* P)
    (hs : Function.Surjective φ) (hk : φ.ker ≤ Subgroup.center J)
    (hZ : Subgroup.center P = ⊥) :
    ∃ Θ : (J ⧸ Subgroup.center J) ≃* P, ∀ j, Θ (QuotientGroup.mk j) = φ j := by
  have hle : Subgroup.center J ≤ φ.ker := fun z hz => by
    have h1 : φ z ∈ Subgroup.center P := Subgroup.mem_center_iff.mpr fun y => by
      obtain ⟨w, rfl⟩ := hs y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w]
    rw [hZ, Subgroup.mem_bot] at h1
    exact MonoidHom.mem_ker.mpr h1
  have hinj : Function.Injective (QuotientGroup.lift (Subgroup.center J) φ hle) := by
    rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H j =>
      rw [QuotientGroup.lift_mk] at hq
      exact (QuotientGroup.eq_one_iff j).mpr (hk (MonoidHom.mem_ker.mpr hq))
  have hsurj : Function.Surjective (QuotientGroup.lift (Subgroup.center J) φ hle) := fun y => by
    obtain ⟨j, rfl⟩ := hs y
    exact ⟨QuotientGroup.mk j, rfl⟩
  exact ⟨MulEquiv.ofBijective _ ⟨hinj, hsurj⟩, fun j => rfl⟩

theorem semilinD4EightAut_fixed {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    (hd : 0 < d) {Q : QuadraticForm F (Fin d → F)} (hQ : (polarBilin Q).Nondegenerate)
    (hF : Nat.card F = 8) (x : orthDerived Q) (hx3 : orderOf x = 3)
    (hW : finrank F (fixedSpace (x : (Fin d → F) ≃ₗ[F] (Fin d → F))) = 8)
    (hpar : IsPlusType Q ↔ Even (finrank F (Fin d → F) / 2))
    {β : MulAut (ProjOrthDerived Q)} (hβx : β (piOrth Q x) = piOrth Q x)
    (hβ : MulAut.congr (coordBridge Q hd).symm β ∈ matrixProjectiveImage Q)
    (γ : MulAut ↥(fixedComponentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F))))
    (hγ : ∀ y, (γ y : ProjOrthDerived Q) = β y) :
    SemilinD4EightAut ↥(fixedComponentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F))) γ := by
  classical
  haveI : NeZero d := ⟨hd.ne'⟩
  have hpl : (3 : ℕ) ≠ ringChar F := by
    rw [ringChar.eq F 2]
    norm_num
  have hx := oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQ x hx3
  obtain ⟨σ, Fs, hFs, μ, hμ, hQF, hconj⟩ := exists_semilin_of_mem_matrixProjectiveImage Q hd β hβ
  let cj : orthDerived Q → orthDerived Q := fun g =>
    ⟨semilinConj Fs σ hFs g, semilinConj_mem_orthDerived Fs σ hFs μ hQF g.2⟩
  have hcj : ∀ g : orthDerived Q, β (piOrth Q g) = piOrth Q (cj g) := fun g =>
    hconj g (cj g) fun v => rfl
  have hxx : cj x = x := piOrth_injective hQ ((hcj x).symm.trans hβx)
  have hc : ∀ v, Fs ((x : (Fin d → F) ≃ₗ[F] (Fin d → F)) v) =
      (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (Fs v) := fun v => by
    have h1 := DFunLike.congr_fun (congrArg Subtype.val hxx) (Fs v)
    rw [← h1]
    show Fs ((x : (Fin d → F) ≃ₗ[F] (Fin d → F)) v) =
      Fs ((x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (Fs.symm (Fs v)))
    rw [AddEquiv.symm_apply_apply]
  have hWn := hx.polarBilin_fixed_nondegenerate
  have hplusW : IsPlusType
      (Q.comp (fixedSpace (x : (Fin d → F) ≃ₗ[F] (Fin d → F))).subtype) :=
    (OrthEight.isPlusType_fixedSpace_iff hF hx hpar).2 (by rw [hW]; decide)
  obtain ⟨ι₁⟩ := nonempty_isometry_quadPlus hWn (n := 4) (by rw [hW]) hplusW
  have hreg := regular_coordinateQuadPlus 4 F (by norm_num)
  obtain ⟨ι₂⟩ := nonempty_isometry_quadPlus hreg.1 (n := 4) (Module.finrank_fin_fun F)
    (omegaPlus_isPlusType 4 F)
  have hγ' : ∀ g : ↥(supportedFixedDerived Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F))),
      ∃ g' : ↥(supportedFixedDerived Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F))),
        (∀ v, (g' : (Fin d → F) ≃ₗ[F] (Fin d → F)) v =
          Fs ((g : (Fin d → F) ≃ₗ[F] (Fin d → F)) (Fs.symm v))) ∧
        γ (fixRho hQ hx g) = fixRho hQ hx g' := by
    intro g
    refine ⟨(fixRho hQ hx).symm (γ (fixRho hQ hx g)), fun v => ?_,
      ((fixRho hQ hx).apply_symm_apply _).symm⟩
    have h1 := congrArg Subtype.val ((fixRho hQ hx).apply_symm_apply (γ (fixRho hQ hx g)))
    rw [hγ, coe_fixRho, coe_fixRho, hcj] at h1
    have h2 := congrArg Subtype.val (piOrth_injective hQ h1)
    exact DFunLike.congr_fun h2 v
  exact semilinD4EightAut_of_mem_image hF _
    (mulAut_congr_mem_image_of_semilin hQ hx (ι₁.trans ι₂.symm) hreg.1 hFs hμ hQF hc γ hγ')

theorem semilinD4EightAut_of_inner {G : ∀ (S : Type) [Group S], MulAut S → Prop} {X : Type}
    [Group X] [Finite X] {K B A : Subgroup X} (ctx : Bal207PlusCtx G 3 K B A)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥K))) {t : StatedLieTag} {n f : ℕ}
    (hf : f = 1 ∨ f = 3) (hn : 5 ≤ n)
    (hcase : (t = .POmegaPlus ∧ Even n ∧ (6 ≤ n ∨ (n = 4 ∧ f = 1))) ∨
      (t = .POmegaMinus ∧ Odd n ∧ 5 ≤ n))
    (hM : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) t n 2 f) {a : X} (haA : a ∈ A)
    (ha1 : a ≠ 1) {s : ↥K ⧸ Subgroup.center ↥K}
    (hs : actHom K ⟨a, ctx.norm (ctx.le haA)⟩ = MulAut.conj s) {J : Subgroup X}
    (hJ : CFSG.Open.GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J)
    (hJc : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordD 4 8) {b : X} (hbB : b ∈ B)
    (hbJ : b ∈ Subgroup.normalizer (J : Set X)) :
    SemilinD4EightAut (↥J ⧸ Subgroup.center ↥J) (actHom J ⟨b, hbJ⟩) := by
  classical
  have haB : a ∈ B := ctx.le haA
  have hBK : B ≤ Subgroup.normalizer (K : Set X) := ctx.norm
  have hKq : CFSG.Open.IsQuasisimple ↥K := ctx.comp.2.2
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have ht : t = .POmegaPlus ∨ t = .POmegaMinus := by
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨F, _, _, _, Q, e, hFc, hQ, hT, hV, htop, -⟩ := exists_coords_of_model hcase hM
  have hd : 0 < 2 * n := by omega
  haveI : NeZero (2 * n) := ⟨hd.ne'⟩
  have hS := CFSG.RankThree.PartOne.KCOrthogonalD4.conj_injective_projOrthDerived Q hQ hT
  have hat : uniAut e ⟨a, hBK haB⟩ = MulAut.conj (e s) := by
    show MulAut.congr e (actHom K ⟨a, hBK haB⟩) = _
    rw [hs, mulAut_congr_conj]
  have hβ3 := OrthFC.uniAut_pow_three ctx.scp hBK e haB
  have hβ1 := OrthFC.uniAut_ne_one ctx e haA ha1
  have ht3 : (e s) ^ 3 = 1 := by
    apply hS
    rw [map_pow, map_one, ← hat]
    exact hβ3
  have ht1 : e s ≠ 1 := fun h => hβ1 (by rw [hat, h, map_one])
  have hs3 : s ^ 3 = 1 := e.injective (by rw [map_pow, map_one]; exact ht3)
  have hlay : PerfectInLayer (MulAut.conj (e s)) :=
    LieSemisimple.perfectInLayer_of_congr e.symm _
      (by
        rw [mulAut_congr_conj, MulEquiv.symm_apply_apply]
        exact LieSemisimple.perfectInLayer_conj_omega (Or.inr ht) hM Nat.prime_three
          (by norm_num) (by norm_num) s hs3)
  obtain ⟨x, hx, hx3⟩ := exists_lift_orderOf_three hQ (orderOf_eq_prime ht3 ht1)
  have hat' : uniAut e ⟨a, hBK haB⟩ = MulAut.conj (piOrth Q x) := by rw [hat, hx]
  have hlay' : PerfectInLayer (uniAut e ⟨a, hBK haB⟩) := by
    rw [hat', hx]
    exact hlay
  obtain ⟨hcomp, hJc', -⟩ := uni_component e Nat.prime_three hKq hZ (hBK haB) hlay' hJ
  rw [hat', fixSubgroup_conj_eq_centralizer] at hJc'
  obtain ⟨eq⟩ := FirstClaim.nonempty_centerQuot_of_image e hJK hcomp.2.2.1 (MulEquiv.refl _)
  have hcard : Nat.card (↥((J.comap K.subtype).map (uniMap e)) ⧸
      Subgroup.center ↥((J.comap K.subtype).map (uniMap e))) = ordD 4 8 := by
    rw [← Nat.card_congr eq.toEquiv, hJc]
  have hF' : Nat.card F = 2 ∨ Nat.card F = 8 := by
    rcases hf with rfl | rfl
    · exact Or.inl (by rw [hFc]; norm_num)
    · exact Or.inr (by rw [hFc]; norm_num)
  obtain ⟨hF8, hW8, hψ⟩ := eq_fixedComponentImage_of_card hF' hQ x hx3 hJc' hcard
  have hpl : (3 : ℕ) ≠ ringChar F := by
    rw [ringChar.eq F 2]
    norm_num
  have hxo := oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQ x hx3
  have hWn := hxo.polarBilin_fixed_nondegenerate
  haveI : Nontrivial ↥(fixedSpace (x : (Fin (2 * n) → F) ≃ₗ[F] (Fin (2 * n) → F))) :=
    Module.nontrivial_of_finrank_pos (R := F) (by rw [hW8]; norm_num)
  have hZW := center_orthDerived_eq_bot hWn
    (exists_threeSingular_of_dim _ hWn (m := 4) (by norm_num) (by rw [hW8]))
  have hZP : Subgroup.center
      ↥(fixedComponentImage Q (x : (Fin (2 * n) → F) ≃ₗ[F] (Fin (2 * n) → F))) = ⊥ :=
    center_eq_bot_of_mulEquiv_of_eq_bot ((fixRho hQ hxo).symm.trans (fixRestr hxo)) hZW
  have hk : ((MulEquiv.subgroupCongr hψ).toMonoidHom.comp (uniRestr e hJK)).ker ≤
      Subgroup.center ↥J := fun j hj => by
    have h0 : (MulEquiv.subgroupCongr hψ) (uniRestr e hJK j) = 1 := MonoidHom.mem_ker.mp hj
    exact ker_uniRestr_le_center e hJK ((MulEquiv.map_eq_one_iff _).mp h0)
  obtain ⟨Θ, hΘ₀⟩ := exists_centerQuot_mulEquiv
    ((MulEquiv.subgroupCongr hψ).toMonoidHom.comp (uniRestr e hJK))
    ((MulEquiv.subgroupCongr hψ).surjective.comp (uniRestr_surjective e hJK)) hk hZP
  have hΘ : ∀ j : ↥J, (Θ (QuotientGroup.mk j) : ProjOrthDerived Q) =
      uniMap e (Subgroup.inclusion hJK j) := fun j => by
    rw [hΘ₀]
    rfl
  have hγ : ∀ y, (MulAut.congr Θ (actHom J ⟨b, hbJ⟩) y : ProjOrthDerived Q) =
      uniAut e ⟨b, hBK hbB⟩ y := by
    intro y
    obtain ⟨q, rfl⟩ := Θ.surjective y
    induction q using QuotientGroup.induction_on with
    | H j =>
      show (Θ (actHom J ⟨b, hbJ⟩ (Θ.symm (Θ (QuotientGroup.mk j)))) : ProjOrthDerived Q) = _
      rw [MulEquiv.symm_apply_apply, actHom_mk, hΘ, hΘ]
      exact uniMap_conj e (hBK hbB) (Subgroup.inclusion hJK j)
        (hJK (J.normalizerMonoidHom ⟨b, hbJ⟩ j).2)
  have hβx : uniAut e ⟨b, hBK hbB⟩ (piOrth Q x) = piOrth Q x := by
    have hc : a * b = b * a :=
      congrArg Subtype.val (ctx.scp.2.1.1.is_comm.comm (⟨a, haB⟩ : ↥B) ⟨b, hbB⟩)
    have hab : (⟨a, hBK haB⟩ : ↥(Subgroup.normalizer (K : Set X))) * ⟨b, hBK hbB⟩ =
        ⟨b, hBK hbB⟩ * ⟨a, hBK haB⟩ := Subtype.ext hc
    have hcomm := congrArg (uniAut e) hab
    rw [map_mul, map_mul, hat'] at hcomm
    apply hS
    ext y
    have h := DFunLike.congr_fun hcomm ((uniAut e ⟨b, hBK hbB⟩)⁻¹ y)
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.apply_inv_self, map_mul,
      map_inv] at h
    simp only [MulAut.conj_apply]
    exact h.symm
  have hE : MulAut.congr (coordBridge Q hd).symm (uniAut e ⟨b, hBK hbB⟩) ∈
      matrixProjectiveImage Q := by
    rw [htop hn]
    exact Subgroup.mem_top _
  have hpar : IsPlusType Q ↔ Even (finrank F (Fin (2 * n) → F) / 2) := by
    rw [Module.finrank_fin_fun, Nat.mul_div_cancel_left n two_pos]
    exact hV
  have hsem := semilinD4EightAut_fixed hd hQ hF8 x hx3 hW8 hpar hβx hE
    (MulAut.congr Θ (actHom J ⟨b, hbJ⟩)) hγ
  have h2 := hsem.of_mulEquiv Θ.symm
  have h3 : MulAut.congr Θ.symm (MulAut.congr Θ (actHom J ⟨b, hbJ⟩)) = actHom J ⟨b, hbJ⟩ := by
    ext y
    simp [MulAut.congr_apply]
  rwa [h3] at h2

theorem orthD4EightComp_holds : OrthD4EightComp := by
  intro G X _ _ K B A ctx hK hZ a haA ha1 J hJ _ hJD
  classical
  refine Glue.noTrialityOn_subgroupOf (fun g _ h => nonSemilinD4Eight_congr g h)
    (hJ.1.trans inf_le_right) ?_
  intro φ hφ hφ'
  obtain ⟨b, hbJ, hbB, rfl⟩ := mem_autImage.1 hφ
  apply hφ'.2
  have haB : a ∈ B := ctx.le haA
  have hBK : B ≤ Subgroup.normalizer (K : Set X) := ctx.norm
  have hKq : CFSG.Open.IsQuasisimple ↥K := ctx.comp.2.2
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  obtain ⟨dJ, hdJ, ⟨eJ⟩⟩ := hJD
  have hJc : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordD 4 8 := by
    rw [Nat.card_congr eJ.toEquiv, OrthFC.card_eq_ordD_of_isD4EightIdx dJ hdJ]
  obtain ⟨t, n, f, hf, hcase, hM⟩ := exists_model_of_famOrth hK
  have hn5 : 5 ≤ n := by
    rcases hcase with ⟨rfl, -, h6 | ⟨rfl, rfl⟩⟩ | ⟨-, -, h5⟩
    · omega
    · exfalso
      have h1 := FirstClaim.card_centerQuot_dvd_card_image
        (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)) hJK
      have h2 : Nat.card ((J.comap K.subtype).map
          (uniMap (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)))) ∣
          Nat.card (↥K ⧸ Subgroup.center ↥K) := Subgroup.card_subgroup_dvd_card _
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hM).2.2.2.1 rfl] at h2
      rw [hJc] at h1
      exact (by unfold ordD; decide : ¬ ordD 4 8 ∣ ordD 4 (2 ^ 1)) (h1.trans h2)
    · exact h5
  have ht : t = .POmegaPlus ∨ t = .POmegaMinus := by
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hβ3 : actHom K ⟨a, hBK haB⟩ ^ 3 = 1 := by
    rw [← OrthFC.uniAut_refl]
    exact OrthFC.uniAut_pow_three ctx.scp hBK (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)) haB
  by_cases hin : ∃ s : ↥K ⧸ Subgroup.center ↥K, actHom K ⟨a, hBK haB⟩ = MulAut.conj s
  · obtain ⟨s, hs⟩ := hin
    exact semilinD4EightAut_of_inner ctx hZ hf hn5 hcase hM haA ha1 hs hJ hJc hbB hbJ
  · push Not at hin
    exfalso
    rcases hf with rfl | rfl
    · obtain ⟨s, hs⟩ := orthTwo_inner ht hn5 hM hβ3
      exact hin s hs.symm
    · obtain ⟨hlay, J₀, hJ₀u, hJ₀Z, hJ₀M⟩ :=
        orthField_comps ht hn5 hM hβ3 fun s h => hin s h.symm
      have hlay' : PerfectInLayer
          (uniAut (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)) ⟨a, hBK haB⟩) := by
        rw [OrthFC.uniAut_refl]
        exact hlay
      obtain ⟨hcomp, hJc', -⟩ := uni_component (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K))
        Nat.prime_three hKq hZ (hBK haB) hlay' hJ
      rw [OrthFC.uniAut_refl] at hJc'
      obtain ⟨eψ⟩ := FirstClaim.nonempty_centerQuot_of_image
        (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)) hJK hcomp.2.2.1
        (MulEquiv.subgroupCongr (hJ₀u _ hJc'))
      have hcard : Nat.card ↥J₀ = ordD 4 8 := by
        rw [← hJc, Nat.card_congr eψ.toEquiv, Nat.card_congr
          ((QuotientGroup.quotientMulEquivOfEq hJ₀Z).trans QuotientGroup.quotientBot).toEquiv]
      have h2n : (Nat.card ↥J₀).factorization 2 = n * (n - 1) := by
        rcases ht with rfl | rfl
        · rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hJ₀M).2.2.2.1 rfl, pow_one]
          exact (factorization_two_ordD_two (by omega)).1
        · rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hJ₀M).2.2.2.2 rfl, pow_one]
          exact (factorization_two_ordD_two (by omega)).2
      rw [hcard, factorization_two_ordD_four_eight] at h2n
      exact mul_sub_one_ne_thirty_six n h2n.symm

end CFSG.HardMathSupport.Dickson.Bal207.OrthFix

end
