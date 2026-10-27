module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
import CFSG.CGT.PushingUpLit.BHS6.ThreeEightSL
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.Quasithin CFSG.RankThree.PartOne Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open CFSG.Quasithin.AutOn
open CFSG.QuasithinUnique
open CFSG.CGT.PushingUpLit.BHS6
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement IsMulCommutative

variable {Ω : Type} [Group Ω]

private noncomputable def gomi410eU_bnsl (B W : Subgroup Ω) [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) :
    ↥(commV (autOn B W)) ≃* ↥(blockU B) :=
  (Subgroup.equivMapOfInjective (commV (autOn B W)) W.subtype W.subtype_injective).trans
    ((MulEquiv.subgroupCongr (map_commV_autOn_eq hBW)).trans
      (MulEquiv.subgroupCongr (show ⁅W, B⁆ = blockU B from hU.symm)))

private theorem gomi410eU_coe_bnsl (B W : Subgroup Ω) [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) (u : ↥(commV (autOn B W))) :
    ((gomi410eU_bnsl B W hBW hU u : ↥(blockU B)) : Ω) = ((u : ↥(commV (autOn B W))) : W) :=
  rfl

private theorem gomi410eU_symm_coe_bnsl (B W : Subgroup Ω) [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) (u : ↥(blockU B)) :
    (((gomi410eU_bnsl B W hBW hU).symm u : ↥(commV (autOn B W))) : W) = (u : Ω) := by
  have h := gomi410eU_coe_bnsl B W hBW hU ((gomi410eU_bnsl B W hBW hU).symm u)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

private noncomputable def gomi410eQ0_bnsl (K : Type) [Field K] :
    (↥(⊤ : Subgroup (Multiplicative (Fin 2 → K)))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin 2 → K))).subgroupOf ⊤ ≃*
      ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K))) :=
  (QuotientGroup.quotientMulEquivOfEq
      (Subgroup.bot_subgroupOf (G := Multiplicative (Fin 2 → K)) (H := ⊤))).trans
    QuotientGroup.quotientBot

private noncomputable def gomi410eQ_bnsl (K : Type) [Field K] :
    (↥(⊤ : Subgroup (Multiplicative (Fin 2 → K)))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin 2 → K))).subgroupOf ⊤ ≃*
      Multiplicative (Fin 2 → K) :=
  (gomi410eQ0_bnsl K).trans Subgroup.topEquiv

private theorem gomi410eQ0_mk_bnsl (K : Type) [Field K]
    (a : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K)))) :
    gomi410eQ0_bnsl K (QuotientGroup.mk a) = a := by
  simp only [gomi410eQ0_bnsl, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

private theorem gomi410eQ_mk_bnsl (K : Type) [Field K]
    (a : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K)))) :
    gomi410eQ_bnsl K (QuotientGroup.mk a) = (a : Multiplicative (Fin 2 → K)) := by
  simp only [gomi410eQ_bnsl, MulEquiv.trans_apply, gomi410eQ0_mk_bnsl]
  rfl

private noncomputable def gomi410alpha_bnsl (B W : Subgroup Ω) [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω)) {K : Type} [Field K]
    (eπ : ↥(StatedSL 2 K) ≃* ↥(autOn B W)) :
    ↥B →* Matrix.SpecialLinearGroup (Fin 2) K :=
  (specialLinearGroupEquivStatedSL 2 K).symm.toMonoidHom.comp
    (eπ.symm.toMonoidHom.comp (actOnRange W B hBW))

private noncomputable def gomi410beta_bnsl (B W : Subgroup Ω) [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) {K : Type} [Field K]
    (β₀ : ↥(commV (autOn B W)) →*
      (↥(⊤ : Subgroup (Multiplicative (Fin 2 → K)))) ⧸
        (⊥ : Subgroup (Multiplicative (Fin 2 → K))).subgroupOf ⊤) :
    ↥(blockU B) →* Multiplicative (Fin 2 → K) :=
  (gomi410eQ_bnsl K).toMonoidHom.comp
    (β₀.comp (gomi410eU_bnsl B W hBW hU).symm.toMonoidHom)

private theorem gomi410alpha_surjective_bnsl (B W : Subgroup Ω) [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω)) {K : Type} [Field K]
    (eπ : ↥(StatedSL 2 K) ≃* ↥(autOn B W)) :
    Function.Surjective (gomi410alpha_bnsl B W hBW eπ) :=
  (specialLinearGroupEquivStatedSL 2 K).symm.surjective.comp
    (eπ.symm.surjective.comp (actOnRange_surjective W B hBW))

private theorem gomi410alpha_ker_bnsl (B W : Subgroup Ω) [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hker : B ⊓ Subgroup.centralizer (W : Set Ω) = pCoreOf 2 B)
    {K : Type} [Field K] (eπ : ↥(StatedSL 2 K) ≃* ↥(autOn B W)) :
    (gomi410alpha_bnsl B W hBW eπ).ker = CFSG.pCore 2 ↥B := by
  ext b
  rw [MonoidHom.mem_ker]
  change (specialLinearGroupEquivStatedSL 2 K).symm
      (eπ.symm (actOnRange W B hBW b)) = 1 ↔ b ∈ CFSG.pCore 2 ↥B
  rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker,
    ker_actOnRange W B hBW, Subgroup.mem_subgroupOf, hker, CFSG.mem_openPCoreOf_iff]

private theorem gomi410beta_surjective_bnsl (B W : Subgroup Ω) [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) {K : Type} [Field K]
    (β₀ : ↥(commV (autOn B W)) →*
      (↥(⊤ : Subgroup (Multiplicative (Fin 2 → K)))) ⧸
        (⊥ : Subgroup (Multiplicative (Fin 2 → K))).subgroupOf ⊤)
    (hβ₀s : Function.Surjective β₀) :
    Function.Surjective (gomi410beta_bnsl B W hBW hU β₀) :=
  (gomi410eQ_bnsl K).surjective.comp
    (hβ₀s.comp (gomi410eU_bnsl B W hBW hU).symm.surjective)

private theorem gomi410beta_ker_bnsl (B W : Subgroup Ω) [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) {K : Type} [Field K]
    (β₀ : ↥(commV (autOn B W)) →*
      (↥(⊤ : Subgroup (Multiplicative (Fin 2 → K)))) ⧸
        (⊥ : Subgroup (Multiplicative (Fin 2 → K))).subgroupOf ⊤)
    (hβ₀k : ∀ x : ↥(commV (autOn B W)),
      β₀ x = 1 ↔ (x : W) ∈ gomiWXKer (autOn B W)) :
    (gomi410beta_bnsl B W hBW hU β₀).ker =
      (blockZ B).subgroupOf (blockU B) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change gomi410eQ_bnsl K (β₀ ((gomi410eU_bnsl B W hBW hU).symm u)) = 1 ↔
    (u : Ω) ∈ blockZ B
  have hxcomm : ((gomi410eU_bnsl B W hBW hU).symm u : W) ∈ commV (autOn B W) :=
    ((gomi410eU_bnsl B W hBW hU).symm u).2
  rw [MulEquiv.map_eq_one_iff, hβ₀k, gomiWXKer, Subgroup.mem_inf,
    show (((gomi410eU_bnsl B W hBW hU).symm u : W) ∈ commV (autOn B W)) = True from
      propext (iff_true_intro hxcomm), true_and,
    fixV_autOn_eq hBW, Subgroup.mem_subgroupOf, gomi410eU_symm_coe_bnsl,
    blockZ, Subgroup.mem_inf]
  exact ⟨fun h => ⟨u.2, h⟩, fun h => h.2⟩

private abbrev gomi410Quot_bnsl (K : Type) [Field K] : Type :=
  (↥(⊤ : Subgroup (Multiplicative (Fin 2 → K)))) ⧸
    (⊥ : Subgroup (Multiplicative (Fin 2 → K))).subgroupOf ⊤

private abbrev gomi410Sec_bnsl (K : Type) [Field K] : Type :=
  ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K)))

private abbrev gomi410BetaEquiv_bnsl {B W : Subgroup Ω} [IsMulCommutative ↥W]
    {K : Type} [Field K] (π : ↥(StatedSL 2 K) →* ↥(autOn B W))
    (β₀ : ↥(commV (autOn B W)) →* gomi410Quot_bnsl K) : Prop :=
  ∀ (γ : ↥(StatedSL 2 K)) (u : ↥(commV (autOn B W))) (m : gomi410Sec_bnsl K)
    (hu : ((π γ : ↥(autOn B W)) : MulAut W) (u : W) ∈ commV (autOn B W))
    (hm : (FFModel.nat (StatedSL 2 K)).act γ (m : Multiplicative (Fin 2 → K)) ∈
      (⊤ : Subgroup (Multiplicative (Fin 2 → K)))),
    β₀ u = QuotientGroup.mk m →
      β₀ ⟨((π γ : ↥(autOn B W)) : MulAut W) (u : W), hu⟩ =
        QuotientGroup.mk ⟨(FFModel.nat (StatedSL 2 K)).act γ
          (m : Multiplicative (Fin 2 → K)), hm⟩

private theorem gomi410beta_setup_bnsl
    (B W : Subgroup Ω) [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) {K : Type} [Field K]
    (π : ↥(StatedSL 2 K) →* ↥(autOn B W))
    (eπ : ↥(StatedSL 2 K) ≃* ↥(autOn B W))
    (hπsymm : ∀ g : ↥(autOn B W), π (eπ.symm g) = g)
    (hreal : (FFModel.nat (StatedSL 2 K)).RealizesVia (autOn B W)
      (commV (autOn B W)) (gomiWXKer (autOn B W)) π)
    (ℓ : ↥B) (u v : ↥(blockU B)) (hv : (v : Ω) = (ℓ : Ω) * (u : Ω) * (ℓ : Ω)⁻¹) :
    ∃ (γ : ↥(StatedSL 2 K)) (x y : ↥(commV (autOn B W))),
      γ = eπ.symm (actOnRange W B hBW ℓ) ∧
      x = (gomi410eU_bnsl B W hBW hU).symm u ∧
      y = (gomi410eU_bnsl B W hBW hU).symm v ∧
      y = ⟨((π γ : ↥(autOn B W)) : MulAut W) (x : W),
        hreal.2.2.2.1 (π γ) x x.2⟩ := by
  let g : ↥(autOn B W) := actOnRange W B hBW ℓ
  let x : ↥(commV (autOn B W)) := (gomi410eU_bnsl B W hBW hU).symm u
  let y : ↥(commV (autOn B W)) := (gomi410eU_bnsl B W hBW hU).symm v
  refine ⟨eπ.symm g, x, y, rfl, rfl, rfl, ?_⟩
  have hπγ : π (eπ.symm g) = g := hπsymm g
  have hxΩ : ((x : W) : Ω) = (u : Ω) := gomi410eU_symm_coe_bnsl B W hBW hU u
  have hyΩ : ((y : W) : Ω) = (v : Ω) := gomi410eU_symm_coe_bnsl B W hBW hU v
  have hgx : (((g : MulAut W) (x : W) : W) : Ω) = (v : Ω) := by
    rw [show (g : MulAut W) = conjAct W ⟨(ℓ : Ω), hBW ℓ.2⟩ from rfl, coe_conjAct_apply,
      hxΩ, hv]
  apply Subtype.ext
  apply W.subtype_injective
  show ((y : W) : Ω) = ((((π (eπ.symm g) : ↥(autOn B W)) : MulAut W) (x : W) : W) : Ω)
  rw [hyΩ, hπγ]
  exact hgx.symm

private theorem gomi410beta_act_bnsl
    (B W : Subgroup Ω) [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) {K : Type} [Field K] [Finite K]
    (π : ↥(StatedSL 2 K) →* ↥(autOn B W))
    (eπ : ↥(StatedSL 2 K) ≃* ↥(autOn B W))
    (hπsymm : ∀ g : ↥(autOn B W), π (eπ.symm g) = g)
    (hreal : (FFModel.nat (StatedSL 2 K)).RealizesVia (autOn B W)
      (commV (autOn B W)) (gomiWXKer (autOn B W)) π)
    (β₀ : ↥(commV (autOn B W)) →* gomi410Quot_bnsl K)
    (hβ₀e : gomi410BetaEquiv_bnsl π β₀)
    (ℓ : ↥B) (u v : ↥(blockU B)) (hv : (v : Ω) = (ℓ : Ω) * (u : Ω) * (ℓ : Ω)⁻¹) :
    ∃ m : gomi410Sec_bnsl K,
      gomi410beta_bnsl B W hBW hU β₀ v =
        (FFModel.nat (StatedSL 2 K)).act (eπ.symm (actOnRange W B hBW ℓ))
          (m : Multiplicative (Fin 2 → K)) ∧
      (m : Multiplicative (Fin 2 → K)) = gomi410beta_bnsl B W hBW hU β₀ u := by
  obtain ⟨γ, x, y, hγ, hx, hy, hyx⟩ :=
    gomi410beta_setup_bnsl B W hBW hU π eπ hπsymm hreal ℓ u v hv
  subst γ; subst x; subst y
  let m : gomi410Sec_bnsl K :=
    gomi410eQ0_bnsl K (β₀ ((gomi410eU_bnsl B W hBW hU).symm u))
  have hmk : β₀ ((gomi410eU_bnsl B W hBW hU).symm u) = QuotientGroup.mk m := by
    symm
    apply (gomi410eQ0_bnsl K).injective
    rw [gomi410eQ0_mk_bnsl]
  have hmem : ((π (eπ.symm (actOnRange W B hBW ℓ)) : ↥(autOn B W)) : MulAut W)
      ((gomi410eU_bnsl B W hBW hU).symm u : W) ∈ commV (autOn B W) :=
    hreal.2.2.2.1 (π (eπ.symm (actOnRange W B hBW ℓ)))
      ((gomi410eU_bnsl B W hBW hU).symm u) ((gomi410eU_bnsl B W hBW hU).symm u).2
  have key := hβ₀e (eπ.symm (actOnRange W B hBW ℓ))
    ((gomi410eU_bnsl B W hBW hU).symm u) m hmem (Subgroup.mem_top _) hmk
  have hβv : gomi410beta_bnsl B W hBW hU β₀ v =
      (FFModel.nat (StatedSL 2 K)).act (eπ.symm (actOnRange W B hBW ℓ))
        (m : Multiplicative (Fin 2 → K)) := by
    change gomi410eQ_bnsl K (β₀ ((gomi410eU_bnsl B W hBW hU).symm v)) = _
    rw [hyx, key, gomi410eQ_mk_bnsl]
  exact ⟨m, hβv, rfl⟩

private theorem gomi410beta_equivariant_bnsl
    (B W : Subgroup Ω) [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) {K : Type} [Field K] [Finite K]
    (π : ↥(StatedSL 2 K) →* ↥(autOn B W))
    (eπ : ↥(StatedSL 2 K) ≃* ↥(autOn B W))
    (hπsymm : ∀ g : ↥(autOn B W), π (eπ.symm g) = g)
    (hreal : (FFModel.nat (StatedSL 2 K)).RealizesVia (autOn B W)
      (commV (autOn B W)) (gomiWXKer (autOn B W)) π)
    (β₀ : ↥(commV (autOn B W)) →* gomi410Quot_bnsl K)
    (hβ₀e : gomi410BetaEquiv_bnsl π β₀) :
    ∀ (ℓ : ↥B) (u v : ↥(blockU B)), (v : Ω) = (ℓ : Ω) * (u : Ω) * (ℓ : Ω)⁻¹ →
      Multiplicative.toAdd (gomi410beta_bnsl B W hBW hU β₀ v) =
        ((gomi410alpha_bnsl B W hBW eπ ℓ : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K).mulVec
          (Multiplicative.toAdd (gomi410beta_bnsl B W hBW hU β₀ u)) := by
  intro ℓ u v hv
  obtain ⟨m, hβv, hmβ⟩ :=
    gomi410beta_act_bnsl B W hBW hU π eπ hπsymm hreal β₀ hβ₀e ℓ u v hv
  have hα : ((gomi410alpha_bnsl B W hBW eπ ℓ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) =
      (((eπ.symm (actOnRange W B hBW ℓ) : ↥(StatedSL 2 K)) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) := by
    have h1 : specialLinearGroupEquivStatedSL 2 K (gomi410alpha_bnsl B W hBW eπ ℓ) =
        eπ.symm (actOnRange W B hBW ℓ) := by
      show specialLinearGroupEquivStatedSL 2 K ((specialLinearGroupEquivStatedSL 2 K).symm
        (eπ.symm (actOnRange W B hBW ℓ))) = eπ.symm (actOnRange W B hBW ℓ)
      rw [MulEquiv.apply_symm_apply]
    rw [← specialLinearGroupEquivStatedSL_coe 2 K
      (gomi410alpha_bnsl B W hBW eπ ℓ), h1]
  rw [hβv, hα, ← hmβ]
  rfl

private theorem isLin2Type_of_realisesVia_bnsl
    {B W : Subgroup Ω} [IsMulCommutative ↥W]
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω))
    (hker : B ⊓ Subgroup.centralizer (W : Set Ω) = pCoreOf 2 B)
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) {m : ℕ} {K : Type} [Field K] [Finite K]
    (hcardK : Nat.card K = 2 ^ m)
    (π : ↥(StatedSL 2 K) →* ↥(autOn B W))
    (hbij : Function.Bijective π)
    (hπ : (FFModel.nat (StatedSL 2 K)).RealizesVia (autOn B W)
      (commV (autOn B W)) (gomiWXKer (autOn B W)) π) :
    IsLin2Type B m := by
  let eπ : ↥(StatedSL 2 K) ≃* ↥(autOn B W) := MulEquiv.ofBijective π hbij
  have hπsymm : ∀ g : ↥(autOn B W), π (eπ.symm g) = g := fun g => eπ.apply_symm_apply g
  have hreal := hπ
  obtain ⟨-, -, -, -, -, -, -, β₀, hβ₀s, hβ₀k, hβ₀e⟩ := hπ
  refine ⟨K, inferInstance, Fintype.ofFinite K, ?_, gomi410alpha_bnsl B W hBW eπ,
    gomi410alpha_surjective_bnsl B W hBW eπ, gomi410alpha_ker_bnsl B W hBW hker eπ, ?_⟩
  · rw [Fintype.card_eq_nat_card, hcardK]
  · exact ⟨gomi410beta_bnsl B W hBW hU β₀,
      gomi410beta_surjective_bnsl B W hBW hU β₀ hβ₀s,
      gomi410beta_ker_bnsl B W hBW hU β₀ hβ₀k,
      gomi410beta_equivariant_bnsl B W hBW hU π eπ hπsymm hreal β₀ hβ₀e⟩

open scoped IsMulCommutative in
theorem isNaturalSLTwoModule_of_binaryNaturalSL {B W : Subgroup Ω} [IsMulCommutative ↥W]
    (hBW : B ≤ normalizer (W : Set Ω)) (hker : B ⊓ centralizer (W : Set Ω) = pCoreOf 2 B)
    (hU : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆) {m : ℕ} (hSL : IsSLn ↥(autOn B W) 2 m)
    (hnat : BinaryNaturalSL (autOn B W) (commV (autOn B W)) (gomiWXKer (autOn B W)) 2 m) :
    IsNaturalSLTwoModule ↥B m := by
  obtain ⟨K, hfield, hfin, hcardK, π, hπ⟩ := hnat
  let _ : Field K := hfield
  let _ : Finite K := hfin
  have _ : Fintype K := Fintype.ofFinite K
  obtain ⟨K0, hfield0, hfin0, hcard0, ⟨e0⟩⟩ := hSL
  let _ : Field K0 := hfield0
  let _ : Finite K0 := hfin0
  have _ : Fintype K0 := Fintype.ofFinite K0
  have hcardEq : Fintype.card K0 = Fintype.card K := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcard0, hcardK]
  let eField : K0 ≃+* K := FiniteField.ringEquivOfCardEq hcardEq
  let eCard : ↥(autOn B W) ≃* ↥(StatedSL 2 K) :=
    e0.trans ((specialLinearGroupEquivStatedSL 2 K0).symm.trans
      ((slEquiv eField).trans (specialLinearGroupEquivStatedSL 2 K)))
  have _ : Finite ↥(StatedSL 2 K) := inferInstance
  have hbij : Function.Bijective π :=
    ⟨(Finite.injective_iff_surjective_of_equiv eCard.symm.toEquiv).2 hπ.1, hπ.1⟩
  have hlin : IsLin2Type B m :=
    isLin2Type_of_realisesVia_bnsl hBW hker hU hcardK π hbij hπ
  have hm : m ≠ 0 := by
    rintro rfl
    have h2 : 1 < Nat.card K := by
      rw [← Fintype.card_eq_nat_card]
      exact Fintype.one_lt_card
    rw [hcardK] at h2
    norm_num at h2
  exact isNaturalSLTwoModule_of_isLin2TypeGF (isLin2TypeGF_of_isLin2Type hm hlin)

end CFSG.GroupTheory
