module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5Classify
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Omega4MinusOfOrthA
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Omega4MinusOfOrthB

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.QuasithinUnique.A5.Delta5 (Alt5)
open OmegaH
open scoped commutatorElement Matrix

theorem omega_y0_ne_one : y0 ≠ 1 := by
  intro h
  have := congrArg Subtype.val h
  change CFSG.QuasithinUnique.A5.Delta5.b0⁻¹ = 1 at this
  revert this
  decide +kernel

theorem omega_bN_ne_one : Certificates.A5GL42.bN ≠ 1 := by decide

theorem omega_bN_cube : Certificates.A5GL42.bN * Certificates.A5GL42.bN * Certificates.A5GL42.bN = 1 := by
  decide

theorem omega_hvec_fixO : ∀ v : Fin 4 → ZMod 2, Certificates.A5GL42.aO *ᵥ v = v →
    Certificates.A5GL42.bO *ᵥ v = v → v = 0 := by
  decide

theorem omega_excl_natural {g b : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hF : Certificates.A5GL42.Facts)
    (hg : IsUnit g) (hfix : ∃ v : Fin 4 → ZMod 2, v ≠ 0 ∧ b *ᵥ v = v)
    (hb : g * b = Certificates.A5GL42.bN * g) : False := by
  obtain ⟨v, hv0, hv⟩ := hfix
  have hfixv : Certificates.A5GL42.bN *ᵥ (g *ᵥ v) = g *ᵥ v := by
    rw [Matrix.mulVec_mulVec, ← hb, ← Matrix.mulVec_mulVec, hv]
  have hgv : g *ᵥ v ≠ 0 := by
    intro h
    apply hv0
    apply Matrix.mulVec_injective_iff_isUnit.mpr hg
    rw [h, Matrix.mulVec_zero]
  exact hgv (hF.fixN _ hF.gens.2.1 omega_bN_ne_one omega_bN_cube _ hfixv)

theorem omega_units_conj_eq {U : (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ} {A B : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : (U : Matrix (Fin 4) (Fin 4) (ZMod 2)) * A = B * U) :
    (U : Matrix (Fin 4) (Fin 4) (ZMod 2)) * A * ((U⁻¹ : (Matrix (Fin 4) (Fin 4) (ZMod 2))ˣ) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) = B := by
  rw [h, mul_assoc, Units.mul_inv, mul_one]

theorem leafOmega4MinusOfOrth [DSLeaf LeafFaithfulA5]
    [DSLeaf LeafShort2OfA5] [DSLeaf LeafM3] [DSLeaf LeafAlt5OfOrth] : LeafOmega4MinusOfOrth := by
  intro G _ _ L hq hc he hn hnat
  classical
  have hF : Certificates.A5GL42.Facts := a5Facts
  have hpre : A5Pre L L (pCoreOf 2 L) ⊥ := omega_a5Pre_self hq hc he hn
  rcases hpre.exists_model' with ⟨hN, -⟩ | ⟨-, ⟨M⟩⟩
  · exact absurd hN hnat
  have hHO : Certificates.A5GL42.GroupFacts Certificates.A5GL42.HO := hF.groupO
  set F := M.F with hFdef
  have hMimg : ∀ l : ↥L, glMat (F.M l) ∈ Certificates.A5GL42.HO := fun l => M.imgL l l.2
  have hMker : ∀ l : ↥L, F.M l = 1 ↔ (l : G) ∈ pCoreOf 2 L := fun l => M.kerL l l.2
  obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hq
  obtain ⟨e₁⟩ := hq
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  obtain ⟨α, hαsurj, hαker⟩ := omega_exists_alpha (K := GaloisField 2 2) e₁
  have hcard : Fintype.card (GaloisField 2 2) = 4 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨ω, h0, h1, h3⟩ := exists_omega hcard
  let C : HermCtx (GaloisField 2 2) ω := ⟨hcard, h0, h1, h3⟩
  let RL : ↥L →* GL (Fin 4) (ZMod 2) := (RSL C).comp α
  have hRLpc : ∀ x : ↥L, x ∈ CFSG.pCore 2 ↥L → RL x = 1 := by
    intro x hx
    have hx' : α x = 1 := by
      have : x ∈ α.ker := by rw [hαker]; exact hx
      exact MonoidHom.mem_ker.mp this
    simp [RL, hx']
  let RQ : oTwoQuot ↥L →* GL (Fin 4) (ZMod 2) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) RL (fun x hx => MonoidHom.mem_ker.mpr (hRLpc x hx))
  let RA : Alt5 →* GL (Fin 4) (ZMod 2) := RQ.comp e.symm.toMonoidHom
  let MQ : oTwoQuot ↥L →* GL (Fin 4) (ZMod 2) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) F.M
      (fun x hx => MonoidHom.mem_ker.mpr ((hMker x).mpr ((omega_mem_pCore_iff x).mp hx)))
  let ψ : Alt5 →* GL (Fin 4) (ZMod 2) := MQ.comp e.symm.toMonoidHom
  have hψl : ∀ l : ↥L, ψ (e (QuotientGroup.mk l)) = F.M l := by
    intro l
    simp [ψ, MQ]
  have hRAl : ∀ l : ↥L, RA (e (QuotientGroup.mk l)) = RL l := by
    intro l
    simp [RA, RQ]
  obtain ⟨ℓx, hℓx⟩ := QuotientGroup.mk_surjective (e.symm x0)
  obtain ⟨ℓy, hℓy⟩ := QuotientGroup.mk_surjective (e.symm y0)
  have hex : e (QuotientGroup.mk ℓx) = x0 := by rw [hℓx, MulEquiv.apply_symm_apply]
  have hey : e (QuotientGroup.mk ℓy) = y0 := by rw [hℓy, MulEquiv.apply_symm_apply]
  have hψx : ψ x0 = F.M ℓx := by rw [← hex, hψl]
  have hψy : ψ y0 = F.M ℓy := by rw [← hey, hψl]
  have hRAx : RA x0 = RL ℓx := by rw [← hex, hRAl]
  have hRAy : RA y0 = RL ℓy := by rw [← hey, hRAl]
  have hψinj : ∀ σ : Alt5, ψ σ = 1 → σ = 1 := by
    intro σ hσ
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (e.symm σ)
    have hσe : σ = e (QuotientGroup.mk m) := by rw [hm, MulEquiv.apply_symm_apply]
    rw [hσe, hψl] at hσ
    rw [hσe, (QuotientGroup.eq_one_iff m).mpr ((omega_mem_pCore_iff m).mpr ((hMker m).mp hσ)),
      map_one]
  have hRA_ne : ∃ σ : Alt5, RA σ ≠ 1 := by
    obtain ⟨ℓt, hℓt⟩ := hαsurj transvSL
    refine ⟨e (QuotientGroup.mk ℓt), ?_⟩
    rw [hRAl]
    intro h
    apply R4_transv_ne_one C
    have hRLt : glMat (RL ℓt) = R4 C transvM := by
      rw [show RL ℓt = RSL C (α ℓt) from rfl, hℓt]
      exact RSL_val C transvSL
    rw [← hRLt, h]
    rfl
  have hRAinj : Function.Injective RA := by
    rw [← MonoidHom.ker_eq_bot_iff]
    haveI : IsSimpleGroup Alt5 := alternatingGroup.isSimpleGroup_five
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker RA) with h | h
    · exact h
    · exfalso
      obtain ⟨σ, hσ⟩ := hRA_ne
      apply hσ
      have hmem : σ ∈ MonoidHom.ker RA := by rw [h]; exact Subgroup.mem_top σ
      exact MonoidHom.mem_ker.mp hmem
  have hx0ne : x0 ≠ 1 := x0_ne_one
  have hy0ne : y0 ≠ 1 := omega_y0_ne_one
  have hx2 : ψ x0 * ψ x0 = 1 := by rw [← map_mul, x0_sq, map_one]
  have hxne : ψ x0 ≠ 1 := fun h => hx0ne (hψinj x0 h)
  have hyne : ψ y0 ≠ 1 := fun h => hy0ne (hψinj y0 h)
  have hy3 : ψ y0 * ψ y0 * ψ y0 = 1 := by
    rw [← map_mul, ← map_mul, ← pow_three', y0_cube, map_one]
  have hxy : (ψ x0 * ψ y0) ^ 5 = 1 := by rw [← map_mul, ← map_pow, x0_y0_pow_five, map_one]
  have hm1 : glMat (ψ x0) * glMat (ψ x0) = 1 := by rw [← Units.val_mul, hx2, Units.val_one]
  have hm2 : glMat (ψ x0) ≠ 1 := fun h => hxne (Units.ext h)
  have hm3 : glMat (ψ y0) ^ 3 = 1 := by
    rw [pow_three', ← Units.val_mul, ← Units.val_mul, hy3, Units.val_one]
  have hm4 : (glMat (ψ x0) * glMat (ψ y0)) ^ 5 = 1 := by
    rw [← Units.val_mul, ← Units.val_pow_eq_pow_val, hxy, Units.val_one]
  obtain ⟨gQ, hgQdet, hcaseQ⟩ := hF.classify _ _ hm1 hm2 hm3 hm4
  have hgQU : IsUnit gQ.det := by rw [hgQdet]; exact isUnit_one
  have hgQ' : IsUnit gQ := (Matrix.isUnit_iff_isUnit_det gQ).mpr hgQU
  let gQU : GL (Fin 4) (ZMod 2) := Matrix.GeneralLinearGroup.mk'' gQ hgQU
  have hyHO : glMat (ψ y0) ∈ Certificates.A5GL42.HO := by rw [hψy]; exact hMimg ℓy
  have hyfix : ∃ v : Fin 4 → ZMod 2, v ≠ 0 ∧ glMat (ψ y0) *ᵥ v = v :=
    hF.fixO _ hyHO (fun h => hyne (Units.ext h)) (by rw [← pow_three']; exact hm3)
  have hOQ : gQ * glMat (ψ x0) = Certificates.A5GL42.aO * gQ ∧
      gQ * glMat (ψ y0) = Certificates.A5GL42.bO * gQ := by
    rcases hcaseQ with ⟨-, hbN⟩ | hO
    · exact (omega_excl_natural hF hgQ' hyfix hbN).elim
    · exact hO
  obtain ⟨hQ1, hQ2⟩ := hOQ
  have hm1' : glMat (RA x0) * glMat (RA x0) = 1 := by
    rw [← Units.val_mul, ← map_mul, x0_sq, map_one, Units.val_one]
  have hm2' : glMat (RA x0) ≠ 1 := fun h => hx0ne (hRAinj (by rw [map_one]; exact Units.ext h))
  have hy3' : RA y0 * RA y0 * RA y0 = 1 := by
    rw [← map_mul, ← map_mul, ← pow_three', y0_cube, map_one]
  have hm3' : glMat (RA y0) ^ 3 = 1 := by
    rw [pow_three', ← Units.val_mul, ← Units.val_mul, hy3', Units.val_one]
  have hxy' : (RA x0 * RA y0) ^ 5 = 1 := by rw [← map_mul, ← map_pow, x0_y0_pow_five, map_one]
  have hm4' : (glMat (RA x0) * glMat (RA y0)) ^ 5 = 1 := by
    rw [← Units.val_mul, ← Units.val_pow_eq_pow_val, hxy', Units.val_one]
  obtain ⟨gH, hgHdet, hcaseH⟩ := hF.classify _ _ hm1' hm2' hm3' hm4'
  have hgHU : IsUnit gH.det := by rw [hgHdet]; exact isUnit_one
  have hgH' : IsUnit gH := (Matrix.isUnit_iff_isUnit_det gH).mpr hgHU
  let gHU : GL (Fin 4) (ZMod 2) := Matrix.GeneralLinearGroup.mk'' gH hgHU
  have hH_fix : ∃ v : Fin 4 → ZMod 2, v ≠ 0 ∧ glMat (RA y0) *ᵥ v = v := by
    have hmk : (QuotientGroup.mk (ℓy ^ 3) : oTwoQuot ↥L) = 1 := by
      apply e.injective
      rw [map_one, QuotientGroup.mk_pow, map_pow, hey, y0_cube]
    have hα3 : α ℓy ^ 3 = 1 := by
      have h3 : ℓy ^ 3 ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp hmk
      have : ℓy ^ 3 ∈ α.ker := by rw [hαker]; exact h3
      rw [← map_pow]
      exact MonoidHom.mem_ker.mp this
    have hcube : (α ℓy : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) * (α ℓy : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *
        (α ℓy : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) = 1 := by
      rw [← pow_three', ← Matrix.SpecialLinearGroup.coe_pow, hα3, Matrix.SpecialLinearGroup.coe_one]
    obtain ⟨v, hv0, hv⟩ := exists_fixed_of_cube C hcube
    have hRy : glMat (RA y0) = R4 C (α ℓy : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) := by
      rw [hRAy]
      exact RSL_val C (α ℓy)
    exact ⟨v, hv0, by rw [hRy]; exact hv⟩
  have hOH : gH * glMat (RA x0) = Certificates.A5GL42.aO * gH ∧
      gH * glMat (RA y0) = Certificates.A5GL42.bO * gH := by
    rcases hcaseH with ⟨-, hbN⟩ | hO
    · exact (omega_excl_natural hF hgH' hH_fix hbN).elim
    · exact hO
  obtain ⟨hH1, hH2⟩ := hOH
  let Θ : GL (Fin 4) (ZMod 2) := gQU⁻¹ * gHU
  have hconjx : gHU * RA x0 * gHU⁻¹ = gQU * ψ x0 * gQU⁻¹ := by
    apply Units.ext
    simp only [Units.val_mul]
    exact (omega_units_conj_eq (U := gHU) hH1).trans (omega_units_conj_eq (U := gQU) hQ1).symm
  have hconjy : gHU * RA y0 * gHU⁻¹ = gQU * ψ y0 * gQU⁻¹ := by
    apply Units.ext
    simp only [Units.val_mul]
    exact (omega_units_conj_eq (U := gHU) hH2).trans (omega_units_conj_eq (U := gQU) hQ2).symm
  have hEq : ψ = (MulAut.conj Θ).toMonoidHom.comp RA := by
    apply MonoidHom.eq_of_eqOn_dense closure_x0_y0
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simp only [MonoidHom.comp_apply, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      calc ψ x0 = gQU⁻¹ * (gQU * ψ x0 * gQU⁻¹) * gQU := by group
        _ = gQU⁻¹ * (gHU * RA x0 * gHU⁻¹) * gQU := by rw [hconjx]
        _ = Θ * RA x0 * Θ⁻¹ := by simp only [Θ]; group
    · simp only [MonoidHom.comp_apply, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      calc ψ y0 = gQU⁻¹ * (gQU * ψ y0 * gQU⁻¹) * gQU := by group
        _ = gQU⁻¹ * (gHU * RA y0 * gHU⁻¹) * gQU := by rw [hconjy]
        _ = Θ * RA y0 * Θ⁻¹ := by simp only [Θ]; group
  have hΘ : ∀ ℓ : ↥L, F.M ℓ = Θ * RL ℓ * Θ⁻¹ := by
    intro ℓ
    have h := DFunLike.congr_fun hEq (e (QuotientGroup.mk ℓ))
    rw [hψl] at h
    simp only [MonoidHom.comp_apply, MulAut.conj_apply, MulEquiv.coe_toMonoidHom, hRAl] at h
    exact h
  have hrel : ∀ ℓ : ↥L, glMat (Θ⁻¹) * glMat (F.M ℓ) =
      R4 C (α ℓ : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) * glMat (Θ⁻¹) := by
    intro ℓ
    have h1 : Θ⁻¹ * F.M ℓ = RL ℓ * Θ⁻¹ := by rw [hΘ ℓ]; group
    have h2 := congrArg (fun g : GL (Fin 4) (ZMod 2) => (g : Matrix (Fin 4) (Fin 4) (ZMod 2))) h1
    simp only [Units.val_mul] at h2
    rw [← RSL_val C (α ℓ)]
    exact h2
  have hU : blockU L = pCoreOf 2 L := omega_blockU_eq_pCoreOf hF hHO hpre M
  have hUle : blockU L ≤ pCoreOf 2 L := hU.le
  let toE : ↥(blockU L) → ↥(pCoreOf 2 L) := fun u => ⟨(u : G), hUle u.2⟩
  have toE_mul : ∀ u v : ↥(blockU L), toE (u * v) = toE u * toE v := fun u v => Subtype.ext rfl
  have toE_one : toE 1 = 1 := Subtype.ext rfl
  have hZ : blockZ L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ blockU L ⊓ Subgroup.centralizer (L : Set G) := hx
    obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.mp hx'
    rw [Subgroup.mem_bot]
    have hxQ : (x : G) ∈ pCoreOf 2 L := hUle hxU
    let ex : ↥(pCoreOf 2 L) := ⟨x, hxQ⟩
    have hfix : ∀ ℓ : ↥L, (ℓ : G) * x = x * (ℓ : G) → glMat (F.M ℓ) *ᵥ Multiplicative.toAdd (F.φ ex) =
        Multiplicative.toAdd (F.φ ex) := by
      intro ℓ hℓ
      apply F.act ℓ ex ex
      show x = (ℓ : G) * x * (ℓ : G)⁻¹
      rw [hℓ, mul_inv_cancel_right]
    have hfixx := hfix ℓx (Subgroup.mem_centralizer_iff.mp hxC _ ℓx.2)
    have hfixy := hfix ℓy (Subgroup.mem_centralizer_iff.mp hxC _ ℓy.2)
    set w := Multiplicative.toAdd (F.φ ex) with hw
    have hψx' : glMat (ψ x0) *ᵥ w = w := by rw [hψx]; exact hfixx
    have hψy' : glMat (ψ y0) *ᵥ w = w := by rw [hψy]; exact hfixy
    have hfa : Certificates.A5GL42.aO *ᵥ (gQ *ᵥ w) = gQ *ᵥ w := by
      rw [Matrix.mulVec_mulVec, ← hQ1, ← Matrix.mulVec_mulVec, hψx']
    have hfb : Certificates.A5GL42.bO *ᵥ (gQ *ᵥ w) = gQ *ᵥ w := by
      rw [Matrix.mulVec_mulVec, ← hQ2, ← Matrix.mulVec_mulVec, hψy']
    have hgw : gQ *ᵥ w = 0 := omega_hvec_fixO _ hfa hfb
    have hw0 : w = 0 := by
      apply Matrix.mulVec_injective_iff_isUnit.mpr hgQ'
      rw [hgw, Matrix.mulVec_zero]
    have hφ1 : F.φ ex = 1 := Multiplicative.toAdd.injective (by rw [toAdd_one]; exact hw0)
    exact (F.ker ex).mp hφ1
  let Ψu : GL (Fin 4) (ZMod 2) := Θ⁻¹
  have hΘΨ : glMat Θ * glMat Ψu = 1 := by
    rw [← Units.val_mul, show Θ * Ψu = 1 from mul_inv_cancel Θ, Units.val_one]
  have hΨΘ : glMat Ψu * glMat Θ = 1 := by
    rw [← Units.val_mul, show Ψu * Θ = 1 from inv_mul_cancel Θ, Units.val_one]
  have hΨinj : ∀ w : Fin 4 → ZMod 2, glMat Ψu *ᵥ w = 0 → w = 0 := by
    intro w hw
    have h1 : w = (glMat Θ * glMat Ψu) *ᵥ w := by rw [hΘΨ, Matrix.one_mulVec]
    rw [h1, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  let βhom : ↥(blockU L) →* Multiplicative (Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) :=
    { toFun := fun u => Multiplicative.ofAdd
        (hermMat ω (glMat Ψu *ᵥ Multiplicative.toAdd (F.φ (toE u))))
      map_one' := by
        simp only [toE_one, map_one, toAdd_one, Matrix.mulVec_zero, hermMat_zero, ofAdd_zero]
      map_mul' := fun u v => by
        simp only [toE_mul, map_mul, toAdd_mul, Matrix.mulVec_add, hermMat_add, ofAdd_add] }
  have hβval : ∀ u : ↥(blockU L), Multiplicative.toAdd (βhom u) =
      hermMat ω (glMat Ψu *ᵥ Multiplicative.toAdd (F.φ (toE u))) := fun u => rfl
  have hsq : (fun x : GaloisField 2 2 => x ^ 2 ^ 1) = sqK (GaloisField 2 2) := by
    funext x
    rw [sqK_apply, pow_one]
  have hβsurj : ∀ X : Matrix (Fin 2) (Fin 2) (GaloisField 2 2),
      (∃ u, Multiplicative.toAdd (βhom u) = X) ↔ X.map (fun x => x ^ 2 ^ 1) = X.transpose := by
    intro X
    rw [hsq]
    constructor
    · rintro ⟨u, rfl⟩
      rw [hβval]
      exact hermMat_isHerm C _
    · intro hX
      obtain ⟨v, rfl⟩ := exists_hermMat C hX
      obtain ⟨ee, hee⟩ := F.surj (Multiplicative.ofAdd (glMat Θ *ᵥ v))
      refine ⟨⟨(ee : G), by rw [hU]; exact ee.2⟩, ?_⟩
      rw [hβval]
      have hee' : toE ⟨(ee : G), by rw [hU]; exact ee.2⟩ = ee := Subtype.ext rfl
      rw [hee']
      have h2 : Multiplicative.toAdd (F.φ ee) = glMat Θ *ᵥ v := by
        rw [hee, toAdd_ofAdd]
      rw [h2, Matrix.mulVec_mulVec, hΨΘ, Matrix.one_mulVec]
  have hβker : βhom.ker = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have hu1 : βhom u = 1 := MonoidHom.mem_ker.mp hu
    have h1 : hermMat ω (glMat Ψu *ᵥ Multiplicative.toAdd (F.φ (toE u))) = 0 := by
      rw [← hβval u, hu1, toAdd_one]
    have h2 : glMat Ψu *ᵥ Multiplicative.toAdd (F.φ (toE u)) = 0 :=
      hermMat_injective C (h1.trans (hermMat_zero ω).symm)
    have h3 : Multiplicative.toAdd (F.φ (toE u)) = 0 := hΨinj _ h2
    have h4 : F.φ (toE u) = 1 := Multiplicative.toAdd.injective (by rw [h3, toAdd_one])
    have h6 : ((toE u : ↥(pCoreOf 2 L)) : G) ∈ (⊥ : Subgroup G) := (F.ker (toE u)).mp h4
    rw [Subgroup.mem_bot] at h6
    rw [Subgroup.mem_bot]
    exact Subtype.ext h6
  have hβequi : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (βhom v) = (α ℓ : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *
        Multiplicative.toAdd (βhom u) *
          ((α ℓ : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)).map (fun x => x ^ 2 ^ 1)).transpose := by
    intro ℓ u v huv
    have hact := F.act ℓ (toE u) (toE v) huv
    rw [hsq]
    have key : glMat Ψu *ᵥ (glMat (F.M ℓ) *ᵥ Multiplicative.toAdd (F.φ (toE u))) =
        R4 C (α ℓ : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *ᵥ
          (glMat Ψu *ᵥ Multiplicative.toAdd (F.φ (toE u))) := by
      rw [Matrix.mulVec_mulVec, hrel ℓ, ← Matrix.mulVec_mulVec]
    show hermMat ω (glMat Ψu *ᵥ Multiplicative.toAdd (F.φ (toE v))) =
      tm (α ℓ : Matrix (Fin 2) (Fin 2) (GaloisField 2 2))
        (hermMat ω (glMat Ψu *ᵥ Multiplicative.toAdd (F.φ (toE u))))
    rw [← hact, key, R4_mulVec]
    exact rhoFun_spec C _ _
  refine ⟨GaloisField 2 2, inferInstance, inferInstance, ?_, α, hαsurj, hαker, βhom, hβsurj, ?_,
    hβequi⟩
  · rw [hcard]
    norm_num
  · rw [hZ, Subgroup.bot_subgroupOf]
    exact hβker

end CFSG.GH74.QTGen4.DSGen4
