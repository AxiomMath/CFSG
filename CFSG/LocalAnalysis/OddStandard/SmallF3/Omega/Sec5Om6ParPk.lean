module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2PocketAbs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2BlockInr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentSplit
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenMat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888F2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PrB
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

structure Om6Par (Q : QuadraticForm (ZMod 3) V) (t : OGroup Q) where
  nd : Q.Nondegenerate
  htt : t * t = 1
  dimW : Module.finrank (ZMod 3) (commSp t) = 4
  dimP : Module.finrank (ZMod 3) (fixSp t) = 2
  signW : quadSign (Q.restrict (commSp t)) = 1
  signP : quadSign (Q.restrict (fixSp t)) = -1
  e : detForm.IsometryEquiv (Q.restrict (commSp t))

noncomputable def Om6Par.mk' (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hs : quadSign Q = -1) {t : OGroup Q} (htt : t * t = 1) (hty : invType t = (4, 1)) :
    Om6Par Q t :=
  have hW : Module.finrank (ZMod 3) (commSp t) = 4 := by
    simpa only [invType, invDim] using congrArg Prod.fst hty
  have hWs : quadSign (Q.restrict (commSp t)) = 1 := by
    simpa only [invType, invSign] using congrArg Prod.snd hty
  have hP : Module.finrank (ZMod 3) (fixSp t) = 2 := by
    have := finrank_fixSp_add_finrank_commSp t
    omega
  have hPs : quadSign (Q.restrict (fixSp t)) = -1 := by
    have h := quadSign_eq_fixSp_commSp hQ htt
    rw [hs, hW, hP, hWs] at h
    have h8 : ((-1 : ℤˣ)) ^ (2 * 4) = 1 := by decide
    rw [h8, mul_one, mul_one] at h
    exact h.symm
  { nd := hQ
    htt := htt
    dimW := hW
    dimP := hP
    signW := hWs
    signP := hPs
    e := Classical.choice (equivalent_of_quadSign_eq detForm_nondegenerate
      (nondegenerate_restrict_commSp hQ htt) (finrank_mat2.trans hW.symm)
      (quadSign_detForm.trans hWs.symm)) }

variable {t : OGroup Q} (D : Om6Par Q t)

@[expose] noncomputable def Om6Par.theta : OGroup detForm →* OGroup Q :=
  (blockInr D.htt).comp (TauCeti.QuadraticMap.orthogonalGroupCongr D.e).toMonoidHom

@[expose] noncomputable def Om6Par.L : Subgroup (OGroup Q) := leftMulHom.range.map D.theta

@[expose] noncomputable def Om6Par.R : Subgroup (OGroup Q) := rightMulHom.range.map D.theta

@[expose] noncomputable def Om6Par.iota : Mat2 →ₗ[ZMod 3] V :=
  (commSp t).subtype ∘ₗ (D.e.toLinearEquiv : Mat2 →ₗ[ZMod 3] commSp t)

theorem Om6Par.theta_injective : Function.Injective D.theta := fun a b h =>
  (TauCeti.QuadraticMap.orthogonalGroupCongr D.e).injective (blockInr_injective D.htt h)

theorem Om6Par.theta_apply_W (a : OGroup detForm) (X : Mat2) :
    ((D.theta a : OGroup Q) : V ≃ₗ[ZMod 3] V) (D.iota X) =
      D.iota (((a : OGroup detForm) : Mat2 ≃ₗ[ZMod 3] Mat2) X) := by
  have h := (FGSplit.comm D.nd D.htt).extW_W
    ((TauCeti.QuadraticMap.orthogonalGroupCongr D.e) a) (D.e X)
  have h2 : (((TauCeti.QuadraticMap.orthogonalGroupCongr D.e) a :
      OGroup (Q.restrict (commSp t))) : commSp t ≃ₗ[ZMod 3] commSp t) (D.e X) =
      D.e (((a : OGroup detForm) : Mat2 ≃ₗ[ZMod 3] Mat2) X) := by
    rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply]
    simp
  exact h.trans (congrArg Subtype.val h2)

theorem Om6Par.theta_apply_P (a : OGroup detForm) {p : V} (hp : p ∈ fixSp t) :
    ((D.theta a : OGroup Q) : V ≃ₗ[ZMod 3] V) p = p :=
  (FGSplit.comm D.nd D.htt).extW_P ((TauCeti.QuadraticMap.orthogonalGroupCongr D.e) a) ⟨p, hp⟩

theorem Om6Par.theta_piOrth : D.theta (piOrth detForm) = t := by
  rw [Om6Par.theta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    orthogonalGroupCongr_piOrth, blockInr_piOrth]

theorem Om6Par.theta_mem_omega {a : OGroup detForm}
    (ha : a ∈ omegaGroup detForm_nondegenerate) : D.theta a ∈ omegaGroup D.nd :=
  blockInr_mem_omegaGroup D.nd D.htt (by rw [D.dimW]; norm_num)
    ((mem_omegaGroup_orthogonalGroupCongr_iff detForm_nondegenerate
      (nondegenerate_restrict_commSp D.nd D.htt) (by rw [finrank_mat2]; norm_num) D.e a).mpr ha)

theorem Om6Par.theta_mem_cent (a : OGroup detForm) :
    D.theta a ∈ Subgroup.centralizer ({t} : Set (OGroup Q)) :=
  blockInr_mem_centralizer D.nd D.htt _

theorem om6par_omega_eq_sup :
    omegaGroup detForm_nondegenerate = leftMulHom.range ⊔ rightMulHom.range := by
  apply le_antisymm
  · rw [← range_detPhi]
    rintro _ ⟨⟨A, B⟩, rfl⟩
    rw [detPhi_apply]
    exact Subgroup.mul_mem_sup ⟨A, rfl⟩ ⟨B, rfl⟩
  · exact sup_le (by rintro _ ⟨A, rfl⟩; exact leftMulHom_mem_omegaGroup A)
      (by rintro _ ⟨B, rfl⟩; exact rightMulHom_mem_omegaGroup B)

theorem Om6Par.map_omega : (omegaGroup detForm_nondegenerate).map D.theta = D.L ⊔ D.R := by
  rw [om6par_omega_eq_sup, Subgroup.map_sup]
  rfl

theorem Om6Par.le_omega_cent : D.L ⊔ D.R ≤
    omegaGroup D.nd ⊓ Subgroup.centralizer ({t} : Set (OGroup Q)) := by
  rw [← D.map_omega]
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨D.theta_mem_omega ha, D.theta_mem_cent a⟩

theorem Om6Par.odd_mem {x : OGroup Q} (hx : x ∈ Subgroup.centralizer ({t} : Set (OGroup Q)))
    (hodd : Odd (orderOf x)) : x ∈ D.L ⊔ D.R := by
  rw [← D.map_omega]
  obtain ⟨n, hn⟩ := hodd
  have hcc : x ^ (n + 1) * x ^ (n + 1) = x := by
    rw [← pow_add, show n + 1 + (n + 1) = (2 * n + 1) + 1 by ring, pow_succ, ← hn,
      pow_orderOf_eq_one, one_mul]
  have hxΩ : x ∈ blockOmega D.nd D.htt :=
    hcc ▸ mul_self_mem_blockOmega D.nd D.htt (Subgroup.pow_mem _ hx _)
  obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hxΩ
  rw [Subgroup.mem_prod] at hq
  have hpow : q ^ (2 * n + 1) = 1 := blockHom_injective D.htt (by
    rw [map_pow, hqx, map_one, ← hn, pow_orderOf_eq_one])
  have h1 : q.1 ^ (2 * n + 1) = 1 := by rw [← Prod.pow_fst, hpow]; rfl
  have h8 : q.1 ^ 8 = 1 := by
    rw [← natCard_oGroup_two_minus (nondegenerate_restrict_fixSp D.nd D.htt) D.dimP D.signP]
    exact pow_card_eq_one'
  have hcop : Nat.Coprime (2 * n + 1) 8 := by
    have h := (Nat.coprime_two_right (n := 2 * n + 1)).mpr ⟨n, rfl⟩
    simpa using h.pow_right 3
  have hq1 : q.1 = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h1, h8⟩
    rwa [hcop] at this
  refine ⟨(TauCeti.QuadraticMap.orthogonalGroupCongr D.e).symm q.2, ?_, ?_⟩
  · refine (mem_omegaGroup_orthogonalGroupCongr_iff detForm_nondegenerate
      (nondegenerate_restrict_commSp D.nd D.htt) (by rw [finrank_mat2]; norm_num) D.e _).mp ?_
    rw [MulEquiv.apply_symm_apply]
    exact hq.2
  · rw [← hqx]
    show blockInr D.htt ((TauCeti.QuadraticMap.orthogonalGroupCongr D.e)
      ((TauCeti.QuadraticMap.orthogonalGroupCongr D.e).symm q.2)) = blockHom D.htt q
    rw [MulEquiv.apply_symm_apply, blockInr_apply]
    exact congrArg (blockHom D.htt) (Prod.ext hq1.symm rfl)

theorem Om6Par.ne_one (D : Om6Par Q t) : t ≠ 1 := by
  intro h
  have h1 : D.theta (piOrth detForm) = D.theta 1 := by rw [D.theta_piOrth, map_one]; exact h
  exact piOrth_ne_one (by rw [finrank_mat2]; norm_num) (D.theta_injective h1)

theorem Om6Par.orderOf_eq (D : Om6Par Q t) : orderOf t = 2 :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  orderOf_eq_prime (by rw [pow_two]; exact D.htt) D.ne_one

theorem Om6Par.sec5Pair : Sec5Pair D.L D.R t := by
  obtain ⟨m, hm⟩ := exists_sl2f3_eq_neg_one
  refine ⟨?_, ⟨(Subgroup.equivMapOfInjective _ D.theta D.theta_injective).symm.trans
      (MonoidHom.ofInjective leftMulHom_injective).symm⟩,
    ⟨(Subgroup.equivMapOfInjective _ D.theta D.theta_injective).symm.trans
      (MonoidHom.ofInjective rightMulHom_injective).symm⟩, ⟨_, ⟨m, rfl⟩, ?_⟩,
    ⟨_, ⟨sl2f3NegOne, rfl⟩, ?_⟩, D.htt, D.ne_one⟩
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩ _ ⟨_, ⟨B, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, leftMulHom_mul_rightMulHom_comm]
  · rw [leftMulHom_eq_piOrth hm, D.theta_piOrth]
  · rw [rightMulHom_sl2f3NegOne, D.theta_piOrth]

theorem Om6Par.twoRes_eq :
    D.L ⊔ D.R = twoRes (omegaGroup D.nd ⊓ Subgroup.centralizer ({t} : Set (OGroup Q))) :=
  le_antisymm (D.sec5Pair.le_twoRes D.le_omega_cent)
    ((Subgroup.closure_le _).2 fun x hx => D.odd_mem hx.1.2 hx.2)

theorem Om6Par.pocket_cases {P : Subgroup (OGroup Q)}
    (hP : Sl23PocketIn (omegaGroup D.nd) t P)
    (hle : P ≤ twoRes (omegaGroup D.nd ⊓ Subgroup.centralizer ({t} : Set (OGroup Q)))) :
    P = D.L ∨ P = D.R := by
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  have hcomm : ⁅D.L, D.R⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (D.sec5Pair.comm a ha b hb)
  obtain ⟨hL, hR⟩ := D.sec5Pair.pocket D.twoRes_eq
  exact asc82FactPocketsTwo_of (OGroup Q) (omegaGroup D.nd) t D.L D.R P D.orderOf_eq hL hR
    D.sec5Pair.ne hcomm D.twoRes_eq D.sec5Pair.iso₁ D.sec5Pair.iso₂ hP (D.twoRes_eq ▸ hle)

end CFSG.OddStandard.SmallF3.Omega
