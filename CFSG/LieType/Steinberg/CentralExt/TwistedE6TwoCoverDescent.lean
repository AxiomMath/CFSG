module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCoverAction
public import CFSG.RankThree.PerfectCover.HopfCoverAutSylow
public import CFSG.Sporadic.Schreier.J4SSylowBase

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

public section

open CFSG.RankThree.PerfectCover

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

open CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
open CFSG.LieType.Chevalley.C2E6Std
open CFSG.Monster.B.TwoA.Amalgam
open CFSG.EvenSmallLie.TwoE6

abbrev Eprime : Type := ↥(commutator Eam)

noncomputable def epsE : Eprime ⧸ Subgroup.center Eprime ≃* ↥stdGroup :=
  Classical.choice (derived_Eam_facts.2.2.2)

noncomputable def qE : Eprime →* ↥stdGroup :=
  epsE.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Eprime))

theorem qE_surjective : Function.Surjective qE := by
  intro x
  obtain ⟨y, hy⟩ := epsE.surjective x
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Eprime) y
  exact ⟨z, hy⟩

theorem qE_ker_close : qE.ker ≤ Subgroup.center Eprime := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : epsE (QuotientGroup.mk' (Subgroup.center Eprime) x) = 1 := hx
  have hx'' : QuotientGroup.mk' (Subgroup.center Eprime) x = 1 :=
    epsE.injective (by rw [hx']; simp)
  exact (QuotientGroup.eq_one_iff x).mp hx''

noncomputable abbrev phiE : HopfCover ↥stdGroup →* Eprime :=
  hopfLift qE qE_surjective qE_ker_close

noncomputable abbrev KE : Subgroup (HopfCover ↥stdGroup) := phiE.ker

theorem KE_le_hopfMultiplier : KE ≤ hopfMultiplier ↥stdGroup := by
  intro x hx
  change phiE x = 1 at hx
  change hopfCoverMap ↥stdGroup x = 1
  have hcomp : qE.comp phiE = hopfCoverMap ↥stdGroup := by
    simpa [phiE] using comp_hopfLift qE qE_surjective qE_ker_close
  have h : qE (phiE x) = 1 := by simpa using congrArg qE hx
  rw [← MonoidHom.comp_apply, hcomp] at h
  exact h

theorem card_KE : Nat.card KE = 6 := by
  letI : Finite stdGroup := finite_stdGroup
  letI : Group.IsPerfect stdGroup := isPerfect_stdGroup
  letI : Group.IsPerfect Eprime := derived_Eam_facts.1
  letI : Finite Eprime := derived_Eam_facts.2.1
  have hM : Nat.card (hopfMultiplier ↥stdGroup) = 12 := card_hopfMultiplier
  have hq : Nat.card qE.ker = 2 := by
    rw [show qE = quotCover epsE from rfl, ker_quotCover]
    exact derived_Eam_facts.2.2.1
  let hm := hopfMultiplierToKer qE qE_surjective qE_ker_close
  have hsurj : Function.Surjective hm :=
    hopfMultiplierToKer_surjective qE qE_surjective qE_ker_close
  have hrange : hm.range = ⊤ := MonoidHom.range_eq_top_of_surjective hm hsurj
  have hker : hm.ker = KE.subgroupOf (hopfMultiplier ↥stdGroup) := by
    rw [show hm = hopfMultiplierToKer qE qE_surjective qE_ker_close from rfl,
      hopfMultiplierToKer_ker]
  have hcard := Subgroup.card_ker_mul_card_range hm
  rw [hker, hrange, Subgroup.card_top, hM, hq] at hcard
  have hsub : Nat.card (KE.subgroupOf (hopfMultiplier ↥stdGroup)) = Nat.card KE :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe KE_le_hopfMultiplier).toEquiv
  rw [hsub] at hcard
  omega

section KernelInvariance

variable [Finite ↥stdGroup] [Group.IsPerfect ↥stdGroup]
variable (δ : MulAut ↥stdGroup) (hδ3 : δ ^ 3 = 1)
  (P : Sylow 2 (hopfMultiplier ↥stdGroup))
  (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup))

noncomputable abbrev Q3H : Subgroup (HopfCover ↥stdGroup) :=
  (Q3 : Subgroup (hopfMultiplier ↥stdGroup)).map
    (hopfMultiplier ↥stdGroup).subtype

noncomputable abbrev PH : Subgroup (HopfCover ↥stdGroup) :=
  (P : Subgroup (hopfMultiplier ↥stdGroup)).map
    (hopfMultiplier ↥stdGroup).subtype

theorem card_Q3 : Nat.card (Q3 : Subgroup (hopfMultiplier ↥stdGroup)) = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Finite stdGroup := finite_stdGroup
  letI : Group.IsPerfect stdGroup := isPerfect_stdGroup
  letI : Finite (HopfCover ↥stdGroup) :=
    CFSG.Alternating.Multipliers.finite_hopfCover
  have h3fac : (Nat.factorization 12) 3 = 1 := by
    rw [show 12 = 3 * 4 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization_self Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd]
  rw [Q3.card_eq_multiplicity, card_hopfMultiplier, h3fac]
  norm_num

theorem Q3H_le_KE : Q3H Q3 ≤ KE := by
  classical
  letI : Finite stdGroup := finite_stdGroup
  letI : Group.IsPerfect stdGroup := isPerfect_stdGroup
  letI : Finite (HopfCover ↥stdGroup) :=
    CFSG.Alternating.Multipliers.finite_hopfCover
  letI : IsMulCommutative (hopfMultiplier ↥stdGroup) :=
    ⟨⟨fun a b => Subtype.ext
      (Subgroup.mem_center_iff.1 (hopfMultiplier_le_center b.2) (a : HopfCover ↥stdGroup))⟩⟩
  have hcardK : Nat.card KE = 6 := card_KE
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := KE) 3
    (by rw [hcardK]; norm_num)
  let zM : hopfMultiplier ↥stdGroup := ⟨(z : HopfCover ↥stdGroup), KE_le_hopfMultiplier z.2⟩
  have hzM : orderOf zM = 3 := by
    calc
      orderOf zM = orderOf (zM : HopfCover ↥stdGroup) :=
        (Subgroup.orderOf_coe zM).symm
      _ = orderOf (z : HopfCover ↥stdGroup) := rfl
      _ = orderOf z := Subgroup.orderOf_coe z
      _ = 3 := hz
  have hzcard : Nat.card (Subgroup.zpowers zM) = 3 := by
    rw [Nat.card_zpowers, hzM]
  have hz3 : IsPGroup 3 (Subgroup.zpowers zM) :=
    IsPGroup.of_card (n := 1) (by simpa using hzcard)
  have hle : Subgroup.zpowers zM ≤ (Q3 : Subgroup (hopfMultiplier ↥stdGroup)) :=
    hz3.le_sylow_of_normal (N := Subgroup.zpowers zM) Q3
  have heq : Subgroup.zpowers zM = (Q3 : Subgroup (hopfMultiplier ↥stdGroup)) := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hzcard, card_Q3]
  change (Q3 : Subgroup (hopfMultiplier ↥stdGroup)).map
    (hopfMultiplier ↥stdGroup).subtype ≤ KE
  rw [← heq]
  rw [MonoidHom.map_zpowers]
  exact Subgroup.zpowers_le.mpr z.2

namespace Aux

abbrev M : Type := hopfMultiplier ↥stdGroup
abbrev H : Type := HopfCover ↥stdGroup

variable (δ : MulAut ↥stdGroup) (hδ3 : δ ^ 3 = 1)
  (P : Sylow 2 M)
  (Q3 : Sylow 3 M)
  (hfixP : ∀ p : (P : Subgroup M), hopfCoverAut δ (((p : M) : H)) = ((p : M) : H))

theorem aut_mem_Q3H {x : H} (hx : x ∈ Q3H Q3) :
    hopfCoverAut δ x ∈ Q3H Q3 := by
  classical
  letI : Finite stdGroup := finite_stdGroup
  letI : Group.IsPerfect stdGroup := isPerfect_stdGroup
  letI : Finite (HopfCover ↥stdGroup) :=
    CFSG.Alternating.Multipliers.finite_hopfCover
  letI : IsMulCommutative M :=
    ⟨⟨fun a b => Subtype.ext
      (Subgroup.mem_center_iff.1 (hopfMultiplier_le_center b.2) (a : H))⟩⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Finite (Sylow 3 M) := Sylow.finite_of_finiteIndex Q3
  rcases (Subgroup.mem_map.mp hx) with ⟨m, hm, rfl⟩
  change ((hopfCoverAutOnMultiplier δ m : M) : H) ∈ Q3H Q3
  have hchar : (Q3 : Subgroup M).Characteristic :=
    Sylow.characteristic_of_normal Q3 inferInstance
  have hmap : (Q3 : Subgroup M).map (hopfCoverAutOnMultiplier δ).toMonoidHom =
      (Q3 : Subgroup M) :=
    Subgroup.characteristic_iff_map_eq.mp hchar (hopfCoverAutOnMultiplier δ)
  have hm' : hopfCoverAutOnMultiplier δ m ∈ (Q3 : Subgroup M) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hm
  exact Subgroup.mem_map_of_mem _ hm'

theorem pow_two_mem_Q3H {k : H} (hk : k ∈ KE) :
    (k : H) ^ 2 ∈ Q3H Q3 := by
  classical
  letI : Finite stdGroup := finite_stdGroup
  letI : Group.IsPerfect stdGroup := isPerfect_stdGroup
  letI : Finite (HopfCover ↥stdGroup) :=
    CFSG.Alternating.Multipliers.finite_hopfCover
  letI : IsMulCommutative M :=
    ⟨⟨fun a b => Subtype.ext
      (Subgroup.mem_center_iff.1 (hopfMultiplier_le_center b.2) (a : H))⟩⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Finite (Sylow 3 M) := Sylow.finite_of_finiteIndex Q3
  let kM : M := ⟨k, KE_le_hopfMultiplier hk⟩
  have hk6 : (k : H) ^ 6 = 1 := by
    have h := pow_card_eq_one' (G := KE) (x := ⟨k, hk⟩)
    rw [card_KE] at h
    simpa using congrArg (fun x : KE => (x : H)) h
  have hk6M : kM ^ 6 = 1 := by
    apply Subtype.ext
    simpa [kM] using hk6
  have h3 : (kM ^ 2) ^ 3 = 1 := by
    rw [← pow_mul]
    norm_num
    exact hk6M
  have hdvd : Nat.card (Subgroup.zpowers (kM ^ 2)) ∣ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one h3
  have h3grp : IsPGroup 3 (Subgroup.zpowers (kM ^ 2)) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hdvd)
  have hle : Subgroup.zpowers (kM ^ 2) ≤ (Q3 : Subgroup M) :=
    h3grp.le_sylow_of_normal (N := Subgroup.zpowers (kM ^ 2)) Q3
  have hm : kM ^ 2 ∈ (Q3 : Subgroup M) := hle (Subgroup.mem_zpowers _)
  change ((kM ^ 2 : M) : H) ∈ Q3H Q3
  exact Subgroup.mem_map_of_mem _ hm

theorem pow_three_mem_PH {k : H} (hk : k ∈ KE) :
    (k : H) ^ 3 ∈ PH P := by
  classical
  letI : Finite stdGroup := finite_stdGroup
  letI : Group.IsPerfect stdGroup := isPerfect_stdGroup
  letI : Finite (HopfCover ↥stdGroup) :=
    CFSG.Alternating.Multipliers.finite_hopfCover
  letI : IsMulCommutative M :=
    ⟨⟨fun a b => Subtype.ext
      (Subgroup.mem_center_iff.1 (hopfMultiplier_le_center b.2) (a : H))⟩⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Finite (Sylow 2 M) := Sylow.finite_of_finiteIndex P
  let kM : M := ⟨k, KE_le_hopfMultiplier hk⟩
  have hk6 : (k : H) ^ 6 = 1 := by
    have h := pow_card_eq_one' (G := KE) (x := ⟨k, hk⟩)
    rw [card_KE] at h
    simpa using congrArg (fun x : KE => (x : H)) h
  have hk6M : kM ^ 6 = 1 := by
    apply Subtype.ext
    simpa [kM] using hk6
  have h2 : (kM ^ 3) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
    exact hk6M
  have hdvd : Nat.card (Subgroup.zpowers (kM ^ 3)) ∣ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one h2
  have h2grp : IsPGroup 2 (Subgroup.zpowers (kM ^ 3)) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hdvd)
  have hle : Subgroup.zpowers (kM ^ 3) ≤ (P : Subgroup M) :=
    h2grp.le_sylow_of_normal (N := Subgroup.zpowers (kM ^ 3)) P
  have hm : kM ^ 3 ∈ (P : Subgroup M) := hle (Subgroup.mem_zpowers _)
  change ((kM ^ 3 : M) : H) ∈ PH P
  exact Subgroup.mem_map_of_mem _ hm

theorem KE_invariant (P : Sylow 2 M) (Q3 : Sylow 3 M)
    (hfixP : ∀ p : (P : Subgroup M), hopfCoverAut δ (((p : M) : H)) = ((p : M) : H)) :
    KE.map (hopfCoverAut δ).toMonoidHom ≤ KE := by
  classical
  intro x hx
  rcases (Subgroup.mem_map.mp hx) with ⟨k, hk, rfl⟩
  let kM : M := ⟨k, KE_le_hopfMultiplier hk⟩
  have hk2 : (k : H) ^ 2 ∈ Q3H Q3 := pow_two_mem_Q3H Q3 hk
  have hk3 : (k : H) ^ 3 ∈ PH P := pow_three_mem_PH P hk
  have hk3P : kM ^ 3 ∈ (P : Subgroup M) := by
    rcases (Subgroup.mem_map.mp hk3) with ⟨m, hm, hmk⟩
    have hmk' : (m : H) = (kM ^ 3 : M) := by simpa [kM] using hmk
    have : m = kM ^ 3 := Subtype.ext hmk'
    simpa [this] using hm
  have hfix3 : hopfCoverAut δ ((kM ^ 3 : M) : H) = ((kM ^ 3 : M) : H) :=
    hfixP ⟨kM ^ 3, hk3P⟩
  have hdecompM : kM = (kM ^ 2)⁻¹ * (kM ^ 3) := by group
  have hdecomp : (k : H) = ((kM ^ 2 : M) : H)⁻¹ * ((kM ^ 3 : M) : H) := by
    have := congrArg (fun x : M => (x : H)) hdecompM
    simpa [kM] using this
  rw [hdecomp]
  simp only [map_mul, map_inv]
  change (hopfCoverAut δ ((kM ^ 2 : M) : H))⁻¹ *
      hopfCoverAut δ ((kM ^ 3 : M) : H) ∈ KE
  rw [hfix3]
  have h2Q : hopfCoverAut δ ((kM ^ 2 : M) : H) ∈ Q3H Q3 := by
    apply aut_mem_Q3H δ Q3
    exact pow_two_mem_Q3H Q3 hk
  have h2K : hopfCoverAut δ ((kM ^ 2 : M) : H) ∈ KE := Q3H_le_KE Q3 h2Q
  have h3K : ((kM ^ 3 : M) : H) ∈ KE := KE.pow_mem hk 3
  exact KE.mul_mem (KE.inv_mem h2K) h3K

end Aux

section Descent

variable (δ : MulAut ↥stdGroup)

instance KE_normal : KE.Normal :=
  Subgroup.normal_of_le_center
    (KE_le_hopfMultiplier.trans (hopfMultiplier_le_center (S := ↥stdGroup)))

noncomputable def alphaQuot (hK : KE.map (hopfCoverAut δ).toMonoidHom ≤ KE) :
    MulAut (HopfCover ↥stdGroup ⧸ KE) := by
  classical
  letI : Finite stdGroup := finite_stdGroup
  letI : Group.IsPerfect stdGroup := isPerfect_stdGroup
  letI : Finite (HopfCover ↥stdGroup) :=
    CFSG.Alternating.Multipliers.finite_hopfCover
  letI : Fintype (HopfCover ↥stdGroup ⧸ KE) := Fintype.ofFinite _
  let f : HopfCover ↥stdGroup ⧸ KE →* HopfCover ↥stdGroup ⧸ KE :=
    QuotientGroup.map KE KE (hopfCoverAut δ).toMonoidHom (by
      intro x hx
      rw [Subgroup.mem_comap]
      exact hK (Subgroup.mem_map_of_mem _ hx))
  have hf : Function.Surjective
      (fun x : HopfCover ↥stdGroup =>
        (QuotientGroup.mk' KE) ((hopfCoverAut δ) x)) :=
    (QuotientGroup.mk'_surjective KE).comp (hopfCoverAut δ).surjective
  have hsurj : Function.Surjective f :=
    QuotientGroup.map_surjective_of_surjective KE KE (hopfCoverAut δ).toMonoidHom hf (by
      intro x hx
      rw [Subgroup.mem_comap]
      exact hK (Subgroup.mem_map_of_mem _ hx))
  exact MulEquiv.ofBijective f hsurj.bijective_of_finite

noncomputable def eK : HopfCover ↥stdGroup ⧸ KE ≃* Eprime := by
  classical
  letI : Finite stdGroup := finite_stdGroup
  letI : Group.IsPerfect stdGroup := isPerfect_stdGroup
  letI : Finite (HopfCover ↥stdGroup) :=
    CFSG.Alternating.Multipliers.finite_hopfCover
  letI : Group.IsPerfect Eprime := derived_Eam_facts.1
  letI : Finite Eprime := derived_Eam_facts.2.1
  refine MulEquiv.ofBijective (QuotientGroup.kerLift phiE) ⟨?_, ?_⟩
  · exact QuotientGroup.kerLift_injective phiE
  · intro y
    obtain ⟨x, rfl⟩ := hopfLift_surjective qE qE_surjective qE_ker_close y
    exact ⟨QuotientGroup.mk' KE x, by simp⟩

theorem eK_mk (x : HopfCover ↥stdGroup) :
    eK (QuotientGroup.mk' KE x) = phiE x := by
  change (QuotientGroup.kerLift phiE) (QuotientGroup.mk' KE x) = phiE x
  exact QuotientGroup.kerLift_mk phiE x

noncomputable def alphaE' (hK : KE.map (hopfCoverAut δ).toMonoidHom ≤ KE) : MulAut Eprime :=
  eK.symm.trans ((alphaQuot δ hK).trans eK)

theorem alphaE'_mk (hK) (x : HopfCover ↥stdGroup) :
    alphaE' δ hK (eK (QuotientGroup.mk' KE x)) =
      eK (QuotientGroup.mk' KE (hopfCoverAut δ x)) := by
  simp [alphaE', alphaQuot, QuotientGroup.map_mk]

theorem autCover_alphaE' (hK) : autCover epsE (alphaE' δ hK) = δ := by
  classical
  letI : Finite stdGroup := finite_stdGroup
  letI : Group.IsPerfect stdGroup := isPerfect_stdGroup
  letI : Finite (HopfCover ↥stdGroup) :=
    CFSG.Alternating.Multipliers.finite_hopfCover
  letI : Group.IsPerfect Eprime := derived_Eam_facts.1
  letI : Finite Eprime := derived_Eam_facts.2.1
  apply MulEquiv.ext
  intro t
  obtain ⟨y, rfl⟩ := qE_surjective t
  obtain ⟨x, rfl⟩ := hopfLift_surjective qE qE_surjective qE_ker_close y
  have hq : qE (alphaE' δ hK (phiE x)) = δ (qE (phiE x)) := by
    have hcomp : qE.comp phiE = hopfCoverMap ↥stdGroup := by
      simpa [phiE] using comp_hopfLift qE qE_surjective qE_ker_close
    calc
      qE (alphaE' δ hK (phiE x))
          = qE (eK (QuotientGroup.mk' KE (hopfCoverAut δ x))) := by
              rw [← eK_mk x, alphaE'_mk]
      _ = qE (phiE (hopfCoverAut δ x)) := by rw [eK_mk]
      _ = hopfCoverMap ↥stdGroup (hopfCoverAut δ x) := by
            rw [← MonoidHom.comp_apply, hcomp]
      _ = δ (hopfCoverMap ↥stdGroup x) := by
            exact DFunLike.congr_fun (hopfCoverMap_hopfCoverAut δ) x
      _ = δ (qE (phiE x)) := by rw [← MonoidHom.comp_apply, hcomp]
  have h := quotCover_autCover epsE (alphaE' δ hK) (phiE x)
  exact h.symm.trans hq

end Descent

section Nontriviality

open CFSG.EvenSmallLie.TwoE6
open scoped MatrixGroups

theorem levi34Diag_comp_levi34Hom
    (A : SL(3, GaloisField 2 (2 * 1))) :
    levi34Diag (isogenyStd (levi34Hom A)) =
      isogenyStd (levi34Hom (conjSLHom diagOmegaGLF A)) := by
  set A' := Matrix.SpecialLinearGroup.map fieldEquiv.toRingHom A with hA'
  have hA : slFieldEquivSymm A' = A :=
    Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp [hA']
  have hB : slFieldEquivSymm (conjSL3 diagOmegaGL A') = conjSLHom diagOmegaGLF A := by
    apply Subtype.ext
    rw [← hA]
    simp only [slFieldEquivSymm, Matrix.SpecialLinearGroup.map_apply_coe,
      coe_conjSL3, coe_conjSLHom, coe_diagOmegaGLF, coe_diagOmegaGLF_inv,
      map_mul]
  have e := DFunLike.congr_fun levi34Diag_comp_isogenyStd A'
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, levi34HomK] at e
  rw [hA, hB] at e
  exact e

theorem levi34Diag_not_fix_sylow_pointwise
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup)) :
    ∃ p : (P : Subgroup (hopfMultiplier ↥stdGroup)),
      hopfCoverAut levi34Diag (((p : hopfMultiplier ↥stdGroup) :
        HopfCover ↥stdGroup)) ≠ ((p : hopfMultiplier ↥stdGroup) : HopfCover ↥stdGroup) := by
  classical
  by_contra h
  have hfixP : ∀ p : (P : Subgroup (hopfMultiplier ↥stdGroup)),
      hopfCoverAut levi34Diag (((p : hopfMultiplier ↥stdGroup) :
        HopfCover ↥stdGroup)) = ((p : hopfMultiplier ↥stdGroup) : HopfCover ↥stdGroup) := by
    intro p
    by_contra hp
    exact h ⟨p, hp⟩
  have hK : KE.map (hopfCoverAut levi34Diag).toMonoidHom ≤ KE :=
    Aux.KE_invariant levi34Diag P Q3 hfixP
  have hα : autCover epsE (alphaE' levi34Diag hK) = levi34Diag :=
    autCover_alphaE' levi34Diag hK
  letI : Group.IsPerfect Eprime := derived_Eam_facts.1
  letI : Finite Eprime := derived_Eam_facts.2.1
  have hE2 : Nat.card (Subgroup.center Eprime) = 2 := derived_Eam_facts.2.2.1
  have hδ' : ∀ A : SL(3, GaloisField 2 (2 * 1)),
      levi34Diag (isogenyStd (levi34Hom A)) =
        isogenyStd (levi34Hom (conjSLHom diagOmegaGLF A)) :=
    levi34Diag_comp_levi34Hom
  exact autCover_ne (X := Eprime) (ε := epsE) hE2
    (e := levi34Hom) levi34Hom_injective range_levi34Hom
    (g := diagOmegaGLF) det_diagOmegaGLF_ne_one hδ'
    (alphaE' levi34Diag hK) hα

theorem hopfCoverAutOnSylowTwo_coe
    (δ : MulAut ↥stdGroup) (P : Sylow 2 (hopfMultiplier ↥stdGroup))
    (p : (P : Subgroup (hopfMultiplier ↥stdGroup))) :
    ((hopfCoverAutOnSylowTwo δ P p : (P : Subgroup (hopfMultiplier ↥stdGroup))) :
      HopfCover ↥stdGroup) =
      hopfCoverAut δ ((p : hopfMultiplier ↥stdGroup) : HopfCover ↥stdGroup) :=
  rfl

theorem levi34Diag_sylow_action_ne
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup)) :
    hopfCoverAutOnSylowTwo levi34Diag P ≠ 1 := by
  intro h1
  obtain ⟨p, hp⟩ := levi34Diag_not_fix_sylow_pointwise P Q3
  apply hp
  have h2 : hopfCoverAutOnSylowTwo levi34Diag P p = p := by
    simpa using congrArg (fun f : MulAut (P : Subgroup (hopfMultiplier ↥stdGroup)) => f p) h1
  have h3 := congrArg (fun q : (P : Subgroup (hopfMultiplier ↥stdGroup)) =>
    (q : HopfCover ↥stdGroup)) h2
  simpa [hopfCoverAutOnSylowTwo_coe] using h3

end Nontriviality

end KernelInvariance

theorem levi34Diag_hopfMultiplier_fixed_two_eq_one
    [Finite ↥stdGroup] [Group.IsPerfect ↥stdGroup]
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup))
    {z : HopfCover ↥stdGroup} (hzM : z ∈ hopfMultiplier ↥stdGroup)
    (hz2 : ∃ k : ℕ, z ^ (2 ^ k) = 1)
    (hfix : hopfCoverAut levi34Diag z = z) : z = 1 :=
  hopfCoverAut_fixed_two_eq_one levi34Diag levi34Diag_pow_three P
    (hopfMultiplier_sylow_two_card P) (levi34Diag_sylow_action_ne P Q3) hzM hz2 hfix

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

end
