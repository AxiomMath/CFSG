module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAS6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAPk
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGALft
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClTwoU43
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClTwoU43Aut
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkBasic
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTInd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimCard

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fj_pi_not_mem_of_perfect_fix (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1)
    {σ : MulAut (omegaGroup hQ)} (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    {J : Subgroup (omegaGroup hQ)} (hJ : ⁅J, J⁆ = J) (hJσ : J ≤ fixSub σ) :
    (⟨piOrth Q, ff_piOrth_mem_omegaGroup_six_minus hQ hdim hs⟩ : omegaGroup hQ) ∉ J := by
  obtain ⟨γ, hγ, hσeq⟩ := cl_exists_simil_of_mulAut_six_minus hQ hdim hs σ hσσ
  have hsim_fix (ha : (γ : V ≃ₗ[ZMod 3] V) = 1 ∨
      (γ : V ≃ₗ[ZMod 3] V) = LinearEquiv.neg (ZMod 3)) :
      ∀ t : ↥(omegaGroup hQ), simAct Q γ (t : OGroup Q) = (t : OGroup Q) := by
    intro t
    rcases ha with ha | ha
    · apply Subtype.ext
      rw [coe_simAct, ha]
      simp
    · apply Subtype.ext
      rw [coe_simAct, ha]
      ext v
      simp [LinearEquiv.mul_apply, LinearEquiv.neg_apply, map_neg]
  have ha1 : (γ : V ≃ₗ[ZMod 3] V) ≠ 1 := by
    intro ha
    apply hσ1
    refine MulEquiv.ext fun t => ?_
    apply Subtype.ext
    rw [hσeq t, hsim_fix (Or.inl ha) t, MulAut.one_apply]
  have ha2 : (γ : V ≃ₗ[ZMod 3] V) ≠ LinearEquiv.neg (ZMod 3) := by
    intro ha
    apply hσ1
    refine MulEquiv.ext fun t => ?_
    apply Subtype.ext
    rw [hσeq t, hsim_fix (Or.inr ha) t, MulAut.one_apply]
  let J0 : Subgroup (V ≃ₗ[ZMod 3] V) :=
    (J.map (omegaGroup hQ).subtype).map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype
  have hJ0perf : ⁅J0, J0⁆ = J0 := by
    have hX : (J.map (omegaGroup hQ).subtype).map
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype = J0 := rfl
    rw [← hX, ← Subgroup.map_commutator (f :=
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype),
      ← Subgroup.map_commutator (f := (omegaGroup hQ).subtype), hJ]
  have hcomm : ∀ g ∈ J0, g * (γ : V ≃ₗ[ZMod 3] V) = (γ : V ≃ₗ[ZMod 3] V) * g := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    show ((t : ↥(omegaGroup hQ)) : V ≃ₗ[ZMod 3] V) * (γ : V ≃ₗ[ZMod 3] V) =
      (γ : V ≃ₗ[ZMod 3] V) * ((t : ↥(omegaGroup hQ)) : V ≃ₗ[ZMod 3] V)
    have hfix : σ t = t := hJσ ht
    have heq : ((t : ↥(omegaGroup hQ)) : OGroup Q) = simAct Q γ (t : OGroup Q) := by
      rw [← hσeq t]
      exact (congrArg Subtype.val hfix).symm
    have hcoe : ((t : ↥(omegaGroup hQ)) : V ≃ₗ[ZMod 3] V) =
        (γ : V ≃ₗ[ZMod 3] V) * ((t : ↥(omegaGroup hQ)) : V ≃ₗ[ZMod 3] V) *
          (γ : V ≃ₗ[ZMod 3] V)⁻¹ := by
      have h := congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V)) heq
      rw [coe_simAct] at h
      exact h
    conv_lhs => rw [hcoe]
    group
  have hnegJ0 : LinearEquiv.neg (ZMod 3) ∉ J0 :=
    cl_neg_not_mem_of_perfect_comm hdim hγ ha1 ha2 hJ0perf hcomm
  intro hpiJ
  apply hnegJ0
  have hpival : ((TauCeti.QuadraticMap.orthogonalGroup Q).subtype
      ((omegaGroup hQ).subtype
        (⟨piOrth Q, ff_piOrth_mem_omegaGroup_six_minus hQ hdim hs⟩ : omegaGroup hQ)) :
        V ≃ₗ[ZMod 3] V) = LinearEquiv.neg (ZMod 3) := by
    apply LinearEquiv.ext
    intro v
    change (piOrth Q : V ≃ₗ[ZMod 3] V) v = LinearEquiv.neg (ZMod 3) v
    rw [coe_piOrth_apply, LinearEquiv.neg_apply]
  rw [← hpival]
  exact Subgroup.mem_map.mpr ⟨(omegaGroup hQ).subtype
    (⟨piOrth Q, ff_piOrth_mem_omegaGroup_six_minus hQ hdim hs⟩ : omegaGroup hQ),
    Subgroup.mem_map.mpr ⟨_, hpiJ, rfl⟩, rfl⟩

theorem fjKGAAt_omegaGroup_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    FJKGAAt ↥(omegaGroup hQ) := by
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite ↥(omegaGroup hQ) := Subtype.finite
  haveI : Finite ↥(omegaProj hQ) :=
    Finite.of_surjective (omegaToProj hQ) (omegaToProj_surjective hQ)
  intro y B hy hB σ hσσ hσ1 hfix hσy
  have hq : CFSG.IsQuasisimple ↥(omegaGroup hQ) := isQuasisimple_omegaGroup_six_minus hQ hdim hs
  have hperf : commutator (omegaGroup hQ) = ⊤ := Group.isPerfect_def.mp hq.1
  have hρker : (omegaToProj hQ).ker ≤ Subgroup.center ↥(omegaGroup hQ) := fun m hm =>
    Subgroup.mem_center_iff.mpr (fun g => omegaToProj_ker_central hQ (MonoidHom.mem_ker.mp hm) g)
  set p : ↥(omegaGroup hQ) := ⟨piOrth Q, ff_piOrth_mem_omegaGroup_six_minus hQ hdim hs⟩ with hp
  have hpp : p * p = 1 := Subtype.ext piOrth_mul_self
  have hp1 : p ≠ 1 := fun h => piOrth_ne_one (by omega) (congrArg Subtype.val h)
  have hpc : p ∈ Subgroup.center ↥(omegaGroup hQ) :=
    Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) (g : OGroup Q))
  have hcen : ∀ z ∈ Subgroup.center ↥(omegaGroup hQ), z = 1 ∨ z = p := by
    obtain ⟨y0, -, huniq⟩ :=
      (Nat.card_eq_two_iff' (1 : Subgroup.center ↥(omegaGroup hQ))).mp
        (natCard_center_omegaGroup_six_minus hQ hdim hs)
    intro z hz
    by_cases h1 : z = 1
    · exact Or.inl h1
    · right
      have e1 : (⟨z, hz⟩ : Subgroup.center ↥(omegaGroup hQ)) = y0 :=
        huniq _ (fun h => h1 (congrArg Subtype.val h))
      have e2 : (⟨p, hpc⟩ : Subgroup.center ↥(omegaGroup hQ)) = y0 :=
        huniq _ (fun h => hp1 (congrArg Subtype.val h))
      exact congrArg Subtype.val (e1.trans e2.symm)
  have hker1 : ∀ x : ↥(omegaGroup hQ), omegaToProj hQ x = 1 → x = 1 ∨ x = p := by
    intro x hx
    rcases (omegaToProj_eq_one_iff hQ x).mp hx with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hker2 : ∀ x : ↥(omegaGroup hQ), (x = 1 ∨ x = p) → omegaToProj hQ x = 1 := by
    intro x hx
    rcases hx with rfl | rfl
    · exact map_one _
    · exact (omegaToProj_eq_one_iff hQ _).mpr (Or.inr rfl)
  have hqtop : CFSG.IsQuasisimple ↥(⊤ : Subgroup ↥(omegaGroup hQ)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq
  obtain ⟨a, -, hay⟩ := exists_noncomm_of_sl23PocketIn hqtop hB
  have hy2 : y ^ 2 = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy] at h
  have hyy : y * y = 1 := by rwa [pow_two] at hy2
  have hy1 : y ≠ 1 := fun h => by
    rw [h, orderOf_one] at hy
    omega
  have hyp : y ≠ p := fun h => hay (by rw [h]; exact Subgroup.mem_center_iff.mp hpc a)
  have hρy1 : omegaToProj hQ y ≠ 1 := fun h => (hker1 y h).elim hy1 hyp
  have hρy : orderOf (omegaToProj hQ y) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, hy2, map_one]) hρy1
  have hpB : p ∉ B := fj_central_not_mem_pocket hyy hy1 hpc hpp hp1 hyp hB.1 hB.2.2.2
  have hdis : Disjoint B (omegaToProj hQ).ker := by
    rw [Subgroup.disjoint_def]
    intro x hxB hxk
    rcases hker1 x (MonoidHom.mem_ker.mp hxk) with h | h
    · exact h
    · exact absurd (h ▸ hxB) hpB
  have hB' : Sl23PocketIn ⊤ (omegaToProj hQ y) (B.map (omegaToProj hQ)) :=
    fj_pocket_map_cover (omegaToProj hQ) (omegaToProj_surjective hQ) hρker hB hdis
  have hkerσ : ∀ n ∈ (omegaToProj hQ).ker, σ n ∈ (omegaToProj hQ).ker := by
    intro n hn
    have hnc : n ∈ Subgroup.center ↥(omegaGroup hQ) := hρker hn
    have hσc : σ n ∈ Subgroup.center ↥(omegaGroup hQ) := by
      rw [Subgroup.mem_center_iff] at hnc ⊢
      intro g
      obtain ⟨h, rfl⟩ := σ.surjective g
      rw [← map_mul, ← map_mul, hnc h]
    exact MonoidHom.mem_ker.mpr (hker2 _ (hcen _ hσc))
  obtain ⟨β, hσβ, hββ⟩ := sec63PT_exists_induced_aut (omegaToProj_surjective hQ) hσσ hkerσ
  have hβ1 : β ≠ 1 := by
    intro hβ
    apply hσ1
    exact sec63PT_eq_one_of_induced_eq_one hρker hperf
      (fun a => by rw [hσβ a, hβ, MulAut.one_apply])
  have hβy : β ≠ MulAut.conj (omegaToProj hQ y) := by
    intro hβ
    apply hσy
    have h1 : (MulAut.conj y)⁻¹ * σ = 1 := by
      refine sec63PT_eq_one_of_induced_eq_one hρker hperf (fun a => ?_)
      rw [MulAut.mul_apply, MulAut.conj_inv_apply, map_mul, map_mul, map_inv, hσβ a, hβ,
        MulAut.conj_apply]
      group
    exact (inv_mul_eq_one.mp h1).symm
  have hβfix : ∀ c ∈ B.map (omegaToProj hQ), β c = c := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← hσβ b, hfix b hb]
  obtain ⟨J, hJ, hJF, hBJ⟩ := fjKGAAt_omegaProj_six_minus hQ hdim hs (omegaToProj hQ y)
    (B.map (omegaToProj hQ)) hρy hB' β hββ hβ1 hβfix hβy
  rw [l34g_fix_eq_fixSub] at hJ
  have hJq : CFSG.IsQuasisimple ↥J := hJ.isQuasisimple
  have hJc : IsComponentIn (coverDerived (omegaToProj hQ) J) (fixSub σ) :=
    fj_isComponentIn_coverDerived (omegaToProj_surjective hQ) hρker hσβ hJ
  have hJq' := fj_isQuasisimple_coverDerived (omegaToProj_surjective hQ) hρker hJq
  have hJmap := fj_map_coverDerived (omegaToProj_surjective hQ) hρker hJq
  set Jh : Subgroup ↥(omegaGroup hQ) := coverDerived (omegaToProj hQ) J with hJh
  have hJperf : ⁅Jh, Jh⁆ = Jh := Subgroup.isPerfect_iff.mp hJq'.1
  have hpJ : p ∉ Jh := fj_pi_not_mem_of_perfect_fix hQ hdim hs hσσ hσ1 hJperf hJc.1
  have hJker : ∀ x ∈ Jh, omegaToProj hQ x = 1 → x = 1 := by
    intro x hx hx1
    rcases hker1 x hx1 with h | h
    · exact h
    · exact absurd (h ▸ hx) hpJ
  have hinjJ : Function.Injective ((omegaToProj hQ).comp Jh.subtype) := by
    intro x z hxz
    have h1 : omegaToProj hQ (((x⁻¹ * z : ↥Jh) : ↥(omegaGroup hQ))) = 1 := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
        show omegaToProj hQ (↑x) = omegaToProj hQ (↑z) from hxz, inv_mul_cancel]
    exact inv_mul_eq_one.mp (Subtype.ext (hJker _ (x⁻¹ * z).2 h1))
  let fJ : ↥Jh →* ↥(Jh.map (omegaToProj hQ)) := (omegaToProj hQ).subgroupMap Jh
  have hfJinj : Function.Injective fJ := fun x z hxz => hinjJ (congrArg Subtype.val hxz)
  let eJ : ↥Jh ≃* ↥(Jh.map (omegaToProj hQ)) :=
    MulEquiv.ofBijective fJ ⟨hfJinj, MonoidHom.subgroupMap_surjective _ _⟩
  have hJhF : InFStar Jh := by
    have h : InFStar (Jh.map (omegaToProj hQ)) := by
      rw [hJmap]
      exact hJF
    exact isFStarGroup_of_mulEquiv eJ.symm h
  have hBJh : B ≤ Jh := by
    refine (l34g_le_closure_odd hB.2.2.2).trans ((Subgroup.closure_le _).mpr ?_)
    rintro c ⟨hcB, hcodd⟩
    have hρc : omegaToProj hQ c ∈ J := hBJ (Subgroup.mem_map_of_mem _ hcB)
    rw [← hJmap] at hρc
    obtain ⟨j, hjJh, hjc⟩ := Subgroup.mem_map.mp hρc
    have hu : omegaToProj hQ (j⁻¹ * c) = 1 := by rw [map_mul, map_inv, hjc, inv_mul_cancel]
    rcases hker1 _ hu with h | h
    · have hcj : c = j := (inv_mul_eq_one.mp h).symm
      rw [hcj]
      exact hjJh
    · exfalso
      have hcj : c = j * p := by
        calc c = j * (j⁻¹ * c) := by rw [mul_inv_cancel_left]
          _ = j * p := by rw [h]
      obtain ⟨k, hk⟩ := hcodd
      have hcpow : c ^ (2 * k + 1) = 1 := by
        rw [← hk]
        exact pow_orderOf_eq_one c
      have hpodd : p ^ (2 * k + 1) = p := by
        rw [pow_succ, pow_mul, show p ^ 2 = 1 by rw [pow_two]; exact hpp, one_pow, one_mul]
      have hcomm : Commute j p := Subgroup.mem_center_iff.mp hpc j
      have h1 : j ^ (2 * k + 1) * p = 1 := by
        have h' := hcpow
        rwa [hcj, hcomm.mul_pow, hpodd] at h'
      have hjp : j ^ (2 * k + 1) = p := by
        calc j ^ (2 * k + 1) = j ^ (2 * k + 1) * p * p := by rw [mul_assoc, hpp, mul_one]
          _ = p := by rw [h1, one_mul]
      exact hpJ (hjp ▸ Subgroup.pow_mem Jh hjJh (2 * k + 1))
  exact ⟨Jh, by rw [l34g_fix_eq_fixSub]; exact hJc, hJhF, hBJh⟩

theorem fjKGAAt_of_isTwoU43 (hS : Asc82SchurU43) {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.IsQuasisimple Y) (h : IsTwoU43 Y) : FJKGAAt Y := by
  obtain ⟨W, i1, i2, i3, R, hR, hdim, hs, ⟨f⟩⟩ := hS Y hq h
  letI := i1
  letI := i2
  letI := i3
  exact fjKGAAt_of_mulEquiv f.symm (fjKGAAt_omegaGroup_six_minus hR hdim hs)

end CFSG.OddStandard.SmallF3.Omega
