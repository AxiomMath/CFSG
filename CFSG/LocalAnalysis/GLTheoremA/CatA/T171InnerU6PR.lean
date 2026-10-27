module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6Trans
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Tools
import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall
import CFSG.GroupTheory.PerfectCoverProduct
import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Ja

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171U6

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KU6Cent
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

private theorem ne_one_of_isPR {g : PGU6} (hg : IsPR g) : g ≠ 1 := by
  rintro rfl
  obtain ⟨ĝ, P, a, b, i, hmk, hab, hmat⟩ := hg
  have hZG : (P⁻¹ * ĝ * P) ∈ ZG := by
    rw [← QuotientGroup.eq_one_iff]
    have hmk1 : (QuotientGroup.mk ĝ : PGU6) = 1 := hmk
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmk1]
  obtain ⟨c, hc⟩ := mem_ZG.mp hZG
  have hmat' : ((Matrix.GeneralLinearGroup.scalar (Fin 6) c : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal (Function.update (fun _ => a) i b) := by
    rw [hc]
    exact hmat
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by norm_num : 1 < Fintype.card (Fin 6)) i
  have hii := congrFun (congrFun hmat' i) i
  have hjj := congrFun (congrFun hmat' j) j
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
    Function.update_self, if_true] at hii hjj
  rw [Function.update_apply, if_neg hji] at hjj
  exact hab (hjj.symm.trans hii)

theorem stepPR_holds :
    PRFix → ∀ (Ω : Type) [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω) (L : Subgroup Ω) [L.Normal]
      (e : ↥L ⧸ Subgroup.center ↥L ≃* S6), Setup B x L →
      ∀ b ∈ B, ∀ g : PGU6, Psi g = theta L e b → ¬ IsPR g := by
  intro hPRfix Ω _ _ B x L _ e hSetup b hbB g hPsi hPR
  classical
  have hc := hSetup.cfg
  have hBel : IsElemAbelian 3 B := hc.elem
  have hx3 : x ^ 3 = 1 := hBel.2 x hc.mem
  have hx1 : x ≠ 1 := hc.ne_one
  have hb3 : b ^ 3 = 1 := hBel.2 b hbB
  have hLperf : Group.IsPerfect ↥L := isPerfect_of_cfg hc
  haveI : Group.IsPerfect ↥L := hLperf
  have hxL : x ∈ Subgroup.centralizer (L : Set Ω) :=
    (hc.cent x hc.mem).mpr (Subgroup.mem_zpowers x)
  have hg1 : g ≠ 1 := ne_one_of_isPR hPR
  have hb_not_zp : b ∉ Subgroup.zpowers x := by
    intro hbzx
    have hbcent : b ∈ Subgroup.centralizer (L : Set Ω) := (hc.cent b hbB).mpr hbzx
    have hθ : theta L e b = 1 := (theta_eq_one_iff e b).mpr hbcent
    have : Psi g = Psi 1 := by rw [hPsi, hθ, map_one]
    exact hg1 (Psi_injective this)
  let D : Subgroup Ω := Subgroup.zpowers x ⊔ Subgroup.zpowers b
  have hxD : x ∈ D := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hbD : b ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hDleB : D ≤ B :=
    sup_le (Subgroup.zpowers_le.mpr hc.mem) (Subgroup.zpowers_le.mpr hbB)
  have hcomm_bx : b * x = x * b := isElemAbelian_commute hBel hbB hc.mem
  have hDinfo := Prop53.isElemAbelian_card_sup_zpowers (p := 3) Nat.prime_three
    (a := b) (b := x) hcomm_bx hb3 hx3 hx1 hb_not_zp
  have hDel : IsElemAbelian 3 D := by
    have h := hDinfo.1
    rwa [sup_comm] at h
  have hDcard : Nat.card D = 3 ^ 2 := by
    have h := hDinfo.2
    rwa [sup_comm] at h
  have hcentD : Subgroup.centralizer (D : Set Ω) = S8.cx x ⊓ S8.cx b :=
    S8.L84.centralizer_eq_inf hDel hDcard hxD hx1 hbD hb_not_zp
  let M : Subgroup Ω := L ⊓ Subgroup.centralizer ({b} : Set Ω)
  have hML : M ≤ L := inf_le_left
  have hMCb : M ≤ Subgroup.centralizer ({b} : Set Ω) := inf_le_right
  have hLleCx : L ≤ Subgroup.centralizer ({x} : Set Ω) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hxL l hl
  have hM_eq : L ⊓ Subgroup.centralizer (D : Set Ω) = M := by
    rw [hcentD]
    ext m
    constructor
    · rintro ⟨hmL, -, hmb⟩
      exact ⟨hmL, hmb⟩
    · rintro ⟨hmL, hmb⟩
      exact ⟨hmL, hLleCx hmL, hmb⟩
  let F : Subgroup S6 := fixSubgroup (Psi g)
  have hFtheta : F = fixSubgroup (theta L e b) := by
    dsimp [F]
    rw [hPsi]
  have hFsimple : IsSimpleGroup ↥F := (hPRfix g hPR).1
  haveI : IsSimpleGroup ↥F := hFsimple
  have hFperf : ⁅F, F⁆ = F := (hPRfix g hPR).2.1
  have h11F : 11 ∣ Nat.card ↥F := (hPRfix g hPR).2.2.1
  have hPRcent := (hPRfix g hPR).2.2.2
  have hFperfTheta : ⁅fixSubgroup (theta L e b), fixSubgroup (theta L e b)⁆ =
      fixSubgroup (theta L e b) := by
    rw [← hFtheta]
    exact hFperf
  have himL_M : imL e M = F := by
    apply le_antisymm
    · rw [hFtheta]
      refine imL_le_fixSubgroup e (H := M) (g := b) ?_
      intro m hm
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hMCb hm)).symm
    · rw [hFtheta]
      exact le_imL_centralizer e le_rfl hFperfTheta
  let gM : ↥M →* S6 := (piL e).comp (Subgroup.inclusion hML)
  have hgM_mem : ∀ m : ↥M, gM m ∈ F := by
    intro m
    have hm : gM m ∈ imL e M :=
      Subgroup.mem_map_of_mem (piL e) (Subgroup.mem_subgroupOf.mpr m.2)
    rwa [himL_M] at hm
  let φ : ↥M →* ↥F := gM.codRestrict F hgM_mem
  have hφ_apply : ∀ m : ↥M, (φ m : S6) = piL e ⟨(m : Ω), hML m.2⟩ := fun _ => rfl
  have hφsurj : Function.Surjective φ := by
    intro s
    have hs : (s : S6) ∈ imL e M := by rw [himL_M]; exact s.2
    obtain ⟨l, hl, hls⟩ := Subgroup.mem_map.mp hs
    refine ⟨⟨l, Subgroup.mem_subgroupOf.mp hl⟩, Subtype.ext ?_⟩
    rw [hφ_apply]
    have hml : (⟨((⟨l, Subgroup.mem_subgroupOf.mp hl⟩ : ↥M) : Ω),
        hML (⟨l, Subgroup.mem_subgroupOf.mp hl⟩ : ↥M).2⟩ : ↥L) = l := Subtype.ext rfl
    rw [hml]
    exact hls
  have hφker : φ.ker ≤ Subgroup.center ↥M := by
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    rw [Subgroup.mem_center_iff]
    intro m'
    have hm1 : piL e ⟨(m : Ω), hML m.2⟩ = 1 := by
      have h := congrArg Subtype.val hm
      rwa [hφ_apply] at h
    have hmZ : (⟨(m : Ω), hML m.2⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [← ker_piL e, MonoidHom.mem_ker]
      exact hm1
    apply Subtype.ext
    change ((m' * m : ↥M) : Ω) = ((m * m' : ↥M) : Ω)
    exact congrArg (fun x : ↥L => (x : Ω))
      (Subgroup.mem_center_iff.mp hmZ ⟨(m' : Ω), hML m'.2⟩)
  have htopPerf : Group.IsPerfect ↥F := Subgroup.isPerfect_iff.mpr hFperf
  haveI : Group.IsPerfect ↥F := htopPerf
  have hFtopPerf : Group.IsPerfect ↥(⊤ : Subgroup ↥F) :=
    Group.IsPerfect.ofSurjective (f := Subgroup.topEquiv.symm.toMonoidHom)
      (fun x => ⟨Subgroup.topEquiv x, Subgroup.topEquiv.symm_apply_apply x⟩)
  have hLtop : ⁅(⊤ : Subgroup ↥F), (⊤ : Subgroup ↥F)⁆ = ⊤ :=
    (Subgroup.isPerfect_iff (H := (⊤ : Subgroup ↥F))).mp hFtopPerf
  let Q : Subgroup ↥M := ⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆
  have hQperf : Group.IsPerfect ↥Q := by
    have h := CFSG.GroupTheory.PerfectCover.isPerfect_commutator_comap φ hφsurj hφker hLtop
    rw [Subgroup.comap_top] at h
    exact h
  have hQmap : Q.map φ = ⊤ := by
    have h := CFSG.GroupTheory.PerfectCover.map_commutator_comap φ hφsurj hLtop
    rw [Subgroup.comap_top] at h
    exact h
  have hFcenter : Subgroup.center ↥F = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
      (Group.IsPerfect.not_isMulCommutative ↥F)
  have hFquasi : CFSG.Open.IsQuasisimple ↥F := by
    refine ⟨Group.isPerfect_def.mp htopPerf, ?_⟩
    let eF : (↥F ⧸ Subgroup.center ↥F) ≃* ↥F :=
      (QuotientGroup.quotientMulEquivOfEq hFcenter).trans QuotientGroup.quotientBot
    exact eF.isSimpleGroup
  have hQsurj : Function.Surjective (φ.comp Q.subtype) := by
    intro s
    have hs : s ∈ Q.map φ := by rw [hQmap]; exact Subgroup.mem_top s
    obtain ⟨m, hm, hmφ⟩ := Subgroup.mem_map.mp hs
    exact ⟨⟨m, hm⟩, hmφ⟩
  have hQker : (φ.comp Q.subtype).ker ≤ Subgroup.center ↥Q := by
    intro q hq
    rw [Subgroup.mem_center_iff]
    intro r
    have hq' : ((q : ↥Q) : ↥M) ∈ φ.ker := hq
    apply Subtype.ext
    change ((r * q : ↥Q) : ↥M) = ((q * r : ↥Q) : ↥M)
    exact Subgroup.mem_center_iff.mp (hφker hq') (r : ↥M)
  have hQqs : CFSG.Open.IsQuasisimple ↥Q :=
    CFSG.HardMathSupport.Solomon.Coordinator.i253_isQuasisimple_of_perfect_cover
      (Group.isPerfect_def.mp hQperf) hFquasi (φ.comp Q.subtype) hQsurj hQker
  let J : Subgroup Ω := Q.map M.subtype
  have hJ_eq : J = ⁅M, M⁆ := by
    dsimp [J, Q]
    rw [Subgroup.map_commutator]
    simp only [Subgroup.map_top, Subgroup.range_subtype]
  have hJ_le_M : J ≤ M := Subgroup.map_subtype_le Q
  have hJ_le_L : J ≤ L := hJ_le_M.trans hML
  have hJqs : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective Q M.subtype M.subtype_injective) hQqs
  have hJnormal : (J.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJ_le_M, hJ_eq]
    exact Subgroup.normalizer_commutator_ge_left M M
  have hJcomp : IsComponentOf J M :=
    ⟨hJ_le_M, IsSubnormal.step hJ_le_M hJnormal (IsSubnormal.refl M), hJqs⟩
  have hJ_imL : imL e J = F := by
    apply le_antisymm
    · rintro s ⟨l, hl, rfl⟩
      rw [← himL_M]
      exact Subgroup.mem_map_of_mem (piL e)
        (Subgroup.mem_subgroupOf.mpr (hJ_le_M (Subgroup.mem_subgroupOf.mp hl)))
    · intro s hs
      have hs' : (⟨s, hs⟩ : ↥F) ∈ Q.map φ := by
        rw [hQmap]
        exact Subgroup.mem_top _
      obtain ⟨m, hm, hmφ⟩ := Subgroup.mem_map.mp hs'
      refine Subgroup.mem_map.mpr ⟨⟨(m : Ω), hML m.2⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨m, hm, rfl⟩)
      · exact congrArg Subtype.val hmφ
  have hlayer : GLALayer M = J := by
    rw [I142N.GLALayer_eq_sSup]
    apply le_antisymm
    · refine sSup_le ?_
      intro K hK
      have hKperf : ⁅K, K⁆ = K :=
        (Subgroup.isPerfect_iff (H := K)).mp (Group.isPerfect_def.mpr hK.2.2.1)
      calc K = ⁅K, K⁆ := hKperf.symm
        _ ≤ ⁅M, M⁆ := Subgroup.commutator_mono hK.1 hK.1
        _ = J := hJ_eq.symm
    · exact le_sSup hJcomp
  have hxJ : x ∈ Subgroup.centralizer (J : Set Ω) :=
    Subgroup.mem_centralizer_iff.mpr fun j hj =>
      Subgroup.mem_centralizer_iff.mp hxL j (hJ_le_L hj)
  have hbJ : b ∈ Subgroup.centralizer (J : Set Ω) :=
    Subgroup.mem_centralizer_iff.mpr fun j hj =>
      Subgroup.mem_centralizer_singleton_iff.mp (hMCb (hJ_le_M hj))
  have hDleCJ : D ≤ Subgroup.centralizer (J : Set Ω) :=
    sup_le (Subgroup.zpowers_le.mpr hxJ) (Subgroup.zpowers_le.mpr hbJ)
  have hD_eq : D = B ⊓ Subgroup.centralizer (J : Set Ω) := by
    apply le_antisymm (le_inf hDleB hDleCJ)
    intro b' hb'
    obtain ⟨hb'B, hb'C⟩ := Subgroup.mem_inf.mp hb'
    have hb'3 : b' ^ 3 = 1 := hBel.2 b' hb'B
    have hθ3 : theta L e b' ^ 3 = 1 := by rw [← map_pow, hb'3, map_one]
    obtain ⟨h, hhPsi⟩ := exists_Psi_of_pow_three (theta L e b') hθ3
    have hfix : ∀ s ∈ F, Psi h s = s := by
      intro s hs
      rw [← hJ_imL] at hs
      obtain ⟨l, hl, hls⟩ := Subgroup.mem_map.mp hs
      rw [← hls, hhPsi, theta_piL]
      congr 1
      apply Subtype.ext
      have hcomm : (l : Ω) * b' = b' * (l : Ω) :=
        Subgroup.mem_centralizer_iff.mp hb'C (l : Ω) (Subgroup.mem_subgroupOf.mp hl)
      calc b' * (l : Ω) * b'⁻¹ = ((l : Ω) * b') * b'⁻¹ := by rw [hcomm.symm]
        _ = (l : Ω) := by group
    have hz : h ∈ Subgroup.zpowers g := hPRcent h hfix
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hθeq : theta L e b' = theta L e (b ^ n) := by
      rw [← hhPsi, ← hn, MonoidHom.map_zpow, hPsi, MonoidHom.map_zpow]
    have hker : b' * (b ^ n)⁻¹ ∈ (theta L e).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hθeq, mul_inv_cancel]
    have hcent' : b' * (b ^ n)⁻¹ ∈ Subgroup.centralizer (L : Set Ω) :=
      (theta_eq_one_iff e (b' * (b ^ n)⁻¹)).mp hker
    have hmemB : b' * (b ^ n)⁻¹ ∈ B :=
      B.mul_mem hb'B (B.inv_mem (Subgroup.zpow_mem B hbB n))
    have hmem : b' * (b ^ n)⁻¹ ∈ Subgroup.zpowers x :=
      (hc.cent (b' * (b ^ n)⁻¹) hmemB).mp hcent'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hb'eq : b' = x ^ k * b ^ n := by
      rw [hk]
      group
    rw [hb'eq]
    exact D.mul_mem (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) n))
  have hstd : GLAStdSubPre 3 B x L D J := by
    refine ⟨hDleB, hDel, hDcard, hxD, ?_, ?_, hD_eq⟩
    · rw [hM_eq]
      exact hlayer.symm
    · rw [hM_eq]
      exact hJcomp
  have hsmall : GLASmall J := hSetup.small D J hstd
  have h11J : 11 ∣ Nat.card J := by
    have hdvd : Nat.card ↥F ∣ Nat.card J := by
      have h1 : Nat.card (imL e J) ∣ Nat.card (J.subgroupOf L) := Subgroup.card_map_dvd _ _
      rw [hJ_imL] at h1
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ_le_L).toEquiv] at h1
    exact h11F.trans hdvd
  rcases hsmall with hU | hA6
  · have hcard : Nat.card J = 25920 := CFSG.StandardType.IOneOrthEnd.card_of_isU42 hU
    rw [hcard] at h11J
    norm_num at h11J
  · obtain ⟨e6⟩ := hA6
    have hcard : Nat.card J = 360 := by
      rw [Nat.card_congr e6.toEquiv, CFSG.StandardType.IOneOrthEnd.card_alternatingGroup_six]
    rw [hcard] at h11J
    norm_num at h11J

end CFSG.LocalAnalysis.GLTheoremA.T171U6

end
