module

public import CFSG.ClassicalInvolution.Q3.Q3MTShapeB
public import CFSG.ClassicalInvolution.Asc77.AscT8ZC1
public import CFSG.ClassicalInvolution.Q3.Q3T8P26D01
import CFSG.ClassicalInvolution.Asc77.AscT8ZC2EngB

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.T8YY
open CFSG.ClassicalInvolution.RouteD.Gaps (InvOf)
namespace T8ZZ
open CFSG.ClassicalInvolution.Asc77.T8ZZ
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_layerDatum [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hnconn : ¬ DConnected (Q3T7.layerFam3 Ω (z * t))) (F : T8YY.FrameData Ω W K J z t) :
    ∃ e : ℕ, ∃ M : Ih8Model 3 1 (Q3T7.layerFam3 Ω (z * t))
        CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus 4 e, e = 1 ∧
      ∃ Rs : Fin 4 → Subgroup (modelUniv CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus 4 3 e
          Fact.out).K,
        (∀ i, Rs i ∈ M.cls) ∧
          (∀ i, Layer.layerImg3 Ω (z * t) (F.ρ i).K = (Rs i).map M.ψ) ∧
            ∀ i j, i ≠ j → Commutes (Rs i) (Rs j) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hs3 := hs.stand.toStand3
  have hKx : T8.XMem Ω (z * t) K := Layer.xMem_zt3 hs
  have hKt : K ∈ Q3NL.tqMembers3 Ω (z * t) := hKx.mem_tqMembers3 hΩ hx
  have hKt' : ∀ {L : Subgroup G}, T8.XMem Ω (z * t) L → L ∈ Q3NL.tqMembers3 Ω (z * t) :=
    fun h => h.mem_tqMembers3 hΩ hx
  have hne0 : (Q3NL.tqMembers3 Ω (z * t)).Nonempty := ⟨K, hKt⟩
  have hL : Layer.LayerHyp Ω (z * t) := Layer.LayerHyp.of_stand3 hs3 hx hne0
  have hc2 : IsPGroup 2 (Subgroup.zpowers (z * t)) := hL.hc2
  have hlt := Q3T7.card_layerQuot3_lt (Ω := Ω) (Layer.zt_not_central3 hs)
  have hΨ := Q3T7.hypOmegaModU_layerFam3 hs3 hc2 hne0
  have hinj : Function.Injective
      (fun i : Fin 3 => Layer.layerImg3 Ω (z * t) (F.ρ i.castSucc).K) := by
    intro i j h
    by_contra hij
    exact frame_layerImg_ne hs F (fun h' => hij (Fin.castSucc_injective _ h')) h
  obtain ⟨e, ⟨M⟩⟩ := T8X.exists_spin8_datum_of_triangle hs.stand.ih hs.stand.below hlt hΨ
    Q3T7.layerQuot3_oddCore_eq_bot (Q3T7.omegaGen_layerFam3 hs3 hc2 hne0)
    (Q3T7.aEmpty_layerFam3 hs3 hc2 hne0)
    (fun i : Fin 3 => Layer.layerImg3 Ω (z * t) (F.ρ i.castSucc).K)
    (fun i => Layer.layerImg3_mem (hKt' (frame_xMem hs F _))) hinj
    (fun i j hij => frame_layerImg_nbr hs F (fun h' => hij (Fin.castSucc_injective _ h')))
    hnconn
  have hD4 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .trialityD4 := by decide
  have hG2 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .G2 := by decide
  have he : e = 1 := M.exp_eq_f hD4
  have hrep : ∀ i : Fin 4, ∃ Ri ∈ M.cls, Layer.layerImg3 Ω (z * t) (F.ρ i).K = Ri.map M.ψ :=
    fun i => (M.mem_iff _).mp (Layer.layerImg3_mem (hKt' (frame_xMem hs F i)))
  choose Rs hRs hRsψ using hrep
  refine ⟨e, M, he, Rs, hRs, hRsψ, fun i j hij => ?_⟩
  have hadj : (Rs j).map M.ψ ∈
      omegaNbr (Q3T7.layerFam3 Ω (z * t)) ((Rs i).map M.ψ) := by
    rw [← hRsψ i, ← hRsψ j]
    exact frame_layerImg_nbr hs F hij
  exact ((Q3MT.omegaNbr_iff3 M hΨ hG2 hD4 (hRs i) (hRs j)).mp hadj).2

theorem layerImg_nbr_eq_frame [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hnconn : ¬ DConnected (Q3T7.layerFam3 Ω (z * t))) (F : T8YY.FrameData Ω W K J z t)
    {L : Subgroup G} (hL : T8.XMem Ω (z * t) L)
    (hadj : Layer.layerImg3 Ω (z * t) L ∈
      omegaNbr (Q3T7.layerFam3 Ω (z * t)) (Layer.layerImg3 Ω (z * t) K)) :
    ∃ j : Fin 4, j ≠ 0 ∧ Layer.layerImg3 Ω (z * t) L = Layer.layerImg3 Ω (z * t) (F.ρ j).K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hs3 := hs.stand.toStand3
  have hKx : T8.XMem Ω (z * t) K := Layer.xMem_zt3 hs
  have hKt : K ∈ Q3NL.tqMembers3 Ω (z * t) := hKx.mem_tqMembers3 hΩ hx
  have hKt' : ∀ {L : Subgroup G}, T8.XMem Ω (z * t) L → L ∈ Q3NL.tqMembers3 Ω (z * t) :=
    fun h => h.mem_tqMembers3 hΩ hx
  have hne0 : (Q3NL.tqMembers3 Ω (z * t)).Nonempty := ⟨K, hKt⟩
  have hLH : Layer.LayerHyp Ω (z * t) := Layer.LayerHyp.of_stand3 hs3 hx hne0
  have hc2 : IsPGroup 2 (Subgroup.zpowers (z * t)) := hLH.hc2
  have hΨ := Q3T7.hypOmegaModU_layerFam3 hs3 hc2 hne0
  obtain ⟨e, M, he, Rs, hRs, hRsψ, hcomm⟩ := exists_layerDatum hs hnconn F
  subst he
  have hD4 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .trialityD4 := by decide
  have hG2 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .G2 := by decide
  obtain ⟨S₀, hS₀, hLS⟩ := (M.mem_iff _).mp (Layer.layerImg3_mem (hKt' hL))
  have hK0 : Layer.layerImg3 Ω (z * t) K = (Rs 0).map M.ψ := by
    rw [← hRsψ 0, F.h0]
  rw [hLS, hK0] at hadj
  obtain ⟨hne0, hc0⟩ := (Q3MT.omegaNbr_iff3 M hΨ hG2 hD4 (hRs 0) hS₀).mp hadj
  obtain ⟨R₂, h₂, R₃, h₃, R₄, h₄, -, -, -, -, -, -, -, -, -, -, -, -, hall⟩ :=
    Q3MT.clique_plus3 (M.cls_sub (hRs 0))
  have hfr : ∀ i : Fin 4, i ≠ 0 → Rs i = R₂ ∨ Rs i = R₃ ∨ Rs i = R₄ := by
    intro i hi
    have hne : Rs 0 ≠ Rs i := by
      intro h
      have := congrArg (fun A => A.map M.ψ) h
      beta_reduce at this
      rw [← hRsψ 0, ← hRsψ i] at this
      exact frame_layerImg_ne hs F (Ne.symm hi) this
    exact hall (Rs i) (M.cls_sub (hRs i)) (Ne.symm hne) (hcomm 0 i (Ne.symm hi))
  have hSc : S₀ = R₂ ∨ S₀ = R₃ ∨ S₀ = R₄ :=
    hall S₀ (M.cls_sub hS₀) (Ne.symm hne0) hc0
  have hdist : ∀ i j : Fin 4, i ≠ j → Rs i ≠ Rs j := by
    intro i j hij h
    have := congrArg (fun A => A.map M.ψ) h
    beta_reduce at this
    rw [← hRsψ i, ← hRsψ j] at this
    exact frame_layerImg_ne hs F hij this
  have hcov := three_cover (hfr 1 (by decide)) (hfr 2 (by decide)) (hfr 3 (by decide)) hSc
    (hdist 1 2 (by decide)) (hdist 1 3 (by decide)) (hdist 2 3 (by decide))
  rcases hcov with h | h | h
  · exact ⟨1, by decide, by rw [hLS, h, ← hRsψ 1]⟩
  · exact ⟨2, by decide, by rw [hLS, h, ← hRsψ 2]⟩
  · exact ⟨3, by decide, by rw [hLS, h, ← hRsψ 3]⟩
end T8ZZ
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.T8YY
open scoped commutatorElement
namespace T8ZZ
open CFSG.ClassicalInvolution.Asc77.T8ZZ
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_xMem_of_omegaNbr (hΩ : HypOmegaMod Ω)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {K L : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hL : L ∈ omegaNbr Ω K) :
    ∃ P : Subgroup G, IsSylow2In P L ∧ (∀ r ∈ P, r * z = z * r) ∧
      z ∈ Subgroup.normalizer (L : Set G) := by
  exact CFSG.ClassicalInvolution.Asc77.T8ZZ.exists_xMem_of_omegaNbrE hΩ.conjInvariant
    (fun hM hR hRM => Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hM hR hRM)
    (fun hM => hΩ.exists_uniqueInvolution hM) (fun hR => hΩ.eight_le_of_mem_RSet hR) hnt hz hL

theorem commute_of_normalizes_sylow {L P : Subgroup G} (hP : IsPGroup 2 P) (hPL : P ≤ L) {a : G}
    (haP : conjSub a P = P) (hcomm : ∀ k ∈ L, ⁅a, k⁆ ∈ oddCoreOf L) {r : G} (hr : r ∈ P) :
    r * a = a * r := by
  exact CFSG.ClassicalInvolution.Asc77.T8ZZ.commute_of_normalizes_sylowE hP hPL haP hcomm hr

theorem exists_common_sylow (hs : Std8 Ω K J S R T W z t) {L : Subgroup G}
    (hLK : L ∈ omegaNbr Ω K) (hLJ : L ∈ omegaNbr Ω J) :
    ∃ P : Subgroup G, IsSylow2In P L ∧ (∀ r ∈ P, r * z = z * r) ∧ (∀ r ∈ P, r * t = t * r) ∧
      z ∈ Subgroup.normalizer (L : Set G) ∧ t ∈ Subgroup.normalizer (L : Set G) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  exact CFSG.ClassicalInvolution.Asc77.T8ZZ.exists_common_sylowE hs.hz hs.ht hLK hLJ
    (fun hz₀ hL₀ => exists_xMem_of_omegaNbr hΩ hnt hz₀ hL₀)
    (fun hR hy hym hyR => T8V.comm_mem_oddCoreOf_of_pow hΩ hLK.1 hR hy hym hyR)
    (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht)
    (T8.ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht)

theorem oddCore_commutes_zz [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) (F : T8YY.FrameData Ω W K J z t)
    (j : Fin 4) {n : G} (hn : n ∈ oddCoreOf (Q3NL.exactLayer3 Ω (z * t))) :
    n * F.zz j = F.zz j * n := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  obtain ⟨-, hαV'⟩ := T8YY.alphaOf_vGroup_eq hs F
  exact CFSG.ClassicalInvolution.Asc77.T8ZZ.oddCore_commutes_zzE F F.vGroup hαV' (fun j => F.zz0_mul_mem_vGroup c j)
    (T8T.oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ (z * t)) hα j hn

theorem eq_frame_of_layerImg_eq [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) (F : T8YY.FrameData Ω W K J z t)
    (j : Fin 4) {L : Subgroup G} (hL : T8.XMem Ω (z * t) L)
    (h : Layer.layerImg3 Ω (z * t) L = Layer.layerImg3 Ω (z * t) (F.ρ j).K) : L = (F.ρ j).K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hs3 := hs.stand.toStand3
  have hKx : T8.XMem Ω (z * t) K := Layer.xMem_zt3 hs
  have hKt : K ∈ Q3NL.tqMembers3 Ω (z * t) := hKx.mem_tqMembers3 hΩ hx
  have hKt' : ∀ {L : Subgroup G}, T8.XMem Ω (z * t) L → L ∈ Q3NL.tqMembers3 Ω (z * t) :=
    fun h => h.mem_tqMembers3 hΩ hx
  have hLH : Layer.LayerHyp Ω (z * t) := Layer.LayerHyp.of_stand3 hs3 hx ⟨K, hKt⟩
  obtain ⟨n, hn, hnK⟩ :=
    Layer.exists_oddCore_conj_of_layerImg3_eq hLH (hKt' (frame_xMem hs F j)) (hKt' hL) h.symm
  have hcomm := oddCore_commutes_zz hs hα F j hn
  have hz' : IsUniqueInvolution L (F.zz j) := by
    have h1 := (F.hz j).conj n
    rw [hnK] at h1
    have e : n * F.zz j * n⁻¹ = F.zz j := by
      rw [hcomm]
      group
    rwa [e] at h1
  exact hnt (F.ρ j).K (F.ρ j).hK L ⟨hL.1, F.zz j, F.hz j, hz'⟩

theorem commonNbr_mem_frame [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hnconn : ¬ DConnected (Q3T7.layerFam3 Ω (z * t)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) (F : T8YY.FrameData Ω W K J z t)
    {L : Subgroup G} (hLK : L ∈ omegaNbr Ω K) (hLJ : L ∈ omegaNbr Ω J) :
    ∃ j : Fin 4, j ≠ 0 ∧ L = (F.ρ j).K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hs3 := hs.stand.toStand3
  have hKx : T8.XMem Ω (z * t) K := Layer.xMem_zt3 hs
  have hKt : K ∈ Q3NL.tqMembers3 Ω (z * t) := hKx.mem_tqMembers3 hΩ hx
  have hKt' : ∀ {L : Subgroup G}, T8.XMem Ω (z * t) L → L ∈ Q3NL.tqMembers3 Ω (z * t) :=
    fun h => h.mem_tqMembers3 hΩ hx
  have hLH : Layer.LayerHyp Ω (z * t) := Layer.LayerHyp.of_stand3 hs3 hx ⟨K, hKt⟩
  obtain ⟨P, hP, hPz, hPt, hzN, htN⟩ := exists_common_sylow hs hLK hLJ
  have hLΩ : L ∈ Ω := hLK.1
  have hPx : P ≤ T8.cenZ (z * t) := fun r hr => by
    rw [T8.mem_cenZ_iff]
    calc r * (z * t) = (r * z) * t := by group
      _ = (z * r) * t := by rw [hPz r hr]
      _ = z * (r * t) := by group
      _ = z * (t * r) := by rw [hPt r hr]
      _ = z * t * r := by group
  have hXL : T8.XMem Ω (z * t) L :=
    ⟨hLΩ, Subgroup.mul_mem _ hzN htN, P, hP, fun r hr => T8.mem_cenZ_iff.mp (hPx hr)⟩
  obtain ⟨u, hu⟩ := hΩ.exists_uniqueInvolution hLΩ
  have h8 := hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hLΩ hP)
  have huP : u ∈ P := T3.mem_of_isPGroup hu hP.1 hP.2.1 (by omega)
  have hzu : z * u = u * z := (hPz u huP).symm
  have hne : Layer.layerImg3 Ω (z * t) K ≠ Layer.layerImg3 Ω (z * t) L :=
    Layer.layerImg3_ne_of_involutions hLH hKx hXL hs.hz hu hzu
      (T8.ne_of_mem_omegaNbr hs.noTwins hLK hs.hz hu)
  have hPN : P ≤ Subgroup.normalizer (K : Set G) := fun r hr =>
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hs.stand.mem hs.noTwins hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr (hPz r hr))
  have hadj := Layer.layerImg3_omegaNbr hKt (hKt' hXL) hP hPx hPN hne
  obtain ⟨j, hj0, hj⟩ := layerImg_nbr_eq_frame hs hnconn F hXL hadj
  exact ⟨j, hj0, eq_frame_of_layerImg_eq hs hα F j hXL hj⟩
end T8ZZ
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.T8YY
open scoped commutatorElement
namespace T8ZZ
open CFSG.ClassicalInvolution.Asc77.T8ZZ
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

variable [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AlphaFrame3] in
theorem ncard_commonNbr_le [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (huni : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      ¬ DConnected (Q3T7.layerFam3 Ω (z * s)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) {M : Subgroup G}
    (hM : M ∈ omegaNbr Ω K) : (omegaNbr Ω K ∩ omegaNbr Ω M).ncard ≤ 2 := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  obtain ⟨s, hs'⟩ := hΩ.exists_uniqueInvolution hM.1
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  have hframe := T8YY.exists_fuzzyFrame hs hμ hnc
  obtain ⟨S', R', T', W', hstd⟩ :=
    c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hs.hz M hM s hs'
  have hμ' := T8YY.muIsoWylD4_transfer hs.stand.modU hs.hW.1 hstd.hW.1 hμ
  have hnc' : ¬ DbarConnected Ω W' := T8X.not_dbarConnected_of_ne hstd hne
  obtain ⟨F'⟩ := T8YY.exists_frameData hstd hμ' hnc'
  have hα' : alphaOf (Subgroup.closure ({s, z} : Set G)) = ⊥ := by
    rw [(T8U.alphaOf_eq_of_omegaNbr_frame hs.stand hs.noTwins hframe hs.hz hs' hs.ht hM
      hs.hJ).symm]
    exact hα
  have hsub : omegaNbr Ω K ∩ omegaNbr Ω M ⊆ {(F'.ρ 2).K, (F'.ρ 3).K} := by
    rintro L ⟨hLK, hLM⟩
    obtain ⟨j, hj0, hjL⟩ := commonNbr_mem_frame hstd (huni M hM s hs') hα' F' hLK hLM
    have hj1 : j ≠ 1 := by
      rintro rfl
      exact hLM.2.1 (by rw [hjL, F'.h1])
    fin_cases j
    · exact absurd rfl hj0
    · exact absurd rfl hj1
    · exact Or.inl hjL
    · exact Or.inr hjL
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
  refine (Set.ncard_insert_le _ _).trans ?_
  rw [Set.ncard_singleton]

variable [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AlphaFrame3] in
theorem commonNbr_frame_eq [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (huni : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      ¬ DConnected (Q3T7.layerFam3 Ω (z * s)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) (F : T8YY.FrameData Ω W K J z t)
    {j : Fin 4} (hj : j ≠ 0) {L : Subgroup G} (hLK : L ∈ omegaNbr Ω K)
    (hLj : L ∈ omegaNbr Ω (F.ρ j).K) : ∃ i : Fin 4, i ≠ 0 ∧ i ≠ j ∧ L = (F.ρ i).K := by
  exact CFSG.ClassicalInvolution.Asc77.T8ZZ.commonNbr_frame_eq_of F hj hLK hLj
    (fun hM => ncard_commonNbr_le hs hdisc hμ hne huni hα hM)
end T8ZZ
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
