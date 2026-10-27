module

public import CFSG.ClassicalInvolution.Q3.Q3T8Hyp51
public import CFSG.ClassicalInvolution.Q3.Q3T8P26B00
public import CFSG.ClassicalInvolution.Q3.Q3T8P26A01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26A03
public import CFSG.ClassicalInvolution.Asc77.AscT8YC4
public import CFSG.ClassicalInvolution.Q3.Q3T7P25B00
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A01
import CFSG.ClassicalInvolution.Asc77.AscT8YC4Eng
import CFSG.ClassicalInvolution.Asc77.AscT8T12Eng
import CFSG.ClassicalInvolution.Asc77.AscT8YAEng
import CFSG.ClassicalInvolution.Asc77.AscT8YC2Eng

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
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
    CFSG.ClassicalInvolution.Asc77.ExactLayer
namespace T8T
open CFSG.ClassicalInvolution.Asc77.T8T
section Triangle
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_triFrame_of_nbrs (hΩ : HypOmegaMod Ω)
    (hΩu : Uniform.HypOmegaModU (.sl2 3 1) Ω) {K J₁ J₂ : Subgroup G} {z t₁ t₂ : G} (hK : K ∈ Ω) (hz
        : IsUniqueInvolution K z)
    (h1 : IsUniqueInvolution J₁ t₁) (h2 : IsUniqueInvolution J₂ t₂) (hJ₁ : J₁ ∈ omegaNbr Ω K)
    (hJ₂ : J₂ ∈ omegaNbr Ω K) (h12 : J₂ ∈ omegaNbr Ω J₁) :
    ∃ R : Fin 3 → Subgroup G, TriFrame Ω ![K, J₁, J₂] ![z, t₁, t₂] R := by
  exact CFSG.ClassicalInvolution.Asc77.T8T.exists_triFrame_of_nbrsE
    (fun hA hB h => Q3CL.T3.omegaNbr_symm (l6_2) hΩ hA hB h)
    (fun hx hJ hy => Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hx hJ hy)
    (fun hA hR hRA =>
      Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hA hR hRA)
    (fun hc2 hA => ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩu hc2 hA)
    hK hz h1 h2 hJ₁ hJ₂ h12
end Triangle
section Alpha
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K : Subgroup G}
end Alpha
section Conn
end Conn
end T8T
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.AscP1Nine3
    CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Balance.Theorem5
namespace T8YY
open CFSG.ClassicalInvolution.Asc77.T8YY
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
namespace FrameData
open CFSG.ClassicalInvolution.Asc77.T8YY.FrameData

theorem exists_triFrame (hs : Std8 Ω K J S R T W z t) (F : FrameData Ω W K J z t) :
    ∃ R₃ : Fin 3 → Subgroup G, T8T.TriFrame Ω ![K, J, (F.ρ 2).K] ![z, t, F.zz 2] R₃ ∧
      F.zz 2 ∉ Subgroup.closure ({z, t} : Set G) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hz2 : IsUniqueInvolution (F.ρ 2).K (F.zz 2) := F.hz 2
  have h02 : (F.ρ 2).K ∈ omegaNbr Ω K := by
    have := F.hadj 0 2 (by decide)
    rwa [F.h0] at this
  have h12 : (F.ρ 2).K ∈ omegaNbr Ω J := by
    have := F.hadj 1 2 (by decide)
    rwa [F.h1] at this
  obtain ⟨R₃, hF⟩ := T8T.exists_triFrame_of_nbrs hΩ hs.stand.modU hK hs.hz hs.ht hz2 hs.hJ h02 h12
  refine ⟨R₃, hF, ?_⟩
  intro hmem
  have hcomm : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  rcases Thompson.eq_of_mem_closure_pair hs.hz.sq hs.ht.sq hcomm hmem with h | h | h | h
  · exact (F.hz 2).ne_one h
  · exact F.hinj 2 0 (by decide) (h.trans F.hz0.symm)
  · exact F.hinj 2 1 (by decide) (h.trans F.hz1.symm)
  · have h2 : F.zz 2 = F.zz 0 * F.zz 1 := by rw [h, F.hz0, F.hz1]
    have h3 : F.zz 3 = 1 := by
      have hp3 := F.hprod
      rw [← h2] at hp3
      have : F.zz 2 * F.zz 2 = 1 := (F.hz 2).sq
      calc F.zz 3 = (F.zz 2 * F.zz 2) * F.zz 3 := by rw [this, one_mul]
        _ = 1 := by rw [mul_assoc]; rw [← mul_assoc (F.zz 2)]; simpa [mul_assoc] using hp3
    exact (F.hz 3).ne_one h3
end FrameData

theorem exists_fuzzyFrame (hs : Std8 Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) : ∃ A₀, Q3NL.FuzzyFrame3 Ω A₀ := by
  obtain ⟨F⟩ := exists_frameData hs hμ hnc
  obtain ⟨R₃, hF, hind⟩ := F.exists_triFrame hs
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  exact ⟨_, fuzzyFrame3_of_triFrame hΩ hs.stand.modU hnt hF
    (by simpa using hind)⟩

variable [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AlphaFrame3] in
theorem alphaOf_eq_of_mem_dComp [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hframe : ∃ A₀, Q3NL.FuzzyFrame3 Ω A₀) {L : Subgroup G} (hL : L ∈ dComp Ω K) :
    L ∈ Ω ∧ ∀ L' ∈ omegaNbr Ω L, ∀ y y' : G, IsUniqueInvolution L y → IsUniqueInvolution L' y' →
      alphaOf (Subgroup.closure ({y', y} : Set G)) =
        alphaOf (Subgroup.closure ({t, z} : Set G)) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  induction hL with
  | refl =>
    refine ⟨hs.stand.mem, fun L' hL' y y' hy hy' => ?_⟩
    have hyz : y = z := hy.eq hs.hz
    subst hyz
    exact T8U.alphaOf_eq_of_omegaNbr_frame hs.stand hs.noTwins hframe hs.hz hs.ht hy' hs.hJ hL'
  | @tail b c hbk hbc ih =>
    obtain ⟨hbΩ, hPb⟩ := ih
    obtain ⟨hcΩ, hadj⟩ := hbc
    have hcb : c ∈ omegaNbr Ω b ∧ b ∈ omegaNbr Ω c := by
      rcases hadj with h | h
      · exact ⟨h, Q3CL.T3.omegaNbr_symm (l6_2) hΩ hbΩ hcΩ h⟩
      · exact ⟨Q3CL.T3.omegaNbr_symm (l6_2) hΩ hcΩ hbΩ h, h⟩
    refine ⟨hcΩ, fun L'' hL'' y₂ y'' hy₂ hy'' => ?_⟩
    obtain ⟨yb, hyb⟩ := hΩ.exists_uniqueInvolution hbΩ
    have h1 : alphaOf (Subgroup.closure ({y'', y₂} : Set G)) =
        alphaOf (Subgroup.closure ({yb, y₂} : Set G)) :=
      T8U.alphaOf_eq_of_omegaNbr_frame (hs.stand.of_mem hcΩ) (hnt c hcΩ) hframe hy₂ hyb hy''
        hcb.2 hL''
    have h2 : alphaOf (Subgroup.closure ({y₂, yb} : Set G)) =
        alphaOf (Subgroup.closure ({t, z} : Set G)) := hPb c hcb.1 yb y₂ hyb hy₂
    rw [h1, Set.pair_comm]
    exact h2

variable [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AlphaFrame3] in
theorem sigmaNorm_le_normalizer_alpha [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hframe : ∃ A₀, Q3NL.FuzzyFrame3 Ω A₀) :
    sigmaNorm Ω K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  intro n hn
  have hKn : conjSub n K ∈ dComp Ω K := (T8.mem_sigmaNorm_iff hΩ.conjInvariant hs.stand.mem).1 hn
  obtain ⟨-, hP⟩ := alphaOf_eq_of_mem_dComp hs hframe hKn
  have h := hP (conjSub n J) (omegaNbr_conj hΩ.conjInvariant hs.hJ n) (n * z * n⁻¹)
    (n * t * n⁻¹) (hs.hz.conj n) (hs.ht.conj n)
  rw [← conjSub_closure_pair, alphaOf_conjSub] at h
  exact mem_normalizer_iff_conjSub_eq.mpr h

variable [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AlphaFrame3] in
theorem centralizer_le_normalizer_alpha_of_nbr [IsSimpleGroup G]
    (hs : Std8 Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (hdisc : ¬ DConnected Ω) (hframe : ∃ A₀, Q3NL.FuzzyFrame3 Ω A₀)
    (hN : sigmaNorm Ω K ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G))
    {M : Subgroup G} (hM : M ∈ omegaNbr Ω K) {s : G} (hs' : IsUniqueInvolution M s)
    (hconn : DConnected (Q3T7.layerFam3 Ω (z * s))) :
    Subgroup.centralizer ({z * s} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨S', R', T', W', hstd⟩ :=
    c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hs.hz M hM s hs'
  have hμ' := muIsoWylD4_transfer hs.stand.modU hs.hW.1 hstd.hW.1 hμ
  have hnc' : ¬ DbarConnected Ω W' := T8X.not_dbarConnected_of_ne hstd hne
  obtain ⟨F⟩ := exists_frameData hstd hμ' hnc'
  obtain ⟨R₃, hF, hind⟩ := F.exists_triFrame hstd
  have hHyp : Hyp51 (Subgroup.closure ({z, s, F.zz 2} : Set G)) :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.hyp51Tri_proved G Ω ![K, M, (F.ρ 2).K] ![z, s, F.zz 2]
        R₃ hstd.stand hnt hF
      (by simpa using hind)
  have hc01 : z * s = s * z := hF.comm hΩ 0 1
  have hc02 : z * F.zz 2 = F.zz 2 * z := hF.comm hΩ 0 2
  have hc12 : s * F.zz 2 = F.zz 2 * s := hF.comm hΩ 1 2
  have hz2 : z * z = 1 := hF.sq 0
  have hs2 : s * s = 1 := hF.sq 1
  have hz''2 : F.zz 2 * F.zz 2 = 1 := hF.sq 2
  have hz1 : z ≠ 1 := hF.ne_one 0
  have hs1 : s ≠ 1 := hF.ne_one 1
  have hz''1 : F.zz 2 ≠ 1 := hF.ne_one 2
  have hzs : z ≠ s := hF.x_ne hnt (i := 0) (j := 1) (by decide)
  have hB : IsElemAbelian 2 (Subgroup.closure ({z, s, F.zz 2} : Set G)) :=
    T8T.isElemAbelian_closure_three hz2 hs2 hz''2 hc01 hc02 hc12
  have hB8 : Nat.card ↥(Subgroup.closure ({z, s, F.zz 2} : Set G)) = 8 :=
    T8T.natCard_closure_three hz2 hs2 hz''2 hc01 hc02 hc12 hz1 hs1 hzs hz''1 (by simpa using hind)
  have hDB : Subgroup.closure ({s, z} : Set G) ≤ Subgroup.closure ({z, s, F.zz 2} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({s, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hs2 hz2 hs1 hz1 hzs.symm hc01.symm
  have h3 : ∀ A : Subgroup G, A ≤ Subgroup.closure ({z, s, F.zz 2} : Set G) →
      IsElemAbelian2 A 2 → alphaOf A = alphaOf (Subgroup.closure ({s, z} : Set G)) :=
    (lemma54_odd_and_eq hHyp hDB hD).2
  have hα : alphaOf (Subgroup.closure ({s, z} : Set G)) =
      alphaOf (Subgroup.closure ({t, z} : Set G)) :=
    (T8U.alphaOf_eq_of_omegaNbr_frame hs.stand hs.noTwins hframe hs.hz hs' hs.ht hM hs.hJ).symm
  intro c hc
  have hx : z * s * (z * s) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hM hs'
  have hKx : T8.XMem Ω (z * s) K := Layer.xMem_zt3 hstd
  have hcz : c ∈ T8.cenZ (z * s) := by
    rw [T8.cenZ_eq_centralizer]
    exact hc
  have hKc : T8.XMem Ω (z * s) (conjSub c K) := hKx.conj3 hΩ.conjInvariant hcz
  have hKt : K ∈ Q3NL.tqMembers3 Ω (z * s) := hKx.mem_tqMembers3 hΩ hx
  have hL : Layer.LayerHyp Ω (z * s) := Layer.LayerHyp.of_stand3 hs.stand.toStand3 hx ⟨K, hKt⟩
  obtain ⟨ν, hν, hνK⟩ :=
    Layer.exists_oddCore_conj_mem_dComp3 hL hKt hconn (hKc.mem_tqMembers3 hΩ hx)
  have hνc : ν * c ∈ sigmaNorm Ω K := by
    rw [T8.mem_sigmaNorm_iff hΩ.conjInvariant hK, conjSub_mul]
    exact hνK
  have hzsB : z * s ∈ Subgroup.closure ({z, s, F.zz 2} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hν' : ν ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({s, z} : Set G)) : Set G) :=
    T8T.oddCoreOf_centralizer_le_normalizer hB hB8 hzsB h3
      (T8T.oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ (z * s) hν)
  rw [hα] at hν'
  have hc' : c = ν⁻¹ * (ν * c) := by group
  rw [hc']
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hν') (hN hνc)
end T8YY
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.AscP1Nine3
    CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Balance.Theorem5
namespace T8YY
open CFSG.ClassicalInvolution.Asc77.T8YY
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem alphaOf_odd [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) :
    Odd (Nat.card ↥(alphaOf (Subgroup.closure ({t, z} : Set G)))) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  obtain ⟨F⟩ := exists_frameData hs hμ hnc
  obtain ⟨R₃, hF, hind⟩ := F.exists_triFrame hs
  have hHyp : Hyp51 (Subgroup.closure ({z, t, F.zz 2} : Set G)) :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.hyp51Tri_proved G Ω ![K, J, (F.ρ 2).K] ![z, t, F.zz 2]
        R₃ hs.stand hnt hF
      (by simpa using hind)
  have hc01 : z * t = t * z := hF.comm hΩ 0 1
  exact CFSG.ClassicalInvolution.Asc77.T8YY.alphaOf_oddE F hnt hF hHyp hc01

theorem layerJoin_le_sigmaNorm_of_lift {x : G} (L : Layer.LayerHyp Ω x)
    {K₀ : Subgroup G} (hK : K₀ ∈ Q3NL.tqMembers3 Ω x)
    (hO : oddCoreOf (Q3NL.exactLayer3 Ω x) ≤ sigmaNorm Ω K₀)
    (hconn : DConnected (Q3T7.layerFam3 Ω x)) : Q3NL.exactLayer3 Ω x ≤ sigmaNorm Ω K₀ := by
  rw [Q3T7.exactLayer3_eq_iSup]
  refine iSup₂_le fun L₁ hL₁ => ?_
  obtain ⟨K', hK', rfl⟩ := hL₁
  obtain ⟨ν, hν, hνK⟩ := Layer.exists_oddCore_conj_mem_dComp3 L hK hconn hK'
  have hle : conjSub ν K' ≤ sigmaNorm Ω K₀ :=
    Subgroup.le_normalizer.trans
      (T8.normalizer_le_sigmaNorm_of_mem L.gen.conjInvariant hK.1 hνK)
  have hνN : ν ∈ sigmaNorm Ω K₀ := hO hν
  intro y hy
  have hyK : y ∈ K' := Q3NL.exactCore3_le_left x K' hy
  have h1 : ν * y * ν⁻¹ ∈ sigmaNorm Ω K₀ :=
    hle (mem_conjSub_iff.mpr (by simpa [mul_assoc] using hyK))
  have h2 := (sigmaNorm Ω K₀).mul_mem ((sigmaNorm Ω K₀).mul_mem ((sigmaNorm Ω K₀).inv_mem hνN) h1)
    hνN
  simpa [mul_assoc] using h2

variable [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AlphaFrame3] in
theorem false_of_caseA_uniform [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (hconn : DConnected (Q3T7.layerFam3 Ω (z * t)))
    (huni : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      DConnected (Q3T7.layerFam3 Ω (z * s))) : False := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  have hframe := exists_fuzzyFrame hs hμ hnc
  have hN := sigmaNorm_le_normalizer_alpha hs hframe
  have hH : T8.H274 Ω K z ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) :=
    sup_le hN (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' =>
      centralizer_le_normalizer_alpha_of_nbr hs hμ hne hdisc hframe hN hM hs' (huni M hM s hs'))
  have htop : T8.H274 Ω K z = ⊤ := h274_eq_top hs hdisc hμ hne
  rw [htop, top_le_iff] at hH
  have hnorm : (alphaOf (Subgroup.closure ({t, z} : Set G))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp hH
  have hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ := by
    rcases hnorm.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hodd := alphaOf_odd hs hμ hne
      have hz := hs.hz
      have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
      have hdvd : 2 ∣ Nat.card G := hord ▸ orderOf_dvd_natCard z
      rw [h, Subgroup.card_top] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hY : oddCoreOf (Q3NL.exactLayer3 Ω (z * t)) ≤ sigmaNorm Ω K :=
    T8.oddCoreOf_layerJoin_le_of_alpha hs hα
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hKx : T8.XMem Ω (z * t) K := Layer.xMem_zt3 hs
  have hY1 : Q3NL.exactLayer3 Ω (z * t) ≤ sigmaNorm Ω K :=
    layerJoin_le_sigmaNorm_of_lift (Layer.LayerHyp.of_stand3 hs.stand.toStand3 hx ⟨K,
        hKx.mem_tqMembers3 hΩ hx⟩) (hKx.mem_tqMembers3 hΩ hx) hY hconn
  have hC : Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K :=
    Layer.centralizer_le_sigmaNorm_of_exactLayer3_le hs hY1
  obtain ⟨F⟩ := exists_frameData hs hμ hnc
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hM := F.mgrp_le_centralizer c 0 1
  rw [F.hz0, F.hz1] at hM
  exact mgrp_not_le_sigmaNorm hs hne (hM.trans hC)
end T8YY
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.AscP1Nine3
    CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Balance.Theorem5
namespace T8YY
open CFSG.ClassicalInvolution.Asc77.T8YY
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
namespace FrameData
open CFSG.ClassicalInvolution.Asc77.T8YY.FrameData
end FrameData

theorem centralizer_le_normalizer_alpha_of_frattini [IsSimpleGroup G]
    (hs : Std8 Ω K J S R T W z t) (F : FrameData Ω W K J z t)
    (hfr : ∀ c ∈ Subgroup.centralizer ({z * t} : Set G),
      ∃ o ∈ oddCoreOf (Q3NL.exactLayer3 Ω (z * t)), conjSub (o * c) F.vGroup = F.vGroup) :
    Subgroup.centralizer ({z * t} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨R₃, hF, hind⟩ := F.exists_triFrame hs
  have hHyp : Hyp51 (Subgroup.closure ({z, t, F.zz 2} : Set G)) :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.hyp51Tri_proved G Ω ![K, J, (F.ρ 2).K] ![z, t, F.zz 2]
        R₃ hs.stand hnt hF
      (by simpa using hind)
  have hc01 : z * t = t * z := hF.comm hΩ 0 1
  have hc02 : z * F.zz 2 = F.zz 2 * z := hF.comm hΩ 0 2
  have hc12 : t * F.zz 2 = F.zz 2 * t := hF.comm hΩ 1 2
  exact CFSG.ClassicalInvolution.Asc77.T8YY.centralizer_le_normalizer_alpha_of_frattiniE F hnt hF hind
    hHyp hc01 hc02 hc12 F.vGroup rfl
    (T8T.oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ (z * t)) hfr
end T8YY
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.AscP1Nine3
    CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Balance.Theorem5
namespace T8YY
open CFSG.ClassicalInvolution.Asc77.T8YY

@[expose] def LayerFrattiniFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoWylD4 Ω W → dComp Ω K ≠ dstarComp Ω K →
        ¬ DConnected (Q3T7.layerFam3 Ω (z * t)) → ∀ F : FrameData Ω W K J z t,
          ∀ c ∈ Subgroup.centralizer ({z * t} : Set G),
            ∃ o ∈ oddCoreOf (Q3NL.exactLayer3 Ω (z * t)), conjSub (o * c) F.vGroup = F.vGroup

@[expose] def PureBCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoWylD4 Ω W → dComp Ω K ≠ dstarComp Ω K →
        (∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
          ¬ DConnected (Q3T7.layerFam3 Ω (z * s))) →
        alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ →
          False
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

variable [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AlphaFrame3] in
theorem centralizer_le_normalizer_alpha_of_edge [IsSimpleGroup G] (hV : LayerFrattiniFact)
    (hs : Std8 Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (hdisc : ¬ DConnected Ω) (hframe : ∃ A₀, Q3NL.FuzzyFrame3 Ω A₀)
    (hN : sigmaNorm Ω K ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G))
    {M : Subgroup G} (hM : M ∈ omegaNbr Ω K) {s : G} (hs' : IsUniqueInvolution M s) :
    Subgroup.centralizer ({z * s} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  by_cases hconn : DConnected (Q3T7.layerFam3 Ω (z * s))
  · exact centralizer_le_normalizer_alpha_of_nbr hs hμ hne hdisc hframe hN hM hs' hconn
  · have hΩ : HypOmegaMod Ω := hs.stand.hyp
    obtain ⟨S', R', T', W', hstd⟩ :=
      c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hs.hz M hM s hs'
    have hμ' := muIsoWylD4_transfer hs.stand.modU hs.hW.1 hstd.hW.1 hμ
    have hnc' : ¬ DbarConnected Ω W' := T8X.not_dbarConnected_of_ne hstd hne
    obtain ⟨F'⟩ := exists_frameData hstd hμ' hnc'
    have hfr := hV G Ω K M S' R' T' W' z s hstd hdisc hμ' hne hconn F'
    have hα : alphaOf (Subgroup.closure ({s, z} : Set G)) =
        alphaOf (Subgroup.closure ({t, z} : Set G)) :=
      (T8U.alphaOf_eq_of_omegaNbr_frame hs.stand hs.noTwins hframe hs.hz hs' hs.ht hM hs.hJ).symm
    rw [← hα]
    exact centralizer_le_normalizer_alpha_of_frattini hstd F' hfr

variable [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AlphaFrame3] in
theorem alphaOf_eq_bot_of_frattini [IsSimpleGroup G] (hV : LayerFrattiniFact)
    (hs : Std8 Ω K J S R T W z t) (hdisc : ¬ DConnected Ω) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) :
    alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ := by
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  have hframe := exists_fuzzyFrame hs hμ hnc
  have hN := sigmaNorm_le_normalizer_alpha hs hframe
  exact CFSG.ClassicalInvolution.Asc77.T8YY.alphaOf_eq_bot_of_frattiniE hs.hz hN
    (fun hM => fun hs' => centralizer_le_normalizer_alpha_of_edge hV hs hμ hne hdisc hframe hN hM hs')
    (h274_eq_top hs hdisc hμ hne) (alphaOf_odd hs hμ hne)

theorem false_of_caseA_of_alpha_bot [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (hconn : DConnected (Q3T7.layerFam3 Ω (z * t)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) : False := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  have hY : oddCoreOf (Q3NL.exactLayer3 Ω (z * t)) ≤ sigmaNorm Ω K :=
    T8.oddCoreOf_layerJoin_le_of_alpha hs hα
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hKx : T8.XMem Ω (z * t) K := Layer.xMem_zt3 hs
  have hY1 : Q3NL.exactLayer3 Ω (z * t) ≤ sigmaNorm Ω K :=
    layerJoin_le_sigmaNorm_of_lift (Layer.LayerHyp.of_stand3 hs.stand.toStand3 hx ⟨K,
        hKx.mem_tqMembers3 hΩ hx⟩) (hKx.mem_tqMembers3 hΩ hx) hY hconn
  have hC : Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K :=
    Layer.centralizer_le_sigmaNorm_of_exactLayer3_le hs hY1
  obtain ⟨F⟩ := exists_frameData hs hμ hnc
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hM := F.mgrp_le_centralizer c 0 1
  rw [F.hz0, F.hz1] at hM
  exact mgrp_not_le_sigmaNorm hs hne (hM.trans hC)

variable [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AlphaFrame3] in
theorem w2caseB_of_facts (hV : LayerFrattiniFact) (hP : PureBCase) : T8X.W2CaseB3 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ hne _
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  have hframe := exists_fuzzyFrame hs hμ hnc
  have hα := alphaOf_eq_bot_of_frattini hV hs hdisc hμ hne
  by_cases huni : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      ¬ DConnected (Q3T7.layerFam3 Ω (z * s))
  · exact hP G Ω K J S R T W z t hs hdisc hμ hne huni hα
  · exfalso
    push Not at huni
    obtain ⟨M, hM, s, hs', hconnM⟩ := huni
    obtain ⟨S', R', T', W', hstd⟩ :=
      c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hs.hz M hM s hs'
    have hμ' := muIsoWylD4_transfer hs.stand.modU hs.hW.1 hstd.hW.1 hμ
    have hα' : alphaOf (Subgroup.closure ({s, z} : Set G)) = ⊥ := by
      rw [(T8U.alphaOf_eq_of_omegaNbr_frame hs.stand hs.noTwins hframe hs.hz hs' hs.ht hM
        hs.hJ).symm]
      exact hα
    exact false_of_caseA_of_alpha_bot hstd hμ' hne hconnM hα'
end T8YY
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.AscP1Nine3
    CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Balance.Theorem5
namespace T8YY
open CFSG.ClassicalInvolution.Asc77.T8YY
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
namespace FrameData
open CFSG.ClassicalInvolution.Asc77.T8YY.FrameData

theorem zz_comm (c : Q3CL.Thompson.Ctx Ω W) (F : FrameData Ω W K J z t) (i j : Fin 4) :
    F.zz i * F.zz j = F.zz j * F.zz i :=
  c.comm_W _ (F.hW i) _ (F.hW j)

theorem zz0_mul_mem_vGroup (c : Q3CL.Thompson.Ctx Ω W) (F : FrameData Ω W K J z t) (j : Fin 4) :
    F.zz 0 * F.zz j ∈ F.vGroup := by
  exact CFSG.ClassicalInvolution.Asc77.T8YY.FrameData.zz0_mul_mem_vGroupE_of c.comm_W F j

theorem mul_mem_vGroup (c : Q3CL.Thompson.Ctx Ω W) (F : FrameData Ω W K J z t) (i j : Fin 4) :
    F.zz i * F.zz j ∈ F.vGroup := by
  exact CFSG.ClassicalInvolution.Asc77.T8YY.FrameData.mul_mem_vGroupE_of c.comm_W F i j

theorem vGroup_eq_of_members {W' K' J' : Subgroup G} {z' t' : G} (c : Q3CL.Thompson.Ctx Ω W)
    (c' : Q3CL.Thompson.Ctx Ω W') (F : FrameData Ω W K J z t) (F' : FrameData Ω W' K' J' z' t')
    (hmem : ∀ j, ∃ i, (F'.ρ j).K = (F.ρ i).K) : F'.vGroup = F.vGroup := by
  exact CFSG.ClassicalInvolution.Asc77.T8YY.FrameData.vGroupE_eq_of_members_of c.comm_W c'.comm_W F F'
    hmem
end FrameData

theorem alphaOf_vGroup_eq [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (F : FrameData Ω W K J z t) :
    IsElemAbelian2 F.vGroup 2 ∧
      alphaOf F.vGroup = alphaOf (Subgroup.closure ({t, z} : Set G)) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨R₃, hF, hind⟩ := F.exists_triFrame hs
  have hHyp : Hyp51 (Subgroup.closure ({z, t, F.zz 2} : Set G)) :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.hyp51Tri_proved G Ω ![K, J, (F.ρ 2).K] ![z, t, F.zz 2]
        R₃ hs.stand hnt hF
      (by simpa using hind)
  have hc01 : z * t = t * z := hF.comm hΩ 0 1
  have hc02 : z * F.zz 2 = F.zz 2 * z := hF.comm hΩ 0 2
  have hc12 : t * F.zz 2 = F.zz 2 * t := hF.comm hΩ 1 2
  exact CFSG.ClassicalInvolution.Asc77.T8YY.alphaOf_vGroup_eqE F hnt hF hHyp hc01 hc02 hc12
    F.vGroup rfl

theorem false_of_singleFrame [IsSimpleGroup G] (hV : LayerFrattiniFact)
    (hs : Std8 Ω K J S R T W z t) (hdisc : ¬ DConnected Ω) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (huni : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      ¬ DConnected (Q3T7.layerFam3 Ω (z * s)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) (F : FrameData Ω W K J z t)
    (hsingle : ∀ i : Fin 4, ∀ M ∈ omegaNbr Ω (F.ρ i).K, ∃ j, M = (F.ρ j).K) : False := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  obtain ⟨hVab, hαV'⟩ := alphaOf_vGroup_eq hs F
  have hαV : alphaOf F.vGroup = ⊥ := hαV'.trans hα
  
  have hSig : ∀ L ∈ dComp Ω K, ∃ i, L = (F.ρ i).K := by
    intro L hL
    induction hL with
    | refl => exact ⟨0, F.h0.symm⟩
    | @tail b c hbk hbc ih =>
      obtain ⟨i, rfl⟩ := ih
      obtain ⟨hcΩ, hadj⟩ := hbc
      rcases hadj with h | h
      · exact hsingle i c h
      · exact hsingle i c (Q3CL.T3.omegaNbr_symm (l6_2) hΩ hcΩ (F.ρ i).hK h)
  have hFm : ∀ i, (F.ρ i).K ∈ dComp Ω K := by
    intro i
    by_cases h0 : i = 0
    · rw [h0, F.h0]
      exact Relation.ReflTransGen.refl
    · have := F.hadj 0 i (Ne.symm h0)
      rw [F.h0] at this
      exact T8.mem_dComp_of_mem_omegaNbr this
  
  have hNle : ∀ n ∈ sigmaNorm Ω K, conjSub n F.vGroup ≤ F.vGroup := by
    intro n hn
    have hKn : conjSub n K ∈ dComp Ω K := (T8.mem_sigmaNorm_iff hΩ.conjInvariant hK).mp hn
    have hdeq : dComp Ω (conjSub n K) = dComp Ω K := T8.dComp_eq_of_mem hK hKn
    have hperm : ∀ i, ∃ j, conjSub n (F.ρ i).K = (F.ρ j).K := by
      intro i
      have h1 := mem_dComp_conjSub hΩ.conjInvariant (hFm i) n
      rw [hdeq] at h1
      exact hSig _ h1
    choose π hπ using hperm
    have hzπ : ∀ i, n * F.zz i * n⁻¹ = F.zz (π i) := fun i =>
      ((F.hz i).conj n).eq (by rw [hπ i]; exact F.hz (π i))
    unfold FrameData.vGroup
    rw [conjSub_closure_pair, Subgroup.closure_le]
    intro y hy
    have hconj : ∀ i j, n * (F.zz i * F.zz j) * n⁻¹ = F.zz (π i) * F.zz (π j) := by
      intro i j
      rw [← hzπ i, ← hzπ j]
      group
    rcases hy with rfl | rfl
    · rw [hconj 0 1]
      exact F.mul_mem_vGroup c _ _
    · rw [hconj 0 2]
      exact F.mul_mem_vGroup c _ _
  have hN : sigmaNorm Ω K ≤ Subgroup.normalizer (F.vGroup : Set G) := fun n hn =>
    Asc77.T8YY.mem_normalizer_of_conjSub_le (hNle n hn) (hNle n⁻¹ ((sigmaNorm Ω K).inv_mem hn))
  
  have hC : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      Subgroup.centralizer ({z * s} : Set G) ≤ Subgroup.normalizer (F.vGroup : Set G) := by
    intro M hM s hs'
    have hnconn := huni M hM s hs'
    obtain ⟨S', R', T', W', hstd⟩ :=
      c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hs.hz M hM s hs'
    have hμ' := muIsoWylD4_transfer hs.stand.modU hs.hW.1 hstd.hW.1 hμ
    have hnc' : ¬ DbarConnected Ω W' := T8X.not_dbarConnected_of_ne hstd hne
    obtain ⟨F'⟩ := exists_frameData hstd hμ' hnc'
    have c' := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hstd) hstd.hW.1
    have hmemF' : ∀ j, ∃ i, (F'.ρ j).K = (F.ρ i).K := by
      intro j
      by_cases h0 : j = 0
      · exact ⟨0, by rw [h0, F'.h0, F.h0]⟩
      by_cases h1 : j = 1
      · obtain ⟨i, hi⟩ := hsingle 0 M (by rw [F.h0]; exact hM)
        exact ⟨i, by rw [h1, F'.h1, hi]⟩
      · have h' := F'.hadj 0 j (Ne.symm h0)
        rw [F'.h0] at h'
        obtain ⟨i, hi⟩ := hsingle 0 _ (by rw [F.h0]; exact h')
        exact ⟨i, hi⟩
    have hVeq : F'.vGroup = F.vGroup := FrameData.vGroup_eq_of_members c c' F F' hmemF'
    have hfr := hV G Ω K M S' R' T' W' z s hstd hdisc hμ' hne hnconn F'
    have hzsV : z * s ∈ F.vGroup := by
      rw [← hVeq]
      have h01 : F'.zz 0 * F'.zz 1 ∈ F'.vGroup := Subgroup.subset_closure (Set.mem_insert _ _)
      rwa [F'.hz0, F'.hz1] at h01
    have hzs1 : z * s ≠ 1 := by
      have := F'.mul_ne_one 0 1 (by decide)
      rwa [F'.hz0, F'.hz1] at this
    intro x hx
    obtain ⟨o, ho, hconj⟩ := hfr x hx
    have hocomm : ∀ y ∈ F.vGroup, o * y = y * o := fun y hy =>
      T8.oddCoreOf_centralizer_commutes hαV hzsV hzs1 hy o
        (T8T.oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ (z * s) ho)
    have hoN : o ∈ Subgroup.normalizer (F.vGroup : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have e : ∀ y ∈ F.vGroup, o * y * o⁻¹ = y := fun y hy => by
        rw [hocomm y hy]
        group
      constructor
      · intro hy
        rw [e y hy]
        exact hy
      · intro hy'
        have hc := hocomm _ hy'
        have e2 : o * y * o⁻¹ = y := by
          calc o * y * o⁻¹ = o⁻¹ * (o * (o * y * o⁻¹)) := by group
            _ = o⁻¹ * ((o * y * o⁻¹) * o) := by rw [hc]
            _ = y := by group
        rw [e2] at hy'
        exact hy'
    have hoxN : o * x ∈ Subgroup.normalizer (F.vGroup : Set G) := by
      rw [← hVeq, mem_normalizer_iff_conjSub_eq]
      exact hconj
    have hx' : x = o⁻¹ * (o * x) := by group
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hoN) hoxN
  have hH : T8.H274 Ω K z ≤ Subgroup.normalizer (F.vGroup : Set G) :=
    sup_le hN (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' => hC M hM s hs')
  have htop : T8.H274 Ω K z = ⊤ := h274_eq_top hs hdisc hμ hne
  rw [htop, top_le_iff] at hH
  have hnorm : F.vGroup.Normal := Subgroup.normalizer_eq_top_iff.mp hH
  rcases hnorm.eq_bot_or_eq_top with h | h
  · have h01 : F.zz 0 * F.zz 1 ∈ F.vGroup := Subgroup.subset_closure (Set.mem_insert _ _)
    rw [h, Subgroup.mem_bot] at h01
    exact F.mul_ne_one 0 1 (by decide) h01
  · have hall : ∀ x : G, x * x = 1 := fun x => hVab.2 x (h ▸ Subgroup.mem_top x)
    have hcomm : ∀ a b : G, a * b = b * a := fun a b => by
      calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (hall (a * b))).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by
          rw [inv_eq_of_mul_eq_one_right (hall a), inv_eq_of_mul_eq_one_right (hall b)]
    obtain ⟨z', hz'cl⟩ := hs.stand.modU.classical K hs.stand.mem
    obtain ⟨x, -, y, -, hxy⟩ := hz'cl.exists_noncomm
    exact hxy (hcomm x y)

end T8YY
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
