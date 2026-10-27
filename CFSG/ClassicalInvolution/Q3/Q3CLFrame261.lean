module

public import CFSG.ClassicalInvolution.Q3.Q3CLFrame
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven
public import CFSG.ClassicalInvolution.Q3.Q3T8Defs

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem Std8Frame.symm' (hs : Std8Frame Ω K J S R T W z t) : Std8Frame Ω J K S T R W t z := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  refine ⟨hΩ, hs.hJ.1, ?_, ?_, hs.ht, ?_, hs.hz, hs.hT, hs.hR, hs.hW⟩
  · intro L hL
    obtain ⟨g, hg⟩ := hs.trans L hL
    obtain ⟨g₀, hg₀⟩ := hs.trans J hs.hJ.1
    refine ⟨g * g₀⁻¹, ?_⟩
    rw [← hg₀, ← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one, hg]
  · exact fun K' hK' => T8.noTwins_of_mem hΩ.conjInvariant hs.trans hs.noTwins hs.hJ.1 K' hK'
  · exact T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hs.mem hs.hJ.1 hs.hJ

theorem Std8Frame.conj (hs : Std8Frame Ω K J S R T W z t) (n : G) :
    Std8Frame Ω (conjSub n K) (conjSub n J) (conjSylow n S) (conjSub n R) (conjSub n T)
      (conjSub n W) (n * z * n⁻¹) (n * t * n⁻¹) := by
  have hcl := hs.hyp.conjInvariant
  have hmem : conjSub n K ∈ Ω := hcl n K hs.mem
  refine ⟨hs.hyp, hmem, ?_, ?_, hs.hz.conj n, omegaNbr_conj hcl hs.hJ n, hs.ht.conj n, ?_, ?_, ?_⟩
  · intro L hL
    obtain ⟨g, hg⟩ := hs.trans L hL
    refine ⟨g * n⁻¹, ?_⟩
    rw [← conjSub_mul, inv_mul_cancel_right, hg]
  · exact fun K' hK' => T8.noTwins_of_mem hcl hs.trans hs.noTwins hmem K' hK'
  · obtain ⟨hR, hRK, hRS⟩ := hs.hR
    refine ⟨RSet.conj hcl hR n, conjSub_mono hRK, ?_⟩
    rw [coe_conjSylow]
    exact conjSub_mono hRS
  · obtain ⟨hT, hTJ, hTS⟩ := hs.hT
    refine ⟨RSet.conj hcl hT n, conjSub_mono hTJ, ?_⟩
    rw [coe_conjSylow]
    exact conjSub_mono hTS
  · obtain ⟨hW, hWS, hWn⟩ := hs.hW
    refine ⟨WSet.conj hcl hW n, ?_, ?_⟩
    · rw [coe_conjSylow]
      exact conjSub_mono hWS
    · intro s hs'
      rw [coe_conjSylow, mem_conjSub_iff] at hs'
      have := hWn _ hs'
      calc conjSub s (conjSub n W) = conjSub n (conjSub (n⁻¹ * s * n) W) := by
            rw [← conjSub_mul, ← conjSub_mul]
            congr 1
            group
        _ = conjSub n W := by rw [this]

end CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc

namespace CFSG.ClassicalInvolution.Q3.Q3CL.Frame

open CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8
  CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc CFSG.ClassicalInvolution.Disconnected.AschTight

section

open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups
section Basic
variable {G : Type} [Group G]
end Basic
section Setup
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
end Setup
section Normalizer
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem s26_conjSub_mem_omegaNbr [Finite G] (hΩ : HypOmegaGen Ω) {K J' : Subgroup G} {b : G}
    (hb : conjSub b K = K) (hJ' : J' ∈ omegaNbr Ω K) : conjSub b J' ∈ omegaNbr Ω K := by
  obtain ⟨hJΩ, hJK, R', hR', hR'J, hR'N⟩ := hJ'
  have hbN : b ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_conjSub_eq.mpr hb
  refine ⟨hΩ.conjInvariant b J' hJΩ, ?_, conjSub b R', Q3CL.Thompson.conjSub_mem_RSet hΩ hR' b,
    conjSub_mono hR'J, ?_⟩
  · intro h
    apply hJK
    have h2 : conjSub b⁻¹ (conjSub b J') = conjSub b⁻¹ K := by rw [h]
    rw [conjSub_inv_conjSub] at h2
    calc J' = conjSub b⁻¹ K := h2
      _ = conjSub b⁻¹ (conjSub b K) := by rw [hb]
      _ = K := conjSub_inv_conjSub b K
  · intro x hx
    rw [mem_conjSub_iff] at hx
    have hy := hR'N hx
    have e : x = b * (b⁻¹ * x * b) * b⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hbN hy) (Subgroup.inv_mem _ hbN)

theorem s26_conjSub_omegaNbrGen_le [Finite G] (hΩ : HypOmegaGen Ω) {K : Subgroup G} {b : G}
    (hb : conjSub b K = K) : conjSub b (omegaNbrGen Ω K) ≤ omegaNbrGen Ω K := by
  show (omegaNbrGen Ω K).map (MulAut.conj b).toMonoidHom ≤ omegaNbrGen Ω K
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun M' hM' => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) (conjSub b M')
    (s26_conjSub_mem_omegaNbr hΩ hb hM')

theorem s26_conjSub_omegaNbrGen [Finite G] (hΩ : HypOmegaGen Ω) {K : Subgroup G} {b : G}
    (hb : conjSub b K = K) : conjSub b (omegaNbrGen Ω K) = omegaNbrGen Ω K := by
  have h1 := s26_conjSub_omegaNbrGen_le hΩ hb
  have hb' : conjSub b⁻¹ K = K := by
    calc conjSub b⁻¹ K = conjSub b⁻¹ (conjSub b K) := by rw [hb]
      _ = K := conjSub_inv_conjSub b K
  have h2 := s26_conjSub_omegaNbrGen_le (Ω := Ω) hΩ hb'
  refine le_antisymm h1 ?_
  have := conjSub_mono (n := b) h2
  rwa [conjSub_conjSub_inv] at this
end Normalizer
section Dichotomy
end Dichotomy
section Main
end Main

end

section

open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Rep
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
end Rep
section Std
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem mem_DSet_of_le_sylow (hs : Std8Frame Ω K J S R T W z t) {X : Subgroup G}
    (hX : X ∈ RSet Ω) (hXS : X ≤ (S : Subgroup G)) : X ∈ DSet Ω W :=
  ⟨hX, fun x hx => mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 x (hXS hx))⟩


end Std
section Klein
variable {Q : Type} [Group Q]
end Klein
section Dichotomy
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
end Dichotomy
section LayerTri
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
end LayerTri
end T8

end

section

set_option linter.unusedSectionVars false
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem eq_of_isSylow2In_of_le_sylow {S : Sylow 2 G} {M P Q : Subgroup G} (hP : IsSylow2In P M)
    (hQ : IsSylow2In Q M) (hPS : P ≤ (S : Subgroup G)) (hQS : Q ≤ (S : Subgroup G)) : P = Q := by
  have h1 : M ⊓ (S : Subgroup G) = P :=
    hP.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hP.1 hPS)
  have h2 : M ⊓ (S : Subgroup G) = Q :=
    hQ.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hQ.1 hQS)
  exact h1.symm.trans h2

variable {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem R_ne_T (hs : Std8Frame Ω K J S R T W z t) : R ≠ T := by
  intro h
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRsyl : IsSylow2In R K :=
    Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.mem hRΩ hRK
  have h8 := hΩ.eight_le_of_mem_RSet hRΩ
  exact hs.hJ.2.1 (hΩ.eq_of_le_of_le hs.hJ.1 hs.mem hRsyl.2.1 (by omega)
    (h ▸ hTJ) hRK)

theorem eq_or_eq_of_mem_RSet_of_le (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {P : Subgroup G} (hP : P ∈ RSet Ω)
    (hPS : P ≤ (S : Subgroup G)) : P = R ∨ P = T := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  by_contra hcon
  push Not at hcon
  obtain ⟨M, hM, hPM⟩ := exists_isSylow2In_of_mem_RSet hP
  have hMK : M ≠ K := by
    rintro rfl
    exact hcon.1 (eq_of_isSylow2In_of_le_sylow hPM hRsyl hPS hRS)
  have hcomm : Commutes P R :=
    l6_7_proved G Ω hΩ S P hP R hRΩ hPS hRS hcon.1
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hRΩ; omega)
  have hPc : P ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx z hzR)
  have hP8 := hΩ.eight_le_of_mem_RSet hP
  have hPN : P ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hK hM (Ne.symm hMK) hs.hz hPM.1 hPM.2.1
      (by omega) hPc
  have hMnbr : M ∈ omegaNbr Ω K := ⟨hM, hMK, P, hP, hPM.1, hPN⟩
  have hMX : M ≤ omegaNbrGen Ω K :=
    le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) M hMnbr
  have hJX : J ≤ omegaNbrGen Ω K :=
    le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have hTX : IsSylow2In T (omegaNbrGen Ω K) := isSylow2In_of_eq_sup_oddCoreOf hJX hX hTsyl
  
  have hQ2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ omegaNbrGen Ω K) := S.isPGroup'.to_inf_left
  have hQle : Nat.card ↥((S : Subgroup G) ⊓ omegaNbrGen Ω K) ≤ Nat.card T :=
    natCard_le_of_eq_sup_oddCoreOf hJX hX hTsyl inf_le_right hQ2
  have hTQ : T ≤ (S : Subgroup G) ⊓ omegaNbrGen Ω K := le_inf hTS (hTsyl.1.trans hJX)
  have hPQ : P ≤ (S : Subgroup G) ⊓ omegaNbrGen Ω K := le_inf hPS (hPM.1.trans hMX)
  have hQT : (S : Subgroup G) ⊓ omegaNbrGen Ω K = T :=
    (Subgroup.eq_of_le_of_card_ge hTQ hQle).symm
  have hcardP : Nat.card P = Nat.card T := by
    exact Disconnected.AschTight.Sec6Gen.natCard_isSylow2In_eq hΩ hM hJΩ hPM hTsyl
  have hPleT : P ≤ T := hQT ▸ hPQ
  have hPT : P = T := Subgroup.eq_of_le_of_card_ge hPleT (le_of_eq hcardP.symm)
  exact hcon.2 hPT

theorem fix_or_swap (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {s : G}
    (hsS : s ∈ (S : Subgroup G)) :
    (conjSub s R = R ∧ conjSub s T = T) ∨ (conjSub s R = T ∧ conjSub s T = R) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRT := R_ne_T hs
  have hcl := hΩ.conjInvariant
  have hsS' : ∀ P ≤ (S : Subgroup G), conjSub s P ≤ (S : Subgroup G) := by
    intro P hP
    have := conjSub_mono (n := s) hP
    rwa [conjSub_eq_self_of_mem hsS] at this
  have hR' := eq_or_eq_of_mem_RSet_of_le hs hX (RSet.conj hcl hRΩ s) (hsS' R hRS)
  have hT' := eq_or_eq_of_mem_RSet_of_le hs hX (RSet.conj hcl hTΩ s) (hsS' T hTS)
  rcases hR' with hR' | hR'
  · left
    refine ⟨hR', ?_⟩
    rcases hT' with hT' | hT'
    · exact absurd ((conjSub_inj s).mp (hT'.trans hR'.symm)).symm hRT
    · exact hT'
  · right
    refine ⟨hR', ?_⟩
    rcases hT' with hT' | hT'
    · exact hT'
    · exact absurd ((conjSub_inj s).mp (hT'.trans hR'.symm)) (Ne.symm hRT)

theorem conj_zt_of_mem_sylow (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {s : G}
    (hsS : s ∈ (S : Subgroup G)) : s * (z * t) * s⁻¹ = z * t := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hcl := hΩ.conjInvariant
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have h8R := hΩ.eight_le_of_mem_RSet hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hTΩ
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  rcases fix_or_swap hs hX hsS with ⟨hR', hT'⟩ | ⟨hR', hT'⟩
  · have hK' : conjSub s K = K := Q3CL.T8.conjSub_eq_of_conjSub_eq hΩ hK hRΩ hRK hR'
    have hJ' : conjSub s J = J := Q3CL.T8.conjSub_eq_of_conjSub_eq hΩ hJΩ hTΩ hTJ hT'
    have h1 := hs.hz.conj_eq hK'
    have h2 := hs.ht.conj_eq hJ'
    calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
      _ = z * t := by rw [h1, h2]
  · have hK' : conjSub s K = J := hΩ.eq_of_le_of_le (hcl s K hK) hJΩ hTsyl.2.1 (by omega)
      (hR' ▸ conjSub_mono (n := s) hRK) hTJ
    have hJ' : conjSub s J = K := hΩ.eq_of_le_of_le (hcl s J hJΩ) hK hRsyl.2.1 (by omega)
      (hT' ▸ conjSub_mono (n := s) hTJ) hRK
    have h1 : s * z * s⁻¹ = t := (hs.ht.eq (hK' ▸ hs.hz.conj s)).symm
    have h2 : s * t * s⁻¹ = z := (hs.hz.eq (hJ' ▸ hs.ht.conj s)).symm
    calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
      _ = t * z := by rw [h1, h2]
      _ = z * t := hzt.symm

theorem exists_conj_of_le_of_eq_sup_oddCoreOf {X J₀ L : Subgroup G} (hΩ : HypOmegaGen Ω) (hJ₀ : J₀
    ∈ Ω) (hL : L ∈ Ω) (hJ₀X : J₀ ≤ X) (hLX : L ≤ X)
    (hX : X = J₀ ⊔ oddCoreOf X) : ∃ x ∈ X, conjSub x J₀ = L := by
  obtain ⟨T₀, hT₀, -⟩ := IsSylow2In.exists_ge (P := J₀) (T := ⊥) IsPGroup.of_bot bot_le
  have hT₀R : T₀ ∈ RSet Ω := mem_RSet_of_isSylow2In hJ₀ hT₀
  have h8 := hΩ.eight_le_of_mem_RSet hT₀R
  have hTX : IsSylow2In T₀ X := isSylow2In_of_eq_sup_oddCoreOf hJ₀X hX hT₀
  obtain ⟨TL, hTL, -⟩ := IsSylow2In.exists_ge (P := L) (T := ⊥) IsPGroup.of_bot bot_le
  have hcard : Nat.card T₀ = Nat.card TL := by
    exact Disconnected.AschTight.Sec6Gen.natCard_isSylow2In_eq hΩ hJ₀ hL hT₀ hTL
  have hTLX : IsSylow2In TL X := hTX.of_natCard_le hTL.2.1 (hTL.1.trans hLX) hcard.le
  obtain ⟨x, hxX, hxT⟩ := Thompson.exists_conj_of_isSylow2In hTX hTLX
  exact ⟨x, hxX, hΩ.eq_of_le_of_le (hΩ.conjInvariant x J₀ hJ₀) hL hTL.2.1 (by omega)
    (hxT ▸ conjSub_mono (n := x) hT₀.1) hTL.1⟩

theorem mul_inv_mem_oddCoreOf_of_mem_omegaNbr (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {L : Subgroup G}
    (hL : L ∈ omegaNbr Ω K) {y : G} (hy : IsUniqueInvolution L y) :
    y * t⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hJX : J ≤ omegaNbrGen Ω K :=
    le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have hLX : L ≤ omegaNbrGen Ω K :=
    le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) L hL
  obtain ⟨x, hxX, hLx⟩ := exists_conj_of_le_of_eq_sup_oddCoreOf hΩ hs.hJ.1 hL.1 hJX hLX hX
  have hyx : y = x * t * x⁻¹ := hy.eq (hLx ▸ hs.ht.conj x)
  have hN : J ≤ Subgroup.normalizer (oddCoreOf (omegaNbrGen Ω K) : Set G) := fun w hw =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hJX hw))
  have hxX' : x ∈ oddCoreOf (omegaNbrGen Ω K) ⊔ J := by
    rw [sup_comm, ← hX]
    exact hxX
  obtain ⟨o, ho, j, hj, rfl⟩ :=
      Disconnected.AschTight.Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hN hxX'
  have hjt : j * t * j⁻¹ = t := hs.ht.conj_eq (conjSub_eq_self_of_mem hj)
  have htn := hN hs.ht.mem
  have h1 : t * o⁻¹ * t⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) :=
    (Subgroup.mem_normalizer_iff.mp htn o⁻¹).mp ((oddCoreOf (omegaNbrGen Ω K)).inv_mem ho)
  have h2 : y * t⁻¹ = o * (t * o⁻¹ * t⁻¹) := by
    rw [hyx]
    calc o * j * t * (o * j)⁻¹ * t⁻¹ = o * (j * t * j⁻¹) * o⁻¹ * t⁻¹ := by group
      _ = o * (t * o⁻¹ * t⁻¹) := by rw [hjt]; group
  rw [h2]
  exact (oddCoreOf (omegaNbrGen Ω K)).mul_mem ho h1

theorem conj_zt_mul_inv_mem_oddCoreOf (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {y : G}
    (hy : y ∈ Subgroup.centralizer ({z} : Set G)) :
    y * (z * t) * y⁻¹ * (z * t)⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  have hyN : y ∈ Subgroup.normalizer (K : Set G) :=
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz hy
  have hyK : conjSub y K = K := mem_normalizer_iff_conjSub_eq.mp hyN
  have hJy : conjSub y J ∈ omegaNbr Ω K := hyK ▸ omegaNbr_conj hΩ.conjInvariant hs.hJ y
  have h1 := mul_inv_mem_oddCoreOf_of_mem_omegaNbr hs hX hJy (hs.ht.conj y)
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hy
    calc y * z * y⁻¹ = (z * y) * y⁻¹ := by rw [this]
      _ = z := by group
  have hzK : conjSub z K = K := conjSub_eq_self_of_mem hs.hz.mem
  have hzX : z ∈ Subgroup.normalizer ((omegaNbrGen Ω K : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (s26_conjSub_omegaNbrGen hΩ hzK)
  have hzN := mem_normalizer_oddCore_of_mem_normalizer hzX
  have h2 : z * (y * t * y⁻¹ * t⁻¹) * z⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) :=
    (Subgroup.mem_normalizer_iff.mp hzN _).mp h1
  have e : y * (z * t) * y⁻¹ * (z * t)⁻¹ = z * (y * t * y⁻¹ * t⁻¹) * z⁻¹ := by
    calc y * (z * t) * y⁻¹ * (z * t)⁻¹ = (y * z * y⁻¹) * (y * t * y⁻¹) * t⁻¹ * z⁻¹ := by group
      _ = z * (y * t * y⁻¹ * t⁻¹) * z⁻¹ := by rw [hyz]; group
  rw [e]
  exact h2

theorem omegaNbrGen_conjSub (hΩ : HypOmegaGen Ω) {K : Subgroup G} (g : G) :
    omegaNbrGen Ω (conjSub g K) = conjSub g (omegaNbrGen Ω K) := by
  apply le_antisymm
  · refine iSup₂_le fun M hM => ?_
    have h1 : conjSub g⁻¹ M ∈ omegaNbr Ω K := by
      have := omegaNbr_conj hΩ.conjInvariant hM g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have h2 : conjSub g⁻¹ M ≤ omegaNbrGen Ω K :=
      le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) _ h1
    have := conjSub_mono (n := g) h2
    rwa [conjSub_conjSub_inv] at this
  · show (omegaNbrGen Ω K).map (MulAut.conj g).toMonoidHom ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun M' hM' => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω (conjSub g K)) => N) (conjSub g M')
      (omegaNbr_conj hΩ.conjInvariant hM' g)


theorem eq_sup_oddCoreOf_swap (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) :
    omegaNbrGen Ω J = K ⊔ oddCoreOf (omegaNbrGen Ω J) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  obtain ⟨m, hm⟩ := hs.trans J hs.hJ.1
  have hXJ : omegaNbrGen Ω J = conjSub m (omegaNbrGen Ω K) := by
    rw [← hm]
    exact omegaNbrGen_conjSub hΩ m
  have hJ' : omegaNbrGen Ω J = conjSub m J ⊔ oddCoreOf (omegaNbrGen Ω J) := by
    rw [hXJ, oddCoreOf_conjSub_eq]
    conv_lhs => rw [hX]
    exact Asc77.conjSub_sup m _ _
  have hmJ : conjSub m J ∈ omegaNbr Ω J := hm ▸ omegaNbr_conj hΩ.conjInvariant hs.hJ m
  have hKJ : K ∈ omegaNbr Ω J := Q3CL.T3.omegaNbr_symm (l6_2) hΩ hK hs.hJ.1 hs.hJ
  obtain ⟨x, hxX, hxK⟩ := exists_conj_of_le_of_eq_sup_oddCoreOf hΩ
    (hΩ.conjInvariant m J hs.hJ.1) hK
    (le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω J) => N) _ hmJ)
    (le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω J) => N) _ hKJ) hJ'
  have hxN : x ∈ Subgroup.normalizer ((omegaNbrGen Ω J : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hxX
  have hxO := mem_normalizer_oddCore_of_mem_normalizer hxN
  have h1 : conjSub x (omegaNbrGen Ω J) = omegaNbrGen Ω J := conjSub_eq_self_of_mem hxX
  have h2 : conjSub x (oddCoreOf (omegaNbrGen Ω J)) = oddCoreOf (omegaNbrGen Ω J) :=
    mem_normalizer_iff_conjSub_eq.mp hxO
  calc omegaNbrGen Ω J = conjSub x (omegaNbrGen Ω J) := h1.symm
    _ = conjSub x (conjSub m J ⊔ oddCoreOf (omegaNbrGen Ω J)) := by rw [← hJ']
    _ = K ⊔ oddCoreOf (omegaNbrGen Ω J) := by rw [Asc77.conjSub_sup, h2, hxK]
end Cert
end T8R

end

section

set_option linter.unusedSectionVars false
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
section Odd
variable {G : Type} [Group G] [Finite G]
end Odd
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem conj_zt_mul_inv_mem_of_conj (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {n : G}
    (hn : conjSub n K = K ∨ conjSub n J = K) :
    n * (z * t) * n⁻¹ * (z * t)⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  rcases hn with hn | hn
  · refine conj_zt_mul_inv_mem_oddCoreOf hs hX ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hs.hz.conj_eq hn
    calc n * z = (n * z * n⁻¹) * n := by group
      _ = z * n := by rw [h1]
  · have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
    have hNΩ : conjSub n K ∈ Ω := hΩ.conjInvariant n K hK
    have hKN : K ∈ omegaNbr Ω (conjSub n K) := by
      have := omegaNbr_conj hΩ.conjInvariant hs.hJ n
      rwa [hn] at this
    have hN : conjSub n K ∈ omegaNbr Ω K :=
      Q3CL.T3.omegaNbr_symm (l6_2) hΩ hNΩ hK hKN
    have hy : IsUniqueInvolution (conjSub n K) (n * z * n⁻¹) := hs.hz.conj n
    have h1 := mul_inv_mem_oddCoreOf_of_mem_omegaNbr hs hX hN hy
    have hnt : n * t * n⁻¹ = z := by
      have := hs.ht.conj n
      rw [hn] at this
      exact (hs.hz.eq this).symm
    have e : n * (z * t) * n⁻¹ * (z * t)⁻¹ = (n * z * n⁻¹) * t⁻¹ := by
      calc n * (z * t) * n⁻¹ * (z * t)⁻¹ = (n * z * n⁻¹) * (n * t * n⁻¹) * (z * t)⁻¹ := by group
        _ = (n * z * n⁻¹) * z * (t⁻¹ * z⁻¹) := by rw [hnt]; group
        _ = (n * z * n⁻¹) * (z * t⁻¹ * z⁻¹) := by group
        _ = (n * z * n⁻¹) * t⁻¹ := by
          have : z * t⁻¹ * z⁻¹ = t⁻¹ := by
            have h2 : z * t⁻¹ = t⁻¹ * z := by
              have h3 : t * z = z * t := hzt.symm
              calc z * t⁻¹ = t⁻¹ * (t * z) * t⁻¹ := by group
                _ = t⁻¹ * (z * t) * t⁻¹ := by rw [h3]
                _ = t⁻¹ * z := by group
            rw [h2]; group
          rw [this]
    rw [e]
    exact h1
end Cert
end T8R

end

section

set_option linter.unusedSectionVars false
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
section Setup
variable {G : Type} [Group G] [Finite G]
end Setup
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem conj_zt_mul_inv_mem_of_orderFour (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (hV : ExtraTrans Ω K J S z t)
    {n x : G} (hxK : x ∈ K) (hx4 : orderOf x = 4)
    (hxc : x * (n * (z * t) * n⁻¹) = (n * (z * t) * n⁻¹) * x) :
    n * (z * t) * n⁻¹ * (z * t)⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  have h8R := hΩ.eight_le_of_mem_RSet hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hTΩ
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
  have haS : ∀ s ∈ (S : Subgroup G), s * (z * t) = (z * t) * s := fun s hs' => by
    have := conj_zt_of_mem_sylow hs hX hs'
    calc s * (z * t) = (s * (z * t) * s⁻¹) * s := by group
      _ = (z * t) * s := by rw [this]
  obtain ⟨n', hn'c, hxn'⟩ := exists_conj_sylow_of_centralizes S haS hx2 hxc
  rw [← hn'c]
  have key : ∀ m : G, (conjSub m K = K ∨ conjSub m J = K) →
      m * (z * t) * m⁻¹ = n' * (z * t) * n'⁻¹ →
      n' * (z * t) * n'⁻¹ * (z * t)⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) := fun m hm hmc => by
    rw [← hmc]
    exact conj_zt_mul_inv_mem_of_conj hs hX hm
  set M : Subgroup G := conjSub n'⁻¹ K with hMdef
  have hMΩ : M ∈ Ω := hΩ.conjInvariant n'⁻¹ K hK
  have hKM : conjSub n' M = K := by rw [hMdef, conjSub_conjSub_inv]
  have hx'M : n'⁻¹ * x * n' ∈ M := by
    rw [hMdef, mem_conjSub_iff]
    have e : (n'⁻¹)⁻¹ * (n'⁻¹ * x * n') * n'⁻¹ = x := by group
    rw [e]
    exact hxK
  have hx'S : n'⁻¹ * x * n' ∈ (S : Subgroup G) := (mem_conjSub_iff.mp hxn')
  have hx'o : orderOf (n'⁻¹ * x * n') = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj n'⁻¹) x
    rw [MulAut.conj_apply, hx4] at this
    simpa using this
  have h4 : 4 ≤ Nat.card ↥(M ⊓ (S : Subgroup G)) := by
    have hle : Subgroup.zpowers (n'⁻¹ * x * n') ≤ M ⊓ (S : Subgroup G) :=
      le_inf (Subgroup.zpowers_le.mpr hx'M) (Subgroup.zpowers_le.mpr hx'S)
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, hx'o] at this
  have hKS : K ⊓ (S : Subgroup G) = R :=
    hRsyl.eq_of_le (S.isPGroup'.to_inf_right) inf_le_left (le_inf hRK hRS)
  have hJS : J ⊓ (S : Subgroup G) = T :=
    hTsyl.eq_of_le (S.isPGroup'.to_inf_right) inf_le_left (le_inf hTJ hTS)
  by_cases hSyl : IsSylow2In (M ⊓ (S : Subgroup G)) M
  · have hMR : M ⊓ (S : Subgroup G) ∈ RSet Ω := mem_RSet_of_isSylow2In hMΩ hSyl
    rcases eq_or_eq_of_mem_RSet_of_le hs hX hMR inf_le_right with h | h
    · have hRM : R ≤ M := h ▸ inf_le_left
      have hMK : M = K :=
        hΩ.eq_of_le_of_le hMΩ hK hRsyl.2.1 (by omega) hRM hRK
      refine key n' (Or.inl ?_) rfl
      have h' := hKM
      rw [hMK] at h'
      exact h'
    · have hTM : T ≤ M := h ▸ inf_le_left
      have hMJ : M = J :=
        hΩ.eq_of_le_of_le hMΩ hJΩ hTsyl.2.1 (by omega) hTM hTJ
      refine key n' (Or.inr ?_) rfl
      have h' := hKM
      rw [hMJ] at h'
      exact h'
  · have hMK : M ≠ K := by
      intro h
      exact hSyl (by rw [h, hKS]; exact hRsyl)
    have hMJ : M ≠ J := by
      intro h
      exact hSyl (by rw [h, hJS]; exact hTsyl)
    obtain ⟨c₁, hc₁, hc₁K⟩ := hV M hMΩ h4 hMK hMJ
    have hc₁a : c₁ * (z * t) * c₁⁻¹ = z * t := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc₁
      calc c₁ * (z * t) * c₁⁻¹ = ((z * t) * c₁) * c₁⁻¹ := by rw [this]
        _ = z * t := by group
    refine key (n' * c₁) ?_ ?_
    · rcases hc₁K with h | h
      · left
        rw [conjSub_mul, h, hKM]
      · right
        rw [conjSub_mul, h, hKM]
    · calc n' * c₁ * (z * t) * (n' * c₁)⁻¹ = n' * (c₁ * (z * t) * c₁⁻¹) * n'⁻¹ := by group
        _ = n' * (z * t) * n'⁻¹ := by rw [hc₁a]
end Cert
end T8R

end

section

set_option linter.unusedSectionVars false
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
section Pure
variable {G : Type} [Group G] [Finite G]
end Pure
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem frame_perm (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {n' : G} {X : Subgroup G}
    (hXR : X ∈ RSet Ω) (hXS : X ≤ conjSub n' (S : Subgroup G)) :
    X = conjSub n' R ∨ X = conjSub n' T := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have h1 : conjSub n'⁻¹ X ∈ RSet Ω := RSet.conj hΩ.conjInvariant hXR n'⁻¹
  have h2 : conjSub n'⁻¹ X ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := n'⁻¹) hXS
    rwa [conjSub_inv_conjSub] at this
  rcases eq_or_eq_of_mem_RSet_of_le hs hX h1 h2 with h | h
  · left
    have := congrArg (conjSub n') h
    rwa [conjSub_conjSub_inv] at this
  · right
    have := congrArg (conjSub n') h
    rwa [conjSub_conjSub_inv] at this

theorem frame_conj_perm (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {n' q : G}
    (hq : q ∈ conjSub n' (S : Subgroup G)) :
    (conjSub q (conjSub n' R) = conjSub n' R ∧ conjSub q (conjSub n' T) = conjSub n' T) ∨
      (conjSub q (conjSub n' R) = conjSub n' T ∧ conjSub q (conjSub n' T) = conjSub n' R) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRT : R ≠ T := R_ne_T hs
  have hcl := hΩ.conjInvariant
  have hP : ∀ Y ≤ (S : Subgroup G), conjSub q (conjSub n' Y) ≤ conjSub n' (S : Subgroup G) := by
    intro Y hY
    have := conjSub_mono (n := q) (conjSub_mono (n := n') hY)
    rwa [conjSub_eq_self_of_mem hq] at this
  have hR1 := frame_perm hs hX (RSet.conj hcl (RSet.conj hcl hRΩ n') q) (hP R hRS)
  have hT1 := frame_perm hs hX (RSet.conj hcl (RSet.conj hcl hTΩ n') q) (hP T hTS)
  have hne : conjSub n' R ≠ conjSub n' T := fun h => hRT (conjSub_injective n' h)
  rcases hR1 with hR1 | hR1
  · left
    refine ⟨hR1, ?_⟩
    rcases hT1 with hT1 | hT1
    · exact absurd ((conjSub_injective q) (hT1.trans hR1.symm)) (Ne.symm hne)
    · exact hT1
  · right
    refine ⟨hR1, ?_⟩
    rcases hT1 with hT1 | hT1
    · exact hT1
    · exact absurd ((conjSub_injective q) (hT1.trans hR1.symm)) (Ne.symm hne)

theorem eq_of_swap (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (hV : ExtraTrans Ω K J S z t)
    {g : G} (hb : g⁻¹ * (z * t) * g ∈ (S : Subgroup G))
    (hswap : conjSub (g⁻¹ * (z * t) * g) R = T) : g⁻¹ * (z * t) * g = z * t := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hK : K ∈ Ω := hs.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hcl := hΩ.conjInvariant
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  have h8R := hΩ.eight_le_of_mem_RSet hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hTΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  have hzRu : IsUniqueInvolution R z := uniqueInvolution_restrict hs.hz hRK hzR
  have haa : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have haS : ∀ s ∈ (S : Subgroup G), s * (z * t) = (z * t) * s := fun s hs' => by
    have := conj_zt_of_mem_sylow hs hX hs'
    calc s * (z * t) = (s * (z * t) * s⁻¹) * s := by group
      _ = (z * t) * s := by rw [this]
  obtain ⟨b, hbdef⟩ : ∃ b, b = g⁻¹ * (z * t) * g := ⟨_, rfl⟩
  rw [← hbdef] at hb hswap ⊢
  have hbb : b * b = 1 := by
    rw [hbdef]
    calc g⁻¹ * (z * t) * g * (g⁻¹ * (z * t) * g) = g⁻¹ * ((z * t) * (z * t)) * g := by group
      _ = 1 := by rw [haa]; group
  have hbK : conjSub b K = J :=
    hΩ.eq_of_le_of_le (hcl b K hK) hJΩ hTsyl.2.1 (by omega) (hswap ▸ conjSub_mono hRK) hTJ
  have hbJ : conjSub b J = K := by
    have := congrArg (conjSub b) hbK
    rw [← conjSub_mul, hbb, conjSub_one] at this
    exact this.symm
  have hbz : b * z * b⁻¹ = t := (hs.ht.eq (hbK ▸ hs.hz.conj b)).symm
  have hRT : Commutes R T :=
    l6_7_proved G Ω hΩ S R hRΩ T hTΩ hRS hTS (R_ne_T hs)
  have hTmem : ∀ r ∈ R, b * r * b⁻¹ ∈ T := fun r hr => by
    rw [← hswap]
    exact conj_mem_conjSub hr
  have hcomm : ∀ r ∈ R, ∀ s ∈ R, s * (b * r * b⁻¹) = (b * r * b⁻¹) * s := fun r hr s hs' =>
    hRT s hs' _ (hTmem r hr)
  let φ : ↥R →* G := MonoidHom.mk' (fun r => (r : G) * (b * (r : G) * b⁻¹)) (by
    intro r s
    simp only [Subgroup.coe_mul]
    calc (r : G) * (s : G) * (b * ((r : G) * (s : G)) * b⁻¹)
        = (r : G) * ((s : G) * (b * (r : G) * b⁻¹)) * (b * (s : G) * b⁻¹) := by group
      _ = (r : G) * ((b * (r : G) * b⁻¹) * (s : G)) * (b * (s : G) * b⁻¹) := by
        rw [hcomm r r.2 s s.2]
      _ = ((r : G) * (b * (r : G) * b⁻¹)) * ((s : G) * (b * (s : G) * b⁻¹)) := by group)
  have hφ : ∀ r : ↥R, φ r = (r : G) * (b * (r : G) * b⁻¹) := fun r => rfl
  have hQS : φ.range ≤ (S : Subgroup G) := by
    rintro _ ⟨r, rfl⟩
    rw [hφ]
    exact S.mul_mem (hRS r.2)
      (S.mul_mem (S.mul_mem hb (hRS r.2)) (S.inv_mem hb))
  have hQ2 : IsPGroup 2 ↥φ.range := S.isPGroup'.to_le hQS
  have hQb : ∀ y ∈ φ.range, y * b = b * y := by
    rintro _ ⟨r, rfl⟩
    rw [hφ]
    have h1 : b * ((r : G) * (b * (r : G) * b⁻¹)) * b⁻¹ = (r : G) * (b * (r : G) * b⁻¹) := by
      calc b * ((r : G) * (b * (r : G) * b⁻¹)) * b⁻¹
          = (b * (r : G) * b⁻¹) * ((b * b) * (r : G) * (b * b)⁻¹) := by group
        _ = (b * (r : G) * b⁻¹) * (r : G) := by rw [hbb]; group
        _ = (r : G) * (b * (r : G) * b⁻¹) := (hcomm r r.2 r r.2).symm
    calc (r : G) * (b * (r : G) * b⁻¹) * b
        = (b * ((r : G) * (b * (r : G) * b⁻¹)) * b⁻¹) * b := by rw [h1]
      _ = b * ((r : G) * (b * (r : G) * b⁻¹)) := by group
  have hbn : g⁻¹ * (z * t) * (g⁻¹)⁻¹ = b := by rw [hbdef, inv_inv]
  obtain ⟨n', hn'b, hQn'⟩ := exists_conj_sylow_of_le_centralizer S haS (n := g⁻¹) hQ2
    (fun y hy => by rw [hbn]; exact hQb y hy)
  rw [hbn] at hn'b
  have htT : t ∈ T := T3.mem_of_isPGroup hs.ht hTJ hTsyl.2.1 (by omega)
  have haSm : z * t ∈ (S : Subgroup G) := S.mul_mem (hRS hzR) (hTS htT)
  let Nsub : Subgroup ↥R := (Subgroup.normalizer ((conjSub n' R : Subgroup G) : Set G)).comap φ
  let N : Subgroup G := Nsub.map R.subtype
  have hNR : N ≤ R := Subgroup.map_subtype_le _
  have hmemN : ∀ r : ↥R, (r : G) ∈ N ↔ conjSub (φ r) (conjSub n' R) = conjSub n' R := by
    intro r
    constructor
    · intro h
      obtain ⟨r', hr', hrr'⟩ := Subgroup.mem_map.mp h
      have : r' = r := Subtype.ext hrr'
      subst this
      exact mem_normalizer_iff_conjSub_eq.mp (Subgroup.mem_comap.mp hr')
    · intro h
      exact Subgroup.mem_map.mpr
        ⟨r, Subgroup.mem_comap.mpr (mem_normalizer_iff_conjSub_eq.mpr h), rfl⟩
  have hperm : ∀ r : ↥R, ¬ (conjSub (φ r) (conjSub n' R) = conjSub n' R) →
      conjSub (φ r) (conjSub n' R) = conjSub n' T ∧
        conjSub (φ r) (conjSub n' T) = conjSub n' R := by
    intro r hr
    rcases frame_conj_perm hs hX (hQn' ⟨r, rfl⟩) with h | h
    · exact absurd h.1 hr
    · exact h
  have hprod : ∀ x ∈ R, ∀ y ∈ R, x ∉ N → y ∉ N → x * y ∈ N := by
    intro x hx y hy hxN hyN
    have hx' := hperm ⟨x, hx⟩ (fun h => hxN ((hmemN ⟨x, hx⟩).mpr h))
    have hy' := hperm ⟨y, hy⟩ (fun h => hyN ((hmemN ⟨y, hy⟩).mpr h))
    have : ((⟨x, hx⟩ * ⟨y, hy⟩ : ↥R) : G) ∈ N := by
      rw [hmemN, map_mul, conjSub_mul, hy'.1, hx'.2]
    exact this
  obtain ⟨r₁, hr₁N, hr₁o⟩ := exists_orderOf_four_of_swap hzRu hRsyl.2.1 h8R N hNR hprod
  have hr₁R : r₁ ∈ R := hNR hr₁N
  have hr₁sq : r₁ * r₁ = z := by
    have hr4 : (r₁ * r₁) * (r₁ * r₁) = 1 := by
      have h4 : r₁ ^ 4 = (r₁ * r₁) * (r₁ * r₁) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [← h4, ← hr₁o]
      exact pow_orderOf_eq_one r₁
    rcases hzRu.unique _ (R.mul_mem hr₁R hr₁R) hr4 with h | h
    · exfalso
      have h2 : r₁ ^ 2 = 1 := by rw [pow_two]; exact h
      have h4 : orderOf r₁ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
      rw [hr₁o] at h4
      omega
    · exact h
  have hqsq : φ ⟨r₁, hr₁R⟩ * φ ⟨r₁, hr₁R⟩ = z * t := by
    have h1 : (⟨r₁, hr₁R⟩ : ↥R) * ⟨r₁, hr₁R⟩ = ⟨z, hzR⟩ := Subtype.ext hr₁sq
    calc φ ⟨r₁, hr₁R⟩ * φ ⟨r₁, hr₁R⟩ = φ (⟨r₁, hr₁R⟩ * ⟨r₁, hr₁R⟩) := (map_mul φ _ _).symm
      _ = φ ⟨z, hzR⟩ := by rw [h1]
      _ = z * t := by
        rw [hφ]
        show z * (b * z * b⁻¹) = z * t
        rw [hbz]
  have hqN : conjSub (φ ⟨r₁, hr₁R⟩) (conjSub n' R) = conjSub n' R :=
    (hmemN ⟨r₁, hr₁R⟩).mp hr₁N
  have hqS' : φ ⟨r₁, hr₁R⟩ ∈ conjSub n' (S : Subgroup G) := hQn' ⟨_, rfl⟩
  have hK'Ω : conjSub n' K ∈ Ω := hcl n' K hK
  have hz' : IsUniqueInvolution (conjSub n' K) (n' * z * n'⁻¹) := hs.hz.conj n'
  have hqK' : conjSub (φ ⟨r₁, hr₁R⟩) (conjSub n' K) = conjSub n' K :=
    Q3CL.T8.conjSub_eq_of_conjSub_eq hΩ hK'Ω (RSet.conj hcl hRΩ n') (conjSub_mono hRK) hqN
  have hq2 : IsPGroup 2 (Subgroup.zpowers (φ ⟨r₁, hr₁R⟩)) :=
    (isPGroup_conjSub n' S.isPGroup').to_le (Subgroup.zpowers_le.mpr hqS')
  obtain ⟨x₂, hx₂K', hx₂o, hx₂c⟩ := Q3CL.T8.exists_orderFour_centralizes_sq hΩ hK'Ω hz' hq2 hqK'
  rw [hqsq] at hx₂c
  have hxK : n'⁻¹ * x₂ * n' ∈ K := mem_conjSub_iff.mp hx₂K'
  have hxo : orderOf (n'⁻¹ * x₂ * n') = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj n'⁻¹) x₂
    rw [MulAut.conj_apply, hx₂o] at this
    simpa using this
  have hxc : (n'⁻¹ * x₂ * n') * (n'⁻¹ * (z * t) * (n'⁻¹)⁻¹) =
      (n'⁻¹ * (z * t) * (n'⁻¹)⁻¹) * (n'⁻¹ * x₂ * n') := by
    rw [inv_inv]
    calc n'⁻¹ * x₂ * n' * (n'⁻¹ * (z * t) * n') = n'⁻¹ * (x₂ * (z * t)) * n' := by group
      _ = n'⁻¹ * ((z * t) * x₂) * n' := by rw [hx₂c]
      _ = n'⁻¹ * (z * t) * n' * (n'⁻¹ * x₂ * n') := by group
  have hw := conj_zt_mul_inv_mem_of_orderFour hs hX hV (n := n'⁻¹) hxK hxo hxc
  have hwb : n'⁻¹ * ((z * t) * b⁻¹) * n' = n'⁻¹ * (z * t) * (n'⁻¹)⁻¹ * (z * t)⁻¹ := by
    rw [← hn'b]
    group
  exact (eq_of_conj_mul_inv_mem_oddCoreOf S.isPGroup' haSm hb (omegaNbrGen Ω K) n'
    (hwb ▸ hw)).symm
end Cert
end T8R

end

section

set_option linter.unusedSectionVars false
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
section Pure
variable {Γ : Type} [Group Γ]
end Pure
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem sylow_inf_omegaNbrGen (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) :
    (S : Subgroup G) ⊓ omegaNbrGen Ω K = T := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  exact CFSG.ClassicalInvolution.Asc77.T8R.sylow_inf_omegaNbrGen_gen hs.hJ hTJ hTS
    (Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hTΩ hTJ) hX

theorem not_mem_omegaNbr_of_four_le (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {M : Subgroup G} (hM : M ∈ Ω)
    (h4 : 4 ≤ Nat.card ↥(M ⊓ (S : Subgroup G))) (hMJ : M ≠ J) : M ∉ omegaNbr Ω K := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  exact CFSG.ClassicalInvolution.Asc77.T8R.not_mem_omegaNbr_of_four_le_gen hs.hJ hTJ hTS
    (Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hTΩ hTJ) hX
    (fun hA h4' hAM hAJ => hΩ.eq_of_le_of_le hM hs.hJ.1 hA (by omega) hAM hAJ) h4 hMJ

end Cert
end T8R

end

section

set_option linter.unusedSectionVars false
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem zt_mem_sylow (hs : Std8Frame Ω K J S R T W z t) : z * t ∈ (S : Subgroup G) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.mem hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hTΩ hTJ
  have h8R := hΩ.eight_le_of_mem_RSet hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hTΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  have htT : t ∈ T := T3.mem_of_isPGroup hs.ht hTJ hTsyl.2.1 (by omega)
  exact S.mul_mem (hRS hzR) (hTS htT)

theorem eq_of_centralizes (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (hV : ExtraTrans Ω K J S z t)
    {g x : G} (hb : g⁻¹ * (z * t) * g ∈ (S : Subgroup G)) (hxK : x ∈ K) (hx4 : orderOf x = 4)
    (hxc : x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x) :
    g⁻¹ * (z * t) * g = z * t := by
  have hn : x * (g⁻¹ * (z * t) * (g⁻¹)⁻¹) = (g⁻¹ * (z * t) * (g⁻¹)⁻¹) * x := by
    rw [inv_inv]
    exact hxc
  have h1 := conj_zt_mul_inv_mem_of_orderFour hs hX hV (n := g⁻¹) hxK hx4 hn
  rw [inv_inv] at h1
  exact eq_of_mul_inv_mem_odd S.isPGroup' hb (zt_mem_sylow hs) (oddCoreOf_odd_natCard _) h1

theorem eq_of_centralizes_J (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (hV' : ExtraTrans Ω J K S t z)
    {g x : G} (hb : g⁻¹ * (z * t) * g ∈ (S : Subgroup G)) (hxJ : x ∈ J) (hx4 : orderOf x = 4)
    (hxc : x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x) :
    g⁻¹ * (z * t) * g = z * t := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have hs' := hs.symm'
  have hX' := eq_sup_oddCoreOf_swap hs hX
  rw [hzt] at hb hxc ⊢
  exact eq_of_centralizes hs' hX' hV' hb hxJ hx4 hxc


theorem exists_not_comm (hs : Std8Frame Ω K J S R T W z t) : ∃ x y : G, x * y ≠ y * x := by
  obtain ⟨-, P, -, hPnc⟩ := hs.hyp.omega1 K hs.mem
  by_contra hcon
  push Not at hcon
  exact hPnc ⟨⟨fun a b => Subtype.ext (hcon a b)⟩⟩

theorem loc26_of_eq_sup (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) :
    CFSG.ClassicalInvolution.Asc77.T8R.Loc.Loc26 Ω K J S R T z t (oddCoreOf (omegaNbrGen Ω K)) where
  odd := oddCoreOf_odd_natCard _
  rset := fun {_} hP hPS => eq_or_eq_of_mem_RSet_of_le hs hX hP hPS
  four := fun {_} hM h4 hMJ => not_mem_omegaNbr_of_four_le hs hX hM h4 hMJ
  invol := fun {_} hL {_} hy => mul_inv_mem_oddCoreOf_of_mem_omegaNbr hs hX hL hy
  zt := fun {_} hy => conj_zt_mul_inv_mem_oddCoreOf hs hX hy

theorem false_of_hX [IsSimpleGroup G] (hs : Std8Frame Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (hV : ExtraTrans Ω K J S z t)
    (hV' : ExtraTrans Ω J K S t z) (hO : OuterFusion K J S R T z t) : False := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have haa : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hza : orderOf (z * t) = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact haa) ?_
    intro h
    have hzt : z ≠ t := by
      intro h'
      exact hs.hJ.2.1 (hs.noTwins J ⟨hs.hJ.1, z, hs.hz, h' ▸ hs.ht⟩)
    exact hzt ((eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right hs.ht.sq))
  have haS := zt_mem_sylow hs
  obtain ⟨g, hgS, hgne⟩ := Asc77.T8R.exists_conj_mem_sylow_ne (exists_not_comm hs) S haS
    (fun s hs' => by
      have := conj_zt_of_mem_sylow hs hX hs'
      calc s * (z * t) = (s * (z * t) * s⁻¹) * s := by group
        _ = (z * t) * s := by rw [this]) hza
  apply hgne
  rcases fix_or_swap hs hX hgS with ⟨hR, hT⟩ | ⟨hR, -⟩
  · by_cases hK : ∃ x ∈ K, orderOf x = 4 ∧
        x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x
    · obtain ⟨x, hxK, hx4, hxc⟩ := hK
      exact eq_of_centralizes hs hX hV hgS hxK hx4 hxc
    by_cases hJ : ∃ x ∈ J, orderOf x = 4 ∧
        x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x
    · obtain ⟨x, hxJ, hx4, hxc⟩ := hJ
      exact eq_of_centralizes_J hs hX hV' hgS hxJ hx4 hxc
    exact hO g hgS hR hT hK hJ
  · exact eq_of_swap hs hX hV hgS hR
end Cert
end T8R

end

section

set_option linter.unusedSectionVars false
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R


end T8R

end

section

set_option linter.unusedSectionVars false
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8
    CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
section Pure
variable {G : Type} [Group G]
end Pure
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem eq_sup_oddCoreOf_conj (hΩ : HypOmegaGen Ω)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (n : G) :
    omegaNbrGen Ω (conjSub n K) = conjSub n J ⊔ oddCoreOf (omegaNbrGen Ω (conjSub n K)) := by
  rw [omegaNbrGen_conjSub hΩ, oddCoreOf_conjSub_eq]
  conv_lhs => rw [hX]
  exact Asc77.conjSub_sup n _ _
end Cert
end T8R

end

section

set_option linter.unusedSectionVars false
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8
    CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


end Cert


end T8R

end

end CFSG.ClassicalInvolution.Q3.Q3CL.Frame
