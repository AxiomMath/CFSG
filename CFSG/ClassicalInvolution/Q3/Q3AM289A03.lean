module

public import CFSG.ClassicalInvolution.Q3.Q3T8B14E
public import CFSG.ClassicalInvolution.Q3.Q3T8B18B
public import CFSG.ClassicalInvolution.Q3.Q3T6AutNorm
import CFSG.ClassicalInvolution.Q3.Q3T8B14Core
public import CFSG.ClassicalInvolution.Q3.Q3T8B01
public import CFSG.ClassicalInvolution.Q3.Q3T8B05

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Asc77.Thompson
open scoped MatrixGroups commutatorElement

namespace S3A

section Shape


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem layerShapeD [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hno : ∀ L : Subgroup G, L ∈ omegaNbr Ω K → L ∈ omegaNbr Ω J → False) :
    ¬ DConnected (Q3T7.layerFam3 Ω (z * t)) ∨
      ∀ M ∈ Q3T7.layerFam3 Ω (z * t),
        M = Layer.layerImg3 Ω (z * t) K ∨ M = Layer.layerImg3 Ω (z * t) J := by
  classical
  by_cases hconn : DConnected (Q3T7.layerFam3 Ω (z * t))
  swap
  · exact Or.inl hconn
  right
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have hXK : T8.XMem Ω (z * t) K := Layer.xMem_zt3 hs
  have hXJ : T8.XMem Ω (z * t) J := T8V.xMem_J hs
  have hKt : K ∈ tqMembers3 Ω (z * t) := hXK.mem_tqMembers3 hΩ hx
  have hJt : J ∈ tqMembers3 Ω (z * t) := hXJ.mem_tqMembers3 hΩ hx
  have hs3 : Q3.Disc3.AscStand3 Ω K := hs.stand.toStand3
  have hL : Layer.LayerHyp Ω (z * t) := Layer.LayerHyp.of_stand3 hs3 hx ⟨K, hKt⟩
  have hn21 : K ∈ omegaNbr Ω J :=
    Q3CL.T3.omegaNbr_symm Disconnected.AschTight.Sec6Gen.l6_2Gen hΩ hs.stand.mem hs.hJ.1 hs.hJ
  have hKJ : ∀ {M : Subgroup G}, M ∈ tqMembers3 Ω (z * t) → M ∈ omegaNbr Ω K → M = J :=
    fun hM hMK => eq_partner_of_mem_omegaNbr_tq hΩ hnt hs.hz hs.ht hs.hJ hno hM hMK
  have hJK : ∀ {M : Subgroup G}, M ∈ tqMembers3 Ω (z * t) → M ∈ omegaNbr Ω J → M = K :=
    fun {M} hM hMJ => by
      have hM' : M ∈ tqMembers3 Ω (t * z) := hzt ▸ hM
      exact eq_partner_of_mem_omegaNbr_tq hΩ hnt hs.ht hs.hz hn21
        (fun L h1 h2 => hno L h2 h1) hM' hMJ
  have hcen : ∀ {n : G}, n ∈ oddCoreOf (exactLayer3 Ω (z * t)) →
      n ∈ Subgroup.centralizer ({z * t} : Set G) := fun {n} hn =>
    (T8.cenZ_eq_centralizer (z * t)) ▸
      Layer.exactLayer3_le_cenZ Ω (z * t) (oddCoreOf_le_self _ hn)
  have step : ∀ {X : Subgroup G}, X ∈ tqMembers3 Ω (z * t) →
      (∀ {M : Subgroup G}, M ∈ tqMembers3 Ω (z * t) → M ∈ omegaNbr Ω X →
        Layer.layerImg3 Ω (z * t) M = Layer.layerImg3 Ω (z * t) K ∨
          Layer.layerImg3 Ω (z * t) M = Layer.layerImg3 Ω (z * t) J) →
      ∀ {B' : Subgroup (Q3T7.layerQuot3 Ω (z * t))}, B' ∈ Q3T7.layerFam3 Ω (z * t) →
        dAdj (Q3T7.layerFam3 Ω (z * t)) (Layer.layerImg3 Ω (z * t) X) B' →
          B' = Layer.layerImg3 Ω (z * t) K ∨ B' = Layer.layerImg3 Ω (z * t) J := by
    intro X hXt hnbr B' hBΦ hadj
    obtain ⟨M, hMt, hMB⟩ : ∃ M ∈ tqMembers3 Ω (z * t), Layer.layerImg3 Ω (z * t) M = B' := by
      obtain ⟨_, ⟨L₀, ⟨⟨M, hM, rfl⟩, -⟩, hLY, rfl⟩, hb⟩ := hBΦ
      exact ⟨M, hM, hb⟩
    have hM' : ∃ M' : Subgroup G, M' ∈ tqMembers3 Ω (z * t) ∧
        Layer.layerImg3 Ω (z * t) M' = B' ∧ M' ∈ omegaNbr Ω X := by
      rcases hadj with h | h
      · rw [← hMB] at h
        obtain ⟨n, hn, hmn⟩ := Layer.exists_oddCore_conj_omegaNbr3 hL hXt hMt h
        have h1 := omegaNbr_conj hΩ.conjInvariant hmn n⁻¹
        rw [conjSub_inv_conjSub] at h1
        have hninv : n⁻¹ ∈ oddCoreOf (exactLayer3 Ω (z * t)) := (oddCoreOf _).inv_mem hn
        exact ⟨conjSub n⁻¹ M, conjSub_mem_tqMembers3 hΩ.conjInvariant (hcen hninv) hMt,
          (Layer.layerImg3_conj_of_mem_oddCore hninv).trans hMB, h1⟩
      · rw [← hMB] at h
        obtain ⟨n, hn, hmn⟩ := Layer.exists_oddCore_conj_omegaNbr3 hL hMt hXt h
        exact ⟨conjSub n M, conjSub_mem_tqMembers3 hΩ.conjInvariant (hcen hn) hMt,
          (Layer.layerImg3_conj_of_mem_oddCore hn).trans hMB,
          Q3CL.T3.omegaNbr_symm Disconnected.AschTight.Sec6Gen.l6_2Gen hΩ
            (hΩ.conjInvariant n M hMt.1) hXt.1 hmn⟩
    obtain ⟨M', hM't, hM'B, hM'X⟩ := hM'
    rw [← hM'B]
    exact hnbr hM't hM'X
  have hmain : ∀ {B' : Subgroup (Q3T7.layerQuot3 Ω (z * t))},
      Relation.ReflTransGen (fun A B : Subgroup (Q3T7.layerQuot3 Ω (z * t)) =>
        B ∈ Q3T7.layerFam3 Ω (z * t) ∧ dAdj (Q3T7.layerFam3 Ω (z * t)) A B)
        (Layer.layerImg3 Ω (z * t) K) B' →
        B' = Layer.layerImg3 Ω (z * t) K ∨ B' = Layer.layerImg3 Ω (z * t) J := by
    intro B' hB'
    induction hB' with
    | refl => exact Or.inl rfl
    | tail _ hadj ih =>
      rcases ih with h | h
      · rw [h] at hadj
        exact step hKt (fun hM hMK => Or.inr (by rw [hKJ hM hMK])) hadj.1 hadj.2
      · rw [h] at hadj
        exact step hJt (fun hM hMJ => Or.inl (by rw [hJK hM hMJ])) hadj.1 hadj.2
  intro M hM
  exact hmain (hconn _ (Layer.layerImg3_mem hKt) _ hM)

theorem omegaNbr_of_trivialOn_layerImg [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t) {t₁ : G}
    (ht1 : t₁ ∈ T8.cenZ (z * t)) (ht1sq : t₁ * t₁ = 1) (hne : t₁ ≠ t) (hnJ : conjSub t₁ J = J)
    {J₁ : Subgroup G} (hJ₁ : J₁ ∈ Ω) (hJ₁t : IsUniqueInvolution J₁ t₁)
    (H₀ : ∀ kb ∈ Layer.layerImg3 Ω (z * t) J,
      s26Act (exactLayer3 Ω (z * t)) ⟨t₁, mem_normalizer_iff_conjSub_eq.mpr
        (Layer.exactLayer3_conjSub_eq hs.stand.hyp.conjInvariant ht1)⟩ kb * kb⁻¹ ∈
          oddCoreOf (Layer.layerImg3 Ω (z * t) J)) :
    J ∈ omegaNbr Ω J₁ :=
  T8W.mem_omegaNbr_of_trivialOn_layerImg hs ht1 ht1sq hne hnJ hJ₁ hJ₁t H₀

end Shape

section Inner

variable {G : Type} [Group G] [Finite G]

theorem exists_exactCore_inner_of_sq {J : Subgroup G} {t c : G} (hJ : IsClassicalMember3 J t)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcJ : c ∈ trivialOnQuot J) {w' s : G}
    (hw' : w' ∈ Subgroup.normalizer (J : Set G)) (hs : w' * w' = s) :
    ∃ i ∈ exactCore3 c J, ∀ j ∈ J, ⁅i⁻¹ * s, j⁆ ∈ oddCoreOf J := by
  obtain ⟨e⟩ := hJ.nonempty_equiv
  have hsN : s ∈ Subgroup.normalizer (J : Set G) :=
    hs ▸ (Subgroup.normalizer (J : Set G)).mul_mem hw' hw'
  have h1 : Q3T6.normalizerToAutSL3 e ⟨s, hsN⟩ =
      Q3T6.normalizerToAutSL3 e ⟨w', hw'⟩ * Q3T6.normalizerToAutSL3 e ⟨w', hw'⟩ := by
    rw [← map_mul]
    exact congrArg _ (Subtype.ext hs.symm)
  have h2 : Q3T6.normalizerToAutSL3 e ⟨s, hsN⟩ ∈ Q3T6.inn3 := by
    rw [h1]
    exact Subgroup.mul_self_mem_of_index_two Q3T6.inn3_index _
  obtain ⟨g, hg⟩ := Q3T6.mem_inn3_iff.mp h2
  obtain ⟨κ, hκ⟩ := QuotientGroup.mk_surjective (e.symm g)
  have hres := axisResidual_exactCore3 hJ hc2 hcJ
  obtain ⟨i, hi, n, hn, hκin⟩ := hres.cover (κ : G) κ.2
  have hiJ : i ∈ J := exactCore3_le_left c J hi
  have hiN : i ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hiJ
  have hmk : e (QuotientGroup.mk ⟨i, hiJ⟩) = g := by
    have hqq : (QuotientGroup.mk ⟨i, hiJ⟩ : ↥J ⧸ classicalInvolutionOddCore ↥J) =
        QuotientGroup.mk κ := by
      obtain ⟨n', hn', rfl⟩ := hn
      have hn'' : n' ∈ classicalInvolutionOddCore ↥J := hn'
      have hκ' : κ = ⟨i, hiJ⟩ * n' := Subtype.ext hκin
      rw [hκ', QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff (N := classicalInvolutionOddCore ↥J) n').mpr hn'', mul_one]
    rw [hqq, hκ, MulEquiv.apply_symm_apply]
  have hΦi : Q3T6.normalizerToAutSL3 e ⟨i, hiN⟩ = MulAut.conj g := by
    rw [Q3T6.normalizerToAutSL3_of_mem e hiJ, hmk]
  have his : i⁻¹ * s ∈ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normalizer (J : Set G)).mul_mem (Subgroup.inv_mem _ hiN) hsN
  have hone : Q3T6.normalizerToAutSL3 e ⟨i⁻¹ * s, his⟩ = 1 := by
    have e1 : (⟨i⁻¹ * s, his⟩ : Subgroup.normalizer (J : Set G)) =
        (⟨i, hiN⟩ : Subgroup.normalizer (J : Set G))⁻¹ * ⟨s, hsN⟩ := Subtype.ext rfl
    rw [e1, map_mul, map_inv, hΦi, hg, inv_mul_cancel]
  exact ⟨i, hi, (Q3T6.normalizerToAutSL3_eq_one_iff e ⟨i⁻¹ * s, his⟩).mp hone⟩

end Inner

end S3A

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
