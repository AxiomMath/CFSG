module

public import CFSG.ClassicalInvolution.Q3.Q3T8B14A
public import CFSG.ClassicalInvolution.Q3.Q3T8E4B
public import CFSG.ClassicalInvolution.Q3.Q3NMDiag

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement MatrixGroups
namespace T8W
open CFSG.ClassicalInvolution.Asc77.T8W
section Vertex
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem mem_omegaNbr_of_trivialOn_layerImg [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    {t₁ : G} (ht1 : t₁ ∈ T8.cenZ (z * t)) (ht1sq : t₁ * t₁ = 1) (hne : t₁ ≠ t)
    (hnJ : conjSub t₁ J = J) {J₁ : Subgroup G} (hJ₁ : J₁ ∈ Ω) (hJ₁t : IsUniqueInvolution J₁ t₁)
    (H₀ : ∀ kb ∈ Layer.layerImg3 Ω (z * t) J,
      s26Act (Q3NL.exactLayer3 Ω (z * t)) ⟨t₁, mem_normalizer_iff_conjSub_eq.mpr
        (Layer.exactLayer3_conjSub_eq hs.stand.hyp.conjInvariant ht1)⟩ kb * kb⁻¹ ∈
          oddCoreOf (Layer.layerImg3 Ω (z * t) J)) :
    J ∈ omegaNbr Ω J₁ := by
  classical
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hXJ : T8.XMem Ω (z * t) J := T8V.xMem_J hs
  have hJt : J ∈ Q3NL.tqMembers3 Ω (z * t) := hXJ.mem_tqMembers3 hΩ hx
  have hyY : t₁ ∈ Subgroup.normalizer ((Q3NL.exactLayer3 Ω (z * t) : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (Layer.exactLayer3_conjSub_eq hΩ.conjInvariant ht1)
  have hJN : t₁ ∈ Subgroup.normalizer (J : Set G) := mem_normalizer_iff_conjSub_eq.mpr hnJ
  have hLaN : t₁ ∈ Subgroup.normalizer (Q3NL.exactCore3 (z * t) J : Set G) :=
    Layer.mem_normalizer_exactCore3 hJN ht1

  have hstep1 : ∀ k ∈ Q3NL.exactCore3 (z * t) J, ⁅t₁, k⁆ ∈ oddCoreOf (Q3NL.exactCore3 (z * t) J) :=
      by
    intro k hk
    have hkY : k ∈ Q3NL.exactLayer3 Ω (z * t) := Q3NL.exactCore3_le_exactLayer3 hJt hk
    have hyk : t₁ * k * t₁⁻¹ ∈ Q3NL.exactLayer3 Ω (z * t) :=
      (Subgroup.mem_normalizer_iff.mp hyY k).mp hkY
    have hkb : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω (z * t)))
        (⟨k, hkY⟩ : ↥(Q3NL.exactLayer3 Ω (z * t))) : Q3T7.layerQuot3 Ω (z * t)) ∈
        Layer.layerImg3 Ω (z * t) J := ⟨⟨k, hkY⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have h0 := H₀ _ hkb
    have e := s26Act_mk (Q3NL.exactLayer3 Ω (z * t)) ⟨t₁, hyY⟩ ⟨k, hkY⟩ ⟨t₁ * k * t₁⁻¹, hyk⟩ rfl
    have hc : ((⟨t₁ * k * t₁⁻¹, hyk⟩ * (⟨k, hkY⟩ : ↥(Q3NL.exactLayer3 Ω (z * t)))⁻¹ :
        ↥(Q3NL.exactLayer3 Ω (z * t))) : G) = ⁅t₁, k⁆ := by
      simp [commutatorElement_def]
    have hcomm_mem : ⁅t₁, k⁆ ∈ Q3NL.exactCore3 (z * t) J := by
      rw [commutatorElement_def]
      exact (Q3NL.exactCore3 (z * t) J).mul_mem ((Subgroup.mem_normalizer_iff.mp hLaN k).mp hk)
        ((Q3NL.exactCore3 (z * t) J).inv_mem hk)
    rw [← hc]
    refine mem_oddCoreOf_layerRes_of_mk_mem hJt _ (by rw [hc]; exact hcomm_mem) ?_
    change s26Act (Q3NL.exactLayer3 Ω (z * t)) ⟨t₁, hyY⟩ (↑(⟨k, hkY⟩ : ↥(Q3NL.exactLayer3 Ω (z *
        t)))) *
      (↑(⟨k, hkY⟩ : ↥(Q3NL.exactLayer3 Ω (z * t))))⁻¹ ∈ _ at h0
    rw [e] at h0
    simpa [QuotientGroup.mk'_apply, map_mul, map_inv] using h0

  set La : Subgroup G := Q3NL.exactCore3 (z * t) J with hLa
  have hLaJ : La ≤ J := Q3NL.exactCore3_le_left _ J
  have hTJ : IsSylow2In T J := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ
      hs.hT.1 hs.hT.2.1
  have hTLa : IsSylow2In T La := Layer.isSylow2In_exactCore3_of_le_cenZ hTJ (T8V.T_le_cenZ hs)
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers t₁) := by
    obtain ⟨m, hm⟩ := T8.exists_orderOf_eq_two_pow ht1sq
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hĴN : La ⊔ Subgroup.zpowers t₁ ≤ Subgroup.normalizer (La : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hLaN)
  obtain ⟨V, hV, hVt⟩ := IsSylow2In.exists_ge hzp
    (le_sup_right : Subgroup.zpowers t₁ ≤ La ⊔ Subgroup.zpowers t₁)
  have hP : IsSylow2In (V ⊓ La) La :=
    AscP1Nine3.isSylow2In_inf_of_le_normalizer' hV le_sup_left hĴN
  have hPcard : Nat.card ↥(V ⊓ La) = Nat.card T := hP.natCard_eq hTLa
  have hPJ : IsSylow2In (V ⊓ La) J :=
    IsSylow2In.of_natCard_le hTJ hP.2.1 (inf_le_right.trans hLaJ) (le_of_eq hPcard.symm)
  have hPc : V ⊓ La ≤ Subgroup.centralizer ({t₁} : Set G) := by
    intro k hk
    have hkV : k ∈ V := hk.1
    have hkLa : k ∈ La := hk.2
    have ht1V : t₁ ∈ V := hVt (Subgroup.mem_zpowers t₁)
    have hmemV : ⁅t₁, k⁆ ∈ V := by
      rw [commutatorElement_def]
      exact V.mul_mem (V.mul_mem (V.mul_mem ht1V hkV) (V.inv_mem ht1V)) (V.inv_mem hkV)
    have hpg : IsPGroup 2 ↥(Subgroup.zpowers ⁅t₁, k⁆) :=
      hV.2.1.to_le (Subgroup.zpowers_le.mpr hmemV)
    have h1 : ⁅t₁, k⁆ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) (hstep1 k hkLa) hpg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

  have hPR : V ⊓ La ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ hPJ
  have h8 : 8 ≤ Nat.card ↥(V ⊓ La) := hΩ.eight_le_of_mem_RSet hPR
  have hJJ₁ : J ≠ J₁ := by
    intro h
    have h1 : t₁ ∈ J := h ▸ hJ₁t.mem
    rcases hs.ht.unique t₁ h1 ht1sq with h2 | h2
    · exact hJ₁t.ne_one h2
    · exact hne h2
  have hPN : V ⊓ La ≤ Subgroup.normalizer (J₁ : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hJ₁ hJΩ (Ne.symm hJJ₁) hJ₁t
      (inf_le_right.trans hLaJ) hP.2.1 (by omega) hPc
  have hJnb : J ∈ omegaNbr Ω J₁ :=
    ⟨hJΩ, hJJ₁, V ⊓ La, hPR, inf_le_right.trans hLaJ, hPN⟩
  exact hJnb

theorem layer_class_psl4_of_not [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    {w : G} (hw2 : w * w = 1) (hwz : z * w = w * z) (hwt : t * w = w * t)
    {R₀ : Subgroup G} (hR₀ : IsSylow2In R₀ K) (hwR : ∀ r ∈ R₀, r * w = w * r)
    (hdisc : ¬ T3.DStarConnected (Q3T7.layerFam3 Ω (z * t)))
    (hwN : w ∈ Subgroup.normalizer ((Q3NL.exactLayer3 Ω (z * t) : Subgroup G) : Set G))
    (hnot : w ∈ T8.cenZ (z * t) → ¬ ∀ kb ∈ Layer.layerImg3 Ω (z * t) J,
      s26Act (Q3NL.exactLayer3 Ω (z * t)) ⟨w, hwN⟩ kb * kb⁻¹ ∈
        oddCoreOf (Layer.layerImg3 Ω (z * t) J)) :
    ∃ (M : Ih8Model 3 1 (Q3T7.layerFam3 Ω (z * t)) .PSL 4 1)
      (D : GL (Fin 4) (GaloisField 3 1)) (y' : SL(4, GaloisField 3 1)),
      M.ψ y' = T8V.layerMk (z * t) t (T8V.t_mem_layerJoin hs) ∧ y' * y' = 1 ∧ D * D = 1 ∧
        (∀ g, s26Act (Q3NL.exactLayer3 Ω (z * t)) ⟨w, hwN⟩ (M.ψ g) =
          M.ψ (Q3NM.conjSLAut D g)) ∧
        (D : Matrix (Fin 4) (Fin 4) (GaloisField 3 1)) *
            (y' : Matrix (Fin 4) (Fin 4) (GaloisField 3 1)) =
          (y' : Matrix (Fin 4) (Fin 4) (GaloisField 3 1)) * D := by
  classical
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hXK : T8.XMem Ω (z * t) K := Layer.xMem_zt3 hs
  have hXJ : T8.XMem Ω (z * t) J := T8V.xMem_J hs
  have hKt : K ∈ Q3NL.tqMembers3 Ω (z * t) := hXK.mem_tqMembers3 hΩ hx
  have hJt : J ∈ Q3NL.tqMembers3 Ω (z * t) := hXJ.mem_tqMembers3 hΩ hx
  have hs3 : Q3.Disc3.AscStand3 Ω K := hs.stand.toStand3
  have hL : Layer.LayerHyp Ω (z * t) := Layer.LayerHyp.of_stand3 hs3 hx ⟨K, hKt⟩
  have hne0 : (Q3NL.tqMembers3 Ω (z * t)).Nonempty := ⟨K, hKt⟩
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have htcen : t ∈ T8.cenZ (z * t) := T8.mem_cenZ_iff.mpr (by
    have h1 : t * (z * t) = z := by rw [hzt, ← mul_assoc, hs.ht.sq, one_mul]
    have h2 : z * t * t = z := by rw [mul_assoc, hs.ht.sq, mul_one]
    rw [h1, h2])
  have hwcen : w ∈ T8.cenZ (z * t) := T8.mem_cenZ_iff.mpr (by
    calc w * (z * t) = (w * z) * t := by rw [mul_assoc]
      _ = (z * w) * t := by rw [hwz]
      _ = z * (w * t) := by rw [mul_assoc]
      _ = z * (t * w) := by rw [hwt]
      _ = z * t * w := by rw [mul_assoc])
  have htY := T8V.t_mem_layerJoin hs
  have hzY := T8V.z_mem_layerJoin hs
  set σ : MulAut (Q3T7.layerQuot3 Ω (z * t)) :=
    s26Act (Q3NL.exactLayer3 Ω (z * t)) ⟨w, hwN⟩ with hσ
  set x' : Q3T7.layerQuot3 Ω (z * t) := T8V.layerMk (z * t) t htY with hx'
  set x : Q3T7.layerQuot3 Ω (z * t) := T8V.layerMk (z * t) z hzY with hxdef
  have hlt := Q3T7.card_layerQuot3_lt (Ω := Ω) (Layer.zt_not_central3 hs)
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω (z * t)))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hne' : Layer.layerImg3 Ω (z * t) K ≠ Layer.layerImg3 Ω (z * t) J :=
    Layer.layerImg3_ne_of_involutions hL hXK hXJ hs.hz hs.ht hzt
      (T8.ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht)
  have hTJ : IsSylow2In T J :=
    Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1
  have hc : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := by
    intro y hy
    have hn21 : K ∈ omegaNbr Ω J :=
      Q3CL.T3.omegaNbr_symm (l6_2) hΩ hs.stand.mem hs.hJ.1 hs.hJ
    have h1 : y ∈ Subgroup.centralizer ({z} : Set G) :=
      T8.rep_le_centralizer hc (T8.stdRepJ hs) (T8.stdRepK hs) (Or.inr hn21) hs.hz hy
    exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hs.stand.mem hs.noTwins hs.hz h1
  have hAB : Layer.layerImg3 Ω (z * t) J ∈ omegaNbr (Q3T7.layerFam3 Ω (z * t))
      (Layer.layerImg3 Ω (z * t) K) :=
    Layer.layerImg3_omegaNbr hKt hJt hTJ (T8V.T_le_cenZ hs) hTN hne'
  have hLYK : Q3NL.exactCore3 (z * t) K ≤ Q3NL.exactLayer3 Ω (z * t) :=
    Q3NL.exactCore3_le_exactLayer3 hKt
  have hLYJ : Q3NL.exactCore3 (z * t) J ≤ Q3NL.exactLayer3 Ω (z * t) :=
    Q3NL.exactCore3_le_exactLayer3 hJt
  have hzL : IsUniqueInvolution (Q3NL.exactCore3 (z * t) K) z :=
    Layer.isUniqueInvolution_exactCore3 hXK.2.1 hs.hz
  have htL : IsUniqueInvolution (Q3NL.exactCore3 (z * t) J) t :=
    Layer.isUniqueInvolution_exactCore3 hXJ.2.1 hs.ht
  have hxA : IsUniqueInvolution (Layer.layerImg3 Ω (z * t) K) x :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
      (isUniqueInvolution_subgroupOf hzL hLYK)
  have hxB : IsUniqueInvolution (Layer.layerImg3 Ω (z * t) J) x' :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
      (isUniqueInvolution_subgroupOf htL hLYJ)
  have hcen : x * x' ∈ Subgroup.center (Q3T7.layerQuot3 Ω (z * t)) := T8V.layerMk_central hs
  have hσsq : σ * σ = 1 := by
    rw [hσ, ← map_mul]
    have : (⟨w, hwN⟩ * ⟨w, hwN⟩ : ↥(Subgroup.normalizer
        ((Q3NL.exactLayer3 Ω (z * t) : Subgroup G) : Set G))) = 1 := Subtype.ext hw2
    rw [this, map_one]
  have hyNK : w ∈ Subgroup.normalizer (K : Set G) :=
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr hwz.symm)
  have hcommK : ∀ k ∈ K, ⁅w, k⁆ ∈ oddCoreOf K :=
    commutator_mem_oddCoreOf_of_pow3 hs.hz hR₀ hyNK (m := 1)
      (by rw [pow_one, pow_two]; exact hw2) (fun r hr => (hwR r hr).symm)
  have hσA : ∀ k ∈ Layer.layerImg3 Ω (z * t) K,
      σ k * k⁻¹ ∈ oddCoreOf (Layer.layerImg3 Ω (z * t) K) :=
    T8V.s26Act_mul_inv_mem hΩ hKt hwcen hyNK hcommK
  have hσnt : ¬ ∀ k ∈ Layer.layerImg3 Ω (z * t) J,
      σ k * k⁻¹ ∈ oddCoreOf (Layer.layerImg3 Ω (z * t) J) :=
    hnot hwcen
  have hΦ : HypOmegaModU (.sl2 3 1) (Q3T7.layerFam3 Ω (z * t)) :=
    Q3T7.hypOmegaModU_layerFam3 hs3 hL.hc2 hne0
  have hKΦ : Layer.layerImg3 Ω (z * t) K ∈ Q3T7.layerFam3 Ω (z * t) := Layer.layerImg3_mem hKt
  obtain ⟨t', k, htag, ⟨M⟩⟩ := E4G3.e4_tag3 hs.stand.below hs.stand.ih hlt hΦ
    Q3T7.layerQuot3_oddCore_eq_bot (Q3T7.omegaGen_layerFam3 hs3 hL.hc2 hne0)
    (Q3T7.aEmpty_layerFam3 hs3 hL.hc2 hne0) hdisc hKΦ hAB
  rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h4 | ⟨rfl, rfl⟩ | h6
  · exact (E4G3.e4_gen_sp3 hΦ M hKΦ hAB hxA hxB hcen σ hσsq hσA hσnt).elim
  · obtain ⟨D, y', hy', hy'2, hD2, hDσ, hDc⟩ :=
      E4G3.e4_class_sl43 hΦ M hKΦ hAB hxA hxB hcen σ hσsq hσA hσnt
    exact ⟨M, D, y', hy', hy'2, hD2, hDσ, hDc⟩
  · exact absurd (E4G3.dstarConnected_psu43 hΦ M) hdisc
  · exact absurd (E4G3.dstarConnected_spin_of_pair3 hΦ M (Or.inl h4) hKΦ hAB hxA hxB hcen) hdisc
  · exact absurd (E4G3.dstarConnected_spin8plus3 hΦ M) hdisc
  · exact absurd (E4G3.dstarConnected_spin_of_pair3 hΦ M (Or.inr h6) hKΦ hAB hxA hxB hcen) hdisc
end Vertex
end T8W
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
