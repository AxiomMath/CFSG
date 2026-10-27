module

public import CFSG.ClassicalInvolution.Q3.Q3T8P26D02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26E03
public import CFSG.ClassicalInvolution.Q3.Q3T8P26E02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26E01

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
open scoped commutatorElement
namespace T8ZZ
open CFSG.ClassicalInvolution.Asc77.T8ZZ
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_xMem_of_mem_layerFam3 {x : G} (hc2 : IsPGroup 2 (Subgroup.zpowers x))
    {C : Subgroup (Q3T7.layerQuot3 Ω x)} (hC : C ∈ Q3T7.layerFam3 Ω x) :
    ∃ L, T8.XMem Ω x L ∧ Layer.layerImg3 Ω x L = C := by
  have hmem : ∃ K ∈ Q3NL.tqMembers3 Ω x, Layer.layerImg3 Ω x K = C := by
    obtain ⟨_, ⟨L₀, ⟨⟨K, hK, rfl⟩, -⟩, hLY, rfl⟩, hb⟩ := hC
    exact ⟨K, hK, hb⟩
  obtain ⟨K, hK, hKC⟩ := hmem
  refine ⟨K, ?_, hKC⟩
  obtain ⟨R, hRK, hRfix⟩ := T3.exists_sylow_normalized hc2 (Subgroup.zpowers_le.mpr hK.2.1)
  have hRx : conjSub x R = R := hRfix x (Subgroup.mem_zpowers x)
  exact ⟨hK.1, hK.2.1, R, hRK, fun r hr =>
    commute_of_normalizes_sylow hRK.2.1 hRK.1 hRx hK.2.2 hr⟩

variable [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AlphaFrame3] in
theorem layerImg_nbr_in_frame_z [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (huni : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      ¬ DConnected (Q3T7.layerFam3 Ω (z * s)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) (F : T8YY.FrameData Ω W K J z t)
    {j : Fin 4} (hj : j ≠ 0) {L : Subgroup G} (hL : T8.XMem Ω z L) (hLK : L ≠ K)
    (hadj : Layer.layerImg3 Ω z L ∈
        omegaNbr (Q3T7.layerFam3 Ω z) (Layer.layerImg3 Ω z (F.ρ j).K) ∨
      Layer.layerImg3 Ω z (F.ρ j).K ∈ omegaNbr (Q3T7.layerFam3 Ω z) (Layer.layerImg3 Ω z L)) :
    ∃ i : Fin 4, i ≠ 0 ∧ i ≠ j ∧ Layer.layerImg3 Ω z L = Layer.layerImg3 Ω z (F.ρ i).K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hz2 : z * z = 1 := hs.hz.sq
  have hKj : (F.ρ j).K ∈ Q3NL.tqMembers3 Ω z := (frame_xMem_z hs F j).mem_tqMembers3 hΩ hz2
  have hLt : L ∈ Q3NL.tqMembers3 Ω z := hL.mem_tqMembers3 hΩ hz2
  have hLH : Layer.LayerHyp Ω z := Layer.LayerHyp.of_stand3 hs.stand.toStand3 hz2 ⟨_, hLt⟩
  have hLnbr : L ∈ omegaNbr Ω K := omegaNbr_of_xMem_z hs hL hLK
  have key : ∃ n ∈ oddCoreOf (Q3NL.exactLayer3 Ω z), conjSub n L ∈ omegaNbr Ω (F.ρ j).K := by
    rcases hadj with h | h
    · obtain ⟨n, hn, hn'⟩ := Layer.exists_oddCore_conj_omegaNbr3 hLH hKj hLt h
      refine ⟨n⁻¹, (oddCoreOf _).inv_mem hn, ?_⟩
      have h1 := omegaNbr_conj hΩ.conjInvariant hn' n⁻¹
      rwa [conjSub_inv_conjSub] at h1
    · obtain ⟨n, hn, hn'⟩ := Layer.exists_oddCore_conj_omegaNbr3 hLH hLt hKj h
      exact ⟨n, hn, Q3CL.T3.omegaNbr_symm (l6_2) hΩ (hΩ.conjInvariant n L hL.1)
        (F.ρ j).hK hn'⟩
  obtain ⟨n, hn, hn1⟩ := key
  have hncen : n ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [← T8.cenZ_eq_centralizer]
    exact Layer.exactLayer3_le_cenZ Ω z (oddCoreOf_le_self _ hn)
  have hnK : conjSub n K = K :=
    mem_normalizer_iff_conjSub_eq.mp
      (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hs.stand.mem hs.noTwins hs.hz
        hncen)
  have hn2 : conjSub n L ∈ omegaNbr Ω K := by
    have h1 := omegaNbr_conj hΩ.conjInvariant hLnbr n
    rwa [hnK] at h1
  obtain ⟨i, hi0, hij, hLi⟩ :=
    commonNbr_frame_eq hs hdisc hμ hne huni hα F hj hn2 hn1
  refine ⟨i, hi0, hij, ?_⟩
  rw [← Layer.layerImg3_conj_of_mem_oddCore (K := L) hn, hLi]

variable [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AlphaFrame3] in
theorem layerImg_frame_of_path [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (huni : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      ¬ DConnected (Q3T7.layerFam3 Ω (z * s)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) (F : T8YY.FrameData Ω W K J z t)
    {B : Subgroup (Q3T7.layerQuot3 Ω z)}
    (hpath : Relation.ReflTransGen
      (fun A C => C ∈ linkFam (Q3T7.layerFam3 Ω z) (Layer.layerImg3 Ω z K) ∧
        (C ∈ omegaNbr (Q3T7.layerFam3 Ω z) A ∨ A ∈ omegaNbr (Q3T7.layerFam3 Ω z) C))
      (Layer.layerImg3 Ω z (F.ρ 1).K) B) :
    ∃ i : Fin 4, i ≠ 0 ∧ B = Layer.layerImg3 Ω z (F.ρ i).K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hz2 : z * z = 1 := hs.hz.sq
  have hKt : K ∈ Q3NL.tqMembers3 Ω z := (xMem_z_K hs).mem_tqMembers3 hΩ hz2
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) :=
    (Layer.LayerHyp.of_stand3 hs.stand.toStand3 hz2 ⟨K, hKt⟩).hc2
  induction hpath with
  | refl => exact ⟨1, by decide, rfl⟩
  | @tail b c hab hbc ih =>
    obtain ⟨i, hi0, hbi⟩ := ih
    obtain ⟨hcmem, hadj⟩ := hbc
    obtain ⟨L, hL, hLc⟩ := exists_xMem_of_mem_layerFam3 hc2 hcmem.1
    have hLK : L ≠ K := fun h => hcmem.2 (by rw [← hLc, h])
    have hadj' : Layer.layerImg3 Ω z L ∈
        omegaNbr (Q3T7.layerFam3 Ω z) (Layer.layerImg3 Ω z (F.ρ i).K) ∨
        Layer.layerImg3 Ω z (F.ρ i).K ∈ omegaNbr (Q3T7.layerFam3 Ω z) (Layer.layerImg3 Ω z L) := by
      rw [hLc, ← hbi]
      exact hadj
    obtain ⟨i', hi'0, -, himg⟩ :=
      layerImg_nbr_in_frame_z hs hdisc hμ hne huni hα F hi0 hL hLK hadj'
    exact ⟨i', hi'0, by rw [← hLc, himg]⟩

variable [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AlphaFrame3] in
theorem singleFrameFact0_proved : T8YY.SingleFrameFact0 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ hne huni hα F M hM
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hz2 : z * z = 1 := hs.hz.sq
  have hKt : K ∈ Q3NL.tqMembers3 Ω z := (xMem_z_K hs).mem_tqMembers3 hΩ hz2
  have hs3 : Q3.Disc3.AscStand3 Ω K := hs.stand.toStand3
  have hLH : Layer.LayerHyp Ω z := Layer.LayerHyp.of_stand3 hs3 hz2 ⟨K, hKt⟩
  have hne0 : (Q3NL.tqMembers3 Ω z).Nonempty := ⟨K, hKt⟩
  have hΨ : Uniform.HypOmegaModU (.sl2 3 1) (Q3T7.layerFam3 Ω z) :=
    Q3T7.hypOmegaModU_layerFam3 hs3 hLH.hc2 hne0
  have hA := Q3T7.aEmpty_layerFam3 hs3 hLH.hc2 hne0
  have hOX : classicalInvolutionOddCore (Q3T7.layerQuot3 Ω z) = ⊥ :=
    Q3T7.layerQuot3_oddCore_eq_bot
  have hk : ∀ g : Q3T7.layerQuot3 Ω z,
      conjSub g (Layer.layerImg3 Ω z K) = Layer.layerImg3 Ω z K := layerImg_z_normal hs
  have hlt := Q3T7.card_layerQuot3_lt (Ω := Ω) (z_not_central hs)
  let B : Fin 3 → Subgroup (Q3T7.layerQuot3 Ω z) := fun i => Layer.layerImg3 Ω z (F.ρ i.succ).K
  have hBk : ∀ i, B i ∈ linkFam (Q3T7.layerFam3 Ω z) (Layer.layerImg3 Ω z K) := by
    intro i
    refine ⟨Layer.layerImg3_mem ((frame_xMem_z hs F _).mem_tqMembers3 hΩ hz2), ?_⟩
    have h := frame_layerImg_ne_z hs F (Fin.succ_ne_zero i)
    rwa [F.h0] at h
  have hBinj : Function.Injective B := by
    intro i j h
    by_contra hij
    exact frame_layerImg_ne_z hs F (fun h' => hij (Fin.succ_injective _ h')) h
  have hBadj : ∀ i j, i ≠ j → B j ∈ omegaNbr (Q3T7.layerFam3 Ω z) (B i) := fun i j hij =>
    frame_layerImg_nbr_z hs F (fun h' => hij (Fin.succ_injective _ h'))
  rcases link_dichotomy hs.stand.ih hs.stand.below hlt hΨ hA hOX hk B hBk hBinj hBadj with
    hconn | ⟨C, hCmem, hCinj, hCadj⟩
  ·
    have hXM := xMem_z_of_nbr hs hM
    have hMk : Layer.layerImg3 Ω z M ∈ linkFam (Q3T7.layerFam3 Ω z) (Layer.layerImg3 Ω z K) :=
      ⟨Layer.layerImg3_mem (hXM.mem_tqMembers3 hΩ hz2), layerImg_nbr_ne_z hs hM⟩
    have hpath := link_path hLH.quot hk hconn (hBk 0) hMk
    obtain ⟨i, hi0, himg⟩ := layerImg_frame_of_path hs hdisc hμ hne huni hα F hpath
    exact ⟨i, eq_of_layerImg_eq_z hs hμ hne hα F hi0 hXM himg⟩
  ·
    exfalso
    have hC2 : ∀ i, C i = Layer.layerImg3 Ω z (F.ρ 2).K ∨ C i = Layer.layerImg3 Ω z (F.ρ 3).K := by
      intro i
      obtain ⟨L, hL, hLC⟩ := exists_xMem_of_mem_layerFam3 hLH.hc2 (hCmem i).1
      have hLK : L ≠ K := fun h => (hCmem i).2 (by rw [← hLC, h])
      have hadj : Layer.layerImg3 Ω z L ∈
          omegaNbr (Q3T7.layerFam3 Ω z) (Layer.layerImg3 Ω z (F.ρ 1).K) := by
        rw [hLC]
        exact hCadj i
      obtain ⟨i', hi0, hi1, himg⟩ := layerImg_nbr_in_frame_z hs hdisc hμ hne huni hα F
        (j := 1) (by decide) hL hLK (Or.inl hadj)
      rw [← hLC, himg]
      fin_cases i'
      · exact absurd rfl hi0
      · exact absurd rfl hi1
      · exact Or.inl rfl
      · exact Or.inr rfl
    have h0 := hC2 0
    have h1 := hC2 1
    have h2 := hC2 2
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      first
        | exact absurd (hCinj (h0.trans h1.symm)) (by decide)
        | exact absurd (hCinj (h0.trans h2.symm)) (by decide)
        | exact absurd (hCinj (h1.trans h2.symm)) (by decide)
end T8ZZ
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
