module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrG
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrKL
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrSAlpha
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrSGlobal
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrSP

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3

open scoped commutatorElement

section Frame

variable {G : Type} [Group G] [Finite G] {K J : Subgroup G} {z t a g : G}

theorem FrameIIHyp.nbrTwin_of_alpha_eq_bot (h : FrameIIHyp K J z t a g)
    (hα : ∀ M ∈ CoreAssembly.conjClass K, ∀ (J' : Subgroup G) (zM zJ : G),
      AViol (CoreAssembly.conjClass K) M J' zM zJ →
        alphaOf (Subgroup.closure ({zM, zJ} : Set G)) = ⊥) :
    ∀ L ∈ omegaNbr (CoreAssembly.conjClass K) K, L ∈ twinSet (CoreAssembly.conjClass K) K := by
  refine omegaNbr_twin_of_transfer h fun M hM J' zM zJ hv =>
    omegaOfSet_subset_of_kl h.hyp hM hv fun N hN o ho => ?_
  have hzN : IsUniqueInvolution N zM := isUniqueInvolution_of_mem_twinSet hv.hzK hN
  have hO : o ∈ oddCoreOf (Subgroup.centralizer ({zM} : Set G)) :=
    Balance.oddCoreIn_le_of_isSubnormal (h.cls.isSubnormal_of_uniqueInvolution hN.1 hzN) ho
  have hzMZ : zM ∈ Subgroup.closure ({zM, zJ} : Set G) := Subgroup.subset_closure (by simp)
  have hzJZ : zJ ∈ Subgroup.closure ({zM, zJ} : Set G) := Subgroup.subset_closure (by simp)
  have hcomm : ⁅o, zJ⁆ ∈ alphaOf (Subgroup.closure ({zM, zJ} : Set G)) := by
    refine Subgroup.mem_sup_left ?_
    exact Subgroup.mem_iSup_of_mem zM (Subgroup.mem_iSup_of_mem hzMZ
      (Subgroup.mem_iSup_of_mem hv.hzK.ne_one (Subgroup.commutator_mem_commutator hO hzJZ)))
  rw [hα M hM J' zM zJ hv, Subgroup.mem_bot] at hcomm
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm

theorem FrameIIHyp.oddProd_le_oddCore_centralizer (h : FrameIIHyp K J z t a g) :
    oddCoreOf K ⊔ oddCoreOf (conjSub a J) ≤
      oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
  have d := h.twin_facts
  exact sup_le (Balance.oddCoreIn_le_of_isSubnormal (h.cls.isSubnormal_of_uniqueInvolution d.mem d.hz))
    (Balance.oddCoreIn_le_of_isSubnormal (h.cls.isSubnormal_of_uniqueInvolution d.mem' d.hz'))

theorem FrameIIHyp.exists_oddProd_conj_centralized (h : FrameIIHyp K J z t a g) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hTK' : T ≤ Subgroup.normalizer ((conjSub a J : Subgroup G) : Set G))
    (hcK : ∀ x ∈ T, ∀ m ∈ K, ⁅x, m⁆ ∈ oddCoreOf K)
    (hcK' : ∀ x ∈ T, ∀ m ∈ conjSub a J, ⁅x, m⁆ ∈ oddCoreOf (conjSub a J))
    {u : G} (hu : u ∈ K ⊔ conjSub a J) (hu2 : u * u = 1) :
    ∃ q ∈ oddCoreOf K ⊔ oddCoreOf (conjSub a J),
      T ≤ Subgroup.centralizer ({q * u * q⁻¹} : Set G) := by
  have d := h.twin_facts
  have hTN : T ≤ Subgroup.normalizer ((K ⊔ conjSub a J : Subgroup G) : Set G) :=
    fun x hx => T3CII.mem_normalizer_sup (hTK hx) (hTK' hx)
  obtain ⟨P, hP, hTP₀⟩ := Asc77.exists_sylow_normalized hT2 hTN
  have hTP : ∀ x ∈ T, x ∈ Subgroup.normalizer (P : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hTP₀ x hx)
  have hcN := commutator_mem_oddCore_sup d.K'_le d.K_le hcK hcK'
  have hTPc : ∀ x ∈ T, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have h1 : ⁅x, y⁆ ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTP x hx) y).mp hy) (P.inv_mem hy)
    have h2 : ⁅x, y⁆ ∈ oddCoreOf (K ⊔ conjSub a J) := hcN x hx y (hP.1 hy)
    have h3 : ⁅x, y⁆ = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) h2
      (hP.2.1.to_le (Subgroup.zpowers_le.mpr h1))
    exact commutatorElement_eq_one_iff_mul_comm.mp h3
  obtain ⟨P₁, hP₁, huP₁⟩ := IsSylow2In.exists_ge (P := K ⊔ conjSub a J)
    (ExactLayer.isPGroup_zpowers_of_sq_eq_one hu2) (Subgroup.zpowers_le.mpr hu)
  obtain ⟨o, ho, hoP⟩ := d.exists_conj_oddProd hP₁ hP
  have huP : o⁻¹ * u * o ∈ P := by
    have h1 : u ∈ conjSub o P := hoP ▸ huP₁ (Subgroup.mem_zpowers u)
    exact mem_conjSub_iff.mp h1
  refine ⟨o⁻¹, Subgroup.inv_mem _ ho, fun x hx => ?_⟩
  rw [inv_inv]
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hTPc x hx _ huP)

end Frame

section Defs


@[expose] def FrameHyp51L : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameCore G] (K J : Subgroup G) (z t a g : G),
    FrameIIHyp K J z t a g → Thm3A.Thm3RBelowG (Nat.card G) → CIT3Below (Nat.card G) →
    TL4.TightBelowRPlus 3 (Nat.card G) →
    ∀ (L T : Subgroup G) (ℓ : G), L ∈ omegaNbr (CoreAssembly.conjClass K) K →
      L ∉ twinSet (CoreAssembly.conjClass K) K → IsSylow2In T L →
      T ≤ Subgroup.normalizer (K : Set G) → IsUniqueInvolution L ℓ →
      ∀ (J₁ : Subgroup G) (u : G), AViol (CoreAssembly.conjClass K) K J₁ z u →
        T ≤ Subgroup.centralizer ({u} : Set G) →
          Hyp51 (Subgroup.closure ({z, u, ℓ} : Set G))

theorem frameNbrTwinSG_of_hyp51L (hL51 : FrameHyp51L) : FrameNbrTwinSG := by
  intro G _ _ _ hT hcit hP K J z t a g h L hL
  by_contra hLtw
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K) := h.hyp
  have d := h.twin_facts
  have hLΩ : L ∈ CoreAssembly.conjClass K := hL.1
  obtain ⟨-, hLK, T, hTR, hTL, hTN⟩ := id hL
  have hTsyl : IsSylow2In T L := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hLΩ hTR hTL
  have hT2 : IsPGroup 2 T := hTsyl.2.1
  have h8 : 8 ≤ Nat.card T := Sec6Gen.eight_le_of_mem_RSet hΩ hTR
  obtain ⟨ℓ, hℓ⟩ := Sec6Gen.exists_uniqueInvolution hΩ hLΩ
  have hK'tw : conjSub a J ∈ twinSet (CoreAssembly.conjClass K) K := by
    rw [d.twins]; exact Or.inr rfl
  have hLK' : L ≠ conjSub a J := fun e => hLtw (e ▸ hK'tw)
  have hTC : T ≤ Subgroup.centralizer ({z} : Set G) :=
    Sec6Gen.le_centralizer_of_le_normalizer' d.hz hTN
  have hTK' : T ≤ Subgroup.normalizer ((conjSub a J : Subgroup G) : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ d.mem' hLΩ hLK'.symm d.hz' hTL hT2 (by omega) hTC
  have hcK : ∀ x ∈ T, ∀ m ∈ K, ⁅x, m⁆ ∈ oddCoreOf K := fun x hx m hm =>
    Q3CL.Thompson.comm_le_oddCore_of_isSylow2In Sec6Gen.l6_2Gen hΩ d.mem hLΩ hLK.symm
      d.hz hℓ hTsyl hTC (Subgroup.commutator_mem_commutator hx hm)
  have hcK' : ∀ x ∈ T, ∀ m ∈ conjSub a J, ⁅x, m⁆ ∈ oddCoreOf (conjSub a J) := fun x hx m hm =>
    Q3CL.Thompson.comm_le_oddCore_of_isSylow2In Sec6Gen.l6_2Gen hΩ d.mem' hLΩ hLK'.symm
      d.hz' hℓ hTsyl hTC (Subgroup.commutator_mem_commutator hx hm)
  have hℓz : ℓ ≠ z := by
    rintro rfl
    exact hLtw ⟨hLΩ, ℓ, d.hz, hℓ⟩
  have hℓ1 : ℓ ≠ 1 := hℓ.ne_one
  have hz1 : z ≠ 1 := d.hz.ne_one
  have key : ∀ (J₁ : Subgroup G) (u : G), AViol (CoreAssembly.conjClass K) K J₁ z u →
      alphaOf (Subgroup.closure ({z, u} : Set G)) = alphaOf (Subgroup.closure ({z, ℓ} : Set G)) ∧
        Odd (Nat.card ↥(alphaOf (Subgroup.closure ({z, ℓ} : Set G)))) := by
    intro J₁ u hv
    obtain ⟨huK, hu2, hu1, huz, -⟩ := d.isAInv_facts ⟨J₁, hv⟩
    obtain ⟨q, hq, hTq⟩ := h.exists_oddProd_conj_centralized hT2 hTN hTK' hcK hcK' huK hu2
    have hqN : q ∈ Subgroup.normalizer (K : Set G) :=
      d.sup_le_normalizer_left (oddProd_le_sup K (conjSub a J) hq)
    obtain ⟨J₂, hv₂⟩ : IsAInv (CoreAssembly.conjClass K) K z (q * u * q⁻¹) :=
      IsAInv.conj_of_mem_normalizer hΩ.conjInvariant ⟨J₁, hv⟩ hqN
    have hqz : q * z * q⁻¹ = z := d.hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hqN)
    obtain ⟨-, -, hu'1, hu'z, -⟩ := d.isAInv_facts ⟨J₂, hv₂⟩
    have hB := hL51 G K J z t a g h hT hcit hP L T ℓ hL hLtw hTsyl hTN hℓ J₂ (q * u * q⁻¹)
      hv₂ hTq
    have hzB : z ∈ Subgroup.closure ({z, q * u * q⁻¹, ℓ} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hu'B : q * u * q⁻¹ ∈ Subgroup.closure ({z, q * u * q⁻¹, ℓ} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hℓB : ℓ ∈ Subgroup.closure ({z, q * u * q⁻¹, ℓ} : Set G) :=
      Subgroup.subset_closure (by simp)
    have he : alphaOf (Subgroup.closure ({z, q * u * q⁻¹} : Set G)) =
        alphaOf (Subgroup.closure ({z, ℓ} : Set G)) :=
      alphaOf_pair_eq_of_hyp51_of_mem hB hzB hz1 hu'B hu'1 hu'z hℓB hℓ1 hℓz
    have hzℓ4 : IsElemAbelian2 (Subgroup.closure ({z, ℓ} : Set G)) 2 :=
      isElemAbelian2_closure_pair_of_mem hB.1 hzB hℓB hz1 hℓ1 hℓz.symm
    have hzℓB : Subgroup.closure ({z, ℓ} : Set G) ≤
        Subgroup.closure ({z, q * u * q⁻¹, ℓ} : Set G) := closure_pair_le_of_mem hzB hℓB
    have hqO : q ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) :=
      h.oddProd_le_oddCore_centralizer hq
    have hfix : conjSub q (alphaOf (Subgroup.closure ({z, ℓ} : Set G))) =
        alphaOf (Subgroup.closure ({z, ℓ} : Set G)) :=
      conjSub_alphaOf_eq_of_mem_oddCore hB hzB hzℓB hzℓ4 hqO
    have hconj : alphaOf (Subgroup.closure ({z, q * u * q⁻¹} : Set G)) =
        conjSub q (alphaOf (Subgroup.closure ({z, u} : Set G))) := by
      rw [← alphaOf_closure_pair_conj, hqz]
    refine ⟨?_, odd_alphaOf_of_hyp51 hB hzℓB hzℓ4⟩
    have h1 : conjSub q (alphaOf (Subgroup.closure ({z, u} : Set G))) =
        conjSub q (alphaOf (Subgroup.closure ({z, ℓ} : Set G))) := by
      rw [← hconj, he, hfix]
    exact conjSub_injective q h1
  have hconst : ∀ (J₁ J₂ : Subgroup G) (u₁ u₂ : G),
      AViol (CoreAssembly.conjClass K) K J₁ z u₁ → AViol (CoreAssembly.conjClass K) K J₂ z u₂ →
        alphaOf (Subgroup.closure ({z, u₁} : Set G)) =
          alphaOf (Subgroup.closure ({z, u₂} : Set G)) :=
    fun J₁ J₂ u₁ u₂ h₁ h₂ => (key J₁ u₁ h₁).1.trans (key J₂ u₂ h₂).1.symm
  have hodd : Odd (Nat.card ↥(alphaOf (Subgroup.closure ({z, t} : Set G)))) := by
    rw [(key J t h.viol).1]
    exact (key J t h.viol).2
  exact hLtw (h.nbrTwin_of_alpha_eq_bot (h.alphaOf_eq_bot_of_const hconst hodd) L hL)

end Defs

section Assembly


theorem frameCaseIITG_of_hyp51L (hL51 : FrameHyp51L) : FrameCaseIITG :=
  frameCaseIITG_of_nbrTwinG (frameNbrTwinSG_of_hyp51L hL51)

end Assembly

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
