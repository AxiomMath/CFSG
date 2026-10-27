module

public import CFSG.CGT.PushingUpLit.T2K.Sylow
public import CFSG.CGT.PushingUpLit.BHS7.OffenderBlock
public import CFSG.CGT.PushingUpLit.T2K.FourTwo

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M T A : Subgroup G} {n : ℕ}

namespace NatBlock

theorem isNatBy (h : NatBlock L n) :
    IsNatBy (fun (s : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (m : Multiplicative (Fin 2 → GaloisField 2 n)) =>
        Multiplicative.ofAdd ((s : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
          (Multiplicative.toAdd m))) L (blockU L) := by
  let D := h.natData
  refine ⟨D.φ, D.ψ, D.φ_surj, ?_, D.ψ_surj, ?_, D.ψ_conj⟩
  · ext l
    rw [MonoidHom.mem_ker, D.φ_ker, Subgroup.mem_subgroupOf, h.inf_centralizer_blockU]
  · ext v
    rw [MonoidHom.mem_ker, D.ψ_ker, Subgroup.mem_subgroupOf]
    rfl

theorem commutator_left_eq (h : NatBlock L n) : ⁅L, blockU L⁆ = blockU L := by
  rw [Subgroup.commutator_comm]
  exact h.blockU_eq

theorem le_centralizer_of_comm_autOn (h : NatBlock L n) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hAM : A ≤ M) (hAe : IsElemAbelian 2 A)
    (h0 : ⁅autOn L (blockU L), autOn A (blockU L)⁆ = ⊥) :
    A ≤ Subgroup.centralizer (blockU L : Set G) := by
  have hLV : L ≤ Subgroup.normalizer (blockU L : Set G) :=
    le_normalizer_blockU L
  have hAV : A ≤ Subgroup.normalizer (blockU L : Set G) :=
    hAM.trans (le_normalizer_blockU_of_le hMN)
  intro a ha
  have haN : a ∈ Subgroup.normalizer (L : Set G) := hMN (hAM ha)
  have hLa := commutator_mem_centralizer_of_commutator_autOn_eq_bot hLV hAV h0
  have hc : ∀ l ∈ L, ⁅a, l⁆ ∈ oTwoIn L := by
    intro l hl
    have h1 : ⁅a, l⁆ ∈ Subgroup.centralizer (blockU L : Set G) := by
      have := (Subgroup.centralizer (blockU L : Set G)).inv_mem (hLa l hl a ha)
      rwa [commutatorElement_inv] at this
    have h2 : ⁅a, l⁆ ∈ L := by
      have e : ⁅a, l⁆ = (a * l * a⁻¹) * l⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact L.mul_mem ((Subgroup.mem_normalizer_iff.1 haN l).1 hl) (L.inv_mem hl)
    rw [← h.inf_centralizer_blockU]
    exact ⟨h2, h1⟩
  have hsq : a ^ 2 = 1 := hAe.2 a ha
  exact h.centralizes_of_pow haN hc (k := 1) (fun v _ => by simp [hsq])

theorem offender_of_isOffG (h : NatBlock L n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) (hAM : A ≤ M) (hAe : IsElemAbelian 2 A)
    (hOff : IsOffG (blockU L) A) (hAV : ¬ A ≤ Subgroup.centralizer (blockU L : Set G)) :
    (A ⊓ Subgroup.centralizer (blockU L : Set G)).relIndex A = 2 ^ n ∧
      (blockU L ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU L) = 2 ^ n ∧
      ∀ a ∈ A, ∃ l ∈ L, ∀ v ∈ blockU L, a * v * a⁻¹ = l * v * l⁻¹ := by
  classical
  set V : Subgroup G := blockU L with hVdef
  have hVe : IsElemAbelian 2 V := h.isElemAbelian_blockU
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := le_normalizer_blockU_of_le hMN
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hLM.trans hMV
  have hAN' : A ≤ Subgroup.normalizer (V : Set G) := hAM.trans hMV
  have hOffA : @IsOff ↥V (commGroupOfElemAbelian hVe) (autOn A V) :=
    (isOffG_iff_isOff_autOn hVe hAN').mp hOff
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hVe.2 v v.2)
  have hLVeq : (⁅L, V⁆ : Subgroup G) = V := h.commutator_left_eq
  have hLVV : (⁅L, V⁆ : Subgroup G) ≤ V := le_of_eq hLVeq
  have hVL : V ≤ (⁅L, V⁆ : Subgroup G) := hLVeq.ge
  have hnat : IsSLNatSection (autOn L V) (commOn hVe L) (commOn hVe L ⊓ fixOn hVe L) n := by
    refine isNatSectionBy_autOn hVe hLV h.isNatBy hLVV
      (fun w hw => ⟨w, hVL hw, 1, one_mem _, by simp⟩) rfl
  have hcomm : ⁅autOn L V, autOn A V⁆ ≠ ⊥ := fun h0 =>
    hAV (h.le_centralizer_of_comm_autOn hMN hAM hAe h0)
  have hsub : IsSubnormal (autOn L V) (autOn M V) := by
    refine autOn_isSubnormal ?_
    refine IsSubnormal.step hLM ?_ (IsSubnormal.refl M)
    exact Subgroup.normal_subgroupOf_of_le_normalizer hMN
  have hres := two_sixteen_sl hV2 h.two_le hOffA (autOn_le_autOn V hAM) (autOn_le_autOn V hLM)
    hsub hnat hcomm
  obtain ⟨hAN, hAL, hcard, -, hrel⟩ := hres
  have hW : commOn hVe L = (⁅L, V⁆ : Subgroup G).subgroupOf V := commOn_eq hVe hLV
  have hAst : autOn A V ≤ stabSub (commOn hVe L) := hAN.trans (normalizer_commV_le_stabSub _)
  have hAL' : autSub (autOn A V) (commOn hVe L) ≤ autSub (autOn L V) (commOn hVe L) := hAL
  have hcard' : Nat.card ↥(autSub (autOn A V) (commOn hVe L)) = 2 ^ n := hcard
  have hrel' : (fixV (autOn A V)).relIndex (commOn hVe L) =
      (cenIn (autOn A V) (commOn hVe L)).relIndex (autOn A V) := hrel
  have hc1 : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A = 2 ^ n := by
    have h1 := card_autSub_eq_relIndex hAst
    rw [hcard'] at h1
    rw [hW, relIndex_cenIn_autOn hVe hAN' hLVV, hLVeq] at h1
    exact h1.symm
  refine ⟨hc1, ?_, ?_⟩
  · rw [hW, relIndex_fixV_autOn hVe hAN' hLVV, relIndex_cenIn_autOn hVe hAN' hLVV, hLVeq]
      at hrel'
    rw [← hc1]
    exact hrel'
  · intro a ha
    have hga : conjAct V ⟨a, hAN' ha⟩ ∈ autOn A V := mem_autOn_iff.mpr ⟨⟨a, hAN' ha⟩, ha, rfl⟩
    obtain ⟨g, hgE, hgres⟩ := mem_autSub.1 (hAL' (mem_autSub.2 ⟨⟨_, hAst hga⟩, hga, rfl⟩))
    obtain ⟨l', hlL, hl⟩ := mem_autOn_iff.mp hgE
    refine ⟨(l' : G), hlL, fun v hv => ?_⟩
    have hvW : (⟨v, hv⟩ : ↥V) ∈ commOn hVe L := by
      rw [hW, Subgroup.mem_subgroupOf]
      exact hVL hv
    have h2 : ((resHom (commOn hVe L) g ⟨⟨v, hv⟩, hvW⟩ : ↥(commOn hVe L)) : ↥V) =
        ((resHom (commOn hVe L) ⟨conjAct V ⟨a, hAN' ha⟩, hAst hga⟩ ⟨⟨v, hv⟩, hvW⟩ :
          ↥(commOn hVe L)) : ↥V) := by rw [hgres]
    have h3 : ((g : MulAut ↥V) ⟨v, hv⟩ : ↥V) =
        ((conjAct V ⟨a, hAN' ha⟩ : MulAut ↥V) ⟨v, hv⟩ : ↥V) := h2
    rw [← hl] at h3
    have h4 := congrArg (fun x : ↥V => (x : G)) h3
    simp only [conjAct_apply'] at h4
    exact h4.symm

theorem offender (h : NatBlock L n) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hA : IsMaxElemAbelian T A)
    (hAV : ¬ A ≤ Subgroup.centralizer (blockU L : Set G)) :
    (A ⊓ Subgroup.centralizer (blockU L : Set G)).relIndex A = 2 ^ n ∧
      (blockU L ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU L) = 2 ^ n ∧
      ∀ a ∈ A, ∃ l ∈ L, ∀ v ∈ blockU L, a * v * a⁻¹ = l * v * l⁻¹ := by
  have hVT : blockU L ≤ T := blockU_le_sylow hLM hMN hT
  have hAM : A ≤ M := hA.1.trans hT.le
  have hMV : M ≤ Subgroup.normalizer (blockU L : Set G) := le_normalizer_blockU_of_le hMN
  exact h.offender_of_isOffG hLM hMN hAM hA.2.1
    (isOffG_of_isMaxElemAbelian h.isElemAbelian_blockU hVT (hT.le.trans hMV) hA hAV) hAV

end NatBlock

end CFSG.CGT.PushingUpLit.T2K
