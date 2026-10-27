module

public import CFSG.ClassicalInvolution.Balance.TheoremQ
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification
open scoped commutatorElement

section GroupLevel

variable {A Q : Type*} [Group A] [Finite A] [Group Q]

theorem map_commutatorElement_eq_one_of_mem_oddCore (φ : A →* Q) (hφ : Function.Surjective φ)
    (hQ : componentClassificationOddCore Q ≤ Subgroup.center Q) {a : A}
    (ha : a ∈ componentClassificationOddCore A) (b : A) : φ ⁅a, b⁆ = 1 := by
  have hN : ((componentClassificationOddCore A).map φ).Normal :=
    Subgroup.Normal.map (componentClassificationOddCore_normal A) φ hφ
  have hodd : Odd (Nat.card ((componentClassificationOddCore A).map φ)) :=
    (OddCore.odd_card A).of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hφa : φ a ∈ Subgroup.center Q :=
    hQ (OddCore.maximal Q _ hN hodd ⟨a, ha, rfl⟩)
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact ((Subgroup.mem_center_iff.mp hφa) (φ b)).symm

end GroupLevel

section Ambient

variable {G : Type*} [Group G] [Finite G]

theorem commutator_oddCoreIn_le_of_oddCore_map_le_center {X P : Subgroup G} (hPX : P ≤ X)
    (hc : componentClassificationOddCore
        ((P.subgroupOf X).map (QuotientGroup.mk' (componentClassificationOddCore X))) ≤
      Subgroup.center
        ((P.subgroupOf X).map (QuotientGroup.mk' (componentClassificationOddCore X)))) :
    ⁅oddCoreIn P, P⁆ ≤ oddCoreIn X := by
  set OX := componentClassificationOddCore X with hOX
  set π := QuotientGroup.mk' OX with hπ
  set Pb : Subgroup X := P.subgroupOf X with hPb
  let e : Pb ≃* P := Subgroup.subgroupOfEquivOfLe hPX
  let φ : Pb →* ↥(Pb.map π) :=
    (π.domRestrict Pb).codRestrict (Pb.map π) fun x => Subgroup.mem_map_of_mem π x.2
  have hφ : Function.Surjective φ := fun y => by
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  rw [Subgroup.commutator_le]
  rintro _ ⟨a', ha', rfl⟩ b hb
  have hã : e.symm a' ∈ componentClassificationOddCore Pb := by
    have h := OddCore.equiv_invariant e
    have ha'' : a' ∈ Subgroup.map e.toMonoidHom (componentClassificationOddCore Pb) := by
      rw [h]
      exact ha'
    exact Subgroup.mem_map_equiv.mp ha''
  have h1 := map_commutatorElement_eq_one_of_mem_oddCore φ hφ hc hã (e.symm ⟨b, hb⟩)
  have h2 : π (⁅e.symm a', e.symm ⟨b, hb⟩⁆ : Pb).1 = 1 := congrArg Subtype.val h1
  exact ⟨_, (QuotientGroup.eq_one_iff _).mp h2, rfl⟩

theorem commutator_oddCoreIn_le_of_image_isQuasisimple {X P : Subgroup G} (hPX : P ≤ X)
    (hq : CFSG.Open.IsQuasisimple
      ((P.subgroupOf X).map (QuotientGroup.mk' (componentClassificationOddCore X)))) :
    ⁅oddCoreIn P, P⁆ ≤ oddCoreIn X := by
  have : Finite ↥((P.subgroupOf X).map (QuotientGroup.mk' (componentClassificationOddCore X))) :=
    inferInstance
  exact commutator_oddCoreIn_le_of_oddCore_map_le_center hPX
    (oddCore_le_center_of_isQuasisimple hq)

theorem commutator_oddCoreIn_normalClosureIn_le_of_le {H L P : Subgroup G} {Y : Subgroup G}
    (hLP : normalClosureIn H L ≤ P) (hPH : P ≤ H)
    (h : ⁅oddCoreIn P, P⁆ ≤ Y) :
    ⁅oddCoreIn (normalClosureIn H L), normalClosureIn H L⁆ ≤ Y := by
  have hsub : IsSubnormal (normalClosureIn H L) P := by
    refine isSubnormal_of_normal_subgroupOf hLP ?_
    rw [Subgroup.normal_subgroupOf_iff hLP]
    intro x p hx hp
    exact conj_mem_normalClosureIn (hPH hp) hx
  exact (Subgroup.commutator_mono (oddCoreIn_le_of_isSubnormal hsub) hLP).trans h

theorem commutator_oddCoreIn_normalClosureIn_le_of_normalized {H L M Y : Subgroup G}
    (hLM : L ≤ M) (hMH : M ≤ H) (hnorm : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M)
    (h : ⁅oddCoreIn M, M⁆ ≤ Y) :
    ⁅oddCoreIn (normalClosureIn H L), normalClosureIn H L⁆ ≤ Y := by
  refine commutator_oddCoreIn_normalClosureIn_le_of_le (P := M) ?_ hMH h
  refine normalClosureIn_le fun g hg => ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hnorm g hg x (hLM hx)

theorem isQuasisimple_of_deltaTrivial_of_image {C K E₀ L₀ : Subgroup G}
    (hKC : IsSubnormal K C) (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hE₀K : E₀ ≤ K) (hE₀ : IsElemAbelian 2 E₀) (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hB : ∀ f ∈ E₀, f ≠ 1 → ∃ P : Subgroup G,
      normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀ ≤ P ∧ P ≤ C ⊓ Subgroup.centralizer {f} ∧
        componentClassificationOddCore ((P.subgroupOf (Subgroup.centralizer {f})).map
            (QuotientGroup.mk' (componentClassificationOddCore (Subgroup.centralizer {f})))) ≤
          Subgroup.center ((P.subgroupOf (Subgroup.centralizer {f})).map
            (QuotientGroup.mk' (componentClassificationOddCore (Subgroup.centralizer {f}))))) :
    CFSG.Open.IsQuasisimple K := by
  refine isQuasisimple_of_deltaTrivial hKC hKperf hKq hE₀K hE₀ hE₀card hL₀K hL₀E hL₀ hL₀ne hΔ
    fun f hf hf1 => ?_
  obtain ⟨P, hLP, hPH, hc⟩ := hB f hf hf1
  exact commutator_oddCoreIn_normalClosureIn_le_of_le hLP hPH
    (commutator_oddCoreIn_le_of_oddCore_map_le_center (hPH.trans inf_le_right) hc)

theorem isQuasisimple_of_isTwoComponent_of_deltaTrivial {C K E₀ L₀ : Subgroup G}
    (hKC : K ≤ C) (hK : TwoComponents.IsTwoComponent (K.subgroupOf C))
    (hE₀K : E₀ ≤ K) (hE₀ : IsElemAbelian 2 E₀) (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤) (hL₀ne : L₀ ≠ ⊥)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hB : ∀ f ∈ E₀, f ≠ 1 →
      ⁅oddCoreIn (normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀),
        normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀⁆ ≤ involutionOddCore f) :
    CFSG.Open.IsQuasisimple K := by
  let e : (K.subgroupOf C) ≃* K := Subgroup.subgroupOfEquivOfLe hKC
  have hKsub : IsSubnormal K C := CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff
    hKC |>.mp hK.1
  have hKperf : commutator K = ⊤ := by
    have : Group.IsPerfect (K.subgroupOf C) := ⟨TwoComponents.perfect hK⟩
    have : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K) := by
    have h := OddCore.equiv_invariant e
    exact Components.quasisimple_of_equiv
      (QuotientGroup.congr (componentClassificationOddCore (K.subgroupOf C))
        (componentClassificationOddCore K) e h).symm (TwoComponents.quasisimple_quotient hK)
  exact isQuasisimple_of_deltaTrivial hKsub hKperf hKq hE₀K hE₀ hE₀card hL₀K hL₀E hL₀ hL₀ne hΔ hB

end Ambient

end CFSG.ClassicalInvolution.Balance
