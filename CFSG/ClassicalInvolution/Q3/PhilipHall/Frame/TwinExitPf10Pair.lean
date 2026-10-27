module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Map
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TightFamily
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinOddCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame


section Pair

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem exists_lifted_pair_Y {n : ℕ} (hcit : CIT3Below n) (hΦ : HypOmegaGen Φ)
    (h2 : ∀ J ∈ Φ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J))
    (hq8 : ∀ J ∈ Φ, ∀ P : Subgroup X, IsSylow2In P J → Nonempty (↥P ≃* QuaternionGroup 2))
    (hlt : Nat.card X < n) (hO : classicalInvolutionOddCore X = ⊥)
    {J₁ J₂ : Subgroup X} (h₁ : J₁ ∈ Φ) (h₂ : J₂ ∈ Φ) (hne : J₁ ≠ J₂) {u : X}
    (hu₁ : IsUniqueInvolution J₁ u) (hu₂ : IsUniqueInvolution J₂ u)
    (hl₁ : ∃ L : Subgroup X, IsLiftOf J₁ L u) (hl₂ : ∃ L : Subgroup X, IsLiftOf J₂ L u)
    (σ : X ≃* X) (hσΦ : ∀ K ∈ Φ, K.map σ.toMonoidHom ∈ Φ)
    (hσ₁ : IsPGroup 2 J₁ → ∀ j ∈ J₁, σ j = j) (hσ₂ : IsPGroup 2 J₂ → ∀ j ∈ J₂, σ j = j) :
    IsPGroup 2 J₁ ∧ IsPGroup 2 J₂ ∧
      ∃ L₁ L₂ : Subgroup X, IsClassicalMember3 L₁ u ∧ IsClassicalMember3 L₂ u ∧ J₁ ≤ L₁ ∧
        J₂ ≤ L₂ ∧ L₁ ≠ L₂ ∧ (∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) ∧ (∀ l ∈ L₁, σ l = l) ∧
          (∀ l ∈ L₂, σ l = l) := by
  classical
  obtain ⟨L₁, hL₁⟩ := hl₁
  obtain ⟨L₂, hL₂⟩ := hl₂
  have hm₁ := satU_mem_liftFam h₁ hL₁
  have hm₂ := satU_mem_liftFam h₂ hL₂
  have hne' : (liftFam Φ).Nonempty := ⟨_, hm₁⟩
  set Y' : Subgroup X := omegaGen (liftFam Φ) with hY'
  haveI hYn : Y'.Normal := omegaGen_normal (conjInvariant_liftFam hΦ.conjInvariant)
  have hYsub : IsSubnormal Y' ⊤ := isSubnormal_of_normal_subgroupOf le_top inferInstance
  have hL₁Y : L₁ ≤ Y' := le_satU.trans (le_omegaGen hm₁)
  have hL₂Y : L₂ ≤ Y' := le_satU.trans (le_omegaGen hm₂)
  have hJ₁Y : J₁ ≤ Y' := hL₁.le.trans hL₁Y
  have hJ₂Y : J₂ ≤ Y' := hL₂.le.trans hL₂Y
  have huY : u ∈ Y' := hJ₁Y hu₁.mem
  set u' : ↥Y' := ⟨u, huY⟩ with hu'
  have hexu : oddCoreIn (Subgroup.centralizer ({u'} : Set ↥Y')) = ⊥ :=
    oddCent_bot_of_liftFam' hcit hΦ hlt hO hne' rfl u' (Subtype.ext hu₁.sq)
  have hΦZ : HypOmegaGen (restrictFamily Φ Y') := hypOmegaGen_restrict hΦ Y'
  have hmem₁ : J₁.subgroupOf Y' ∈ restrictFamily Φ Y' := ⟨J₁, h₁, hJ₁Y, rfl⟩
  have hmem₂ : J₂.subgroupOf Y' ∈ restrictFamily Φ Y' := ⟨J₂, h₂, hJ₂Y, rfl⟩
  have htwo : ∀ K ∈ restrictFamily Φ Y', IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K) := by
    rintro _ ⟨J, hJ, -, rfl⟩
    exact isPGroup_two_quotient_subgroupOf J Y' (h2 J hJ)
  have hu₁' := Asc77.isUniqueInvolution_subgroupOf hu₁ hJ₁Y
  have hu₂' := Asc77.isUniqueInvolution_subgroupOf hu₂ hJ₂Y
  have hP₁' : IsPGroup 2 ↥(J₁.subgroupOf Y') :=
    isPGroup_of_oddCent hΦZ hmem₁ hu₁' hexu (htwo _ hmem₁)
  have hP₂' : IsPGroup 2 ↥(J₂.subgroupOf Y') :=
    isPGroup_of_oddCent hΦZ hmem₂ hu₂' hexu (htwo _ hmem₂)
  have hP₁ : IsPGroup 2 ↥J₁ := hP₁'.of_equiv (Subgroup.subgroupOfEquivOfLe hJ₁Y)
  have hP₂ : IsPGroup 2 ↥J₂ := hP₂'.of_equiv (Subgroup.subgroupOfEquivOfLe hJ₂Y)
  refine ⟨hP₁, hP₂, ?_⟩
  have hq : ∀ {J : Subgroup X} (hJ : J ∈ Φ) (hJY : J ≤ Y') (hP : IsPGroup 2 ↥J),
      Nonempty (↥(J.subgroupOf Y') ≃* QuaternionGroup 2) := by
    intro J hJ hJY hP
    have hKS : IsSylow2In J J := ⟨le_rfl, hP, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
    obtain ⟨e⟩ := hq8 J hJ J hKS
    exact ⟨(Subgroup.subgroupOfEquivOfLe hJY).trans e⟩
  have hlift : ∀ {J L : Subgroup X}, IsLiftOf J L u → L ≤ Y' → J ≤ Y' →
      IsLiftOf (J.subgroupOf Y') (L.subgroupOf Y') u' := by
    intro J L hL hLY hJY
    exact ⟨Asc77.isUniqueInvolution_subgroupOf hL.inv hJY, fun x hx => Subgroup.mem_subgroupOf.mpr (hL.le (Subgroup.mem_subgroupOf.mp hx)),
      hL.member.subgroupOf hLY⟩
  have hmap : Y'.map σ.toMonoidHom = Y' := map_omegaGen_liftFam σ hσΦ
  let σ' : ↥Y' ≃* ↥Y' := (σ.subgroupMap Y').trans (MulEquiv.subgroupCongr hmap)
  have hσ' : ∀ y : ↥Y', ((σ' y : ↥Y') : X) = σ (y : X) := fun y => rfl
  have hfix₁ : ∀ j ∈ J₁.subgroupOf Y', σ' j = j := fun j hj =>
    Subtype.ext (by rw [hσ']; exact hσ₁ hP₁ _ (Subgroup.mem_subgroupOf.mp hj))
  have hfix₂ : ∀ j ∈ J₂.subgroupOf Y', σ' j = j := fun j hj =>
    Subtype.ext (by rw [hσ']; exact hσ₂ hP₂ _ (Subgroup.mem_subgroupOf.mp hj))
  have hne'' : J₁.subgroupOf Y' ≠ J₂.subgroupOf Y' := by
    intro h
    apply hne
    have := congrArg (Subgroup.map Y'.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hJ₁Y, Subgroup.map_subgroupOf_eq_of_le hJ₂Y] at this
  obtain ⟨M₁, M₂, hM₁, hM₂, hJM₁, hJM₂, hMne, hcomm, hfM₁, hfM₂⟩ :=
    TwinExitPf6.exists_lifted_pair hΦZ hmem₁ hmem₂ hP₁' hP₂' (hq h₁ hJ₁Y hP₁) (hq h₂ hJ₂Y hP₂)
      hu₁' hu₂' ⟨_, hlift hL₁ hL₁Y hJ₁Y⟩ ⟨_, hlift hL₂ hL₂Y hJ₂Y⟩ hexu hne'' σ' hfix₁ hfix₂
  refine ⟨M₁.map Y'.subtype, M₂.map Y'.subtype, isClassicalMember3_map_subnormal hYsub hM₁,
    isClassicalMember3_map_subnormal hYsub hM₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have : j ∈ (J₁.subgroupOf Y').map Y'.subtype := by
      rw [Subgroup.map_subgroupOf_eq_of_le hJ₁Y]; exact hj
    obtain ⟨j', hj', rfl⟩ := this
    exact ⟨j', hJM₁ hj', rfl⟩
  · intro j hj
    have : j ∈ (J₂.subgroupOf Y').map Y'.subtype := by
      rw [Subgroup.map_subgroupOf_eq_of_le hJ₂Y]; exact hj
    obtain ⟨j', hj', rfl⟩ := this
    exact ⟨j', hJM₂ hj', rfl⟩
  · intro h
    exact hMne (Subgroup.map_injective Y'.subtype_injective h)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hcomm a ha b hb)
  · rintro _ ⟨a, ha, rfl⟩
    exact (hσ' a).symm.trans (congrArg Subtype.val (hfM₁ a ha))
  · rintro _ ⟨a, ha, rfl⟩
    exact (hσ' a).symm.trans (congrArg Subtype.val (hfM₂ a ha))

end Pair

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10
