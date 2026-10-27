module

public import CFSG.GH74.GLS.C3.Layer1.Thm1Normal
public import CFSG.GH74.GLS.C3.Layer1.St1P14Uniq
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1A7

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1

section Loc

variable {G : Type} [Group G] [Finite G] {x y : G} {K : Subgroup G}

theorem normal_of_rank_le_one (hrk : pRank 2 ↥(CxK x K) ≤ 1) (h𝒰 : Is2TerminalU2Triple x y K)
    (hshape : HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
  intro c hc k hk
  by_contra hkc
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := h𝒰.1.1.2
  have hK' : IsPCompIn 2 (centralizer ({x} : Set G)) (K.map (MulAut.conj c).toMonoidHom) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hK c
    rwa [map_conj_eq_self_of_mem hc] at this
  have hne : K.map (MulAut.conj c).toMonoidHom ≠ K := by
    intro h
    apply hkc
    have hmem : c * k * c⁻¹ ∈ K.map (MulAut.conj c).toMonoidHom :=
      ⟨k, hk, by simp [MulAut.conj_apply]⟩
    rwa [h] at hmem
  have hle : K.map (MulAut.conj c).toMonoidHom ≤ CxK x K :=
    le_inf hK'.1 (Stage1.Thm2.Recip.le_cSec_of_ne hK' hK hne)
  obtain ⟨u, hu, v, hv, hu2, hv2, huv, hcomm⟩ :=
    U1a.exists_commuting_involutions (D := K) (two_le_pRank_of_shape hshape)
  have hord : ∀ w : G, orderOf (c * w * c⁻¹) = orderOf w := fun w => by
    have := MulEquiv.orderOf_eq (MulAut.conj c) w
    simpa [MulAut.conj_apply] using this
  have hmemu : c * u * c⁻¹ ∈ K.map (MulAut.conj c).toMonoidHom :=
    ⟨u, hu, by simp [MulAut.conj_apply]⟩
  have hmemv : c * v * c⁻¹ ∈ K.map (MulAut.conj c).toMonoidHom :=
    ⟨v, hv, by simp [MulAut.conj_apply]⟩
  have h2 : 2 ≤ pRank 2 ↥(CxK x K) :=
    U1a.two_le_pRank_of_commute (hle hmemu) (hle hmemv) (by rw [hord, hu2]) (by rw [hord, hv2])
      (by
        calc c * u * c⁻¹ * (c * v * c⁻¹) = c * (u * v) * c⁻¹ := by group
          _ = c * (v * u) * c⁻¹ := by rw [hcomm]
          _ = c * v * c⁻¹ * (c * u * c⁻¹) := by group)
      (fun h => huv (by
        have := (MulAut.conj c).injective (a₁ := u) (a₂ := v) (by
          simpa [MulAut.conj_apply] using h)
        exact this))
  omega

theorem card_le_two_of_rank_le_one (hrk : pRank 2 ↥(CxK x K) ≤ 1) :
    ∀ A : Subgroup G, A ≤ CMK (centralizer ({x} : Set G)) K → IsElementaryAbelian 2 ↥A →
      Nat.card ↥A ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro A hAC hA
  by_contra hlt
  push Not at hlt
  have hAC' : A ≤ CxK x K := hAC
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card).1 (IsElementaryAbelian.isPGroup 2 ↥A)
  have hr2 : 2 ≤ r := by
    by_contra hr2
    push Not at hr2
    have h2r : 2 ^ r ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hA' : IsElementaryAbelian 2 ↥(A.subgroupOf (CxK x K)) := by
    have := hA
    exact IsElementaryAbelian.subgroupOf hAC'
  have hcard : Nat.card ↥(A.subgroupOf (CxK x K)) = 2 ^ r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC').toEquiv]
    exact hr
  have h2 : 2 ≤ pRank 2 ↥(CxK x K) :=
    hr2.trans (LieType.SteinbergBR.le_pRank_of_card one_lt_two _ hA' hcard)
  omega

theorem unique_of_rank_le_one
    (hGKF : Generic.GenericKnownFacts) (hE2 : E2.E2ComponentFacts) (hL34 : B_gen4_noL34_elem)
    (hGc : C3Hyp G) (hrk : pRank 2 ↥(CxK x K) ≤ 1) (h𝒰 : Is2TerminalU2Triple x y K) :
    ∀ K' : Subgroup G, IsPCompIn 2 (centralizer ({x} : Set G)) K' → K' = K := by
  intro K' hK'
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : orderOf x = 2 := h𝒰.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := h𝒰.1.1.2
  have hle : K' ≤ CxK x K := le_inf hK'.1 (Stage1.Thm2.Recip.le_cSec_of_ne hK' hK hne)
  have hbarc : CFSG.IsComponent (PumpCalc.bar x K') := PumpCalc.isComponent_bar hK'
  obtain ⟨e⟩ := PumpCalc.kBar_equiv_bar hK'
  have hcls : InC2 ↥(PumpCalc.bar x K') ∨ InU2 ↥(PumpCalc.bar x K') := hGc.lt2o.2 x hx2 _ hbarc
  have hgenL : CFSG.GH74.Gen4 ↥(PumpCalc.bar x K') :=
    (TwoThin.gen4Comp_of_gen4Cen (TwoThin.gen4Cen_barQ hGc.gen4 hx2) (PumpCalc.bar x K')).gen4
  have hnoL : ¬ (IsL34Quotient ↥(PumpCalc.bar x K') ∧
      CFSG.IsElementaryAbelian 2 ↥(center ↥(PumpCalc.bar x K')) ∧
      Nat.card ↥(center ↥(PumpCalc.bar x K')) ≤ 4) := fun h =>
    hL34 G hGc.gen4 x K' hx2 hK' (P14.l34type_of_mulEquiv e.symm h)
  have h2L : 2 ≤ CFSG.pRank 2 ↥(PumpCalc.bar x K') :=
    P14.two_le_pRank_of_c2u2 hGKF hE2 hbarc.1 hcls hgenL hnoL
  have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥K') := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hr : pRank 2 (kBar K') = pRank 2 ↥K' :=
    GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two (pPrimeCore 2 ↥K')
      hodd
  have h2K' : 2 ≤ pRank 2 ↥K' := by
    rw [← hr, Stage1.Thm2.Recip.pRank_eq_of_mulEquiv' e]
    exact h2L
  obtain ⟨u, hu, v, hv, hu2, hv2, huv, hcomm⟩ := U1a.exists_commuting_involutions (D := K') h2K'
  have h2 : 2 ≤ pRank 2 ↥(CxK x K) :=
    U1a.two_le_pRank_of_commute (hle hu) (hle hv) hu2 hv2 hcomm huv
  omega

structure A7Env (x y : G) (K T : Subgroup G) (f z : G) : Prop where
  hu2 : Is2TerminalU2Triple x y K
  e7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))
  hrk : pRank 2 ↥(CxK x K) ≤ 1
  hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K
  hsetup : Setup1D x K T
  hfT : f ∈ T
  hf2 : orderOf f = 2
  hfc : ∀ p ∈ T ⊓ K, f * p = p * f
  hind : P34.InducesFAutL2A7 f K
  hfout : Back.actHom hKN ⟨f, hsetup.sylowT.le hfT⟩ ∉ IVK.innAut (kBar K)
  hdih : ∃ n : ℕ, 3 ≤ n ∧ IVK.IsDihedralTwoGroup ↥(T ⊓ K) n
  hzP : z ∈ T ⊓ K
  hz2 : orderOf z = 2
  hzc : ∀ p ∈ T ⊓ K, z * p = p * z
  hzu : ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z

theorem exists_a7env (hG : C3Hyp G) (h𝒰 : Is2TerminalU2Triple x y K)
    (e7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) (hrk : pRank 2 ↥(CxK x K) ≤ 1)
    {T : Subgroup G} (hT : Setup1D x K T) : ∃ f z : G, A7Env x y K T f z := by
  have hshape : HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7)) :=
    Or.inr e7
  have hKN := normal_of_rank_le_one hrk h𝒰 hshape
  have hQ2 := card_le_two_of_rank_le_one hrk
  have hKC : K ≤ centralizer ({x} : Set G) := h𝒰.1.1.2.1
  have hxK : ∀ k ∈ K, x * k = k * x := fun k hk =>
    (mem_centralizer_singleton_iff.1 (hKC hk)).symm
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)) :=
    conj_injective_of_A7 e7.some
  have hAut : AutLevelF (kBar K) := autLevelF_of_A7 e7.some
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ :=
    exists_E₁ hT.sylowT (by rw [h𝒰.2.2.1.2, hG.pRank_eq_four])
  obtain ⟨f, z, hfT, hf2, hfc, hfx, hind, hinn, hdih, hzP, hz2, hzc, hzu⟩ :=
    transport_G hKC hKN hT.sylowT hxC hxK hcen hAut hE₁T hE₁ hE₁16 hQ2
  exact ⟨f, z, ⟨h𝒰, e7, hrk, hKN, hT, hfT, hf2, hfc, hind, hinn (hT.sylowT.le hfT), hdih, hzP, hz2,
    hzc, hzu⟩⟩

end Loc

end CFSG.GH74.GLS.C3.Layer1.Thm1A7

end
