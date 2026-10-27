module

public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelBase
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3Uniq
public import CFSG.GH74.GLS.C3.Layer1.Thm1Layer
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelLeaves
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3Aux

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L3Uniq

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1

theorem thm1_P31_unique_of_rel (hP31c : B_thm1_P31c_rel) : B_thm1_P31_unique_rel := by
  intro G _ _ hG hNo x y K hu2 _ _ h5 K' hK'
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcomp : IsPCompIn 2 (centralizer ({x} : Set G)) K := hu2.1.1.2
  have hK'le : K' ≤ CxK x K :=
    le_inf hK'.1 (Stage1.Thm2.Recip.le_cSec_of_ne hK' hKcomp hne)
  have hS : IsSylowOf 2 (zpowers x) (CxK x K) := hP31c G hG hNo x y K hu2 h5
  have h4 : 4 ∣ Nat.card ↥K' := by
    have hq : CFSG.IsQuasisimple (kBar K') := TwoThin.isQuasisimple_hat hK'
    exact (four_dvd_card_of_isQuasisimple hq).trans
      (Subgroup.card_quotient_dvd_card _)
  obtain ⟨A, hA⟩ := exists_isSylowOf 2 K'
  have hAle := Thm1L3.card_le_of_isPGroup_of_isSylowOf hA.isPGroup (hA.le.trans hK'le) hS
  rw [Nat.card_zpowers, hu2.1.1.1] at hAle
  have hfac : 2 ≤ (Nat.card ↥K').factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1
      (by simpa using h4)
  have hAcard : Nat.card ↥A = 2 ^ (Nat.card ↥K').factorization 2 := hA.card_eq
  have : 2 ^ 2 ≤ 2 ^ (Nat.card ↥K').factorization 2 := Nat.pow_le_pow_right (by norm_num) hfac
  omega


end CFSG.GH74.GLS.C3.Layer1.Thm1L3Uniq

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1
open scoped commutatorElement

theorem thm1_P31_normal_rel {G : Type} [Group G] [Finite G] (hV : NoV2Fine G) {x y : G} {K : Subgroup G}
    (h𝒰 : Is2TerminalU2Triple x y K)
    (hshape : HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (h5 : ¬ HasL2Model (kBar K) (fun q => q = 5)) :
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
  exact h5 (hV x y K ⟨h𝒰.1, h𝒰.2.1, Or.inl h2, fun _ => h𝒰⟩)


theorem thm1_P31s_of_rel
    (h2hb : IVK.IVK_1_2h_b) (hL1 : B_thm1_P31_comp_rel) (hL2 : B_thm1_P31_layer_rel) :
    B_thm1_P31s_rel := by
  intro G _ _ hG hV x y K h𝒰 hshape h5
  obtain ⟨hKN, huniq⟩ := hL1 G hG hV x y K h𝒰 hshape h5
  have hKC : K ≤ centralizer ({x} : Set G) := h𝒰.1.1.2.1
  have hxK : ∀ k ∈ K, x * k = k * x := fun k hk =>
    (mem_centralizer_singleton_iff.1 (hKC hk)).symm
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hQ2 := card_le_two_of_noV2Fine hV h𝒰 h5
  obtain ⟨hcen, hAut⟩ := kBar_autData_rel h2hb hV h𝒰 hshape h5
  refine ⟨hKN, huniq, exists_Q_of_card_le_two hQ2, ?_⟩
  intro T hT
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ :=
    exists_E₁ hT.sylowT (by rw [h𝒰.2.2.1.2, hG.pRank_eq_four])
  obtain ⟨f, z, hfT, hf2, hfc, hfx, hind, hinn, hdih, hzP, hz2, hzc, hzu⟩ :=
    transport_G hKC hKN hT.sylowT hxC hxK hcen hAut hE₁T hE₁ hE₁16 hQ2
  have hfC : f ∈ centralizer ({x} : Set G) := hT.sylowT.le hfT
  have hzC : z ∈ centralizer ({x} : Set G) := hT.sylowT.le hzP.1
  refine ⟨?_, hdih, z, hzP, hz2, hzc, hzu⟩
  rcases hL2 G hG hV x y K h𝒰 hshape hKN T hT f z hfT hf2 hfc hind hzP hz2 hzc h5 with hl | ⟨hA7, hl⟩
  · exact ⟨f, ⟨hfT, hf2, hfc, hfx, hl⟩, hind⟩
  ·
    have hfz : f * z = z * f := hfc z hzP
    have hzT : z ∈ T := hzP.1
    have hzK : z ∈ K := hzP.2
    have hfzC : f * z ∈ centralizer ({x} : Set G) := Subgroup.mul_mem _ hfC hzC
    have hφz : Back.actHom hKN ⟨z, hzC⟩ ∈ IVK.innAut (kBar K) := by
      rw [Back.actHom_of_mem hKN hzK hzC]
      exact ⟨_, rfl⟩
    have hφfz : Back.actHom hKN ⟨f * z, hfzC⟩ ∉ IVK.innAut (kBar K) := by
      intro h
      apply hinn hfC
      have h1 := (Back.actHom hKN).map_mul ⟨f, hfC⟩ ⟨z, hzC⟩
      have e : (⟨f, hfC⟩ * ⟨z, hzC⟩ : ↥(centralizer ({x} : Set G))) = ⟨f * z, hfzC⟩ := rfl
      rw [e] at h1
      rw [h1] at h
      have := (IVK.innAut (kBar K)).mul_mem h ((IVK.innAut (kBar K)).inv_mem hφz)
      simpa using this
    have hfz1 : f * z ≠ 1 := fun h => hφfz (by
      have : (⟨f * z, hfzC⟩ : ↥(centralizer ({x} : Set G))) = 1 := Subtype.ext h
      rw [this, map_one]
      exact (IVK.innAut (kBar K)).one_mem)
    have hφx : Back.actHom hKN ⟨x, hxC⟩ = 1 :=
      (Back.actHom_eq_one_iff_commutator_mem hKN ⟨x, hxC⟩).2 (fun k hk => by
        have : ⁅k, x⁆ = 1 := by
          rw [commutatorElement_def, ← hxK k hk]
          group
        rw [this]
        exact (pPrimeCoreOf 2 K).one_mem)
    have hfzx : f * z ≠ x := fun h => hφfz (by
      have : (⟨f * z, hfzC⟩ : ↥(centralizer ({x} : Set G))) = ⟨x, hxC⟩ := Subtype.ext h
      rw [this, hφx]
      exact (IVK.innAut (kBar K)).one_mem)
    have hf2' : orderOf (f * z) = 2 := by
      refine orderOf_eq_prime ?_ hfz1
      have hff : f * f = 1 := by
        have := pow_orderOf_eq_one f
        rwa [hf2, sq] at this
      have hzz : z * z = 1 := by
        have := pow_orderOf_eq_one z
        rwa [hz2, sq] at this
      calc (f * z) ^ 2 = f * z * (f * z) := sq _
        _ = f * (z * f) * z := by simp only [mul_assoc]
        _ = f * (f * z) * z := by rw [← hfz]
        _ = (f * f) * (z * z) := by simp only [mul_assoc]
        _ = 1 := by rw [hff, hzz, one_mul]
    refine ⟨f * z, ⟨T.mul_mem hfT hzT, hf2', fun p hp => ?_, hfzx, hl⟩, ?_⟩
    · have h1 := hfc p hp
      have h2 := hzc p hp
      calc f * z * p = f * (z * p) := by group
        _ = f * (p * z) := by rw [h2]
        _ = (f * p) * z := by group
        _ = (p * f) * z := by rw [h1]
        _ = p * (f * z) := by group
    · have hφfz1 : Back.actHom hKN ⟨f * z, hfzC⟩ ≠ 1 := fun h =>
        hφfz (by rw [h]; exact (IVK.innAut (kBar K)).one_mem)
      exact ⟨U1a.mem_normalizer_of_norm hKN hfzC, hφfz1, Or.inr ⟨hA7, hφfz⟩⟩

end CFSG.GH74.GLS.C3.Layer1.Thm1

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1

theorem thm1_P31_comp_of_rel (hU : B_thm1_P31_unique_rel) : B_thm1_P31_comp_rel := by
  intro G _ _ hG hV x y K h𝒰 hshape h5
  have hN := thm1_P31_normal_rel hV h𝒰 hshape h5
  exact ⟨hN, hU G hG hV x y K h𝒰 hshape hN h5⟩

theorem thm1_P31_layer_of_rel
    (h2hb : IVK.IVK_1_2h_b) : B_thm1_P31_layer_rel := by
  intro G _ _ hG hV x y K h𝒰 hshape hKN T hT f z hfT hf2 hfc hind hzP hz2 hzc h5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ≤ centralizer ({x} : Set G) := h𝒰.1.1.2.1
  have hQ2 := card_le_two_of_noV2Fine hV h𝒰 h5
  obtain ⟨hcen, hAut⟩ := kBar_autData_rel h2hb hV h𝒰 hshape h5
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ := exists_E₁ hT.sylowT (by rw [h𝒰.2.2.1.2, hG.pRank_eq_four])
  have hfC : f ∈ centralizer ({x} : Set G) := hT.sylowT.le hfT
  have hzC : z ∈ centralizer ({x} : Set G) := hT.sylowT.le hzP.1
  obtain ⟨f₁, z₁, -, -, -, -, -, -, -, hz₁, hz₁2, hz₁c, hz₁u, -, -, -, hlay⟩ :=
    core_lift_G hKC hKN hT.sylowT hcen hAut hE₁T hE₁ hE₁16 hQ2
  have hzP' : (⟨z, hzC⟩ : ↥(centralizer ({x} : Set G))) ∈
      (T ⊓ K).subgroupOf (centralizer ({x} : Set G)) := hzP
  have hzz₁ : (⟨z, hzC⟩ : ↥(centralizer ({x} : Set G))) = z₁ := by
    rcases hz₁u ⟨z, hzC⟩ hzP' (fun q hq => Subtype.ext (hzc (q : G) hq)) with h | h
    · exfalso
      have : z = 1 := congrArg Subtype.val h
      rw [this, orderOf_one] at hz2
      omega
    · exact h
  have hfCT : (⟨f, hfC⟩ : ↥(centralizer ({x} : Set G))) ∈
      T.subgroupOf (centralizer ({x} : Set G)) := hfT
  have hf2' : orderOf (⟨f, hfC⟩ : ↥(centralizer ({x} : Set G))) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hf2
  have hfc' : ∀ p ∈ (T ⊓ K).subgroupOf (centralizer ({x} : Set G)),
      (⟨f, hfC⟩ : ↥(centralizer ({x} : Set G))) * p = p * ⟨f, hfC⟩ :=
    fun p hp => Subtype.ext (hfc p hp)
  have hφfinn : Back.actHom hKN ⟨f, hfC⟩ ∉ IVK.innAut (kBar K) := by
    obtain ⟨hfN, hF⟩ := hind
    exact not_mem_innAut_of_isFAutL2A7 hF
  rcases hlay ⟨f, hfC⟩ hfCT hf2' hfc' hφfinn with hg | ⟨hA7, hg⟩
  · exact Or.inl (layer_ne_bot_of_good hKN hfC hf2 hg)
  · refine Or.inr ⟨hA7, ?_⟩
    have hfzC : f * z ∈ centralizer ({x} : Set G) := Subgroup.mul_mem _ hfC hzC
    have hfz : f * z = z * f := hfc z hzP
    have hφz : Back.actHom hKN ⟨z, hzC⟩ ∈ IVK.innAut (kBar K) := by
      rw [Back.actHom_of_mem hKN hzP.2 hzC]
      exact ⟨_, rfl⟩
    have hφfz_eq : Back.actHom hKN ⟨f * z, hfzC⟩ =
        Back.actHom hKN ⟨f, hfC⟩ * Back.actHom hKN ⟨z, hzC⟩ := by
      have h1 := (Back.actHom hKN).map_mul ⟨f, hfC⟩ ⟨z, hzC⟩
      have e : (⟨f, hfC⟩ * ⟨z, hzC⟩ : ↥(centralizer ({x} : Set G))) = ⟨f * z, hfzC⟩ := rfl
      rw [e] at h1
      exact h1
    have hfz1 : f * z ≠ 1 := by
      intro h
      apply hφfinn
      have h1 : Back.actHom hKN ⟨f * z, hfzC⟩ = 1 := by
        have : (⟨f * z, hfzC⟩ : ↥(centralizer ({x} : Set G))) = 1 := Subtype.ext h
        rw [this, map_one]
      rw [hφfz_eq] at h1
      have h2 : Back.actHom hKN ⟨f, hfC⟩ = (Back.actHom hKN ⟨z, hzC⟩)⁻¹ :=
        eq_inv_of_mul_eq_one_left h1
      rw [h2]
      exact (IVK.innAut (kBar K)).inv_mem hφz
    have hfz2 : orderOf (f * z) = 2 := orderOf_mul_eq_two_of_commute hf2 hz2 hfz hfz1
    refine layer_ne_bot_of_good hKN hfzC hfz2 ?_
    rw [hφfz_eq, hzz₁]
    exact hg

end CFSG.GH74.GLS
