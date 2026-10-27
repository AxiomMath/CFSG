module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinPair
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFacts

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Quasithin

section Cent

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_of_isPGroup {A : Subgroup G} (hA2 : IsPGroup 2 ↥A) (hA : A ≠ ⊥) :
    ∃ t ∈ A, orderOf t = 2 := by
  have hn : 1 < Nat.card ↥A :=
    Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot A).mpr hA)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hA2
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    omega
  have hdvd : 2 ∣ Nat.card ↥A := by
    rw [hm]
    exact dvd_pow_self 2 hm0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩

theorem isPGroup_inf_centralizer_of_cent_two {K A : Subgroup G}
    (hcent : ∀ i : ↥K, orderOf i = 2 → IsPGroup 2 ↥(Subgroup.centralizer ({i} : Set ↥K)))
    (hAK : A ≤ K) (hA2 : IsPGroup 2 ↥A) (hA : A ≠ ⊥) :
    IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (A : Set G)) := by
  obtain ⟨t, htA, hto⟩ := exists_involution_of_isPGroup hA2 hA
  have hio : orderOf (⟨t, hAK htA⟩ : ↥K) = 2 := by
    rw [← hto]
    exact (Subgroup.orderOf_coe (⟨t, hAK htA⟩ : ↥K)).symm
  refine isPGroup_of_forall_pow fun y hy => ?_
  have hyK : y ∈ K := hy.1
  have hyc : (⟨y, hyK⟩ : ↥K) ∈ Subgroup.centralizer ({(⟨t, hAK htA⟩ : ↥K)} : Set ↥K) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hy.2 t htA).symm
  obtain ⟨k, hk⟩ := hcent _ hio ⟨⟨y, hyK⟩, hyc⟩
  exact ⟨k, by simpa using congrArg (fun w : ↥(Subgroup.centralizer
    ({(⟨t, hAK htA⟩ : ↥K)} : Set ↥K)) => ((w : ↥K) : G)) hk⟩

theorem charTwo_inf_normalizer_of_cent_two {K R : Subgroup G}
    (hcent : ∀ i : ↥K, orderOf i = 2 → IsPGroup 2 ↥(Subgroup.centralizer ({i} : Set ↥K)))
    (hRK : R ≤ K) (hR2 : IsPGroup 2 ↥R) (hR : R ≠ ⊥)
    (hrad : pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) = R) :
    CharTwo (K ⊓ Subgroup.normalizer (R : Set G)) :=
  charTwo_of_isPGroup_inf_centralizer inf_le_right hrad
    ((isPGroup_inf_centralizer_of_cent_two hcent hRK hR2 hR).to_le fun _ hx => ⟨hx.1.1, hx.2⟩)

end Cent

section Radical

variable {G : Type} [Group G] [Finite G] {T M H S : Subgroup G} {z : G}

theorem charTwo_inf_normalizer_of_l2p
    (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z)
    (hinn : ∀ L : Subgroup G, IsComponentIn L H → Ch1.InducesInner z L) {K : Subgroup G}
    (hK : IsComponentIn K H) (hL2p : IsL2pType ↥K) {R : Subgroup G} (hRD : R ≤ conjJoin H K)
    (hR2 : IsPGroup 2 ↥R)
    (hcomp : ∀ L : Subgroup G, IsComponentIn L H → L ≤ conjJoin H K →
      ¬ R ≤ Subgroup.centralizer (L : Set G))
    (hrad : pCoreOf 2 (conjJoin H K ⊓ Subgroup.normalizer (R : Set G)) = R) :
    CharTwo (conjJoin H K ⊓ Subgroup.normalizer (R : Set G)) := by
  have hdata : L2pData ↥K := l2pFacts ↥K hL2p
  have hRK : ¬ R ≤ Subgroup.centralizer (K : Set G) := hcomp K hK (le_conjJoin_self H K)
  have hRne : R ≠ ⊥ := fun h => hRK (h ▸ bot_le)
  rcases shape hs ht hinn hK with hD | ⟨s, hsS, -, hK', hcomm, hD⟩
  · rw [hD] at hRD hrad ⊢
    exact charTwo_inf_normalizer_of_cent_two hdata.cent_two hRD hR2 hRne hrad
  · have hDK' : CFSG.conjugate K s ≤ conjJoin H K := by
      rw [hD]
      exact le_sup_right
    have hRK' : ¬ R ≤ Subgroup.centralizer (CFSG.conjugate K s : Set G) :=
      hcomp _ hK' hDK'
    have hc : ∀ a ∈ K, ∀ b ∈ CFSG.conjugate K s, a * b = b * a := fun a ha b hb =>
      BenderBranch.commute_of_commutator_eq_bot hcomm ha hb
    have hKK' : ∀ x, x ∈ K → x ∈ CFSG.conjugate K s → x = 1 := fun x hxK hxK' =>
      BenderBranch.eq_one_of_commute_of_simple hdata.simple hdata.nonabelian hxK fun w hw =>
        hc w hw x hxK'
    have e : ↥(CFSG.conjugate K s) ≃* ↥K :=
      (K.equivMapOfInjective (MulAut.conj s⁻¹).toMonoidHom (MulAut.conj s⁻¹).injective).symm
    have hdata' : L2pData ↥(CFSG.conjugate K s) := Unc25K1.l2pData_of_mulEquiv e hdata
    rw [hD] at hRD hrad ⊢
    exact charTwo_inf_normalizer_of_pair hc hKK'
      (fun A hAK hA2 hA => isPGroup_inf_centralizer_of_cent_two hdata.cent_two hAK hA2 hA)
      (fun A hAK hA2 hA => isPGroup_inf_centralizer_of_cent_two hdata'.cent_two hAK hA2 hA)
      hRD hR2 hRK hRK' hrad

end Radical

end CFSG.QuasithinUnique.Fin253
