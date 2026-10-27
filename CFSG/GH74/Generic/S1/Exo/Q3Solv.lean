module

public import CFSG.GH74.GLS.Balance.Defs

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74.GLS Subgroup
open scoped MatrixGroups

theorem exists_solvTwoComp_of_subnormal_sl23 {X : Type} [Group X] [Finite X] {x : X}
    {J : Subgroup X} (hJ : J ≤ centralizer ({x} : Set X))
    (hsub : (J.subgroupOf (centralizer ({x} : Set X))).IsSubnormal)
    (hsl : Nonempty (↥J ≃* SL(2, ZMod 3)))
    (hodd : ∀ N : Subgroup ↥J, N.Normal → Odd (Nat.card N) → N = ⊥) :
    ∃ V : Subgroup X, Balance.IsSolvTwoCompSL23In (centralizer ({x} : Set X)) V ∧ J ≤ V := by
  obtain ⟨σ⟩ := hsl
  set Y : Subgroup X := centralizer ({x} : Set X)
  have : Finite ↥Y := inferInstance
  let π : ↥Y →* ↥Y ⧸ pPrimeCore 2 ↥Y := QuotientGroup.mk' (pPrimeCore 2 ↥Y)
  let J' : Subgroup ↥Y := J.subgroupOf Y
  let e : ↥J' ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJ
  let φ : ↥J' →* ↥Y ⧸ pPrimeCore 2 ↥Y := π.comp J'.subtype
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    set K : Subgroup ↥J' := φ.ker
    have hKnorm : K.Normal := MonoidHom.normal_ker _
    have hKodd : Odd (Nat.card K) := by
      have hle : K.map J'.subtype ≤ pPrimeCore 2 ↥Y := by
        rintro _ ⟨k, hk, rfl⟩
        have : π (k : ↥Y) = 1 := hk
        exact (QuotientGroup.eq_one_iff _).mp this
      have hdvd : Nat.card (K.map J'.subtype) ∣ Nat.card (pPrimeCore 2 ↥Y) :=
        Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective J'.subtype_injective] at hdvd
      have hodd2 : Odd (Nat.card (pPrimeCore 2 ↥Y)) :=
        Nat.coprime_two_left.mp pPrimeCore_coprime_card
      exact hodd2.of_dvd_nat hdvd
    have hKe : K.map e.toMonoidHom = ⊥ :=
      hodd _ (hKnorm.map _ e.surjective)
        (by rwa [Subgroup.card_map_of_injective e.injective])
    exact (Subgroup.map_eq_bot_iff_of_injective K e.injective).mp hKe
  have hW : J'.map π = φ.range := by
    ext w
    simp [φ, MonoidHom.mem_range, Subgroup.mem_map]
  have hWsub : (J'.map π).IsSubnormal :=
    Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective _) hsub
  have hWe : Nonempty (↥(J'.map π) ≃* SL(2, ZMod 3)) :=
    ⟨(MulEquiv.subgroupCongr hW).trans ((MonoidHom.ofInjective hinj).symm.trans (e.trans σ))⟩
  refine ⟨((J'.map π).comap π).map Y.subtype, ⟨Subgroup.map_subtype_le _, ?_⟩, ?_⟩
  · refine ⟨J'.map π, hWsub, hWe, ?_⟩
    exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  · intro j hj
    refine ⟨⟨j, hJ hj⟩, ?_, rfl⟩
    exact ⟨⟨j, hJ hj⟩, hj, rfl⟩

end CFSG.GH74.Generic.S1.Exo
