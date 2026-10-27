module

public import Mathlib.GroupTheory.Transfer
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open Subgroup

theorem false_of_cyclic_two_subgroup_odd_index {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnc : ∃ a b : G, a * b ≠ b * a) {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) (hcyc : IsCyclic T) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 G := hT2.toSylow hTi
  have hScyc : IsCyclic S := hcyc
  have hcomm_of_cyclic : IsCyclic G → False := fun hG => by
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (@mul_comm G (@IsCyclic.commGroup G _ hG).toCommMagma a b)
  by_cases hev : 2 ∣ Nat.card G
  · have hmin : (Nat.card G).minFac = 2 := Nat.minFac_eq_two_iff _ |>.mpr hev
    have hcomp := IsCyclic.isComplement' hmin hScyc
    have hNn : (MonoidHom.transferSylow S (hScyc.normalizer_le_centralizer hmin)).ker.Normal :=
      MonoidHom.normal_ker _
    have hcard := hcomp.card_mul_card
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ _
      (MonoidHom.transferSylow S (hScyc.normalizer_le_centralizer hmin)).ker hNn with h | h
    · rw [h, Subgroup.card_bot, one_mul] at hcard
      have hST : (S : Subgroup G) = ⊤ := Subgroup.card_eq_iff_eq_top _ |>.mp hcard
      have : IsCyclic G := by
        have : IsCyclic (⊤ : Subgroup G) := by rw [← hST]; exact hScyc
        exact isCyclic_of_surjective (Subgroup.topEquiv (G := G)).toMonoidHom
          (Subgroup.topEquiv (G := G)).surjective
      exact hcomm_of_cyclic this
    · rw [h, Subgroup.card_top] at hcard
      have h1 : Nat.card S = 1 := by
        have hpos : 0 < Nat.card G := Nat.card_pos
        nlinarith [hcard, hpos]
      have hidx : T.index = Nat.card G := by
        have := Subgroup.card_mul_index T
        have hT1 : Nat.card T = 1 := h1
        rw [hT1, one_mul] at this
        exact this
      exact hTi (hidx ▸ hev)
  · have hodd' : Odd (Nat.card G) := Nat.odd_iff.mpr (by omega)
    have hsolv : Group.IsSolvable G := CFSG.FeitThompson.isSolvable_of_odd_natCard G hodd'
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := G)).mpr hsolv a b)

theorem two_dvd_relIndex_of_cyclic_two_subgroup {X : Type} [Group X] [Finite X]
    {K Γ T : Subgroup X} (hKs : IsSimpleGroup ↥K) (hnc : ∃ a b : ↥K, a * b ≠ b * a)
    (hΓK : Γ ≤ K) (hTΓ : T ≤ Γ) (hT2 : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.relIndex Γ)
    (hcyc : IsCyclic ↥T) : 2 ∣ Γ.relIndex K := by
  by_contra hodd
  have hTK : T ≤ K := hTΓ.trans hΓK
  let e : ↥T ≃* ↥(T.subgroupOf K) := (Subgroup.subgroupOfEquivOfLe hTK).symm
  refine false_of_cyclic_two_subgroup_odd_index (G := ↥K) hnc (T := T.subgroupOf K)
    (hT2.of_surjective e.toMonoidHom e.surjective) ?_
    (isCyclic_of_surjective e.toMonoidHom e.surjective)
  have hidx : (T.subgroupOf K).index = T.relIndex Γ * Γ.relIndex K :=
    (Subgroup.relIndex_mul_relIndex T Γ K hTΓ hΓK).symm
  rw [hidx]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
  · exact hTi h
  · exact hodd h

theorem isCyclic_quotient_of_normal_sup {X : Type*} [Group X] {Γ Q J : Subgroup X}
    (hΓ : Γ = Q ⊔ J) (hN : Γ ≤ Subgroup.normalizer (Q : Set X)) (hJ : IsCyclic ↥J) :
    haveI : (Q.subgroupOf Γ).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hΓ ▸ le_sup_left)).mpr hN
    IsCyclic (↥Γ ⧸ Q.subgroupOf Γ) := by
  have hQΓ : Q ≤ Γ := hΓ ▸ le_sup_left
  have hSΓ : J ≤ Γ := hΓ ▸ le_sup_right
  have hQn : (Q.subgroupOf Γ).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQΓ).mpr hN
  let f : ↥J →* (↥Γ ⧸ Q.subgroupOf Γ) :=
    (QuotientGroup.mk' (Q.subgroupOf Γ)).comp (Subgroup.inclusion hSΓ)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hsup : Q.subgroupOf Γ ⊔ J.subgroupOf Γ = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hQΓ hSΓ, ← hΓ, Subgroup.subgroupOf_self]
    have hg : g ∈ (J.subgroupOf Γ ⊔ Q.subgroupOf Γ : Subgroup ↥Γ) := by
      rw [sup_comm, hsup]; exact Subgroup.mem_top g
    have hg' : g ∈ ((J.subgroupOf Γ ⊔ Q.subgroupOf Γ : Subgroup ↥Γ) : Set ↥Γ) := hg
    rw [Subgroup.mul_normal] at hg'
    obtain ⟨s', hs', q', hq', rfl⟩ := hg'
    refine ⟨⟨(s' : X), hs'⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion hSΓ ⟨(s' : X), hs'⟩) = QuotientGroup.mk (s' * q')
    rw [QuotientGroup.eq]
    have h1 : Subgroup.inclusion hSΓ ⟨(s' : X), hs'⟩ = s' := rfl
    rw [h1, inv_mul_cancel_left]
    exact hq'
  exact isCyclic_of_surjective f hf

theorem exists_cyclic_sylow_two_of_normal_sup {X : Type*} [Group X] [Finite X] {Γ Q J : Subgroup X}
    (hΓ : Γ = Q ⊔ J) (hN : Γ ≤ Subgroup.normalizer (Q : Set X)) (hQ3 : IsPGroup 3 Q)
    (hJ : IsCyclic ↥J) :
    ∃ T : Subgroup X, T ≤ Γ ∧ IsPGroup 2 T ∧ ¬ 2 ∣ T.relIndex Γ ∧ IsCyclic ↥T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQΓ : Q ≤ Γ := hΓ ▸ le_sup_left
  have hQn : (Q.subgroupOf Γ).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQΓ).mpr hN
  have hcyc := isCyclic_quotient_of_normal_sup hΓ hN hJ
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 ↥Γ) := inferInstance
  have hTΓ : (T₀ : Subgroup ↥Γ).map Γ.subtype ≤ Γ := Subgroup.map_subtype_le _
  have hsub : ((T₀ : Subgroup ↥Γ).map Γ.subtype).subgroupOf Γ = T₀ :=
    Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective _
  refine ⟨(T₀ : Subgroup ↥Γ).map Γ.subtype, hTΓ, T₀.isPGroup'.map _, ?_, ?_⟩
  · show ¬ 2 ∣ (((T₀ : Subgroup ↥Γ).map Γ.subtype).subgroupOf Γ).index
    rw [hsub]; exact T₀.not_dvd_index
  · have hinj : Function.Injective
        ((QuotientGroup.mk' (Q.subgroupOf Γ)).comp (T₀ : Subgroup ↥Γ).subtype) := by
      refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
      have hxQ : (x : ↥Γ) ∈ Q.subgroupOf Γ := (QuotientGroup.eq_one_iff _).mp hx
      have hQ3' : IsPGroup 3 (Q.subgroupOf Γ) :=
        hQ3.of_surjective (Subgroup.subgroupOfEquivOfLe hQΓ).symm.toMonoidHom
          (Subgroup.subgroupOfEquivOfLe hQΓ).symm.surjective
      obtain ⟨a, ha⟩ := T₀.isPGroup' x
      obtain ⟨b, hb⟩ := hQ3' ⟨(x : ↥Γ), hxQ⟩
      have h2 : (x : ↥Γ) ^ (2 ^ a) = 1 := by simpa using congrArg Subtype.val ha
      have h3 : (x : ↥Γ) ^ (3 ^ b) = 1 := by simpa using congrArg Subtype.val hb
      have hd2 : orderOf (x : ↥Γ) ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h2
      have hd3 : orderOf (x : ↥Γ) ∣ 3 ^ b := orderOf_dvd_of_pow_eq_one h3
      have hcop : Nat.Coprime (2 ^ a) (3 ^ b) :=
        Nat.Coprime.pow _ _ (by norm_num)
      have : orderOf (x : ↥Γ) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd3
      exact Subtype.ext (orderOf_eq_one_iff.mp this)
    have hcT : IsCyclic ↥(T₀ : Subgroup ↥Γ) := isCyclic_of_injective _ hinj
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (T₀ : Subgroup ↥Γ) Γ.subtype Γ.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective (T₀ : Subgroup ↥Γ) Γ.subtype Γ.subtype_injective).surjective

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
