module

public import CFSG.ClassicalInvolution.Q3.Q3TLTDatum
public import CFSG.ClassicalInvolution.SmallCases.NobqOut

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem outTwoCyclic_of_hom {X C : Type*} [Group X] [Group C] (Θ : MulAut X →* C)
    (hC : ∀ P : Subgroup C, IsPGroup 2 P → IsCyclic P) (hinn : inner X ≤ Θ.ker)
    (hodd : ∀ δ ∈ Θ.ker, ∀ k : ℕ, δ ^ 2 ^ k ∈ inner X → δ ∈ inner X) :
    Nobq.OutTwoCyclic X := by
  intro P hP
  let Θ' : Outer X →* C := QuotientGroup.lift (inner X) Θ hinn
  let f : P →* P.map Θ' := (Θ'.comp P.subtype).codRestrict _ fun p => ⟨p, p.2, rfl⟩
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hp1 : Θ' (p : Outer X) = 1 := congrArg Subtype.val hp
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) p
    obtain ⟨δ, hδ⟩ := QuotientGroup.mk_surjective (p : Outer X)
    have hδker : δ ∈ Θ.ker := by
      rw [MonoidHom.mem_ker]
      rw [← hδ] at hp1
      exact hp1
    have hδk : δ ^ 2 ^ k ∈ inner X := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hδ]
      have : (p : Outer X) ^ 2 ^ k = 1 := by
        rw [← Subgroup.orderOf_coe] at hk
        rw [← hk, pow_orderOf_eq_one]
      exact this
    have hδ1 : (QuotientGroup.mk δ : Outer X) = 1 :=
      (QuotientGroup.eq_one_iff δ).mpr (hodd δ hδker k hδk)
    apply Subtype.ext
    rw [← hδ, hδ1]
    rfl
  have : IsCyclic (P.map Θ') := hC _ (hP.map Θ')
  exact Nobq.isCyclic_of_injective_hom f hf

theorem outTwoCyclic_of_hom_cyclic {X C : Type*} [Group X] [Group C] [IsCyclic C]
    (Θ : MulAut X →* C) (hker : Θ.ker = inner X) : Nobq.OutTwoCyclic X :=
  outTwoCyclic_of_hom Θ (fun _ _ => inferInstance) hker.ge (fun _ hδ _ _ => hker ▸ hδ)

theorem outTwoCyclic_of_card_dvd {X : Type*} [Group X] [Finite X] {m : ℕ} (hm : Odd m)
    (h : Nat.card (Outer X) ∣ 2 * m) : Nobq.OutTwoCyclic X := by
  intro P hP
  have : Finite (MulAut X) := Nobq.finite_mulAut_of_finite X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : 2 ^ k ∣ 2 * m := hk ▸ (Subgroup.card_subgroup_dvd_card P).trans h
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have h4 : 2 ^ 2 ∣ 2 * m := (pow_dvd_pow 2 (by omega)).trans hdvd
    obtain ⟨j, rfl⟩ := hm
    omega
  interval_cases k
  · have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp (by rw [hk, pow_zero])).1
    infer_instance
  · exact isCyclic_of_prime_card (by rw [hk, pow_one])

theorem TightDatum.exists_cyclic4_of_outTwoCyclic {G : Type} [Group G] [Finite G]
    {R : Subgroup G} {S : Sylow 2 R} {t : G} (hD : Q3.TightDatum R S t) {N : Subgroup G}
    [N.Normal] (hC : Subgroup.centralizer (N : Set G) = ⊥) (hO : Nobq.OutTwoCyclic N) :
    t ∈ N ∧ ∃ s ∈ R, s ∈ N ∧ orderOf s = 4 := by
  obtain ⟨r, hr, ⟨eS⟩⟩ := hD.quat
  obtain ⟨htN, hU⟩ := Nobq.exists_uniqueInvNormal_of_datum N
    (Nobq.isCyclic_of_outTwoCyclic N hC hO) S hr eS hD.mem hD.order hD.cent hD.normal
  obtain ⟨s, hs, hs4⟩ := hU.exists_orderOf_eq_four
  obtain ⟨hsR, hsN⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hs)
  exact ⟨htN, s, hsR, hsN, by rw [Subgroup.orderOf_coe]; exact hs4⟩

end CFSG.ClassicalInvolution.Q3.TA3
