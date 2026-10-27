module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.DerivedContainment.DerivedContainment

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.LargeElementaryDerivedContainment

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.DerivedContainment

theorem derived_le {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ)
    (hEA : CFSG.Open.IsElemAbelian p P) (hlarge : 2 < CFSG.Open.pRank p P) :
    P ≤ commutator G := by
  have hs := h51.setting
  haveI : Fact p.Prime := ⟨hs.prime⟩
  haveI hPn : P.Normal := h53.normal
  have hcommP : ∀ a b : ↥P, a * b = b * a := fun a b => hEA.1.is_comm.comm a b
  by_cases hr : 1 < CFSG.Open.pRank p (P ⊓ commutator G)
  · have := h53.minimal (P ⊓ commutator G) inferInstance hr inf_le_left
    exact this ▸ inf_le_right
  exfalso
  set N : Subgroup G := P ⊓ commutator G with hNdef
  have hNP : N ≤ P := inf_le_left
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hs.odd (by decide)
  have hNp : IsPGroup p N := (hs.pGroup.to_subgroup (N.subgroupOf P)).of_equiv
    (Subgroup.subgroupOfEquivOfLe hNP)
  have hNcyc : IsCyclic N := OddRankOneQuotient.isCyclic_of_pRank_le_one hs.prime hp2 hNp (by
    rw [SectionRank.pRank_coe_eq_openPRank]; omega)
  have hexpP : ∀ x : ↥P, x ^ p = 1 := fun x => by
    have := Monoid.pow_exponent_eq_one x
    rwa [hs.exponent] at this
  haveI : IsCyclic (N.subgroupOf P) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hNP).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hNP).symm.surjective
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h51.actor_ne_bot
  have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  let ψ : MulAut ↥P := MulAut.conjNormal (H := P) (b : G)
  have hψ : ∀ x : ↥P, ((ψ x : ↥P) : G) = (b : G) * x * (b : G)⁻¹ := fun x => rfl
  have hz : ∀ x : ↥P, ψ x * x⁻¹ ∈ N.subgroupOf P := by
    intro x
    show (((ψ x * x⁻¹ : ↥P)) : G) ∈ N
    refine ⟨(ψ x * x⁻¹ : ↥P).2, ?_⟩
    have hc := Subgroup.commutator_mem_commutator (Subgroup.mem_top (b : G))
      (Subgroup.mem_top (x : G))
    simpa [hψ, commutatorElement_def, commutator_def] using hc
  let f : ↥P →* ↥(N.subgroupOf P) := MonoidHom.mk' (fun x => ⟨ψ x * x⁻¹, hz x⟩) (by
    intro x y
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul, mul_inv_rev]
    calc ψ x * ψ y * (y⁻¹ * x⁻¹) = ψ x * (ψ y * y⁻¹) * x⁻¹ := by group
      _ = ψ x * (x⁻¹ * (ψ y * y⁻¹)) := by rw [mul_assoc, hcommP (ψ y * y⁻¹) x⁻¹]
      _ = ψ x * x⁻¹ * (ψ y * y⁻¹) := by group)
  have hker : f.ker = (P ⊓ Subgroup.centralizer ({(b : G)} : Set G)).subgroupOf P := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      have h' : ψ x * x⁻¹ = 1 := by simpa [f] using congrArg (fun z => ((z : ↥P) : ↥P)) (congrArg Subtype.val h)
      have h'' : ψ x = x := mul_inv_eq_one.1 h'
      refine ⟨x.2, ?_⟩
      have := congrArg Subtype.val h''
      rw [hψ] at this
      calc (b : G) * x = ((b : G) * x * (b : G)⁻¹) * b := by rw [inv_mul_cancel_right]
        _ = x * b := by rw [this]
    · rintro ⟨-, h⟩
      apply Subtype.ext
      have : ψ x * x⁻¹ = 1 := by
        apply mul_inv_eq_one.2
        apply Subtype.ext
        rw [hψ]
        calc (b : G) * x * b⁻¹ = x * b * b⁻¹ := by rw [h]
          _ = x := mul_inv_cancel_right _ _
      simpa [f] using this
  have hkercard : Nat.card f.ker ≤ p := by
    rw [hker]
    haveI : IsCyclic ↥(P ⊓ Subgroup.centralizer ({(b : G)} : Set G)) :=
      h51.cyclic_centralizer b b.2 hb1'
    haveI : IsCyclic ((P ⊓ Subgroup.centralizer ({(b : G)} : Set G)).subgroupOf P) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe inf_le_left).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe inf_le_left).symm.surjective
    exact card_le_of_cyclic hs.prime _ (fun x _ => hexpP x)
  have hrange : Nat.card f.range ≤ p := by
    calc Nat.card f.range ≤ Nat.card (N.subgroupOf P) :=
          Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ ≤ p := by
        haveI : IsCyclic (N.subgroupOf P) := inferInstance
        exact card_le_of_cyclic hs.prime _ (fun x _ => hexpP x)
  have hPcard : Nat.card ↥P ≤ p * p := by
    rw [← Subgroup.card_mul_index f.ker, Subgroup.index_ker]
    exact Nat.mul_le_mul hkercard hrange
  obtain ⟨E, hEP, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hs.prime.one_lt P
  have hpk : p ^ 3 ≤ Nat.card E := by
    rw [hEcard]; exact Nat.pow_le_pow_right hs.prime.pos hlarge
  have hEle : Nat.card E ≤ Nat.card ↥P := Nat.card_le_card_of_injective _
    (Subgroup.inclusion_injective hEP)
  have h2 := hs.prime.two_le
  nlinarith [Nat.pos_of_ne_zero hs.prime.ne_zero, pow_succ p 2, sq p]

end CFSG.LocalAnalysis.RankThreeUC.Section5.LargeElementaryDerivedContainment
