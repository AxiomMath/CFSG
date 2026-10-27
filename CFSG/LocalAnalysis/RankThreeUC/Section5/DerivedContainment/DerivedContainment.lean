module

public import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
public import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter
public import CFSG.LocalAnalysis.RankThreeUC.Section5.NontrivialActor

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

namespace DerivedContainment

theorem card_le_of_cyclic {E : Type*} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    (K : Subgroup E) [IsCyclic K] (hexp : ∀ x ∈ K, x ^ p = 1) : Nat.card K ≤ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K)
  have hord : orderOf g = Nat.card K := orderOf_eq_card_of_forall_mem_zpowers hg
  have : g ^ p = 1 := Subtype.ext (by simpa using hexp g g.2)
  exact hord ▸ Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one this)

theorem derived_le {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ)
    (hext : CFSG.IsExtraspecialPGroup p ↥P) : P ≤ commutator G := by
  have cyclic_normal_le_center {E : Type} [Group E] [Finite E] {p : ℕ} [hp : Fact p.Prime]
      (hE : IsPGroup p E) (hexp : ∀ x : E, x ^ p = 1) (N : Subgroup E) [N.Normal] [IsCyclic N] :
      N ≤ Subgroup.center E := by
    by_cases hN : N = ⊥
    · rw [hN]; exact bot_le
    have hne := CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot hE N hN
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have haN : (a : E) ∈ N := a.2.1
    have haZ : (a : E) ∈ Subgroup.center E := a.2.2
    have ha1' : (a : E) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hord : orderOf (a : E) = p := orderOf_eq_prime (hexp _) ha1'
    have hle : Subgroup.zpowers (a : E) ≤ N := (Subgroup.zpowers_le).2 haN
    have hcard : Nat.card N ≤ Nat.card (Subgroup.zpowers (a : E)) := by
      rw [Nat.card_zpowers, hord]
      exact card_le_of_cyclic hp.out N (fun x _ => hexp x)
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    rw [← heq]
    exact (Subgroup.zpowers_le).2 haZ
  have hs := h51.setting
  haveI : Fact p.Prime := ⟨hs.prime⟩
  haveI hPn : P.Normal := h53.normal
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
  have hNcyc : IsCyclic N := CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one hs.prime hp2 hNp (by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]; omega)
  have hexpP : ∀ x : ↥P, x ^ p = 1 := fun x => by
    have := Monoid.pow_exponent_eq_one x
    rwa [hs.exponent] at this
  haveI : IsCyclic (N.subgroupOf P) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hNP).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hNP).symm.surjective
  haveI : (N.subgroupOf P).Normal := Subgroup.Normal.subgroupOf inferInstance P
  have hcen := cyclic_normal_le_center hs.pGroup hexpP (N.subgroupOf P)
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h51.actor_ne_bot
  have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  let ψ : MulAut ↥P := MulAut.conjNormal (H := P) (b : G)
  have hψ : ∀ x : ↥P, ((ψ x : ↥P) : G) = (b : G) * x * (b : G)⁻¹ := fun x => rfl
  have hz : ∀ x : ↥P, ψ x * x⁻¹ ∈ Subgroup.center ↥P := by
    intro x
    have h1 : ψ x * x⁻¹ ∈ N.subgroupOf P := by
      show (((ψ x * x⁻¹ : ↥P)) : G) ∈ N
      refine ⟨(ψ x * x⁻¹ : ↥P).2, ?_⟩
      have hc := Subgroup.commutator_mem_commutator (Subgroup.mem_top (b : G))
        (Subgroup.mem_top (x : G))
      simpa [hψ, commutatorElement_def, commutator_def] using hc
    exact hcen h1
  let f : ↥P →* Subgroup.center ↥P := MonoidHom.mk' (fun x => ⟨ψ x * x⁻¹, hz x⟩) (by
    intro x y
    apply Subtype.ext
    have hy := Subgroup.mem_center_iff.1 (hz y) x⁻¹
    simp only [map_mul, Subgroup.coe_mul, mul_inv_rev]
    calc ψ x * ψ y * (y⁻¹ * x⁻¹) = ψ x * (ψ y * y⁻¹) * x⁻¹ := by group
      _ = ψ x * (x⁻¹ * (ψ y * y⁻¹)) := by rw [mul_assoc, hy]
      _ = ψ x * x⁻¹ * (ψ y * y⁻¹) := by group)
  have hker : f.ker = (P ⊓ Subgroup.centralizer ({(b : G)} : Set G)).subgroupOf P := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      have h' : ψ x * x⁻¹ = 1 := by simpa [f] using congrArg Subtype.val h
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
  have hZcard : Nat.card (Subgroup.center ↥P) = p := hext.2.2.2
  have hrange : Nat.card f.range ≤ p := by
    rw [← hZcard]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hPcard : Nat.card ↥P ≤ p * p := by
    rw [← Subgroup.card_mul_index f.ker, Subgroup.index_ker]
    exact Nat.mul_le_mul hkercard hrange
  obtain ⟨E, hEP, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hs.prime.one_lt P
  have hk := h53.rank_gt
  have hpk : p ^ 2 ≤ Nat.card E := by
    rw [hEcard]; exact Nat.pow_le_pow_right hs.prime.pos hk
  have hEle : Nat.card ↥P ≤ Nat.card E := by nlinarith
  have hEeq : E = P := Subgroup.eq_of_le_of_card_ge hEP hEle
  subst hEeq
  have hcomm := hE.1
  have hctop : Subgroup.center ↥E = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact Subgroup.mem_center_iff.2 fun g => hcomm.is_comm.comm g x
  rw [hctop, Subgroup.card_top] at hZcard
  nlinarith [hs.prime.two_le]

end DerivedContainment

end Section5

end CFSG.LocalAnalysis.RankThreeUC
