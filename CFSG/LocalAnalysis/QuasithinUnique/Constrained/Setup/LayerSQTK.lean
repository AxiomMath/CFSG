module

public import CFSG.LocalAnalysis.SectionRank.Induction

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.SectionRank CFSG.Open CFSG.LocalCores

theorem elemAbelian_le_of_two_quotient {G : Type} [Group G] (L : Subgroup G) [L.Normal]
    (h2 : IsPGroup 2 (G ⧸ L)) {p : ℕ} (hp2 : p ≠ 2) (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) : E ≤ L := by
  intro x hx
  obtain ⟨n, hn⟩ := h2 (QuotientGroup.mk x)
  have h1 : (QuotientGroup.mk x : G ⧸ L) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hE.2 x hx, QuotientGroup.mk_one]
  have hcop : Nat.Coprime (2 ^ n) p :=
    Nat.Coprime.pow_left n ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h3 : orderOf (QuotientGroup.mk x : G ⧸ L) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h4 : orderOf (QuotientGroup.mk x : G ⧸ L) ∣ p := orderOf_dvd_of_pow_eq_one h1
  have h5 : orderOf (QuotientGroup.mk x : G ⧸ L) = 1 := Nat.eq_one_of_dvd_coprimes hcop h3 h4
  have h6 : (QuotientGroup.mk x : G ⧸ L) = 1 := orderOf_eq_one_iff.1 h5
  exact (QuotientGroup.eq_one_iff x).1 h6

theorem sqtk_two_power_index (hcent : OddKernelCentralization) (hcat : CatalogStepHyp)
    {X : Type} [Group X] [Finite X] (hX : IsSQTKCat X) (H : Subgroup X) {G : Type} [Group G]
    [Finite G] (π : ↥H →* G) (hπ : Function.Surjective π) (L : Subgroup G) [L.Normal]
    (hL : CFSG.layer ↥L = ⊤) (h2 : IsPGroup 2 (G ⧸ L)) :
    IsSQTKCat G ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p (⊤ : Subgroup G) = CFSG.Open.pRank p (⊤ : Subgroup ↥L) ∧
        CFSG.Open.pRank p (⊤ : Subgroup ↥L) ≤ 2 := by
  classical
  let P : Subgroup ↥H := L.comap π
  let N : Subgroup ↥P := π.ker.subgroupOf P
  let ρ : ↥P →* ↥L := (π.comp P.subtype).codRestrict L (fun x => x.2)
  have hρ : Function.Surjective ρ := fun l => by
    obtain ⟨h, hh⟩ := hπ (l : G)
    exact ⟨⟨h, show π h ∈ L from hh ▸ l.2⟩, Subtype.ext hh⟩
  have hker : ρ.ker = N := by
    ext x
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h
      have := congrArg Subtype.val h
      exact this
    · intro h
      exact Subtype.ext h
  have e : (↥P ⧸ N) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)
  have hE : CFSG.layer (↥P ⧸ N) = ⊤ := layer_eq_top_of_mulEquiv e.symm hL
  have hsqt : IsStronglyQuasithin (↥P ⧸ N) :=
    sqtk_semisimple_section_rank_of_catalog hcent hcat (hX.subgroup H) P N hE
  have hsqtL : IsStronglyQuasithin ↥L := by
    rw [isStronglyQuasithin_iff] at hsqt ⊢
    intro q hq hq2
    rw [← pRank_top_eq_of_mulEquiv hq.one_lt e]
    exact hsqt q hq hq2
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p (⊤ : Subgroup G) = CFSG.Open.pRank p (⊤ : Subgroup ↥L) := by
    intro p hp hp2
    apply le_antisymm
    · obtain ⟨E, -, hE, hcard⟩ := exists_pRank hp.one_lt (⊤ : Subgroup G)
      have hEL : E ≤ L := elemAbelian_le_of_two_quotient L h2 hp2 hp hE
      have hE' : IsElemAbelian p (E.subgroupOf L) := by
        have e1 : ↥(E.subgroupOf L) ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEL
        refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
        · apply e1.injective
          rw [map_mul, map_mul]
          exact hE.1.is_comm.comm _ _
        · have := hE.2 (x : G) hx
          exact Subtype.ext this
      refine le_pRank hp.one_lt le_top hE' ?_
      rw [← hcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
    · exact pRank_top_le_of_injective hp.one_lt L.subtype L.subtype_injective
  refine ⟨⟨?_, ?_⟩, fun p hp hp2 => ⟨hrank p hp hp2, ?_⟩⟩
  · rw [isStronglyQuasithin_iff]
    intro q hq hq2
    rw [hrank q hq hq2]
    exact (isStronglyQuasithin_iff.1 hsqtL) q hq hq2
  ·
    have hH : IsKGroupCat ↥H := hX.2.subgroup H
    have hq : IsKGroupCat (↥H ⧸ π.ker) := hH.quotient π.ker
    exact hq.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm
  · exact (isStronglyQuasithin_iff.1 hsqtL) p hp hp2

end CFSG.QuasithinUnique.Setup.Layer
