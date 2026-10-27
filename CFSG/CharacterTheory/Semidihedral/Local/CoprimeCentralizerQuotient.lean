module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.CharacterTheory.Semidihedral.OddCoreQuotient

public section

namespace CFSG.Semidihedral.Local

open CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.CoprimeFixedPoint

variable {G : Type*} [Group G]

theorem pPrimeCore_map_eq_of_coprime_ker {E F : Type*} [Group E] [Group F] [Finite E] [Finite F]
    (p : ℕ) [Fact p.Prime] (f : E →* F) (hf : Function.Surjective f)
    (hker : Nat.Coprime p (Nat.card f.ker)) :
    (CFSG.pPrimeCore p E).map f = CFSG.pPrimeCore p F := by
  apply le_antisymm (CFSG.Semidihedral.OddCoreQuotient.pPrimeCore_map_le_of_surjective p f hf)
  have hWn : ((CFSG.pPrimeCore p F).comap f).Normal :=
    (CFSG.pPrimeCore_normal (p := p) (G := F)).comap f
  have hWcard : Nat.Coprime p (Nat.card ((CFSG.pPrimeCore p F).comap f)) := by
    have h1 := Subgroup.relIndex_mul_card f.ker ((CFSG.pPrimeCore p F).comap f)
    rw [Subgroup.relIndex_ker, Subgroup.map_comap_eq_self_of_surjective hf] at h1
    rw [← h1]
    exact Nat.Coprime.mul_right (CFSG.pPrimeCore_coprime_card (p := p) (G := F))
      (hker.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left))
  have hW : (CFSG.pPrimeCore p F).comap f ≤ CFSG.pPrimeCore p E := le_sSup ⟨hWn, hWcard⟩
  calc CFSG.pPrimeCore p F = ((CFSG.pPrimeCore p F).comap f).map f :=
        (Subgroup.map_comap_eq_self_of_surjective hf _).symm
    _ ≤ (CFSG.pPrimeCore p E).map f := Subgroup.map_mono hW

theorem map_centralizer_eq_of_coprime [Finite G] (p : ℕ) [Fact p.Prime] (N : Subgroup G)
    [N.Normal] (hN : ¬ p ∣ Nat.card N) (A : Subgroup G) (hA : IsPGroup p A) :
    (Subgroup.centralizer (A : Set G)).map (QuotientGroup.mk' N) =
      Subgroup.centralizer ((A.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc a ha]
  · intro q hq
    let α : A →* MulAut G := MulAut.conj.comp A.subtype
    have hNα : ∀ a : A, ∀ n ∈ N, α a n ∈ N := fun a n hn =>
      (inferInstance : N.Normal).conj_mem n hn a
    have hfix : q ∈ {q : G ⧸ N | ∀ a : A, quotientAction α N hNα a q = q} := by
      intro a
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [quotientAction_mk]
      have h := Subgroup.mem_centralizer_iff.mp hq (QuotientGroup.mk' N (a : G))
        ⟨a, a.2, rfl⟩
      change ((((a : G) * x * (a : G)⁻¹ : G)) : G ⧸ N) = (x : G ⧸ N)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change QuotientGroup.mk' N (a : G) * (x : G ⧸ N) * (QuotientGroup.mk' N (a : G))⁻¹ =
        (x : G ⧸ N)
      rw [h, mul_inv_cancel_right]
    rw [coprime_fixed_point_lifting p hA α N hNα hN] at hfix
    obtain ⟨c, hc, rfl⟩ := hfix
    refine ⟨c, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_, rfl⟩
    have h : (a : G) * c * a⁻¹ = c := hc ⟨a, ha⟩
    calc a * c = (a * c * a⁻¹) * a := by group
      _ = c * a := by rw [h]

theorem coprime_centralizer_prime_complement_core_quotient [Finite G] (p : ℕ) [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hN : ¬ p ∣ Nat.card N) (A : Subgroup G) (hA : IsPGroup p A) :
    let π := QuotientGroup.mk' N
    let CA := Subgroup.centralizer (A : Set G)
    let CQ := Subgroup.centralizer ((A.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N))
    CA.map π = CQ ∧
      ((CFSG.pPrimeCore p CA).map CA.subtype).map π = (CFSG.pPrimeCore p CQ).map CQ.subtype ∧
      (π.comp CA.subtype).ker = N.subgroupOf CA ∧
      (π.comp CA.subtype).ker ≤ CFSG.pPrimeCore p CA := by
  intro π CA CQ
  have hcent : CA.map π = CQ := map_centralizer_eq_of_coprime p N hN A hA
  have hcopN : Nat.Coprime p (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN
  have hker : (π.comp CA.subtype).ker = N.subgroupOf CA := by
    ext c
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  have hkercop : Nat.Coprime p (Nat.card (π.comp CA.subtype).ker) := by
    rw [hker]
    refine hcopN.coprime_dvd_right ?_
    rw [← Subgroup.card_map_of_injective CA.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hkerle : (π.comp CA.subtype).ker ≤ CFSG.pPrimeCore p CA := le_sSup ⟨inferInstance, hkercop⟩
  let f : CA →* CQ := (π.comp CA.subtype).codRestrict CQ fun c =>
    hcent ▸ Subgroup.mem_map_of_mem π c.2
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    rw [← hcent] at hq
    obtain ⟨c, hc, rfl⟩ := hq
    exact ⟨⟨c, hc⟩, rfl⟩
  have hfker : f.ker = (π.comp CA.subtype).ker := MonoidHom.ker_codRestrict _ _ _
  have hcore := pPrimeCore_map_eq_of_coprime_ker p f hf (hfker ▸ hkercop)
  refine ⟨hcent, ?_, hker, hkerle⟩
  rw [← hcore, Subgroup.map_map, Subgroup.map_map]
  rfl

end CFSG.Semidihedral.Local
