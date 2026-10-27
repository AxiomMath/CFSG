module

public import Mathlib.GroupTheory.Sylow
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMExcB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.LocalAnalysis.GLTheoremA

theorem uexc_exists_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω Ω' : Type} [Group Ω] [Finite Ω]
    [Group Ω'] (π : Ω →* Ω') (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    {B₀ : Subgroup Ω} (hB₀ : IsPGroup p B₀) {Q' : Subgroup Ω'} (hQ' : IsPGroup p Q')
    (hle : B₀.map π ≤ Q') :
    ∃ Q : Subgroup Ω, B₀ ≤ Q ∧ IsPGroup p Q ∧ Q.map π = Q' ∧ Q ⊓ π.ker = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hN : ¬ p ∣ Nat.card π.ker := uexc_not_dvd_card_ker hp hp2 π hk
  set P : Subgroup Ω := Q'.comap π with hPdef
  have hB₀P : B₀ ≤ P := fun b hb => hle (Subgroup.mem_map_of_mem π hb)
  have hB₀p : IsPGroup p (B₀.subgroupOf P) :=
    hB₀.of_equiv (Subgroup.subgroupOfEquivOfLe hB₀P).symm
  obtain ⟨Q₀, hQ₀⟩ := hB₀p.exists_le_sylow
  set Q : Subgroup Ω := (Q₀ : Subgroup P).map P.subtype with hQdef
  have hQP : Q ≤ P := Subgroup.map_subtype_le _
  have hQp : IsPGroup p Q := Q₀.isPGroup'.map _
  have hQmap : Q.map π = Q' := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact hQP
    · let πP : P →* Q' := (π.comp P.subtype).codRestrict Q' (fun x => x.2)
      have hπP : Function.Surjective πP := by
        rintro ⟨s, hs⟩
        obtain ⟨x, rfl⟩ := hπ s
        exact ⟨⟨x, hs⟩, rfl⟩
      have htop : ((Q₀.mapSurjective hπP : Sylow p Q') : Subgroup Q') = ⊤ :=
        ((Q₀.mapSurjective hπP).is_maximal' (hQ'.of_equiv Subgroup.topEquiv.symm) le_top).symm
      intro s hs
      have hmem : (⟨s, hs⟩ : Q') ∈ ((Q₀.mapSurjective hπP : Sylow p Q') : Subgroup Q') := by
        rw [htop]
        exact Subgroup.mem_top _
      rw [Sylow.coe_mapSurjective, Subgroup.mem_map] at hmem
      obtain ⟨x, hx, hxs⟩ := hmem
      exact ⟨x, ⟨x, hx, rfl⟩, congrArg Subtype.val hxs⟩
  refine ⟨Q, ?_, hQp, hQmap, S267.inf_ker_eq_bot' hp π hN hQp⟩
  intro b hb
  exact ⟨⟨b, hB₀P hb⟩, hQ₀ (Subgroup.mem_subgroupOf.2 hb), rfl⟩

theorem uexc_mem_of_mem_map {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω Ω' : Type} [Group Ω]
    [Finite Ω] [Group Ω'] (π : Ω →* Ω') (hk : IsPGroup 2 π.ker) {K S : Subgroup Ω} (hKS : K ≤ S)
    (hkc : π.ker ≤ Subgroup.centralizer (S : Set Ω)) {c : Ω}
    (hc : IsPGroup p (Subgroup.zpowers c)) (hcK : π c ∈ K.map π) : c ∈ K := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hkK, hkc'⟩ := Subgroup.mem_map.1 hcK
  have hzker : k⁻¹ * c ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkc', inv_mul_cancel]
  have hcomm : Commute k (k⁻¹ * c) :=
    Subgroup.mem_centralizer_iff.1 (hkc hzker) k (hKS hkK)
  have hcdef : c = k * (k⁻¹ * c) := by group
  obtain ⟨e, he⟩ := hk.exists_card_eq
  have hzm : (k⁻¹ * c) ^ Nat.card π.ker = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (G := π.ker) (x := ⟨k⁻¹ * c, hzker⟩))
  have hcm : c ^ Nat.card π.ker = k ^ Nat.card π.ker := by
    conv_lhs => rw [hcdef]
    rw [hcomm.mul_pow, hzm, mul_one]
  obtain ⟨a, ha⟩ := hc.exists_card_eq
  have hord : orderOf c = p ^ a := by
    rw [← Nat.card_zpowers, ha]
  have hcop : Nat.Coprime (Nat.card π.ker) (orderOf c) := by
    rw [hord, he]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hmem : c ∈ Subgroup.zpowers (c ^ Nat.card π.ker) := mem_zpowers_pow_iff.2 hcop
  have hcmK : c ^ Nat.card π.ker ∈ K := by
    rw [hcm]
    exact K.pow_mem hkK _
  exact Subgroup.zpowers_le.2 hcmK hmem

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
