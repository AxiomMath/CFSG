module

public import CFSG.GH74.GLS.Balance.Defs
public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.GroupTheory.PrimeCorefreeQuasisimple

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1Three

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup
open scoped MatrixGroups

theorem exists_lift_two_le {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y] (ρ : X →* Y)
    (hker : ¬ 2 ∣ Nat.card ρ.ker) (E : Subgroup Y) (hE : E ≤ ρ.range) (hE2 : IsPGroup 2 ↥E)
    {P₀ : Subgroup X} (hP₀ : IsPGroup 2 ↥P₀) (hP₀E : P₀.map ρ ≤ E) :
    ∃ S : Subgroup X, P₀ ≤ S ∧ S.map ρ = E ∧ ∀ s ∈ S, ρ s = 1 → s = 1 := by
  classical
  have hp : Nat.Prime 2 := Nat.prime_two
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  obtain ⟨k, hEcard⟩ := hE2.exists_card_eq
  set P' : Subgroup X := E.comap ρ with hP'
  let f : P' →* E := (ρ.comp P'.subtype).codRestrict E fun x => x.2
  have hfsurj : Function.Surjective f := fun e => by
    obtain ⟨g, hg⟩ := hE e.2
    exact ⟨⟨g, show ρ g ∈ E by rw [hg]; exact e.2⟩, Subtype.ext hg⟩
  have hfx : ∀ x : P', (f x : Y) = ρ x := fun x => rfl
  have hkerf : Nat.card f.ker = Nat.card ρ.ker := by
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, ?_⟩, fun x => ⟨⟨x.1, ?_⟩, ?_⟩, ?_, ?_⟩
    · have := x.2
      rw [MonoidHom.mem_ker] at this ⊢
      have h2 := congrArg Subtype.val this
      rwa [hfx] at h2
    · show ρ x.1 ∈ E
      rw [MonoidHom.mem_ker.mp x.2]; exact E.one_mem
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hfx]
      exact MonoidHom.mem_ker.mp x.2
    · intro x; rfl
    · intro x; rfl
  have hPc : Nat.card P' = Nat.card ρ.ker * 2 ^ k := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfsurj).toEquiv, hEcard,
      hkerf] at h1
    rw [h1, mul_comm]
  set P₀' : Subgroup ↥P' := P₀.comap P'.subtype with hP₀'
  have hP₀'2 : IsPGroup 2 ↥P₀' := hP₀.comap_of_injective P'.subtype P'.subtype_injective
  obtain ⟨S, hP₀S⟩ := hP₀'2.exists_le_sylow
  have hScard : Nat.card S = 2 ^ k := by
    rw [Sylow.card_eq_multiplicity, hPc, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero k hp.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, Nat.Prime.factorization_pow hp]
    simp
  have key : ∀ x ∈ S.map P'.subtype, ρ x = 1 → x = 1 := by
    intro x hx hρx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    have h1 : orderOf (x' : X) ∣ 2 ^ k := by
      rw [← hScard]
      have := Subgroup.orderOf_dvd_natCard (S : Subgroup P') hx'
      simpa [Subgroup.orderOf_coe] using this
    have h2 : orderOf (x' : X) ∣ Nat.card ρ.ker := by
      have hmem : (x' : X) ∈ ρ.ker := hρx
      have := Subgroup.orderOf_dvd_natCard ρ.ker hmem
      simpa [Subgroup.orderOf_coe] using this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ρ.ker) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hker)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
  have hSinj : ∀ x ∈ S.map P'.subtype, ∀ y ∈ S.map P'.subtype, ρ x = ρ y → x = y := by
    intro x hx y hy hxy
    have : x * y⁻¹ = 1 := key _ (Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hy))
      (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  set E₀ : Subgroup X := S.map P'.subtype with hE₀
  have hE₀card : Nat.card E₀ = 2 ^ k := by
    rw [hE₀, Subgroup.card_map_of_injective P'.subtype_injective, hScard]
  have hmapE : E₀.map ρ = E := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
      exact g'.2
    · have : Nat.card (E₀.map ρ) = Nat.card E₀ := by
        refine Nat.card_congr (Equiv.ofBijective
          (fun x : E₀ => ⟨ρ x, Subgroup.mem_map_of_mem _ x.2⟩) ⟨?_, ?_⟩).symm
        · intro x y hxy
          exact Subtype.ext (hSinj _ x.2 _ y.2 (congrArg Subtype.val hxy))
        · rintro ⟨_, g, hg, rfl⟩
          exact ⟨⟨g, hg⟩, rfl⟩
      rw [this, hE₀card, hEcard]
  refine ⟨E₀, fun p hp => ?_, hmapE, key⟩
  have hpP' : p ∈ P' := hP₀E ⟨p, hp, rfl⟩
  exact ⟨⟨p, hpP'⟩, hP₀S (show (⟨p, hpP'⟩ : ↥P') ∈ P₀' from hp), rfl⟩

theorem isSolvTwoComp_of_map {Y Q : Type*} [Group Y] [Finite Y] [Group Q] (g : Y →* Q)
    (hker : ¬ 2 ∣ Nat.card g.ker) {J : Subgroup Q} (hJ : J ≤ g.range)
    (hsub : (J.subgroupOf g.range).IsSubnormal) (hsl : Nonempty (↥J ≃* SL(2, ZMod 3))) :
    ∃ V : Subgroup Y, Balance.IsSolvTwoCompSL23 Y V ∧ J.comap g ≤ V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σ⟩ := hsl
  set P : Subgroup Y := J.comap g with hP
  set π : Y →* Y ⧸ pPrimeCore 2 Y := QuotientGroup.mk' (pPrimeCore 2 Y) with hπ
  set W : Subgroup (Y ⧸ pPrimeCore 2 Y) := P.map π with hW
  refine ⟨W.comap π, ⟨W, ?_, ?_, rfl⟩, Subgroup.le_comap_map π P⟩
  ·
    have hPsub : P.IsSubnormal := by
      have hPeq : P = (J.subgroupOf g.range).comap g.rangeRestrict := by
        ext y
        simp [hP, Subgroup.mem_subgroupOf]
      rw [hPeq]
      exact hsub.comap _
    exact hPsub.map (QuotientGroup.mk'_surjective _)
  ·
    have hkerO : g.ker ≤ pPrimeCore 2 Y :=
      CFSG.GroupTheory.le_pPrimeCore_of_normal (MonoidHom.normal_ker g)
        (Nat.coprime_two_left.2 (Nat.odd_iff.2 (by omega)))
    let gP : ↥P →* ↥J := (g.comp P.subtype).codRestrict J (fun p => p.2)
    have hgPs : Function.Surjective gP := by
      rintro ⟨j, hj⟩
      obtain ⟨y, hy⟩ := hJ hj
      exact ⟨⟨y, show g y ∈ J by rw [hy]; exact hj⟩, Subtype.ext hy⟩
    let πP : ↥P →* ↥W := (π.comp P.subtype).codRestrict W (fun p => Subgroup.mem_map_of_mem π p.2)
    have hπPs : Function.Surjective πP := by
      rintro ⟨w, p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
    have hk : πP.ker = gP.ker := by
      ext p
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      constructor
      · intro h
        have h1 : π (p : Y) = 1 := congrArg Subtype.val h
        have hpO : (p : Y) ∈ pPrimeCore 2 Y := (QuotientGroup.eq_one_iff _).1 h1
        set N : Subgroup ↥P := (pPrimeCore 2 Y).subgroupOf P with hN
        have hNn : N.Normal := Subgroup.Normal.subgroupOf (inferInstance : (pPrimeCore 2 Y).Normal) P
        have hNodd : Odd (Nat.card ↥(N.map gP)) := by
          have hdvd : Nat.card ↥(N.map gP) ∣ Nat.card ↥N := Subgroup.card_map_dvd _ _
          have hNc : Nat.card ↥N ∣ Nat.card ↥(pPrimeCore 2 Y) := by
            have h1 : N.map P.subtype ≤ pPrimeCore 2 Y := by
              rintro _ ⟨n, hn, rfl⟩
              exact hn
            rw [← Subgroup.card_map_of_injective P.subtype_injective]
            exact Subgroup.card_dvd_of_le h1
          have hc : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 Y)) := CFSG.pPrimeCore_coprime_card
          exact Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_right (hdvd.trans hNc) hc)
        have hbot := CFSG.ClassicalInvolution.normal_odd_of_equiv_sl2 (P := ↥J) (F := ZMod 3)
          (by rw [Nat.card_zmod]; decide) (by rw [Nat.card_zmod]) σ (N.map gP)
          (hNn.map gP hgPs) hNodd
        have : gP p ∈ N.map gP := Subgroup.mem_map_of_mem gP (show p ∈ N from hpO)
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      · intro h
        have h1 : g (p : Y) = 1 := congrArg Subtype.val h
        apply Subtype.ext
        show π (p : Y) = 1
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hkerO h1
    exact ⟨(QuotientGroup.quotientKerEquivOfSurjective πP hπPs).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        ((QuotientGroup.quotientKerEquivOfSurjective gP hgPs).trans σ))⟩

end S1Three

end CFSG.GH74.Generic.BProg.B3
