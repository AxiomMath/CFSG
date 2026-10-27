module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291SCDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BTransport
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer
public import CFSG.RankThree.PartTwo.Sec4.T444.Coprime

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem sc_map {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) {B : Subgroup X}
    (hB : IsPGroup p B) (hSC : ∀ y ∈ centralizer (B : Set X), y ^ p = 1 → y ∈ B) :
    ∀ y ∈ centralizer ((B.map (QuotientGroup.mk' (primeComplementCore (G := X) p)) :
        Subgroup (X ⧸ primeComplementCore (G := X) p)) : Set (X ⧸ primeComplementCore (G := X) p)),
      y ^ p = 1 → y ∈ B.map (QuotientGroup.mk' (primeComplementCore (G := X) p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup X := primeComplementCore (G := X) p with hD
  set π : X →* X ⧸ D := QuotientGroup.mk' D with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hker : ¬ p ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (primeComplementCore_coprime p)
  intro yb hybc hybp
  set K : Subgroup X := centralizer (B : Set X) with hK
  set C : Subgroup (X ⧸ D) := centralizer ((B.map π : Subgroup (X ⧸ D)) : Set (X ⧸ D)) with hC
  have hmap : K.map π = C :=
    CFSG.RankThreeEvenClassification.Helpers.centralizer_map_eq_of_pGroup_prime_complement_kernel
      p hp π hπs hker B hB
  let ρ : ↥K →* ↥C := (π.comp K.subtype).codRestrict C
    (fun k => hmap ▸ Subgroup.mem_map_of_mem π k.2)
  have hρ : Function.Surjective ρ := by
    rintro ⟨c, hc⟩
    rw [← hmap] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact ⟨⟨k, hk⟩, rfl⟩
  let ybC : ↥C := ⟨yb, hybc⟩
  have hord : orderOf ybC ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext hybp)
  have hpg : IsPGroup p (zpowers ybC) := by
    rcases (Nat.dvd_prime hp).1 hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective hρ p S
  have hmem : ybC ∈ ((Q : Subgroup ↥K).map ρ) := by
    have := hS (Subgroup.mem_zpowers ybC)
    rwa [Sylow.coe_mapSurjective] at this
  obtain ⟨r, hrQ, hr⟩ := hmem
  have hπr : π (r : X) = yb := congrArg Subtype.val hr
  set Q' : Subgroup X := (Q : Subgroup ↥K).map K.subtype with hQ'
  have hQ'p : IsPGroup p Q' := Q.isPGroup'.map K.subtype
  have hrQ' : (r : X) ∈ Q' := Subgroup.mem_map_of_mem K.subtype hrQ
  have hrp : (r : X) ^ p = 1 := by
    refine K62B.eq_one_of_mk_eq_one hp hQ'p (pow_mem hrQ' p) ?_
    show π ((r : X) ^ p) = 1
    rw [map_pow, hπr, hybp]
  exact ⟨(r : X), hSC (r : X) r.2 hrp, hπr⟩

theorem yData_of_plane63 {p : ℕ} {X : Type} [Group X] [Finite X] {P : Sylow p X} {x z : X}
    (hpl : Plane63 p X P x z) :
    YData p (X ⧸ primeComplementCore (G := X) p)
      ((P : Subgroup X).map (QuotientGroup.mk' (primeComplementCore (G := X) p)))
      (x : X ⧸ primeComplementCore (G := X) p) (z : X ⧸ primeComplementCore (G := X) p) := by
  have hprime := hpl.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  set D : Subgroup X := primeComplementCore (G := X) p with hD
  have hD3 : ¬ p ∣ Nat.card D :=
    (Nat.Prime.coprime_iff_not_dvd hprime).mp (primeComplementCore_coprime p)
  set π : X →* X ⧸ D := QuotientGroup.mk' D with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  have hker : ¬ p ∣ Nat.card π.ker := by rw [QuotientGroup.ker_mk']; exact hD3
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup X) := hpl.plane.isIsolatedPlane.1
  have hxP : x ∈ (P : Subgroup X) := hBP (Subgroup.mem_sup_left (mem_zpowers x))
  have hB : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup X) :=
    IsPGroup.of_card (n := 2) hpl.plane.card_eq
  have hBmap : (zpowers x ⊔ zpowers z : Subgroup X).map π =
      zpowers (x : X ⧸ D) ⊔ zpowers (z : X ⧸ D) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  refine ⟨K62B.cfg_of_plane63 hpl, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := CFSG.SectionRank.pRank_quotient_eq (G := X) (p := p) D hD3
    have h2 := hpl.four_le
    have h3 : Open.pRank p (P : Subgroup X) ≤ Open.pRank p (⊤ : Subgroup X) :=
      CFSG.SectionRank.pRank_mono hprime.one_lt le_top
    omega
  · have hxp : IsPGroup p (zpowers x) := P.isPGroup'.to_le (zpowers_le.mpr hxP)
    have hmap :=
      CFSG.RankThreeEvenClassification.Helpers.centralizer_map_eq_of_pGroup_prime_complement_kernel
        p hprime π hπs hker (zpowers x) hxp
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hmap
    have hxπ : π x = (x : X ⧸ D) := rfl
    rw [hxπ] at hmap
    rw [← hmap]
    exact (CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hprime π hker _).trans
      hpl.rank_centralizer
  · intro N _ hN
    set f : X →* (X ⧸ D) ⧸ N := (QuotientGroup.mk' N).comp π with hf
    have hfs : Function.Surjective f := (QuotientGroup.mk'_surjective N).comp hπs
    have hfker : f.ker = N.comap π := by
      rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    have hp' : IsPGroup p (X ⧸ f.ker) :=
      hN.of_equiv (QuotientGroup.quotientKerEquivOfSurjective f hfs).symm
    have hp'' : IsPGroup p (X ⧸ N.comap π) :=
      hp'.of_equiv (QuotientGroup.quotientMulEquivOfEq hfker)
    have htop := hpl.perfect (N.comap π) hp''
    rw [← Subgroup.map_comap_eq_self_of_surjective hπs N, htop, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr hπs]
  · rw [← hBmap]
    exact (K62B.card_map_mk_eq hprime hB).trans hpl.plane.card_eq
  · rw [← hBmap]
    exact sc_map hprime hB (fun y hy hyp => hpl.plane.mem_of_mem_centralizer y hy hyp)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291
