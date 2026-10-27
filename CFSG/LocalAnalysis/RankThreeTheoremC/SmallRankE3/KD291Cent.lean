module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291PerfHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4GammaCent
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29InnerHolds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem kd291_aux_PS_prime_card {Q : Type} [Group Q] [IsSimpleGroup Q] (hQ : Group.IsSolvable Q) :
    (Nat.card Q).Prime := by
  haveI : IsMulCommutative Q := IsMulCommutative.of_comm (IsSimpleGroup.comm_iff_isSolvable.mpr hQ)
  exact Group.is_simple_iff_prime_card.mp inferInstance

theorem kd291_isPSolvable_of_map {p : ℕ} (hp : p.Prime) {G B : Type} [Group G] [Finite G]
    [Group B] (φ : G →* B) (hker : Nat.Coprime p (Nat.card φ.ker))
    (hs : Group.IsSolvable φ.range) : CFSG.HallHigman.IsPSolvable p G := by
  intro H _hH T _hT hQ
  have hle : (φ.comp H.subtype).range ≤ φ.range := by
    intro b hb
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hb
    exact MonoidHom.mem_range.mpr ⟨x.1, rfl⟩
  haveI : Group.IsSolvable (φ.comp H.subtype).range :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  haveI hA : Group.IsSolvable (H ⧸ (φ.comp H.subtype).ker) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (QuotientGroup.quotientKerEquivRange (φ.comp H.subtype)).toMonoidHom)
      (QuotientGroup.quotientKerEquivRange (φ.comp H.subtype)).injective
  have hcardN : Nat.card (φ.comp H.subtype).ker ∣ Nat.card φ.ker := by
    have hN : (φ.comp H.subtype).ker = φ.ker.comap H.subtype := by
      ext x
      simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [hN]
    exact Subgroup.card_comap_dvd_of_injective φ.ker H.subtype H.subtype_injective
  haveI : ((φ.comp H.subtype).ker.map (QuotientGroup.mk' T)).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' T) (QuotientGroup.mk'_surjective T)
  rcases Subgroup.Normal.eq_bot_or_eq_top
      ((φ.comp H.subtype).ker.map (QuotientGroup.mk' T)) with h | h
  ·
    have hNT : (φ.comp H.subtype).ker ≤ T := by
      intro n hn
      have hmem : QuotientGroup.mk' T n ∈ (φ.comp H.subtype).ker.map (QuotientGroup.mk' T) :=
        Subgroup.mem_map_of_mem _ hn
      rw [h, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff n).mp hmem
    have hNT' : (φ.comp H.subtype).ker ≤ (QuotientGroup.mk' T).ker := by
      rw [QuotientGroup.ker_mk']
      exact hNT
    have hsurj : Function.Surjective
        (QuotientGroup.lift (φ.comp H.subtype).ker (QuotientGroup.mk' T) hNT') := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective T q
      exact ⟨QuotientGroup.mk' (φ.comp H.subtype).ker x, rfl⟩
    haveI : Group.IsSolvable (H ⧸ T) := Group.isSolvable_of_surjective hsurj
    have hprime := kd291_aux_PS_prime_card (Q := H ⧸ T) inferInstance
    rw [Subgroup.index_eq_card]
    by_cases hrp : Nat.card (H ⧸ T) = p
    · exact Or.inl hrp
    · exact Or.inr ((Nat.coprime_primes hp hprime).2 (fun h' => hrp h'.symm))
  ·
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' T).comp (φ.comp H.subtype).ker.subtype) := by
      intro q
      have hq : q ∈ (φ.comp H.subtype).ker.map (QuotientGroup.mk' T) := by
        rw [h]
        exact Subgroup.mem_top q
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq
      exact ⟨⟨x, hx⟩, rfl⟩
    have hdvd : Nat.card (H ⧸ T) ∣ Nat.card φ.ker :=
      dvd_trans (Subgroup.card_dvd_of_surjective hsurj) hcardN
    right
    rw [Subgroup.index_eq_card]
    exact Nat.Coprime.coprime_dvd_right hdvd hker


section CertificateInstances



theorem gammaCentP_holds : GammaCentP := by
  intro p hp hp5 X _ _ P x hcat hxP hx1 hx5 hP hC hperf _ hcomp
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨L, hLn, hLs, hLnab, hLcat, hLlu, hLC, hxL, -⟩ :=
    gammaStructureP_holds p hp hp5 X P x hcat hxP hx1 hx5 hP hC hperf hcomp
  haveI := hLn
  have hxo : orderOf x = p := orderOf_eq_prime hx5 hx1
  have hY : 3 ≤ Open.pRank p (⊤ : Subgroup (X ⧸ primeComplementCore (G := X) p)) :=
    (kd291_pRank_quot hp P hP).ge
  have hsolv := kd291_solvable_of_inner hp hp5 CFSG.LocalAnalysis.RankFourTheoremC.kd29Inner_holds
    L hLs hLnab hLcat hLlu hLC hY hxL (kd291_orderOf_mk hp hxo)
    (kd291_pRank_cent_quot hp hxo hC.le)
  let φ : ↥(centralizer ({x} : Set X)) →* X ⧸ primeComplementCore (G := X) p :=
    (QuotientGroup.mk' (primeComplementCore (G := X) p)).comp (centralizer ({x} : Set X)).subtype
  refine kd291_isPSolvable_of_map hp φ ?_ ?_
  ·
    let f : φ.ker →* ↥(primeComplementCore (G := X) p) :=
      MonoidHom.codRestrict ((centralizer ({x} : Set X)).subtype.comp φ.ker.subtype)
        (primeComplementCore (G := X) p) (fun g => by
          have h := g.2
          rw [MonoidHom.mem_ker] at h
          exact (QuotientGroup.eq_one_iff _).1 h)
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(primeComplementCore (G := X) p) => (z : X)) hab
    exact (primeComplementCore_coprime (G := X) p).coprime_dvd_right
      (Subgroup.card_dvd_of_injective f hf)
  ·
    have hle : φ.range ≤
        centralizer ({(QuotientGroup.mk x : X ⧸ primeComplementCore (G := X) p)} :
          Set (X ⧸ primeComplementCore (G := X) p)) := by
      rintro _ ⟨c, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h : (c : X) * x = x * c := Subgroup.mem_centralizer_singleton_iff.1 c.2
      change (QuotientGroup.mk (c : X) : X ⧸ primeComplementCore (G := X) p) * QuotientGroup.mk x =
        QuotientGroup.mk x * QuotientGroup.mk (c : X)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
    exact solvable_of_solvable_injective (Subgroup.inclusion_injective hle)

end CertificateInstances

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
