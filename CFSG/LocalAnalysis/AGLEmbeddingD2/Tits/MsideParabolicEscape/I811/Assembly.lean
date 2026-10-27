module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.Tools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.I811Leaves
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverTransport
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.Frattini
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.Socle
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Hall

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThreeCoreUniqueness.Helpers

theorem not_isPSolvable_inf_of_schreier (hSch : KFactCatalogSchreier) {Y : Type} [Group Y]
    [Finite Y] {K : Subgroup Y} [K.Normal] (hKs : IsSimpleGroup ↥K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup ↥K)
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) {Q : Subgroup Y}
    (hQ : ¬ CFSG.HallHigman.IsPSolvable 3 ↥Q) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(Q ⊓ K) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hOut : Group.IsSolvable (Outer ↥K) := hSch ↥K hKs hnab hcat
  set φ : Y →* MulAut ↥K := MulAut.conjNormal with hφ
  set ψ : Y →* Outer ↥K := (QuotientGroup.mk' (inner ↥K)).comp φ with hψ
  have hker : ∀ y : Y, ψ y = 1 → y ∈ K := by
    intro y hy
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    obtain ⟨k, hk⟩ := hy
    have hc : (k : Y)⁻¹ * y ∈ Subgroup.centralizer (K : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun f : MulAut ↥K => ((f ⟨x, hx⟩ : K) : Y)) hk
      simp only [MulAut.conj_apply, hφ, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h1
      calc x * ((k : Y)⁻¹ * y) = (k : Y)⁻¹ * ((k : Y) * x * (k : Y)⁻¹) * y := by group
        _ = (k : Y)⁻¹ * (y * x * y⁻¹) * y := by rw [h1]
        _ = (k : Y)⁻¹ * y * x := by group
    rw [hC, Subgroup.mem_bot] at hc
    have : y = k := by
      have := congrArg (fun z => (k : Y) * z) hc
      simpa using this
    rw [this]
    exact k.2
  intro hQK
  apply hQ
  set ψQ : ↥Q →* Outer ↥K := ψ.comp Q.subtype with hψQ
  have hkerle : (ψQ.ker).map Q.subtype ≤ Q ⊓ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.2, hker x hx⟩
  have hkerS : CFSG.HallHigman.IsPSolvable 3 ↥ψQ.ker := by
    have h1 := OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hQK hkerle
    exact OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective _ Q.subtype Q.subtype_injective).symm h1
  refine OrdinaryProofs.PSolvableClosure.isPSolvable_of_normal ψQ.ker hkerS ?_
  have hrs : Group.IsSolvable ↥ψQ.range := subgroup_solvable_of_solvable _
  exact MsideParabolicEscape.isPSolvable_of_isSolvable' Nat.prime_three
    (Group.isSolvable_of_isSolvable_injective
      (f := (QuotientGroup.quotientKerEquivRange ψQ).toMonoidHom)
      (QuotientGroup.quotientKerEquivRange ψQ).injective)

theorem isCatalogGroup_of_isKGroup_subgroup {Y : Type} [Group Y] (hY : CFSG.Open.IsKGroup Y)
    (K : Subgroup Y) (hKs : IsSimpleGroup ↥K) (hnab : ∃ a b : K, a * b ≠ b * a) :
    CFSG.Open.IsCatalogGroup ↥K := by
  have hK := CFSG.LocalAnalysis.GLTheoremB.isKGroup_subgroup' hY K
  have e : ↥K ⧸ (⊥ : Subgroup ↥K) ≃* ↥K := QuotientGroup.quotientBot
  have hs : IsSimpleGroup (↥K ⧸ (⊥ : Subgroup ↥K)) := e.isSimpleGroup_congr.2 hKs
  have hnab' : ∃ a b : ↥K ⧸ (⊥ : Subgroup ↥K), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  obtain ⟨i, ⟨f⟩⟩ := isCatalogGroup_of_isKGroup_quotient hK ⊥ hs hnab'
  exact ⟨i, ⟨e.symm.trans f⟩⟩

theorem card_sup_mul_card_inf {X : Type} [Group X] [Finite X] {A Y : Subgroup X}
    (hA : A ≤ Subgroup.normalizer (Y : Set X)) :
    Nat.card ↥(Y ⊔ A) * Nat.card ↥(Y ⊓ A) = Nat.card Y * Nat.card A := by
  have hYn : (Y.subgroupOf (Y ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hA)
  have h1 : A.relIndex (Y ⊔ A) = A.relIndex Y :=
    relIndex_sup_of_normal (J := Y ⊔ A) le_sup_right le_sup_left
  have e1 := Subgroup.relIndex_mul_card A (Y ⊔ A)
  have e2 := Subgroup.relIndex_mul_card A Y
  rw [inf_of_le_left le_sup_right, h1] at e1
  rw [← e1, ← e2, inf_comm]
  ring

theorem not_two_dvd_relIndex_core (hSz : KFactCoprimeThreeTwoPart) {X : Type} [Group X]
    [Finite X] (hK : CFSG.Open.IsKGroup X) (O : Subgroup X) [O.Normal] (hO3 : ¬ 3 ∣ Nat.card O)
    {MB TB : Subgroup X} (hTB : IsSylowTwoOf TB MB)
    (hns : ¬ CFSG.HallHigman.IsPSolvable 3 ↥MB)
    (hNM : ∀ Y : Subgroup X, Y ≤ MB → IsPGroup 3 Y → Y ≠ ⊥ →
      Subgroup.normalizer (Y : Set X) ≤ MB)
    (hbd : ∀ S : Subgroup X, IsPGroup 2 S → Nat.card S ≤ 8 * Nat.card TB) :
    ¬ 2 ∣ MB.relIndex O := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTBMB : TB ≤ MB := hTB.1
  have hTB2 : IsPGroup 2 TB := hTB.2.1
  have hOtop : ∀ g : X, g ∈ Subgroup.normalizer (O : Set X) := fun g => by
    rw [(Subgroup.normalizer_eq_top_iff).mpr inferInstance]
    exact Subgroup.mem_top g
  set U := TB ⊓ O with hUdef
  have hUsyl : IsSylowTwoOf U (O ⊓ MB) := by
    have h := isSylowTwoOf_inf_of_normal (N := O ⊓ MB) hTB inf_le_right
      (fun m hm => mem_normalizer_inf (hOtop m) (Subgroup.le_normalizer hm))
    have he : TB ⊓ (O ⊓ MB) = U := by
      rw [hUdef, ← inf_assoc]
      exact inf_of_le_left (inf_le_left.trans hTBMB)
    rwa [he] at h
  have hU2 : IsPGroup 2 U := hTB2.to_le inf_le_left
  have hUMB : U ≤ MB := inf_le_left.trans hTBMB
  have hUO : U ≤ O := inf_le_right
  set N₀ := MB ⊓ Subgroup.normalizer (U : Set X) with hN₀
  have hns₀ : ¬ CFSG.HallHigman.IsPSolvable 3 ↥N₀ := by
    intro h
    apply hns
    refine isPSolvable_of_isPSolvable_map O hO3 MB ?_
    have hle : MB.map (QuotientGroup.mk' O) ≤ N₀.map (QuotientGroup.mk' O) := by
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨n, hn, hnm⟩ := exists_mem_normalizer_of_isSylowTwoOf (X := MB) (N := O ⊓ MB)
        (fun x hx => mem_normalizer_inf (hOtop x) (Subgroup.le_normalizer hx)) hUsyl hm
      refine ⟨n⁻¹ * m, ⟨MB.mul_mem (MB.inv_mem hn.2) hm, hnm⟩, ?_⟩
      have hn1 : QuotientGroup.mk' O n = 1 := (QuotientGroup.eq_one_iff n).mpr hn.1
      rw [map_mul, map_inv, hn1, inv_one, one_mul]
    exact OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
      (OrdinaryProofs.PSolvableClosure.isPSolvable_map _ h) hle
  obtain ⟨k, hk⟩ := exists_isPerfect_derivedSeries ↥N₀
  set L₀ := (derivedSeries ↥N₀ k).map N₀.subtype with hL₀
  have eL : ↥(derivedSeries ↥N₀ k) ≃* ↥L₀ :=
    Subgroup.equivMapOfInjective _ N₀.subtype N₀.subtype_injective
  have : Group.IsPerfect ↥L₀ := Group.IsPerfect.ofSurjective (f := eL.toMonoidHom) eL.surjective
  have hL₀N : L₀ ≤ N₀ := Subgroup.map_subtype_le _
  have hnsL : ¬ CFSG.HallHigman.IsPSolvable 3 ↥L₀ := fun h =>
    not_isPSolvable_derivedSeries hns₀ k
      (OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv eL.symm h)
  have h3L : 3 ∣ Nat.card L₀ := by
    by_contra h
    exact hnsL (MsideParabolicEscape.isPSolvable_three_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h))
  obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' (G := L₀) 3 h3L
  set A₀ := Subgroup.zpowers (a₀ : X) with hA₀
  have hA₀L : A₀ ≤ L₀ := Subgroup.zpowers_le.mpr a₀.2
  have hA₀3 : IsPGroup 3 A₀ :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha₀, pow_one])
  have hA₀1 : A₀ ≠ ⊥ := by
    intro h
    have : Nat.card A₀ = 3 := by rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha₀]
    rw [h, Subgroup.card_bot] at this
    omega
  have hCA : Subgroup.centralizer (A₀ : Set X) ≤ MB :=
    (Subgroup.centralizer_le_normalizer _).trans
      (hNM A₀ ((hA₀L.trans hL₀N).trans inf_le_left) hA₀3 hA₀1)
  set J := O ⊓ Subgroup.normalizer (U : Set X) with hJ
  have hUJ : U ≤ J := le_inf hUO Subgroup.le_normalizer
  have hJU : J ≤ Subgroup.normalizer (U : Set X) := inf_le_right
  have hLJ : L₀ ≤ Subgroup.normalizer (J : Set X) := fun l hl =>
    mem_normalizer_inf (hOtop l) (Subgroup.le_normalizer ((hL₀N hl).2))
  have hJ3 : ¬ 3 ∣ Nat.card J := fun h => hO3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hTBJ : TB ≤ Subgroup.normalizer (J : Set X) := by
    intro t ht
    refine mem_normalizer_inf (hOtop t) (Subgroup.le_normalizer ?_)
    exact mem_normalizer_inf (Subgroup.le_normalizer ht) (hOtop t)
  have hJTB : J ⊓ TB = U := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.2, hx.1.1⟩
    · exact le_inf hUJ inf_le_left
  have hbdJ : ∀ S : Subgroup X, S ≤ J → IsPGroup 2 S → Nat.card S ≤ 8 * Nat.card U := by
    intro S hSJ hS2
    obtain ⟨V, hTBV, hV⟩ := exists_isSylowTwoOf_of_le (le_sup_right : TB ≤ J ⊔ TB) hTB2
    have hVJ : IsSylowTwoOf (V ⊓ J) J := isSylowTwoOf_inf_of_normal hV le_sup_left
      (sup_le Subgroup.le_normalizer hTBJ)
    have hSV : Nat.card S ≤ Nat.card ↥(V ⊓ J) := by
      rw [hVJ.card_eq]
      exact card_le_twoPart hSJ hS2
    have hTBn : TB ≤ Subgroup.normalizer ((V ⊓ J : Subgroup X) : Set X) := fun t ht =>
      mem_normalizer_inf (Subgroup.le_normalizer (hTBV ht)) (hTBJ ht)
    have hprod := card_sup_mul_card_inf hTBn
    have hinf : (V ⊓ J) ⊓ TB = U := by
      rw [inf_assoc, inf_comm J, ← inf_assoc, inf_of_le_right hTBV, inf_comm, hJTB]
    rw [hinf] at hprod
    have hle : Nat.card ↥((V ⊓ J) ⊔ TB) ≤ 8 * Nat.card TB :=
      hbd _ (hV.2.1.to_le (sup_le inf_le_left hTBV))
    have hUpos : 0 < Nat.card U := Nat.card_pos
    have hTBpos : 0 < Nat.card TB := Nat.card_pos
    have : Nat.card ↥(V ⊓ J) * Nat.card TB ≤ 8 * Nat.card U * Nat.card TB := by
      rw [← hprod]
      calc Nat.card ↥((V ⊓ J) ⊔ TB) * Nat.card U ≤ 8 * Nat.card TB * Nat.card U :=
            Nat.mul_le_mul_right _ hle
        _ = 8 * Nat.card U * Nat.card TB := by ring
    have := Nat.le_of_mul_le_mul_right this hTBpos
    omega
  have hC := not_two_dvd_relIndex_inf_of_perfect hSz hK hU2 hUMB
    (fun l hl => ((hL₀N hl).2)) (fun l hl => Subgroup.le_normalizer ((hL₀N hl).1))
    hA₀L hA₀3 J hUJ hJU hLJ hJ3 (fun x hx => hCA hx.2) hbdJ
  have hUJMB : IsSylowTwoOf U (J ⊓ MB) :=
    CFSG.QuasithinUnique.Lin2.isSylowTwoOf_of_le_of_le hUsyl (le_inf hUJ hUMB)
      (inf_le_inf_right _ inf_le_left)
  have hUJs : IsSylowTwoOf U J := by
    refine ⟨hUJ, hU2, fun h2 => ?_⟩
    change 2 ∣ U.relIndex J at h2
    rw [← Subgroup.relIndex_mul_relIndex U (J ⊓ MB) J (le_inf hUJ hUMB) inf_le_left] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact hUJMB.2.2 h
    · exact hC h
  have hUOs : IsSylowTwoOf U O := OrdinaryProofs.isSylowTwoOf_of_normalizer hUO hUJs
  intro h2
  apply hUOs.2.2
  change 2 ∣ U.relIndex O
  rw [← Subgroup.relIndex_mul_relIndex U (O ⊓ MB) O (le_inf hUO hUMB) inf_le_left]
  refine Dvd.dvd.mul_left ?_ _
  rwa [inf_comm, Subgroup.inf_relIndex_right]

theorem agl81I811Cyc_of_kfacts (hSch : KFactCatalogSchreier) (hSz : KFactCoprimeThreeTwoPart)
    (hW : KFactThreeRankOneOvergroup) : AGL81I811Cyc := by
  intro G _ _ hKp M hstr H hHtop hcyc hns T hT hbd
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKH : CFSG.Open.IsKGroup ↥H :=
    isKGroup_of_catalogSimpleSections (catalogSimpleSections_of_isKProper hKp H hHtop)
  set MB : Subgroup ↥H := (H ⊓ M).subgroupOf H with hMB
  have eMB : ↥MB ≃* ↥(H ⊓ M) := Subgroup.subgroupOfEquivOfLe inf_le_left
  have hns' : ¬ CFSG.HallHigman.IsPSolvable 3 ↥MB := fun h =>
    hns (OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv eMB h)
  have h3HM : 3 ∣ Nat.card ↥(H ⊓ M) := by
    by_contra h
    exact hns (MsideParabolicEscape.isPSolvable_three_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h))
  have hcycB := isCyclic_of_stronglyEmbedded hstr hcyc h3HM
  have hnsB : ¬ CFSG.HallHigman.IsPSolvable 3 ↥H := by
    intro h
    apply hns'
    have h' : CFSG.HallHigman.IsPSolvable 3 ↥(⊤ : Subgroup ↥H) :=
      OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
        Subgroup.topEquiv.symm h
    exact OrdinaryProofs.PSolvableClosure.isPSolvable_of_le h' le_top
  have hNM : ∀ Y : Subgroup ↥H, Y ≤ MB → IsPGroup 3 Y → Y ≠ ⊥ →
      Subgroup.normalizer (Y : Set ↥H) ≤ MB := by
    intro Y hYMB hY3 hY1 g hg
    have hg' : (g : G) ∈ Subgroup.normalizer ((Y.map H.subtype : Subgroup G) : Set G) :=
      (McLaughlin.TightPairAndPureRank.mem_normalizer_iff_map' Y g).mp hg
    have hYM : Y.map H.subtype ≤ M := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_subgroupOf.mp (hYMB hy)).2
    have hY1' : Y.map H.subtype ≠ ⊥ := by
      intro h
      apply hY1
      rw [eq_bot_iff]
      intro y hy
      have : (y : G) ∈ Y.map H.subtype := ⟨y, hy, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).mpr (Subtype.ext this)
    exact Subgroup.mem_subgroupOf.mpr
      ⟨g.2, normalizer_le_of_stronglyEmbedded Nat.prime_three hstr (hY3.map _) hYM hY1' hg'⟩
  have hTH : T ≤ H := hT.1.trans inf_le_left
  set TB : Subgroup ↥H := T.subgroupOf H with hTBdef
  have eTB : ↥TB ≃* ↥T := Subgroup.subgroupOfEquivOfLe hTH
  have hTBcard : Nat.card TB = Nat.card T := Nat.card_congr eTB.toEquiv
  have hTB : IsSylowTwoOf TB MB := by
    refine ⟨fun x hx => Subgroup.mem_subgroupOf.mpr (hT.1 hx), hT.2.1.of_equiv eTB.symm, ?_⟩
    change ¬ 2 ∣ TB.relIndex MB
    rw [hTBdef, hMB, Subgroup.relIndex_subgroupOf inf_le_left]
    exact hT.2.2
  have hbdB : ∀ S : Subgroup ↥H, IsPGroup 2 S → Nat.card S ≤ 8 * Nat.card TB := by
    intro S hS
    have := hbd (S.map H.subtype) (Subgroup.map_subtype_le S) (hS.map _)
    rwa [Subgroup.card_map_of_injective H.subtype_injective, ← hTBcard] at this
  set O := primeComplementCore (G := ↥H) 3 with hOdef
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (primeComplementCore_coprime 3)
  have hodd2 := not_two_dvd_relIndex_core hSz hKH O hO3 hTB hns' hNM hbdB
  obtain ⟨K, hKn, hKs, hKnab, hKC, hK3⟩ := exists_simple_socle hcycB hnsB
  set π := QuotientGroup.mk' O with hπ
  have h3MB : 3 ∣ Nat.card MB := by rw [Nat.card_congr eMB.toEquiv]; exact h3HM
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := MB) 3 h3MB
  set A : Subgroup ↥H := Subgroup.zpowers (a : ↥H) with hAdef
  have hAMB : A ≤ MB := Subgroup.zpowers_le.mpr a.2
  have hA3 : Nat.card A = 3 := by rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha]
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by rw [hA3, pow_one])
  have hA1 : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA3
    omega
  have hNĀ : Subgroup.normalizer ((A.map π : Subgroup (↥H ⧸ O)) : Set (↥H ⧸ O)) ≤ MB.map π :=
    (normalizer_map_le_map_normalizer O hO3 hA3).trans (Subgroup.map_mono (hNM A hAMB hAp hA1))
  have hAO : A ⊓ O = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have h1 : Nat.card (A ⊓ O : Subgroup ↥H) ∣ 3 := hA3 ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (A ⊓ O : Subgroup ↥H) ∣ Nat.card O := Subgroup.card_dvd_of_le inf_le_right
    have h3 : Nat.card (A ⊓ O : Subgroup ↥H) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact h
      · exact absurd (h ▸ h2) hO3
    exact (Subgroup.card_eq_one.mp h3) ▸ hy
  have hĀ3 : Nat.card (A.map π) = 3 := by
    rw [hπ, OrdinaryProofs.card_map_mk_of_inf_eq_bot A O hAO, hA3]
  have hcycY : ∀ X : Subgroup (↥H ⧸ O), IsPGroup 3 X → IsCyclic X := by
    intro X hX
    obtain ⟨Wb, hW3, hWX⟩ := CFSG.AGLEmbeddingD2.exists_isPGroup_map_mk_eq_of_isPGroup O hX
    have := hcycB Wb hW3
    rw [← hWX]
    exact isCyclic_of_surjective ((QuotientGroup.mk' _).subgroupMap Wb)
      (MonoidHom.subgroupMap_surjective _ Wb)
  have hKMB : K ⊔ MB.map π = ⊤ := by
    have h := sup_normalizer_eq_top (K := K) hcycY hK3 hĀ3
    rw [eq_top_iff, ← h]
    exact sup_le_sup_left hNĀ K
  have hidx : MB.index = (MB.map π).relIndex K * MB.relIndex O := by
    have h1 := Subgroup.relIndex_mul_index (le_sup_left : MB ≤ MB ⊔ O)
    have h2 : MB.relIndex (MB ⊔ O) = MB.relIndex O := by
      rw [sup_comm]
      exact relIndex_sup_of_normal (J := ⊤) le_top le_top
    have h3 : (MB ⊔ O).index = (MB.map π).index := by
      rw [← Subgroup.index_comap_of_surjective (MB.map π) (QuotientGroup.mk'_surjective O),
        Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    have h4 : (MB.map π).index = (MB.map π).relIndex K := by
      rw [← Subgroup.relIndex_top_right, ← hKMB]
      exact relIndex_sup_of_normal (J := ⊤) le_top le_top
    rw [← h1, h2, h3, h4, mul_comm]
  have h16 : ¬ 16 ∣ MB.index := by
    intro h16
    obtain ⟨t, ht⟩ := hTB.2.1.exists_card_eq
    have hdvd : 2 ^ (t + 4) ∣ Nat.card ↥H := by
      rw [← MB.card_mul_index, pow_add]
      exact Nat.mul_dvd_mul (ht ▸ Subgroup.card_dvd_of_le hTB.1) (by norm_num; exact h16)
    obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
    have hb := hbdB S (IsPGroup.of_card hS)
    rw [hS, ht, pow_add] at hb
    have : 0 < 2 ^ t := by positivity
    nlinarith
  have hKKG : CFSG.Open.IsKGroup (↥H ⧸ O) := CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH O
  have hcatK := isCatalogGroup_of_isKGroup_subgroup hKKG K hKs hKnab
  have hĀK : A.map π ≤ K := hK3 _ hĀ3
  set AK : Subgroup ↥K := (A.map π).subgroupOf K with hAK
  set WK : Subgroup ↥K := (MB.map π).subgroupOf K with hWK
  have hAK3 : Nat.card AK = 3 := by
    rw [hAK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hĀK).toEquiv, hĀ3]
  have hcycK : ∀ X : Subgroup ↥K, IsPGroup 3 X → IsCyclic X := by
    intro X hX
    have := hcycY (X.map K.subtype) (hX.map _)
    exact OrdinaryProofs.isCyclic_of_map_injective K.subtype K.subtype_injective X
  have hNAK : Subgroup.normalizer (AK : Set ↥K) ≤ WK := by
    intro k hk
    have h1 := (McLaughlin.TightPairAndPureRank.mem_normalizer_iff_map' AK k).mp hk
    rw [hAK, Subgroup.map_subgroupOf_eq_of_le hĀK] at h1
    exact Subgroup.mem_subgroupOf.mpr (hNĀ h1)
  have hnsW : ¬ CFSG.HallHigman.IsPSolvable 3 ↥WK := by
    have hnsQ : ¬ CFSG.HallHigman.IsPSolvable 3 ↥(MB.map π) := fun h =>
      hns' (isPSolvable_of_isPSolvable_map O hO3 MB h)
    have h1 := not_isPSolvable_inf_of_schreier hSch hKs hKnab hcatK hKC hnsQ
    intro h
    apply h1
    rw [← Subgroup.subgroupOf_map_subtype]
    exact OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective) h
  have h16W : ¬ 16 ∣ WK.index := fun h =>
    h16 (hidx ▸ h.trans (Dvd.intro _ rfl))
  have hoddW := hW ↥K hKs hKnab hcatK hcycK AK WK hAK3 hNAK hnsW h16W
  have hodd1 : ¬ 2 ∣ (MB.map π).relIndex K := by
    change ¬ 2 ∣ WK.index
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hoddW
  refine ⟨hTH, hT.2.1, ?_⟩
  change ¬ 2 ∣ T.relIndex H
  rw [← Subgroup.relIndex_mul_relIndex T (H ⊓ M) H hT.1 inf_le_left]
  intro h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
  · exact hT.2.2 h
  · change 2 ∣ MB.index at h
    rw [hidx] at h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h' | h'
    · exact hodd1 h'
    · exact hodd2 h'

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811
