module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Transfer
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Reduce
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeG2
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.ToralCensus CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus

section Group

variable {G : Type*} [Group G]

theorem exists_conj_le_of_sup [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L R : Subgroup G} (hR : IsPGroup 2 R) (hLR : L ≤ Subgroup.normalizer (R : Set G))
    {A : Subgroup G} (hA : A ≤ L ⊔ R) (hAp : IsPGroup p A) :
    ∃ g ∈ L ⊔ R, ∀ a ∈ A, g * a * g⁻¹ ∈ L := by
  have : Fact p.Prime := ⟨hp⟩
  set N := L ⊔ R with hN
  set L' : Subgroup N := L.subgroupOf N with hL'
  have hidx : L'.index ∣ Nat.card R := by
    have h1 := card_sup_dvd_mul L R hLR
    have h2 : Nat.card L' = Nat.card L :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
    have h3 := L'.card_mul_index
    rw [h2] at h3
    rw [← hN, ← h3] at h1
    exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h1
  have hpL : ¬ p ∣ L'.index := by
    obtain ⟨a, ha⟩ := hR.exists_card_eq
    intro hd
    have h2 := (hd.trans hidx).trans (by rw [ha])
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
  obtain ⟨S₁⟩ : Nonempty (Sylow p L') := inferInstance
  set S : Subgroup N := (S₁ : Subgroup L').map L'.subtype with hS
  have hSp : IsPGroup p S := S₁.isPGroup'.map _
  have hSi : ¬ p ∣ S.index := by
    rw [hS, Subgroup.index_map_subtype]
    exact fun hd => (hp.dvd_mul.1 hd).elim S₁.not_dvd_index hpL
  obtain ⟨Q, hQ⟩ := (hAp.comap_subtype (K := N)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N Q (hSp.toSylow hSi)
  refine ⟨g, g.2, fun a ha => ?_⟩
  have hgu : g * (⟨a, hA ha⟩ : N) * g⁻¹ ∈ S := by
    have : g * (⟨a, hA ha⟩ : N) * g⁻¹ ∈ ((hSp.toSylow hSi : Sylow p N) : Subgroup N) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨_, hQ (Subgroup.mem_subgroupOf.2 ha), rfl⟩
    simpa using this
  obtain ⟨y, -, hy⟩ := hgu
  have hyL : ((y : N) : G) ∈ L := Subgroup.mem_subgroupOf.1 y.2
  have hye : ((y : N) : G) = g * a * (g : G)⁻¹ := by
    have := congrArg Subtype.val hy
    simpa using this
  rwa [hye] at hyL

end Group

section Single

variable {K : Type*} {Y : Type} [Group K] [Group Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem exists_conj_le_rankOne_of_single [Finite K] [Finite Y] (h : BorelQuotient D n H π M)
    {J : Subgroup Y} (hBJ : (borel D H).map π ≤ J) {i : Fin D.rank}
    (hI : negIndices D (J.comap π) = {i}) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup Y} (hA : A ≤ perfectJoin J) (hAp : IsPGroup p A) :
    ∃ g ∈ J, ∀ a ∈ A, g * a * g⁻¹ ∈ (rankOne D.rootGroup i).map π := by
  have hBA : borel D H ≤ J.comap π := fun b hb => hBJ ⟨b, hb, rfl⟩
  have hi : i ∈ negIndices D (J.comap π) := by rw [hI]; rfl
  set T := (⨆ k, H k).map π with hT
  set R := (posUnipotentExcept D i).map π with hR
  set Li := (rankOne D.rootGroup i).map π with hLi
  have hLiJ : Li ≤ J :=
    (Subgroup.map_mono (rankOne_le_of_mem_negIndices hBA hi)).trans (Subgroup.map_comap_le _ _)
  have hRJ : R ≤ J := (Subgroup.map_mono ((posUnipotentExcept_le_posUnipotent i).trans
    posUnipotent_le_borel)).trans hBJ
  have hJ : J ≤ T ⊔ (Li ⊔ R) := by
    rw [eq_map_borel_sup_of_le h.ct h.extras h.surj hBJ]
    refine sup_le ?_ (iSup₂_le fun j hj => ?_)
    · rw [CFSG.LieType.Steinberg.borel, Subgroup.map_sup, posUnipotent_eq_sup h.extras i,
        Subgroup.map_sup]
      refine sup_le le_sup_left (sup_le (le_sup_of_le_right le_sup_right) ?_)
      exact le_sup_of_le_right (le_sup_of_le_left (Subgroup.map_mono le_sup_left))
    · rw [hI] at hj
      rw [Set.mem_singleton_iff.1 hj]
      exact le_sup_of_le_right le_sup_left
  have hTN : T ≤ Subgroup.normalizer ((Li ⊔ R : Subgroup Y) : Set Y) := fun t ht =>
    ParabAutIrr.mem_normalizer_sup
      (((Subgroup.map_mono (iSup_torus_le_normalizer_rankOne h.ct i)).trans
        (Subgroup.le_normalizer_map π)) ht)
      (((Subgroup.map_mono (iSup_torus_le_normalizer_posUnipotentExcept h.ct i)).trans
        (Subgroup.le_normalizer_map π)) ht)
  have hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.torus_mul_comm ha hb]
  have hPN := perfectJoin_le_of_le_sup hJ hTN hTc
  have hR2 : IsPGroup 2 R := ((isPGroup_iSup_pos h.extras h.pGroup).to_le
    (posUnipotentExcept_le_posUnipotent i)).map π
  have hLR : Li ≤ Subgroup.normalizer (R : Set Y) :=
    (Subgroup.map_mono (rankOne_le_normalizer_posUnipotentExcept h.ct h.extras i)).trans
      (Subgroup.le_normalizer_map π)
  obtain ⟨g, hg, hga⟩ := exists_conj_le_of_sup hp hp2 hR2 hLR (fun a ha => hPN (hA ha)) hAp
  exact ⟨g, sup_le hLiJ hRJ hg, hga⟩

end Single

section Cyclic

open scoped IsMulCommutative

theorem sylow_isCyclic_of_surjective {A B : Type*} [Group A] [Group B] [Finite A] {p : ℕ}
    [Fact p.Prime] {f : A →* B} (hf : Function.Surjective f)
    (h : ∀ P : Sylow p A, IsCyclic ↥(P : Subgroup A)) :
    ∀ Q : Sylow p B, IsCyclic ↥(Q : Subgroup B) := by
  intro Q
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hf p Q
  have := h P
  rw [Sylow.coe_mapSurjective]
  exact isCyclic_of_surjective (f.subgroupMap (P : Subgroup A)) (f.subgroupMap_surjective _)

theorem isCyclic_of_le_range {S X : Type*} [Group S] [Group X] [Finite S] {p : ℕ}
    [Fact p.Prime] (ψ : S →* X) (hS : ∀ P : Sylow p S, IsCyclic ↥(P : Subgroup S))
    {Q : Subgroup X} (hQ : Q ≤ ψ.range) (hQp : IsPGroup p Q) : IsCyclic Q := by
  have hsurj : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  have hSyl := sylow_isCyclic_of_surjective (p := p) hsurj hS
  have hQ' : IsPGroup p (Q.subgroupOf ψ.range) := hQp.comap_subtype
  obtain ⟨P, hP⟩ := hQ'.exists_le_sylow
  have hPc : IsCyclic ↥(P : Subgroup ↥ψ.range) := hSyl P
  have h1 : IsCyclic ↥((Q.subgroupOf ψ.range).subgroupOf (P : Subgroup ↥ψ.range)) :=
    Subgroup.isCyclic _
  have h2 : IsCyclic ↥(Q.subgroupOf ψ.range) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hP).toMonoidHom
      (MulEquiv.surjective _)
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQ).toMonoidHom
    (MulEquiv.surjective _)

end Cyclic

section SL2

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sylow_isCyclic_sl2 (h4 : 4 ≤ Nat.card F) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ P : Sylow p (Matrix.SpecialLinearGroup (Fin 2) F),
      IsCyclic ↥(P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hF⟩ : ∃ m : ℕ, Nat.card F = 2 ^ m := by
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨m, -, hm⟩ := FiniteField.card (K := F) 2
    exact ⟨m, by rw [Nat.card_eq_fintype_card]; exact hm⟩
  by_cases h7 : 7 ≤ Nat.card F
  · have hcop : Nat.Coprime p (Nat.card F) := by
      rw [hF]
      exact Nat.Coprime.pow_right m ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have hP := CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F hF h7 p hp2 hcop
    let e : Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
      (QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq sl2_center_eq_bot.symm))
    exact sylow_isCyclic_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective hP
  · have h4' : Nat.card F = 4 := by
      have hm : 2 ≤ m := by
        by_contra hlt
        interval_cases m <;> omega
      have hm' : m ≤ 2 := by
        by_contra hlt
        have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases m
      simpa using hF
    have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
      rw [card_sl2, h4']; norm_num
    intro P
    refine isCyclic_of_isPGroup_of_not_sq_dvd hp ?_ P.isPGroup'
    rw [hcard]
    intro hd
    have hle : p ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) hd
    have hp7 : p ≤ 7 := by nlinarith
    have hp2' := hp.two_le
    interval_cases p <;> omega

end SL2

section G2


theorem exists_rankOne_eq_range_g2 {F : Type} [Field F] [Finite F] [CharP F 2]
    (i : Fin (Tag.rank .G2)) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* adjointGroup .G2 F,
      rankOne (g2Datum F).rootGroup i = φ.range := by
  obtain ⟨φ, -, hx, hy⟩ := g2_exists_sl2_hom (K := F) i
  exact ⟨φ, rankOne_eq_range_of_sl2
    (adjDatum_isParametrization (F := rootOperatorFamily .G2) (K := F)
      (RootSystem.ofCartan (g2Datum F).isFiniteType (g2Datum F).divisible)
      (adjDatum_roots (rootOperatorFamily .G2) F))
    (fun c => (hx c).trans (xPar_simple i c).symm)
    (fun c => (hy c).trans (xPar_neg_simple i c).symm)⟩

theorem isCyclic_pSubgroup_perfectJoin_g2 {F : Type} [Field F] [Finite F] [CharP F 2] {X : Type}
    [Group X] [Finite X] (e : X ≃* AdjointQuotient .G2 F) (hq4 : 4 ≤ Nat.card F) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (S : Sylow 2 X) {J : Subgroup X}
    (hNJ : Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ J)
    (hJN : J ≠ Subgroup.normalizer ((S : Subgroup X) : Set X)) (hJtop : J ≠ ⊤)
    {A : Subgroup X} (hA : A ≤ perfectJoin J) (hAp : IsPGroup p A) : IsCyclic A := by
  have : Finite ↥(adjointGroup .G2 F) := generated_group_finite .G2 F
  have h := borelQuotient_g2 e
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq S
  have hQ : BorelQuotient (g2Datum F) (weylElement .G2 F) (torus (τ := .G2) F) π'
      (Nat.card F - 1) :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel (g2Datum F) (torus (τ := .G2) F)).map π' ≤ J := by
    rw [← hNπ]
    exact hNJ
  have hBA : borel (g2Datum F) (torus (τ := .G2) F) ≤ J.comap π' := fun b hb => hBJ ⟨b, hb, rfl⟩
  have hne : J.comap π' ≠ borel (g2Datum F) (torus (τ := .G2) F) := by
    intro he
    apply hJN
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ']
  obtain ⟨i, hi⟩ := negIndices_nonempty_of_ne hQ.ct hQ.extras hBA hne
  obtain ⟨k, hk⟩ := LieOut.exists_node_not_mem_negIndices hQ hBJ hJtop
  have hik : i ≠ k := fun e => hk (e ▸ hi)
  obtain ⟨-, hrest⟩ := g2_nodes hik
  have hI : negIndices (g2Datum F) (J.comap π') = {i} := by
    ext c
    exact ⟨fun hc => hrest c fun e => hk (e ▸ hc), fun hc => hc ▸ hi⟩
  obtain ⟨g, -, hga⟩ := exists_conj_le_rankOne_of_single hQ hBJ hI hp hp2 hA hAp
  obtain ⟨φ, hφ⟩ := exists_rankOne_eq_range_g2 (F := F) i
  have : Fact p.Prime := ⟨hp⟩
  set c : X →* X := (MulAut.conj g).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  have hle : A.map c ≤ (π'.comp φ).range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := hga a ha
    rw [hφ] at hb
    obtain ⟨s, rfl⟩ := hb
    exact ⟨s, hba⟩
  have hcyc := isCyclic_of_le_range (p := p) (π'.comp φ)
    (fun P => sylow_isCyclic_sl2 hq4 hp hp2 P) hle (hAp.map c)
  exact isCyclic_of_surjective (Subgroup.equivMapOfInjective A c hcinj).symm.toMonoidHom
    (MulEquiv.surjective _)

theorem isCyclic_pSubgroup_perfectJoin_of_isLieOf_g2 {X : Type} [Group X] [Finite X]
    (hX : IsLieOf IdxG2 X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (S : Sylow 2 X)
    {J : Subgroup X} (hNJ : Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ J)
    (hJN : J ≠ Subgroup.normalizer ((S : Subgroup X) : Set X)) (hJtop : J ≠ ⊤)
    {A : Subgroup X} (hA : A ≤ perfectJoin J) (hAp : IsPGroup p A) : IsCyclic A := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hX
  cases d with
  | G2 q =>
    change q.p = 2 at hd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
      (GaloisField q.p q.exponent) hK
    have hq3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hq4 : 4 ≤ Nat.card (GaloisField q.p q.exponent) := by
      rw [hK, TauCeti.PrimePower.card_def, hd]
      rw [TauCeti.PrimePower.card_def, hd] at hq3
      have hf : 2 ≤ q.exponent := by
        by_contra hf
        have : q.exponent = 1 := by have := q.exponent_pos; omega
        rw [this] at hq3
        omega
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf
    exact isCyclic_pSubgroup_perfectJoin_g2 (e.trans b.symm) hq4 hp hp2 S hNJ hJN hJtop hA hAp
  | _ => exact hd.elim

section Component

variable {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}

theorem isCyclic_of_pGroup_perfect_le_g2 (h : CompParabE L J)
    (hG : IsLieOf IdxG2 (↥L ⧸ Subgroup.center ↥L)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {V : Subgroup Y} (hVJ : V ≤ J)
    (hV : ⁅V, V⁆ = V) {Q : Subgroup Y} (hQV : Q ≤ V) (hQ : IsPGroup p Q) : IsCyclic Q := by
  have hJL : J ≤ L := h.parab.1
  obtain ⟨S₀, hNJ, hJN, hJtop⟩ := exists_sylow_parab_central h
  set ψ : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hψ
  have hQL : Q ≤ L := hQV.trans (hVJ.trans hJL)
  set f : ↥Q →* ↥L ⧸ Subgroup.center ↥L := ψ.comp (Subgroup.inclusion hQL) with hf
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    have hzc : (⟨(q : Y), hQL q.2⟩ : ↥L) ∈ Subgroup.center ↥L := by
      have := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hq)
      exact this
    obtain ⟨k, hk⟩ := hQ q
    have h1 : orderOf (⟨(q : Y), hQL q.2⟩ : ↥L) ∣ Nat.card (Subgroup.center ↥L) := by
      have := orderOf_dvd_natCard (⟨(⟨(q : Y), hQL q.2⟩ : ↥L), hzc⟩ : Subgroup.center ↥L)
      simpa using this
    have h2 : orderOf (⟨(q : Y), hQL q.2⟩ : ↥L) ∣ p ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk
      exact Subtype.ext (by simpa using this)
    have hcop : Nat.Coprime (p ^ k) (Nat.card (Subgroup.center ↥L)) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpZ)
    have h3 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
    have := orderOf_eq_one_iff.1 h3
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    simpa using congrArg Subtype.val this
  have hVbar : ((V.subgroupOf L).map ψ) ≤ perfectJoin (jBar L J) := by
    refine le_perfectJoin (Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.2 (hVJ (Subgroup.mem_subgroupOf.1 hx))) ?_
    rw [← Subgroup.map_commutator]
    congr 1
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (hVJ.trans hJL),
      hV]
  have hrange : f.range ≤ perfectJoin (jBar L J) := by
    rintro _ ⟨q, rfl⟩
    refine hVbar ⟨⟨(q : Y), hQL q.2⟩, Subgroup.mem_subgroupOf.2 (hQV q.2), rfl⟩
  have hpg : IsPGroup p ↥f.range := hQ.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hcyc := isCyclic_pSubgroup_perfectJoin_of_isLieOf_g2 hG hp hp2 S₀ hNJ hJN hJtop hrange hpg
  exact isCyclic_of_injective f.rangeRestrict (by
    intro a b hab
    exact hfinj (congrArg Subtype.val hab))

theorem false_of_elemAbelian_perfect_g2 (h : CompParabE L J)
    (hG : IsLieOf IdxG2 (↥L ⧸ Subgroup.center ↥L)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {V : Subgroup Y} (hVJ : V ≤ J)
    (hV : ⁅V, V⁆ = V) {E : Subgroup Y} (hEV : E ≤ V) (hE : IsPGroup p E)
    (hEc : p ^ 2 ∣ Nat.card E) (hEe : ∀ e ∈ E, e ^ p = 1) : False := by
  have hcyc := isCyclic_of_pGroup_perfect_le_g2 h hG hp hp2 hpZ hVJ hV hEV hE
  have hexp : Monoid.exponent E ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hEe x x.2)
  have hcard : Nat.card E ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact hexp
  have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos ((hEc.trans hcard))
  have := hp.two_le
  nlinarith

theorem false_of_card_sq_perfect_g2 (h : CompParabE L J)
    (hG : IsLieOf IdxG2 (↥L ⧸ Subgroup.center ↥L)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {V : Subgroup Y} (hVJ : V ≤ J)
    (hV : ⁅V, V⁆ = V) {E : Subgroup Y} (hEV : E ≤ V) (hEcard : Nat.card E = p ^ 2)
    (hEe : ∀ e ∈ E, e ^ p = 1) : False :=
  false_of_elemAbelian_perfect_g2 h hG hp hp2 hpZ hVJ hV hEV
    (have : Fact p.Prime := ⟨hp⟩
     IsPGroup.of_card hEcard)
    (by rw [hEcard]) hEe

end Component

end G2

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
