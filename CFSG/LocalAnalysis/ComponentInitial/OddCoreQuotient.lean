module

public import CFSG.LocalAnalysis.ComponentInitial.OddCoreCorrespondence
public import CFSG.LocalAnalysis.LyonsUnitaryFour.CentralHall

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {G : Type*} [Group G]

theorem pPrimeCore_le_of_isPGroup_quotient [Finite G] {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hGN : IsPGroup p (G ⧸ N)) : pPrimeCore p G ≤ N := fun d hd => by
  refine mem_of_coprime_orderOf hGN ?_
  rw [← Subgroup.orderOf_mk d hd]
  exact (pPrimeCore_coprime_card (p := p) (G := G)).coprime_dvd_right (orderOf_dvd_natCard _)

theorem le_pPrimeCore {p : ℕ} {N : Subgroup G} (hN : N.Normal)
    (hcop : Nat.Coprime p (Nat.card N)) : N ≤ pPrimeCore p G :=
  le_sSup ⟨hN, hcop⟩

theorem le_pCore {p : ℕ} {N : Subgroup G} (hN : N.Normal) (hp : IsPGroup p N) :
    N ≤ pCore p G :=
  le_sSup ⟨hN, hp⟩

theorem pPrimeCore_normal_intersection [Finite G] (p : ℕ) [Fact p.Prime] {N : Subgroup G}
    (hN : N.Normal) : (pPrimeCore p N).map N.subtype = N ⊓ pPrimeCore p G := by
  have := CFSG.LocalCores.prime_set_core_normal_intersection {q : Nat.Primes | q.val ≠ p} hN
  rwa [← CFSG.pPrimeCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore] at this

theorem pCore_normal_intersection [Finite G] (p : ℕ) [Fact p.Prime] {N : Subgroup G}
    (hN : N.Normal) : (pCore p N).map N.subtype = N ⊓ pCore p G := by
  have := CFSG.LocalCores.prime_set_core_normal_intersection {q : Nat.Primes | q.val = p} hN
  rwa [← CFSG.pCore_eq_piCore, ← CFSG.pCore_eq_piCore] at this

theorem mem_pPrimeCore_of_mem_center {p : ℕ} {z : G} (hz : z ∈ center G)
    (hcop : Nat.Coprime p (orderOf z)) : z ∈ pPrimeCore p G := by
  refine le_pPrimeCore (normal_of_le_center ((zpowers_le).2 hz)) ?_ (mem_zpowers z)
  rwa [Nat.card_zpowers]

theorem coprime_orderOf_of_mem_pPrimeCore [Finite G] {p : ℕ} [Fact p.Prime] {z : G}
    (hz : z ∈ pPrimeCore p G) : Nat.Coprime p (orderOf z) := by
  rw [← Subgroup.orderOf_mk z hz]
  exact (pPrimeCore_coprime_card (p := p) (G := G)).coprime_dvd_right (orderOf_dvd_natCard _)

section Correspondence

variable {B C : Type*} [Group B] [Group C] {I : Subgroup C}

theorem pPrimeCore_le_of_two_index [Finite C] [I.Normal] (hCI : IsPGroup 2 (C ⧸ I)) : pPrimeCore 2 C ≤ I :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  pPrimeCore_le_of_isPGroup_quotient hCI

theorem pPrimeCore_eq_subgroupOf [Finite C] [hI : I.Normal] (hCI : IsPGroup 2 (C ⧸ I)) :
    pPrimeCore 2 I = (pPrimeCore 2 C).subgroupOf I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := pPrimeCore_normal_intersection 2 hI
  rw [inf_eq_right.2 (pPrimeCore_le_of_two_index hCI)] at h
  rw [← h]
  exact (Subgroup.comap_map_eq_self_of_injective I.subtype_injective _).symm

variable {f : B →* I}

theorem map_pPrimeCore_le [Finite B] (hf : Function.Surjective f) :
    (pPrimeCore 2 B).map f ≤ pPrimeCore 2 I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pPrimeCore ((pPrimeCore_normal (p := 2) (G := B)).map f hf)
    ((pPrimeCore_coprime_card (p := 2) (G := B)).coprime_dvd_right (Subgroup.card_map_dvd _ _))

theorem mem_ker_of_isPGroup [Finite I] {w : B} (hw : f w ∈ pPrimeCore 2 I) {k : ℕ}
    (hk : w ^ 2 ^ k = 1) : w ∈ f.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf (f w) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
  have h2 := coprime_orderOf_of_mem_pPrimeCore hw
  rw [MonoidHom.mem_ker, ← orderOf_eq_one_iff]
  exact ((h2.pow_left k).symm).eq_one_of_dvd h1

theorem pPrimeCore_le_map [Finite B] [Finite I] (hf : Function.Surjective f)
    (hK : f.ker ≤ center B) : pPrimeCore 2 I ≤ (pPrimeCore 2 B).map f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := (pPrimeCore 2 I).comap f with hW
  have hWn : W.Normal := (pPrimeCore_normal (p := 2) (G := I)).comap f
  obtain ⟨P⟩ : Nonempty (Sylow 2 W) := inferInstance
  have hPker : ∀ a ∈ (P : Subgroup W), (a : B) ∈ f.ker := by
    intro a ha
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨a, ha⟩
    refine mem_ker_of_isPGroup a.2 (k := k) ?_
    have := congrArg (fun x : (P : Subgroup W) => ((x : W) : B)) hk
    simpa using this
  have hPcen : (P : Subgroup W) ≤ center W := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext ((Subgroup.mem_center_iff.1 (hK (hPker a ha))) w)
  obtain ⟨V, hVcard, hsup, -, -, hVchar, -⟩ :=
    CFSG.LyonsUnitaryFour.central_hall_direct_complement (P : Subgroup W) hPcen
      (Sylow.card_coprime_index P)
  have hV0n : (V.map W.subtype).Normal := by
    have := hWn
    have := hVchar
    exact ConjAct.normal_of_characteristic_of_normal
  have hV0R : V.map W.subtype ≤ pPrimeCore 2 B := by
    refine le_pPrimeCore hV0n ?_
    rw [Subgroup.card_map_of_injective W.subtype_injective, hVcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (Sylow.not_dvd_index P)
  intro d hd
  obtain ⟨b, rfl⟩ := hf d
  have hbW : b ∈ W := hd
  have hPn : (P : Subgroup W).Normal := normal_of_le_center hPcen
  have hmem : (⟨b, hbW⟩ : W) ∈ (P : Subgroup W) ⊔ V := hsup ▸ mem_top _
  obtain ⟨a, ha, v, hv, hav⟩ := Subgroup.mem_sup_of_normal_left.1 hmem
  refine ⟨v, hV0R ⟨v, hv, rfl⟩, ?_⟩
  have hfa : f a = 1 := hPker a ha
  have hb : b = (a : B) * (v : B) := (congrArg Subtype.val hav).symm
  rw [hb, map_mul, hfa, one_mul]

theorem pPrimeCore_inf_ker [Finite B] (hK : f.ker ≤ center B) :
    pPrimeCore 2 B ⊓ f.ker = (pPrimeCore 2 f.ker).map f.ker.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro x hx
    obtain ⟨hxR, hxK⟩ := Subgroup.mem_inf.1 hx
    have hle : (pPrimeCore 2 B).subgroupOf f.ker ≤ pPrimeCore 2 f.ker := by
      refine le_pPrimeCore inferInstance ?_
      have h1 : Nat.card ((pPrimeCore 2 B).subgroupOf f.ker) =
          Nat.card ↥(pPrimeCore 2 B ⊓ f.ker) := by
        rw [← Subgroup.subgroupOf_map_subtype,
          Subgroup.card_map_of_injective f.ker.subtype_injective]
      rw [h1]
      exact (pPrimeCore_coprime_card (p := 2) (G := B)).coprime_dvd_right
        (Subgroup.card_dvd_of_le inf_le_left)
    exact ⟨⟨x, hxK⟩, hle hxR, rfl⟩
  · refine le_inf ?_ (map_subtype_le _)
    refine le_pPrimeCore (normal_of_le_center ((map_subtype_le _).trans hK)) ?_
    rw [Subgroup.card_map_of_injective f.ker.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := f.ker)

end Correspondence

abbrev quotientInclusion {C : Type*} [Group C] (I D : Subgroup C) [D.Normal] :
    I ⧸ D.subgroupOf I →* C ⧸ D :=
  QuotientGroup.map (D.subgroupOf I) D I.subtype le_rfl

theorem central_quotient_normal_two_index_odd_core_correspondence {B C : Type*} [Group B]
    [Group C] [Finite B] [Finite C] {I : Subgroup C} [hI : I.Normal] (hCI : IsPGroup 2 (C ⧸ I))
    (f : B →* I) (hf : Function.Surjective f) (hK : f.ker ≤ center B) :
    let R := pPrimeCore 2 B
    let D := pPrimeCore 2 C
    let K := f.ker
    D ≤ I ∧ (pPrimeCore 2 I).map I.subtype = D ∧ (R.map f).map I.subtype = D ∧
      (D.subgroupOf I).comap f = R ⊔ K ∧ R ⊓ K = (pPrimeCore 2 K).map K.subtype ∧
      ∃ β : B ⧸ R →* I ⧸ D.subgroupOf I,
        (∀ b : B, β b = ((f b : I) : I ⧸ D.subgroupOf I)) ∧ Function.Surjective β ∧
        β.ker = K.map (QuotientGroup.mk' R) ∧ β.ker ≤ center (B ⧸ R) ∧ IsPGroup 2 β.ker ∧
        (∀ S : Sylow 2 K,
          Function.Injective
            ((QuotientGroup.mk' R).comp (K.subtype.comp (S : Subgroup K).subtype)) ∧
          ((QuotientGroup.mk' R).comp (K.subtype.comp (S : Subgroup K).subtype)).range =
            β.ker) ∧
        Function.Injective (quotientInclusion I D) ∧
        (quotientInclusion I D).range = I.map (QuotientGroup.mk' D) ∧
        (pCore 2 (B ⧸ R)).map β = pCore 2 (I ⧸ D.subgroupOf I) ∧
        pCore 2 (I ⧸ D.subgroupOf I) = (pCore 2 (C ⧸ D)).comap (quotientInclusion I D) ∧
        ((pCore 2 (C ⧸ D)).comap (quotientInclusion I D)).comap β = pCore 2 (B ⧸ R) ∧
        β.ker ≤ pCore 2 (B ⧸ R) ∧
      (Group.IsSolvable B ↔ Group.IsSolvable C) := by
  intro R D K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDI : D ≤ I := pPrimeCore_le_of_two_index hCI
  have hDsub : pPrimeCore 2 I = D.subgroupOf I := pPrimeCore_eq_subgroupOf hCI
  have hDmap : (pPrimeCore 2 I).map I.subtype = D := by
    rw [hDsub, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hDI]
  have hRf : R.map f = pPrimeCore 2 I :=
    le_antisymm (map_pPrimeCore_le hf) (pPrimeCore_le_map hf hK)
  have hW : (D.subgroupOf I).comap f = R ⊔ K := by
    rw [← hDsub, ← hRf, Subgroup.comap_map_eq]
  have hRle : R ≤ (D.subgroupOf I).comap f := hW ▸ le_sup_left
  set β := QuotientGroup.map R (D.subgroupOf I) f hRle with hβ
  have hβsurj : Function.Surjective β :=
    QuotientGroup.map_surjective_of_surjective _ _ _
      ((QuotientGroup.mk_surjective).comp hf) hRle
  have hβker : β.ker = K.map (QuotientGroup.mk' R) := by
    rw [hβ, QuotientGroup.ker_map, hW, Subgroup.map_sup, QuotientGroup.map_mk'_self,
      bot_sup_eq]
  have hβcen : β.ker ≤ center (B ⧸ R) := by
    rw [hβker]
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective R x
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 (hK hk) b]
  have hβ2 : IsPGroup 2 β.ker := by
    rintro ⟨y, hy⟩
    have hy' := hβker ▸ hy
    obtain ⟨k, hk, rfl⟩ := hy'
    obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
    refine ⟨e, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine mem_pPrimeCore_of_mem_center (Subgroup.pow_mem _ (hK hk) _) ?_
    have hdvd : orderOf (k ^ 2 ^ e) ∣ m :=
      orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, ← hn, pow_orderOf_eq_one])
    exact (Nat.coprime_two_left.2 hm).coprime_dvd_right hdvd
  have hsyl : ∀ S : Sylow 2 K,
      Function.Injective
        ((QuotientGroup.mk' R).comp (K.subtype.comp (S : Subgroup K).subtype)) ∧
      ((QuotientGroup.mk' R).comp (K.subtype.comp (S : Subgroup K).subtype)).range =
        β.ker := by
    intro S
    refine ⟨?_, ?_⟩
    · rw [injective_iff_map_eq_one]
      intro s hs
      have hsR : ((s : K) : B) ∈ R := by
        simpa [QuotientGroup.eq_one_iff] using hs
      obtain ⟨k, hk⟩ := S.isPGroup' s
      have h1 : orderOf ((s : K) : B) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
        have := congrArg (fun x : (S : Subgroup K) => ((x : K) : B)) hk
        simpa using this)
      have h3 : orderOf ((s : K) : B) = 1 :=
        (((coprime_orderOf_of_mem_pPrimeCore hsR).pow_left k).symm).eq_one_of_dvd h1
      rw [orderOf_eq_one_iff] at h3
      exact Subtype.ext (Subtype.ext h3)
    · let ψ : K →* β.ker := ((QuotientGroup.mk' R).comp K.subtype).codRestrict β.ker
        (fun k => by rw [hβker]; exact ⟨k, k.2, rfl⟩)
      have hψ : Function.Surjective ψ := by
        rintro ⟨y, hy⟩
        have hy' := hβker ▸ hy
        obtain ⟨k, hk, rfl⟩ := hy'
        exact ⟨⟨k, hk⟩, rfl⟩
      have hS' : (S : Subgroup K).map ψ = ⊤ := by
        have hT : IsPGroup 2 (⊤ : Subgroup β.ker) := hβ2.to_subgroup ⊤
        have := (Sylow.mapSurjective hψ S).is_maximal' hT le_top
        rw [Sylow.coe_mapSurjective] at this
        exact this.symm
      have hφ : (QuotientGroup.mk' R).comp (K.subtype.comp (S : Subgroup K).subtype) =
          β.ker.subtype.comp (ψ.comp (S : Subgroup K).subtype) := by
        ext; rfl
      rw [hφ, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype, hS',
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set ι := quotientInclusion I D with hι
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : ((i : C) : C ⧸ D) = 1 := hx
    rw [QuotientGroup.eq_one_iff] at h1
    exact (QuotientGroup.eq_one_iff i).2 h1
  have hιrange : ι.range = I.map (QuotientGroup.mk' D) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨i, i.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨((⟨c, hc⟩ : I) : I ⧸ D.subgroupOf I), rfl⟩
  have hpcore : pCore 2 (I ⧸ D.subgroupOf I) = (pCore 2 (C ⧸ D)).comap ι := by
    have hN : (ι.range).Normal :=
      hιrange ▸ hI.map (QuotientGroup.mk' D) (QuotientGroup.mk'_surjective D)
    have hint := pCore_normal_intersection 2 hN
    let e : (I ⧸ D.subgroupOf I) ≃* ι.range := MonoidHom.ofInjective hιinj
    have hpe := CFSG.pCore_map_iso 2 e
    ext x
    constructor
    · intro hx
      have h1 : e x ∈ pCore 2 ι.range := hpe ▸ ⟨x, hx, rfl⟩
      have h2 : ((e x : ι.range) : C ⧸ D) ∈ ι.range ⊓ pCore 2 (C ⧸ D) := hint ▸ ⟨e x, h1, rfl⟩
      have h3 := (Subgroup.mem_inf.1 h2).2
      rw [MonoidHom.ofInjective_apply] at h3
      exact h3
    · intro hx
      have h2 : ι x ∈ ι.range ⊓ pCore 2 (C ⧸ D) := ⟨⟨x, rfl⟩, hx⟩
      rw [← hint] at h2
      obtain ⟨y, hy, hyx⟩ := h2
      have hye : y = e x := Subtype.ext (by rw [MonoidHom.ofInjective_apply]; exact hyx)
      rw [hye, ← hpe] at hy
      obtain ⟨z, hz, hzx⟩ := hy
      rw [← e.injective hzx]
      exact hz
  have hkerP : β.ker ≤ pCore 2 (B ⧸ R) := le_pCore β.normal_ker hβ2
  have hQ : (pCore 2 (I ⧸ D.subgroupOf I)).comap β ≤ pCore 2 (B ⧸ R) :=
    le_pCore ((pCore_normal (p := 2)).comap β)
      (IsPGroup.comap_of_ker_isPGroup pCore_isPGroup β hβ2)
  have hPmap : (pCore 2 (B ⧸ R)).map β = pCore 2 (I ⧸ D.subgroupOf I) := by
    apply le_antisymm
    · exact le_pCore ((pCore_normal (p := 2)).map β hβsurj) (pCore_isPGroup.map β)
    · calc pCore 2 (I ⧸ D.subgroupOf I)
          = ((pCore 2 (I ⧸ D.subgroupOf I)).comap β).map β :=
            (Subgroup.map_comap_eq_self_of_surjective hβsurj _).symm
        _ ≤ _ := Subgroup.map_mono hQ
  have hPcomap : ((pCore 2 (C ⧸ D)).comap ι).comap β = pCore 2 (B ⧸ R) := by
    rw [← hpcore]
    exact le_antisymm hQ (hPmap ▸ Subgroup.le_comap_map β _)
  have hKsolv : Group.IsSolvable K :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.1 (hK b.2) a)
  have hsolv : Group.IsSolvable B ↔ Group.IsSolvable C := by
    constructor
    · intro hB
      have hIs : Group.IsSolvable I := Group.isSolvable_of_surjective hf
      have hCIs : Group.IsSolvable (C ⧸ I) := by
        have := hCI.isNilpotent
        infer_instance
      exact Group.isSolvable_of_ker_le_range I.subtype (QuotientGroup.mk' I)
        (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
    · intro hC
      have hIs : Group.IsSolvable I :=
        Group.isSolvable_of_isSolvable_injective I.subtype_injective
      exact Group.isSolvable_of_ker_le_range K.subtype f (by rw [Subgroup.range_subtype])
  exact ⟨hDI, hDmap, by rw [hRf, hDmap], hW, pPrimeCore_inf_ker hK, β, fun b => rfl, hβsurj,
    hβker, hβcen, hβ2, hsyl, hιinj, hιrange, hPmap, hpcore, hPcomap, hkerP, hsolv⟩

end CFSG.LocalAnalysis.ComponentInitial
