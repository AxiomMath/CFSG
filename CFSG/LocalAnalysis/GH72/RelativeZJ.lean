module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.Foundations.MaxCardThompson
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.Gorenstein.RelativeZJ
import CFSG.GroupTheory.ABGLocalTools.PStabilityDGroup
import CFSG.LinearAlgebra.LinearGroups.OddPStableActions

public section

namespace CFSG.GH72

open CFSG CFSG.ABGLocalTools Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

section Helpers

private theorem odd_card_of_isPGroup (hp : p ≠ 2) {H : Subgroup G} (hH : IsPGroup p H) :
    Odd (Nat.card H) := by
  have hpp : p.Prime := Fact.out
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH
  rw [hn]
  exact (hpp.odd_of_ne_two hp).pow

private theorem pCore_le_oddCore' (hp : p ≠ 2) (H : Type*) [Group H] [Finite H] :
    pCore p H ≤ oddCore H :=
  le_oddCore_of_normal inferInstance (odd_card_of_isPGroup hp pCore_isPGroup)

private theorem odd_card_sup_of_normal (hp : p ≠ 2) {N P : Subgroup G} [N.Normal]
    (hN : Odd (Nat.card N)) (hP : IsPGroup p P) : Odd (Nat.card (N ⊔ P : Subgroup G)) := by
  have h1 := Subgroup.relIndex_mul_card P (N ⊔ P)
  rw [inf_eq_left.mpr (le_sup_right : P ≤ N ⊔ P), relIndex_sup_eq_relIndex_of_normal N P] at h1
  rw [← h1]
  exact (Odd.of_dvd_nat hN (Subgroup.relIndex_dvd_card _ _)).mul (odd_card_of_isPGroup hp hP)

private theorem comap_le_oddCore {N : Subgroup G} [N.Normal] (hN : N ≤ oddCore G)
    (R : Subgroup (G ⧸ N)) [hR : R.Normal] (hodd : Odd (Nat.card R)) :
    R.comap (QuotientGroup.mk' N) ≤ oddCore G := by
  apply le_oddCore_of_normal (hR.comap _)
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R.comap (QuotientGroup.mk' N)) 2 h2
  have hxo : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe, hx]
  have h1 : orderOf (QuotientGroup.mk' N (x : G)) = 1 := by
    have hd1 : orderOf (QuotientGroup.mk' N (x : G)) ∣ 2 := hxo ▸ orderOf_map_dvd _ _
    have hd2 : orderOf (QuotientGroup.mk' N (x : G)) ∣ Nat.card R :=
      Subgroup.orderOf_dvd_natCard R (Subgroup.mem_comap.mp x.2)
    exact Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hodd) hd1 hd2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hdvd : orderOf (x : G) ∣ Nat.card (oddCore G) := Subgroup.orderOf_dvd_natCard _ (hN h1)
  rw [hxo] at hdvd
  exact (Nat.not_even_iff_odd.mpr odd_card_oddCore) (even_iff_two_dvd.mpr hdvd)

private theorem isSylowOf_map {H : Type*} [Group H] {P K : Subgroup G}
    (h : IsSylowOf p P K) (f : G →* H) : IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem map_pPrimeCore_le {N : Subgroup G} [N.Normal] :
    (pPrimeCore p N).map N.subtype ≤ pPrimeCore p G := by
  apply le_sSup
  refine ⟨inferInstance, ?_⟩
  rw [Subgroup.card_map_of_injective N.subtype_injective]
  exact pPrimeCore_coprime_card

omit [Finite G] [Fact p.Prime] in
private theorem map_pCore_le {N : Subgroup G} [N.Normal] :
    (pCore p N).map N.subtype ≤ pCore p G :=
  le_sSup ⟨inferInstance, pCore_isPGroup.map _⟩

private theorem pPrimeCore_eq_bot_of_normal {N : Subgroup G} [N.Normal]
    (h : pPrimeCore p G = ⊥) : pPrimeCore p N = ⊥ := by
  have h1 : (pPrimeCore p N).map N.subtype = ⊥ := le_bot_iff.mp (h ▸ map_pPrimeCore_le)
  exact (map_eq_bot_iff_of_injective _ N.subtype_injective).mp h1

omit [Finite G] [Fact p.Prime] in
private theorem le_of_isPGroup_two_of_le_sup {N K X : Subgroup G} [N.Normal]
    (hK : Odd (Nat.card K)) (hX : IsPGroup 2 X) (hXNK : X ≤ N ⊔ K) : X ≤ N := by
  intro x hx
  obtain ⟨n, hn, k, hk, hnk⟩ := (mem_sup_of_normal_left (s := N) (t := K)).mp (hXNK hx)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπ : QuotientGroup.mk' N x = QuotientGroup.mk' N k := by
    rw [← hnk, map_mul, show QuotientGroup.mk' N n = 1 from (QuotientGroup.eq_one_iff n).mpr hn,
      one_mul]
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hX) ⟨x, hx⟩
  have hd1 : orderOf (QuotientGroup.mk' N x) ∣ 2 ^ a := by
    rw [← ha, Subgroup.orderOf_mk]
    exact orderOf_map_dvd _ _
  have hd2 : orderOf (QuotientGroup.mk' N x) ∣ Nat.card K := by
    rw [hπ]
    exact (orderOf_map_dvd _ _).trans (Subgroup.orderOf_dvd_natCard K hk)
  have h1 := Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left.mpr hK).pow_left a) hd1 hd2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

omit [Finite G] in
private theorem le_centralizer_of_commutator_mem [Finite G] {Q X M : Subgroup G}
    (hQ : IsPGroup p Q) (hM : Nat.Coprime p (Nat.card M)) (hXQ : X ≤ normalizer (Q : Set G))
    (h : ∀ x ∈ X, ∀ y ∈ Q, y * x * y⁻¹ * x⁻¹ ∈ M) : X ≤ centralizer (Q : Set G) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  have hc : y * x * y⁻¹ * x⁻¹ ∈ Q := by
    have h' : x * y⁻¹ * x⁻¹ ∈ Q := (mem_normalizer_iff.mp (hXQ hx) y⁻¹).mp (Q.inv_mem hy)
    have := Q.mul_mem hy h'
    simpa [mul_assoc] using this
  have hbot : Q ⊓ M = ⊥ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
    have hcop : Nat.Coprime (Nat.card Q) (Nat.card M) := by
      rw [hn]
      exact hM.pow_left n
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have h1 : y * x * y⁻¹ * x⁻¹ = 1 := by
    have hmem : y * x * y⁻¹ * x⁻¹ ∈ Q ⊓ M := ⟨hc, h x hx y hy⟩
    rwa [hbot, mem_bot] at hmem
  calc y * x = y * x * y⁻¹ * x⁻¹ * (x * y) := by group
    _ = x * y := by rw [h1, one_mul]

private theorem centralizer_pCore_le_of_odd (H : Type*) [Group H] [Finite H]
    (hodd : Odd (Nat.card H)) (h : pPrimeCore p H = ⊥) :
    centralizer (pCore p H : Set H) ≤ pCore p H := by
  have hpp : p.Prime := Fact.out
  have hcon := isPConstrained_of_isSolvable (p := p) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  have hOp : Op_p'p p H = pCore p H := Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (p := p) h
  have hsyl : IsSylowOf p (pCore p H) (Op_p'p p H) := by
    rw [hOp, isSylowOf_iff, Subgroup.relIndex_self]
    exact ⟨le_rfl, pCore_isPGroup, hpp.not_dvd_one⟩
  have h' := hcon _ hsyl
  rwa [hOp] at h'

end Helpers

section Quotient

variable (hO : pPrimeCore p G ≤ oddCore G)
include hO

private theorem map_oddCore_eq :
    (oddCore G).map (QuotientGroup.mk' (pPrimeCore p G)) = oddCore (G ⧸ pPrimeCore p G) := by
  have hqs := QuotientGroup.mk'_surjective (pPrimeCore p G)
  apply le_antisymm
  · refine le_oddCore_of_normal ((inferInstance : (oddCore G).Normal).map _ hqs) ?_
    exact Odd.of_dvd_nat odd_card_oddCore (Subgroup.card_map_dvd _ _)
  · have h := comap_le_oddCore hO (oddCore (G ⧸ pPrimeCore p G)) odd_card_oddCore
    calc oddCore (G ⧸ pPrimeCore p G) =
          ((oddCore (G ⧸ pPrimeCore p G)).comap (QuotientGroup.mk' (pPrimeCore p G))).map
            (QuotientGroup.mk' (pPrimeCore p G)) :=
          (map_comap_eq_self_of_surjective hqs _).symm
      _ ≤ _ := map_mono h

omit [Finite G] in
private theorem map_inf_oddCore_eq (P : Subgroup G) :
    (P ⊓ oddCore G).map (QuotientGroup.mk' (pPrimeCore p G)) =
      P.map (QuotientGroup.mk' (pPrimeCore p G)) ⊓
        (oddCore G).map (QuotientGroup.mk' (pPrimeCore p G)) := by
  refine le_antisymm (map_inf_le _ _ _) ?_
  rintro x ⟨⟨u, hu, rfl⟩, ⟨o, ho, hou⟩⟩
  have hdiv : o⁻¹ * u ∈ pPrimeCore p G := by
    rw [← QuotientGroup.eq_one_iff (N := pPrimeCore p G)]
    change QuotientGroup.mk' (pPrimeCore p G) (o⁻¹ * u) = 1
    rw [map_mul, map_inv, hou, inv_mul_cancel]
  have huO : u ∈ oddCore G := by
    have : u = o * (o⁻¹ * u) := by group
    rw [this]
    exact mul_mem ho (hO hdiv)
  exact mem_map_of_mem _ ⟨hu, huO⟩

end Quotient

section Main

theorem oddCore_sup_normalizer_zj_eq_top_of_quotient (hp : p ≠ 2) {P : Subgroup G}
    (hP : IsPGroup p P) (hQ : IsSylowOf p (P ⊓ oddCore G) (oddCore G))
    (hO : pPrimeCore p G ≤ oddCore G)
    (hCB : centralizer (pCore p (G ⧸ pPrimeCore p G) : Set (G ⧸ pPrimeCore p G)) ≤
      pCore p (G ⧸ pPrimeCore p G))
    (hD : GorensteinWalter.HasDihedralSylowTwo G)
    (hmin : ∀ N : Subgroup G, N.Normal → oddCore G < N → N ⊔ P = ⊤) :
    oddCore G ⊔ normalizer (ambientMaxCardZJ P : Set G) = ⊤ := by
  classical
  have hpp : p.Prime := Fact.out
  have hpodd : Odd p := hpp.odd_of_ne_two hp
  set M : Subgroup G := pPrimeCore p G with hMdef
  set q : G →* G ⧸ M := QuotientGroup.mk' M with hqdef
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective M
  set Ob : Subgroup (G ⧸ M) := (oddCore G).map q with hObdef
  set Ub : Subgroup (G ⧸ M) := P.map q with hUbdef
  have hObn : Ob.Normal := (inferInstance : (oddCore G).Normal).map q hqs
  have hUbp : IsPGroup p Ub := hP.map q
  have hOb_eq : Ob = oddCore (G ⧸ M) := map_oddCore_eq hO
  have hObodd : Odd (Nat.card Ob) := hOb_eq ▸ odd_card_oddCore
  have hQb : IsSylowOf p (Ub ⊓ Ob) Ob := map_inf_oddCore_eq hO P ▸ isSylowOf_map hQ q
  have hBO : pCore p (G ⧸ M) ≤ Ob := hOb_eq ▸ pCore_le_oddCore' hp _
  have hBU : pCore p (G ⧸ M) ≤ Ub := by
    have hsup : pCore p (G ⧸ M) ⊔ (Ub ⊓ Ob) = Ub ⊓ Ob :=
      hQb.eq_of_le le_sup_right (sup_le hBO inf_le_right)
        (IsPGroup.to_sup_of_normal_left pCore_isPGroup (hUbp.to_le inf_le_left))
    exact (le_sup_left.trans hsup.le).trans inf_le_left
  have hst : ∀ B' A : Subgroup (G ⧸ M), B'.Normal → IsPGroup p B' → B' ≠ ⊥ → A ≤ Ub →
      ⁅⁅B', A⁆, A⁆ = ⊥ → A ≤ normalizerPCoreModCentralizer p B' := by
    intro B' A hB' hB'p _ _ hcomm
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
    obtain ⟨m, hm, ⟨e⟩⟩ := hD S
    have hS : Nonempty (DihedralGroup (2 ^ (m + 1 - 1)) ≃* (S : Subgroup G)) := by
      rw [Nat.add_sub_cancel]
      exact ⟨e.symm⟩
    have hrange : q.range = ⊤ := MonoidHom.range_eq_top.mpr hqs
    refine le_normalizerPCoreModCentralizer_of_isPStableAction q ?_ ?_ ?_ hcomm ?_
    · rw [hrange]
      infer_instance
    · rw [hrange]
      exact le_top
    · rw [normalizer_eq_top]
      exact le_top
    · intro M' ρ
      exact CFSG.LinearGroups.dihedral_subgroup_actions_are_odd_p_stable S (by omega) hS M' hpp
        hpodd B' hB'p ρ
  have hOZ : Ob ≤ normalizer (thompsonCenter Ub : Set (G ⧸ M)) := by
    set K : Subgroup (G ⧸ M) := Ob ⊔ Ub with hKdef
    have hrel : Ub.relIndex K = (Ub ⊓ Ob).relIndex Ob := by
      rw [hKdef, relIndex_sup_eq_relIndex_of_normal Ob Ub, Subgroup.inf_relIndex_right]
    have hKodd : Odd (Nat.card K) := odd_card_sup_of_normal hp hObodd hUbp
    haveI : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hKodd
    have hUK : IsSylowOf p Ub K := by
      rw [isSylowOf_iff]
      refine ⟨le_sup_right, hUbp, ?_⟩
      rw [hrel]
      exact ((isSylowOf_iff.mp hQb).2.2)
    obtain ⟨S, hS⟩ := hUK.exists_sylow_eq_subgroupOf
    have hK' : pPrimeCore p K = ⊥ := by
      set MK : Subgroup (G ⧸ M) := (pPrimeCore p K).map K.subtype with hMKdef
      have hMKO : MK ≤ Ob := by
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨o, ho, u, hu, hou⟩ := (mem_sup_of_normal_left (s := Ob) (t := Ub)).mp x.2
        have hπ : QuotientGroup.mk' Ob (x : G ⧸ M) = QuotientGroup.mk' Ob u := by
          rw [← hou, map_mul,
            show QuotientGroup.mk' Ob o = 1 from (QuotientGroup.eq_one_iff o).mpr ho, one_mul]
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hUbp) ⟨u, hu⟩
        have hd1 : orderOf (QuotientGroup.mk' Ob (x : G ⧸ M)) ∣ p ^ k := by
          rw [hπ, ← hk, Subgroup.orderOf_mk]
          exact orderOf_map_dvd _ _
        have hd2 : orderOf (QuotientGroup.mk' Ob (x : G ⧸ M)) ∣ Nat.card (pPrimeCore p K) := by
          refine (orderOf_map_dvd _ _).trans ?_
          rw [Subgroup.orderOf_coe]
          exact Subgroup.orderOf_dvd_natCard _ hx
        have h1 := Nat.eq_one_of_dvd_coprimes ((pPrimeCore_coprime_card (G := K)).pow_left k)
          hd1 hd2
        rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact h1
      have hMKn : (MK.subgroupOf Ob).Normal := by
        refine ⟨fun n hn g => ?_⟩
        rw [mem_subgroupOf] at hn ⊢
        obtain ⟨y, hy, hyn⟩ := hn
        refine ⟨⟨(g : G ⧸ M), mem_sup_left g.2⟩ * y * ⟨(g : G ⧸ M), mem_sup_left g.2⟩⁻¹,
          (pPrimeCore_normal (p := p) (G := K)).conj_mem y hy _, ?_⟩
        rw [Subgroup.coe_subtype] at hyn
        simp [hyn]
      have hcop : Nat.Coprime p (Nat.card (MK.subgroupOf Ob)) := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hMKO).toEquiv, hMKdef,
          Subgroup.card_map_of_injective K.subtype_injective]
        exact pPrimeCore_coprime_card
      have hle : MK.subgroupOf Ob ≤ pPrimeCore p Ob := le_sSup ⟨hMKn, hcop⟩
      have hObbot : pPrimeCore p Ob = ⊥ :=
        pPrimeCore_eq_bot_of_normal (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) p)
      rw [hObbot, le_bot_iff, ← map_eq_bot_iff_of_injective _ Ob.subtype_injective,
        map_subgroupOf_eq_of_le hMKO] at hle
      exact (map_eq_bot_iff_of_injective _ K.subtype_injective).mp hle
    have h62 := CFSG.theorem_6_2 hKodd S
    rw [hK', sup_bot_eq, hS] at h62
    have hmap : (ambientMaxCardZJ (Ub.subgroupOf K)).map K.subtype = ambientMaxCardZJ Ub := by
      rw [map_ambientMaxCardZJ_of_injective K.subtype _
        (K.subtype_injective.comp Subtype.val_injective), map_subgroupOf_eq_of_le le_sup_right]
    haveI : (ambientMaxCardZJ (Ub.subgroupOf K)).Normal := h62
    have hN := le_normalizer_map_subtype K (ambientMaxCardZJ (Ub.subgroupOf K))
    rw [hmap] at hN
    exact le_sup_left.trans hN
  have hFr : ∀ (L : Subgroup (G ⧸ M)) [L.Normal], Ob ≤ L →
      (IsSylowOf p (Ub ⊓ L) L ∧ pCore p ((G ⧸ M) ⧸ L) ≤ Ub.map (QuotientGroup.mk' L)) ∨
        L ⊔ normalizer (thompsonCenter Ub : Set (G ⧸ M)) = ⊤ := by
    intro L hL hOL
    by_cases hLO : L ≤ Ob
    · left
      have hLeq : L = Ob := le_antisymm hLO hOL
      refine ⟨hLeq ▸ hQb, ?_⟩
      have hLodd : L ≤ oddCore (G ⧸ M) := hOb_eq ▸ hLO
      have hR := comap_le_oddCore hLodd (pCore p ((G ⧸ M) ⧸ L))
        (odd_card_of_isPGroup hp pCore_isPGroup)
      rw [← hOb_eq, ← hLeq] at hR
      have h := map_mono (f := QuotientGroup.mk' L) hR
      rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
        QuotientGroup.map_mk'_self] at h
      rw [le_bot_iff.mp h]
      exact bot_le
    · right
      have hON : oddCore G < L.comap q := by
        refine lt_of_le_of_ne (fun x hx => hOL (mem_map_of_mem q hx)) ?_
        intro hEq
        apply hLO
        rw [← map_comap_eq_self_of_surjective hqs L, ← hEq]
      have hNP := hmin (L.comap q) (hL.comap q) hON
      have hLU : L ⊔ Ub = ⊤ := by
        have h := congrArg (map q) hNP
        rwa [Subgroup.map_sup, map_comap_eq_self_of_surjective hqs, map_top_of_surjective q hqs]
          at h
      rw [eq_top_iff, ← hLU]
      exact sup_le_sup_left (le_normalizer.trans (normalizer_le_normalizer_ambientMaxCardZJ Ub)) L
  have hZ := CFSG.ABGTheoremB.RelativeZJ.relative_zj_normal hp Ub hUbp hCB hBU hst Ob hObn hOZ hFr
  have h := CFSG.ABGTheoremB.RelativeZJ.relative_zj_factorization_of_normal P hP hZ
  exact top_le_iff.mp (h.ge.trans (sup_le_sup_right hO _))

omit [Fact p.Prime] in
theorem oddCore_sup_normalizer_zj_eq_top_of_le_oddCore [Fact p.Prime] {P : Subgroup G}
    (hQ : IsSylowOf p (P ⊓ oddCore G) (oddCore G)) (hPO : P ≤ oddCore G) :
    oddCore G ⊔ normalizer (ambientMaxCardZJ P : Set G) = ⊤ := by
  rw [inf_eq_left.mpr hPO] at hQ
  obtain ⟨T, hT⟩ := hQ
  have hfr := Sylow.normalizer_sup_eq_top (N := oddCore G) T
  rw [hT] at hfr
  apply top_le_iff.mp
  rw [← hfr, sup_comm]
  exact sup_le_sup_left (normalizer_le_normalizer_ambientMaxCardZJ P) _

end Main

section GH72Form

theorem pPrimeCore_le_oddCore_of_not_le_centralizer {P X : Subgroup G} (hP : IsPGroup p P)
    (hX : IsPGroup 2 X) (hXP : X ≤ normalizer (P : Set G))
    (hXQ : ¬ X ≤ centralizer ((P ⊓ oddCore G : Subgroup G) : Set G))
    (hXN : ∀ N : Subgroup G, N.Normal → oddCore G < N → X ≤ N) :
    pPrimeCore p G ≤ oddCore G := by
  by_contra hMO
  have hlt : oddCore G < pPrimeCore p G ⊔ oddCore G :=
    lt_of_le_of_ne le_sup_right fun h => hMO (le_sup_left.trans h.ge)
  have hXM : X ≤ pPrimeCore p G :=
    le_of_isPGroup_two_of_le_sup odd_card_oddCore hX (hXN _ inferInstance hlt)
  apply hXQ
  refine le_centralizer_of_commutator_mem (hP.to_le inf_le_left) pPrimeCore_coprime_card ?_ ?_
  · intro x hx
    exact inf_normalizer_le_normalizer_inf ⟨hXP hx, by rw [normalizer_eq_top]; exact mem_top x⟩
  · intro x hx y _
    exact (pPrimeCore p G).mul_mem ((pPrimeCore_normal).conj_mem x (hXM hx) y)
      ((pPrimeCore p G).inv_mem (hXM hx))

theorem centralizer_pCore_quotient_le_of_not_le_centralizer (hp : p ≠ 2) {P X : Subgroup G}
    (hP : IsPGroup p P) (hQ : IsSylowOf p (P ⊓ oddCore G) (oddCore G))
    (hX : IsPGroup 2 X) (hXP : X ≤ normalizer (P : Set G))
    (hXQ : ¬ X ≤ centralizer ((P ⊓ oddCore G : Subgroup G) : Set G))
    (hXN : ∀ N : Subgroup G, N.Normal → oddCore G < N → X ≤ N) :
    centralizer (pCore p (G ⧸ pPrimeCore p G) : Set (G ⧸ pPrimeCore p G)) ≤
      pCore p (G ⧸ pPrimeCore p G) := by
  classical
  have hO := pPrimeCore_le_oddCore_of_not_le_centralizer hP hX hXP hXQ hXN
  set M : Subgroup G := pPrimeCore p G with hMdef
  set q : G →* G ⧸ M := QuotientGroup.mk' M with hqdef
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective M
  set Ob : Subgroup (G ⧸ M) := (oddCore G).map q with hObdef
  set Qb : Subgroup (G ⧸ M) := P.map q ⊓ Ob with hQbdef
  set B : Subgroup (G ⧸ M) := pCore p (G ⧸ M) with hBdef
  have hObn : Ob.Normal := (inferInstance : (oddCore G).Normal).map q hqs
  have hOb_eq : Ob = oddCore (G ⧸ M) := map_oddCore_eq hO
  have hObodd : Odd (Nat.card Ob) := hOb_eq ▸ odd_card_oddCore
  have hQmap : (P ⊓ oddCore G).map q = Qb := map_inf_oddCore_eq hO P
  have hQb : IsSylowOf p Qb Ob := hQmap ▸ isSylowOf_map hQ q
  have hObbot : pPrimeCore p Ob = ⊥ :=
    pPrimeCore_eq_bot_of_normal (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) p)
  have hBOb : (pCore p Ob).map Ob.subtype ≤ B := map_pCore_le
  have hCO : centralizer (B : Set (G ⧸ M)) ⊓ Ob ≤ B := by
    rintro c ⟨hcC, hcO⟩
    have hc : (⟨c, hcO⟩ : Ob) ∈ pCore p Ob := by
      refine centralizer_pCore_le_of_odd Ob hObodd hObbot ?_
      rw [mem_centralizer_iff]
      intro z hz
      apply Subtype.ext
      exact (mem_centralizer_iff.mp hcC) _ (hBOb (mem_map_of_mem _ hz))
    exact hBOb (mem_map_of_mem Ob.subtype hc)
  have hCOb : centralizer (B : Set (G ⧸ M)) ≤ Ob := by
    by_contra hCO'
    have hON : oddCore G < (centralizer (B : Set (G ⧸ M)) ⊔ Ob).comap q := by
      refine lt_of_le_of_ne (fun x hx => mem_sup_right (mem_map_of_mem q hx)) ?_
      intro hEq
      apply hCO'
      have h := map_comap_eq_self_of_surjective hqs (centralizer (B : Set (G ⧸ M)) ⊔ Ob)
      rw [← hEq] at h
      exact le_sup_left.trans h.ge
    have hXc : X.map q ≤ centralizer (B : Set (G ⧸ M)) := by
      refine le_of_isPGroup_two_of_le_sup hObodd (hX.map q) ?_
      exact map_le_iff_le_comap.mpr (hXN _ ((inferInstance : (centralizer (B : Set (G ⧸ M)) ⊔
        Ob).Normal).comap q) hON)
    have hXnQb : X.map q ≤ normalizer (Qb : Set (G ⧸ M)) := by
      intro x hx
      refine inf_normalizer_le_normalizer_inf ⟨?_, by rw [normalizer_eq_top]; exact mem_top x⟩
      exact le_normalizer_map q (map_mono hXP hx)
    have hXQb : X.map q ≤ centralizer (Qb : Set (G ⧸ M)) := by
      refine (two_group_centralizes_sylow_iff hObodd (hX.map q) (by
        rw [normalizer_eq_top]; exact le_top) hQb hXnQb).mpr ?_
      refine hXc.trans (centralizer_le ?_)
      rw [Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (p := p) hObbot]
      exact inf_le_right.trans hBOb
    apply hXQ
    refine le_centralizer_of_commutator_mem (hP.to_le inf_le_left) pPrimeCore_coprime_card ?_ ?_
    · intro x hx
      exact inf_normalizer_le_normalizer_inf ⟨hXP hx, by rw [normalizer_eq_top]; exact mem_top x⟩
    · intro x hx y hy
      rw [← QuotientGroup.eq_one_iff (N := M)]
      change q (y * x * y⁻¹ * x⁻¹) = 1
      have hyQ : q y ∈ Qb := hQmap ▸ mem_map_of_mem q hy
      have hcomm : q y * q x = q x * q y :=
        (mem_centralizer_iff.mp (hXQb (mem_map_of_mem q hx))) _ hyQ
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
  exact fun c hc => hCO ⟨hc, hCOb hc⟩

theorem le_of_oddCore_lt (hp : p ≠ 2) {L P : Subgroup G} (hL : L.Normal) (hP : IsPGroup p P)
    (hOL : oddCore G ≤ L) (hLP : L ⊔ P = ⊤)
    (hLmin : ∀ N : Subgroup G, N.Normal → oddCore G ≤ N → N ≤ L → N = oddCore G ∨ N = L)
    {N : Subgroup G} (hN : N.Normal) (hON : oddCore G < N) : L ≤ N := by
  have hpp : p.Prime := Fact.out
  rcases hLmin (N ⊓ L) (Subgroup.normal_inf_normal N L) (le_inf hON.le hOL) inf_le_right with
    h | h
  · exfalso
    refine hON.not_ge (le_oddCore_of_normal hN ?_)
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 h2
    have hyo : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
    obtain ⟨l, hl, u, hu, hlu⟩ :=
      (mem_sup_of_normal_left (s := L) (t := P)).mp (hLP ▸ mem_top (y : G))
    have hπ : QuotientGroup.mk' L (y : G) = QuotientGroup.mk' L u := by
      rw [← hlu, map_mul, show QuotientGroup.mk' L l = 1 from (QuotientGroup.eq_one_iff l).mpr hl,
        one_mul]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨u, hu⟩
    have hd1 : orderOf (QuotientGroup.mk' L (y : G)) ∣ 2 := hyo ▸ orderOf_map_dvd _ _
    have hd2 : orderOf (QuotientGroup.mk' L (y : G)) ∣ p ^ k := by
      rw [hπ, ← hk, Subgroup.orderOf_mk]
      exact orderOf_map_dvd _ _
    have hcop : Nat.Coprime 2 (p ^ k) :=
      Nat.coprime_two_left.mpr ((hpp.odd_of_ne_two hp).pow)
    have h1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hyO : (y : G) ∈ oddCore G := h ▸ ⟨y.2, h1⟩
    have hdvd : orderOf (y : G) ∣ Nat.card (oddCore G) := Subgroup.orderOf_dvd_natCard _ hyO
    rw [hyo] at hdvd
    exact (Nat.not_even_iff_odd.mpr odd_card_oddCore) (even_iff_two_dvd.mpr hdvd)
  · exact h ▸ inf_le_left

theorem oddCore_sup_normalizer_zj_eq_top (hp : p ≠ 2) {P X L : Subgroup G} (hP : IsPGroup p P)
    (hQ : IsSylowOf p (P ⊓ oddCore G) (oddCore G)) (hX : IsPGroup 2 X)
    (hXP : X ≤ normalizer (P : Set G))
    (hXQ : ¬ X ≤ centralizer ((P ⊓ oddCore G : Subgroup G) : Set G))
    (hL : L.Normal) (hOL : oddCore G ≤ L) (hXL : X ≤ L) (hLP : L ⊔ P = ⊤)
    (hLmin : ∀ N : Subgroup G, N.Normal → oddCore G ≤ N → N ≤ L → N = oddCore G ∨ N = L)
    (hD : GorensteinWalter.HasDihedralSylowTwo G) :
    oddCore G ⊔ normalizer (ambientMaxCardZJ P : Set G) = ⊤ := by
  have hLN : ∀ N : Subgroup G, N.Normal → oddCore G < N → L ≤ N :=
    fun N hN hON => le_of_oddCore_lt hp hL hP hOL hLP hLmin hN hON
  have hXN : ∀ N : Subgroup G, N.Normal → oddCore G < N → X ≤ N :=
    fun N hN hON => hXL.trans (hLN N hN hON)
  refine oddCore_sup_normalizer_zj_eq_top_of_quotient hp hP hQ
    (pPrimeCore_le_oddCore_of_not_le_centralizer hP hX hXP hXQ hXN)
    (centralizer_pCore_quotient_le_of_not_le_centralizer hp hP hQ hX hXP hXQ hXN) hD ?_
  intro N hN hON
  exact top_le_iff.mp (hLP ▸ sup_le_sup_right (hLN N hN hON) P)

end GH72Form

end CFSG.GH72
