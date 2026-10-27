module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentZFrattini
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1FusionIndex

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

section General

variable {X : Type} [Group X] [Finite X] {H N : Subgroup X}

omit [Finite X] in
theorem exists_mk_eq_inclusion
    (hdec : ∀ g ∈ H, ∃ o ∈ (CFSG.pPrimeCore 2 H).map H.subtype, ∃ n ∈ N, o * n = g)
    (hNH : N ≤ H) (g : H) :
    ∃ n : N, (g : H ⧸ CFSG.pPrimeCore 2 H) =
      (Subgroup.inclusion hNH n : H ⧸ CFSG.pPrimeCore 2 H) := by
  obtain ⟨o, ho, n, hn, hon⟩ := hdec g g.2
  obtain ⟨o', ho', hoo⟩ := Subgroup.mem_map.mp ho
  refine ⟨⟨n, hn⟩, ?_⟩
  have hg : g = o' * Subgroup.inclusion hNH ⟨n, hn⟩ := Subtype.ext (by
    rw [Subgroup.coe_mul, ← hon, ← hoo]
    rfl)
  rw [hg, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr ho', one_mul]

omit [Finite X] in
theorem normal_map_mk_of_le_normalizer
    (hdec : ∀ g ∈ H, ∃ o ∈ (CFSG.pPrimeCore 2 H).map H.subtype, ∃ n ∈ N, o * n = g)
    (hNH : N ≤ H) {A : Subgroup X} (hNA : N ≤ Subgroup.normalizer (A : Set X)) :
    ((A.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 H))).Normal := by
  refine ⟨fun a ha g => ?_⟩
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨n, hn⟩ := exists_mk_eq_inclusion hdec hNH g'
  refine ⟨Subgroup.inclusion hNH n * a' * (Subgroup.inclusion hNH n)⁻¹, ?_, ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp (hNA n.2) _).mp (Subgroup.mem_subgroupOf.mp ha')
  · rw [hn]
    simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem le_map_pPrimeCore_of_odd
    (hdec : ∀ g ∈ H, ∃ o ∈ (CFSG.pPrimeCore 2 H).map H.subtype, ∃ n ∈ N, o * n = g)
    (hNH : N ≤ H) {A : Subgroup X} (hAH : A ≤ H) (hNA : N ≤ Subgroup.normalizer (A : Set X))
    (hA : Odd (Nat.card A)) : A ≤ (CFSG.pPrimeCore 2 H).map H.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.Coprime 2
      (Nat.card ((A.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 H)))) :=
    Nat.coprime_two_left.mpr (hA.of_dvd_nat ((Subgroup.card_map_dvd _ _).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv).dvd))
  have hle : (A.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 H)) ≤
      CFSG.pPrimeCore 2 (H ⧸ CFSG.pPrimeCore 2 H) :=
    le_sSup ⟨normal_map_mk_of_le_normalizer hdec hNH hNA, hc⟩
  rw [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot] at hle
  intro a ha
  have h1 := hle (Subgroup.mem_map_of_mem _
    (Subgroup.mem_subgroupOf.mpr ha : (⟨a, hAH ha⟩ : H) ∈ A.subgroupOf H))
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, rfl⟩

omit [Finite X] in
theorem card_quotient_pPrimeCore_eq_relIndex
    (hdec : ∀ g ∈ H, ∃ o ∈ (CFSG.pPrimeCore 2 H).map H.subtype, ∃ n ∈ N, o * n = g)
    (hNH : N ≤ H) :
    Nat.card (H ⧸ CFSG.pPrimeCore 2 H) = ((CFSG.pPrimeCore 2 H).map H.subtype ⊓ N).relIndex N := by
  let φ : N →* H ⧸ CFSG.pPrimeCore 2 H :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 2 H)).comp (Subgroup.inclusion hNH)
  have hφ : Function.Surjective φ := fun q => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨n, hn⟩ := exists_mk_eq_inclusion hdec hNH g
    exact ⟨n, hn.symm⟩
  have hker : φ.ker = ((CFSG.pPrimeCore 2 H).map H.subtype ⊓ N).subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨fun h => ⟨⟨_, h, rfl⟩, n.2⟩, fun ⟨⟨o, ho, hon⟩, _⟩ => ?_⟩
    rwa [show o = Subgroup.inclusion hNH n from Subtype.ext hon] at ho
  rw [Subgroup.relIndex, ← hker, Subgroup.index]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv).symm

omit [Finite X] in
theorem isCharacteristicP_of_forall_mul
    (hdec : ∀ g ∈ H, ∃ o ∈ (CFSG.pPrimeCore 2 H).map H.subtype, ∃ n ∈ N, o * n = g)
    (hNH : N ≤ H) {E : Subgroup X} (hEH : E ≤ H) (hNE : N ≤ Subgroup.normalizer (E : Set X))
    (hE : IsPGroup 2 E)
    (hC : ∀ n ∈ N, (∀ s ∈ E, n * s * n⁻¹ * s⁻¹ ∈ (CFSG.pPrimeCore 2 H).map H.subtype) →
      ∃ e ∈ E, ∃ o ∈ (CFSG.pPrimeCore 2 H).map H.subtype, e * o = n) :
    CFSG.IsCharacteristicP 2 (H ⧸ CFSG.pPrimeCore 2 H) := by
  have hÊle : (E.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 H)) ≤
      CFSG.pCore 2 (H ⧸ CFSG.pPrimeCore 2 H) :=
    le_sSup ⟨normal_map_mk_of_le_normalizer hdec hNH hNE,
      (hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEH).symm).map _⟩
  intro x hx
  have hxE := Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hÊle) hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨n, hn⟩ := exists_mk_eq_inclusion hdec hNH g
  rw [hn] at hxE ⊢
  obtain ⟨e, he, o, ho, heo⟩ := hC n n.2 fun s hs => by
    have h1 := Subgroup.mem_centralizer_iff.mp hxE (QuotientGroup.mk ⟨s, hEH hs⟩)
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hs))
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
    refine ⟨_, (CFSG.pPrimeCore_normal (p := 2) (G := H)).conj_mem _ h1
      (⟨s, hEH hs⟩ * Subgroup.inclusion hNH n), ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    group
  obtain ⟨o', ho', hoo⟩ := Subgroup.mem_map.mp ho
  refine hÊle ⟨⟨e, hEH he⟩, Subgroup.mem_subgroupOf.mpr he, ?_⟩
  have hno : Subgroup.inclusion hNH n = ⟨e, hEH he⟩ * o' := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_inclusion, ← heo, ← hoo]
    rfl)
  rw [hno, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr ho', mul_one]
  rfl

end General

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem e1EBar_le_centralizer_forty : e1EBar (Subgroup.center J) u m y x ≤
    Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} := fun _ hs =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (d.caseC3BCD.commute_of_mem_e1EBar hs d.caseC3BCD.forty_mem_e1EBar)

theorem centralizer_e1EBar_le_centralizer_forty :
    Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) ≤
      Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr d.caseC3BCD.forty_mem_e1EBar)

theorem eq_one_of_mem_e1EBar_of_mem_map_pPrimeCore {s : J ⧸ Subgroup.center J}
    (hs : s ∈ e1EBar (Subgroup.center J) u m y x)
    (hO : s ∈ (CFSG.pPrimeCore 2 (Subgroup.centralizer
      {caseC3Word (Subgroup.center J) u m y x 40})).map
        (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}).subtype) : s = 1 :=
  eq_one_of_mul_self_of_odd (d.caseC3BCD.mul_self_of_mem_e1EBar hs)
    (odd_orderOf_of_mem_map_pPrimeCore hO)

theorem mem_centralizer_of_conj_mem_map_pPrimeCore {n : J ⧸ Subgroup.center J}
    (hn : n ∈ Subgroup.normalizer
      (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)))
    (hnE : ∀ s ∈ e1EBar (Subgroup.center J) u m y x, n * s * n⁻¹ * s⁻¹ ∈
      (CFSG.pPrimeCore 2 (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})).map
        (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}).subtype) :
    n ∈ Subgroup.centralizer
      (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have h1 : n * s * n⁻¹ * s⁻¹ ∈ e1EBar (Subgroup.center J) u m y x :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hn s).mp hs) (Subgroup.inv_mem _ hs)
  have h3 := d.eq_one_of_mem_e1EBar_of_mem_map_pPrimeCore h1 (hnE s hs)
  calc s * n = (n * s * n⁻¹ * s⁻¹)⁻¹ * (n * s) := by group
    _ = n * s := by rw [h3, inv_one, one_mul]

theorem mem_centralizer_of_mem_map_pPrimeCore {o : J ⧸ Subgroup.center J}
    (hO : o ∈ (CFSG.pPrimeCore 2 (Subgroup.centralizer
      {caseC3Word (Subgroup.center J) u m y x 40})).map
        (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}).subtype)
    (hn : o ∈ Subgroup.normalizer
      (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J))) :
    o ∈ Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) :=
  d.mem_centralizer_of_conj_mem_map_pPrimeCore hn fun s hs => by
    rw [show o * s * o⁻¹ * s⁻¹ = o * (s * o⁻¹ * s⁻¹) by group]
    exact Subgroup.mul_mem _ hO (conj_mem_map_subtype (d.e1EBar_le_centralizer_forty hs)
      (Subgroup.inv_mem _ hO))

variable (hdec : ∀ g ∈ Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40},
  ∃ o ∈ (CFSG.pPrimeCore 2 (Subgroup.centralizer
    {caseC3Word (Subgroup.center J) u m y x 40})).map
      (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}).subtype,
    ∃ n ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)),
      o * n = g)
include hdec

theorem mem_map_pPrimeCore_of_mem_centralizer_e1EBar {c : J ⧸ Subgroup.center J}
    (hc : c ∈ Subgroup.centralizer
      (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)))
    (hodd : Odd (orderOf c)) :
    c ∈ (CFSG.pPrimeCore 2 (Subgroup.centralizer
      {caseC3Word (Subgroup.center J) u m y x 40})).map
        (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}).subtype := by
  obtain ⟨O, hOC, hOodd, -, hiff, -, hnorm⟩ := d.exists_oddCore_centralizer_e1EBar
  exact le_map_pPrimeCore_of_odd hdec d.normalizer_e1EBar_le
    (hOC.trans d.centralizer_e1EBar_le_centralizer_forty)
    (fun n hn => mem_normalizer_of_forall_conj_mem fun o ho => hnorm n hn o ho) hOodd
    ((hiff c hc).mpr hodd)

theorem isCharacteristicP_quotient_pPrimeCore_centralizer_forty :
    CFSG.IsCharacteristicP 2 (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} ⧸
      CFSG.pPrimeCore 2 (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})) := by
  obtain ⟨O, hOC, -, hdecE, hiff, -, -⟩ := d.exists_oddCore_centralizer_e1EBar
  refine isCharacteristicP_of_forall_mul hdec d.normalizer_e1EBar_le d.e1EBar_le_centralizer_forty
    le_rfl (IsPGroup.of_card (n := 3) (by rw [d.caseC3BCD.card_e1EBar]; norm_num))
      fun n hn hnE => ?_
  obtain ⟨e, he, o, ho, rfl⟩ := hdecE n (d.mem_centralizer_of_conj_mem_map_pPrimeCore hn hnE)
  exact ⟨e, he, o, d.mem_map_pPrimeCore_of_mem_centralizer_e1EBar hdec (hOC ho)
    ((hiff o (hOC ho)).mp ho), rfl⟩

theorem card_quotient_pPrimeCore_centralizer_forty
    (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
      s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
        CaseC3.Genuine (Subgroup.center J) s) :
    Nat.card (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} ⧸
      CFSG.pPrimeCore 2 (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})) =
        192 := by
  have hb := d.caseC3BCD
  obtain ⟨O, hOC, -, hdecE, hiff, hEO, -⟩ := d.exists_oddCore_centralizer_e1EBar
  set E := e1EBar (Subgroup.center J) u m y x with hE
  set C := Subgroup.centralizer (E : Set (J ⧸ Subgroup.center J)) with hC
  have heq : (CFSG.pPrimeCore 2 (Subgroup.centralizer
      {caseC3Word (Subgroup.center J) u m y x 40})).map
        (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}).subtype ⊓
          Subgroup.normalizer (E : Set (J ⧸ Subgroup.center J)) = O := by
    ext c
    exact ⟨fun ⟨hcO, hcN⟩ => (hiff c (d.mem_centralizer_of_mem_map_pPrimeCore hcO hcN)).mpr
      (odd_orderOf_of_mem_map_pPrimeCore hcO), fun hc =>
        ⟨d.mem_map_pPrimeCore_of_mem_centralizer_e1EBar hdec (hOC hc) ((hiff c (hOC hc)).mp hc),
          Subgroup.centralizer_le_normalizer _ (hOC hc)⟩⟩
  have hEC : E ≤ C := fun s hs =>
    Subgroup.mem_centralizer_iff.mpr fun t ht => hb.commute_of_mem_e1EBar ht hs
  have hcard : Nat.card C = 8 * Nat.card O := by
    rw [← hb.card_e1EBar, ← Nat.card_prod]
    refine (Nat.card_eq_of_bijective (fun p : E × O =>
      (⟨p.1 * p.2, C.mul_mem (hEC p.1.2) (hOC p.2.2)⟩ : C)) ⟨?_, fun c => ?_⟩).symm
    · rintro ⟨⟨e, he⟩, ⟨o, ho⟩⟩ ⟨⟨e', he'⟩, ⟨o', ho'⟩⟩ h
      have h' : e * o = e' * o' := congrArg Subtype.val h
      have h1 : e'⁻¹ * e = o' * o⁻¹ :=
        calc e'⁻¹ * e = e'⁻¹ * (e * o) * o⁻¹ := by group
          _ = o' * o⁻¹ := by rw [h']; group
      have hee : e' = e := inv_mul_eq_one.mp
        (hEO _ (E.mul_mem (E.inv_mem he') he) (h1 ▸ O.mul_mem ho' (O.inv_mem ho)))
      subst hee
      obtain rfl : o = o' := mul_left_cancel h'
      rfl
    · obtain ⟨e, he, o, ho, he'⟩ := hdecE c c.2
      exact ⟨(⟨e, he⟩, ⟨o, ho⟩), Subtype.ext he'⟩
  have h := Subgroup.relIndex_mul_card O C
  rw [inf_eq_left.mpr hOC, hcard] at h
  rw [card_quotient_pPrimeCore_eq_relIndex hdec d.normalizer_e1EBar_le, heq,
    ← Subgroup.relIndex_mul_relIndex O C _ hOC (Subgroup.centralizer_le_normalizer _),
    Nat.eq_of_mul_eq_mul_right Nat.card_pos h, d.relIndex_centralizer_normalizer_e1EBar htype]

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
