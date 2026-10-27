module

public import CFSG.Goldschmidt.Steps.G310TypeID

public section

namespace CFSG.Goldschmidt.G310

open CFSG.Open

section Bar

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem barOf_normalClosureIn (H A : Subgroup G) :
    barOf H (normalClosureIn H A) = normalClosureIn ⊤ (barOf H A) := by
  have h1 : (normalClosureIn H A).subgroupOf H =
      Subgroup.normalClosure ((A.subgroupOf H : Subgroup H) : Set H) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [barOf, h1, Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _), normalClosureIn,
    Subgroup.map_normalClosure _ _ (fun x => ⟨⟨x, trivial⟩, rfl⟩)]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨_, trivial⟩, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

theorem centralizer_barOf {H A : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup 2 A) :
    Subgroup.centralizer (barOf H A : Set (H ⧸ goldschmidtOddCore H)) =
      barOf H (Subgroup.centralizer (A : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 (A.subgroupOf H)) := ⟨hA.comap_subtype⟩
  have hcop : Nat.Coprime 2 (Nat.card (goldschmidtOddCore H)) :=
    Nat.coprime_two_left.mpr (SStarTransport.odd_card_goldschmidtOddCore H)
  have h := CFSG.centralizer_map_quotient_eq_map_centralizer 2 (A.subgroupOf H)
    (goldschmidtOddCore H) inferInstance hcop
  have hC : Subgroup.centralizer ((A.subgroupOf H : Subgroup H) : Set H) =
      (Subgroup.centralizer (A : Set G)).subgroupOf H := by
    ext x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx a ha
      exact congrArg Subtype.val (hx ⟨a, hAH ha⟩ ha)
    · intro hx a ha
      exact Subtype.ext (hx a ha)
  rw [barOf, barOf, ← hC]
  exact h

@[expose] noncomputable def centralizerMap {H A : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup 2 A) :
    (H ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) →*
      (⊤ ⊓ Subgroup.centralizer (barOf H A : Set (H ⧸ goldschmidtOddCore H)) :
        Subgroup (H ⧸ goldschmidtOddCore H)) :=
  ((QuotientGroup.mk' (goldschmidtOddCore H)).comp (Subgroup.inclusion inf_le_left)).codRestrict
    _ (fun x => by
      refine ⟨Subgroup.mem_top _, ?_⟩
      rw [centralizer_barOf hAH hA]
      exact ⟨⟨x, x.2.1⟩, x.2.2, rfl⟩)

theorem centralizerMap_apply {H A : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup 2 A)
    (x : (H ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)) :
    ((centralizerMap hAH hA x : _) : H ⧸ goldschmidtOddCore H) =
      QuotientGroup.mk' (goldschmidtOddCore H) ⟨x, x.2.1⟩ := rfl

theorem centralizerMap_surjective {H A : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup 2 A) :
    Function.Surjective (centralizerMap hAH hA) := by
  rintro ⟨y, -, hy⟩
  rw [centralizer_barOf hAH hA] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨x, x.2, hx⟩, rfl⟩

theorem odd_card_ker_centralizerMap {H A : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup 2 A) :
    Odd (Nat.card (centralizerMap hAH hA).ker) := by
  have hle : (centralizerMap hAH hA).ker.map
      ((Subgroup.inclusion (inf_le_left : H ⊓ Subgroup.centralizer (A : Set G) ≤ H))) ≤
      goldschmidtOddCore H := by
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
    have h1 := congrArg Subtype.val hx
    rw [centralizerMap_apply] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have h1 := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective _)] at h1
  exact Odd.of_dvd_nat (SStarTransport.odd_card_goldschmidtOddCore H) h1

theorem comap_oddCent {H A : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup 2 A) :
    (goldschmidtOddCore (⊤ ⊓ Subgroup.centralizer (barOf H A : Set (H ⧸ goldschmidtOddCore H)) :
        Subgroup (H ⧸ goldschmidtOddCore H))).comap (centralizerMap hAH hA) =
      goldschmidtOddCore (H ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
  SStarTransport.comap_goldschmidtOddCore_eq _ (centralizerMap_surjective hAH hA)
    (odd_card_ker_centralizerMap hAH hA)

theorem mem_oddCoreOf_of_barOf {H A : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup 2 A) {x : G}
    (hx : x ∈ H ⊓ Subgroup.centralizer (A : Set G))
    (hbar : QuotientGroup.mk' (goldschmidtOddCore H) ⟨x, hx.1⟩ ∈
      oddCoreOf (⊤ ⊓ Subgroup.centralizer (barOf H A : Set (H ⧸ goldschmidtOddCore H)))) :
    x ∈ oddCoreOf (H ⊓ Subgroup.centralizer (A : Set G)) := by
  obtain ⟨y, hy, hyx⟩ := hbar
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  rw [← comap_oddCent hAH hA, SetLike.mem_coe, Subgroup.mem_comap]
  have : centralizerMap hAH hA ⟨x, hx⟩ = y := Subtype.ext hyx.symm
  rw [this]
  exact hy

theorem barOf_mem_oddCoreOf {H A : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup 2 A) {x : G}
    (hx : x ∈ oddCoreOf (H ⊓ Subgroup.centralizer (A : Set G))) (hxH : x ∈ H) :
    QuotientGroup.mk' (goldschmidtOddCore H) ⟨x, hxH⟩ ∈
      oddCoreOf (⊤ ⊓ Subgroup.centralizer (barOf H A : Set (H ⧸ goldschmidtOddCore H))) := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← comap_oddCent hAH hA, SetLike.mem_coe, Subgroup.mem_comap] at hy
  exact ⟨_, hy, rfl⟩

end Bar

section SylowConj

variable {X : Type*} [Group X] [Finite X]

theorem exists_conjSub_eq_of_fusionIsSylowIn {p : ℕ} [Fact p.Prime] {S S' Y : Subgroup X}
    (hS : fusionIsSylowIn p S Y) (hS' : fusionIsSylowIn p S' Y) :
    ∃ y ∈ Y, S' = conjSub y S := by
  obtain ⟨P, rfl⟩ := exists_sylow_of_fusionIsSylowIn hS
  obtain ⟨P', rfl⟩ := exists_sylow_of_fusionIsSylowIn hS'
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Y P P'
  refine ⟨(g : X)⁻¹, Y.inv_mem g.2, ?_⟩
  rw [map_subtype_smul_sylow, conjSub_eq_map_conj]

omit [Finite X] in
theorem fusionIsSylowIn_conjSub {p : ℕ} {S Y : Subgroup X} (hS : fusionIsSylowIn p S Y)
    (n : X) : fusionIsSylowIn p (conjSub n S) (conjSub n Y) := by
  refine ⟨conjSub_mono hS.1, hS.2.1.map _, fun Q hQY hQ hSQ => ?_⟩
  have h1 : conjSub n⁻¹ Q ≤ Y := by
    have := conjSub_mono (g := n⁻¹) hQY
    rwa [conjSub_inv_conjSub] at this
  have h2 : S ≤ conjSub n⁻¹ Q := by
    have := conjSub_mono (g := n⁻¹) hSQ
    rwa [conjSub_inv_conjSub] at this
  have h3 := hS.2.2 _ h1 (hQ.map _) h2
  rw [← h3, conjSub_conjSub_inv]

end SylowConj

section Corr

variable {G : Type} [Group G] [Finite G]

theorem barOf_mem_sigN {H A P : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup 2 A) {p : ℕ}
    (hP : P ∈ sigN H A p) : barOf H P ∈ sigN ⊤ (barOf H A) p := by
  obtain ⟨hPH, hPp, hAP, hPC⟩ := hP
  refine ⟨le_top, (hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm).map _, ?_, ?_⟩
  · apply le_normalizer_of_conj_mem
    rintro _ ⟨a, ha, rfl⟩ _ ⟨x, hx, rfl⟩
    refine ⟨a * x * a⁻¹, ?_, by simp⟩
    show (a : G) * x * (a : G)⁻¹ ∈ P
    exact (Subgroup.mem_normalizer_iff.mp (hAP ha) x).mp hx
  · rintro _ ⟨⟨y, hyP, rfl⟩, hyC⟩
    rw [centralizer_barOf hAH hA] at hyC
    obtain ⟨c, hcC, hcy⟩ := hyC
    have hyc : y⁻¹ * c ∈ goldschmidtOddCore H := by
      rw [← QuotientGroup.eq]
      exact hcy.symm
    have hcmem : (c : G) ∈ (P ⊔ oddCoreOf H) ⊓ Subgroup.centralizer (A : Set G) := by
      refine ⟨?_, hcC⟩
      have e : (c : G) = (y : G) * ((y⁻¹ * c : H) : G) := by simp
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyP)
        (Subgroup.mem_sup_right ⟨_, hyc, rfl⟩)
    have h1 := sup_oddCoreOf_inf_centralizer_le hAH hA ⟨hPH, hPp, hAP, hPC⟩ hcmem
    rw [← hcy]
    exact barOf_mem_oddCoreOf hAH hA h1 c.2

omit [Finite G] in
theorem preOf_barOf {H P : Subgroup G} (hPH : P ≤ H) :
    preOf H (barOf H P) = P ⊔ oddCoreOf H := by
  have hPO : P ≤ Subgroup.normalizer (oddCoreOf H : Set G) :=
    hPH.trans (le_normalizer_oddCoreOf H)
  apply le_antisymm
  · rintro _ ⟨x, ⟨y, hyP, hyx⟩, rfl⟩
    have hyx' : y⁻¹ * x ∈ goldschmidtOddCore H := by
      rw [← QuotientGroup.eq]
      exact hyx
    have e : (x : G) = (y : G) * ((y⁻¹ * x : H) : G) := by simp
    show (x : G) ∈ _
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyP) (Subgroup.mem_sup_right ⟨_, hyx', rfl⟩)
  · intro x hx
    have hxH : x ∈ H := sup_le hPH (oddCoreOf_le H) hx
    obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_of_mem_sup hPO hx
    obtain ⟨z', hz', rfl⟩ := hz
    refine ⟨⟨y * z', hxH⟩, ⟨⟨y, hPH hy⟩, hy, ?_⟩, rfl⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : (⟨y, hPH hy⟩ : H)⁻¹ * ⟨y * z', hxH⟩ = z' := Subtype.ext (by simp)
    rw [this]
    exact hz'

theorem not_two_dvd_card_preOf {H : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : Subgroup (H ⧸ goldschmidtOddCore H)} (hQ : IsPGroup p Q) :
    ¬ 2 ∣ Nat.card (preOf H Q) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [preOf, Subgroup.card_map_of_injective H.subtype_injective]
  set g := (QuotientGroup.mk' (goldschmidtOddCore H)).domRestrict
    (Q.comap (QuotientGroup.mk' (goldschmidtOddCore H))) with hg
  have hcard := Subgroup.card_ker_mul_card_range g
  have hrange : Nat.card g.range ∣ Nat.card Q := by
    apply Subgroup.card_dvd_of_le
    rintro _ ⟨v, rfl⟩
    exact v.2
  have hkerdvd : Nat.card g.ker ∣ Nat.card (goldschmidtOddCore H) := by
    have hsub : g.ker.map (Q.comap (QuotientGroup.mk' (goldschmidtOddCore H))).subtype ≤
        goldschmidtOddCore H := by
      rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hv
      exact (QuotientGroup.eq_one_iff _).mp hv
    rw [← Subgroup.card_map_of_injective (K := g.ker)
      (Q.comap (QuotientGroup.mk' (goldschmidtOddCore H))).subtype_injective]
    exact Subgroup.card_dvd_of_le hsub
  have hQodd : Odd (Nat.card Q) := by
    obtain ⟨n, hn⟩ := hQ.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hodd : Odd (Nat.card (Q.comap (QuotientGroup.mk' (goldschmidtOddCore H)))) := by
    rw [← hcard]
    exact ((SStarTransport.odd_card_goldschmidtOddCore H).of_dvd_nat hkerdvd).mul
      (hQodd.of_dvd_nat hrange)
  exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)

theorem maximal_sigN_barOf {H A P : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup 2 A) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hP : Maximal (· ∈ sigN H A p) P) :
    Maximal (· ∈ sigN ⊤ (barOf H A) p) (barOf H P) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hPH, hPp, hAP, -⟩ := hP.prop
  refine ⟨barOf_mem_sigN hAH hA hP.prop, fun Q hQ hle => ?_⟩
  obtain ⟨-, hQp, hAQ, hQC⟩ := hQ
  set Qt := preOf H Q with hQt
  have hQtH : Qt ≤ H := Subgroup.map_subtype_le _
  have hPQ : P ≤ Qt := fun x hx => ⟨⟨x, hPH hx⟩, hle ⟨⟨x, hPH hx⟩, hx, rfl⟩, rfl⟩
  have hAQt : A ≤ Subgroup.normalizer (Qt : Set G) := by
    apply le_normalizer_of_conj_mem
    rintro a ha _ ⟨x, hx, rfl⟩
    refine ⟨⟨a, hAH ha⟩ * x * ⟨a, hAH ha⟩⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap] at hx ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hAQ ⟨⟨a, hAH ha⟩, ha, rfl⟩) _).mp hx
  obtain ⟨S, hS, hPS, hAS⟩ := exists_invariant_sylow_containing Nat.prime_two hp hA
    (not_two_dvd_card_preOf hp hp2 hQp) hAQt hPQ hPp hAP
  have hSsig : S ∈ sigN H A p := by
    refine ⟨hS.1.trans hQtH, hS.2.1, hAS, fun x hx => ?_⟩
    have hxH : x ∈ H := hQtH (hS.1 hx.1)
    have hxQ : QuotientGroup.mk' (goldschmidtOddCore H) ⟨x, hxH⟩ ∈ Q := by
      obtain ⟨y, hy, hyx⟩ := hS.1 hx.1
      rwa [show y = ⟨x, hxH⟩ from Subtype.ext hyx] at hy
    have hxC : QuotientGroup.mk' (goldschmidtOddCore H) ⟨x, hxH⟩ ∈
        Subgroup.centralizer (barOf H A : Set (H ⧸ goldschmidtOddCore H)) := by
      rw [centralizer_barOf hAH hA]
      exact ⟨⟨x, hxH⟩, hx.2, rfl⟩
    exact mem_oddCoreOf_of_barOf hAH hA ⟨hxH, hx.2⟩ (hQC ⟨hxQ, hxC⟩)
  have hSP : S = P := le_antisymm (hP.2 hSsig hPS) hPS
  rw [hSP] at hS
  have hS' : fusionIsSylowIn p (P.subgroupOf H) (Qt.subgroupOf H) :=
    fusionIsSylowIn_subgroupOf hS hQtH
  have hQtQ : (Qt.subgroupOf H).map (QuotientGroup.mk' (goldschmidtOddCore H)) = Q := by
    rw [hQt, preOf, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      H.subtype_injective,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have h1 := map_eq_of_fusionIsSylowIn (QuotientGroup.mk' (goldschmidtOddCore H)) hS'
    (by rw [hQtQ]; exact hQp)
  rw [hQtQ] at h1
  exact h1.symm.le.trans le_rfl

theorem le_preOf_sup_normalizer {H A P : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup 2 A) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hP : Maximal (· ∈ sigN H A p) P)
    {Lb : Subgroup (H ⧸ goldschmidtOddCore H)} [Lb.Normal]
    (h : (⊤ : Subgroup (H ⧸ goldschmidtOddCore H)) ≤
      Lb ⊔ Subgroup.normalizer (barOf H P : Set (H ⧸ goldschmidtOddCore H))) :
    preOf H Lb ⊔ H ⊓ Subgroup.normalizer (P : Set G) = H := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hPH, hPp, hAP, -⟩ := hP.prop
  set π := QuotientGroup.mk' (goldschmidtOddCore H) with hπ
  have hOL : oddCoreOf H ≤ preOf H Lb := by
    rintro _ ⟨o, ho, rfl⟩
    refine ⟨o, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff o).mpr ho]
    exact Lb.one_mem
  have hsyl := (fusionIsSylowIn_of_maximal_sigN hAH hA hp hp2 hP).1
  refine le_antisymm (sup_le (Subgroup.map_subtype_le _) inf_le_left) fun x hx => ?_
  have hxs := h (Subgroup.mem_top (π ⟨x, hx⟩))
  obtain ⟨l, hl, n, hn, hln⟩ := Subgroup.mem_sup_of_normal_left.mp hxs
  obtain ⟨l', rfl⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore H) l
  set y : H := l'⁻¹ * ⟨x, hx⟩ with hy
  have hπy : π y = n := by
    rw [hy, map_mul, map_inv, ← hln, hπ]
    group
  set Y := P ⊔ oddCoreOf H with hY
  have hYpre : preOf H (barOf H P) = Y := preOf_barOf hPH
  have hyN : (y : G) ∈ Subgroup.normalizer (Y : Set G) := by
    apply mem_normalizer_of_map_le
    rw [← hYpre]
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨y * z * y⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap] at hz ⊢
    rw [map_mul, map_mul, map_inv, hπy]
    exact (Subgroup.mem_normalizer_iff.mp hn _).mp hz
  have hconj := fusionIsSylowIn_conjSub hsyl (y : G)
  rw [conjSub_eq_of_mem_normalizer hyN] at hconj
  obtain ⟨w, hw, hwP⟩ := exists_conjSub_eq_of_fusionIsSylowIn hsyl hconj
  have h1 : conjSub ((y : G) * w⁻¹) P = P := by
    rw [conjSub_mul, hwP, conjSub_inv_conjSub]
  have h2 := mem_normalizer_of_conjSub_eq h1
  have hwH : w ∈ H := sup_le hPH (oddCoreOf_le H) hw
  have hyw : (y : G) * w⁻¹ ∈ H ⊓ Subgroup.normalizer (P : Set G) :=
    ⟨H.mul_mem y.2 (H.inv_mem hwH), h2⟩
  have hwmem : w ∈ preOf H Lb ⊔ H ⊓ Subgroup.normalizer (P : Set G) :=
    (sup_le (le_sup_of_le_right (le_inf hPH Subgroup.le_normalizer))
      (le_sup_of_le_left hOL)) hw
  have hl'mem : (l' : G) ∈ preOf H Lb := ⟨l', hl, rfl⟩
  have e : x = (l' : G) * (((y : G) * w⁻¹) * w) := by
    rw [hy]
    simp
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl'mem)
    (Subgroup.mul_mem _ (Subgroup.mem_sup_right hyw) hwmem)

end Corr

end CFSG.Goldschmidt.G310
