module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XFinal
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS81Defs

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools

@[expose] def zC {G : Type*} [Group G] (z : G) : ↥(centralizer ({z} : Set G)) :=
  ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩

instance zpowers_zC_normal {G : Type*} [Group G] (z : G) : (zpowers (zC z)).Normal :=
  normal_of_le_center (zpowers_le.mpr (mem_center_iff.mpr fun c =>
    Subtype.ext (mem_centralizer_singleton_iff.mp c.2)))

theorem mem_zpowers_zC {G : Type*} [Group G] {z : G} {y : ↥(centralizer ({z} : Set G))} :
    y ∈ zpowers (zC z) ↔ (y : G) ∈ zpowers z := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp [zC]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa [zC] using hk)⟩

theorem eq_sup_oddCoreIn_of_central {H : Type} [Group H] [Finite H] {N L : Subgroup H}
    (hN2 : IsPGroup 2 N) (hNL : N ≤ L) (hNc : N ≤ centralizer (L : Set H))
    (hodd : Odd (N.relIndex L)) : L = N ⊔ AS76b.oddCoreIn L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' := N.subgroupOf L with hN'
  have hcen : ∀ n ∈ N', ∀ l : ↥L, n * l = l * n := fun n hn l =>
    Subtype.ext (mem_centralizer_iff.mp (hNc hn) l l.2).symm
  have hN'n : N'.Normal := ⟨fun n hn l => by
    rw [← hcen n hn l, mul_inv_cancel_right]
    exact hn⟩
  have hN'2 : IsPGroup 2 N' := hN2.of_equiv (subgroupOfEquivOfLe hNL).symm
  obtain ⟨k, hk⟩ := hN'2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card N') N'.index := by
    rw [hk]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      hodd.not_two_dvd_nat)
  obtain ⟨K, hK⟩ := exists_right_complement'_of_coprime hcop
  have htop : N' ⊔ K = ⊤ := hK.sup_eq_top
  have hKn : K.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← htop]
    refine sup_le (fun n hn => mem_normalizer_iff.mpr fun k => ?_) le_normalizer
    rw [hcen n hn k, mul_inv_cancel_right]
  have hKodd : Odd (Nat.card K) := by
    have h1 := hK.card_mul_card
    have h2 := N'.index_mul_card
    have hpos : 0 < Nat.card N' := Nat.card_pos
    have : Nat.card K = N'.index := by
      have h3 : Nat.card N' * Nat.card K = Nat.card N' * N'.index := by rw [h1, mul_comm, h2]
      exact Nat.eq_of_mul_eq_mul_left hpos h3
    rw [this]
    exact hodd
  have hKO : K ≤ CFSG.Assembly.oddCore L := le_sSup ⟨hKn, hKodd⟩
  apply le_antisymm
  · calc L = (⊤ : Subgroup L).map L.subtype := by rw [← MonoidHom.range_eq_map, range_subtype]
      _ = (N' ⊔ K).map L.subtype := by rw [htop]
      _ = N'.map L.subtype ⊔ K.map L.subtype := Subgroup.map_sup _ _ _
      _ ≤ N ⊔ AS76b.oddCoreIn L :=
        sup_le_sup (by rw [hN', subgroupOf_map_subtype]; exact inf_le_left) (map_mono hKO)
  · exact sup_le hNL (AS76b.oddCoreIn_le L)

section General

variable {H : Type} [Group H]

@[expose] def qbarClosure (z : H) [(zpowers z).Normal] (Q : Subgroup H) :
    Subgroup (H ⧸ zpowers z) :=
  normalClosure ((Q.map (QuotientGroup.mk' (zpowers z)) : Subgroup (H ⧸ zpowers z)) :
    Set (H ⧸ zpowers z))

@[expose] def QbarNoComponentIn (z : H) [(zpowers z).Normal] (Q : Subgroup H) : Prop :=
  goldschmidtLayer (↥(qbarClosure z Q) ⧸ goldschmidtOddCore ↥(qbarClosure z Q)) = ⊥

variable [Finite H]

theorem normal_sup_oddCore_of_goldschmidt (hGA : Asc76X.GoldschmidtTheoremA) {z : H}
    [(zpowers z).Normal] (hzc : ∀ h : H, h * z = z * h) (hz2 : z ^ 2 = 1) (S : Sylow 2 H)
    {Q : Subgroup H} (hQS : Q ≤ S) (hzQ : z ∈ Q)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ zpowers z)
    (hcl : ∀ x ∈ Q, ∀ h : H, h⁻¹ * x * h ∈ (S : Subgroup H) → h⁻¹ * x * h ∈ Q)
    (hnc : QbarNoComponentIn z Q) : (Q ⊔ CFSG.Assembly.oddCore H).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := zpowers z with hNdef
  set π₀ := QuotientGroup.mk' N with hπ₀def
  have hπ₀ : Function.Surjective π₀ := QuotientGroup.mk'_surjective N
  have hker : π₀.ker = N := QuotientGroup.ker_mk' N
  have hNQ : N ≤ Q := zpowers_le.mpr hzQ
  have hNS : N ≤ S := hNQ.trans hQS
  let Sb : Sylow 2 (H ⧸ N) := S.mapSurjective hπ₀
  have hSb : (Sb : Subgroup (H ⧸ N)) = (S : Subgroup H).map π₀ := Sylow.coe_mapSurjective _ _
  set Qb : Subgroup (H ⧸ N) := Q.map π₀ with hQbdef
  have hQbS : Qb ≤ Sb := by
    rw [hSb]
    exact map_mono hQS
  have hQbab : IsMulCommutative Qb := by
    refine isMulCommutative_iff_of_setLike.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hπ₀def, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have := hQab _ (Q.inv_mem hb) _ (Q.inv_mem ha)
    simpa [mul_assoc] using this
  have hclb : ∀ a ∈ Qb, ∀ g : H ⧸ N, g⁻¹ * a * g ∈ (Sb : Subgroup (H ⧸ N)) →
      g⁻¹ * a * g ∈ Qb := by
    rintro _ ⟨a, ha, rfl⟩ g hg
    obtain ⟨h, rfl⟩ := hπ₀ g
    rw [← map_inv, ← map_mul, ← map_mul] at hg ⊢
    rw [hSb] at hg
    obtain ⟨s, hs, hse⟩ := hg
    have hmem : h⁻¹ * a * h ∈ (S : Subgroup H) := by
      have h1 : s⁻¹ * (h⁻¹ * a * h) ∈ N := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hse, inv_mul_cancel]
      have h2 := (S : Subgroup H).mul_mem hs (hNS h1)
      simpa [mul_assoc] using h2
    exact ⟨_, hcl a ha h hmem, rfl⟩
  obtain ⟨ha, hb, -⟩ := hGA (H ⧸ N) Sb Qb hQbS hQbab hclb
  set M : Subgroup (H ⧸ N) := normalClosure (Qb : Set (H ⧸ N)) with hMdef
  have hnc' : goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M) = ⊥ := hnc
  rw [hnc', sup_bot_eq] at ha
  have hcl0 : closure {t : ↥M ⧸ goldschmidtOddCore ↥M |
      t ∈ (((Sb : Subgroup (H ⧸ N)).subgroupOf M).map
        (QuotientGroup.mk' (goldschmidtOddCore ↥M)) ⊓ goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M))
      ∧ t ^ 2 = 1} = ⊥ := by
    rw [closure_eq_bot_iff]
    rintro t ⟨ht, -⟩
    rw [hnc', inf_bot_eq] at ht
    exact ht
  rw [hcl0, sup_bot_eq, ha] at hb
  have hsup : Qb.subgroupOf M ⊔ goldschmidtOddCore ↥M = ⊤ := by
    have h1 := congrArg (Subgroup.comap (QuotientGroup.mk' (goldschmidtOddCore ↥M))) hb
    rwa [comap_map_eq, QuotientGroup.ker_mk', comap_top] at h1
  have hQbM : Qb ≤ M := le_normalClosure
  set O' : Subgroup (H ⧸ N) := AS76b.oddCoreIn M with hO'def
  have hO'eq : O' = (goldschmidtOddCore ↥M).map M.subtype := rfl
  have hMeq : M = Qb ⊔ O' := by
    have h2 := congrArg (Subgroup.map M.subtype) hsup
    rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_eq_left.mpr hQbM, ← hO'eq,
      ← MonoidHom.range_eq_map,
      range_subtype] at h2
    exact h2.symm
  have hMn : M.Normal := normalClosure_normal
  have hO'n : O'.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← normalizer_eq_top_iff.mpr hMn]
    exact AS76b.normalizer_le_normalizer_oddCoreIn M
  set L : Subgroup H := O'.comap π₀ with hLdef
  have hLn : L.Normal := hO'n.comap π₀
  have hNL : N ≤ L := by
    rw [← hker]
    exact ker_le_comap π₀ O'
  have hmapL : L.map π₀ = O' := map_comap_eq_self_of_surjective hπ₀ O'
  have hrel : Odd (N.relIndex L) := by
    rw [← hker, relIndex_ker, hmapL]
    exact AS76b.odd_card_oddCoreIn M
  have hN2 : IsPGroup 2 N := by
    refine IsPGroup.of_card (n := (Nat.card N).factorization 2) ?_
    have hdvd : Nat.card N ∣ 2 ^ 1 := by
      rw [hNdef, Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hz2
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [hj', Nat.prime_two.factorization_pow, Finsupp.single_eq_same]
  have hNc : N ≤ centralizer (L : Set H) := by
    rw [hNdef, zpowers_le, mem_centralizer_iff]
    exact fun h _ => hzc h
  have hLeq := eq_sup_oddCoreIn_of_central hN2 hNL hNc hrel
  have hOL : AS76b.oddCoreIn L ≤ CFSG.Assembly.oddCore H := by
    refine le_sSup ⟨?_, AS76b.odd_card_oddCoreIn L⟩
    rw [← normalizer_eq_top_iff, eq_top_iff, ← normalizer_eq_top_iff.mpr hLn]
    exact AS76b.normalizer_le_normalizer_oddCoreIn L
  have hcomapM : M.comap π₀ = Q ⊔ L := by
    rw [hMeq, ← hmapL, hQbdef, ← Subgroup.map_sup, comap_map_eq, hker,
      sup_eq_left.mpr (hNQ.trans le_sup_left)]
  have hQLn : (Q ⊔ L).Normal := hcomapM ▸ hMn.comap π₀
  have heq : Q ⊔ CFSG.Assembly.oddCore H = (Q ⊔ L) ⊔ CFSG.Assembly.oddCore H := by
    apply le_antisymm
    · exact sup_le_sup_right le_sup_left _
    · refine sup_le (sup_le le_sup_left ?_) le_sup_right
      rw [hLeq]
      exact sup_le (hNQ.trans le_sup_left) (hOL.trans le_sup_right)
  rw [heq]
  have := hQLn
  infer_instance

end General

section Centralizer

variable {G : Type} [Group G]

@[expose] def QbarNoComponent (z : G) (Q : Subgroup G) : Prop :=
  QbarNoComponentIn (zC z) (Q.subgroupOf (centralizer ({z} : Set G)))

variable [Finite G]

theorem centralizer_le_normalizer_of_goldschmidt (hGA : Asc76X.GoldschmidtTheoremA) {z : G}
    {S Q : Subgroup G} (hz2 : z ^ 2 = 1) (hS : IsSylowOf 2 S (centralizer ({z} : Set G)))
    (hQS : Q ≤ S) (hzQ : z ∈ Q) (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ zpowers z)
    (hcl : ∀ x ∈ Q, ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * x * h ∈ S → h⁻¹ * x * h ∈ Q)
    (hnc : QbarNoComponent z Q) :
    centralizer ({z} : Set G) ≤
      normalizer ((Q ⊔ AS76b.oddCoreIn (centralizer ({z} : Set G)) : Subgroup G) : Set G) := by
  set C := centralizer ({z} : Set G) with hCdef
  obtain ⟨T, hT⟩ := hS
  have hSC : S ≤ C := hT ▸ map_subtype_le _
  have hQC : Q ≤ C := hQS.trans hSC
  have hzc : ∀ h : ↥C, h * zC z = zC z * h := fun h =>
    Subtype.ext (mem_centralizer_singleton_iff.mp h.2)
  have hz2' : (zC z) ^ 2 = 1 := Subtype.ext (by simpa [zC] using hz2)
  have hQT : Q.subgroupOf C ≤ (T : Subgroup C) := by
    intro x hx
    have hxS : (x : G) ∈ S := hQS (mem_subgroupOf.mp hx)
    rw [← hT] at hxS
    obtain ⟨y, hy, hyx⟩ := hxS
    rwa [← Subtype.ext hyx]
  have hzQ' : zC z ∈ Q.subgroupOf C := mem_subgroupOf.mpr hzQ
  have hQab' : ∀ x ∈ Q.subgroupOf C, ∀ y ∈ Q.subgroupOf C,
      x * y * x⁻¹ * y⁻¹ ∈ zpowers (zC z) := fun x hx y hy => by
    rw [mem_zpowers_zC]
    exact hQab _ (mem_subgroupOf.mp hx) _ (mem_subgroupOf.mp hy)
  have hcl' : ∀ x ∈ Q.subgroupOf C, ∀ h : ↥C, h⁻¹ * x * h ∈ (T : Subgroup C) →
      h⁻¹ * x * h ∈ Q.subgroupOf C := fun x hx h hh => by
    rw [mem_subgroupOf]
    refine hcl _ (mem_subgroupOf.mp hx) _ h.2 ?_
    rw [← hT]
    exact ⟨_, hh, rfl⟩
  have key := normal_sup_oddCore_of_goldschmidt hGA hzc hz2' T hQT hzQ' hQab' hcl' hnc
  have hmap : ((Q.subgroupOf C) ⊔ CFSG.Assembly.oddCore ↥C).map C.subtype =
      Q ⊔ AS76b.oddCoreIn C := by
    rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_eq_left.mpr hQC]
    rfl
  rw [← hmap]
  exact AS76b.le_normalizer_map_subtype_of_normal C _

omit [Finite G] in
theorem commutator_mem_of_extraspecial {Q : Subgroup G} {z : G}
    (hext : CFSG.IsExtraspecialPGroup 2 Q) (hcen : centerIn Q = zpowers z) {x y : G} (hx : x ∈ Q)
    (hy : y ∈ Q) : x * y * x⁻¹ * y⁻¹ ∈ zpowers z := by
  rw [← hcen]
  have h1 : (⟨x, hx⟩ : Q) * ⟨y, hy⟩ * (⟨x, hx⟩ : Q)⁻¹ * (⟨y, hy⟩ : Q)⁻¹ ∈ center Q := by
    rw [← hext.2.1]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  refine ⟨Q.mul_mem (Q.mul_mem (Q.mul_mem hx hy) (Q.inv_mem hx)) (Q.inv_mem hy),
    mem_centralizer_iff.mpr fun w hw => ?_⟩
  exact congrArg Subtype.val ((mem_center_iff.mp h1) ⟨w, hw⟩)

omit [Finite G] in
theorem sq_eq_one_of_extraspecial {Q : Subgroup G} {z : G}
    (hext : CFSG.IsExtraspecialPGroup 2 Q) (hcen : centerIn Q = zpowers z) : z ^ 2 = 1 := by
  have hc : Nat.card (centerIn Q) = 2 := by
    rw [← hext.2.2.2]
    have h : (center Q).map Q.subtype = centerIn Q := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, mem_centralizer_iff.mpr fun w hw =>
          congrArg Subtype.val ((mem_center_iff.mp hy) ⟨w, hw⟩)⟩
      · rintro ⟨hx, hxc⟩
        exact ⟨⟨x, hx⟩, mem_center_iff.mpr fun w =>
          Subtype.ext (mem_centralizer_iff.mp hxc w w.2), rfl⟩
    rw [← h, card_map_of_injective Q.subtype_injective]
  rw [hcen, Nat.card_zpowers] at hc
  rw [← hc]
  exact pow_orderOf_eq_one z

theorem centralizer_le_normalizer_of_goldschmidt_of_extraspecial
    (hGA : Asc76X.GoldschmidtTheoremA) {z : G} {S Q : Subgroup G}
    (hext : CFSG.IsExtraspecialPGroup 2 Q) (hcen : centerIn Q = zpowers z)
    (hS : IsSylowOf 2 S (centralizer ({z} : Set G))) (hQS : Q ≤ S)
    (hcl : ∀ x ∈ Q, ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * x * h ∈ S → h⁻¹ * x * h ∈ Q)
    (hnc : QbarNoComponent z Q) :
    centralizer ({z} : Set G) ≤
      normalizer ((Q ⊔ AS76b.oddCoreIn (centralizer ({z} : Set G)) : Subgroup G) : Set G) := by
  have hzQ : z ∈ Q := by
    have : z ∈ centerIn Q := by rw [hcen]; exact mem_zpowers z
    exact this.1
  exact centralizer_le_normalizer_of_goldschmidt hGA (sq_eq_one_of_extraspecial hext hcen) hS hQS
    hzQ (fun x hx y hy => commutator_mem_of_extraspecial hext hcen hx hy) hcl hnc

end Centralizer

end CFSG.ComponentClassification.AS81
