module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveQbarComp
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveGoldCore
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQ
public import CFSG.Goldschmidt.Steps.IHConseq
public import CFSG.Goldschmidt.Steps.Ind

public section

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalCores CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.RankTwoAltFive

theorem eq_one_or_eq_of_mem_zpowers_of_sq {G : Type*} [Group G] {z c : G} (hz2 : z * z = 1)
    (hc : c ∈ zpowers z) : c = 1 ∨ c = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  have hz : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz2
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, hz, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, hz, one_zpow, mul_one, zpow_one]

theorem card_eq_two_mul_of_ker {G : Type*} [Group G] {Q : Subgroup G} [Finite Q] {Y : Type*}
    [Group Y] [Finite Y] (ι : Q →* Y) {z : G} (hzQ : z ∈ Q) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hzc : ∀ x ∈ Q, z * x = x * z) (hker : ∀ x : Q, ι x = 1 ↔ (x : G) ∈ zpowers z)
    (D : Subgroup Y) :
    Nat.card {x : Q // ι x ∈ D ∧ (x : G) * x = 1 ∧ (x : G) ∉ zpowers z} =
      2 * Nat.card {d : D // (∃ x : Q, ι x = d ∧ (x : G) * x = 1) ∧ (d : Y) ≠ 1} := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have : Fintype {d : D // (∃ x : Q, ι x = d ∧ (x : G) * x = 1) ∧ (d : Y) ≠ 1} :=
    Fintype.ofFinite _
  set z' : Q := ⟨z, hzQ⟩ with hz'
  have hιz : ι z' = 1 := (hker z').mpr (mem_zpowers z)
  let g : {x : Q // ι x ∈ D ∧ (x : G) * x = 1 ∧ (x : G) ∉ zpowers z} →
      {d : D // (∃ x : Q, ι x = d ∧ (x : G) * x = 1) ∧ (d : Y) ≠ 1} := fun x =>
    ⟨⟨ι x.1, x.2.1⟩, ⟨x.1, rfl, x.2.2.1⟩, fun h => x.2.2.2 ((hker x.1).mp h)⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.univ) (fun _ _ => Finset.mem_univ _),
    ← Finset.card_univ (α := {d : D // _}), mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun t _ => ?_
  obtain ⟨⟨x₀, hx₀t, hx₀2⟩, ht1⟩ := t.2
  have hx₀z : (x₀ : G) ∉ zpowers z := fun h => ht1 (by rw [← hx₀t, (hker x₀).mpr h])
  have hx₀D : ι x₀ ∈ D := by rw [hx₀t]; exact (t.1).2
  have h1D : ι (x₀ * z') ∈ D := by rw [map_mul, hιz, mul_one]; exact hx₀D
  have h12 : ((x₀ * z' : Q) : G) * (x₀ * z' : Q) = 1 := by
    change (x₀ : G) * z * (x₀ * z) = 1
    calc (x₀ : G) * z * (x₀ * z) = x₀ * (z * x₀) * z := by group
      _ = x₀ * (x₀ * z) * z := by rw [hzc x₀ x₀.2]
      _ = (x₀ * x₀) * (z * z) := by group
      _ = 1 := by rw [hx₀2, hz2, one_mul]
  have h1z : ((x₀ * z' : Q) : G) ∉ zpowers z := fun h => hx₀z (by
    change (x₀ : G) * z ∈ zpowers z at h
    have := mul_mem h (inv_mem (mem_zpowers z))
    rwa [mul_inv_cancel_right] at this)
  let a : {x : Q // ι x ∈ D ∧ (x : G) * x = 1 ∧ (x : G) ∉ zpowers z} := ⟨x₀, hx₀D, hx₀2, hx₀z⟩
  let b : {x : Q // ι x ∈ D ∧ (x : G) * x = 1 ∧ (x : G) ∉ zpowers z} := ⟨x₀ * z', h1D, h12, h1z⟩
  have hab : a ≠ b := fun h => hz1 (by
    have h' : (x₀ : G) = x₀ * z := congrArg (fun y => ((y.1 : Q) : G)) h
    calc z = (x₀ : G)⁻¹ * (x₀ * z) := by group
      _ = 1 := by rw [← h']; group)
  have hfib : Finset.univ.filter (fun y => g y = t) = {a, b} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hy
      have hy' : ι y.1 = ι x₀ := by
        have := congrArg (fun d => ((d.1 : D) : Y)) hy
        simpa [g, hx₀t] using this
      have hk : ((x₀⁻¹ * y.1 : Q) : G) ∈ zpowers z := (hker _).mp (by
        rw [map_mul, map_inv, hy', inv_mul_cancel])
      rcases eq_one_or_eq_of_mem_zpowers_of_sq hz2 hk with h | h
      · left
        apply Subtype.ext
        apply Subtype.ext
        change (y.1 : G) = x₀
        calc (y.1 : G) = x₀ * ((x₀⁻¹ * y.1 : Q) : G) := by simp
          _ = x₀ := by rw [h, mul_one]
      · right
        apply Subtype.ext
        apply Subtype.ext
        change (y.1 : G) = x₀ * z
        calc (y.1 : G) = x₀ * ((x₀⁻¹ * y.1 : Q) : G) := by simp
          _ = x₀ * z := by rw [h]
    · rintro (rfl | rfl)
      · exact Subtype.ext (Subtype.ext hx₀t)
      · exact Subtype.ext (Subtype.ext (by
          change ι (x₀ * z') = _
          rw [map_mul, hιz, mul_one, hx₀t]))
  rw [hfib, Finset.card_pair hab]

theorem card_comap_eq_mul {Q Y : Type*} [Group Q] [Group Y] [Finite Q] (ι : Q →* Y)
    (D : Subgroup Y) (hD : D ≤ ι.range) : Nat.card (D.comap ι) = Nat.card ι.ker * Nat.card D := by
  set f := ι.comp (D.comap ι).subtype with hf
  have h1 := Subgroup.card_ker_mul_card_range f
  have hrange : f.range = D := by
    ext d
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hd
      obtain ⟨x, hx⟩ := hD hd
      exact ⟨⟨x, by rw [mem_comap, hx]; exact hd⟩, hx⟩
  have hle : ι.ker ≤ D.comap ι := fun x hx => by
    rw [mem_comap, (MonoidHom.mem_ker).mp hx]
    exact one_mem D
  have hkeq : f.ker = ι.ker.subgroupOf (D.comap ι) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.mem_ker]
    rfl
  rw [hrange, hkeq, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at h1
  exact h1.symm

theorem qbarNoComponent_of_card
    (hGA : Asc76X.GoldschmidtTheoremA) {G : Type} [Group G] [Finite G] {z : G}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) {S Q : Subgroup G}
    (hS : IsSylowOf 2 S (centralizer ({z} : Set G))) (hQS : Q ≤ S) (hzQ : z ∈ Q)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ zpowers z)
    (hQsq : ∀ x ∈ Q, x * x ∈ zpowers z)
    (hcl : ∀ x ∈ Q, ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * x * h ∈ S → h⁻¹ * x * h ∈ Q)
    (hSQ : ∀ s ∈ S, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q)
    (hO : AS76b.oddCoreIn (centralizer ({z} : Set G)) = ⊥) (hQ32 : Nat.card Q = 32)
    (hI : Nat.card {x : Q // (x : G) * x = 1 ∧ (x : G) ∉ zpowers z} = 10)
    (horb : ∀ B : Subgroup G, z ∈ B → B ≤ Q → (∀ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ ∈ B) →
      Nat.card B = 8 → Nat.card {x : B // (x : G) * x = 1 ∧ (x : G) ∉ zpowers z} ≠ 4) :
    AS81.QbarNoComponent z Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold AS81.QbarNoComponent AS81.QbarNoComponentIn AS81.qbarClosure
  set C := centralizer ({z} : Set G) with hCdef
  obtain ⟨T₀, hT₀⟩ := hS
  have hTC : S ≤ C := hT₀ ▸ map_subtype_le _
  have hQC : Q ≤ C := hQS.trans hTC
  set Q' := Q.subgroupOf C with hQ'
  have hQ'T : Q' ≤ (T₀ : Subgroup C) := by
    intro x hx
    have hxS : (x : G) ∈ S := hQS (mem_subgroupOf.mp hx)
    rw [← hT₀] at hxS
    obtain ⟨y, hy, hyx⟩ := hxS
    rwa [← Subtype.ext hyx]
  have hcl' : ∀ x ∈ Q', ∀ h : C, h⁻¹ * x * h ∈ (T₀ : Subgroup C) → h⁻¹ * x * h ∈ Q' :=
    fun x hx h hh => by
      rw [mem_subgroupOf]
      refine hcl _ (mem_subgroupOf.mp hx) _ h.2 ?_
      rw [← hT₀]
      exact ⟨_, hh, rfl⟩
  have hQab' : ∀ x ∈ Q', ∀ y ∈ Q', x * y * x⁻¹ * y⁻¹ ∈ zpowers (AS81.zC z) := fun x hx y hy => by
    rw [AS81.mem_zpowers_zC]
    exact hQab _ (mem_subgroupOf.mp hx) _ (mem_subgroupOf.mp hy)
  set Zc := zpowers (AS81.zC z) with hZc
  set π₀ := QuotientGroup.mk' Zc with hπ₀
  have hπ₀s : Function.Surjective π₀ := QuotientGroup.mk'_surjective Zc
  have hker : π₀.ker = Zc := QuotientGroup.ker_mk' Zc
  have hZcQ' : Zc ≤ Q' := zpowers_le.mpr (mem_subgroupOf.mpr hzQ)
  have hZcT : Zc ≤ (T₀ : Subgroup C) := hZcQ'.trans hQ'T
  set Sb : Sylow 2 (C ⧸ Zc) := T₀.mapSurjective hπ₀s with hSb
  have hSbcoe : (Sb : Subgroup (C ⧸ Zc)) = (T₀ : Subgroup C).map π₀ :=
    Sylow.coe_mapSurjective _ _
  set Qb := Q'.map π₀ with hQb
  have hQbS : Qb ≤ Sb := by
    rw [hSbcoe]
    exact map_mono hQ'T
  have hQbab : IsMulCommutative Qb := by
    refine isMulCommutative_iff_of_setLike.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hπ₀, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have := hQab' _ (Q'.inv_mem hb) _ (Q'.inv_mem ha)
    simpa [mul_assoc] using this
  have hQbcl : fusionStronglyClosed (Qb : Set (C ⧸ Zc)) (Sb : Subgroup (C ⧸ Zc)) := by
    rintro _ ⟨a, ha, rfl⟩ g hg
    obtain ⟨h, rfl⟩ := hπ₀s g
    rw [← map_inv, ← map_mul, ← map_mul] at hg ⊢
    rw [hSbcoe] at hg
    obtain ⟨s, hs, hse⟩ := hg
    have hmem : h⁻¹ * a * h ∈ (T₀ : Subgroup C) := by
      have h1 : s⁻¹ * (h⁻¹ * a * h) ∈ Zc := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hse, inv_mul_cancel]
      have h2 := (T₀ : Subgroup C).mul_mem hs (hZcT h1)
      simpa [mul_assoc] using h2
    exact ⟨_, hcl' a ha h hmem, rfl⟩
  have hIH : IH (Nat.card (C ⧸ Zc) + 1) := fun Z _ _ _ =>
    coreStatement_iff.mp (coreStatement_of_goldschmidtTheoremA hGA) Z
  have hTsyl : fusionIsSylowIn 2 (Sb : Subgroup (C ⧸ Zc)) ⊤ :=
    ⟨le_top, Sb.isPGroup', fun P _ hP hTP => Sb.is_maximal' hP hTP⟩
  obtain ⟨hConc, -, -, hC3, -⟩ := N16_of N1 _ hIH (C ⧸ Zc) Sb Qb ⊤ Sb hQbS hQbab hQbcl hQbS hTsyl
    (by rw [card_top]; omega)
  set M : Subgroup (C ⧸ Zc) := normalClosureIn ⊤ Qb with hMdef
  have hMeq : M = normalClosure (Qb : Set (C ⧸ Zc)) := by
    rw [hMdef, normalClosureIn, map_normalClosure _ _ (fun y => ⟨⟨y, mem_top y⟩, rfl⟩)]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_subgroupOf.1 hx
    · intro hy
      exact ⟨⟨y, mem_top y⟩, mem_subgroupOf.2 hy, rfl⟩
  suffices hgoal : goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M) = ⊥ by
    have e : ∀ M₁ M₂ : Subgroup (C ⧸ Zc), M₁ = M₂ →
        goldschmidtLayer (↥M₁ ⧸ goldschmidtOddCore ↥M₁) = ⊥ →
        goldschmidtLayer (↥M₂ ⧸ goldschmidtOddCore ↥M₂) = ⊥ := by
      rintro M₁ M₂ rfl h
      exact h
    exact e M _ hMeq hgoal
  have hMn : M.Normal := by
    rw [hMeq]
    exact normalClosure_normal
  have hQbM : Qb ≤ M := by
    rw [hMeq]
    exact le_normalClosure
  set π := QuotientGroup.mk' (goldschmidtOddCore M) with hπ
  obtain ⟨PM, hPM⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Sb hMn.isSubnormal
  have hPMeq : (PM : Subgroup M) = (Sb : Subgroup (C ⧸ Zc)).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [hPM, subgroupOf_map_subtype]
  have hQbPM : Qb.subgroupOf M ≤ (PM : Subgroup M) := by
    rw [hPMeq]
    exact fun x hx => mem_subgroupOf.2 (hQbS (mem_subgroupOf.1 hx))
  have hclM := stronglyClosed_subgroupOf Sb hQbcl hQbM PM hQbPM
  obtain ⟨Sbar, hSbar, hclbar⟩ := CFSG.ShultStronglyClosedTI.quotient_stronglyClosed PM
    (Qb.subgroupOf M) (goldschmidtOddCore M) hQbPM hclM
  set A := (Qb.subgroupOf M).map π with hA
  have hASbar : A ≤ Sbar := by
    rw [hSbar]
    exact map_mono hQbPM
  have hAab : IsMulCommutative A := isMulCommutative_map (isMulCommutative_subgroupOf hQbab M) π
  have hO' : goldschmidtOddCore (M ⧸ goldschmidtOddCore M) = ⊥ :=
    goldschmidtOddCore_quotient_eq_bot M
  have hSbarT : (Sbar : Subgroup (M ⧸ goldschmidtOddCore M)) = barOf M Sb := by
    rw [hSbar, hPMeq]
    rfl
  have hopen : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M), IsComponentOf K.1 ⊤ :=
    fun K => (CFSG.isComponent_iff_open K.1).mp K.2
  have htype : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M),
      goldschmidtSimpleType (K.1 ⧸ center K.1) := fun K => hConc.2.2 K.1 (hopen K)
  have hind : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M), InducesOmega1 A K.1 Sbar :=
    fun K => by
      rw [hSbarT]
      exact hC3 K.1 (hopen K)
  have hcover : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M), ∀ a ∈ A, ∃ x ∈ A ⊓ K.1,
      ∀ y ∈ K.1, a⁻¹ * y * a = x⁻¹ * y * x :=
    fun K => N17_of N11b _ Sbar A K.1 hASbar hAab hclbar hO' (hopen K) (htype K) (hind K)
  have hAeq := hConc.2.1
  have hAinv : ∀ t ∈ (Sbar : Subgroup (M ⧸ goldschmidtOddCore M)) ⊓
      goldschmidtLayer (M ⧸ goldschmidtOddCore M), t ^ 2 = 1 → t ∈ A := by
    intro t ht ht2
    have h1 : A = _ := hAeq
    rw [h1]
    refine mem_sup_right (subset_closure ⟨?_, ht2⟩)
    have hSbarT' : (Sbar : Subgroup (M ⧸ goldschmidtOddCore M)) =
        ((Sb : Subgroup (C ⧸ Zc)).subgroupOf M).map π := hSbarT
    rw [← hSbarT']
    exact ht
  have hAO : CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) ≤ A := by
    have h1 : A = _ := hAeq
    rw [h1]
    exact le_sup_left
  have hOC : goldschmidtOddCore C = ⊥ :=
    (map_eq_bot_iff_of_injective _ C.subtype_injective).mp hO
  have hOM : goldschmidtOddCore M = ⊥ := by
    set O' : Subgroup (C ⧸ Zc) := AS76b.oddCoreIn M with hO'def
    have hO'eq : O' = (goldschmidtOddCore ↥M).map M.subtype := rfl
    have hO'n : O'.Normal := by
      rw [← normalizer_eq_top_iff, eq_top_iff, ← normalizer_eq_top_iff.mpr hMn]
      exact AS76b.normalizer_le_normalizer_oddCoreIn M
    set L : Subgroup C := O'.comap π₀ with hLdef
    have hLn : L.Normal := hO'n.comap π₀
    have hNL : Zc ≤ L := by
      rw [← hker]
      exact ker_le_comap π₀ O'
    have hmapL : L.map π₀ = O' := map_comap_eq_self_of_surjective hπ₀s O'
    have hrel : Odd (Zc.relIndex L) := by
      rw [← hker, relIndex_ker, hmapL]
      exact AS76b.odd_card_oddCoreIn M
    have hN2 : IsPGroup 2 Zc := by
      refine IsPGroup.of_card (n := (Nat.card Zc).factorization 2) ?_
      have hdvd : Nat.card Zc ∣ 2 ^ 1 := by
        rw [hZc, Nat.card_zpowers, pow_one]
        refine orderOf_dvd_of_pow_eq_one ?_
        apply Subtype.ext
        simp [AS81.zC, sq, hz2]
      obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      rw [hj', Nat.prime_two.factorization_pow, Finsupp.single_eq_same]
    have hNc : Zc ≤ centralizer (L : Set C) := by
      rw [hZc, zpowers_le, mem_centralizer_iff]
      exact fun h _ => Subtype.ext (mem_centralizer_singleton_iff.mp h.2)
    have hLeq := AS81.eq_sup_oddCoreIn_of_central hN2 hNL hNc hrel
    have hOL : AS76b.oddCoreIn L = ⊥ := by
      have hn : (AS76b.oddCoreIn L).Normal := by
        rw [← normalizer_eq_top_iff, eq_top_iff, ← normalizer_eq_top_iff.mpr hLn]
        exact AS76b.normalizer_le_normalizer_oddCoreIn L
      have hle : AS76b.oddCoreIn L ≤ goldschmidtOddCore C :=
        le_sSup ⟨hn, AS76b.odd_card_oddCoreIn L⟩
      rwa [hOC, le_bot_iff] at hle
    have hO'bot : O' = ⊥ := by
      rw [← hmapL, hLeq, hOL, sup_bot_eq, eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_bot, hπ₀, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hx
    rw [hO'eq] at hO'bot
    exact (map_eq_bot_iff_of_injective _ M.subtype_injective).mp hO'bot
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hπ, QuotientGroup.ker_mk', hOM]
  have hιM : ∀ x : Q, π₀ (inclusion hQC x) ∈ M := fun x =>
    hQbM (mem_map.mpr ⟨inclusion hQC x, mem_subgroupOf.mpr x.2, rfl⟩)
  set ι : Q →* M ⧸ goldschmidtOddCore M :=
    π.comp ((π₀.comp (inclusion hQC)).codRestrict M hιM) with hι
  have hιA : ∀ x : Q, ι x ∈ A := by
    intro x
    refine mem_map.mpr ⟨⟨π₀ (inclusion hQC x), hιM x⟩, ?_, rfl⟩
    rw [mem_subgroupOf]
    exact mem_map.mpr ⟨inclusion hQC x, mem_subgroupOf.mpr x.2, rfl⟩
  have hιsurj : ∀ a ∈ A, ∃ x : Q, ι x = a := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : (w : C ⧸ Zc) ∈ Qb := hw
    obtain ⟨c, hc, hcw⟩ := mem_map.mp hw'
    refine ⟨⟨c, mem_subgroupOf.mp hc⟩, ?_⟩
    rw [hι, MonoidHom.comp_apply]
    exact congrArg π (Subtype.ext hcw)
  have hιker : ∀ x : Q, ι x = 1 ↔ (x : G) ∈ zpowers z := by
    intro x
    have h1 : ι x = π ⟨π₀ (inclusion hQC x), hιM x⟩ := rfl
    rw [h1, ← map_one π, hπinj.eq_iff]
    constructor
    · intro h
      have h2 : π₀ (inclusion hQC x) = 1 := congrArg Subtype.val h
      rw [hπ₀, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact AS81.mem_zpowers_zC.mp h2
    · intro h
      apply Subtype.ext
      change π₀ (inclusion hQC x) = 1
      rw [hπ₀, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact AS81.mem_zpowers_zC.mpr h
  have hzc : ∀ x ∈ Q, z * x = x * z := fun x hx =>
    (mem_centralizer_singleton_iff.mp (hQC hx)).symm
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨x, rfl⟩ := hιsurj a ha
    rw [← map_pow, sq, hιker]
    exact hQsq x x.2
  have hker2 : Nat.card ι.ker = 2 := by
    have hkeq : ι.ker = (zpowers z).subgroupOf Q := by
      ext x
      rw [MonoidHom.mem_ker, hιker, mem_subgroupOf]
    rw [hkeq, Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr hzQ)).toEquiv,
      Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  have hA16 : Nat.card A = 16 := by
    have h1 := Subgroup.card_ker_mul_card_range ι
    have hrange : ι.range = A := by
      ext a
      constructor
      · rintro ⟨x, rfl⟩
        exact hιA x
      · intro ha
        obtain ⟨x, hx⟩ := hιsurj a ha
        exact ⟨x, hx⟩
    rw [hrange, hker2, hQ32] at h1
    omega
  have hconjz : ∀ c : C, ∀ w ∈ zpowers z, (c : G) * w * (c : G)⁻¹ = w := by
    intro c w hw
    rcases eq_one_or_eq_of_mem_zpowers_of_sq hz2 hw with rfl | rfl
    · group
    · rw [mem_centralizer_singleton_iff.mp c.2, mul_inv_cancel_right]
  have hlift : ∀ n : M ⧸ goldschmidtOddCore M, (∀ b ∈ A, n * b * n⁻¹ ∈ A) → ∀ x : Q,
      ∃ x' : Q, ι x' = n * ι x * n⁻¹ ∧ (x' : G) * x' = (x : G) * x := by
    intro n hn x
    obtain ⟨x', hx'⟩ := hιsurj _ (hn _ (hιA x))
    refine ⟨x', hx', ?_⟩
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore M) n
    obtain ⟨c, hc⟩ := hπ₀s (m : C ⧸ Zc)
    have h1 : (⟨π₀ (inclusion hQC x'), hιM x'⟩ : M) =
        m * ⟨π₀ (inclusion hQC x), hιM x⟩ * m⁻¹ := by
      apply hπinj
      rw [map_mul, map_mul, map_inv]
      exact hx'
    have h2 : π₀ (inclusion hQC x') = π₀ (c * inclusion hQC x * c⁻¹) := by
      have := congrArg Subtype.val h1
      rw [map_mul, map_mul, map_inv, hc]
      exact this
    rw [hπ₀, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
    have h3 : (x' : G)⁻¹ * ((c : G) * x * (c : G)⁻¹) ∈ zpowers z := AS81.mem_zpowers_zC.mp h2
    have hxx := hconjz c _ (hQsq x x.2)
    have hcxC : (c : G) * x * (c : G)⁻¹ ∈ C := mul_mem (mul_mem c.2 (hQC x.2)) (inv_mem c.2)
    rcases eq_one_or_eq_of_mem_zpowers_of_sq hz2 h3 with h4 | h4
    · have e : (x' : G) = (c : G) * x * (c : G)⁻¹ := by
        calc (x' : G) = (c : G) * x * (c : G)⁻¹ *
            ((x' : G)⁻¹ * ((c : G) * x * (c : G)⁻¹))⁻¹ := by group
          _ = (c : G) * x * (c : G)⁻¹ := by rw [h4, inv_one, mul_one]
      rw [e, show (c : G) * x * (c : G)⁻¹ * ((c : G) * x * (c : G)⁻¹) =
        (c : G) * (x * x) * (c : G)⁻¹ by group, hxx]
    · have e : (x' : G) = (c : G) * x * (c : G)⁻¹ * z := by
        calc (x' : G) = (c : G) * x * (c : G)⁻¹ *
            ((x' : G)⁻¹ * ((c : G) * x * (c : G)⁻¹))⁻¹ := by group
          _ = (c : G) * x * (c : G)⁻¹ * z := by
            rw [h4, show z⁻¹ = z from inv_eq_of_mul_eq_one_right hz2]
      have hzx := mem_centralizer_singleton_iff.mp hcxC
      rw [e, show (c : G) * x * (c : G)⁻¹ * z * ((c : G) * x * (c : G)⁻¹ * z) =
        (c : G) * x * (c : G)⁻¹ * (z * ((c : G) * x * (c : G)⁻¹)) * z by group, ← hzx,
        show (c : G) * x * (c : G)⁻¹ * ((c : G) * x * (c : G)⁻¹ * z) * z =
          (c : G) * (x * x) * (c : G)⁻¹ * (z * z) by group, hz2, mul_one, hxx]
  have hsq_eq : ∀ x₁ x₂ : Q, ι x₁ = ι x₂ → (x₁ : G) * x₁ = (x₂ : G) * x₂ := by
    intro x₁ x₂ h
    have hk : ((x₁⁻¹ * x₂ : Q) : G) ∈ zpowers z :=
      (hιker _).mp (by rw [map_mul, map_inv, h, inv_mul_cancel])
    have e : (x₂ : G) = x₁ * ((x₁⁻¹ * x₂ : Q) : G) := by simp
    rcases eq_one_or_eq_of_mem_zpowers_of_sq hz2 hk with h1 | h1
    · rw [h1, mul_one] at e
      rw [e]
    · rw [h1] at e
      rw [e, show (x₁ : G) * z * (x₁ * z) = x₁ * (z * x₁) * z by group, hzc x₁ x₁.2,
        show (x₁ : G) * (x₁ * z) * z = x₁ * x₁ * (z * z) by group, hz2, mul_one]
  classical
  have hsing : ∀ n : M ⧸ goldschmidtOddCore M, (∀ b ∈ A, n * b * n⁻¹ ∈ A) → ∀ a ∈ A,
      ((∃ x : Q, ι x = a ∧ (x : G) * x = 1) ↔
        (∃ x : Q, ι x = n * a * n⁻¹ ∧ (x : G) * x = 1)) := by
    intro n hn a ha
    obtain ⟨x, rfl⟩ := hιsurj a ha
    obtain ⟨x', hx', hxx'⟩ := hlift n hn x
    constructor
    · rintro ⟨y, hy, hy2⟩
      refine ⟨x', hx', ?_⟩
      rw [hxx', hsq_eq x y hy.symm]
      exact hy2
    · rintro ⟨y, hy, hy2⟩
      refine ⟨x, rfl, ?_⟩
      rw [← hxx', hsq_eq x' y (hx'.trans hy.symm)]
      exact hy2
  have h5 : Nat.card {a : A // (∃ x : Q, ι x = a ∧ (x : G) * x = 1) ∧
      (a : M ⧸ goldschmidtOddCore M) ≠ 1} = 5 := by
    have h := card_eq_two_mul_of_ker ι hzQ hz1 hz2 hzc hιker A
    have hl : Nat.card {x : Q // ι x ∈ A ∧ (x : G) * x = 1 ∧ (x : G) ∉ zpowers z} = 10 := by
      rw [← hI]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun x => ⟨fun h => h.2, fun h => ⟨hιA x, h⟩⟩)
    omega
  set σ : S →* MulAut (M ⧸ goldschmidtOddCore M) :=
    (MonoidHom.mk' (Asc76X.conjQuot hMn) (Asc76X.conjQuot_mul hMn)).comp
      (π₀.comp (inclusion hTC)) with hσ
  have hSQ' : ∀ (s : S) (x : Q), (s : G) * x * (s : G)⁻¹ ∈ Q := fun s x => hSQ s s.2 x x.2
  have hequiv : ∀ (s : S) (x : Q), σ s (ι x) = ι ⟨(s : G) * x * (s : G)⁻¹, hSQ' s x⟩ :=
    fun s x => rfl
  have hσA : ∀ s, ∀ a ∈ A, σ s a ∈ A := by
    intro s a ha
    obtain ⟨x, rfl⟩ := hιsurj a ha
    rw [hequiv]
    exact hιA _
  have horbY : ∀ D : Subgroup (M ⧸ goldschmidtOddCore M), D ≤ A → Nat.card D = 4 →
      (∀ s, ∀ d ∈ D, σ s d ∈ D) →
      Nat.card {d : D // (∃ x : Q, ι x = d ∧ (x : G) * x = 1) ∧
        (d : M ⧸ goldschmidtOddCore M) ≠ 1} ≠ 2 := by
    intro D hDA hD4 hDσ h2
    set B : Subgroup G := (D.comap ι).map Q.subtype with hB
    have hmemB : ∀ x : Q, (x : G) ∈ B ↔ ι x ∈ D := fun x =>
      ⟨fun ⟨y, hy, hyx⟩ => by rwa [← Subtype.ext hyx], fun h => ⟨x, h, rfl⟩⟩
    have hzB : z ∈ B := (hmemB ⟨z, hzQ⟩).mpr (by
      rw [(hιker _).mpr (mem_zpowers z)]
      exact one_mem D)
    have hBQ : B ≤ Q := map_subtype_le _
    have hBS : ∀ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ ∈ B := by
      intro s hs b hb
      obtain ⟨x, hx, rfl⟩ := hb
      refine (hmemB ⟨_, hSQ' ⟨s, hs⟩ x⟩).mpr ?_
      rw [← hequiv ⟨s, hs⟩ x]
      exact hDσ _ _ hx
    have hB8 : Nat.card B = 8 := by
      have hDr : D ≤ ι.range := fun d hd => by
        obtain ⟨x, hx⟩ := hιsurj d (hDA hd)
        exact ⟨x, hx⟩
      rw [hB, card_map_of_injective Q.subtype_injective, card_comap_eq_mul ι D hDr, hker2, hD4]
    have h4 : Nat.card {x : B // (x : G) * x = 1 ∧ (x : G) ∉ zpowers z} = 4 := by
      have h := card_eq_two_mul_of_ker ι hzQ hz1 hz2 hzc hιker D
      rw [h2] at h
      have h' : Nat.card {x : Q // ι x ∈ D ∧ (x : G) * x = 1 ∧ (x : G) ∉ zpowers z} = 4 := by
        rw [h]
      rw [← h']
      exact Nat.card_congr
        { toFun := fun x => ⟨⟨x, hBQ x.1.2⟩, (hmemB _).mp x.1.2, x.2⟩
          invFun := fun y => ⟨⟨y.1, (hmemB y.1).mpr y.2.1⟩, y.2.2⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
    exact horb B hzB hBQ hBS hB8 h4
  have hE := isEmpty_componentIndex_of_singular Sbar hO' hASbar hA2 hAinv hAO htype hind hcover
    hA16 (fun a => ∃ x : Q, ι x = a ∧ (x : G) * x = 1) hsing h5 σ hσA horbY
  rw [goldschmidtLayer, sSup_eq_bot]
  intro K hK
  exact (hE.false ⟨K, (CFSG.isComponent_iff_open K).mpr hK⟩).elim

end CFSG.ComponentClassification.RankTwoAltFive
