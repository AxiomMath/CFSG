module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PumpDown
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm13Aux
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.Sol76 CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_coreActionKernel_of_odd_commutator {X A J R : Subgroup G} (hA : IsTwoComponentIn A X)
    (hJX : J ≤ twoLayerIn X) (hJ : ⁅J, J⁆ = J) (hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J))
    (hm : ¬ J ≤ coreActionKernel A)
    (ht : Nat.card (↥A ⧸ Open.fusionZStar ↥A) = Nat.card (↥J ⧸ Open.fusionZStar ↥J))
    (hRX : R ≤ X) (hRA : R ≤ normalizer (A : Set G)) (hodd : ¬ 2 ∣ Nat.card ↥⁅R, J⁆) :
    R ≤ coreActionKernel A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := twoLayerIn X with hL
  have hLX : L ≤ X := map_subtype_le _
  set O := pPrimeCore 2 ↥X with hO
  have hOn : O.Normal := pPrimeCore_normal
  set π := QuotientGroup.mk' O with hπ
  set A' := A.subgroupOf X with hA'
  set K := A'.map π with hK
  have hKc : IsComponent K :=
    (CatalogueBPrimeJoin.canonical_prime_component_lift (X := ↥X) 2).2.1 hA.2
  set E := layer (↥X ⧸ O) with hE
  set Z := E ⊓ centralizer (K : Set (↥X ⧸ O)) with hZ
  have hKE : K ≤ E := component_le_layer hKc
  have hEK : E ≤ normalizer (K : Set (↥X ⧸ O)) := layer_le_normalizer hKc
  have hZE : Z ≤ E := inf_le_left
  have hZn : (Z.subgroupOf E).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hZE]
    refine le_normalizer_of_forall_conj_mem fun c hc x hx => ?_
    obtain ⟨hxE, hxC⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨mul_mem (mul_mem hc hxE) (inv_mem hc), ?_⟩
    rw [mem_centralizer_iff]
    intro k hk
    have hk' : c⁻¹ * k * c ∈ K := by
      have := (mem_normalizer_iff.mp (hEK (inv_mem hc)) k).mp hk
      simpa using this
    have h1 : c⁻¹ * k * c * x = x * (c⁻¹ * k * c) := (mem_centralizer_iff.mp hxC) _ hk'
    calc k * (c * x * c⁻¹) = c * (c⁻¹ * k * c * x) * c⁻¹ := by group
      _ = c * (x * (c⁻¹ * k * c)) * c⁻¹ := by rw [h1]
      _ = c * x * c⁻¹ * k := by group
  set φ := QuotientGroup.mk' (Z.subgroupOf E) with hφ
  let φK : ↥K →* ↥E ⧸ Z.subgroupOf E := φ.comp (Subgroup.inclusion hKE)
  have hφKsurj : Function.Surjective φK := by
    intro q
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf E) q
    obtain ⟨u, hu, huc⟩ := exists_mem_mul_centralizer hKc e.2
    refine ⟨⟨u, hu⟩, ?_⟩
    change φ ⟨u, hKE hu⟩ = φ e
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      mem_subgroupOf]
    refine mem_inf.mpr ⟨mul_mem (inv_mem (hKE hu)) e.2, ?_⟩
    rw [mem_centralizer_iff]
    intro k hk
    exact (huc k hk).eq
  have hφKker : φK.ker = center ↥K := by
    ext k
    rw [MonoidHom.mem_ker, mem_center_iff]
    change φ ⟨k, hKE k.2⟩ = 1 ↔ _
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    constructor
    · intro h l
      exact Subtype.ext ((mem_centralizer_iff.mp (mem_inf.mp h).2) l l.2)
    · intro h
      refine mem_inf.mpr ⟨hKE k.2, ?_⟩
      rw [mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val (h ⟨l, hl⟩)
  let eQ : ↥K ⧸ center ↥K ≃* ↥E ⧸ Z.subgroupOf E :=
    (QuotientGroup.quotientMulEquivOfEq hφKker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φK hφKsurj)
  have hQcard : Nat.card (↥E ⧸ Z.subgroupOf E) = (center ↥K).index :=
    (Nat.card_congr eQ.toEquiv).symm
  have hKs : IsSimpleGroup (↥K ⧸ center ↥K) := hKc.1.2.1
  have hQs : IsSimpleGroup (↥E ⧸ Z.subgroupOf E) := MulEquiv.isSimpleGroup eQ.symm
  have hAK : Nat.card (↥A ⧸ Open.fusionZStar ↥A) = (center ↥K).index := by
    have h3 := index_fusionZStar_eq_index_center hKc.2 (L := A') rfl
    have h2 : Nat.card (↥A ⧸ Open.fusionZStar ↥A) = Nat.card (↥A' ⧸ Open.fusionZStar ↥A') :=
      Nat.card_congr (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hA.1).symm).toEquiv
    rw [h2]
    exact h3
  have hLE : ∀ x : ↥L, π (Subgroup.inclusion hLX x) ∈ E := by
    rintro ⟨x, hx⟩
    refine (LBalance.Quot.map_pLayer_eq_layer_quotient (H := ↥X) (p := 2)).le ?_
    obtain ⟨y, hy, hyx⟩ := hx
    refine mem_map_of_mem π ?_
    have : Subgroup.inclusion hLX ⟨x, ⟨y, hy, hyx⟩⟩ = y := Subtype.ext hyx.symm
    rw [this]
    exact hy
  let Ψ : ↥L →* ↥E ⧸ Z.subgroupOf E :=
    φ.comp ((π.comp (Subgroup.inclusion hLX)).codRestrict E hLE)
  have hΨ : ∀ x : ↥L, Ψ x = φ ⟨π (Subgroup.inclusion hLX x), hLE x⟩ := fun _ => rfl
  have hsurj : ∀ J : Subgroup G, ∀ hJL : J ≤ L, ⁅J, J⁆ = J →
      IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) → ¬ J ≤ coreActionKernel A →
      Nat.card (↥A ⧸ Open.fusionZStar ↥A) = Nat.card (↥J ⧸ Open.fusionZStar ↥J) →
      (Ψ.comp (Subgroup.inclusion hJL)).range = ⊤ := by
    intro J hJL hJ hJq hm ht
    have hJperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJ
    set ψ := Ψ.comp (Subgroup.inclusion hJL) with hψdef
    have hψ : ∀ j : ↥J, ψ j = φ ⟨π (Subgroup.inclusion hLX (Subgroup.inclusion hJL j)),
        hLE (Subgroup.inclusion hJL j)⟩ := fun _ => rfl
    have hkerψ : ψ.ker ≠ ⊤ := by
      intro h
      apply hm
      intro j hj
      have h1 : ψ ⟨j, hj⟩ = 1 := MonoidHom.mem_ker.mp (by rw [h]; exact mem_top _)
      rw [hψ, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
      have hjC := (mem_inf.mp h1).2
      have hjN : j ∈ normalizer (A : Set G) :=
        ((hJL.trans (FooteLit.twoLayerIn_le_normalizer hA.1 hA.2)) hj)
      refine ⟨hjN, fun a ha => ?_⟩
      set xa : ↥X := ⟨a, hA.1 ha⟩ with hxa
      set xj : ↥X := ⟨j, hLX (hJL hj)⟩ with hxj
      have hcomm' : (xa : ↥X ⧸ O) * (xj : ↥X ⧸ O) = (xj : ↥X ⧸ O) * (xa : ↥X ⧸ O) :=
        (mem_centralizer_iff.mp hjC) (π xa) ⟨xa, mem_subgroupOf.mpr ha, rfl⟩
      have hO1 : xa⁻¹ * xj⁻¹ * xa * xj ∈ O := by
        have h1 : ((xa⁻¹ * xj⁻¹ * xa * xj : ↥X) : ↥X ⧸ O) = 1 := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
            QuotientGroup.mk_inv, QuotientGroup.mk_inv, mul_assoc _ (xa : ↥X ⧸ O), hcomm']
          group
        exact (QuotientGroup.eq_one_iff _).mp h1
      have hmemX : a⁻¹ * j⁻¹ * a * j ∈ oddCoreIn X := ⟨_, hO1, rfl⟩
      have hmemA : a⁻¹ * j⁻¹ * a * j ∈ A := by
        have h3 : j⁻¹ * a * j⁻¹⁻¹ ∈ A := (mem_normalizer_iff.mp (inv_mem hjN) a).mp ha
        rw [inv_inv] at h3
        rw [mul_assoc, mul_assoc]
        refine mul_mem (inv_mem ha) ?_
        simpa [mul_assoc] using h3
      exact oddCoreIn_inf_le hA.1 (mem_inf.mpr ⟨hmemX, hmemA⟩)
    have hleZ : ψ.ker ≤ Open.fusionZStar ↥J :=
      le_fusionZStar_of_normal hJperf hJq ψ.normal_ker hkerψ
    have hidx : (Open.fusionZStar ↥J).index = (center ↥K).index := by
      change Nat.card (↥J ⧸ Open.fusionZStar ↥J) = _
      rw [← ht, hAK]
    apply eq_top_of_card_eq
    apply le_antisymm (card_le_of_le le_top |>.trans (by rw [card_top]))
    rw [hQcard, ← hidx, ← index_ker]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
      (index_dvd_of_le hleZ)
  have hJL : J ≤ L := hJX
  have hrJ := hsurj J hJL hJ hJq hm ht
  have hXL : ∀ x ∈ X, ∀ y ∈ L, x * y * x⁻¹ ∈ L := by
    intro x hx y hy
    obtain ⟨y', hy', rfl⟩ := hy
    have hn : (pLayer ↥X 2).Normal := inferInstance
    exact ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹, hn.conj_mem y' hy' _, rfl⟩
  have hcL : ⁅R, J⁆ ≤ L := commutator_le.mpr fun r hr' j hj => by
    rw [commutatorElement_def]
    exact mul_mem (hXL r (hRX hr') j (hJL hj)) (inv_mem (hJL hj))
  set ψJ := Ψ.comp (Subgroup.inclusion hJL) with hψJ
  set ψc := Ψ.comp (Subgroup.inclusion hcL) with hψc
  have hcn : ψc.range.Normal := by
    refine ⟨fun x hx q => ?_⟩
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨j, rfl⟩ : q ∈ ψJ.range := hrJ ▸ mem_top q
    have hjc : (j : G) * c * (j : G)⁻¹ ∈ ⁅R, J⁆ :=
      ((mem_normalizer_iff.mp (normalizer_commutator_ge_right R J j.2)) c).mp c.2
    refine ⟨⟨_, hjc⟩, ?_⟩
    have he : Subgroup.inclusion hcL ⟨_, hjc⟩ =
        Subgroup.inclusion hJL j * Subgroup.inclusion hcL c * (Subgroup.inclusion hJL j)⁻¹ :=
      Subtype.ext (by simp)
    rw [hψc, MonoidHom.comp_apply, he, map_mul, map_mul, map_inv]
    rfl
  have hJperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJ
  have hPperf : ⁅(⊤ : Subgroup (↥E ⧸ Z.subgroupOf E)), (⊤ : Subgroup (↥E ⧸ Z.subgroupOf E))⁆ =
      ⊤ := by
    have h := congrArg (Subgroup.map ψJ) hJperf.commutator_eq_top
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, hrJ] at h
    exact h
  have hbot : ψc.range = ⊥ := by
    have := hcn
    rcases hQs.eq_bot_or_eq_top_of_normal ψc.range with h | h
    · exact h
    · exfalso
      have hdvd : Nat.card (↥E ⧸ Z.subgroupOf E) ∣ Nat.card ↥⁅R, J⁆ := by
        have h1 := card_range_dvd ψc
        rw [h, card_top] at h1
        exact h1
      have hPodd : Odd (Nat.card (↥E ⧸ Z.subgroupOf E)) :=
        Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 => hodd (h2.trans hdvd))
      have hsolv : Group.IsSolvable (↥E ⧸ Z.subgroupOf E) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hPodd
      have hnt : Nontrivial (↥E ⧸ Z.subgroupOf E) := hQs.toNontrivial
      have hPp : Group.IsPerfect (↥E ⧸ Z.subgroupOf E) :=
        ⟨by rw [_root_.commutator_def]; exact hPperf⟩
      exact Group.IsPerfect.not_isSolvable _ hsolv
  have hcZ : ∀ c : ↥⁅R, J⁆, π (Subgroup.inclusion hLX (Subgroup.inclusion hcL c)) ∈ Z := by
    intro c
    have h1 : ψc c = 1 := by
      have h2 : ψc c ∈ ψc.range := ⟨c, rfl⟩
      rw [hbot, mem_bot] at h2
      exact h2
    rw [hψc, MonoidHom.comp_apply, hΨ, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_subgroupOf] at h1
    exact h1
  have hEc : (layer (↥X ⧸ O)).Characteristic := LocalCores.layer_characteristic
  have hEn : (layer (↥X ⧸ O)).Normal := inferInstance
  have hgK : ∀ r (hr : r ∈ R), ∀ k ∈ K, π ⟨r, hRX hr⟩ * k * (π ⟨r, hRX hr⟩)⁻¹ ∈ K := by
    intro r hr k hk
    obtain ⟨a', ha', rfl⟩ := mem_map.mp hk
    refine ⟨⟨r, hRX hr⟩ * a' * ⟨r, hRX hr⟩⁻¹, ?_, by simp⟩
    show _ ∈ A.subgroupOf X
    rw [mem_subgroupOf]
    have h1 : r * (a' : G) * r⁻¹ ∈ A :=
      (mem_normalizer_iff.mp (hRA hr) a').mp (mem_subgroupOf.mp ha')
    simpa using h1
  have hgZ : ∀ r (hr : r ∈ R), ∀ z ∈ Z, π ⟨r, hRX hr⟩ * z * (π ⟨r, hRX hr⟩)⁻¹ ∈ Z := by
    intro r hr z hz
    obtain ⟨hzE, hzC⟩ := mem_inf.mp hz
    refine mem_inf.mpr ⟨hEn.conj_mem z hzE _, ?_⟩
    rw [mem_centralizer_iff]
    intro k hk
    have hk' : (π ⟨r, hRX hr⟩)⁻¹ * k * π ⟨r, hRX hr⟩ ∈ K := by
      have h1 := hgK r⁻¹ (inv_mem hr) k hk
      have h2 : π ⟨r⁻¹, hRX (inv_mem hr)⟩ = (π ⟨r, hRX hr⟩)⁻¹ := by
        rw [← map_inv]; rfl
      rw [h2, inv_inv] at h1
      exact h1
    have h1 := (mem_centralizer_iff.mp hzC) _ hk'
    calc k * (π ⟨r, hRX hr⟩ * z * (π ⟨r, hRX hr⟩)⁻¹) =
        π ⟨r, hRX hr⟩ * ((π ⟨r, hRX hr⟩)⁻¹ * k * π ⟨r, hRX hr⟩ * z) * (π ⟨r, hRX hr⟩)⁻¹ := by
          group
      _ = π ⟨r, hRX hr⟩ * (z * ((π ⟨r, hRX hr⟩)⁻¹ * k * π ⟨r, hRX hr⟩)) * (π ⟨r, hRX hr⟩)⁻¹ := by
          rw [h1]
      _ = π ⟨r, hRX hr⟩ * z * (π ⟨r, hRX hr⟩)⁻¹ * k := by group
  have heZ : ∀ e ∈ E, ∀ z ∈ Z, e * z * e⁻¹ ∈ Z := by
    intro e he z hz
    have h1 := hZn.conj_mem ⟨z, hZE hz⟩ (mem_subgroupOf.mpr hz) ⟨e, he⟩
    rw [mem_subgroupOf] at h1
    simpa using h1
  have hcomm : ∀ r (hr : r ∈ R), ∀ k ∈ K,
      π ⟨r, hRX hr⟩ * k * (π ⟨r, hRX hr⟩)⁻¹ * k⁻¹ ∈ centralizer (K : Set _) := by
    intro r hr k hk
    set g := π ⟨r, hRX hr⟩ with hg
    obtain ⟨j, hj⟩ : φ ⟨k, hKE hk⟩ ∈ ψJ.range := hrJ ▸ mem_top _
    set a := π (Subgroup.inclusion hLX (Subgroup.inclusion hJL j)) with ha
    have haE : a ∈ E := hLE _
    have hj' : ((⟨a, haE⟩ : ↥E) : ↥E ⧸ Z.subgroupOf E) =
        ((⟨k, hKE hk⟩ : ↥E) : ↥E ⧸ Z.subgroupOf E) := hj
    have hzZ : a⁻¹ * k ∈ Z := by
      have h1 := QuotientGroup.eq.mp hj'
      rw [mem_subgroupOf] at h1
      simpa using h1
    set z := a⁻¹ * k with hz
    have hk : k = a * z := by rw [hz]; group
    have hga : g * a * g⁻¹ * a⁻¹ ∈ Z := by
      have h1 := hcZ ⟨⁅r, (j : G)⁆, commutator_mem_commutator hr j.2⟩
      have h2 : π (Subgroup.inclusion hLX (Subgroup.inclusion hcL
          ⟨⁅r, (j : G)⁆, commutator_mem_commutator hr j.2⟩)) = ⁅g, a⁆ := by
        rw [hg, ha, ← map_commutatorElement]
        congr 1
      rw [h2, commutatorElement_def] at h1
      exact h1
    have hgz : g * z * g⁻¹ * z⁻¹ ∈ Z := mul_mem (hgZ r hr z hzZ) (inv_mem hzZ)
    have hmem : g * k * g⁻¹ * k⁻¹ ∈ Z := by
      have e : g * k * g⁻¹ * k⁻¹ = (g * a * g⁻¹ * a⁻¹) * (a * (g * z * g⁻¹ * z⁻¹) * a⁻¹) := by
        rw [hk]; group
      rw [e]
      exact mul_mem hga (heZ a haE _ hgz)
    exact (mem_inf.mp hmem).2
  set Rb := (π.comp (Subgroup.inclusion hRX)).range with hRb
  have hKR : ⁅K, Rb⁆ ≤ centralizer (K : Set _) := by
    rw [commutator_le]
    rintro k hk _ ⟨⟨r, hr⟩, rfl⟩
    change ⁅k, π ⟨r, hRX hr⟩⁆ ∈ centralizer (K : Set _)
    have h1 := hcomm r hr k⁻¹ (inv_mem hk)
    rw [inv_inv] at h1
    have hc := (mem_centralizer_iff.mp h1) k hk
    have h2 : ⁅k, π ⟨r, hRX hr⟩⁆ = π ⟨r, hRX hr⟩ * k⁻¹ * (π ⟨r, hRX hr⟩)⁻¹ * k := by
      rw [commutatorElement_def]
      calc k * π ⟨r, hRX hr⟩ * k⁻¹ * (π ⟨r, hRX hr⟩)⁻¹ =
          k * (π ⟨r, hRX hr⟩ * k⁻¹ * (π ⟨r, hRX hr⟩)⁻¹ * k) * k⁻¹ := by group
        _ = π ⟨r, hRX hr⟩ * k⁻¹ * (π ⟨r, hRX hr⟩)⁻¹ * k * k * k⁻¹ := by rw [hc]
        _ = π ⟨r, hRX hr⟩ * k⁻¹ * (π ⟨r, hRX hr⟩)⁻¹ * k := by group
    rw [h2]
    exact h1
  have hKperf : Group.IsPerfect ↥K := hKc.1.1
  have hKR' : ⁅K, Rb⁆ = ⊥ :=
    LocalCores.perfect_double_commutator hKperf (commutator_eq_bot_iff_le_centralizer.mpr hKR)
  intro r hr
  refine ⟨hRA hr, fun a haA => ?_⟩
  have hπc : π ⟨a⁻¹ * r⁻¹ * a * r, mul_mem (mul_mem (mul_mem (inv_mem (hA.1 haA))
      (inv_mem (hRX hr))) (hA.1 haA)) (hRX hr)⟩ = 1 := by
    have h1 : ⁅π ⟨a⁻¹, inv_mem (hA.1 haA)⟩, π ⟨r⁻¹, inv_mem (hRX hr)⟩⁆ ∈ ⁅K, Rb⁆ :=
      commutator_mem_commutator ⟨⟨a⁻¹, inv_mem (hA.1 haA)⟩, mem_subgroupOf.mpr (inv_mem haA), rfl⟩
        ⟨⟨r⁻¹, inv_mem hr⟩, rfl⟩
    rw [hKR', mem_bot, ← map_commutatorElement] at h1
    rw [← h1]
    congr 1
    exact Subtype.ext (by simp [commutatorElement_def])
  have hO1 : (⟨a⁻¹ * r⁻¹ * a * r, mul_mem (mul_mem (mul_mem (inv_mem (hA.1 haA))
      (inv_mem (hRX hr))) (hA.1 haA)) (hRX hr)⟩ : ↥X) ∈ O :=
    (QuotientGroup.eq_one_iff _).mp hπc
  have hmemX : a⁻¹ * r⁻¹ * a * r ∈ oddCoreIn X := ⟨_, hO1, rfl⟩
  have hmemA : a⁻¹ * r⁻¹ * a * r ∈ A := by
    have h3 : r⁻¹ * a * r⁻¹⁻¹ ∈ A := (mem_normalizer_iff.mp (inv_mem (hRA hr)) a).mp haA
    rw [inv_inv] at h3
    rw [mul_assoc, mul_assoc]
    refine mul_mem (inv_mem haA) ?_
    simpa [mul_assoc] using h3
  exact oddCoreIn_inf_le hA.1 (mem_inf.mpr ⟨hmemX, hmemA⟩)

end CFSG.ComponentClassification.Sol76T13
