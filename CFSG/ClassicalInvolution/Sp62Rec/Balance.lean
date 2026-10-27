module

public import CFSG.ClassicalInvolution.Balance.Basic
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.GroupTheory.ThompsonAxB
import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

theorem oddCoreIn_eq_bot_iff {G : Type*} [Group G] (X : Subgroup G) :
    CFSG.ClassicalInvolution.Balance.oddCoreIn X = ⊥ ↔ CFSG.pPrimeCore 2 ↥X = ⊥ := by
  have h : CFSG.Open.componentClassificationOddCore ↥X = CFSG.pPrimeCore 2 ↥X := by
    unfold CFSG.Open.componentClassificationOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp only [Set.mem_setOf_eq, Nat.coprime_two_left]
  rw [CFSG.ClassicalInvolution.Balance.oddCoreIn, h,
    Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective]

theorem centralizes_of_thompson_AxB {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {P R B : Subgroup H} (hP : IsPGroup p P) (hR : Nat.Coprime (Nat.card R) p)
    (hB : IsPGroup p B) (hRP : R ≤ Subgroup.normalizer (P : Set H))
    (hBP : B ≤ Subgroup.normalizer (P : Set H)) (hRB : ⁅R, B⁆ = ⊥)
    (hfix : P ⊓ Subgroup.centralizer (B : Set H) ≤ Subgroup.centralizer (R : Set H)) :
    P ≤ Subgroup.centralizer (R : Set H) := by
  have hRB' : R ≤ Subgroup.centralizer (B : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRB
  let α : R →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hRP)
  let β : B →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hBP)
  have hα : ∀ (r : R) (x : P), ((α r x : P) : H) = r * x * (r : H)⁻¹ := fun r x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hRP r) x
  have hβ : ∀ (b : B) (x : P), ((β b x : P) : H) = b * x * (b : H)⁻¹ := fun b x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hBP b) x
  have hcomm : ∀ r b, α r * β b = β b * α r := by
    intro r b
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have hrb : (b : H) * r = r * b := Subgroup.mem_centralizer_iff.mp (hRB' r.2) b b.2
    rw [MulAut.mul_apply, MulAut.mul_apply, hα, hβ, hβ, hα]
    calc (r : H) * (b * x * (b : H)⁻¹) * (r : H)⁻¹ = (r * b) * x * ((r : H) * b)⁻¹ := by
          group
      _ = (b * r) * x * ((b : H) * r)⁻¹ := by rw [hrb]
      _ = b * (r * x * (r : H)⁻¹) * (b : H)⁻¹ := by group
  have hfix' : ∀ r x, (∀ b, β b x = x) → α r x = x := by
    intro r x hx
    have hxB : (x : H) ∈ Subgroup.centralizer (B : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h := congrArg Subtype.val (hx ⟨b, hb⟩)
      rw [hβ] at h
      calc b * (x : H) = b * x * b⁻¹ * b := by group
        _ = x * b := by rw [h]
    have hrx : (r : H) * x = x * r :=
      Subgroup.mem_centralizer_iff.mp (hfix ⟨x.2, hxB⟩) r r.2
    apply Subtype.ext
    rw [hα, hrx, mul_inv_cancel_right]
  have hR' : ¬ p ∣ Nat.card R :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hR.symm
  have key := CFSG.GroupTheory.thompson_A_times_B hP hR' hB α β hcomm hfix'
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have h := congrArg (fun f : MulAut P => ((f ⟨x, hx⟩ : P) : H)) (key ⟨r, hr⟩)
  simp only [hα, MulAut.one_apply] at h
  calc r * x = r * x * r⁻¹ * r := by group
    _ = x * r := by rw [h]

theorem commutator_eq_bot_of_isComponent {H : Type*} [Group H] [Finite H]
    (hO : CFSG.pPrimeCore 2 H = ⊥) {K Y Z : Subgroup H} (hK : CFSG.IsComponent K)
    (hY : Odd (Nat.card Y)) (hKY : K ≤ Subgroup.normalizer (Y : Set H)) (hZY : Z ≤ Y)
    (hZK : Z ≤ Subgroup.normalizer (K : Set H)) : ⁅K, Z⁆ = ⊥ := by
  have hcomm : ⁅K, Z⁆ ≤ K ⊓ Y := by
    rw [Subgroup.commutator_le]
    intro k hk z hz
    rw [commutatorElement_def]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : z * k⁻¹ * z⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hZK hz) _).mp (K.inv_mem hk)
      have h2 := K.mul_mem hk h1
      rwa [← mul_assoc, ← mul_assoc] at h2
    · have h1 : k * z * k⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hKY hk) z).mp (hZY hz)
      exact Y.mul_mem h1 (Y.inv_mem (hZY hz))
  have hKnY : ¬ K ≤ Y := by
    intro hKY'
    have hodd : Odd (Nat.card K) := hY.of_dvd_nat (Subgroup.card_dvd_of_le hKY')
    have hbot : K = ⊥ := CFSG.Walter.eq_bot_of_isSubnormal_of_odd hO hK.2 hodd
    exact ((Subgroup.nontrivial_iff_ne_bot K).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial hK.1)) hbot
  have hnormal : ((K ⊓ Y).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro z k hz hk
    exact Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hk hz.1) (K.inv_mem hk),
      (Subgroup.mem_normalizer_iff.mp (hKY hk) z).mp hz.2⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK.1 hnormal with htop | hcen
  · exfalso
    apply hKnY
    intro k hk
    have h : (⟨k, hk⟩ : K) ∈ (K ⊓ Y).subgroupOf K := by
      rw [htop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h)).2
  · have hKYc : K ⊓ Y ≤ Subgroup.centralizer (K : Set H) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 : (⟨z, (Subgroup.mem_inf.mp hz).1⟩ : K) ∈ (K ⊓ Y).subgroupOf K :=
        Subgroup.mem_subgroupOf.mpr hz
      have h3 := Subgroup.mem_center_iff.mp (hcen h1) ⟨k, hk⟩
      exact congrArg Subtype.val h3
    refine CFSG.LocalCores.perfect_double_commutator hK.1.1 (eq_bot_iff.mpr ?_)
    calc ⁅⁅K, Z⁆, K⁆ ≤ ⁅K ⊓ Y, K⁆ := Subgroup.commutator_mono hcomm le_rfl
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKYc
      _ ≤ ⊥ := le_rfl

theorem eq_bot_of_odd_of_normalized_by_centralizer {H : Type*} [Group H] [Finite H]
    (hO : CFSG.pPrimeCore 2 H = ⊥) {a : H} (ha : a ∈ CFSG.pCore 2 H) {Y : Subgroup H}
    (hY : Odd (Nat.card Y)) (hYa : Y ≤ Subgroup.centralizer ({a} : Set H))
    (hnorm : Subgroup.centralizer ({a} : Set H) ≤ Subgroup.normalizer (Y : Set H)) :
    Y = ⊥ := by
  have hP2 : IsPGroup 2 (CFSG.pCore 2 H) := CFSG.pCore_isPGroup
  have hPn : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  have hYP : Disjoint Y (CFSG.pCore 2 H) := by
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    exact Subgroup.disjoint_of_coprime_natCard
      (hn ▸ (Nat.coprime_two_right.mpr hY).pow_right n)
  have hB : IsPGroup 2 (Subgroup.zpowers a) := hP2.to_le (Subgroup.zpowers_le.mpr ha)
  have hcz : Subgroup.centralizer (Subgroup.zpowers a : Set H) =
      Subgroup.centralizer ({a} : Set H) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hfix : CFSG.pCore 2 H ⊓ Subgroup.centralizer (Subgroup.zpowers a : Set H) ≤
      Subgroup.centralizer (Y : Set H) := by
    rintro x ⟨hxP, hxC⟩
    rw [hcz] at hxC
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : x * y⁻¹ * x⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hnorm hxC) _).mp (Y.inv_mem hy)
    have h2 : y * (x * y⁻¹ * x⁻¹) ∈ Y := Y.mul_mem hy h1
    have h3 : y * (x * y⁻¹ * x⁻¹) ∈ CFSG.pCore 2 H := by
      have : y * (x * y⁻¹ * x⁻¹) = (y * x * y⁻¹) * x⁻¹ := by group
      rw [this]
      exact (CFSG.pCore 2 H).mul_mem (hPn.conj_mem x hxP y) ((CFSG.pCore 2 H).inv_mem hxP)
    have h4 : y * (x * y⁻¹ * x⁻¹) = 1 := Subgroup.disjoint_def.mp hYP h2 h3
    calc y * x = (y * (x * y⁻¹ * x⁻¹)) * x * y := by group
      _ = x * y := by rw [h4]; group
  have hPnorm : Subgroup.normalizer (CFSG.pCore 2 H : Set H) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hPn
  have hPY : CFSG.pCore 2 H ≤ Subgroup.centralizer (Y : Set H) :=
    centralizes_of_thompson_AxB hP2 (Nat.coprime_two_right.mpr hY) hB
      (le_top.trans hPnorm.ge) (le_top.trans hPnorm.ge)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (by rw [hcz]; exact hYa)) hfix
  haveI : (CFSG.layer H).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hLn : (CFSG.layer H).Normal := inferInstance
  have hLa : CFSG.layer H ≤ Subgroup.centralizer ({a} : Set H) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (CFSG.WholeGroup.pCore_le_centralizer_layer 2 ha) l hl
  have hLN : CFSG.layer H ≤ Subgroup.normalizer (Y : Set H) := hLa.trans hnorm
  have hKcomm : ∀ K : Subgroup H, CFSG.IsComponent K → ⁅K, Y ⊓ CFSG.layer H⁆ = ⊥ := by
    intro K hK
    refine commutator_eq_bot_of_isComponent hO hK hY ?_ inf_le_left ?_
    · exact (CFSG.LocalCores.component_le_layer hK).trans hLN
    · exact inf_le_right.trans (CFSG.LocalCores.layer_le_normalizer hK)
  have hYLcent : Y ⊓ CFSG.layer H ≤ Subgroup.centralizer (CFSG.layer H : Set H) := by
    rw [Subgroup.le_centralizer_iff]
    refine sSup_le fun K hK => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hKcomm K hK)
  have hYLbot : Y ⊓ CFSG.layer H = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyc : y ∈ (Subgroup.center ↥(CFSG.layer H)).map (CFSG.layer H).subtype :=
      (CFSG.LocalCores.mem_map_center_iff _).mpr ⟨hy.2, hYLcent hy⟩
    have hyP : y ∈ CFSG.pCore 2 H :=
      CFSG.WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot 2 hO hyc
    exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp hYP hy.1 hyP)
  have hYL : Y ≤ Subgroup.centralizer (CFSG.layer H : Set H) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : l * y * l⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hLN hl) y).mp hy
    have h2 : l * y * l⁻¹ * y⁻¹ ∈ Y := Y.mul_mem h1 (Y.inv_mem hy)
    have h3 : l * y * l⁻¹ * y⁻¹ ∈ CFSG.layer H := by
      have : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
      rw [this]
      exact (CFSG.layer H).mul_mem hl (hLn.conj_mem l⁻¹ ((CFSG.layer H).inv_mem hl) y)
    have h4 : l * y * l⁻¹ * y⁻¹ ∈ Y ⊓ CFSG.layer H := Subgroup.mem_inf.mpr ⟨h2, h3⟩
    rw [hYLbot] at h4
    have h5 : l * y * l⁻¹ * y⁻¹ = 1 := Subgroup.mem_bot.mp h4
    calc l * y = (l * y * l⁻¹ * y⁻¹) * (y * l) := by group
      _ = y * l := by rw [h5, one_mul]
  have hF : Y ≤ Subgroup.centralizer (CFSG.generalizedFitting H : Set H) := by
    rw [Subgroup.le_centralizer_iff, CFSG.generalizedFitting.eq_sup,
      CFSG.Fitting_eq_pcore H 2 hO]
    exact sup_le hPY (Subgroup.le_centralizer_iff.mp hYL)
  rw [eq_bot_iff]
  intro y hy
  have hyF : y ∈ CFSG.pCore 2 H ⊔ CFSG.layer H := by
    have := CFSG.centralizer_generalizedFitting_le H (hF hy)
    rwa [CFSG.generalizedFitting.eq_sup, CFSG.Fitting_eq_pcore H 2 hO] at this
  obtain ⟨q, hq, l, hl, hql⟩ := Subgroup.mem_sup_of_normal_left.mp hyF
  have hlc : l ∈ Subgroup.centralizer (CFSG.layer H : Set H) := by
    have hl' : l = q⁻¹ * y := by rw [← hql]; group
    rw [hl']
    exact mul_mem (inv_mem (CFSG.WholeGroup.pCore_le_centralizer_layer 2 hq)) (hYL hy)
  have hlP : l ∈ CFSG.pCore 2 H :=
    CFSG.WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot 2 hO
      ((CFSG.LocalCores.mem_map_center_iff _).mpr ⟨hl, hlc⟩)
  have hyP : y ∈ CFSG.pCore 2 H := by
    rw [← hql]
    exact mul_mem hq hlP
  exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp hYP hy hyP)

theorem oddCoreIn_inf_eq_bot_of_mem_pCore {G : Type*} [Group G] [Finite G] (C : Subgroup G)
    (hO : CFSG.ClassicalInvolution.Balance.oddCoreIn C = ⊥) {a : ↥C}
    (ha : a ∈ CFSG.pCore 2 ↥C) :
    CFSG.ClassicalInvolution.Balance.oddCoreIn (Subgroup.centralizer ({(a : G)} : Set G)) ⊓ C =
      ⊥ := by
  set X : Subgroup G :=
    CFSG.ClassicalInvolution.Balance.oddCoreIn (Subgroup.centralizer ({(a : G)} : Set G)) ⊓ C
    with hX
  have hXC : X ≤ C := inf_le_right
  have hXodd : Odd (Nat.card X) :=
    (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn _).of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_left)
  have hY : X.subgroupOf C = ⊥ := by
    refine eq_bot_of_odd_of_normalized_by_centralizer ((oddCoreIn_eq_bot_iff C).mp hO) ha ?_ ?_ ?_
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv]
      exact hXodd
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have h1 : (y : G) ∈ CFSG.ClassicalInvolution.Balance.oddCoreIn
          (Subgroup.centralizer ({(a : G)} : Set G)) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).1
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (CFSG.ClassicalInvolution.Balance.oddCoreIn_le _ h1)
    · intro c hc
      have hcA : (c : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
      have h1 := CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn
        (Subgroup.centralizer ({(a : G)} : Set G)) hcA
      have h2 : (c : G) ∈ Subgroup.normalizer (C : Set G) := Subgroup.le_normalizer c.2
      rw [← Subgroup.subgroupOf_normalizer_eq hXC]
      change (c : G) ∈ Subgroup.normalizer (X : Set G)
      rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
      intro h
      rw [hX, Subgroup.mem_inf, Subgroup.mem_inf, h1 h, h2 h]
  rw [Subgroup.subgroupOf_eq_bot] at hY
  exact hY.eq_bot_of_le hXC

theorem oddCoreIn_centralizer_inf_eq_bot {G : Type*} [Group G] [Finite G] {a b : G}
    (hO : CFSG.ClassicalInvolution.Balance.oddCoreIn (Subgroup.centralizer ({b} : Set G)) = ⊥)
    (ha : a ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ({b} : Set G))).map
      (Subgroup.centralizer ({b} : Set G)).subtype) :
    CFSG.ClassicalInvolution.Balance.oddCoreIn (Subgroup.centralizer ({a} : Set G)) ⊓
      Subgroup.centralizer ({b} : Set G) = ⊥ := by
  obtain ⟨a', ha', rfl⟩ := ha
  exact oddCoreIn_inf_eq_bot_of_mem_pCore (Subgroup.centralizer ({b} : Set G)) hO ha'

end CFSG.ClassicalInvolution.Sp62Rec
