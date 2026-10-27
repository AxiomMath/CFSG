module

public import CFSG.LocalAnalysis.EvenBN.GMS.GoldschmidtTypeInvolution
public import CFSG.LocalAnalysis.ComponentClassification.CommutingComponentFamily
public import CFSG.LocalAnalysis.EvenBN.GMS.LocalSetup

public section

namespace CFSG.LocalAnalysis.EvenBN.GMS

open Subgroup CFSG.Open CFSG.ComponentClassification
open scoped MatrixGroups

section Projection

variable {G : Type*} [Group G]

theorem le_normalizer_centralizer (K : Subgroup G) :
    K ≤ normalizer (centralizer (K : Set G) : Set G) :=
  (le_centralizer_iff.mp le_rfl).trans (Subgroup.centralizer_le_normalizer _)

theorem conj_mem_centralizer {K : Subgroup G} {x c : G} (hx : x ∈ normalizer (K : Set G))
    (hc : c ∈ centralizer (K : Set G)) : x * c * x⁻¹ ∈ centralizer (K : Set G) := by
  refine mem_centralizer_iff.mpr fun k hk => ?_
  have hk' : x⁻¹ * k * x⁻¹⁻¹ ∈ K := (mem_normalizer_iff.mp (inv_mem hx) k).mp hk
  have h1 : (x⁻¹ * k * x⁻¹⁻¹) * c = c * (x⁻¹ * k * x⁻¹⁻¹) := (mem_centralizer_iff.mp hc) _ hk'
  calc k * (x * c * x⁻¹) = x * ((x⁻¹ * k * x⁻¹⁻¹) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * k * x⁻¹⁻¹)) * x⁻¹ := by rw [h1]
    _ = x * c * x⁻¹ * k := by group

theorem exists_inv_mul_mem_centralizer {K : Subgroup G} {x : G}
    (hx : x ∈ K ⊔ centralizer (K : Set G)) :
    ∃ k ∈ K, k⁻¹ * x ∈ centralizer (K : Set G) := by
  have hx' : x ∈ ((K ⊔ centralizer (K : Set G) : Subgroup G) : Set G) := hx
  rw [coe_mul_of_left_le_normalizer_right K _ (le_normalizer_centralizer K)] at hx'
  obtain ⟨k, hk, c, hc, rfl⟩ := hx'
  exact ⟨k, hk, by rwa [inv_mul_cancel_left]⟩

theorem eq_of_inv_mul_mem_centralizer {K : Subgroup G}
    (hZ : K ⊓ centralizer (K : Set G) = ⊥) {x k₁ k₂ : G} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (h₁ : k₁⁻¹ * x ∈ centralizer (K : Set G)) (h₂ : k₂⁻¹ * x ∈ centralizer (K : Set G)) :
    k₁ = k₂ := by
  have hmem : k₁⁻¹ * k₂ ∈ K ⊓ centralizer (K : Set G) := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem hk₁) hk₂, ?_⟩
    have : k₁⁻¹ * k₂ = (k₁⁻¹ * x) * (k₂⁻¹ * x)⁻¹ := by group
    rw [this]
    exact mul_mem h₁ (inv_mem h₂)
  rw [hZ, mem_bot] at hmem
  exact (inv_mul_eq_one.mp hmem)

@[expose] noncomputable def factorProj (K M : Subgroup G) (hZ : K ⊓ centralizer (K : Set G) = ⊥)
    (hM : M ≤ K ⊔ centralizer (K : Set G)) : M →* G where
  toFun x := Classical.choose (exists_inv_mul_mem_centralizer (hM x.2))
  map_one' := by
    obtain ⟨hk, hc⟩ := Classical.choose_spec (exists_inv_mul_mem_centralizer (hM (one_mem M)))
    exact eq_of_inv_mul_mem_centralizer hZ hk (one_mem K) hc (by simp [one_mem])
  map_mul' x y := by
    obtain ⟨hk, hc⟩ := Classical.choose_spec (exists_inv_mul_mem_centralizer (hM (x * y).2))
    obtain ⟨hkx, hcx⟩ := Classical.choose_spec (exists_inv_mul_mem_centralizer (hM x.2))
    obtain ⟨hky, hcy⟩ := Classical.choose_spec (exists_inv_mul_mem_centralizer (hM y.2))
    refine eq_of_inv_mul_mem_centralizer hZ hk (mul_mem hkx hky) hc ?_
    set kx := Classical.choose (exists_inv_mul_mem_centralizer (hM x.2))
    set ky := Classical.choose (exists_inv_mul_mem_centralizer (hM y.2))
    have hcomm : (kx⁻¹ * (x : G)) * ky⁻¹ = ky⁻¹ * (kx⁻¹ * (x : G)) :=
      ((mem_centralizer_iff.mp hcx) ky⁻¹ (inv_mem hky)).symm
    have : (kx * ky)⁻¹ * ((x * y : M) : G) = (kx⁻¹ * (x : G)) * (ky⁻¹ * (y : G)) := by
      calc (kx * ky)⁻¹ * ((x * y : M) : G) = ky⁻¹ * (kx⁻¹ * (x : G)) * (y : G) := by
            rw [coe_mul]; group
        _ = (kx⁻¹ * (x : G)) * ky⁻¹ * (y : G) := by rw [hcomm]
        _ = _ := by group
    rw [this]
    exact mul_mem hcx hcy

variable {K M : Subgroup G} {hZ : K ⊓ centralizer (K : Set G) = ⊥}
  {hM : M ≤ K ⊔ centralizer (K : Set G)}

theorem factorProj_mem (x : M) : factorProj K M hZ hM x ∈ K :=
  (Classical.choose_spec (exists_inv_mul_mem_centralizer (hM x.2))).1

theorem factorProj_inv_mul_mem (x : M) :
    (factorProj K M hZ hM x)⁻¹ * x ∈ centralizer (K : Set G) :=
  (Classical.choose_spec (exists_inv_mul_mem_centralizer (hM x.2))).2

theorem factorProj_eq (x : M) {k : G} (hk : k ∈ K) (hc : k⁻¹ * x ∈ centralizer (K : Set G)) :
    factorProj K M hZ hM x = k :=
  eq_of_inv_mul_mem_centralizer hZ (factorProj_mem x) hk (factorProj_inv_mul_mem x) hc

theorem factorProj_eq_one_iff (x : M) :
    factorProj K M hZ hM x = 1 ↔ (x : G) ∈ centralizer (K : Set G) := by
  constructor
  · intro h1
    have := factorProj_inv_mul_mem (hZ := hZ) (hM := hM) x
    rwa [h1, inv_one, one_mul] at this
  · intro hx
    exact factorProj_eq x (one_mem K) (by rwa [inv_one, one_mul])

end Projection

theorem card_map_of_injOn {G N : Type*} [Group G] [Group N] (f : G →* N) (K : Subgroup G)
    (hf : ∀ a ∈ K, ∀ b ∈ K, f a = f b → a = b) : Nat.card (K.map f) = Nat.card K := by
  refine (Nat.card_congr (Equiv.ofBijective (fun x : K => (⟨f x, mem_map_of_mem f x.2⟩ :
    K.map f)) ⟨fun x y hxy => Subtype.ext (hf x x.2 y y.2 (congrArg Subtype.val hxy)), ?_⟩)).symm
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem isComponentOf_conj {G : Type*} [Group G] {K : Subgroup G} (hK : IsComponentOf K ⊤)
    (g : G) :
    IsComponentOf (K.map (MulAut.conj g).toMonoidHom) ⊤ :=
  (LocalComponents.equiv_iff (MulAut.conj g) K).mpr hK

theorem layer_eq_sSup (H : Type*) [Group H] :
    CFSG.layer H = sSup {K : Subgroup H | IsComponentOf K ⊤} := by
  rw [CFSG.layer_eq_componentClassification]
  rfl

theorem le_layer_of_isComponentOf {G : Type*} [Group G] {K : Subgroup G}
    (hK : IsComponentOf K ⊤) : K ≤ CFSG.layer G := by
  rw [layer_eq_sSup]
  exact le_sSup hK

namespace LocalSetting

variable {H : Type} [Group H] [Finite H] {A : Subgroup H} {t : H} {U V D : Subgroup H} {n : ℕ}

section Centralizer

variable (h : LocalSetting A t U V D n)
include h

theorem U_ne_bot : U ≠ ⊥ := by
  intro hU
  have h1 := h.card_U
  rw [hU, Subgroup.card_bot] at h1
  have := h.four_le
  omega

theorem A_le_normalClosure : A ≤ normalClosure (V : Set H) := by
  have := h.isSimpleGroup
  have hn : ((normalClosure (V : Set H)).subgroupOf A).Normal :=
    (normalClosure_normal (s := (V : Set H))).subgroupOf A
  rcases hn.eq_bot_or_eq_top with hb | ht
  · exfalso
    apply h.U_ne_bot
    rw [eq_bot_iff]
    intro u hu
    have h1 : (⟨u, h.U_le hu⟩ : A) ∈ (normalClosure (V : Set H)).subgroupOf A :=
      mem_subgroupOf.mpr (subset_normalClosure (h.U_le_V hu))
    rw [hb, mem_bot] at h1
    exact mem_bot.mpr (congrArg Subtype.val h1)
  · intro a ha
    have : (⟨a, ha⟩ : A) ∈ (normalClosure (V : Set H)).subgroupOf A := by rw [ht]; exact mem_top _
    exact this

theorem eq_one_or_eq_t_of_mem_zpowers {x : H} (hx : x ∈ zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, h.orderOf_t]
  have h2 : (k % ((2 : ℕ) : ℤ)) = 0 ∨ (k % ((2 : ℕ) : ℤ)) = 1 := by omega
  rcases h2 with h0 | h1
  · left; rw [h0, zpow_zero]
  · right; rw [h1, zpow_one]

theorem exists_conj_eq_t {s : H} (hs : s ∈ centralizer (A : Set H)) (hs2 : orderOf s = 2) :
    ∃ c ∈ centralizer (A : Set H), s = c * t * c⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := h.exists_sylow_centralizer
  let s' : centralizer (A : Set H) := ⟨s, hs⟩
  have hs'2 : IsPGroup 2 (zpowers s') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_mk, hs2, pow_one])
  obtain ⟨R, hR⟩ := hs'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (centralizer (A : Set H)) T R
  have hmem : s' ∈ ((g • T : Sylow 2 (centralizer (A : Set H))) :
      Subgroup (centralizer (A : Set H))) := by
    rw [hg]; exact hR (mem_zpowers s')
  rw [Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨x, hxT, hx⟩ := hmem
  rw [hT] at hxT
  have hxt : (x : H) ∈ zpowers t := mem_subgroupOf.mp hxT
  rcases h.eq_one_or_eq_t_of_mem_zpowers hxt with h1 | h1
  · exfalso
    have : x = 1 := Subtype.ext h1
    rw [this, smul_one] at hx
    have h3 : s = 1 := (congrArg Subtype.val hx).symm
    rw [h3, orderOf_one] at hs2
    omega
  · refine ⟨g, g.2, ?_⟩
    have h3 := congrArg Subtype.val hx
    rw [MulAut.smul_def, MulAut.conj_apply] at h3
    simp only [coe_mul, coe_inv] at h3
    rw [h1] at h3
    exact h3.symm

theorem t_not_mem_centralizer_V : t ∉ centralizer (V : Set H) := by
  intro ht
  have hVU : V ≤ U := by
    rw [← h.V_inf_centralizer]
    exact le_inf le_rfl fun v hv => mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp ht) v hv)
  have h1 := Subgroup.card_le_of_le hVU
  rw [h.card_V, h.card_U] at h1
  have := h.four_le
  nlinarith

theorem centralizer_normalClosure_eq_bot :
    centralizer (normalClosure (V : Set H) : Set H) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := centralizer (normalClosure (V : Set H) : Set H) with hNdef
  have hNn : N.Normal := inferInstance
  have hNA : N ≤ centralizer (A : Set H) := centralizer_le h.A_le_normalClosure
  have hodd : Odd (Nat.card N) := by
    by_contra heven
    have h2 : 2 ∣ Nat.card N := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp heven)
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 2 h2
    obtain ⟨c, -, hsc⟩ := h.exists_conj_eq_t (hNA s.2) (by rw [orderOf_coe]; exact hs)
    have htN : t ∈ N := by
      have h3 := hNn.conj_mem _ s.2 c⁻¹
      rw [hsc] at h3
      simpa [mul_assoc] using h3
    exact h.t_not_mem_centralizer_V (centralizer_le subset_normalClosure htN)
  have hle : N ≤ CFSG.Open.standardComponentOddCore H := le_sSup ⟨hNn, hodd⟩
  rw [h.oddCore_eq_bot] at hle
  exact le_bot_iff.mp hle

theorem le_normalClosure_of_isComponentOf {K : Subgroup H} (hK : IsComponentOf K ⊤) :
    K ≤ normalClosure (V : Set H) := by
  rcases LocalComponents.normal_contains_or_commutes K (normalClosure (V : Set H)) hK with
    hle | hc
  · exact hle
  · exfalso
    have hKC := commutator_eq_bot_iff_le_centralizer.mp hc
    rw [h.centralizer_normalClosure_eq_bot] at hKC
    have := Quasisimple.nontrivial hK.2.2
    exact (K.nontrivial_iff_ne_bot.mp this) (le_bot_iff.mp hKC)

theorem diag_facts {K : Subgroup H} (hK : IsComponentOf K ⊤)
    (hne : K.map (MulAut.conj t⁻¹).toMonoidHom ≠ K) {y : H} (hy : y ∈ K) :
    y * (t⁻¹ * y * t) ∈ CFSG.layer H ∧ y * (t⁻¹ * y * t) ∈ centralizer ({t} : Set H) ∧
      t⁻¹ * y * t ∈ K.map (MulAut.conj t⁻¹).toMonoidHom ∧
      t⁻¹ * y * t ∈ centralizer (K : Set H) := by
  have hKt := isComponentOf_conj hK t⁻¹
  have hyt : t⁻¹ * y * t ∈ K.map (MulAut.conj t⁻¹).toMonoidHom :=
    ⟨y, hy, by simp⟩
  have hKtC : K.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer (K : Set H) :=
    commutator_eq_bot_iff_le_centralizer.mp (LocalComponents.commute_of_ne _ K hKt hK hne)
  have hcomm : y * (t⁻¹ * y * t) = (t⁻¹ * y * t) * y :=
    ((mem_centralizer_iff.mp (hKtC hyt)) y hy)
  refine ⟨mul_mem (le_layer_of_isComponentOf hK hy) (le_layer_of_isComponentOf hKt hyt), ?_, hyt,
    hKtC hyt⟩
  rw [mem_centralizer_singleton_iff]
  have htt : t * t = 1 := h.t_mul_t
  have htinv : t⁻¹ = t := h.t_inv
  calc y * (t⁻¹ * y * t) * t = y * t⁻¹ * y * (t * t) := by group
    _ = y * t * y := by rw [htt, htinv, mul_one]
    _ = t * ((t⁻¹ * y * t) * y) := by group
    _ = t * (y * (t⁻¹ * y * t)) := by rw [hcomm]

end Centralizer

instance layer_normal (H : Type*) [Group H] : (CFSG.layer H).Normal := by
  have : (CFSG.layer H).Characteristic := CFSG.LocalCores.layer_characteristic
  infer_instance

section Layer

variable (h : LocalSetting A t U V D n)
  (hE : sSup {K : Subgroup H | IsComponentOf K ⊤ ∧ K ≤ normalClosure (V : Set H)} =
    normalClosure (V : Set H))
include h hE

theorem layer_eq_normalClosure : CFSG.layer H = normalClosure (V : Set H) := by
  rw [layer_eq_sSup]
  apply le_antisymm
  · exact sSup_le fun K hK => h.le_normalClosure_of_isComponentOf hK
  · rw [← hE]
    exact sSup_le_sSup fun K hK => hK.1

omit h in
theorem normalClosure_le_normalizer {K : Subgroup H} (hK : IsComponentOf K ⊤) :
    normalClosure (V : Set H) ≤ normalizer (K : Set H) := by
  rw [← hE]
  refine sSup_le fun K' hK' => ?_
  by_cases hKK : K' = K
  · rw [hKK]
    exact le_normalizer
  · exact (commutator_eq_bot_iff_le_centralizer.mp
      (LocalComponents.commute_of_ne K' K hK'.1 hK hKK)).trans
        (Subgroup.centralizer_le_normalizer _)

omit h in
theorem normalClosure_le_sup_centralizer {K : Subgroup H} (hK : IsComponentOf K ⊤) :
    normalClosure (V : Set H) ≤ K ⊔ centralizer (K : Set H) := by
  rw [← hE]
  refine sSup_le fun K' hK' => ?_
  by_cases hKK : K' = K
  · rw [hKK]
    exact le_sup_left
  · exact (commutator_eq_bot_iff_le_centralizer.mp
      (LocalComponents.commute_of_ne K' K hK'.1 hK hKK)).trans le_sup_right

theorem inf_centralizer_eq_bot_of_isComponentOf {K : Subgroup H} (hK : IsComponentOf K ⊤) :
    K ⊓ centralizer (K : Set H) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzK, hzC⟩ := mem_inf.mp hz
  have hle : normalClosure (V : Set H) ≤ centralizer ({z} : Set H) := by
    rw [← hE]
    refine sSup_le fun K' hK' => ?_
    by_cases hKK : K' = K
    · rw [hKK]
      intro y hy
      exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hzC) y hy)
    · intro y hy
      have hyC := commutator_eq_bot_iff_le_centralizer.mp
        (LocalComponents.commute_of_ne K' K hK'.1 hK hKK) hy
      exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hyC) z hzK).symm
  have hzM : z ∈ centralizer (normalClosure (V : Set H) : Set H) :=
    mem_centralizer_iff.mpr fun y hy => mem_centralizer_singleton_iff.mp (hle hy)
  rwa [h.centralizer_normalClosure_eq_bot] at hzM

theorem center_eq_bot_of_isComponentOf {K : Subgroup H} (hK : IsComponentOf K ⊤) :
    center K = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : (z : H) ∈ K ⊓ centralizer (K : Set H) := mem_inf.mpr ⟨z.2,
    mem_centralizer_iff.mpr fun y hy => congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)⟩
  rw [h.inf_centralizer_eq_bot_of_isComponentOf hE hK, mem_bot] at hz'
  exact mem_bot.mpr (Subtype.ext hz')

theorem isSimpleGroup_of_isComponentOf {K : Subgroup H} (hK : IsComponentOf K ⊤) :
    IsSimpleGroup K := by
  have hZ := h.center_eq_bot_of_isComponentOf hE hK
  let e : (K ⧸ center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have := hK.2.2.2
  exact e.symm.isSimpleGroup

theorem inf_eq_bot_of_not_le {K : Subgroup H} (hK : IsComponentOf K ⊤) (hAK : ¬ A ≤ K) :
    A ⊓ K = ⊥ := by
  have := h.isSimpleGroup
  have hAN : A ≤ normalizer (K : Set H) :=
    h.A_le_normalClosure.trans (normalClosure_le_normalizer hE hK)
  have hn : (K.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hAN
  rcases hn.eq_bot_or_eq_top with hb | ht
  · rw [inf_comm, ← subgroupOf_map_subtype, hb, Subgroup.map_bot]
  · exfalso
    apply hAK
    intro a ha
    have : (⟨a, ha⟩ : A) ∈ K.subgroupOf A := by rw [ht]; exact mem_top _
    exact this

theorem A_le_layer : A ≤ CFSG.layer H := by
  rw [h.layer_eq_normalClosure hE]
  exact h.A_le_normalClosure

theorem layer_le_sup_centralizer {K : Subgroup H} (hK : IsComponentOf K ⊤) :
    CFSG.layer H ≤ K ⊔ centralizer (K : Set H) := by
  rw [h.layer_eq_normalClosure hE]
  exact normalClosure_le_sup_centralizer hE hK

variable (htype : ∀ K : Subgroup H, IsComponentOf K ⊤ → K ≤ normalClosure (V : Set H) →
  goldschmidtSimpleType (K ⧸ center K))
include htype

theorem not_le_centralizer_A {K : Subgroup H} (hK : IsComponentOf K ⊤) :
    ¬ K ≤ centralizer (A : Set H) := by
  intro hKA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM := h.le_normalClosure_of_isComponentOf hK
  have h2 : 2 ∣ Nat.card K :=
    (two_dvd_card_of_goldschmidtSimpleType (htype K hK hKM)).trans (card_quotient_dvd_card _)
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨c, hc, hsc⟩ := h.exists_conj_eq_t (hKA s.2) (by rw [orderOf_coe]; exact hs)
  set K' := K.map (MulAut.conj c⁻¹).toMonoidHom with hK'def
  have hK' : IsComponentOf K' ⊤ := (LocalComponents.equiv_iff (MulAut.conj c⁻¹) K).mpr hK
  have htK' : t ∈ K' := ⟨s, s.2, by
    change c⁻¹ * (s : H) * c⁻¹⁻¹ = t
    rw [hsc]
    group⟩
  have hK'A : K' ≤ centralizer (A : Set H) := by
    rintro _ ⟨k, hk, rfl⟩
    refine mem_centralizer_iff.mpr fun a ha => ?_
    have hca : a * c = c * a := (mem_centralizer_iff.mp hc) a ha
    have hka : a * k = k * a := (mem_centralizer_iff.mp (hKA hk)) a ha
    change a * (c⁻¹ * k * c⁻¹⁻¹) = c⁻¹ * k * c⁻¹⁻¹ * a
    have hca' : a * c⁻¹ = c⁻¹ * a := by
      calc a * c⁻¹ = c⁻¹ * (c * a) * c⁻¹ := by group
        _ = c⁻¹ * (a * c) * c⁻¹ := by rw [hca]
        _ = c⁻¹ * a := by group
    calc a * (c⁻¹ * k * c⁻¹⁻¹) = (a * c⁻¹) * k * c := by group
      _ = c⁻¹ * (a * k) * c := by rw [hca']; group
      _ = c⁻¹ * (k * a) * c := by rw [hka]
      _ = c⁻¹ * k * (a * c) := by group
      _ = c⁻¹ * k * c⁻¹⁻¹ * a := by rw [hca]; group
  have hUK' : U ≤ K' := by
    rw [← h.closure_commutator]
    refine (closure_le K').mpr ?_
    rintro x ⟨v, hv, rfl⟩
    have hvN : v ∈ normalizer (K' : Set H) :=
      normalClosure_le_normalizer hE hK' (subset_normalClosure hv)
    have h1 : v⁻¹ * t⁻¹ * v⁻¹⁻¹ ∈ K' :=
      (mem_normalizer_iff.mp (inv_mem hvN) t⁻¹).mp (inv_mem htK')
    have h2 : v⁻¹ * (t⁻¹ * v * t) = (v⁻¹ * t⁻¹ * v⁻¹⁻¹) * t := by group
    rw [h2]
    exact mul_mem h1 htK'
  have hUA : U ≤ A ⊓ centralizer (A : Set H) := le_inf h.U_le (hUK'.trans hK'A)
  rw [h.inf_centralizer_eq_bot] at hUA
  exact h.U_ne_bot (le_bot_iff.mp hUA)

theorem normalClosure_A_eq : normalClosure (A : Set H) = normalClosure (V : Set H) := by
  apply le_antisymm
  · exact normalClosure_le_normal h.A_le_normalClosure
  · rw [← hE]
    refine sSup_le fun K hK => ?_
    rcases LocalComponents.normal_contains_or_commutes K (normalClosure (A : Set H)) hK.1 with
      hle | hc
    · exact hle
    · exact absurd ((commutator_eq_bot_iff_le_centralizer.mp hc).trans
        (centralizer_le subset_normalClosure)) (h.not_le_centralizer_A hE htype hK.1)

theorem inf_centralizer_component_eq_bot {K : Subgroup H} (hK : IsComponentOf K ⊤) :
    A ⊓ centralizer (K : Set H) = ⊥ := by
  have := h.isSimpleGroup
  have hAN : A ≤ normalizer (K : Set H) :=
    h.A_le_normalClosure.trans (normalClosure_le_normalizer hE hK)
  have hn : ((centralizer (K : Set H)).subgroupOf A).Normal :=
    ⟨fun x hx g => mem_subgroupOf.mpr (by
      simpa only [coe_mul, coe_inv] using
        conj_mem_centralizer (hAN g.2) (mem_subgroupOf.mp hx))⟩
  rcases hn.eq_bot_or_eq_top with hb | ht
  · rw [inf_comm, ← subgroupOf_map_subtype, hb, Subgroup.map_bot]
  · exfalso
    apply h.not_le_centralizer_A hE htype hK
    rw [← le_centralizer_iff]
    intro a ha
    have : (⟨a, ha⟩ : A) ∈ (centralizer (K : Set H)).subgroupOf A := by rw [ht]; exact mem_top _
    exact this

theorem factorProj_injOn {K : Subgroup H} (hK : IsComponentOf K ⊤)
    (hZ : K ⊓ centralizer (K : Set H) = ⊥) (hM : CFSG.layer H ≤ K ⊔ centralizer (K : Set H))
    (a b : CFSG.layer H) (ha : (a : H) ∈ A) (hb : (b : H) ∈ A)
    (hab : factorProj K _ hZ hM a = factorProj K _ hZ hM b) : a = b := by
  have h1 : factorProj K _ hZ hM (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
  rw [factorProj_eq_one_iff] at h1
  have h2 : ((a * b⁻¹ : CFSG.layer H) : H) ∈ A ⊓ centralizer (K : Set H) :=
    mem_inf.mpr ⟨by simpa using mul_mem ha (inv_mem hb), h1⟩
  rw [h.inf_centralizer_component_eq_bot hE htype hK, mem_bot] at h2
  exact mul_inv_eq_one.mp (Subtype.ext h2)

theorem t_not_mem_normalizer {K : Subgroup H} (hK : IsComponentOf K ⊤) (hAK : A ⊓ K = ⊥) :
    t ∉ normalizer (K : Set H) := by
  intro htN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := h.inf_centralizer_eq_bot_of_isComponentOf hE hK
  have hM := h.layer_le_sup_centralizer hE hK
  have hAL := h.A_le_layer hE
  have hAN : A ≤ normalizer (K : Set H) :=
    h.A_le_normalClosure.trans (normalClosure_le_normalizer hE hK)
  set p := factorProj K (CFSG.layer H) hZ hM with hpdef
  have hpA : ∀ a : CFSG.layer H, (a : H) ∈ A → p a ∈ centralizer (A : Set H) := by
    intro a ha
    have hat : (a : H) * t = t * a :=
      mem_centralizer_singleton_iff.mp (h.le_centralizer ha)
    have hmem : t⁻¹ * p a * t ∈ K := by
      simpa using (mem_normalizer_iff.mp (inv_mem htN) (p a)).mp (factorProj_mem a)
    have hc : (t⁻¹ * p a * t)⁻¹ * a ∈ centralizer (K : Set H) := by
      have h1 := conj_mem_centralizer (inv_mem htN) (factorProj_inv_mul_mem (hZ := hZ)
        (hM := hM) a)
      have h2 : (t⁻¹ * p a * t)⁻¹ * a = t⁻¹ * ((p a)⁻¹ * a) * t⁻¹⁻¹ := by
        rw [inv_inv]
        calc (t⁻¹ * p a * t)⁻¹ * (a : H) = t⁻¹ * (p a)⁻¹ * (t * a) := by group
          _ = t⁻¹ * (p a)⁻¹ * (a * t) := by rw [hat]
          _ = t⁻¹ * ((p a)⁻¹ * a) * t := by group
      rw [h2]
      exact h1
    have heq : p a = t⁻¹ * p a * t := factorProj_eq a hmem hc
    have hpt : p a ∈ centralizer ({t} : Set H) := by
      rw [mem_centralizer_singleton_iff]
      calc p a * t = t * (t⁻¹ * p a * t) := by group
        _ = t * p a := by rw [← heq]
    have hpN : p a ∈ normalizer (A : Set H) := h.centralizer_le_normalizer hpt
    refine mem_centralizer_iff.mpr fun b hb => ?_
    have hk : p a * b * (p a)⁻¹ * b⁻¹ ∈ A ⊓ K := by
      refine mem_inf.mpr ⟨mul_mem ((mem_normalizer_iff.mp hpN b).mp hb) (inv_mem hb), ?_⟩
      have h1 : b * (p a)⁻¹ * b⁻¹ ∈ K :=
        (mem_normalizer_iff.mp (hAN hb) _).mp (inv_mem (factorProj_mem a))
      have h2 : p a * b * (p a)⁻¹ * b⁻¹ = p a * (b * (p a)⁻¹ * b⁻¹) := by group
      rw [h2]
      exact mul_mem (factorProj_mem a) h1
    rw [hAK, mem_bot] at hk
    have h3 : p a * b * (p a)⁻¹ = b := mul_inv_eq_one.mp hk
    calc b * p a = p a * b * (p a)⁻¹ * p a := by rw [h3]
      _ = p a * b := by group
  have hUL : U ≤ CFSG.layer H := h.U_le.trans hAL
  have hU2 : IsPGroup 2 (U.subgroupOf (CFSG.layer H)) :=
    (@IsElementaryAbelian.isPGroup 2 U _ h.isElementaryAbelian_U).comap_subtype
  have hX2 := hU2.map p
  have hXC : (U.subgroupOf (CFSG.layer H)).map p ≤ centralizer (A : Set H) := by
    rintro _ ⟨u, hu, rfl⟩
    exact hpA u (h.U_le (mem_subgroupOf.mp hu))
  have hcard : Nat.card ((U.subgroupOf (CFSG.layer H)).map p) = 2 ^ n := by
    rw [card_map_of_injOn p _ fun a ha b hb hab => h.factorProj_injOn hE htype hK hZ hM a b
      (h.U_le (mem_subgroupOf.mp ha)) (h.U_le (mem_subgroupOf.mp hb)) hab]
    rw [← h.card_U]
    exact Nat.card_congr (subgroupOfEquivOfLe hUL).toEquiv
  have h4 := h.card_le_two hXC hX2
  rw [hcard] at h4
  have := h.four_le
  omega

theorem conj_ne {K : Subgroup H} (hK : IsComponentOf K ⊤) (hAK : A ⊓ K = ⊥) :
    K.map (MulAut.conj t⁻¹).toMonoidHom ≠ K := by
  intro heq
  apply h.t_not_mem_normalizer hE htype hK hAK
  have h1 : t⁻¹ ∈ normalizer (K : Set H) :=
    (CommutingComponentFamily.normalizer_iff_conjugate_eq K t⁻¹).mpr heq
  simpa using inv_mem h1

theorem factorProj_surjOn {K : Subgroup H} (hK : IsComponentOf K ⊤) (hAK : A ⊓ K = ⊥)
    (hZ : K ⊓ centralizer (K : Set H) = ⊥) (hM : CFSG.layer H ≤ K ⊔ centralizer (K : Set H))
    {y : H} (hy : y ∈ K) :
    ∃ a : CFSG.layer H, (a : H) ∈ A ∧ factorProj K _ hZ hM a = y := by
  have hne := h.conj_ne hE htype hK hAK
  have hAL := h.A_le_layer hE
  have := h.isSimpleGroup_of_isComponentOf hE hK
  set p := factorProj K (CFSG.layer H) hZ hM with hpdef
  have hd : ∀ y ∈ K, ∃ d : CFSG.layer H, (d : H) ∈ centralizer ({t} : Set H) ∧ p d = y := by
    intro y hy
    obtain ⟨hdL, hdt, -, hdC⟩ := h.diag_facts hK hne hy
    refine ⟨⟨_, hdL⟩, hdt, factorProj_eq _ hy ?_⟩
    change y⁻¹ * (y * (t⁻¹ * y * t)) ∈ _
    rw [inv_mul_cancel_left]
    exact hdC
  set PA : Subgroup H := (A.subgroupOf (CFSG.layer H)).map p with hPAdef
  have hPAK : PA ≤ K := by
    rintro _ ⟨a, -, rfl⟩
    exact factorProj_mem a
  have hn : (PA.subgroupOf K).Normal := by
    refine ⟨fun z hz g => mem_subgroupOf.mpr ?_⟩
    obtain ⟨a, ha, haz⟩ := mem_map.mp (mem_subgroupOf.mp hz)
    obtain ⟨d, hdt, hdg⟩ := hd g g.2
    have hdA : (d : H) * a * (d : H)⁻¹ ∈ A :=
      (mem_normalizer_iff.mp (h.centralizer_le_normalizer hdt) a).mp (mem_subgroupOf.mp ha)
    refine ⟨d * a * d⁻¹, mem_subgroupOf.mpr (by rw [coe_mul, coe_mul, coe_inv]; exact hdA), ?_⟩
    simp only [map_mul, map_inv, hdg, haz, coe_mul, coe_inv]
  rcases hn.eq_bot_or_eq_top with hb | ht
  · exfalso
    apply h.U_ne_bot
    rw [eq_bot_iff]
    intro u hu
    have hul : (⟨u, h.U_le.trans hAL hu⟩ : CFSG.layer H) = 1 := by
      refine h.factorProj_injOn hE htype hK hZ hM _ 1 (h.U_le hu) (one_mem A) ?_
      have h1 : (⟨p ⟨u, h.U_le.trans hAL hu⟩, factorProj_mem _⟩ : K) ∈ PA.subgroupOf K :=
        mem_subgroupOf.mpr (mem_map_of_mem p (mem_subgroupOf.mpr (h.U_le hu)))
      rw [hb, mem_bot] at h1
      rw [map_one]
      exact congrArg Subtype.val h1
    exact mem_bot.mpr (congrArg Subtype.val hul)
  · have h1 : (⟨y, hy⟩ : K) ∈ PA.subgroupOf K := by rw [ht]; exact mem_top _
    obtain ⟨a, ha, hay⟩ := mem_map.mp (mem_subgroupOf.mp h1)
    exact ⟨a, mem_subgroupOf.mp ha, hay⟩

theorem eq_or_eq_conj {K K' : Subgroup H} (hK : IsComponentOf K ⊤) (hAK : A ⊓ K = ⊥)
    (hK' : IsComponentOf K' ⊤) : K' = K ∨ K' = K.map (MulAut.conj t⁻¹).toMonoidHom := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  have hne := h.conj_ne hE htype hK hAK
  have hKt := isComponentOf_conj hK t⁻¹
  have hZ := h.inf_centralizer_eq_bot_of_isComponentOf hE hK
  have hM := h.layer_le_sup_centralizer hE hK
  have hZ' := h.inf_centralizer_eq_bot_of_isComponentOf hE hK'
  have hM' := h.layer_le_sup_centralizer hE hK'
  have hAL := h.A_le_layer hE
  set p := factorProj K (CFSG.layer H) hZ hM with hpdef
  set p' := factorProj K' (CFSG.layer H) hZ' hM' with hp'def
  have hKK' : K ≤ centralizer (K' : Set H) :=
    commutator_eq_bot_iff_le_centralizer.mp (LocalComponents.commute_of_ne K K' hK hK'
      (Ne.symm hne1))
  have hKtK' : K.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer (K' : Set H) :=
    commutator_eq_bot_iff_le_centralizer.mp (LocalComponents.commute_of_ne _ K' hKt hK'
      (Ne.symm hne2))
  have hyC : ∀ y ∈ K, y ∈ centralizer (K : Set H) := by
    intro y hy
    obtain ⟨hdL, hdt, hyt, hdC⟩ := h.diag_facts hK hne hy
    set d : CFSG.layer H := ⟨_, hdL⟩ with hd
    have hdK' : (d : H) ∈ centralizer (K' : Set H) := mul_mem (hKK' hy) (hKtK' hyt)
    have hp'd : p' d = 1 := (factorProj_eq_one_iff d).mpr hdK'
    have hpd : p d = y := factorProj_eq d hy (by
      change y⁻¹ * (y * (t⁻¹ * y * t)) ∈ _
      rw [inv_mul_cancel_left]
      exact hdC)
    have hdA : ∀ a : CFSG.layer H, (a : H) ∈ A → d * a * d⁻¹ = a := by
      intro a ha
      have hdaA : ((d * a * d⁻¹ : CFSG.layer H) : H) ∈ A := by
        rw [coe_mul, coe_mul, coe_inv]
        exact (mem_normalizer_iff.mp (h.centralizer_le_normalizer hdt) a).mp ha
      refine h.factorProj_injOn hE htype hK' hZ' hM' _ _ hdaA ha ?_
      rw [map_mul, map_mul, map_inv, hp'd, one_mul, inv_one, mul_one]
    refine mem_centralizer_iff.mpr fun z hz => ?_
    obtain ⟨a, ha, haz⟩ := h.factorProj_surjOn hE htype hK hAK hZ hM hz
    have h1 := congrArg p (hdA a ha)
    rw [map_mul, map_mul, map_inv, hpd, haz] at h1
    calc z * y = y * z * y⁻¹ * y := by rw [h1]
      _ = y * z := by group
  have hKbot : K = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : y ∈ K ⊓ centralizer (K : Set H) := mem_inf.mpr ⟨hy, hyC y hy⟩
    rwa [hZ] at this
  have := Quasisimple.nontrivial hK.2.2
  exact (K.nontrivial_iff_ne_bot.mp this) hKbot

theorem layer_eq_sup_conj {K : Subgroup H} (hK : IsComponentOf K ⊤) (hAK : A ⊓ K = ⊥) :
    CFSG.layer H = K ⊔ K.map (MulAut.conj t⁻¹).toMonoidHom := by
  apply le_antisymm
  · rw [layer_eq_sSup]
    refine sSup_le fun K' hK' => ?_
    rcases h.eq_or_eq_conj hE htype hK hAK hK' with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (le_layer_of_isComponentOf hK)
      (le_layer_of_isComponentOf (isComponentOf_conj hK t⁻¹))

theorem alternative_one (hII : ∀ K : Subgroup H, IsComponentOf K ⊤ → ¬ A ≤ K) :
    ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ n ∧
      ∃ (ψ : CFSG.layer H ≃* SL(2, k) × SL(2, k)) (α : A ≃* SL(2, k)),
        (∀ (a : A) (x : CFSG.layer H), (x : H) = a → ψ x = (α a, α a)) ∧
        ∀ (x y : CFSG.layer H) (y₁ y₂ : SL(2, k)), (y : H) = t⁻¹ * x * t →
          ψ x = (y₁, y₂) → ψ y = (y₂, y₁) := by
  obtain ⟨K, hK⟩ : ∃ K : Subgroup H, IsComponentOf K ⊤ := by
    by_contra hno
    push Not at hno
    apply h.U_ne_bot
    have hL : CFSG.layer H = ⊥ := by
      rw [layer_eq_sSup, sSup_eq_bot]
      intro K hK
      exact absurd hK (hno K)
    rw [eq_bot_iff, ← hL]
    exact h.U_le.trans (h.A_le_layer hE)
  have hAK : A ⊓ K = ⊥ := h.inf_eq_bot_of_not_le hE hK (hII K hK)
  have hKt := isComponentOf_conj hK t⁻¹
  have hne := h.conj_ne hE htype hK hAK
  have hKtC : K.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer (K : Set H) :=
    commutator_eq_bot_iff_le_centralizer.mp (LocalComponents.commute_of_ne _ K hKt hK hne)
  have hZ := h.inf_centralizer_eq_bot_of_isComponentOf hE hK
  have hM := h.layer_le_sup_centralizer hE hK
  have hAL := h.A_le_layer hE
  have hLsup := h.layer_eq_sup_conj hE htype hK hAK
  have hLC : centralizer (CFSG.layer H : Set H) = ⊥ := by
    rw [h.layer_eq_normalClosure hE]
    exact h.centralizer_normalClosure_eq_bot
  have htinv : t⁻¹ = t := h.t_inv
  have htt : t * t = 1 := h.t_mul_t
  have htt' : t⁻¹ * t⁻¹ = 1 := by rw [htinv, htt]
  have hconjmem : ∀ y ∈ K, t⁻¹ * y * t ∈ K.map (MulAut.conj t⁻¹).toMonoidHom :=
    fun y hy => ⟨y, hy, by simp⟩
  set p := factorProj K (CFSG.layer H) hZ hM with hpdef
  let τ : CFSG.layer H →* CFSG.layer H :=
    (MulAut.conjNormal t⁻¹ : MulAut (CFSG.layer H)).toMonoidHom
  have hτ : ∀ x : CFSG.layer H, (τ x : H) = t⁻¹ * x * t := by
    intro x
    change ((MulAut.conjNormal t⁻¹) x : H) = _
    rw [MulAut.conjNormal_apply, inv_inv]
  have hττ : ∀ x : CFSG.layer H, τ (τ x) = x := by
    intro x
    apply Subtype.ext
    rw [hτ, hτ]
    calc t⁻¹ * (t⁻¹ * (x : H) * t) * t = (t⁻¹ * t⁻¹) * x * (t * t) := by group
      _ = x := by rw [htt', htt, one_mul, mul_one]
  let φ₁ : CFSG.layer H →* K := p.codRestrict K factorProj_mem
  have hφ₁ : ∀ x, (φ₁ x : H) = p x := fun x => rfl
  let Φ : CFSG.layer H →* K × K := φ₁.prod (φ₁.comp τ)
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : p x = 1 := congrArg Subtype.val (congrArg Prod.fst hx)
    have h2 : p (τ x) = 1 := congrArg Subtype.val (congrArg Prod.snd hx)
    rw [factorProj_eq_one_iff] at h1 h2
    rw [hτ] at h2
    have hle : CFSG.layer H ≤ centralizer ({(x : H)} : Set H) := by
      refine hLsup.le.trans (sup_le (fun y hy => mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp h1) y hy)) ?_)
      rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have h3 : y * (t⁻¹ * x * t) = (t⁻¹ * x * t) * y := (mem_centralizer_iff.mp h2) y hy
      change t⁻¹ * y * t⁻¹⁻¹ * x = x * (t⁻¹ * y * t⁻¹⁻¹)
      have h4 : t * y * t⁻¹ * (x : H) = x * (t * y * t⁻¹) := by
        calc t * y * t⁻¹ * (x : H) = t * (y * (t⁻¹ * x * t)) * t⁻¹ := by group
          _ = t * ((t⁻¹ * x * t) * y) * t⁻¹ := by rw [h3]
          _ = x * (t * y * t⁻¹) := by group
      rw [inv_inv, htinv]
      rw [htinv] at h4
      exact h4
    have hxC : (x : H) ∈ centralizer (CFSG.layer H : Set H) :=
      mem_centralizer_iff.mpr fun y hy => mem_centralizer_singleton_iff.mp (hle hy)
    rw [hLC, mem_bot] at hxC
    exact Subtype.ext hxC
  have hsurj : Function.Surjective Φ := by
    rintro ⟨y, z⟩
    have hzt := hconjmem z z.2
    have hyt := hconjmem y y.2
    have hxL : (y : H) * (t⁻¹ * z * t) ∈ CFSG.layer H :=
      mul_mem (le_layer_of_isComponentOf hK y.2) (le_layer_of_isComponentOf hKt hzt)
    refine ⟨⟨_, hxL⟩, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
    · change p ⟨_, hxL⟩ = y
      refine factorProj_eq _ y.2 ?_
      change (y : H)⁻¹ * (y * (t⁻¹ * z * t)) ∈ _
      rw [inv_mul_cancel_left]
      exact hKtC hzt
    · change p (τ ⟨_, hxL⟩) = z
      refine factorProj_eq _ z.2 ?_
      rw [hτ]
      have hcomm : (z : H) * (t⁻¹ * y * t) = (t⁻¹ * y * t) * z :=
        (mem_centralizer_iff.mp (hKtC hyt)) z z.2
      have h4 : (z : H)⁻¹ * (t⁻¹ * ((y : H) * (t⁻¹ * z * t)) * t) = t⁻¹ * y * t := by
        calc (z : H)⁻¹ * (t⁻¹ * ((y : H) * (t⁻¹ * z * t)) * t) =
              (z : H)⁻¹ * ((t⁻¹ * y * t) * ((t⁻¹ * t⁻¹) * z * (t * t))) := by group
          _ = (z : H)⁻¹ * ((t⁻¹ * y * t) * z) := by rw [htt', htt, one_mul, mul_one]
          _ = (z : H)⁻¹ * (z * (t⁻¹ * y * t)) := by rw [hcomm]
          _ = t⁻¹ * y * t := by group
      rw [h4]
      exact hKtC hyt
  let ΦE : CFSG.layer H ≃* K × K := MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  let β₀ : A →* K := φ₁.comp (inclusion hAL)
  have hβinj : Function.Injective β₀ := by
    intro a b hab
    have h1 := h.factorProj_injOn hE htype hK hZ hM (inclusion hAL a) (inclusion hAL b) a.2 b.2
      (congrArg Subtype.val hab)
    exact inclusion_injective hAL h1
  have hβsurj : Function.Surjective β₀ := by
    intro y
    obtain ⟨a, ha, hay⟩ := h.factorProj_surjOn hE htype hK hAK hZ hM y.2
    exact ⟨⟨a, ha⟩, Subtype.ext hay⟩
  let β : A ≃* K := MulEquiv.ofBijective β₀ ⟨hβinj, hβsurj⟩
  obtain ⟨k, hkF, hkFin, hk, ⟨αA⟩⟩ := h.app.2.2.1.2.2
  let γ : K ≃* SL(2, k) := β.symm.trans αA
  have hγ : ∀ a : A, γ (β₀ a) = αA a := by
    intro a
    change αA (β.symm (β a)) = αA a
    rw [MulEquiv.symm_apply_apply]
  have hψ : ∀ x : CFSG.layer H,
      (ΦE.trans (MulEquiv.prodCongr γ γ)) x = (γ (φ₁ x), γ (φ₁ (τ x))) := fun x => rfl
  refine ⟨k, hkF, hkFin, hk, ΦE.trans (MulEquiv.prodCongr γ γ), αA, ?_, ?_⟩
  · intro a x hxa
    have hx : x = inclusion hAL a := Subtype.ext hxa
    have hat : (a : H) * t = t * a := mem_centralizer_singleton_iff.mp (h.le_centralizer a.2)
    have hτx : τ x = x := by
      apply Subtype.ext
      rw [hτ, hxa]
      calc t⁻¹ * (a : H) * t = t⁻¹ * (t * a) := by rw [mul_assoc, hat]
        _ = a := by group
    rw [hψ, hτx, hx]
    exact Prod.ext (hγ a) (hγ a)
  · intro x y y₁ y₂ hyx hψx
    have hy : y = τ x := Subtype.ext (by rw [hτ]; exact hyx)
    rw [hψ] at hψx
    rw [hψ, hy, hττ]
    obtain ⟨h1, h2⟩ := Prod.mk.inj hψx
    rw [h1, h2]

theorem layer_dichotomy :
    (∃ K : Subgroup H, IsComponentOf K ⊤ ∧ CFSG.layer H = K) ∨
    (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ n ∧
      ∃ (ψ : CFSG.layer H ≃* SL(2, k) × SL(2, k)) (α : A ≃* SL(2, k)),
        (∀ (a : A) (x : CFSG.layer H), (x : H) = a → ψ x = (α a, α a)) ∧
        ∀ (x y : CFSG.layer H) (y₁ y₂ : SL(2, k)), (y : H) = t⁻¹ * x * t →
          ψ x = (y₁, y₂) → ψ y = (y₂, y₁)) := by
  by_cases hI : ∃ K : Subgroup H, IsComponentOf K ⊤ ∧ A ≤ K
  · left
    obtain ⟨K, hK, hAK⟩ := hI
    refine ⟨K, hK, le_antisymm ?_ (le_layer_of_isComponentOf hK)⟩
    rw [layer_eq_sSup]
    refine sSup_le fun K' hK' => ?_
    by_cases hKK : K' = K
    · rw [hKK]
    · exact absurd ((commutator_eq_bot_iff_le_centralizer.mp
        (LocalComponents.commute_of_ne K' K hK' hK hKK)).trans (centralizer_le hAK))
        (h.not_le_centralizer_A hE htype hK')
  · right
    push Not at hI
    exact h.alternative_one hE htype hI

end Layer

end LocalSetting

end CFSG.LocalAnalysis.EvenBN.GMS
