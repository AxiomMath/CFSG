module

public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3VMain
public import CFSG.HardMathSupport.Solomon.Proving.LBLayerConj
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bar
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Split

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem on25_normal_le_center_or_top {K : Type*} [Group K] (hq : CFSG.Open.IsQuasisimple K)
    (M : Subgroup K) [M.Normal] : M ≤ Subgroup.center K ∨ M = ⊤ := by
  obtain ⟨hperf, hs⟩ := hq
  have hnorm : (M.map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    Subgroup.Normal.map ‹M.Normal› (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have := hnorm
  rcases hs.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (Subgroup.center K))) with h | h
  · left
    intro m hm
    have h1 : QuotientGroup.mk' (Subgroup.center K) m ∈
        M.map (QuotientGroup.mk' (Subgroup.center K)) := Subgroup.mem_map_of_mem _ hm
    rw [h, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff m).mp h1
  · right
    have hsup : M ⊔ Subgroup.center K = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center K)) M
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hle : commutator K ≤ M :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hperf] at hle
    exact top_le_iff.mp hle

theorem on25_primeCore_eq_bot {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hZ : IsPGroup 3 (Subgroup.center K)) (h3 : 3 ∣ Nat.card K) : GLAPPrimeCore 3 K = ⊥ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  refine le_bot_iff.1 (sSup_le fun N hN => ?_)
  obtain ⟨hNn, hcop⟩ := hN
  haveI := hNn
  rcases on25_normal_le_center_or_top hq N with hle | htop
  · obtain ⟨k, hk⟩ := hZ.exists_card_eq
    have hd : Nat.card N ∣ 3 ^ k := hk ▸ Subgroup.card_dvd_of_le hle
    have h1 : Nat.card N = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop.symm) hd
    exact (Subgroup.eq_bot_of_card_eq N h1).le
  · exfalso
    rw [htop, Subgroup.card_top] at hcop
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop h3)

theorem on25_glaPComponent_self {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hZ : IsPGroup 3 (Subgroup.center ↥K))
    (h3 : 3 ∣ Nat.card K) : GLAPComponent 3 K K := by
  have hO := on25_primeCore_eq_bot hq hZ h3
  have hc : IsComponentOf (⊤ : Subgroup ↥K) ⊤ :=
    ⟨le_top, IsSubnormal.refl _,
      CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
        Subgroup.topEquiv.symm hq⟩
  have h1 := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112b_glaPComponent_of_isComponentOf hO hc
  have h2 := glaPComponent_map Nat.prime_three K.subtype (by
    rw [K.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right _) h1
  rwa [Subgroup.map_top, Subgroup.range_subtype] at h2

theorem on25_le_layer {G : Type} [Group G] [Finite G] {C N K : Subgroup G}
    (hKN : K ≤ N) (hNC : N ≤ C) (hKn : (K.subgroupOf N).Normal) (hNn : (N.subgroupOf C).Normal)
    (hq : CFSG.Open.IsQuasisimple ↥K) (hZ : IsPGroup 3 (Subgroup.center ↥K))
    (h3 : 3 ∣ Nat.card K) : K ≤ GLAPLayer 3 C := by
  have h1 := on25_glaPComponent_self hq hZ h3
  have h2 := Proving.glaPComponent_of_normal_overgroup Nat.prime_three hKN hKn h1
  have h3' := Proving.glaPComponent_of_normal_overgroup Nat.prime_three hNC hNn h2
  exact le_sSup h3'

theorem on25_map_centralizer_normal {G₁ G₂ : Type*} [Group G₁] [Group G₂] (q : G₁ →* G₂)
    (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center G₁) (a : G₁) :
    (((Subgroup.centralizer ({a} : Set G₁)).map q).subgroupOf
      (Subgroup.centralizer ({q a} : Set G₂))).Normal := by
  have hle : (Subgroup.centralizer ({a} : Set G₁)).map q ≤
      Subgroup.centralizer ({q a} : Set G₂) := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c ∈ Subgroup.centralizer ({a} : Set G₁) := hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc' ⊢
    rw [← map_mul, ← map_mul, hc']
  rw [Subgroup.normal_subgroupOf_iff hle]
  rintro _ k ⟨c, hc, rfl⟩ hk
  obtain ⟨g, rfl⟩ := hq k
  refine ⟨g * c * g⁻¹, ?_, by simp⟩
  have hk' := Subgroup.mem_centralizer_singleton_iff.1 hk
  have hw : g⁻¹ * a * g * a⁻¹ ∈ Subgroup.center G₁ := by
    apply hker
    rw [MonoidHom.mem_ker]
    have h1 : (q g)⁻¹ * q a * q g = q a := by
      calc (q g)⁻¹ * q a * q g = (q g)⁻¹ * (q a * q g) := by group
        _ = (q g)⁻¹ * (q g * q a) := by rw [← hk']
        _ = q a := by group
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1, mul_inv_cancel]
  have hc' := Subgroup.mem_centralizer_singleton_iff.1 (show c ∈ Subgroup.centralizer
    ({a} : Set G₁) from hc)
  show g * c * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G₁)
  rw [Subgroup.mem_centralizer_singleton_iff]
  set w := g⁻¹ * a * g * a⁻¹ with hwdef
  have e : g⁻¹ * a * g = w * a := by rw [hwdef]; group
  have hcw : c * (g⁻¹ * a * g) = (g⁻¹ * a * g) * c := by
    rw [e]
    calc c * (w * a) = (c * w) * a := by group
      _ = (w * c) * a := by rw [Subgroup.mem_center_iff.1 hw c]
      _ = w * (c * a) := by group
      _ = w * (a * c) := by rw [hc']
      _ = (w * a) * c := by group
  calc (g * c * g⁻¹) * a = g * (c * (g⁻¹ * a * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * a * g) * c) * g⁻¹ := by rw [hcw]
    _ = a * (g * c * g⁻¹) := by group

theorem on25_layer_image {G₁ G₂ : Type} [Group G₁] [Group G₂] [Finite G₂] (q : G₁ →* G₂)
    (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center G₁) {a : G₁} {K : Subgroup G₁}
    (hC : Subgroup.centralizer ({a} : Set G₁) = Subgroup.zpowers a ⊔ K)
    (hqs : CFSG.Open.IsQuasisimple ↥(K.map q)) (hZ : IsPGroup 3 (Subgroup.center ↥(K.map q)))
    (h3 : 3 ∣ Nat.card (K.map q)) : K.map q ≤ GLAPLayer 3 (Subgroup.centralizer ({q a} : Set G₂)) := by
  have hKC : K ≤ Subgroup.centralizer ({a} : Set G₁) := by rw [hC]; exact le_sup_right
  have hKa : ∀ k ∈ K, a * k = k * a := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hKC hk)).symm
  have hKnorm : ∀ c ∈ Subgroup.centralizer ({a} : Set G₁), ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
    intro c hc k hk
    rw [hC] at hc
    obtain ⟨x, hx, y, hy, rfl⟩ := i224_mem_sup_of_comm (P := Subgroup.zpowers a) (Q := K)
      (fun x hx y hy => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        exact (Commute.zpow_left (show Commute a y from hKa y hy) m).eq) hc
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hcx : ∀ z ∈ K, a ^ m * z = z * a ^ m := fun z hz =>
      (Commute.zpow_left (show Commute a z from hKa z hz) m).eq
    have hyk : y * k * y⁻¹ ∈ K := K.mul_mem (K.mul_mem hy hk) (K.inv_mem hy)
    have e : a ^ m * y * k * (a ^ m * y)⁻¹ = y * k * y⁻¹ := by
      calc a ^ m * y * k * (a ^ m * y)⁻¹ = a ^ m * (y * k * y⁻¹) * (a ^ m)⁻¹ := by group
        _ = y * k * y⁻¹ := by rw [hcx _ hyk]; group
    rw [e]
    exact hyk
  have hKN : K.map q ≤ (Subgroup.centralizer ({a} : Set G₁)).map q := Subgroup.map_mono hKC
  have hNC : (Subgroup.centralizer ({a} : Set G₁)).map q ≤
      Subgroup.centralizer ({q a} : Set G₂) := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c ∈ Subgroup.centralizer ({a} : Set G₁) := hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc' ⊢
    rw [← map_mul, ← map_mul, hc']
  have hKn : ((K.map q).subgroupOf ((Subgroup.centralizer ({a} : Set G₁)).map q)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKN]
    rintro _ _ ⟨k, hk, rfl⟩ ⟨c, hc, rfl⟩
    refine ⟨c * k * c⁻¹, hKnorm c hc k hk, ?_⟩
    simp
  exact on25_le_layer hKN hNC hKn (on25_map_centralizer_normal q hq hker a) hqs hZ h3

theorem on25_normalizer_layer {G : Type} [Group G] [Finite G] (p : ℕ) {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (GLAPLayer p X : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hg ⊢
  calc GLBConj g (GLAPLayer p X) = GLAPLayer p (GLBConj g X) :=
        (i183v_glaPLayer_gLBConj p g X).symm
    _ = GLAPLayer p X := by rw [hg]

theorem on25_normalizer_centralizer {G : Type*} [Group G] {g b : G}
    (hw : g * b * g⁻¹ * b⁻¹ ∈ Subgroup.center G) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  show y ∈ Subgroup.centralizer ({b} : Set G) ↔ g * y * g⁻¹ ∈ Subgroup.centralizer ({b} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  set w := g * b * g⁻¹ * b⁻¹ with hwdef
  have hwc : ∀ x : G, x * w = w * x := fun x => (Subgroup.mem_center_iff.1 hw x)
  have hwc' : ∀ x : G, x * w⁻¹ = w⁻¹ * x := fun x =>
    (Subgroup.mem_center_iff.1 ((Subgroup.center G).inv_mem hw) x)
  have h1 : g * b * g⁻¹ = w * b := by rw [hwdef]; group
  have h2 : g⁻¹ * b * g = w⁻¹ * b := by
    calc g⁻¹ * b * g = g⁻¹ * w⁻¹ * (w * b) * g := by group
      _ = g⁻¹ * w⁻¹ * (g * b * g⁻¹) * g := by rw [h1]
      _ = (g⁻¹ * w⁻¹ * g) * b := by group
      _ = w⁻¹ * b := by
          have : g⁻¹ * w⁻¹ * g = w⁻¹ := by
            rw [hwc' g⁻¹, mul_assoc, inv_mul_cancel, mul_one]
          rw [this]
  have h3 : (g * y * g⁻¹) * b = g * (y * (w⁻¹ * b)) * g⁻¹ := by
    calc (g * y * g⁻¹) * b = g * y * (g⁻¹ * b * g) * g⁻¹ := by group
      _ = _ := by rw [h2]; group
  have h4 : b * (g * y * g⁻¹) = g * ((w⁻¹ * b) * y) * g⁻¹ := by
    calc b * (g * y * g⁻¹) = g * (g⁻¹ * b * g) * y * g⁻¹ := by group
      _ = _ := by rw [h2]; group
  have key : (g * y * g⁻¹) * b = b * (g * y * g⁻¹) ↔ y * b = b * y := by
    rw [h3, h4]
    have e1 : y * (w⁻¹ * b) = w⁻¹ * (y * b) := by rw [← mul_assoc, hwc' y, mul_assoc]
    rw [e1, mul_left_inj, mul_right_inj, mul_assoc w⁻¹ b y, mul_right_inj]
  exact key.symm

end CFSG.HardMathSupport.Solomon.Coordinator
