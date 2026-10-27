module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFusionC2Basic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotClasses
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionC

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms (congr_conj)

section Transport

variable {L C : Type*} [Group L] [Group C]

theorem complement_of_mulEquiv (e : L ≃* C)
    (h : ∀ T : Subgroup (MulAut C), IsPGroup 2 T → ∃ φ : MulAut C,
      (∀ y ∈ zpowers φ, y ∈ (MulAut.conj : C →* MulAut C).range → y = 1) ∧
      ∀ a ∈ T, ∃ c : C, ∃ y ∈ zpowers φ, a = MulAut.conj c * y)
    (T : Subgroup (MulAut L)) (hT : IsPGroup 2 T) :
    ∃ φ : MulAut L, (∀ y ∈ zpowers φ, y ∈ (MulAut.conj : L →* MulAut L).range → y = 1) ∧
      ∀ a ∈ T, ∃ c : L, ∃ y ∈ zpowers φ, a = MulAut.conj c * y := by
  set κ := MulAut.congr e with hκ
  obtain ⟨φ, hφI, hTφ⟩ := h (T.map κ.toMonoidHom) (hT.map _)
  refine ⟨κ.symm φ, fun y hy hyI => ?_, fun a ha => ?_⟩
  · have h1 : κ y ∈ zpowers φ := by
      obtain ⟨z, rfl⟩ := mem_zpowers_iff.1 hy
      rw [map_zpow, MulEquiv.apply_symm_apply]
      exact zpow_mem (mem_zpowers φ) z
    have h2 : κ y ∈ (MulAut.conj : C →* MulAut C).range := by
      obtain ⟨l, rfl⟩ := hyI
      exact ⟨e l, (congr_conj e l).symm⟩
    exact κ.injective ((hφI _ h1 h2).trans (map_one κ).symm)
  · obtain ⟨c, y, hy, hcy⟩ := hTφ (κ a) ⟨a, ha, rfl⟩
    refine ⟨e.symm c, κ.symm y, ?_, ?_⟩
    · obtain ⟨z, rfl⟩ := mem_zpowers_iff.1 hy
      rw [map_zpow]
      exact zpow_mem (mem_zpowers _) z
    · apply κ.injective
      rw [map_mul, MulEquiv.apply_symm_apply, hκ, congr_conj, MulEquiv.apply_symm_apply, ← hκ,
        ← hcy]

end Transport

section Rep

theorem exists_conj_eq_mul_rep_of_twoCentral {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {C : Type*} [Group C] (e : L ≃* C) {t : G}
    (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G)) {r : C}
    (hr : ∀ x : C, orderOf x = 2 → (∃ S : Sylow 2 C, ∀ s ∈ (S : Subgroup C), s * x = x * s) →
      IsConj x r)
    {g z : G} (hzL : z ∈ L) (hgz : g⁻¹ * t * g = t * z) (hz1 : z ≠ 1)
    (hzU : ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u) :
    ∃ h : G, h⁻¹ * t * h = t * (e.symm r : G) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hzt : z * t = t * z := mem_centralizer_iff.1 htC z hzL
  have hz2 : z * z = 1 := by
    have hs : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
      calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [htt, mul_one, inv_mul_cancel]
    rw [hgz] at hs
    calc z * z = t * t * (z * z) := by rw [htt, one_mul]
      _ = t * (t * z) * z := by group
      _ = t * (z * t) * z := by rw [hzt]
      _ = t * z * (t * z) := by group
      _ = 1 := hs
  have hzo : orderOf (e ⟨z, hzL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, orderOf_mk]
    exact orderOf_eq_prime (by rw [sq, hz2]) hz1
  obtain ⟨U, hU⟩ := hzU
  have hS : ∃ S : Sylow 2 C, ∀ s ∈ (S : Subgroup C), s * e ⟨z, hzL⟩ = e ⟨z, hzL⟩ * s := by
    refine ⟨Sylow.mapSurjective (f := e.toMonoidHom) e.surjective U, fun s hs => ?_⟩
    obtain ⟨u, hu, rfl⟩ := hs
    have h1 := hU u hu
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext h1)
  obtain ⟨c, hc⟩ := isConj_iff.1 (hr _ hzo hS)
  set l : L := e.symm c with hl
  have hlt : (l : G) * t = t * l := mem_centralizer_iff.1 htC l l.2
  have hlz : (l : G) * z * (l : G)⁻¹ = e.symm r := by
    have h1 : l * ⟨z, hzL⟩ * l⁻¹ = e.symm r := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, hl, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hc]
    exact congrArg Subtype.val h1
  refine ⟨g * (l : G)⁻¹, ?_⟩
  calc (g * (l : G)⁻¹)⁻¹ * t * (g * (l : G)⁻¹) = l * (g⁻¹ * t * g) * (l : G)⁻¹ := by group
    _ = l * t * z * (l : G)⁻¹ := by rw [hgz, mul_assoc (l : G) t z]
    _ = t * ((l : G) * z * (l : G)⁻¹) := by rw [hlt]; group
    _ = t * (e.symm r : G) := by rw [hlz]

end Rep

section Complement

theorem complement_twistedE6 {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (T : Subgroup (MulAut (graphFixedRootGroup TwistTag.E6 K σ))) (hT : IsPGroup 2 T) :
    ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
      (∀ y ∈ zpowers φ, y ∈ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ →*
        MulAut (graphFixedRootGroup TwistTag.E6 K σ)).range → y = 1) ∧
      ∀ a ∈ T, ∃ c : graphFixedRootGroup TwistTag.E6 K σ, ∃ y ∈ zpowers φ,
        a = MulAut.conj c * y := by
  have := finite_of_card hK
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  obtain ⟨-, -, -, -, -, -, -, hNF, ⟨Θ, hΘ, -, hΘker, -, hexp, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σE hσ
  obtain ⟨σ₂, -, hord, hz, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
    Nat.prime_two (by omega : 1 ≤ 2 * f) (show Nat.card K = 2 ^ (2 * f) by
      rw [hK, ← pow_mul, mul_comm])
  have hfin : IsOfFinOrder σ₂ := orderOf_pos_iff.1 (by rw [hord]; omega)
  set φ := fieldActor σE σ₂ with hφdef
  have hΘconj : ∀ g u, Θ (MulAut.conj g * compatDiagAutHom TwistTag.E6 K σE.toRingHom u) = 1 :=
    fun g u => hΘ _ g u 1 (by rw [fieldActor_one, mul_one])
  have hIΘ : (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σE.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)).range ≤ Θ.ker := by
    rintro _ ⟨g, rfl⟩
    rw [MonoidHom.mem_ker]
    have h := hΘconj g 1
    rwa [map_one, mul_one] at h
  have hodd : ∀ a ∈ Θ.ker, ∃ m : ℕ, Odd m ∧ a ^ m ∈ (MulAut.conj :
      graphFixedRootGroup TwistTag.E6 K σE.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)).range := by
    intro a ha
    rw [hΘker] at ha
    refine ⟨3, by decide, ?_⟩
    have h1 := hexp (QuotientGroup.mk ⟨a, ha⟩)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    exact h1
  have hφpow : ∀ n : ℕ, φ ^ n = fieldActor σE (σ₂ ^ n) := fun n =>
    (map_pow (fieldActorHom (t := TwistTag.E6) σE) σ₂ n).symm
  have hgen : ∀ a, ∃ κ ∈ Θ.ker, ∃ k : ℕ, a = κ * φ ^ k := by
    intro a
    obtain ⟨g, u, δ, rfl⟩ := hNF a
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1
      (hfin.mem_powers_iff_mem_zpowers.2 (by rw [hz]; exact mem_top δ))
    exact ⟨MulAut.conj g * compatDiagAutHom TwistTag.E6 K σE.toRingHom u, hΘconj g u, k,
      by rw [hφpow, hk]⟩
  have hφ : ∀ n : ℕ, Θ (φ ^ n) = 1 → φ ^ n = 1 := by
    intro n hn
    have h1 : Θ (φ ^ n) = σ₂ ^ n :=
      hΘ _ 1 1 (σ₂ ^ n) (by rw [map_one, map_one, one_mul, one_mul, hφpow])
    rw [h1] at hn
    rw [hφpow, hn, fieldActor_one]
  have : (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σE.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)).range.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  obtain ⟨φ', hφ'I, hTφ'⟩ := exists_conj_complement_of_isPGroup Θ hIΘ hodd hgen hφ hT
  refine ⟨φ', hφ'I, fun a ha => ?_⟩
  obtain ⟨c, ⟨g, rfl⟩, y, hy, rfl⟩ := hTφ' a ha
  exact ⟨g, y, hy, rfl⟩

end Complement

section C2

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_eq_mul_twoCentral_of_forall_inner_twistedE6 (hset : StandardSetting G L)
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ g : G, g⁻¹ * t * g ∉ L)
    (hinner : ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g ∈ L ⊔ zpowers t) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht
  obtain ⟨M₀, hLM, htM, hM, hodd, x₀, hx₀, hgen, hlift⟩ :=
    exists_odd_relIndex_gen_of_mulAut hCN hLt hKt
      (complement_of_mulEquiv e (complement_twistedE6 hf hK σ hσ))
  have : IsSimpleGroup G := hset.simple
  exact exists_conj_eq_mul_of_forall_inner_of_odd_relIndex
    (F4Pilot.two_lt_card_of_exists_mul_ne hset.nonab) ht hLM htM hM hodd hCN hnot hinner hx₀
    hgen hlift

theorem exists_conj_eq_mul_repXC_zero_of_forall_inner_twistedE6 (hset : StandardSetting G L)
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ g : G, g⁻¹ * t * g ∉ L)
    (hinner : ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g ∈ L ⊔ zpowers t) :
    ∃ h : G, h⁻¹ * t * h = t * (e.symm (repXC (apply_apply_eq hK hσ) 0) : G) := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  obtain ⟨g, z, hzL, hgz, hz1, hzU⟩ :=
    exists_conj_eq_mul_twoCentral_of_forall_inner_twistedE6 hset hf hK σ hσ e ht hKt hnot hinner
  exact exists_conj_eq_mul_rep_of_twoCentral e ht htK.1
    (fun x hx hS => (isConj_repXC_zero_iff_twoCentral hf hK hσ hx).2 hS) hzL hgz hz1 hzU

end C2

end CFSG.SeitzReduction.TwistedE6Pilot
