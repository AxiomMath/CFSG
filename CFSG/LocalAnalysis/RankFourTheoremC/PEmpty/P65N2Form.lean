module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2Omega
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2Sec
public import CFSG.RankThree.PartOne.LIT.RankAbstract

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2

open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

section ClassTwo

variable {Ω : Subgroup K}

theorem commutator_mem_of_mem {x y : K} (hx : x ∈ Ω) (hy : y ∈ Ω) : ⁅x, y⁆ ∈ Ω := by
  rw [commutatorElement_def]
  exact Ω.mul_mem (Ω.mul_mem (Ω.mul_mem hx hy) (Ω.inv_mem hx)) (Ω.inv_mem hy)

theorem comm_mul_left (hc : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ w ∈ Ω, w * ⁅x, y⁆ = ⁅x, y⁆ * w)
    {x x' y : K} (hx : x ∈ Ω) (hx' : x' ∈ Ω) (hy : y ∈ Ω) :
    ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆ := by
  have h1 : x * ⁅x', y⁆ * x⁻¹ = ⁅x', y⁆ := by rw [hc x' hx' y hy x hx]; group
  have h2 : ⁅x * x', y⁆ = (x * ⁅x', y⁆ * x⁻¹) * ⁅x, y⁆ := by
    simp only [commutatorElement_def]; group
  have h3 : ⁅x', y⁆ * ⁅x, y⁆ = ⁅x, y⁆ * ⁅x', y⁆ :=
    hc x hx y hy ⁅x', y⁆ (commutator_mem_of_mem hx' hy)
  rw [h2, h1, h3]

theorem comm_mul_right (hc : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ w ∈ Ω, w * ⁅x, y⁆ = ⁅x, y⁆ * w)
    {x y y' : K} (hx : x ∈ Ω) (hy : y ∈ Ω) (hy' : y' ∈ Ω) :
    ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  have h1 : y * ⁅x, y'⁆ * y⁻¹ = ⁅x, y'⁆ := by rw [hc x hx y' hy' y hy]; group
  have h2 : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [h2, h1]

theorem comm_mul_central_left {x y m : K} (hmx : m * x = x * m) (hmy : m * y = y * m) :
    ⁅x * m, y⁆ = ⁅x, y⁆ := by
  have h : m * y * m⁻¹ = y := by rw [hmy]; group
  calc ⁅x * m, y⁆ = x * (m * y * m⁻¹) * x⁻¹ * y⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅x, y⁆ := by rw [h]; simp only [commutatorElement_def]

theorem comm_mul_central_right {x y m : K} (hmx : m * x = x * m) (hmy : m * y = y * m) :
    ⁅x, y * m⁆ = ⁅x, y⁆ := by
  have h : m * x⁻¹ * m⁻¹ = x⁻¹ := by
    have : m * x⁻¹ = x⁻¹ * m := by
      have := congrArg (fun z => x⁻¹ * z * x⁻¹) hmx
      simpa [mul_assoc] using this.symm
    rw [this]; group
  calc ⁅x, y * m⁆ = x * y * (m * x⁻¹ * m⁻¹) * y⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅x, y⁆ := by rw [h]; simp only [commutatorElement_def]

end ClassTwo

section Pairing

variable {f : ℕ} [Fact f.Prime] {Ω N : Subgroup K}

theorem commutator_le_centralizer (hc : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ w ∈ Ω, w * ⁅x, y⁆ = ⁅x, y⁆ * w) :
    ⁅Ω, Ω⁆ ≤ centralizer (Ω : Set K) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [mem_centralizer_iff]
  intro w hw
  exact hc a ha b hb w hw

theorem exists_pairing (hc : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ w ∈ Ω, w * ⁅x, y⁆ = ⁅x, y⁆ * w)
    {W W' : Type} [AddCommGroup W] [Module (ZMod f) W] [AddCommGroup W'] [Module (ZMod f) W']
    {π : K → W} {ρ : Representation (ZMod f) ↥N W}
    {π' : K → W'} {ρ' : Representation (ZMod f) ↥N W'}
    (hs : ElemSec f Ω ⁅Ω, Ω⁆ N W π ρ) (hs' : ElemSec f ⁅Ω, Ω⁆ ⊥ N W' π' ρ') :
    ∃ B₀ : W → W → W', (∀ x ∈ Ω, ∀ y ∈ Ω, B₀ (π x) (π y) = π' ⁅x, y⁆) ∧
      (∀ u u' v, B₀ (u + u') v = B₀ u v + B₀ u' v) ∧
      (∀ u v v', B₀ u (v + v') = B₀ u v + B₀ u v') ∧ (∀ v, B₀ v v = 0) := by
  have hcent := commutator_le_centralizer hc
  have hcom : ∀ m ∈ (⁅Ω, Ω⁆ : Subgroup K), ∀ y ∈ Ω, m * y = y * m := by
    intro m hm y hy
    exact ((mem_centralizer_iff.mp (hcent hm)) y hy).symm
  have hle : (⁅Ω, Ω⁆ : Subgroup K) ≤ Ω := commutator_le_self Ω
  choose s hsΩ hsπ using hs.surj
  have hwd : ∀ x₁ ∈ Ω, ∀ x₂ ∈ Ω, ∀ y₁ ∈ Ω, ∀ y₂ ∈ Ω, π x₁ = π x₂ → π y₁ = π y₂ →
      ⁅x₁, y₁⁆ = ⁅x₂, y₂⁆ := by
    intro x₁ hx₁ x₂ hx₂ y₁ hy₁ y₂ hy₂ hx hy
    have hm : x₁⁻¹ * x₂ ∈ (⁅Ω, Ω⁆ : Subgroup K) := (hs.eq_iff hx₁ hx₂).mp hx
    have hn : y₁⁻¹ * y₂ ∈ (⁅Ω, Ω⁆ : Subgroup K) := (hs.eq_iff hy₁ hy₂).mp hy
    have hx₂e : x₂ = x₁ * (x₁⁻¹ * x₂) := by group
    have hy₂e : y₂ = y₁ * (y₁⁻¹ * y₂) := by group
    rw [hx₂e, hy₂e, comm_mul_central_left (hcom _ hm x₁ hx₁) (hcom _ hm _ (Ω.mul_mem hy₁
      (hle hn))), comm_mul_central_right (hcom _ hn x₁ hx₁) (hcom _ hn y₁ hy₁)]
  refine ⟨fun u v => π' ⁅s u, s v⁆, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact congrArg π' (hwd _ (hsΩ _) x hx _ (hsΩ _) y hy (hsπ _) (hsπ _))
  · intro u u' v
    have h1 : ⁅s (u + u'), s v⁆ = ⁅s u * s u', s v⁆ :=
      hwd _ (hsΩ _) _ (Ω.mul_mem (hsΩ u) (hsΩ u')) _ (hsΩ v) _ (hsΩ v)
        (by rw [hsπ, hs.add _ (hsΩ u) _ (hsΩ u'), hsπ, hsπ]) rfl
    show π' ⁅s (u + u'), s v⁆ = π' ⁅s u, s v⁆ + π' ⁅s u', s v⁆
    rw [h1, comm_mul_left hc (hsΩ u) (hsΩ u') (hsΩ v),
      hs'.add _ (Subgroup.commutator_mem_commutator (hsΩ u) (hsΩ v)) _
        (Subgroup.commutator_mem_commutator (hsΩ u') (hsΩ v))]
  · intro u v v'
    have h1 : ⁅s u, s (v + v')⁆ = ⁅s u, s v * s v'⁆ :=
      hwd _ (hsΩ _) _ (hsΩ u) _ (hsΩ _) _ (Ω.mul_mem (hsΩ v) (hsΩ v')) rfl
        (by rw [hsπ, hs.add _ (hsΩ v) _ (hsΩ v'), hsπ, hsπ])
    show π' ⁅s u, s (v + v')⁆ = π' ⁅s u, s v⁆ + π' ⁅s u, s v'⁆
    rw [h1, comm_mul_right hc (hsΩ u) (hsΩ v) (hsΩ v'),
      hs'.add _ (Subgroup.commutator_mem_commutator (hsΩ u) (hsΩ v)) _
        (Subgroup.commutator_mem_commutator (hsΩ u) (hsΩ v'))]
  · intro v
    show π' ⁅s v, s v⁆ = 0
    rw [commutatorElement_self]
    exact hs'.map_one

end Pairing

section Linear

variable {f : ℕ} [Fact f.Prime] {W : Type} [AddCommGroup W] [Module (ZMod f) W]
  [Module.Finite (ZMod f) W]

theorem alt_swap_zero {B : W →ₗ[ZMod f] W →ₗ[ZMod f] ZMod f} (hB : ∀ v, B v v = 0) {a b : W}
    (h : B a b = 0) : B b a = 0 := by
  have := CFSG.RankThree.PartOne.LIT.alt_skew hB b a
  rw [h] at this
  exact this.trans neg_zero

theorem exists_isotropic_three (hdim : Module.finrank (ZMod f) W = 4)
    (B : W →ₗ[ZMod f] W →ₗ[ZMod f] ZMod f) (hB : ∀ v, B v v = 0) {v₀ : W} (hv₀ : v₀ ≠ 0)
    (hrad : ∀ w, B v₀ w = 0) :
    ∃ U : Submodule (ZMod f) W, 3 ≤ Module.finrank (ZMod f) U ∧
      ∀ u ∈ U, ∀ u' ∈ U, B u u' = 0 := by
  classical
  haveI : Finite W := Module.finite_of_finite (ZMod f)
  have hf2 : 2 ≤ f := (Fact.out : f.Prime).two_le
  have hrad' : ∀ w, B w v₀ = 0 := fun w => alt_swap_zero hB (hrad w)
  set S₁ : Submodule (ZMod f) W := Submodule.span (ZMod f) {v₀} with hS₁
  have hS₁r : Module.finrank (ZMod f) S₁ = 1 := finrank_span_singleton hv₀
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, w₁ ∉ S₁ := by
    by_contra h
    push Not at h
    have : S₁ = ⊤ := eq_top_iff.mpr fun w _ => h w
    rw [this, finrank_top, hdim] at hS₁r
    omega
  set S₂ : Submodule (ZMod f) W := Submodule.span (ZMod f) {v₀, w₁} with hS₂
  have hS₁₂ : S₁ < S₂ := by
    refine lt_of_le_of_ne (Submodule.span_mono (by simp)) fun h => hw₁ ?_
    rw [h]
    exact Submodule.subset_span (by simp)
  have hS₂r : Module.finrank (ZMod f) S₂ ≤ 2 := by
    have h := finrank_span_finset_le_card (R := ZMod f) ({v₀, w₁} : Finset W)
    have e : (↑({v₀, w₁} : Finset W) : Set W) = {v₀, w₁} := by simp
    rw [e] at h
    exact h.trans Finset.card_le_two
  obtain ⟨w₂, hw₂L, hw₂⟩ : ∃ w₂, B w₁ w₂ = 0 ∧ w₂ ∉ S₂ := by
    by_contra h
    push Not at h
    let φ : W →+ ZMod f := (B w₁).toAddMonoidHom
    have h1 := AddSubgroup.card_ker_mul_card_range φ
    have hW : Nat.card W = f ^ 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod f) (V := W), Nat.card_zmod, hdim]
    have hr : Nat.card φ.range ≤ f := by
      have := AddSubgroup.card_le_card_addGroup φ.range
      rwa [Nat.card_zmod] at this
    have hS : Nat.card S₂ ≤ f ^ 2 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod f) (V := S₂), Nat.card_zmod]
      exact Nat.pow_le_pow_right (Fact.out : f.Prime).pos hS₂r
    have hker : Nat.card φ.ker ≤ Nat.card S₂ := by
      refine Nat.card_le_card_of_injective
        (fun w => ⟨w.1, h w.1 (AddMonoidHom.mem_ker.mp w.2 : (B w₁) w.1 = 0)⟩) ?_
      intro a b hab
      have := congrArg (fun x : S₂ => (x : W)) hab
      exact Subtype.ext this
    have h3 : f ^ 4 ≤ f ^ 2 * f := by
      calc f ^ 4 = Nat.card φ.ker * Nat.card φ.range := by rw [h1, hW]
        _ ≤ f ^ 2 * f := Nat.mul_le_mul (hker.trans hS) hr
    have h4 : f ^ 2 * f = f ^ 3 := by ring
    have h5 : f ^ 3 < f ^ 4 := Nat.pow_lt_pow_right hf2 (by norm_num)
    omega
  set S₃ : Submodule (ZMod f) W := Submodule.span (ZMod f) {v₀, w₁, w₂} with hS₃
  have hS₂₃ : S₂ < S₃ := by
    refine lt_of_le_of_ne (Submodule.span_mono (by intro x hx; simp at hx ⊢; tauto)) fun h => hw₂ ?_
    rw [h]
    exact Submodule.subset_span (by simp)
  refine ⟨S₃, ?_, ?_⟩
  · have h1 := Submodule.finrank_lt_finrank_of_lt hS₁₂
    have h2 := Submodule.finrank_lt_finrank_of_lt hS₂₃
    omega
  · have hw₂'' : B w₂ w₁ = 0 := alt_swap_zero hB hw₂L
    have gen : ∀ x ∈ ({v₀, w₁, w₂} : Set W), ∀ y ∈ ({v₀, w₁, w₂} : Set W), B x y = 0 := by
      intro x hx y hy
      rcases hx with rfl | rfl | rfl
      · exact hrad y
      · rcases hy with rfl | rfl | rfl
        · exact hrad' _
        · exact hB _
        · exact hw₂L
      · rcases hy with rfl | rfl | rfl
        · exact hrad' _
        · exact hw₂''
        · exact hB _
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      intro u' hu'
      induction hu' using Submodule.span_induction with
      | mem y hy => exact gen x hx y hy
      | zero => simp
      | add a b _ _ ha hb => simp [ha, hb]
      | smul c a _ ha => simp [ha]
    | zero => intro u' _; simp
    | add a b _ _ ha hb => intro u' hu'; simp [ha u' hu', hb u' hu']
    | smul c a _ ha => intro u' hu'; simp [ha u' hu']

end Linear

section Form

variable {f : ℕ} [Fact f.Prime] {Ω N : Subgroup K}

theorem zmod_smul_of_add {W V : Type*} [AddCommGroup W] [Module (ZMod f) W] [AddCommGroup V]
    [Module (ZMod f) V] (φ : W → V) (hφ : ∀ a b, φ (a + b) = φ a + φ b) (c : ZMod f) (w : W) :
    φ (c • w) = c • φ w :=
  ((AddMonoidHom.mk' φ hφ).toZModLinearMap f).map_smul c w

theorem exists_form (hexp : ∀ x ∈ Ω, x ^ f = 1)
    (hc : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ w ∈ Ω, w * ⁅x, y⁆ = ⁅x, y⁆ * w)
    (hNΩ : N ≤ normalizer (Ω : Set K)) (hcard : Nat.card (⁅Ω, Ω⁆ : Subgroup K) = f)
    (hab : ∀ E : Subgroup K, E ≤ Ω → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → Nat.card E ≤ f ^ 3)
    {W : Type} [AddCommGroup W] [Module (ZMod f) W] [Module.Finite (ZMod f) W]
    {π : K → W} {ρ : Representation (ZMod f) ↥N W}
    (hs : ElemSec f Ω ⁅Ω, Ω⁆ N W π ρ) (hdim : Module.finrank (ZMod f) W = 4) :
    ∃ (B : W →ₗ[ZMod f] W →ₗ[ZMod f] ZMod f) (lam : ↥N →* (ZMod f)ˣ),
      (∀ v, (∀ w, B v w = 0) → v = 0) ∧ (∀ v, B v v = 0) ∧
      ∀ g : ↥N, lam g = 1 → ∀ u w, B (ρ g u) (ρ g w) = B u w := by
  have hcent := commutator_le_centralizer hc
  have hle : (⁅Ω, Ω⁆ : Subgroup K) ≤ Ω := commutator_le_self Ω
  obtain ⟨W', _, _, _, π', ρ', hs'⟩ := exists_elemSec (f := f) (Y := (⁅Ω, Ω⁆ : Subgroup K))
    (M := ⊥) (G := N) bot_le
    (fun x _ m hm => by rw [Subgroup.mem_bot.mp hm]; simp)
    (fun x hx y hy => by
      have hxy : y * x = x * y := (mem_centralizer_iff.mp (hcent hx)) y (hle hy)
      rw [Subgroup.mem_bot, ← hxy]
      group)
    (fun x hx => by rw [hexp x (hle hx)]; exact one_mem _)
    (fun g hg => normalizer_le_normalizer_commutator Ω (hNΩ hg))
    (fun g _ => by rw [normalizer_eq_top_iff.mpr inferInstance]; exact mem_top _)
  have hW'card : Nat.card W' = f := by
    have := hs'.card_eq bot_le
    rw [hcard, Subgroup.card_bot, one_mul] at this
    exact this.symm
  have hW'dim : Module.finrank (ZMod f) W' = 1 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod f) (V := W')
    rw [Nat.card_zmod, hW'card] at h1
    have h2 : f ^ 1 = f ^ Module.finrank (ZMod f) W' := by rw [pow_one]; exact h1
    exact (Nat.pow_right_injective (Fact.out : f.Prime).two_le h2).symm
  let ι : W' ≃ₗ[ZMod f] ZMod f :=
    LinearEquiv.ofFinrankEq W' (ZMod f) (by rw [hW'dim, Module.finrank_self])
  obtain ⟨B₀, hB₀spec, hB₀1, hB₀2, hB₀alt⟩ := exists_pairing hc hs hs'
  let B : W →ₗ[ZMod f] W →ₗ[ZMod f] ZMod f :=
    LinearMap.mk₂ (ZMod f) (fun u v => ι (B₀ u v))
      (fun u u' v => by simp only [hB₀1, map_add])
      (fun c u v => by
        show ι (B₀ (c • u) v) = c • ι (B₀ u v)
        rw [zmod_smul_of_add (fun u => B₀ u v) (fun a b => hB₀1 a b v) c u, map_smul])
      (fun u v v' => by simp only [hB₀2, map_add])
      (fun c u v => by
        show ι (B₀ u (c • v)) = c • ι (B₀ u v)
        rw [zmod_smul_of_add (fun v => B₀ u v) (fun a b => hB₀2 u a b) c v, map_smul])
  have hBalt : ∀ v, B v v = 0 := fun v => by
    show ι (B₀ v v) = 0
    rw [hB₀alt, map_zero]
  let ρ'u : ↥N →* (W' ≃ₗ[ZMod f] W') :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod f) W').toMonoidHom.comp ρ'.toHomUnits
  have hρ'u : ∀ (g : ↥N) (w : W'), ρ'u g w = ρ' g w := fun g w => rfl
  refine ⟨B, LinearEquiv.det.comp ρ'u, ?_, hBalt, ?_⟩
  ·
    intro v₀ hv₀
    by_contra hne
    obtain ⟨U, hU3, hUiso⟩ := exists_isotropic_three hdim B hBalt hne hv₀
    have hcardU : Nat.card (hs.preimage U) = f * Nat.card U := by
      rw [hs.card_preimage hle, hcard]
    have hUle : hs.preimage U ≤ Ω := fun x hx => hx.1
    have hUab : ∀ a ∈ hs.preimage U, ∀ b ∈ hs.preimage U, a * b = b * a := by
      intro a ha b hb
      have h0 : B (π a) (π b) = 0 := hUiso _ ha.2 _ hb.2
      have h1 : π' ⁅a, b⁆ = 0 := by
        have h2 : ι (π' ⁅a, b⁆) = 0 := by
          have := hB₀spec a ha.1 b hb.1
          change ι (B₀ (π a) (π b)) = 0 at h0
          rw [this] at h0
          exact h0
        exact ι.injective (h2.trans (map_zero ι).symm)
      have h3 : ⁅a, b⁆ ∈ (⊥ : Subgroup K) :=
        (hs'.ker _ (Subgroup.commutator_mem_commutator ha.1 hb.1)).mp h1
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
      exact h3
    have h4 := hab _ hUle hUab
    haveI : Finite W := Module.finite_of_finite (ZMod f)
    have h5 : Nat.card U = f ^ Module.finrank (ZMod f) U := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod f) (V := U), Nat.card_zmod]
    have h6 : f ^ 3 ≤ Nat.card U := by
      rw [h5]
      exact Nat.pow_le_pow_right (Fact.out : f.Prime).pos hU3
    have h7 : f * f ^ 3 ≤ f * Nat.card U := Nat.mul_le_mul_left f h6
    have h8 : f ^ 3 < f * f ^ 3 := by
      have := (Fact.out : f.Prime).two_le
      have hpos : 0 < f ^ 3 := by positivity
      nlinarith
    rw [hcardU] at h4
    omega
  ·
    intro g hg u w
    obtain ⟨x, hx, rfl⟩ := hs.surj u
    obtain ⟨y, hy, rfl⟩ := hs.surj w
    have hid : ∀ w' : W', ρ' g w' = w' := by
      have h1 : LinearMap.det ((ρ'u g : W' ≃ₗ[ZMod f] W') : W' →ₗ[ZMod f] W') = 1 := by
        have := congrArg (fun z : (ZMod f)ˣ => (z : ZMod f)) hg
        simpa [LinearEquiv.coe_det] using this
      have h2 := CFSG.RankThree.PartOne.LIT.eq_id_of_det_eq_one_of_finrank_eq_one hW'dim _ h1
      exact fun w' => LinearMap.congr_fun h2 w'
    show ι (B₀ (ρ g (π x)) (ρ g (π y))) = ι (B₀ (π x) (π y))
    have hgx : (g : K) * x * (g : K)⁻¹ ∈ Ω := (mem_normalizer_iff.mp (hNΩ g.2) x).mp hx
    have hgy : (g : K) * y * (g : K)⁻¹ ∈ Ω := (mem_normalizer_iff.mp (hNΩ g.2) y).mp hy
    rw [hs.act g x hx, hs.act g y hy]
    simp only [Subgroup.coe_inv]
    rw [hB₀spec _ hgx _ hgy, hB₀spec x hx y hy]
    have e : ⁅(g : K) * x * (g : K)⁻¹, (g : K) * y * (g : K)⁻¹⁆ = (g : K) * ⁅x, y⁆ * (g : K)⁻¹ := by
      simp only [commutatorElement_def]; group
    have hact := hs'.act g _ (Subgroup.commutator_mem_commutator hx hy)
    simp only [Subgroup.coe_inv] at hact
    rw [e, ← hact, hid]

end Form

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2
