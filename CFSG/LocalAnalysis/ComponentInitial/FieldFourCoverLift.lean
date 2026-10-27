module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.InvariantFormRetraction
public import Mathlib.GroupTheory.Transfer

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

open Subgroup

variable {X P : Type*} [Group X] [Group P]

theorem card_comap_of_surjective [Finite X] {f : X →* P} (hf : Function.Surjective f)
    (H : Subgroup P) : Nat.card (H.comap f) = Nat.card H * Nat.card f.ker := by
  let ψ : H.comap f →* H := (f.comp (H.comap f).subtype).codRestrict _ fun x => x.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hψker : ψ.ker = f.ker.subgroupOf (H.comap f) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, ← OneMemClass.coe_eq_one]
    rfl
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv, hψker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (f.ker_le_comap H)).toEquiv] at h1
  exact h1

theorem isElementaryAbelian_of_sq_eq_one {H : Subgroup X} (h : ∀ x ∈ H, x ^ 2 = 1) :
    CFSG.IsElementaryAbelian 2 H := by
  have h' : ∀ x : H, x ^ 2 = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, h x x.2, Subgroup.coe_one])
  have hinv : ∀ x : H, x⁻¹ = x := fun x => by
    rw [inv_eq_iff_mul_eq_one, ← sq, h']
  have hcomm : IsMulCommutative H := ⟨⟨fun a b => by
    calc a * b = (a * b)⁻¹ := (hinv _).symm
      _ = b * a := by rw [mul_inv_rev, hinv, hinv]⟩⟩
  exact
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one h' }

section Central

variable {π : X →* P}

theorem sq_eq_one_of_comap (hπ : Function.Surjective π) (hCZ : π.ker ≤ center X)
    (hC2 : ∀ c ∈ π.ker, c ^ 2 = 1) {R : Subgroup P} (hR2 : ∀ r ∈ R, r ^ 2 = 1)
    (hRc : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r)
    (htrans : ∀ r ∈ R, ∀ s ∈ R, r ≠ 1 → s ≠ 1 → ∃ g : P, g * r * g⁻¹ = s)
    (hind : ∃ r₁ ∈ R, ∃ r₂ ∈ R, ∃ r₃ ∈ R, r₁ ≠ 1 ∧ r₂ ≠ 1 ∧ r₃ ≠ 1 ∧ r₁ * r₂ ≠ 1 ∧
      r₁ * r₃ ≠ 1 ∧ r₂ * r₃ ≠ 1 ∧ r₁ * (r₂ * r₃) ≠ 1) :
    ∀ x ∈ R.comap π, x ^ 2 = 1 := by
  have hcent : ∀ c ∈ π.ker, ∀ g : X, g * c = c * g := fun c hc g =>
    mem_center_iff.1 (hCZ hc) g
  have hsqC : ∀ x ∈ R.comap π, x ^ 2 ∈ π.ker := fun x hx => by
    rw [MonoidHom.mem_ker, map_pow]
    exact hR2 _ hx
  have hconst : ∀ x ∈ R.comap π, ∀ y ∈ R.comap π, π x ≠ 1 → π y ≠ 1 → x ^ 2 = y ^ 2 := by
    intro x hx y hy hx1 hy1
    obtain ⟨g, hg⟩ := htrans _ hx _ hy hx1 hy1
    obtain ⟨g', rfl⟩ := hπ g
    have hcC : y⁻¹ * (g' * x * g'⁻¹) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hg, inv_mul_cancel]
    set c := y⁻¹ * (g' * x * g'⁻¹) with hc
    have hxy : g' * x * g'⁻¹ = y * c := by rw [hc, mul_inv_cancel_left]
    have h1 : g' * x ^ 2 * g'⁻¹ = x ^ 2 := by rw [hcent _ (hsqC x hx) g', mul_inv_cancel_right]
    calc x ^ 2 = g' * x ^ 2 * g'⁻¹ := h1.symm
      _ = (g' * x * g'⁻¹) ^ 2 := by rw [sq, sq]; group
      _ = (y * c) ^ 2 := by rw [hxy]
      _ = y * (c * y) * c := by rw [sq]; group
      _ = y ^ 2 * c ^ 2 := by rw [← hcent c hcC y, sq, sq]; group
      _ = y ^ 2 := by rw [hC2 c hcC, mul_one]
  obtain ⟨r₁, h₁, r₂, h₂, r₃, h₃, h1, h2, h3, h12, h13, h23, h123⟩ := hind
  obtain ⟨x₁, rfl⟩ := hπ r₁
  obtain ⟨x₂, rfl⟩ := hπ r₂
  obtain ⟨x₃, rfl⟩ := hπ r₃
  have hx₁ : x₁ ∈ R.comap π := h₁
  have hc2 : (x₁ ^ 2) ^ 2 = 1 := hC2 _ (hsqC x₁ hx₁)
  have hcomm : ∀ x ∈ R.comap π, ∀ y ∈ R.comap π, π x ≠ 1 → π y ≠ 1 → π (x * y) ≠ 1 →
      y * x * y⁻¹ * x⁻¹ = x₁ ^ 2 := by
    intro x hx y hy hx1 hy1 hxy1
    have ex : x ^ 2 = x₁ ^ 2 := hconst x hx x₁ hx₁ hx1 h1
    have ey : y ^ 2 = x₁ ^ 2 := hconst y hy x₁ hx₁ hy1 h1
    have exy : (x * y) ^ 2 = x₁ ^ 2 := hconst (x * y) (mul_mem hx hy) x₁ hx₁ hxy1 h1
    have hdC : y * x * y⁻¹ * x⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hRc _ hy _ hx]
      group
    set d := y * x * y⁻¹ * x⁻¹ with hd
    have hyx : y * x = d * x * y := by rw [hd]; group
    have hsq : (x * y) ^ 2 = d * (x ^ 2 * y ^ 2) := by
      calc (x * y) ^ 2 = x * (y * x) * y := by rw [sq]; group
        _ = x * d * (x * y) * y := by rw [hyx]; group
        _ = d * x * (x * y) * y := by rw [hcent d hdC x]
        _ = d * (x ^ 2 * y ^ 2) := by rw [sq, sq]; group
    rw [exy, ex, ey] at hsq
    calc d = d * (x₁ ^ 2 * x₁ ^ 2) := by rw [← sq, hc2, mul_one]
      _ = x₁ ^ 2 := hsq.symm
  have hx₂ : x₂ ∈ R.comap π := h₂
  have hx₃ : x₃ ∈ R.comap π := h₃
  have e12 := hcomm x₁ hx₁ x₂ hx₂ h1 h2 (by rwa [map_mul])
  have e13 := hcomm x₁ hx₁ x₃ hx₃ h1 h3 (by rwa [map_mul])
  have e123 := hcomm x₁ hx₁ (x₂ * x₃) (mul_mem hx₂ hx₃) h1 (by rwa [map_mul])
    (by rwa [map_mul, map_mul])
  have hcC : x₃ * x₁ * x₃⁻¹ * x₁⁻¹ ∈ π.ker := by
    rw [e13]
    exact hsqC x₁ hx₁
  have hsplit : x₂ * x₃ * x₁ * (x₂ * x₃)⁻¹ * x₁⁻¹ =
      (x₃ * x₁ * x₃⁻¹ * x₁⁻¹) * (x₂ * x₁ * x₂⁻¹ * x₁⁻¹) := by
    calc x₂ * x₃ * x₁ * (x₂ * x₃)⁻¹ * x₁⁻¹ =
        x₂ * (x₃ * x₁ * x₃⁻¹ * x₁⁻¹) * x₁ * x₂⁻¹ * x₁⁻¹ := by group
      _ = (x₃ * x₁ * x₃⁻¹ * x₁⁻¹) * x₂ * x₁ * x₂⁻¹ * x₁⁻¹ := by rw [hcent _ hcC x₂]
      _ = _ := by group
  have hc1 : x₁ ^ 2 = 1 := by
    have h := hsplit
    rw [e123, e13, e12, ← sq, hc2] at h
    exact h
  intro x hx
  by_cases hx1 : π x = 1
  · exact hC2 x hx1
  · rw [hconst x hx x₁ hx₁ hx1 h1, hc1]

end Central

theorem lift_complement {D : Type*} [Group D] {π : X →* P} (hπ : Function.Surjective π)
    {R : Subgroup P} {δ : D →* P} (hδ : Function.Injective δ)
    (hN : normalizer (R : Set P) = R ⊔ δ.range) (hRL : R ⊓ δ.range = ⊥) (s : D →* X)
    (hs : ∀ d, π (s d) = δ d) :
    Function.Injective s ∧ (∀ d, s d ∈ normalizer (R.comap π : Set X)) ∧
      R.comap π ⊔ s.range = normalizer (R.comap π : Set X) ∧ R.comap π ⊓ s.range = ⊥ := by
  have hNX : normalizer (R.comap π : Set X) = (normalizer (R : Set P)).comap π :=
    (Subgroup.comap_normalizer_eq_of_surjective R hπ).symm
  have hLN : δ.range ≤ normalizer (R : Set P) := hN ▸ le_sup_right
  have hsN : ∀ d, s d ∈ normalizer (R.comap π : Set X) := fun d => by
    rw [hNX, Subgroup.mem_comap, hs]
    exact hLN ⟨d, rfl⟩
  refine ⟨fun d d' h => hδ (by rw [← hs, ← hs, h]), hsN, le_antisymm (sup_le le_normalizer ?_) ?_,
    ?_⟩
  · rintro _ ⟨d, rfl⟩
    exact hsN d
  · intro x hx
    rw [hNX, Subgroup.mem_comap, hN, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_right_le_normalizer_left R δ.range hLN] at hx
    obtain ⟨r, hr, _, ⟨d, rfl⟩, hrd⟩ := hx
    have hh : x * (s d)⁻¹ ∈ R.comap π := by
      rw [Subgroup.mem_comap, map_mul, map_inv, hs, ← hrd, mul_inv_cancel_right]
      exact hr
    have : x = x * (s d)⁻¹ * s d := by group
    rw [this]
    exact mul_mem_sup hh ⟨d, rfl⟩
  · rw [eq_bot_iff]
    rintro _ ⟨hx, d, rfl⟩
    have h1 : δ d ∈ R ⊓ δ.range := ⟨by rw [← hs]; exact hx, d, rfl⟩
    rw [hRL, Subgroup.mem_bot, ← map_one δ] at h1
    rw [hδ h1, map_one]
    exact one_mem _

theorem card_normalizer_of_lift {D : Type*} [Group D] {π : X →* P}
    {R : Subgroup P} (s : D →* X) (hs : Function.Injective s)
    (hsN : ∀ d, s d ∈ normalizer (R.comap π : Set X))
    (hsup : R.comap π ⊔ s.range = normalizer (R.comap π : Set X))
    (hinf : R.comap π ⊓ s.range = ⊥) :
    Nat.card (normalizer (R.comap π : Set X)) = Nat.card (R.comap π) * Nat.card D := by
  have hle : s.range ≤ normalizer (R.comap π : Set X) := by
    rintro _ ⟨d, rfl⟩
    exact hsN d
  rw [← hsup, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hle
    (disjoint_iff.2 hinf), Nat.card_congr (MonoidHom.ofInjective hs).toEquiv.symm]

section Transfer

open scoped IsMulCommutative

variable [Finite X] {π : X →* P} [IsMulCommutative π.ker]

theorem transfer_retraction (hπ : Function.Surjective π) (hCZ : π.ker ≤ center X)
    (hC2 : ∀ c ∈ π.ker, c ^ 2 = 1) (L : Subgroup P) {T : Subgroup X} (hTQ : T ≤ L.comap π)
    (hCT : π.ker ≤ T) (hodd : Odd (T.subgroupOf (L.comap π)).index) (lam : T →* π.ker)
    (hlam : ∀ c : π.ker, lam (Subgroup.inclusion hCT c) = c) :
    (∀ c : π.ker, (lam.comp (Subgroup.subgroupOfEquivOfLe hTQ).toMonoidHom).transfer
        (Subgroup.inclusion (π.ker_le_comap L) c) = c) ∧
      ∃ e : ((lam.comp (Subgroup.subgroupOfEquivOfLe hTQ).toMonoidHom).transfer).ker ≃* L,
        ∀ x, (e x : P) = π ((x : L.comap π) : X) := by
  set Q := L.comap π with hQ
  set τ : Q →* π.ker := (lam.comp (Subgroup.subgroupOfEquivOfLe hTQ).toMonoidHom).transfer
    with hτ
  have hCQ : π.ker ≤ Q := π.ker_le_comap L
  have hτC : ∀ c : π.ker, τ (Subgroup.inclusion hCQ c) = c := by
    intro c
    have key : ∀ (n : ℕ) (g₀ : Q), g₀⁻¹ * Subgroup.inclusion hCQ c ^ n * g₀ ∈
        T.subgroupOf Q → g₀⁻¹ * Subgroup.inclusion hCQ c ^ n * g₀ =
          Subgroup.inclusion hCQ c ^ n := by
      intro n g₀ _
      apply Subtype.ext
      have hc : (c : X) ^ n ∈ π.ker := π.ker.pow_mem c.2 n
      change (g₀ : X)⁻¹ * (c : X) ^ n * g₀ = (c : X) ^ n
      rw [mul_assoc, ← mem_center_iff.1 (hCZ hc) (g₀ : X), inv_mul_cancel_left]
    rw [hτ, MonoidHom.transfer_eq_pow _ _ key]
    obtain ⟨m, hm⟩ := hodd
    have hcpow : (c : X) ^ (T.subgroupOf Q).index = c := by
      rw [hm, pow_succ, pow_mul, hC2 _ c.2, one_pow, one_mul]
    apply Subtype.ext
    have h1 : ((Subgroup.subgroupOfEquivOfLe hTQ)
        ⟨Subgroup.inclusion hCQ c ^ (T.subgroupOf Q).index,
          MonoidHom.transfer_eq_pow_aux _ key⟩ : T) = Subgroup.inclusion hCT c := by
      apply Subtype.ext
      change ((c : X) ^ (T.subgroupOf Q).index) = c
      exact hcpow
    change ((lam ((Subgroup.subgroupOfEquivOfLe hTQ)
      ⟨Subgroup.inclusion hCQ c ^ (T.subgroupOf Q).index,
        MonoidHom.transfer_eq_pow_aux _ key⟩) : π.ker) : X) = c
    rw [h1, hlam]
  refine ⟨hτC, ?_⟩
  let f : τ.ker →* L := ((π.comp Q.subtype).comp τ.ker.subtype).codRestrict L fun x => x.1.2
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxC : ((x : Q) : X) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hx
    have h1 : τ (Subgroup.inclusion hCQ ⟨_, hxC⟩) = ⟨_, hxC⟩ := hτC ⟨_, hxC⟩
    have h2 : Subgroup.inclusion hCQ ⟨_, hxC⟩ = (x : Q) := Subtype.ext rfl
    rw [h2, x.2] at h1
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg Subtype.val h1).symm
  have hfsurj : Function.Surjective f := by
    rintro ⟨l, hl⟩
    obtain ⟨q, rfl⟩ := hπ l
    let q' : Q := ⟨q, hl⟩
    refine ⟨⟨q' * (Subgroup.inclusion hCQ (τ q'))⁻¹, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, hτC, mul_inv_cancel]
    · apply Subtype.ext
      change π (q * ((τ q' : π.ker) : X)⁻¹) = π q
      rw [map_mul, map_inv, MonoidHom.mem_ker.1 (τ q').2, inv_one, mul_one]
  exact ⟨MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩, fun x => rfl⟩

end Transfer

open scoped IsMulCommutative in
theorem exists_retraction {C T : Subgroup X} (hCT : C ≤ T) (hT : CFSG.IsElementaryAbelian 2 T) :
    ∃ lam : T →* C, ∀ c : C, lam (Subgroup.inclusion hCT c) = c := by
  have hT2 : ∀ t : T, t ^ 2 = 1 := fun t => Subtype.ext (by
    rw [Subgroup.coe_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := T) t t.2,
      Subgroup.coe_one])
  obtain ⟨p, hp, hpC⟩ := exists_retraction_of_sq_eq_one hT2 (C.subgroupOf T)
  refine ⟨(Subgroup.subgroupOfEquivOfLe hCT).toMonoidHom.comp (p.codRestrict _ hp), fun c => ?_⟩
  apply Subtype.ext
  change (((p (Subgroup.inclusion hCT c)) : T) : X) = c
  rw [hpC _ (by rw [Subgroup.mem_subgroupOf]; exact c.2)]
  rfl

end CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
