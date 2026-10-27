module

public import CFSG.LieType.Chevalley.E6GraphInnerCosetExhaustion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphFullCoset

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphInnerCoset
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Generic

variable {M : Type*} [Group M] {G : Subgroup M}

theorem exists_mul_pow_eq {g z : M} (hg : g ∈ G) (hz : z ∈ Subgroup.normalizer (G : Set M))
    (n : ℕ) : ∃ c ∈ G, (g * z) ^ n = c * z ^ n := by
  induction n with
  | zero => exact ⟨1, G.one_mem, by rw [pow_zero, pow_zero, one_mul]⟩
  | succ n ih =>
    obtain ⟨c, hc, e⟩ := ih
    refine ⟨c * (z ^ n * g * (z ^ n)⁻¹),
      G.mul_mem hc ((Subgroup.mem_normalizer_iff.1 (pow_mem hz n) g).1 hg), ?_⟩
    rw [pow_succ, e, pow_succ]
    group

theorem exists_conj_eq_conj_mul_of_odd {H : Type*} [Group H] {x η : MulAut H} (hη : η * η = 1)
    (hα : (x * η) ^ 2 = 1) {m : ℕ} (hm : Odd m) {c : H} (hx : x ^ m = MulAut.conj c) :
    ∃ φ : MulAut H, φ * (x * η) * φ⁻¹ = MulAut.conj c * η := by
  obtain ⟨k, rfl⟩ := hm
  have hη' : η⁻¹ = η := (eq_inv_of_mul_eq_one_left hη).symm
  have h1 : η * x * η⁻¹ = x⁻¹ := by
    rw [hη']
    have h : x * η * (x * η) = 1 := by rw [← sq]; exact hα
    calc η * x * η = x⁻¹ * (x * η * (x * η)) := by group
      _ = x⁻¹ := by rw [h, mul_one]
  have h2 : η * x ^ k * η⁻¹ = x⁻¹ ^ k := by rw [← conj_pow, h1]
  refine ⟨x ^ k, ?_⟩
  calc x ^ k * (x * η) * (x ^ k)⁻¹ = x ^ k * x * (η * x ^ k * η⁻¹)⁻¹ * η := by group
    _ = x ^ k * x * (x⁻¹ ^ k)⁻¹ * η := by rw [h2]
    _ = x ^ (2 * k + 1) * η := by group
    _ = MulAut.conj c * η := by rw [hx]

theorem exists_conj_eq_inner_mul {P w : M} (hPP : P * P = 1) {η : MulAut G}
    (hη : ∀ g : G, (η g : M) = P * g * P⁻¹) (hw : w ∈ Subgroup.normalizer (G : Set M)) {m : ℕ}
    (hm : Odd m) (hwm : w ^ m ∈ G) {α : MulAut G}
    (hα : ∀ g : G, (α g : M) = w * (P * g * P⁻¹) * w⁻¹) (hα2 : α ^ 2 = 1) :
    ∃ (φ : MulAut G) (c : G), φ * α * φ⁻¹ = MulAut.conj c * η := by
  set x := G.normalizerMonoidHom ⟨w, hw⟩ with hxdef
  have hxα : α = x * η := MulEquiv.ext fun g => Subtype.ext (by
    rw [hα, MulAut.mul_apply, hxdef, Subgroup.normalizerMonoidHom_apply_apply_coe, hη])
  have hηη : η * η = 1 := MulEquiv.ext fun g => Subtype.ext (by
    rw [MulAut.mul_apply, hη, hη, MulAut.one_apply]
    calc P * (P * g * P⁻¹) * P⁻¹ = (P * P) * g * (P * P)⁻¹ := by group
      _ = g := by rw [hPP]; group)
  have hxm : x ^ m = MulAut.conj (⟨w ^ m, hwm⟩ : G) := by
    rw [hxdef, ← map_pow]
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
    simp
  rw [hxα] at hα2 ⊢
  obtain ⟨φ, hφ⟩ := exists_conj_eq_conj_mul_of_odd hηη hα2 hm hxm
  exact ⟨φ, _, hφ⟩

theorem inner_case {P t : M} (ht : t ∈ G) {η : MulAut G} (hη : ∀ g : G, (η g : M) = P * g * P⁻¹)
    (hexh : ∀ a ∈ G, (a * P) ^ 2 = 1 → (∃ g ∈ G, g * (a * P) * g⁻¹ = P) ∨
      ∃ g ∈ G, g * (a * P) * g⁻¹ = t * P)
    (hfaith : ∀ x ∈ G ⊔ Subgroup.zpowers P, (∀ g ∈ G, x * g * x⁻¹ = g) → x = 1)
    {c : G} (hc : (MulAut.conj c * η) ^ 2 = 1) :
    (∃ φ : MulAut G, φ * (MulAut.conj c * η) * φ⁻¹ = η) ∨
      ∃ φ : MulAut G, φ * (MulAut.conj c * η) * φ⁻¹ = MulAut.conj ⟨t, ht⟩ * η := by
  have happ : ∀ (b g : G), ((MulAut.conj b * η) g : M) = ((b : M) * P) * g * ((b : M) * P)⁻¹ := by
    intro b g
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hη]
    group
  have hconj : ∀ (g b h : G), ((MulAut.conj g * (MulAut.conj b * η) * (MulAut.conj g)⁻¹) h : M) =
      ((g : M) * ((b : M) * P) * (g : M)⁻¹) * h * ((g : M) * ((b : M) * P) * (g : M)⁻¹)⁻¹ := by
    intro g b h
    rw [← map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, happ, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hsq : ((c : M) * P) ^ 2 = 1 := by
    refine hfaith _ (pow_mem (mul_mem (Subgroup.mem_sup_left c.2)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers P))) 2) fun g hg => ?_
    have h1 : (((MulAut.conj c * η) ^ 2) ⟨g, hg⟩ : M) =
        ((c : M) * P) ^ 2 * g * (((c : M) * P) ^ 2)⁻¹ := by
      rw [sq, sq, MulAut.mul_apply, happ, happ]
      group
    rw [hc, MulAut.one_apply] at h1
    exact h1.symm
  rcases hexh c c.2 hsq with ⟨g, hg, hgc⟩ | ⟨g, hg, hgc⟩
  · refine Or.inl ⟨MulAut.conj ⟨g, hg⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
    rw [hconj]
    change (g * ((c : M) * P) * g⁻¹) * h * (g * ((c : M) * P) * g⁻¹)⁻¹ = _
    rw [hgc, hη]
  · refine Or.inr ⟨MulAut.conj ⟨g, hg⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
    rw [hconj, happ]
    change (g * ((c : M) * P) * g⁻¹) * h * (g * ((c : M) * P) * g⁻¹)⁻¹ = _
    rw [hgc]

theorem mem_normalizer_of_mul_self {P : M} (hPP : P * P = 1)
    (hPG : ∀ g ∈ G, P * g * P⁻¹ ∈ G) : P ∈ Subgroup.normalizer (G : Set M) := by
  refine Subgroup.mem_normalizer_iff.2 fun g => ⟨hPG g, fun h => ?_⟩
  have hPinv : P⁻¹ = P := (eq_inv_of_mul_eq_one_left hPP).symm
  have := hPG _ h
  rwa [show P * (P * g * P⁻¹) * P⁻¹ = g by
    rw [hPinv]
    calc P * (P * g * P) * P = (P * P) * g * (P * P) := by group
      _ = g := by rw [hPP, one_mul, mul_one]] at this

end Generic

section Transport

variable {C G : Type*} [Group C] [Group G]

theorem congr_conj (ψ : C ≃* G) (c : C) : MulAut.congr ψ (MulAut.conj c) = MulAut.conj (ψ c) :=
  MulEquiv.ext fun g => by
    simp [MulAut.congr_apply]

theorem transport_conj (ψ : C ≃* G) {α β : MulAut C} (h : ∃ φ : MulAut C, φ * α * φ⁻¹ = β) :
    ∃ φ : MulAut G, φ * MulAut.congr ψ α * φ⁻¹ = MulAut.congr ψ β := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨MulAut.congr ψ φ, by rw [← map_inv, ← map_mul, ← map_mul, hφ]⟩

theorem transport_not_conj (ψ : C ≃* G) {α β : MulAut C} (h : ∀ φ : MulAut C, φ * α * φ⁻¹ ≠ β) :
    ∀ φ : MulAut G, φ * MulAut.congr ψ α * φ⁻¹ ≠ MulAut.congr ψ β := by
  intro φ hφ
  apply h ((MulAut.congr ψ).symm φ)
  apply (MulAut.congr ψ).injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hφ]

end Transport

theorem nonempty_ringHom_of_card {f : ℕ} (hf : 1 ≤ f) {k K : Type} [Field k] [Field K]
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) : Nonempty (k →+* K) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (two_eq_zero_of_card hf hk)
  have : CharP K 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (two_eq_zero_of_card_sq hf hK)
  let _ : Algebra (ZMod 2) k := ZMod.algebra k 2
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hfin : ∀ (F : Type) [Field F] [Finite F] [Algebra (ZMod 2) F] (n : ℕ),
      Nat.card F = 2 ^ n → Module.finrank (ZMod 2) F = n := by
    intro F _ _ _ n hF
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [hF, Nat.card_zmod] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have h1 := hfin k f hk
  have h2 := hfin K (2 * f) (by rw [hK, ← pow_mul, mul_comm])
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2) (K := k) (L := K)
    (by rw [h1, h2]; exact dvd_mul_left f 2)
  exact ⟨φ.toRingHom⟩

@[expose] def IsOrdinaryDiagGraph (k : Type) [Field k]
    (α : MulAut (adjointGroup TwistTag.E6.tag k)) : Prop :=
  ∃ (g : ModGL TwistTag.E6.tag k) (a : Fin TwistTag.E6.tag.rank → kˣ),
    g ∈ adjointGroup TwistTag.E6.tag k ∧ ∀ h : adjointGroup TwistTag.E6.tag k,
      (α h : ModGL TwistTag.E6.tag k) = g * rootDiagUnit TwistTag.E6.tag a *
        (diagramMap TwistTag.E6 k * h * (diagramMap TwistTag.E6 k)⁻¹) *
          (g * rootDiagUnit TwistTag.E6.tag a)⁻¹

@[expose] def IsTwistedDiagGraph
    (K : Type) [Field K] (σ : K →+* K)
    (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ)) : Prop :=
  ∃ (g : ModGL TwistTag.E6.tag K)
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ a)ˣ),
    g ∈ graphFixedRootGroup TwistTag.E6 K σ ∧ ∀ h : graphFixedRootGroup TwistTag.E6 K σ,
      (α h : ModGL TwistTag.E6.tag K) =
        g * rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ u) *
          (diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) *
            (g * rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ u))⁻¹

theorem odd_two_pow_sub_one {f : ℕ} (hf : 1 ≤ f) : Odd (2 ^ f - 1) := by
  have h1 := Nat.one_le_two_pow (n := f)
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  rw [Nat.odd_iff]
  omega

section Cases

variable {M : Type*} [Group M] {G : Subgroup M} {P t : M}

theorem conj_of_odd_diag (hPP : P * P = 1) (ht : t ∈ G) {η : MulAut G}
    (hη : ∀ g : G, (η g : M) = P * g * P⁻¹)
    (hexh : ∀ a ∈ G, (a * P) ^ 2 = 1 → (∃ g ∈ G, g * (a * P) * g⁻¹ = P) ∨
      ∃ g ∈ G, g * (a * P) * g⁻¹ = t * P)
    (hfaith : ∀ x ∈ G ⊔ Subgroup.zpowers P, (∀ g ∈ G, x * g * x⁻¹ = g) → x = 1)
    {w : M} (hw : w ∈ Subgroup.normalizer (G : Set M)) {m : ℕ} (hm : Odd m) (hwm : w ^ m ∈ G)
    {α : MulAut G} (hα : ∀ g : G, (α g : M) = w * (P * g * P⁻¹) * w⁻¹) (hα2 : α ^ 2 = 1) :
    (∃ φ : MulAut G, φ * α * φ⁻¹ = η) ∨
      ∃ φ : MulAut G, φ * α * φ⁻¹ = MulAut.conj ⟨t, ht⟩ * η := by
  obtain ⟨φ₁, c, hφ₁⟩ := exists_conj_eq_inner_mul hPP hη hw hm hwm hα hα2
  have hc2 : (MulAut.conj c * η) ^ 2 = 1 := by
    rw [← hφ₁, conj_pow, hα2, mul_one, mul_inv_cancel]
  have e : ∀ φ₂ : MulAut G, φ₂ * φ₁ * α * (φ₂ * φ₁)⁻¹ = φ₂ * (φ₁ * α * φ₁⁻¹) * φ₂⁻¹ :=
    fun φ₂ => by group
  rcases inner_case ht hη hexh hfaith hc2 with ⟨φ₂, hφ₂⟩ | ⟨φ₂, hφ₂⟩
  · exact Or.inl ⟨φ₂ * φ₁, by rw [e, hφ₁, hφ₂]⟩
  · exact Or.inr ⟨φ₂ * φ₁, by rw [e, hφ₁, hφ₂]⟩

end Cases

theorem isOrdinaryDiagGraph_iff
    (k : Type) [Field k] [Finite k]
    (Θ : MulAut (adjointGroup TwistTag.E6.tag k) →*
      RingAut k × Multiplicative (ZMod (exactE TwistTag.E6.tag)))
    (hΘ : ∀ (α : MulAut (adjointGroup TwistTag.E6.tag k)) (g : adjointGroup TwistTag.E6.tag k)
      (a : Fin TwistTag.E6.tag.rank → kˣ) (σ : k ≃+* k) (ε : Fin (exactE TwistTag.E6.tag)),
      (∀ h : adjointGroup TwistTag.E6.tag k, (α h : ModGL TwistTag.E6.tag k) =
        (g : ModGL TwistTag.E6.tag k) * rootDiagUnit TwistTag.E6.tag a *
          exactQ TwistTag.E6.tag k ε * Units.map (entrywiseHom σ.toRingHom)
            (h : ModGL TwistTag.E6.tag k) * (exactQ TwistTag.E6.tag k ε)⁻¹ *
              (rootDiagUnit TwistTag.E6.tag a)⁻¹ * (g : ModGL TwistTag.E6.tag k)⁻¹) →
      Θ α = (σ, Multiplicative.ofAdd ((ε : ℕ) : ZMod (exactE TwistTag.E6.tag))))
    (α : MulAut (adjointGroup TwistTag.E6.tag k)) :
    IsOrdinaryDiagGraph k α ↔ Θ α = (1, Multiplicative.ofAdd 1) := by
  have hid : ∀ h : ModGL TwistTag.E6.tag k,
      Units.map (entrywiseHom (RingEquiv.refl k).toRingHom) h = h :=
    fun h => Units.ext (entrywise_id _)
  constructor
  · rintro ⟨g, a, hg, hα⟩
    have h1 := hΘ α ⟨g, hg⟩ a (RingEquiv.refl k) ⟨1, by decide⟩ fun h => by
      rw [hα h, hid, exactQ_E6, pow_one]
      group
    rw [h1]
    rfl
  · intro h1
    obtain ⟨g, a, σ, ε, rfl⟩ :=
      exists_conj_mul_exactNormalAut (τ := TwistTag.E6.tag) (K := k) (Or.inl rfl) α
    have h2 := hΘ (MulAut.conj g * exactNormalAut TwistTag.E6.tag k a σ ε) g a σ ε fun h => by
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, coe_exactNormalAut]
      group
    rw [h1] at h2
    have hσ : σ = 1 := (congrArg Prod.fst h2).symm
    have h3 : ((ε : ℕ) : ZMod 2) = 1 := (congrArg (fun x => Multiplicative.toAdd x.2) h2).symm
    have h4 : (ε : ℕ) = 1 := by
      have h5 := congrArg ZMod.val h3
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (show (ε : ℕ) < 2 from ε.2)] at h5
      exact h5
    refine ⟨g, a, g.2, fun h => ?_⟩
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_exactNormalAut, hσ, h4, exactQ_E6, pow_one]
    rw [show (1 : RingAut k) = RingEquiv.refl k from rfl, hid]
    group


theorem ordinary_full
    {f : ℕ} (hf : 1 ≤ f) (k : Type) [Field k] (hk : Nat.card k = 2 ^ f) :
    ∃ (ht : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag k)
      (η : MulAut (adjointGroup TwistTag.E6.tag k)),
      (∀ h : adjointGroup TwistTag.E6.tag k, (η h : ModGL TwistTag.E6.tag k) =
        diagramMap TwistTag.E6 k * h * (diagramMap TwistTag.E6 k)⁻¹) ∧
      (∀ α : MulAut (adjointGroup TwistTag.E6.tag k), IsOrdinaryDiagGraph k α → α ^ 2 = 1 →
        (∃ φ : MulAut (adjointGroup TwistTag.E6.tag k), φ * α * φ⁻¹ = η) ∨
          ∃ φ : MulAut (adjointGroup TwistTag.E6.tag k), φ * α * φ⁻¹ = MulAut.conj ⟨_, ht⟩ * η) ∧
      (∀ Θ : MulAut (adjointGroup TwistTag.E6.tag k) →*
          RingAut k × Multiplicative (ZMod (exactE TwistTag.E6.tag)),
        (∀ (α : MulAut (adjointGroup TwistTag.E6.tag k)) (g : adjointGroup TwistTag.E6.tag k)
          (a : Fin TwistTag.E6.tag.rank → kˣ) (σ : k ≃+* k) (ε : Fin (exactE TwistTag.E6.tag)),
          (∀ h : adjointGroup TwistTag.E6.tag k, (α h : ModGL TwistTag.E6.tag k) =
            (g : ModGL TwistTag.E6.tag k) * rootDiagUnit TwistTag.E6.tag a *
              exactQ TwistTag.E6.tag k ε * Units.map (entrywiseHom σ.toRingHom)
                (h : ModGL TwistTag.E6.tag k) * (exactQ TwistTag.E6.tag k ε)⁻¹ *
                  (rootDiagUnit TwistTag.E6.tag a)⁻¹ * (g : ModGL TwistTag.E6.tag k)⁻¹) →
          Θ α = (σ, Multiplicative.ofAdd ((ε : ℕ) : ZMod (exactE TwistTag.E6.tag)))) →
        ∀ α : MulAut (adjointGroup TwistTag.E6.tag k),
          IsOrdinaryDiagGraph k α ↔ Θ α = (1, Multiplicative.ofAdd 1)) ∧
      (∀ φ : MulAut (adjointGroup TwistTag.E6.tag k), φ * η * φ⁻¹ ≠ MulAut.conj ⟨_, ht⟩ * η) ∧
      ∀ (G : Type) [Group G] (e : G ≃* AdjointQuotient TwistTag.E6.tag k),
        ∃ ψ : adjointGroup TwistTag.E6.tag k ≃* G,
          (∀ c, e (ψ c) = (QuotientGroup.mk c : AdjointQuotient TwistTag.E6.tag k)) ∧
          (∀ α : MulAut (adjointGroup TwistTag.E6.tag k), IsOrdinaryDiagGraph k α → α ^ 2 = 1 →
            (∃ φ : MulAut G, φ * MulAut.congr ψ α * φ⁻¹ = MulAut.congr ψ η) ∨
              ∃ φ : MulAut G, φ * MulAut.congr ψ α * φ⁻¹ =
                MulAut.congr ψ (MulAut.conj ⟨_, ht⟩ * η)) ∧
          ∀ φ : MulAut G,
            φ * MulAut.congr ψ η * φ⁻¹ ≠ MulAut.congr ψ (MulAut.conj ⟨_, ht⟩ * η) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  obtain ⟨ι⟩ := nonempty_ringHom_of_card hf hk hK
  let _ : Algebra k (GaloisField 2 (2 * f)) := ι.toAlgebra
  let σ : GaloisField 2 (2 * f) →+* GaloisField 2 (2 * f) := iterateFrobenius _ 2 f
  have hσ : ∀ c, σ c = c ^ 2 ^ f := fun c => iterateFrobenius_def 2 f c
  obtain ⟨⟨-, hPP, hPG, -, hexh, hfaith, ht, η, hη, -, hnc⟩, -⟩ :=
    even_E6_graph_inner_coset_exhaustion f hf k _ hk hK σ hσ
  have hinv : ∀ α : MulAut (adjointGroup TwistTag.E6.tag k), IsOrdinaryDiagGraph k α →
      α ^ 2 = 1 → (∃ φ : MulAut (adjointGroup TwistTag.E6.tag k), φ * α * φ⁻¹ = η) ∨
        ∃ φ : MulAut (adjointGroup TwistTag.E6.tag k), φ * α * φ⁻¹ = MulAut.conj ⟨_, ht⟩ * η := by
    rintro α ⟨g, a, hg, hα⟩ hα2
    have hd := (root_diagonal_conjugation TwistTag.E6.tag k a).2.2
    have hwm : (g * rootDiagUnit TwistTag.E6.tag a) ^ (2 ^ f - 1) ∈
        adjointGroup TwistTag.E6.tag k := by
      obtain ⟨c, hc, e⟩ := exists_mul_pow_eq hg hd (2 ^ f - 1)
      have ha : a ^ (2 ^ f - 1) = 1 := funext fun i => by
        rw [Pi.pow_apply, Pi.one_apply, ← hk, ← Nat.card_units k]
        exact pow_card_eq_one'
      rw [e, rootDiagUnit_pow, ha, rootDiagUnit_one, mul_one]
      exact hc
    exact conj_of_odd_diag hPP ht hη hexh hfaith (mul_mem (Subgroup.le_normalizer hg) hd)
      (odd_two_pow_sub_one hf) hwm hα hα2
  refine ⟨ht, η, hη, hinv, fun Θ hΘ => isOrdinaryDiagGraph_iff k Θ hΘ, hnc, fun G _ e => ?_⟩
  have hZ : Subgroup.center (adjointGroup TwistTag.E6.tag k) = ⊥ := center_adjointGroup_eq_bot
  let ψ₀ : adjointGroup TwistTag.E6.tag k ≃* AdjointQuotient TwistTag.E6.tag k :=
    MulEquiv.ofBijective (QuotientGroup.mk' _)
      ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk', hZ]),
        QuotientGroup.mk'_surjective _⟩
  refine ⟨ψ₀.trans e.symm, fun c => by rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]; rfl,
    fun α hα hα2 => ?_, transport_not_conj _ hnc⟩
  rcases hinv α hα hα2 with h | h
  · exact Or.inl (transport_conj _ h)
  · exact Or.inr (transport_conj _ h)

theorem twisted_full
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ (ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 K σ)
      (η : MulAut (graphFixedRootGroup TwistTag.E6 K σ)),
      (∀ h : graphFixedRootGroup TwistTag.E6 K σ, (η h : ModGL TwistTag.E6.tag K) =
        diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) ∧
      (∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ), IsTwistedDiagGraph K σ α →
        α ^ 2 = 1 → (∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ), φ * α * φ⁻¹ = η) ∨
          ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
            φ * α * φ⁻¹ = MulAut.conj ⟨_, ht⟩ * η) ∧
      (∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ), α ^ 2 = 1 →
        ((∀ c, α ≠ MulAut.conj c) ↔ IsTwistedDiagGraph K σ α)) ∧
      (∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ), α ^ 2 = 1 →
        (∀ c, α ≠ MulAut.conj c) →
        (∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ), φ * α * φ⁻¹ = η) ∨
          ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
            φ * α * φ⁻¹ = MulAut.conj ⟨_, ht⟩ * η) ∧
      (∀ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
        φ * η * φ⁻¹ ≠ MulAut.conj ⟨_, ht⟩ * η) ∧
      ∀ (G : Type) [Group G]
        (e : G ≃* DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σ)),
        ∃ ψ : graphFixedRootGroup TwistTag.E6 K σ ≃* G,
          (∀ (c : graphFixedRootGroup TwistTag.E6 K σ) (hc : (c : ModGL TwistTag.E6.tag K) ∈
              ⁅twistedFixedGroup TwistTag.E6 K σ, twistedFixedGroup TwistTag.E6 K σ⁆),
            e (ψ c) = QuotientGroup.mk ⟨c, hc⟩) ∧
          (∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ), IsTwistedDiagGraph K σ α →
            α ^ 2 = 1 → (∃ φ : MulAut G, φ * MulAut.congr ψ α * φ⁻¹ = MulAut.congr ψ η) ∨
              ∃ φ : MulAut G, φ * MulAut.congr ψ α * φ⁻¹ =
                MulAut.congr ψ (MulAut.conj ⟨_, ht⟩ * η)) ∧
          (∀ α : MulAut G, α ^ 2 = 1 → (∀ c, α ≠ MulAut.conj c) →
            (∃ φ : MulAut G, φ * α * φ⁻¹ = MulAut.congr ψ η) ∨
              ∃ φ : MulAut G, φ * α * φ⁻¹ = MulAut.congr ψ (MulAut.conj ⟨_, ht⟩ * η)) ∧
          ∀ φ : MulAut G,
            φ * MulAut.congr ψ η * φ⁻¹ ≠ MulAut.congr ψ (MulAut.conj ⟨_, ht⟩ * η) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨σE, rfl⟩ : ∃ σE : K ≃+* K, σE.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
      RingHom.ext fun _ => rfl⟩
  have hσ' : ∀ c, σE c = c ^ 2 ^ f := hσ
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ι⟩ := nonempty_ringHom_of_card hf hk hK
  let _ : Algebra (GaloisField 2 f) K := ι.toAlgebra
  obtain ⟨-, ⟨-, hPP, hPG, -, hexh, hfaith, ht, η, hη, -, hnc⟩⟩ :=
    even_E6_graph_inner_coset_exhaustion f hf (GaloisField 2 f) K hk hK σE.toRingHom hσ
  have : CharP K 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (two_eq_zero_of_card_sq hf hK)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hcoe, -, -, ⟨Θ, hΘ, -, -, -, -, hinvNF⟩, hfP, hperf, hZ, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σE hσ'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hmem3, -⟩ :=
    twisted_E6_all_characteristic_compatible_diagonal_cubes Nat.prime_two K hK σE hσ'
  have hσ1 : σE ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
      (p := 2) (f := f) hK).exists_ne
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← hσ', h1] at hc
    exact hc rfl
  have hinv : ∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σE.toRingHom),
      IsTwistedDiagGraph K σE.toRingHom α → α ^ 2 = 1 →
      (∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σE.toRingHom), φ * α * φ⁻¹ = η) ∨
        ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σE.toRingHom),
          φ * α * φ⁻¹ = MulAut.conj ⟨_, ht⟩ * η := by
    rintro α ⟨g, u, hg, hα⟩ hα2
    have hd := rootDiagUnit_mem_normalizer_graphFixedRootGroup (σ := σE.toRingHom)
      (compatDiag_perm u)
    have hwm : (g * rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σE.toRingHom u)) ^ 3 ∈
        graphFixedRootGroup TwistTag.E6 K σE.toRingHom := by
      obtain ⟨c, hc, e⟩ := exists_mul_pow_eq hg hd 3
      rw [e]
      exact mul_mem hc (hmem3 u)
    exact conj_of_odd_diag hPP ht hη hexh hfaith (mul_mem (Subgroup.le_normalizer hg) hd)
      (by decide) hwm hα hα2
  have hform : ∀ (α : MulAut (graphFixedRootGroup TwistTag.E6 K σE.toRingHom))
      (g : graphFixedRootGroup TwistTag.E6 K σE.toRingHom) u,
      α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σE.toRingHom u * fieldActor σE σE ↔
        ∀ h : graphFixedRootGroup TwistTag.E6 K σE.toRingHom,
          (α h : ModGL TwistTag.E6.tag K) =
            g * rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σE.toRingHom u) *
              (diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) *
                (g * rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σE.toRingHom u))⁻¹ := by
    intro α g u
    have e : ∀ h : graphFixedRootGroup TwistTag.E6 K σE.toRingHom,
        (((MulAut.conj g * compatDiagAutHom TwistTag.E6 K σE.toRingHom u * fieldActor σE σE :
          MulAut (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)) h :
            graphFixedRootGroup TwistTag.E6 K σE.toRingHom) : ModGL TwistTag.E6.tag K) =
            g * rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σE.toRingHom u) *
              (diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) *
                (g * rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σE.toRingHom u))⁻¹ := by
      intro h
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_inv, hcoe, hfP]
      group
    constructor
    · rintro rfl
      exact e
    · intro hα
      exact MulEquiv.ext fun h => Subtype.ext ((hα h).trans (e h).symm)
  have hnon : ∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σE.toRingHom), α ^ 2 = 1 →
      ((∀ c, α ≠ MulAut.conj c) ↔ IsTwistedDiagGraph K σE.toRingHom α) := by
    intro α hα2
    constructor
    · intro hα
      rcases hinvNF α hα2 with ⟨c, hc⟩ | ⟨-, g, u, hgu⟩
      · exact absurd hc.symm (hα c)
      · exact ⟨g, u, g.2, (hform α g u).1 hgu⟩
    · rintro ⟨g, u, hg, hα⟩ c rfl
      have h1 := hΘ _ ⟨g, hg⟩ u σE ((hform _ ⟨g, hg⟩ u).2 hα)
      have h2 := hΘ (MulAut.conj c) c 1 1 (by rw [map_one, fieldActor_one, mul_one, mul_one])
      exact hσ1 (h1.symm.trans h2)
  have hclass : ∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σE.toRingHom), α ^ 2 = 1 →
      (∀ c, α ≠ MulAut.conj c) →
      (∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σE.toRingHom), φ * α * φ⁻¹ = η) ∨
        ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σE.toRingHom),
          φ * α * φ⁻¹ = MulAut.conj ⟨_, ht⟩ * η := fun α hα2 hα =>
    hinv α ((hnon α hα2).1 hα) hα2
  refine ⟨ht, η, hη, hinv, hnon, hclass, hnc, fun G _ e => ?_⟩
  let ε : ↥⁅twistedFixedGroup TwistTag.E6 K σE.toRingHom,
      twistedFixedGroup TwistTag.E6 K σE.toRingHom⁆ ≃*
        graphFixedRootGroup TwistTag.E6 K σE.toRingHom :=
    MulEquiv.subgroupCongr hperf
  have hZ' : Subgroup.center ↥⁅twistedFixedGroup TwistTag.E6 K σE.toRingHom,
      twistedFixedGroup TwistTag.E6 K σE.toRingHom⁆ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hεx : ε x ∈ Subgroup.center (graphFixedRootGroup TwistTag.E6 K σE.toRingHom) :=
      Subgroup.mem_center_iff.2 fun y => by
        obtain ⟨y', rfl⟩ := ε.surjective y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y']
    rw [hZ, Subgroup.mem_bot] at hεx
    exact Subgroup.mem_bot.2 (ε.injective (hεx.trans (map_one ε).symm))
  let ψ₀ : graphFixedRootGroup TwistTag.E6 K σE.toRingHom ≃*
      DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σE.toRingHom) :=
    ε.symm.trans (MulEquiv.ofBijective (QuotientGroup.mk' _)
      ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk', hZ']),
        QuotientGroup.mk'_surjective _⟩)
  refine ⟨ψ₀.trans e.symm, fun c hc => ?_, fun α hα hα2 => ?_, fun α hα2 hα => ?_,
    transport_not_conj _ hnc⟩
  · rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  · rcases hinv α hα hα2 with h | h
    · exact Or.inl (transport_conj _ h)
    · exact Or.inr (transport_conj _ h)
  · set Φ := MulAut.congr (ψ₀.trans e.symm)
    have h2 : (Φ.symm α) ^ 2 = 1 := by rw [← map_pow, hα2, map_one]
    have hn : ∀ c, Φ.symm α ≠ MulAut.conj c := fun c hc => by
      apply hα ((ψ₀.trans e.symm) c)
      rw [← congr_conj, ← hc, MulEquiv.apply_symm_apply]
    rcases hclass _ h2 hn with h | h
    · have := transport_conj (ψ₀.trans e.symm) h
      rw [MulEquiv.apply_symm_apply] at this
      exact Or.inl this
    · have := transport_conj (ψ₀.trans e.symm) h
      rw [MulEquiv.apply_symm_apply] at this
      exact Or.inr this


theorem _root_.CFSG.LieType.Chevalley.even_E6_graph_full_inner_diagonal_coset_exhaustion
    (f : ℕ) (hf : 1 ≤ f) :
    (∀ (k : Type) [Field k], Nat.card k = 2 ^ f →
      ∃ (ht : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag k)
        (η : MulAut (adjointGroup TwistTag.E6.tag k)),
        (∀ h : adjointGroup TwistTag.E6.tag k, (η h : ModGL TwistTag.E6.tag k) =
          diagramMap TwistTag.E6 k * h * (diagramMap TwistTag.E6 k)⁻¹) ∧
        (∀ α : MulAut (adjointGroup TwistTag.E6.tag k), IsOrdinaryDiagGraph k α → α ^ 2 = 1 →
          (∃ φ : MulAut (adjointGroup TwistTag.E6.tag k), φ * α * φ⁻¹ = η) ∨
            ∃ φ : MulAut (adjointGroup TwistTag.E6.tag k), φ * α * φ⁻¹ = MulAut.conj ⟨_, ht⟩ * η) ∧
        (∀ Θ : MulAut (adjointGroup TwistTag.E6.tag k) →*
            RingAut k × Multiplicative (ZMod (exactE TwistTag.E6.tag)),
          (∀ (α : MulAut (adjointGroup TwistTag.E6.tag k)) (g : adjointGroup TwistTag.E6.tag k)
            (a : Fin TwistTag.E6.tag.rank → kˣ) (σ : k ≃+* k) (ε : Fin (exactE TwistTag.E6.tag)),
            (∀ h : adjointGroup TwistTag.E6.tag k, (α h : ModGL TwistTag.E6.tag k) =
              (g : ModGL TwistTag.E6.tag k) * rootDiagUnit TwistTag.E6.tag a *
                exactQ TwistTag.E6.tag k ε * Units.map (entrywiseHom σ.toRingHom)
                  (h : ModGL TwistTag.E6.tag k) * (exactQ TwistTag.E6.tag k ε)⁻¹ *
                    (rootDiagUnit TwistTag.E6.tag a)⁻¹ * (g : ModGL TwistTag.E6.tag k)⁻¹) →
            Θ α = (σ, Multiplicative.ofAdd ((ε : ℕ) : ZMod (exactE TwistTag.E6.tag)))) →
          ∀ α : MulAut (adjointGroup TwistTag.E6.tag k),
            IsOrdinaryDiagGraph k α ↔ Θ α = (1, Multiplicative.ofAdd 1)) ∧
        (∀ φ : MulAut (adjointGroup TwistTag.E6.tag k), φ * η * φ⁻¹ ≠ MulAut.conj ⟨_, ht⟩ * η) ∧
        ∀ (G : Type) [Group G] (e : G ≃* AdjointQuotient TwistTag.E6.tag k),
          ∃ ψ : adjointGroup TwistTag.E6.tag k ≃* G,
            (∀ c, e (ψ c) = (QuotientGroup.mk c : AdjointQuotient TwistTag.E6.tag k)) ∧
            (∀ α : MulAut (adjointGroup TwistTag.E6.tag k), IsOrdinaryDiagGraph k α → α ^ 2 = 1 →
              (∃ φ : MulAut G, φ * MulAut.congr ψ α * φ⁻¹ = MulAut.congr ψ η) ∨
                ∃ φ : MulAut G, φ * MulAut.congr ψ α * φ⁻¹ =
                  MulAut.congr ψ (MulAut.conj ⟨_, ht⟩ * η)) ∧
            ∀ φ : MulAut G,
              φ * MulAut.congr ψ η * φ⁻¹ ≠ MulAut.congr ψ (MulAut.conj ⟨_, ht⟩ * η)) ∧
    (∀ (K : Type) [Field K], Nat.card K = (2 ^ f) ^ 2 → ∀ σ : K →+* K, (∀ c, σ c = c ^ 2 ^ f) →
      ∃ (ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 K σ)
        (η : MulAut (graphFixedRootGroup TwistTag.E6 K σ)),
        (∀ h : graphFixedRootGroup TwistTag.E6 K σ, (η h : ModGL TwistTag.E6.tag K) =
          diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) ∧
        (∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ), IsTwistedDiagGraph K σ α →
          α ^ 2 = 1 → (∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ), φ * α * φ⁻¹ = η) ∨
            ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
              φ * α * φ⁻¹ = MulAut.conj ⟨_, ht⟩ * η) ∧
        (∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ), α ^ 2 = 1 →
          ((∀ c, α ≠ MulAut.conj c) ↔ IsTwistedDiagGraph K σ α)) ∧
        (∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ), α ^ 2 = 1 →
          (∀ c, α ≠ MulAut.conj c) →
          (∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ), φ * α * φ⁻¹ = η) ∨
            ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
              φ * α * φ⁻¹ = MulAut.conj ⟨_, ht⟩ * η) ∧
        (∀ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
          φ * η * φ⁻¹ ≠ MulAut.conj ⟨_, ht⟩ * η) ∧
        ∀ (G : Type) [Group G]
          (e : G ≃* DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σ)),
          ∃ ψ : graphFixedRootGroup TwistTag.E6 K σ ≃* G,
            (∀ (c : graphFixedRootGroup TwistTag.E6 K σ) (hc : (c : ModGL TwistTag.E6.tag K) ∈
                ⁅twistedFixedGroup TwistTag.E6 K σ, twistedFixedGroup TwistTag.E6 K σ⁆),
              e (ψ c) = QuotientGroup.mk ⟨c, hc⟩) ∧
            (∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ), IsTwistedDiagGraph K σ α →
              α ^ 2 = 1 → (∃ φ : MulAut G, φ * MulAut.congr ψ α * φ⁻¹ = MulAut.congr ψ η) ∨
                ∃ φ : MulAut G, φ * MulAut.congr ψ α * φ⁻¹ =
                  MulAut.congr ψ (MulAut.conj ⟨_, ht⟩ * η)) ∧
            (∀ α : MulAut G, α ^ 2 = 1 → (∀ c, α ≠ MulAut.conj c) →
              (∃ φ : MulAut G, φ * α * φ⁻¹ = MulAut.congr ψ η) ∨
                ∃ φ : MulAut G, φ * α * φ⁻¹ = MulAut.congr ψ (MulAut.conj ⟨_, ht⟩ * η)) ∧
            ∀ φ : MulAut G,
              φ * MulAut.congr ψ η * φ⁻¹ ≠ MulAut.congr ψ (MulAut.conj ⟨_, ht⟩ * η)) :=
  ⟨fun k _ hk => ordinary_full hf k hk, fun K _ hK σ hσ => twisted_full hf K hK σ hσ⟩

end CFSG.LieType.Chevalley.E6GraphFullCoset
