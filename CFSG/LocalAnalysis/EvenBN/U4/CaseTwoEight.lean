module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseTwoSeven

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_inf
  mem_normalizer_sup card_sup_mul_card_inf_eq)
open scoped MatrixGroups Pointwise commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem commutator_mem_of_simple {X Y Z : Subgroup G} [IsSimpleGroup X]
    (hYZ : Y ≤ normalizer (Z : Set G)) (hXY : X ≤ normalizer (Y : Set G))
    (hXZ : X ≤ normalizer (Z : Set G)) {x₀ : G} (hx₀ : x₀ ∈ X) (hx₀1 : x₀ ≠ 1)
    (hx₀c : ∀ y ∈ Y, x₀ * y * x₀⁻¹ * y⁻¹ ∈ Z) {x y : G} (hx : x ∈ X) (hy : y ∈ Y) :
    x * y * x⁻¹ * y⁻¹ ∈ Z := by
  set Z' : Subgroup Y := Z.subgroupOf Y with hZ'
  have hZ'n : Z'.Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp (hYZ g.2) n).mp (Subgroup.mem_subgroupOf.mp hn))⟩
  set ρY := CFSG.SL2MinimalFaithful.conjAction hXY
  have hmap : ∀ j, Z'.map (ρY j : Y →* Y) = Z' := by
    intro j
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      change (j : G) * z * (j : G)⁻¹ ∈ Z
      exact (Subgroup.mem_normalizer_iff.mp (hXZ j.2) z).mp hz
    · intro z hz
      refine ⟨ρY j⁻¹ z, ?_, ?_⟩
      · change ((j⁻¹ : X) : G) * z * ((j⁻¹ : X) : G)⁻¹ ∈ Z
        exact (Subgroup.mem_normalizer_iff.mp (hXZ (X.inv_mem j.2)) z).mp hz
      · change ρY j (ρY j⁻¹ z) = z
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  set ρ := CFSG.SL2MinimalFaithful.quotientAction ρY Z' hmap
  have hker : (⟨x₀, hx₀⟩ : X) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    ext v
    induction v using QuotientGroup.induction_on with
    | H v =>
      rw [CFSG.SL2MinimalFaithful.quotientAction_mk, MulAut.one_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      change (ρY ⟨x₀, hx₀⟩ v : G)⁻¹ * v ∈ Z
      rw [CFSG.SL2MinimalFaithful.conjAction_apply]
      show (x₀ * (v : G) * x₀⁻¹)⁻¹ * v ∈ Z
      have h1 := hx₀c v v.2
      have h3 := (Subgroup.mem_normalizer_iff.mp (hYZ (inv_mem v.2)) _).mp (inv_mem h1)
      rw [inv_inv] at h3
      convert h3 using 1
      group
  have htop : ρ.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with hb | ht
    · exfalso
      have h0 : (⟨x₀, hx₀⟩ : X) ∈ (⊥ : Subgroup X) := hb ▸ hker
      rw [mem_bot] at h0
      exact hx₀1 (congrArg Subtype.val h0)
    · exact ht
  have h2 : ρ ⟨x, hx⟩ ((⟨y, hy⟩ : Y) : Y ⧸ Z') = ((⟨y, hy⟩ : Y) : Y ⧸ Z') := by
    have hk : (⟨x, hx⟩ : X) ∈ ρ.ker := htop ▸ mem_top _
    rw [(MonoidHom.mem_ker).1 hk, MulAut.one_apply]
  rw [CFSG.SL2MinimalFaithful.quotientAction_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    at h2
  change (ρY ⟨x, hx⟩ ⟨y, hy⟩ : G)⁻¹ * y ∈ Z at h2
  rw [CFSG.SL2MinimalFaithful.conjAction_apply] at h2
  exact (CFSG.SL2MinimalFaithful.inv_mul_mem_iff hYZ hy).1 h2

theorem le_centralizer_of_simple_of_perfect {X Ω E : Subgroup G} [IsSimpleGroup X]
    (hperf : ⁅X, X⁆ = X) (hΩE : Ω ≤ normalizer (E : Set G)) (hXΩ : X ≤ normalizer (Ω : Set G))
    (hXE : X ≤ centralizer (E : Set G)) {x₀ : G} (hx₀ : x₀ ∈ X) (hx₀1 : x₀ ≠ 1)
    (hx₀c : ∀ y ∈ Ω, x₀ * y * x₀⁻¹ * y⁻¹ ∈ E) : X ≤ centralizer (Ω : Set G) := by
  have hXE' : X ≤ normalizer (E : Set G) := fun x hx => mem_normalizer_of_mem_centralizer'
    (hXE hx)
  have hq : ∀ x ∈ X, ∀ y ∈ Ω, x * y * x⁻¹ * y⁻¹ ∈ E := fun x hx y hy =>
    commutator_mem_of_simple hΩE hXΩ hXE' hx₀ hx₀1 hx₀c hx hy
  have hΩX : ⁅Ω, X⁆ ≤ E := by
    rw [commutator_le]
    intro y hy x hx
    have h1 := hq x hx y⁻¹ (inv_mem hy)
    have h2 := (mem_normalizer_iff.1 (hΩE hy) _).1 h1
    rw [commutatorElement_def]
    convert h2 using 1
    group
  have hEX : ⁅E, X⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.2 (le_centralizer_iff.1 hXE)
  have h1 : ⁅⁅Ω, X⁆, X⁆ = ⊥ := eq_bot_iff.2 (hEX ▸ commutator_mono hΩX le_rfl)
  have h2 : ⁅⁅X, Ω⁆, X⁆ = ⊥ := by rw [commutator_comm X Ω]; exact h1
  have h3 := commutator_commutator_eq_bot_of_rotate h2 h1
  rw [hperf] at h3
  exact commutator_eq_bot_iff_le_centralizer.1 h3

end Generic

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

local notation "𝓥" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

local notation "𝓤" => miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)

local notation "𝓨" => CFSG.centerIn 𝓤 ⊓
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (miyamotoR1G h L η))) (CFSG.centerIn 𝓤)

local notation "𝓨t" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓨

local notation "𝓚" => 𝓨t ⊔ prodFactorOne ψ

local notation "𝓦'" => miyamotoRG h L η t Q ⊓ 𝓚

local notation "𝓦'ᵗ" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓦'

theorem prodFactor_M2_simple_perfect (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂]
    [Fintype k₂] (hk₂ : Fintype.card k₂ = 2 ^ f)
    (ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)) :
    IsSimpleGroup (prodFactorTwo ψ₂) ∧ ⁅prodFactorTwo ψ₂, prodFactorTwo ψ₂⁆ = prodFactorTwo ψ₂ ∧
      IsSimpleGroup (prodFactorOne ψ₂) ∧
      ⁅prodFactorOne ψ₂, prodFactorOne ψ₂⁆ = prodFactorOne ψ₂ := by
  have : CharP k₂ 2 := charP_of_card_eq_prime_pow (f := f) hk₂
  have h4 : 4 ≤ Nat.card k₂ := by rw [Nat.card_eq_fintype_card, hk₂]; exact hS.four_le
  have : IsSimpleGroup SL(2, k₂) := Common.sl2_isSimpleGroup_of_charTwo h4
  have hP : Group.IsPerfect SL(2, k₂) :=
    LinearGroups.special_linear_dimension_two_perfect (Common.exists_finset_card_four h4)
  refine ⟨(Common.prodFactorTwoEquiv ψ₂).isSimpleGroup, ?_,
    (Common.prodFactorOneEquiv ψ₂).isSimpleGroup, ?_⟩
  · have : Group.IsPerfect (prodFactorTwo ψ₂) :=
      Group.IsPerfect.ofSurjective (f := (Common.prodFactorTwoEquiv ψ₂).symm.toMonoidHom)
        (Common.prodFactorTwoEquiv ψ₂).symm.surjective
    exact Subgroup.isPerfect_iff.1 this
  · have : Group.IsPerfect (prodFactorOne ψ₂) :=
      Group.IsPerfect.ofSurjective (f := (Common.prodFactorOneEquiv ψ₂).symm.toMonoidHom)
        (Common.prodFactorOneEquiv ψ₂).symm.surjective
    exact Subgroup.isPerfect_iff.1 this

theorem V2_inf_W'_eq [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {k₂ : Type} [Field k₂] [Fintype k₂] (hk₂ : Fintype.card k₂ = 2 ^ f)
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)} {α₂ : miyamotoN2G h L η ≃* SL(2, k₂)}
    (hψα₂ : ∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
      ψ₂ x = (α₂ a, α₂ a))
    {j : G} (hj : j ∈ miyamotoJ2G h L η t Q) (hj1 : j ≠ 1)
    (hjC : j ∈ centralizer ((𝓚 : Subgroup G) : Set G)) (hjY : j ∈ prodFactorTwo ψ₂) :
    𝓥 ⊓ 𝓦' = 𝓥 ⊓ prodFactorOne ψ₂ := by
  obtain ⟨hV, h1, -⟩ := hS.V2_eq_sup_Y hk₂ ψ₂
  have hjM : j ∈ miyamotoM2G h L η t Q := (mem_inf.1 hj).1
  have hψj : (ψ₂ ⟨j, hjM⟩).2 ≠ 1 := by
    intro e
    obtain ⟨hjM', hj2⟩ := (Common.mem_prodFactorTwo_iff ψ₂).1 hjY
    have hψ : ψ₂ ⟨j, hjM⟩ = 1 := Prod.ext hj2 e
    rw [← map_one ψ₂] at hψ
    exact hj1 (congrArg Subtype.val (ψ₂.injective hψ))
  have hfp := hS.V2_inf_Y2_inf_centralizer hk₂ hψα₂ hj hψj
  have hle : 𝓥 ⊓ 𝓦' ≤ 𝓥 ⊓ prodFactorOne ψ₂ := by
    intro v hv
    have hvV : v ∈ (𝓥 ⊓ prodFactorOne ψ₂) ⊔ (𝓥 ⊓ prodFactorTwo ψ₂) := hV ▸ (mem_inf.1 hv).1
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun x hx y hy => (mem_centralizer_iff.1 (Common.prodFactorTwo_le_centralizer ψ₂
        (mem_inf.1 hy).2) x (mem_inf.1 hx).2)) hvV
    have hvj : s₁ * s₂ * j = j * (s₁ * s₂) :=
      mem_centralizer_iff.1 hjC _ (mem_inf.1 (mem_inf.1 hv).2).2
    have hs₁j : s₁ * j = j * s₁ := mem_centralizer_iff.1
      (Common.prodFactorTwo_le_centralizer ψ₂ hjY) s₁ (mem_inf.1 hs₁).2
    have hs₂j : s₂ * j = j * s₂ := by
      calc s₂ * j = s₁⁻¹ * (s₁ * s₂ * j) := by group
        _ = s₁⁻¹ * (j * (s₁ * s₂)) := by rw [hvj]
        _ = s₁⁻¹ * (j * s₁) * s₂ := by group
        _ = s₁⁻¹ * (s₁ * j) * s₂ := by rw [hs₁j]
        _ = j * s₂ := by group
    have hs₂1 : s₂ = 1 := by
      have : s₂ ∈ (𝓥 ⊓ prodFactorTwo ψ₂) ⊓ centralizer ({j} : Set G) :=
        mem_inf.2 ⟨hs₂, mem_centralizer_singleton_iff.2 hs₂j⟩
      rwa [hfp, mem_bot] at this
    rw [hs₂1, mul_one]
    exact hs₁
  refine eq_of_le_of_card_ge hle ?_
  rw [h1]
  obtain ⟨-, hC, hinf, -, -⟩ := hS.sec5_2_one hk hψA hψt hZ
  have hVW := hS.V2_eq_sup_W' hk hψA hψt hZ
  have hN : 𝓥 ⊓ 𝓦'ᵗ ≤ normalizer ((𝓥 ⊓ 𝓦' : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_of_mem_centralizer' (centralizer_le (SetLike.coe_subset_coe.2 inf_le_right)
      (hC (mem_inf.1 hy).2))
  have h2 := card_sup_mul_card_inf_eq hN
  have hinf2 : (𝓥 ⊓ 𝓦') ⊓ (𝓥 ⊓ 𝓦'ᵗ) = ⊥ :=
    eq_bot_iff.2 (hinf ▸ inf_le_inf inf_le_right inf_le_right)
  have htV : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) (𝓥 : Subgroup G) = 𝓥 :=
    mem_normalizer_iff_map_conj_eq.1 hS.t_mem_normalizer_V2
  have e : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) (𝓥 ⊓ 𝓦') = 𝓥 ⊓ 𝓦'ᵗ := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective, htV]
  have hcardt : Nat.card (𝓥 ⊓ 𝓦'ᵗ : Subgroup G) = Nat.card (𝓥 ⊓ 𝓦' : Subgroup G) := by
    rw [← e, card_map_of_injective (MulAut.conj t).injective]
  rw [hinf2, card_bot, mul_one, ← hVW, hS.card_V2, hcardt] at h2
  have h3 : (2 ^ f) ^ 2 = 2 ^ f * 2 ^ f := sq _
  rw [h3] at h2
  exact (Nat.mul_self_inj.1 h2).le

theorem W'_eq_sup [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {k₂ : Type} [Field k₂] [Fintype k₂] (hk₂ : Fintype.card k₂ = 2 ^ f)
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)} {α₂ : miyamotoN2G h L η ≃* SL(2, k₂)}
    (hψα₂ : ∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
      ψ₂ x = (α₂ a, α₂ a))
    {j : G} (hj : j ∈ miyamotoJ2G h L η t Q) (hj1 : j ≠ 1)
    (hjC : j ∈ centralizer ((𝓚 : Subgroup G) : Set G)) (hjY : j ∈ prodFactorTwo ψ₂) :
    𝓦' = (𝓦' ⊓ miyamotoF2G h L η t Q) ⊔ (𝓥 ⊓ prodFactorOne ψ₂) := by
  have hSW := hS.V2_inf_W'_eq hk hψA hψt hZ hk₂ hψα₂ hj hj1 hjC hjY
  obtain ⟨-, h1, -⟩ := hS.V2_eq_sup_Y hk₂ ψ₂
  have hle : (𝓦' ⊓ miyamotoF2G h L η t Q) ⊔ (𝓥 ⊓ prodFactorOne ψ₂) ≤ 𝓦' :=
    sup_le inf_le_left (hSW ▸ inf_le_right)
  refine (eq_of_le_of_card_ge hle ?_).symm
  have hN : 𝓥 ⊓ prodFactorOne ψ₂ ≤
      normalizer ((𝓦' ⊓ miyamotoF2G h L η t Q : Subgroup G) : Set G) := by
    intro x hx
    have hx' : x ∈ 𝓥 ⊓ 𝓦' := by rw [hSW]; exact hx
    exact mem_normalizer_inf (le_normalizer (mem_inf.1 hx').2)
      (hS.RG_le_normalizer_F2 (mem_inf.1 (mem_inf.1 hx).1).1)
  have h2 := card_sup_mul_card_inf_eq hN
  have hinf : (𝓦' ⊓ miyamotoF2G h L η t Q) ⊓ (𝓥 ⊓ prodFactorOne ψ₂) = ⊥ := by
    rw [eq_bot_iff, ← hS.F2_inf_centralizer_I2]
    exact inf_le_inf inf_le_right (inf_le_left.trans inf_le_right)
  rw [hinf, card_bot, mul_one, (hS.sec5_2_two hk hψA hψt hZ).2.2, h1] at h2
  rw [h2, (hS.sec5_2_one hk hψA hψt hZ).2.2.2.2]
  ring_nf
  exact le_rfl

theorem mem_W2E_of_commutator [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) {x : G}
    (hx : x ∈ miyamotoF2G h L η t Q)
    (hc : ∀ y ∈ miyamotoF2G h L η t Q, x * y * x⁻¹ * y⁻¹ ∈ miyamotoEG h L η Q ⊓ 𝓦') :
    x ∈ (𝓦' ⊓ miyamotoF2G h L η t Q) ⊔ miyamotoEG h L η Q := by
  obtain ⟨-, hC, hinf, -, -⟩ := hS.sec5_2_one hk hψA hψt hZ
  obtain ⟨hW2t, hF2, -⟩ := hS.sec5_2_two hk hψA hψt hZ
  have hcomm : ∀ a ∈ 𝓦' ⊓ miyamotoF2G h L η t Q, ∀ b ∈ 𝓦'ᵗ ⊓ miyamotoF2G h L η t Q,
      a * b = b * a := fun a ha b hb => mem_centralizer_iff.1 (hC (mem_inf.1 hb).1) a
        (mem_inf.1 ha).1
  rw [hF2] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hx
  have hbd : ∀ d ∈ 𝓦'ᵗ ⊓ miyamotoF2G h L η t Q, b * d = d * b := by
    intro d hd
    have hdF : d ∈ miyamotoF2G h L η t Q := (mem_inf.1 hd).2
    have h1 := hc d hdF
    have e : a * b * d * (a * b)⁻¹ * d⁻¹ = b * d * b⁻¹ * d⁻¹ := by
      have h2 : a * (b * d * b⁻¹) = (b * d * b⁻¹) * a := hcomm a ha _
        (mem_inf.2 ⟨mul_mem (mul_mem (mem_inf.1 hb).1 (mem_inf.1 hd).1)
          (inv_mem (mem_inf.1 hb).1), mul_mem (mul_mem (mem_inf.1 hb).2 hdF)
          (inv_mem (mem_inf.1 hb).2)⟩)
      calc a * b * d * (a * b)⁻¹ * d⁻¹ = a * (b * d * b⁻¹) * a⁻¹ * d⁻¹ := by group
        _ = (b * d * b⁻¹) * a * a⁻¹ * d⁻¹ := by rw [h2]
        _ = b * d * b⁻¹ * d⁻¹ := by group
    rw [e] at h1
    have h3 : b * d * b⁻¹ * d⁻¹ ∈ 𝓦' ⊓ 𝓦'ᵗ := mem_inf.2 ⟨(mem_inf.1 h1).2,
      mul_mem (mul_mem (mul_mem (mem_inf.1 hb).1 (mem_inf.1 hd).1) (inv_mem (mem_inf.1 hb).1))
        (inv_mem (mem_inf.1 hd).1)⟩
    rw [hinf, mem_bot] at h3
    calc b * d = b * d * b⁻¹ * d⁻¹ * (d * b) := by group
      _ = d * b := by rw [h3, one_mul]
  have hbE : b ∈ miyamotoEG h L η Q := by
    rw [← hS.centerIn_F2]
    refine mem_inf.2 ⟨(mem_inf.1 hb).2, mem_centralizer_iff.2 fun y hy => ?_⟩
    rw [hF2] at hy
    obtain ⟨c, hc', d, hd, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hy
    calc c * d * b = c * (d * b) := mul_assoc _ _ _
      _ = c * (b * d) := by rw [hbd d hd]
      _ = (c * b) * d := (mul_assoc _ _ _).symm
      _ = (b * c) * d := by rw [hcomm c hc' b hb]
      _ = b * (c * d) := mul_assoc _ _ _
  exact mul_mem (mem_sup_left ha) (mem_sup_right hbE)

theorem M2_le_normalizer_W2E [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    miyamotoM2G h L η t Q ≤ normalizer
      (((𝓦' ⊓ miyamotoF2G h L η t Q) ⊔ miyamotoEG h L η Q : Subgroup G) : Set G) := by
  obtain ⟨-, hC, -, -, -⟩ := hS.sec5_2_one hk hψA hψt hZ
  obtain ⟨-, hF2, -⟩ := hS.sec5_2_two hk hψA hψt hZ
  have hEF2 : miyamotoEG h L η Q ≤ miyamotoF2G h L η t Q := hS.E_le_F.trans hS.F_le_F2
  have hΩF2 : (𝓦' ⊓ miyamotoF2G h L η t Q) ⊔ miyamotoEG h L η Q ≤ miyamotoF2G h L η t Q :=
    sup_le inf_le_right hEF2
  have hEc : ∀ e ∈ miyamotoEG h L η Q, ∀ y ∈ miyamotoF2G h L η t Q, e * y = y * e := by
    intro e he y hy
    rw [← hS.centerIn_F2] at he
    exact (mem_centralizer_iff.1 (mem_inf.1 he).2 y hy).symm
  have hcomm : ∀ x ∈ (𝓦' ⊓ miyamotoF2G h L η t Q) ⊔ miyamotoEG h L η Q,
      ∀ z ∈ miyamotoF2G h L η t Q, x * z * x⁻¹ * z⁻¹ ∈ miyamotoEG h L η Q ⊓ 𝓦' := by
    intro x hx z hz
    obtain ⟨w, hw, e, he, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => (hEc b hb a (mem_inf.1 ha).2).symm) hx
    have hez := hEc e he z hz
    have e1 : w * e * z * (w * e)⁻¹ * z⁻¹ = w * z * w⁻¹ * z⁻¹ := by
      calc w * e * z * (w * e)⁻¹ * z⁻¹ = w * (e * z) * e⁻¹ * w⁻¹ * z⁻¹ := by group
        _ = w * (z * e) * e⁻¹ * w⁻¹ * z⁻¹ := by rw [hez]
        _ = w * z * w⁻¹ * z⁻¹ := by group
    rw [e1]
    refine mem_inf.2 ⟨(hS.F2_mod_E).2 w (mem_inf.1 hw).2 z hz, ?_⟩
    rw [hF2] at hz
    obtain ⟨c, hc, d, hd, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => mem_centralizer_iff.1 (hC (mem_inf.1 hb).1) a (mem_inf.1 ha).1) hz
    have hwd : w * d = d * w := mem_centralizer_iff.1 (hC (mem_inf.1 hd).1) w (mem_inf.1 hw).1
    have e2 : w * (c * d) * w⁻¹ * (c * d)⁻¹ = w * c * w⁻¹ * c⁻¹ := by
      calc w * (c * d) * w⁻¹ * (c * d)⁻¹ = w * c * (d * w⁻¹) * d⁻¹ * c⁻¹ := by group
        _ = w * c * (w⁻¹ * d) * d⁻¹ * c⁻¹ := by
          rw [show d * w⁻¹ = w⁻¹ * d from (Commute.inv_right (hwd.symm : Commute d w)).eq]
        _ = w * c * w⁻¹ * c⁻¹ := by group
    rw [e2]
    exact mul_mem (mul_mem (mul_mem (mem_inf.1 hw).1 (mem_inf.1 hc).1) (inv_mem (mem_inf.1 hw).1))
      (inv_mem (mem_inf.1 hc).1)
  intro m hm
  refine mem_normalizer_of_conj_le fun x hx => ?_
  have hmF2 : m ∈ normalizer (miyamotoF2G h L η t Q : Set G) :=
    (hS.sec3_12_two.1.trans inf_le_left) hm
  have hmE : m ∈ centralizer (miyamotoEG h L η Q : Set G) := hS.M2G_le_centralizer_E hm
  refine hS.mem_W2E_of_commutator hk hψA hψt hZ ((mem_normalizer_iff.1 hmF2 x).1 (hΩF2 hx))
    fun y hy => ?_
  have hz : m⁻¹ * y * m ∈ miyamotoF2G h L η t Q := by
    have := (mem_normalizer_iff.1 (inv_mem hmF2) y).1 hy
    rwa [inv_inv] at this
  have h1 := hcomm x hx _ hz
  have e : m * x * m⁻¹ * y * (m * x * m⁻¹)⁻¹ * y⁻¹ =
      m * (x * (m⁻¹ * y * m) * x⁻¹ * (m⁻¹ * y * m)⁻¹) * m⁻¹ := by group
  rw [e]
  have hcm := mem_centralizer_iff.1 hmE _ (mem_inf.1 h1).1
  rw [← hcm, mul_inv_cancel_right]
  exact h1

theorem Y2_le_centralizer_W2E [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {k₂ : Type} [Field k₂] [Fintype k₂] (hk₂ : Fintype.card k₂ = 2 ^ f)
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)}
    {j : G} (hj : j ∈ miyamotoJ2G h L η t Q) (hj1 : j ≠ 1)
    (hjC : j ∈ centralizer ((𝓚 : Subgroup G) : Set G)) (hjY : j ∈ prodFactorTwo ψ₂) :
    prodFactorTwo ψ₂ ≤ centralizer
      (((𝓦' ⊓ miyamotoF2G h L η t Q) ⊔ miyamotoEG h L η Q : Subgroup G) : Set G) := by
  obtain ⟨hsimp, hperf, -, -⟩ := hS.prodFactor_M2_simple_perfect hk₂ ψ₂
  have hY2M : prodFactorTwo ψ₂ ≤ miyamotoM2G h L η t Q := Common.prodFactorTwo_le ψ₂
  have hEF2 : miyamotoEG h L η Q ≤ miyamotoF2G h L η t Q := hS.E_le_F.trans hS.F_le_F2
  have hΩE : (𝓦' ⊓ miyamotoF2G h L η t Q) ⊔ miyamotoEG h L η Q ≤
      normalizer (miyamotoEG h L η Q : Set G) := by
    refine sup_le (fun x hx => ?_) le_normalizer
    have : x ∈ centralizer (miyamotoEG h L η Q : Set G) := by
      rw [mem_centralizer_iff]
      intro e he
      rw [← hS.centerIn_F2] at he
      exact (mem_centralizer_iff.1 (mem_inf.1 he).2 x (mem_inf.1 hx).2).symm
    exact mem_normalizer_of_mem_centralizer' this
  have hjΩ : j ∈ centralizer
      (((𝓦' ⊓ miyamotoF2G h L η t Q) ⊔ miyamotoEG h L η Q : Subgroup G) : Set G) := by
    have hle : (𝓦' ⊓ miyamotoF2G h L η t Q) ⊔ miyamotoEG h L η Q ≤
        centralizer ({j} : Set G) := by
      refine sup_le (fun x hx => mem_centralizer_singleton_iff.2 ?_) (fun e he =>
        mem_centralizer_singleton_iff.2 ?_)
      · exact (mem_centralizer_iff.1 hjC x (mem_inf.1 (mem_inf.1 hx).1).2)
      · exact (mem_centralizer_iff.1 (hS.M2G_le_centralizer_E (mem_inf.1 hj).1) e he)
    exact mem_centralizer_iff.2 fun y hy => (mem_centralizer_singleton_iff.1 (hle hy))
  exact le_centralizer_of_simple_of_perfect hperf hΩE
    (hY2M.trans (hS.M2_le_normalizer_W2E hk hψA hψt hZ))
    (hY2M.trans hS.M2G_le_centralizer_E) hjY hj1 fun y hy => by
      rw [← mem_centralizer_iff.1 hjΩ y hy, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
