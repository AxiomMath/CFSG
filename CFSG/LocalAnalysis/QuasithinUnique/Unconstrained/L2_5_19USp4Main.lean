module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19USp4Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs

public section

namespace CFSG.QuasithinUnique.Id2519.USp4

open scoped commutatorElement

@[expose] def TabAutCentSp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
    K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)) →
    PatSp4 X K →
    ∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (X : Set G) → Y ≤ Subgroup.centralizer (K : Set G) →
      (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y ≤ 2

@[expose] def TabConjSp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
    K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)) →
    PatSp4 X K →
    ∀ u ∈ K, u * u = 1 → ∃ x ∈ X, x⁻¹ * t * x = t * u

section Model

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem sp4_model {G : Type} [Group G] {X K : Subgroup G} (hpat : PatSp4 X K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
      Nonempty (↥X ≃* StatedProj (StatedSp 2 F)) := by
  obtain ⟨-, -, F, hF, hFin, hcard, ⟨θ⟩⟩ := hpat
  have hch : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by norm_num) hcard
  exact ⟨F, hF, hFin, hch, by rw [hcard]; norm_num, ⟨θ⟩⟩

theorem center_eq_bot_of_equiv {F : Type} [Field F] [Finite F] [CharP F 2] {X : Type*} [Group X]
    (θ : X ≃* StatedProj (StatedSp 2 F)) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : θ z = 1 := by
    refine eq_one_of_central fun q => ?_
    obtain ⟨x, rfl⟩ := θ.surjective q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
  rw [Subgroup.mem_bot]
  exact θ.injective (by rw [h1, map_one])

end Model

section AutCent

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.QuasithinUnique.Id2519.Tab

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem tabAutCentSp4 : TabAutCentSp4 := by
  intro G _ _ X K t hXq ht ht2 hcomm hK hpat Y hYn hYc
  obtain ⟨F, _, _, _, hF, ⟨θ⟩⟩ := sp4_model hpat
  have hZ : Subgroup.center ↥X = ⊥ := center_eq_bot_of_equiv θ
  let π : ↥X →* StatedProj (StatedSp 2 F) := θ.toMonoidHom
  have hπ : Function.Surjective π := θ.surjective
  have hker : π.ker = Subgroup.center ↥X := by
    rw [hZ]
    exact (MonoidHom.ker_eq_bot_iff π).mpr θ.injective
  have hKle : K ≤ X ⊓ Subgroup.centralizer ({t} : Set G) :=
    hK.le.trans (perfectResidualOf_le _)
  have hKX : K ≤ X := hKle.trans inf_le_left
  have hKC : ∀ x ∈ K, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKle hx).2
  let Kb : Subgroup (StatedProj (StatedSp 2 F)) := (K.subgroupOf X).map π
  have hKb : Nat.card Kb = 360 := by
    obtain ⟨⟨e⟩, -⟩ := hpat
    have h1 : Nat.card Kb = Nat.card (K.subgroupOf X) :=
      Subgroup.card_map_of_injective θ.injective
    have h2 : Nat.card (K.subgroupOf X) = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv
    have h3 : Nat.card K = 360 := (Nat.card_congr e.toEquiv).trans card_alt_six
    rw [h1, h2, h3]
  have hτ2 := quotAct_mul_self π hπ hker ht ht2
  have hτ1 := quotAct_ne_one π hπ hker ht hXq hcomm
  have hτfix : quotAct π hπ hker ht ∈ pointwiseStab Kb := by
    rintro _ ⟨x, hx, rfl⟩
    have hxK : (x : G) ∈ K := hx
    refine quotAct_apply π hπ hker ht x x ?_
    rw [← hKC _ hxK]
    group
  have hstab : (actHom π hπ hker Y hYn).range ≤ pointwiseStab Kb := by
    rintro _ ⟨y, rfl⟩ _ ⟨x, hx, rfl⟩
    exact actHom_fix π hπ hker Y hYn (Subgroup.mem_centralizer_iff.mp (hYc y.2) x hx)
  rw [relIndex_eq_card_range π hπ hker Y hYn hXq.1]
  exact (Subgroup.card_le_of_le hstab).trans (card_pointwiseStab_le_two hF hKb hτfix hτ2 hτ1)

end AutCent

section Conj

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.QuasithinUnique.Id2519.Tab

section Action

variable {G : Type} [Group G] {X : Subgroup G} {Q : Type*} [Group Q]
  (π : X →* Q) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center X)

theorem quotAct_mul_elem {t u : G} (ht : t ∈ Subgroup.normalizer (X : Set G)) (hu : u ∈ X)
    (htu : t * u ∈ Subgroup.normalizer (X : Set G)) :
    quotAct π hπ hker htu = quotAct π hπ hker ht * MulAut.conj (π ⟨u, hu⟩) := by
  ext q
  obtain ⟨x, rfl⟩ := hπ q
  have hz : (u * x * u⁻¹ : G) ∈ X := X.mul_mem (X.mul_mem hu x.2) (X.inv_mem hu)
  have hy : (t * (u * x * u⁻¹) * t⁻¹ : G) ∈ X := (Subgroup.mem_normalizer_iff.mp ht _).mp hz
  rw [MulAut.mul_apply]
  have h1 : MulAut.conj (π ⟨u, hu⟩) (π x) = π ⟨u * x * u⁻¹, hz⟩ := by
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [h1, quotAct_apply π hπ hker ht ⟨u * x * u⁻¹, hz⟩ ⟨t * (u * x * u⁻¹) * t⁻¹, hy⟩ rfl,
    quotAct_apply π hπ hker htu x ⟨t * (u * x * u⁻¹) * t⁻¹, hy⟩ (by group)]

theorem quotAct_conj_elem (x₀ : X) {w : G} (hw : w ∈ Subgroup.normalizer (X : Set G))
    (hw' : (x₀ : G) * w * (x₀ : G)⁻¹ ∈ Subgroup.normalizer (X : Set G)) :
    quotAct π hπ hker hw' =
      MulAut.conj (π x₀) * quotAct π hπ hker hw * (MulAut.conj (π x₀))⁻¹ := by
  ext q
  obtain ⟨x, rfl⟩ := hπ q
  have hz : ((x₀ : G)⁻¹ * x * x₀ : G) ∈ X := X.mul_mem (X.mul_mem (X.inv_mem x₀.2) x.2) x₀.2
  have hy : (w * ((x₀ : G)⁻¹ * x * x₀) * w⁻¹ : G) ∈ X := (Subgroup.mem_normalizer_iff.mp hw _).mp hz
  have h1 : (MulAut.conj (π x₀))⁻¹ (π x) = π ⟨(x₀ : G)⁻¹ * x * x₀, hz⟩ := by
    rw [← map_inv, MulAut.conj_apply, inv_inv, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [MulAut.mul_apply, MulAut.mul_apply, h1,
    quotAct_apply π hπ hker hw ⟨(x₀ : G)⁻¹ * x * x₀, hz⟩ ⟨w * ((x₀ : G)⁻¹ * x * x₀) * w⁻¹, hy⟩ rfl,
    MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  exact quotAct_apply π hπ hker hw' x _ (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)

theorem commute_of_quotAct_eq (hπinj : Function.Injective π) {w₁ w₂ : G}
    (h₁ : w₁ ∈ Subgroup.normalizer (X : Set G)) (h₂ : w₂ ∈ Subgroup.normalizer (X : Set G))
    (h : quotAct π hπ hker h₁ = quotAct π hπ hker h₂) :
    ∀ x ∈ X, (w₂⁻¹ * w₁) * x = x * (w₂⁻¹ * w₁) := by
  intro x hx
  have hy₁ : w₁ * x * w₁⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp h₁ x).mp hx
  have hy₂ : w₂ * x * w₂⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp h₂ x).mp hx
  have e₁ := quotAct_apply π hπ hker h₁ ⟨x, hx⟩ ⟨w₁ * x * w₁⁻¹, hy₁⟩ rfl
  have e₂ := quotAct_apply π hπ hker h₂ ⟨x, hx⟩ ⟨w₂ * x * w₂⁻¹, hy₂⟩ rfl
  rw [h, e₂] at e₁
  have e₃ := congrArg Subtype.val (hπinj e₁)
  change w₂ * x * w₂⁻¹ = w₁ * x * w₁⁻¹ at e₃
  calc w₂⁻¹ * w₁ * x = w₂⁻¹ * (w₁ * x * w₁⁻¹) * w₁ := by group
    _ = w₂⁻¹ * (w₂ * x * w₂⁻¹) * w₁ := by rw [e₃]
    _ = x * (w₂⁻¹ * w₁) := by group

end Action

theorem tabConjSp4 : TabConjSp4 := by
  intro G _ _ X K t hXq ht ht2 hcomm hK hpat u huK hu2
  obtain ⟨F, _, _, _, hF, ⟨θ⟩⟩ := sp4_model hpat
  have hZ : Subgroup.center ↥X = ⊥ := center_eq_bot_of_equiv θ
  let π : ↥X →* StatedProj (StatedSp 2 F) := θ.toMonoidHom
  have hπ : Function.Surjective π := θ.surjective
  have hker : π.ker = Subgroup.center ↥X := by
    rw [hZ]
    exact (MonoidHom.ker_eq_bot_iff π).mpr θ.injective
  have hKle : K ≤ X ⊓ Subgroup.centralizer ({t} : Set G) :=
    hK.le.trans (perfectResidualOf_le _)
  have hKX : K ≤ X := hKle.trans inf_le_left
  have hKC : ∀ x ∈ K, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKle hx).2
  let Kb : Subgroup (StatedProj (StatedSp 2 F)) := (K.subgroupOf X).map π
  have hKb : Nat.card Kb = 360 := by
    obtain ⟨⟨e⟩, -⟩ := hpat
    have h1 : Nat.card Kb = Nat.card (K.subgroupOf X) :=
      Subgroup.card_map_of_injective θ.injective
    have h2 : Nat.card (K.subgroupOf X) = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv
    have h3 : Nat.card K = 360 := (Nat.card_congr e.toEquiv).trans card_alt_six
    rw [h1, h2, h3]
  set τ := quotAct π hπ hker ht with hτdef
  have hτ2 : τ * τ = 1 := quotAct_mul_self π hπ hker ht ht2
  have hτ1 : τ ≠ 1 := quotAct_ne_one π hπ hker ht hXq hcomm
  have hτfix : ∀ k ∈ Kb, τ k = k := by
    rintro _ ⟨x, hx, rfl⟩
    have hxK : (x : G) ∈ K := hx
    refine quotAct_apply π hπ hker ht x x ?_
    rw [← hKC _ hxK]
    group
  obtain ⟨hinvol, -, -⟩ := aut_facts hF
  have hord : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
  have hnot : τ ∉ inner (StatedProj (StatedSp 2 F)) :=
    not_mem_inner_of_fix hF (by rw [hKb]; norm_num) hτfix hτ2 hτ1
  have huX : u ∈ X := hKX huK
  have hut : u * t = t * u := hKC u huK
  have htu : t * u ∈ Subgroup.normalizer (X : Set G) := mul_mem ht (Subgroup.le_normalizer huX)
  have htu2 : (t * u) * (t * u) = 1 := by
    calc t * u * (t * u) = t * (u * t) * u := by group
      _ = t * (t * u) * u := by rw [hut]
      _ = (t * t) * (u * u) := by group
      _ = 1 := by rw [ht2, hu2, mul_one]
  have hτ'2 := quotAct_mul_self π hπ hker htu htu2
  set τ' := quotAct π hπ hker htu with hτ'def
  have hinnu : MulAut.conj (π ⟨u, huX⟩) ∈ inner (StatedProj (StatedSp 2 F)) := ⟨_, rfl⟩
  have hτ'eq : τ' = τ * MulAut.conj (π ⟨u, huX⟩) := quotAct_mul_elem π hπ hker ht huX htu
  have hτ'E : τ' ∈ spSemilinearAutGroup 2 F :=
    hτ'eq ▸ mul_mem (hinvol τ hord) (inner_le_spSemilinearAutGroup hinnu)
  have hτ'inner : τ' ∉ inner (StatedProj (StatedSp 2 F)) := by
    intro h
    apply hnot
    have : τ = τ' * (MulAut.conj (π ⟨u, huX⟩))⁻¹ := by rw [hτ'eq]; group
    rw [this]
    exact mul_mem h (inv_mem hinnu)
  obtain ⟨σ, h, hσ1, hσσ, hτh⟩ := exists_conj_fieldAut hF hτ2 hnot (hinvol τ hord)
  obtain ⟨σ', h', hσ'1, hσ'σ', hτ'h⟩ := exists_conj_fieldAut hF hτ'2 hτ'inner hτ'E
  have hσσ' : σ' = σ := (eq_one_or_eq_of_ne_one hF hσ1 σ').resolve_left hσ'1
  subst hσσ'
  let x₀ : ↥X := θ.symm (proj 2 F (h' * h⁻¹))
  have hπx₀ : π x₀ = proj 2 F (h' * h⁻¹) := θ.apply_symm_apply _
  have hconj : τ' = MulAut.conj (π x₀) * τ * (MulAut.conj (π x₀))⁻¹ := by
    rw [hπx₀, ← spInner_eq_conj, map_mul, map_inv, hτh, hτ'h]
    group
  have hw₁ : (x₀ : G) * t * (x₀ : G)⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
    mul_mem (mul_mem (Subgroup.le_normalizer x₀.2) ht) (inv_mem (Subgroup.le_normalizer x₀.2))
  have heq : quotAct π hπ hker hw₁ = τ' := by
    rw [quotAct_conj_elem π hπ hker x₀ ht hw₁, hconj]
  have hcomm₂ := commute_of_quotAct_eq π hπ hker θ.injective hw₁ htu heq
  have hc : (t * u)⁻¹ * ((x₀ : G) * t * (x₀ : G)⁻¹) ∈ X := by
    have h1 : t⁻¹ * (x₀ : G) * t ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem ht) x₀).mp x₀.2
      simpa using this
    have h2 : (t * u)⁻¹ * ((x₀ : G) * t * (x₀ : G)⁻¹) =
        u⁻¹ * (t⁻¹ * (x₀ : G) * t) * (x₀ : G)⁻¹ := by group
    rw [h2]
    exact X.mul_mem (X.mul_mem (X.inv_mem huX) h1) (X.inv_mem x₀.2)
  have hc1 : (t * u)⁻¹ * ((x₀ : G) * t * (x₀ : G)⁻¹) = 1 := by
    have hmem : (⟨_, hc⟩ : ↥X) ∈ Subgroup.center ↥X :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hcomm₂ g g.2).symm
    rw [hZ] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  refine ⟨(x₀ : G)⁻¹, X.inv_mem x₀.2, ?_⟩
  rw [inv_inv]
  calc (x₀ : G) * t * (x₀ : G)⁻¹
      = (t * u) * ((t * u)⁻¹ * ((x₀ : G) * t * (x₀ : G)⁻¹)) := by group
    _ = t * u := by rw [hc1, mul_one]

end Conj

end CFSG.QuasithinUnique.Id2519.USp4
