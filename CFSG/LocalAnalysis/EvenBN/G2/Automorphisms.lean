module

public import CFSG.LocalAnalysis.EvenBN.G2.Radicals
public import CFSG.LocalAnalysis.EvenBN.Common.FreeSeries
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)


theorem isElementaryAbelian_quotient_of_mul_self {G : Type*} [Group G] {N E : Subgroup G}
    [(N.subgroupOf E).Normal] (h : ∀ x ∈ E, x * x ∈ N) :
    CFSG.IsElementaryAbelian 2 (E ⧸ N.subgroupOf E) := by
  have hsq : ∀ q : E ⧸ N.subgroupOf E, q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact mem_subgroupOf.2 (h a a.2)
  have hinv : ∀ q : E ⧸ N.subgroupOf E, q⁻¹ = q := fun q => inv_eq_of_mul_eq_one_right (hsq q)
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · calc a * b = (a * b)⁻¹ := (hinv _).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv, hinv]
  · exact Monoid.exponent_dvd_of_forall_pow_eq_one fun q => by rw [sq]; exact hsq q

theorem orderOf_inv_mul_mul {G : Type*} [Group G] (a w : G) :
    orderOf (w⁻¹ * a * w) = orderOf a := by
  have h := MulEquiv.orderOf_eq (MulAut.conj w⁻¹) a
  rwa [MulAut.conj_apply, inv_inv] at h

theorem card_map_conj {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
  card_map_of_injective (MulAut.conj g).injective

section Frobenius

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem frobeniusEquiv_pow_apply (k : ℕ) (c : K) : (frobeniusEquiv K 2 ^ k) c = c ^ 2 ^ k :=
  ComponentInitial.ringAut_pow_apply_of_sq (fun a => by
    rw [frobeniusEquiv_apply, frobenius_def]) k c

theorem orderOf_frobeniusEquiv {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) :
    orderOf (frobeniusEquiv K 2) = n := by
  obtain ⟨σ, hσ, hord, -⟩ :=
    ComponentInitial.finite_field_automorphism_fixed_field_cardinality Nat.prime_two hn hK
  have : σ = frobeniusEquiv K 2 := RingEquiv.ext fun a => by
    rw [hσ, frobeniusEquiv_apply, frobenius_def]
  rwa [← this]

theorem exists_eq_frobeniusEquiv_pow {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    (σ : K ≃+* K) : ∃ s < n, σ = frobeniusEquiv K 2 ^ s := by
  obtain ⟨s, hs, hσs, -⟩ := ComponentInitial.exists_frobenius_pow_eq hn hK σ
  exact ⟨s, hs, RingEquiv.ext fun c => by rw [hσs, frobeniusEquiv_pow_apply]⟩

theorem eq_zero_of_forall_pow_eq {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {k : ℕ}
    (hk : k < n) (h : ∀ c : K, c ^ 2 ^ k = c) : k = 0 := by
  have h1 : frobeniusEquiv K 2 ^ k = 1 :=
    RingEquiv.ext fun c => by rw [frobeniusEquiv_pow_apply, h]; rfl
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_frobeniusEquiv hK (by omega)] at h2
  exact Nat.eq_zero_of_dvd_of_lt h2 hk

end Frobenius

namespace Model

section Inn

variable {K : Type} [Field K]

@[expose] noncomputable def inn (H : Subgroup (ModGL .G2 K)) :
    Subgroup (MulAut (adjointGroup .G2 K)) :=
  (H.subgroupOf (adjointGroup .G2 K)).map MulAut.conj

theorem mem_inn {H : Subgroup (ModGL .G2 K)} {α : MulAut (adjointGroup .G2 K)} :
    α ∈ inn H ↔ ∃ g : adjointGroup .G2 K, (g : ModGL .G2 K) ∈ H ∧ MulAut.conj g = α := by
  simp only [inn, mem_map, mem_subgroupOf]

theorem conj_mem_inn {H : Subgroup (ModGL .G2 K)} {g : adjointGroup .G2 K}
    (hg : (g : ModGL .G2 K) ∈ H) : MulAut.conj g ∈ inn H :=
  mem_inn.2 ⟨g, hg, rfl⟩

theorem inn_mono {H₁ H₂ : Subgroup (ModGL .G2 K)} (h : H₁ ≤ H₂) : inn H₁ ≤ inn H₂ := by
  intro α hα
  obtain ⟨g, hg, rfl⟩ := mem_inn.1 hα
  exact conj_mem_inn (h hg)

theorem inn_sup {H₁ H₂ : Subgroup (ModGL .G2 K)} (h₁ : H₁ ≤ adjointGroup .G2 K)
    (h₂ : H₂ ≤ adjointGroup .G2 K) : inn (H₁ ⊔ H₂) = inn H₁ ⊔ inn H₂ := by
  rw [inn, subgroupOf_sup h₁ h₂, Subgroup.map_sup]
  rfl

theorem inn_adjointGroup : inn (adjointGroup .G2 K) = inner (adjointGroup .G2 K) := by
  rw [inn, subgroupOf_self, ← MonoidHom.range_eq_map]
  rfl

theorem inn_le_inner (H : Subgroup (ModGL .G2 K)) : inn H ≤ inner (adjointGroup .G2 K) := by
  rintro _ ⟨g, -, rfl⟩
  exact ⟨g, rfl⟩

theorem inn_bot : inn (⊥ : Subgroup (ModGL .G2 K)) = ⊥ := by
  rw [inn, bot_subgroupOf, Subgroup.map_bot]

theorem inn_subgroupOf_normal {H₁ H₂ : Subgroup (ModGL .G2 K)}
    (h : H₂ ≤ normalizer (H₁ : Set (ModGL .G2 K))) : ((inn H₁).subgroupOf (inn H₂)).Normal := by
  refine ⟨fun x hx y => ?_⟩
  rw [mem_subgroupOf] at hx ⊢
  obtain ⟨a, ha, hax⟩ := mem_inn.1 hx
  obtain ⟨b, hb, hby⟩ := mem_inn.1 y.2
  rw [coe_mul, coe_mul, coe_inv, ← hax, ← hby, ← map_mul, ← map_inv, ← map_mul]
  refine conj_mem_inn ?_
  rw [coe_mul, coe_mul, coe_inv]
  exact (mem_normalizer_iff.1 (h hb) _).1 ha

theorem inn_quotient_isElementaryAbelian {H₁ H₂ : Subgroup (ModGL .G2 K)}
    [((inn H₁).subgroupOf (inn H₂)).Normal]
    (h : ∀ x ∈ H₂, x ∈ adjointGroup .G2 K → x * x ∈ H₁) :
    CFSG.IsElementaryAbelian 2 (inn H₂ ⧸ (inn H₁).subgroupOf (inn H₂)) :=
  isElementaryAbelian_quotient_of_mul_self fun x hx => by
    obtain ⟨g, hg, rfl⟩ := mem_inn.1 hx
    rw [← map_mul]
    exact conj_mem_inn (by rw [coe_mul]; exact h _ hg g.2)

end Inn

section InnFinite

variable
  {K : Type} [Field K] [Finite K]

theorem conj_injective :
    Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
  mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot

theorem conj_mem_inn_iff {H : Subgroup (ModGL .G2 K)} {g : adjointGroup .G2 K} :
    MulAut.conj g ∈ inn H ↔ (g : ModGL .G2 K) ∈ H := by
  refine ⟨fun h => ?_, conj_mem_inn⟩
  obtain ⟨g', hg', he⟩ := mem_inn.1 h
  rwa [← conj_injective he]

theorem mem_centralizer_inn_iff {H : Subgroup (ModGL .G2 K)} {α : MulAut (adjointGroup .G2 K)} :
    α ∈ centralizer (inn H : Set (MulAut (adjointGroup .G2 K))) ↔
      ∀ x : adjointGroup .G2 K, (x : ModGL .G2 K) ∈ H → α x = x := by
  rw [mem_centralizer_iff]
  constructor
  · intro h x hx
    have h1 := h _ (conj_mem_inn hx)
    have h2 : MulAut.conj (α x) = MulAut.conj x := by
      rw [← mulAut_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
    exact conj_injective h2
  · intro h β hβ
    obtain ⟨x, hx, rfl⟩ := mem_inn.1 hβ
    have h2 : α * MulAut.conj x * α⁻¹ = MulAut.conj x := by
      rw [mulAut_mul_conj_mul_inv, h x hx]
    calc MulAut.conj x * α = α * MulAut.conj x * α⁻¹ * α := by rw [h2]
      _ = α * MulAut.conj x := by group

theorem mem_normalizer_inn_iff {H : Subgroup (ModGL .G2 K)} {α : MulAut (adjointGroup .G2 K)} :
    α ∈ normalizer (inn H : Set (MulAut (adjointGroup .G2 K))) ↔
      ∀ x : adjointGroup .G2 K, ((α x : adjointGroup .G2 K) : ModGL .G2 K) ∈ H ↔
        (x : ModGL .G2 K) ∈ H := by
  rw [mem_normalizer_iff]
  constructor
  · intro h x
    have := h (MulAut.conj x)
    rw [mulAut_mul_conj_mul_inv, conj_mem_inn_iff, conj_mem_inn_iff] at this
    exact this.symm
  · intro h β
    constructor
    · intro hβ
      obtain ⟨x, hx, rfl⟩ := mem_inn.1 hβ
      rw [mulAut_mul_conj_mul_inv, conj_mem_inn_iff]
      exact (h x).2 hx
    · intro hβ
      obtain ⟨y, hy, hye⟩ := mem_inn.1 hβ
      have e : β = MulAut.conj (α⁻¹ y) := by
        rw [← mulAut_mul_conj_mul_inv, hye]
        group
      rw [e, conj_mem_inn_iff]
      have := (h (α⁻¹ y)).1
      rw [MulAut.apply_inv_self] at this
      exact this hy

theorem card_inn {H : Subgroup (ModGL .G2 K)} (h : H ≤ adjointGroup .G2 K) :
    Nat.card (inn H) = Nat.card H := by
  rw [inn, card_map_of_injective conj_injective]
  exact Nat.card_congr (subgroupOfEquivOfLe h).toEquiv

end InnFinite

section Field

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem fieldAut_eq : fieldAut K = entrywiseAdjointAut .G2 (frobeniusEquiv K 2) :=
  MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_entrywiseAdjointAut, fieldAut, coe_exactNormalAut_zero,
      rootDiagUnit_one, one_mul, inv_one, mul_one])

theorem fieldAut_pow (k : ℕ) :
    fieldAut K ^ k = entrywiseAdjointAut .G2 (frobeniusEquiv K 2 ^ k) := by
  rw [fieldAut_eq, entrywiseAdjointAut_pow]

theorem coe_fieldAut_pow_apply (k : ℕ) (h : adjointGroup .G2 K) :
    (((fieldAut K ^ k) h : adjointGroup .G2 K) : ModGL .G2 K) =
      Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom) (h : ModGL .G2 K) := by
  rw [fieldAut_pow, coe_entrywiseAdjointAut]

omit
  [Finite K] [CharP K 2] in
theorem units_map_entrywise_pinnedX (σ : K ≃+* K) (s : Fin Tag.G2.rank → ℤ) (c : K) :
    Units.map (entrywiseHom σ.toRingHom) (pinnedX .G2 K s c) = pinnedX .G2 K s (σ c) :=
  Units.ext (by
    rw [Units.coe_map]
    exact entrywise_pinnedX σ.toRingHom s c)

theorem fieldAut_pow_pinnedX (k : ℕ) (s : Fin Tag.G2.rank → ℤ) (c : K) :
    (((fieldAut K ^ k) ⟨pinnedX .G2 K s c, pinnedX_mem_adjointGroup s c⟩ :
      adjointGroup .G2 K) : ModGL .G2 K) = pinnedX .G2 K s (c ^ 2 ^ k) := by
  rw [coe_fieldAut_pow_apply, units_map_entrywise_pinnedX]
  exact congrArg _ (frobeniusEquiv_pow_apply k c)

theorem fieldAut_pow_g2N (k : ℕ) (A B C D E F : K) (h : g2N A B C D E F ∈ adjointGroup .G2 K) :
    (((fieldAut K ^ k) ⟨g2N A B C D E F, h⟩ : adjointGroup .G2 K) : ModGL .G2 K) =
      g2N (A ^ 2 ^ k) (B ^ 2 ^ k) (C ^ 2 ^ k) (D ^ 2 ^ k) (E ^ 2 ^ k) (F ^ 2 ^ k) := by
  rw [coe_fieldAut_pow_apply]
  simp only [g2N, map_mul, units_map_entrywise_pinnedX, frobeniusEquiv_pow_apply]

theorem fieldAut_pow_torusElt (k : ℕ) (i : Fin Tag.G2.rank) (t : Kˣ) :
    (((fieldAut K ^ k) ⟨torusElt .G2 K i t, torusElt_mem_adjointGroup i t⟩ :
      adjointGroup .G2 K) : ModGL .G2 K) = torusElt .G2 K i (t ^ 2 ^ k) := by
  rw [coe_fieldAut_pow_apply, entrywise_torusElt]
  congr 1
  exact Units.ext (by
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact frobeniusEquiv_pow_apply k (t : K))

theorem fieldAut_pow_weylElt (k : ℕ) (i : Fin Tag.G2.rank) :
    (fieldAut K ^ k) ⟨weylElt .G2 K i 1, weylElt_mem_adjointGroup i 1⟩ =
      ⟨weylElt .G2 K i 1, weylElt_mem_adjointGroup i 1⟩ :=
  Subtype.ext (by rw [coe_fieldAut_pow_apply, entrywise_weylElt_one])

end Field


section NormalForm

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem coe_conj_mul_fieldAut_pow_apply (g : adjointGroup .G2 K) (k : ℕ)
    (h : adjointGroup .G2 K) :
    (((MulAut.conj g * fieldAut K ^ k) h : adjointGroup .G2 K) : ModGL .G2 K) =
      (g : ModGL .G2 K) * Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom)
        (h : ModGL .G2 K) * (g : ModGL .G2 K)⁻¹ := by
  rw [MulAut.mul_apply, MulAut.conj_apply, coe_mul, coe_mul, coe_inv, coe_fieldAut_pow_apply]

theorem exists_eq_conj_mul_fieldAut_pow {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (α : MulAut (adjointGroup .G2 K)) :
    ∃ g : adjointGroup .G2 K, ∃ k < n, α = MulAut.conj g * fieldAut K ^ k := by
  obtain ⟨hNF, -⟩ := even_G2_exact_automorphism_normal_form hn K hK
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF α
  obtain ⟨k, hk, rfl⟩ := exists_eq_frobeniusEquiv_pow hK (by omega) σ
  refine ⟨g, k, hk, MulEquiv.ext fun h => Subtype.ext ?_⟩
  rw [hgσ h, coe_conj_mul_fieldAut_pow_apply]

theorem conj_mul_fieldAut_pow_inj {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {g g' : adjointGroup .G2 K} {k k' : ℕ} (hk : k < n) (hk' : k' < n)
    (h : MulAut.conj g * fieldAut K ^ k = MulAut.conj g' * fieldAut K ^ k') :
    g = g' ∧ k = k' := by
  obtain ⟨hNF, -⟩ := even_G2_exact_automorphism_normal_form hn K hK
  obtain ⟨p, -, huniq⟩ := hNF (MulAut.conj g * fieldAut K ^ k)
  have h1 := huniq (g, frobeniusEquiv K 2 ^ k) (coe_conj_mul_fieldAut_pow_apply g k)
  have h2 := huniq (g', frobeniusEquiv K 2 ^ k') (by
    rw [h]
    exact coe_conj_mul_fieldAut_pow_apply g' k')
  have h3 := h1.trans h2.symm
  refine ⟨congrArg Prod.fst h3, ?_⟩
  have h4 : frobeniusEquiv K 2 ^ k = frobeniusEquiv K 2 ^ k' := congrArg Prod.snd h3
  rw [pow_eq_pow_iff_modEq, orderOf_frobeniusEquiv hK (by omega)] at h4
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk'] at h4

theorem fieldAut_pow_card {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    fieldAut K ^ n = 1 := by
  rw [fieldAut_pow, ← orderOf_frobeniusEquiv hK (by omega), pow_orderOf_eq_one]
  exact map_one (entrywiseAdjointAutHom (τ := .G2) (K := K))

theorem fieldAut_pow_mem_inner_iff {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (k : ℕ) :
    fieldAut K ^ k ∈ inner (adjointGroup .G2 K) ↔ n ∣ k := by
  have hf : ∀ m, fieldAut K ^ m = fieldAut K ^ (m % n) := fun m => by
    conv_lhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, fieldAut_pow_card hK hn, one_pow,
      one_mul]
  constructor
  · rintro ⟨g, hg⟩
    have e : MulAut.conj g * fieldAut K ^ 0 = MulAut.conj 1 * fieldAut K ^ (k % n) := by
      rw [pow_zero, mul_one, map_one, one_mul, ← hf, hg]
    obtain ⟨-, h0⟩ := conj_mul_fieldAut_pow_inj hK hn (by omega) (Nat.mod_lt _ (by omega)) e
    exact Nat.dvd_of_mod_eq_zero h0.symm
  · rintro ⟨m, rfl⟩
    rw [pow_mul, fieldAut_pow_card hK hn, one_pow]
    exact one_mem _

theorem orderOf_fieldAut {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    orderOf (fieldAut K) = n := by
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (fieldAut_pow_card hK hn)) ?_
  rw [← fieldAut_pow_mem_inner_iff hK hn, pow_orderOf_eq_one]
  exact one_mem _

theorem exists_eq_fieldAut_pow_of_mem_zpowers {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {α : MulAut (adjointGroup .G2 K)} (hα : α ∈ zpowers (fieldAut K)) :
    ∃ k < n, α = fieldAut K ^ k := by
  have hfin : IsOfFinOrder (fieldAut K) :=
    orderOf_pos_iff.1 (by rw [orderOf_fieldAut hK hn]; omega)
  obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (hfin.mem_powers_iff_mem_zpowers.2 hα)
  refine ⟨m % n, Nat.mod_lt _ (by omega), ?_⟩
  rw [← orderOf_fieldAut hK hn, pow_mod_orderOf]

theorem fieldAut_pow_mem_normalizer_inn {H : Subgroup (ModGL .G2 K)}
    (hHC : H ≤ adjointGroup .G2 K)
    (hH : ∀ k : ℕ, H.map (Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom)) = H)
    (k : ℕ) : fieldAut K ^ k ∈ normalizer (inn H : Set (MulAut (adjointGroup .G2 K))) := by
  rw [mem_normalizer_inn_iff]
  intro x
  rw [coe_fieldAut_pow_apply]
  constructor
  · intro hx
    rw [← hH k] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have e : (fieldAut K ^ k) ⟨y, hHC hy⟩ = (fieldAut K ^ k) x :=
      Subtype.ext (by rw [coe_fieldAut_pow_apply, hyx, coe_fieldAut_pow_apply])
    rw [← (fieldAut K ^ k).injective e]
    exact hy
  · intro hx
    rw [← hH k]
    exact ⟨_, hx, rfl⟩

theorem yamada_3_18 {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) ∧
      (inner (adjointGroup .G2 K)).Normal ∧
      inner (adjointGroup .G2 K) ⊓ zpowers (fieldAut K) = ⊥ ∧
      inner (adjointGroup .G2 K) ⊔ zpowers (fieldAut K) = ⊤ ∧
      orderOf (fieldAut K) = n ∧
      (∀ α : MulAut (adjointGroup .G2 K), ∃! p : adjointGroup .G2 K × Fin n,
        α = MulAut.conj p.1 * fieldAut K ^ (p.2 : ℕ)) ∧
      (∀ (r : Fin Tag.G2.rank → ℤ) (c : K),
        ((fieldAut K ⟨pinnedX .G2 K r c, pinnedX_mem_adjointGroup r c⟩ : adjointGroup .G2 K) :
          ModGL .G2 K) = pinnedX .G2 K r (c ^ 2)) ∧
      (∀ r : Fin Tag.G2.rank → ℤ, fieldAut K ∈
        normalizer (inn (rootSubgroup .G2 K r) : Set (MulAut (adjointGroup .G2 K)))) ∧
      (∀ i : Fin Tag.G2.rank, fieldAut K ⟨weylElt .G2 K i 1, weylElt_mem_adjointGroup i 1⟩ =
        ⟨weylElt .G2 K i 1, weylElt_mem_adjointGroup i 1⟩) ∧
      ∀ (i : Fin Tag.G2.rank) (t : Kˣ),
        ((fieldAut K ⟨torusElt .G2 K i t, torusElt_mem_adjointGroup i t⟩ :
          adjointGroup .G2 K) : ModGL .G2 K) = torusElt .G2 K i (t ^ 2) := by
  refine ⟨conj_injective, inner_normal _, ?_, ?_, orderOf_fieldAut hK hn, fun α => ?_,
    fun r c => ?_, fun r => ?_, fun i => ?_, fun i t => ?_⟩
  · refine eq_bot_iff.2 fun α ⟨hα₁, hα₂⟩ => ?_
    obtain ⟨k, hk, rfl⟩ := exists_eq_fieldAut_pow_of_mem_zpowers hK hn hα₂
    obtain ⟨m, rfl⟩ := (fieldAut_pow_mem_inner_iff hK hn k).1 hα₁
    rw [mem_bot, pow_mul, fieldAut_pow_card hK hn, one_pow]
  · refine eq_top_iff.2 fun α _ => ?_
    obtain ⟨g, k, -, rfl⟩ := exists_eq_conj_mul_fieldAut_pow hK hn α
    exact mul_mem (mem_sup_left ⟨g, rfl⟩) (mem_sup_right (pow_mem (mem_zpowers _) k))
  · obtain ⟨g, k, hk, rfl⟩ := exists_eq_conj_mul_fieldAut_pow hK hn α
    refine ⟨(g, ⟨k, hk⟩), rfl, fun p hp => ?_⟩
    obtain ⟨hg, hk'⟩ := conj_mul_fieldAut_pow_inj hK hn p.2.2 hk hp.symm
    exact Prod.ext hg (Fin.ext hk')
  · have := fieldAut_pow_pinnedX (K := K) 1 r c
    rwa [pow_one, pow_one] at this
  · have := fieldAut_pow_mem_normalizer_inn (K := K) (rootSubgroup_le_adjointGroup r)
      (fun k => map_entrywise_rootSubgroup (frobeniusEquiv K 2 ^ k) r) 1
    rwa [pow_one] at this
  · have := fieldAut_pow_weylElt (K := K) 1 i
    rwa [pow_one] at this
  · have := fieldAut_pow_torusElt (K := K) 1 i t
    rwa [pow_one, pow_one] at this

end NormalForm

section Centralizers

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_eq_conj_of_fix_rootSubgroup {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {s : Fin Tag.G2.rank → ℤ}
    (hcent : adjointGroup .G2 K ⊓ centralizer {pinnedX .G2 K s 1} ≤
      centralizer (rootSubgroup .G2 K s : Set (ModGL .G2 K)))
    {α : MulAut (adjointGroup .G2 K)}
    (hα : ∀ x : adjointGroup .G2 K, (x : ModGL .G2 K) ∈ rootSubgroup .G2 K s → α x = x) :
    ∃ g : adjointGroup .G2 K,
      (g : ModGL .G2 K) ∈ centralizer (rootSubgroup .G2 K s : Set (ModGL .G2 K)) ∧
        α = MulAut.conj g := by
  obtain ⟨g, k, hk, rfl⟩ := exists_eq_conj_mul_fieldAut_pow hK hn α
  have key : ∀ c : K, (g : ModGL .G2 K) * pinnedX .G2 K s (c ^ 2 ^ k) * (g : ModGL .G2 K)⁻¹ =
      pinnedX .G2 K s c := fun c => by
    have := congrArg Subtype.val (hα ⟨pinnedX .G2 K s c, pinnedX_mem_adjointGroup s c⟩
      (mem_rootSubgroup.2 ⟨c, rfl⟩))
    rwa [coe_conj_mul_fieldAut_pow_apply, units_map_entrywise_pinnedX,
      frobeniusEquiv_pow_apply] at this
  have hg : (g : ModGL .G2 K) ∈ centralizer (rootSubgroup .G2 K s : Set (ModGL .G2 K)) := by
    refine hcent ⟨g.2, mem_centralizer_singleton_iff.2 ?_⟩
    have := key 1
    rw [one_pow] at this
    calc (g : ModGL .G2 K) * pinnedX .G2 K s 1 =
        (g : ModGL .G2 K) * pinnedX .G2 K s 1 * (g : ModGL .G2 K)⁻¹ * g := by group
      _ = pinnedX .G2 K s 1 * g := by rw [this]
  have hk0 : k = 0 := by
    refine eq_zero_of_forall_pow_eq hK hn hk fun c => pinnedX_injective .G2 K s ?_
    rw [← key c]
    have := mem_centralizer_iff.1 hg _ (mem_rootSubgroup.2 ⟨c ^ 2 ^ k, rfl⟩)
    rw [← this]
    group
  subst hk0
  exact ⟨g, hg, by rw [pow_zero, mul_one]⟩

theorem centralizer_pinnedX_c_le :
    adjointGroup .G2 K ⊓ centralizer {pinnedX .G2 K g2c 1} ≤
      centralizer (rootSubgroup .G2 K g2c : Set (ModGL .G2 K)) := by
  obtain ⟨-, -, -, hC, -, -, -, -, hQ, -, -, hL⟩ := even_G2_highest_long_root_centralizer K
  rw [hC]
  refine sup_le (fun q hq => mem_centralizer_iff.2 fun x hx => ?_)
    fun l hl => mem_centralizer_iff.2 fun x hx => ?_
  · obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
    exact ((hQ y).2 q hq).eq
  · obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
    exact (hL l hl y).eq.symm

theorem centralizer_pinnedX_v_le :
    adjointGroup .G2 K ⊓ centralizer {pinnedX .G2 K g2v 1} ≤
      centralizer (rootSubgroup .G2 K g2v : Set (ModGL .G2 K)) := by
  obtain ⟨-, -, -, hC, -, -, -, -, hL, -⟩ := even_G2_highest_short_root_centralizer K
  rw [hC]
  refine sup_le (fun w hw => mem_centralizer_iff.2 fun x hx => ?_)
    fun l hl => mem_centralizer_iff.2 fun x hx => ?_
  · obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
    exact (commute_of_mem_g2ShortRadical (pinnedX_v_mem_g2ShortRadical y) hw).eq
  · obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
    exact (hL l hl y).eq.symm

omit
  [Finite K] [CharP K 2] in
theorem exists_weyl_smul_eq {δ : Fin Tag.G2.rank → ℤ} (hδ : IsRoot .G2 δ) :
    ∃ w : WeylGroup .G2, w • g2c = δ ∨ w • g2v = δ := by
  have hneg : ∀ {γ : Fin Tag.G2.rank → ℤ}, (γ = g2r ∨ γ = g2a ∨ γ = g2u ∨ γ = g2v ∨ γ = g2b ∨
      γ = g2c) → g2LongestWeyl • γ = -γ := fun hγ => by
    have := g2LongestWeyl_smul_neg _ hγ
    rw [smul_neg] at this
    exact neg_eq_iff_eq_neg.mp this
  have hpos : ∀ {γ : Fin Tag.G2.rank → ℤ}, (γ = g2r ∨ γ = g2a ∨ γ = g2u ∨ γ = g2v ∨ γ = g2b ∨
      γ = g2c) → ∃ w : WeylGroup .G2, w • g2c = γ ∨ w • g2v = γ := fun hγ => by
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨simple .G2 g2ia * simple .G2 g2ir, Or.inr ?_⟩
      simp only [mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · refine ⟨simple .G2 g2ir * simple .G2 g2ia, Or.inl ?_⟩
      simp only [mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · refine ⟨simple .G2 g2ir, Or.inr ?_⟩
      simp only [simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · exact ⟨1, Or.inr (one_smul _ _)⟩
    · refine ⟨simple .G2 g2ia, Or.inl ?_⟩
      simp only [simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · exact ⟨1, Or.inl (one_smul _ _)⟩
  have hnegpos : ∀ {γ : Fin Tag.G2.rank → ℤ}, (γ = g2r ∨ γ = g2a ∨ γ = g2u ∨ γ = g2v ∨
      γ = g2b ∨ γ = g2c) → ∃ w : WeylGroup .G2, w • g2c = -γ ∨ w • g2v = -γ := fun hγ => by
    obtain ⟨w, hw | hw⟩ := hpos hγ
    · exact ⟨g2LongestWeyl * w, Or.inl (by rw [mul_smul, hw, hneg hγ])⟩
    · exact ⟨g2LongestWeyl * w, Or.inr (by rw [mul_smul, hw, hneg hγ])⟩
  rcases g2_root_cases hδ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact hpos (Or.inl rfl)
  · exact hpos (Or.inr (Or.inl rfl))
  · exact hpos (Or.inr (Or.inr (Or.inl rfl)))
  · exact hpos (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact hpos (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact hpos (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  · exact hnegpos (Or.inl rfl)
  · exact hnegpos (Or.inr (Or.inl rfl))
  · exact hnegpos (Or.inr (Or.inr (Or.inl rfl)))
  · exact hnegpos (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact hnegpos (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact hnegpos (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

omit [CharP K 2] in
theorem inn_centralizer_le {H : Subgroup (ModGL .G2 K)} :
    inn (centralizer (H : Set (ModGL .G2 K))) ≤
      centralizer (inn H : Set (MulAut (adjointGroup .G2 K))) := by
  intro α hα
  obtain ⟨g, hg, rfl⟩ := mem_inn.1 hα
  rw [mem_centralizer_inn_iff]
  intro x hx
  refine Subtype.ext ?_
  rw [MulAut.conj_apply, coe_mul, coe_mul, coe_inv, ← mem_centralizer_iff.1 hg _ hx]
  group

theorem yamada_3_19_1 {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {δ : Fin Tag.G2.rank → ℤ} (hδ : IsRoot .G2 δ) :
    centralizer (inn (rootSubgroup .G2 K δ) : Set (MulAut (adjointGroup .G2 K))) =
      inn (centralizer (rootSubgroup .G2 K δ : Set (ModGL .G2 K))) := by
  refine le_antisymm (fun α hα => ?_) inn_centralizer_le
  rw [mem_centralizer_inn_iff] at hα
  obtain ⟨w, hw⟩ := exists_weyl_smul_eq hδ
  set m : adjointGroup .G2 K :=
    ⟨canonicalRep (coxeterSystem .G2) K w, canonicalRep_mem_adjointGroup _ K w⟩ with hm
  obtain ⟨s, hs, hcent, hconj⟩ : ∃ s : Fin Tag.G2.rank → ℤ, IsRoot .G2 s ∧
      (adjointGroup .G2 K ⊓ centralizer {pinnedX .G2 K s 1} ≤
        centralizer (rootSubgroup .G2 K s : Set (ModGL .G2 K))) ∧
      ∀ c : K, (m : ModGL .G2 K) * pinnedX .G2 K s c * (m : ModGL .G2 K)⁻¹ =
        pinnedX .G2 K δ c := by
    rcases hw with hw | hw
    · exact ⟨g2c, isRoot_g2c, centralizer_pinnedX_c_le, fun c => by
        rw [hm, canonicalRep_conj w isRoot_g2c, hw]⟩
    · exact ⟨g2v, isRoot_g2v, centralizer_pinnedX_v_le, fun c => by
        rw [hm, canonicalRep_conj w isRoot_g2v, hw]⟩
  have hβ : ∀ x : adjointGroup .G2 K, (x : ModGL .G2 K) ∈ rootSubgroup .G2 K s →
      ((MulAut.conj m)⁻¹ * α * MulAut.conj m) x = x := by
    intro x hx
    obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hx
    have hmx : (m * x * m⁻¹ : adjointGroup .G2 K) = ⟨pinnedX .G2 K δ c,
        pinnedX_mem_adjointGroup δ c⟩ := Subtype.ext (by
      rw [coe_mul, coe_mul, coe_inv, ← hc, hconj c])
    have hfix := hα (m * x * m⁻¹) (by rw [hmx]; exact mem_rootSubgroup.2 ⟨c, rfl⟩)
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hfix, MulAut.inv_apply,
      MulAut.conj_symm_apply]
    group
  obtain ⟨g, hg, hge⟩ := exists_eq_conj_of_fix_rootSubgroup hK hn hcent hβ
  have hα' : α = MulAut.conj (m * g * m⁻¹) := by
    rw [map_mul, map_mul, map_inv, ← hge]
    group
  rw [hα']
  refine conj_mem_inn (mem_centralizer_iff.2 fun y hy => ?_)
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hy
  rw [← hconj c]
  have := mem_centralizer_iff.1 hg _ (mem_rootSubgroup.2 ⟨c, rfl⟩)
  simp only [coe_mul, coe_inv]
  calc (m : ModGL .G2 K) * pinnedX .G2 K s c * (m : ModGL .G2 K)⁻¹ *
      ((m : ModGL .G2 K) * g * (m : ModGL .G2 K)⁻¹) =
      m * (pinnedX .G2 K s c * g) * (m : ModGL .G2 K)⁻¹ := by group
    _ = m * (g * pinnedX .G2 K s c) * (m : ModGL .G2 K)⁻¹ := by rw [this]
    _ = (m : ModGL .G2 K) * g * (m : ModGL .G2 K)⁻¹ *
      ((m : ModGL .G2 K) * pinnedX .G2 K s c * (m : ModGL .G2 K)⁻¹) := by group

theorem coe_fieldAut_pow_torus (k : ℕ) (t₁ t₂ : Kˣ)
    (h : torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ ∈ adjointGroup .G2 K) :
    (((fieldAut K ^ k) ⟨_, h⟩ : adjointGroup .G2 K) : ModGL .G2 K) =
      torusElt .G2 K g2ia (t₁ ^ 2 ^ k) * torusElt .G2 K g2ir (t₂ ^ 2 ^ k) := by
  have e : (⟨_, h⟩ : adjointGroup .G2 K) =
      ⟨torusElt .G2 K g2ia t₁, torusElt_mem_adjointGroup g2ia t₁⟩ *
        ⟨torusElt .G2 K g2ir t₂, torusElt_mem_adjointGroup g2ir t₂⟩ := rfl
  rw [e, map_mul, coe_mul, fieldAut_pow_torusElt, fieldAut_pow_torusElt]

theorem eq_zero_of_fieldAut_pow_fix_torus {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {k : ℕ} (hk : k < n) {p₁ p₂ m₁ m₂ : ℤ} {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot .G2 γ)
    (h₁ : ∑ j, Tag.G2.cartan g2ia j * γ j = m₁) (h₂ : ∑ j, Tag.G2.cartan g2ir j * γ j = m₂)
    (he : p₁ * m₁ + p₂ * m₂ = 1)
    (hfix : ∀ t : Kˣ, ∀ h : torusElt .G2 K g2ia (t ^ p₁) * torusElt .G2 K g2ir (t ^ p₂) ∈
      adjointGroup .G2 K, (fieldAut K ^ k) ⟨_, h⟩ = ⟨_, h⟩) : k = 0 := by
  refine eq_zero_of_forall_pow_eq hK hn hk fun c => ?_
  by_cases hc : c = 0
  · rw [hc, zero_pow (by positivity)]
  set t := Units.mk0 c hc with ht
  have hmem := mul_mem (torusElt_mem_adjointGroup (K := K) g2ia (t ^ p₁))
    (torusElt_mem_adjointGroup (K := K) g2ir (t ^ p₂))
  have h1 := congrArg Subtype.val (hfix t hmem)
  rw [coe_fieldAut_pow_torus] at h1
  have h2 := torus_conj_of hγ ((t ^ p₁) ^ 2 ^ k) ((t ^ p₂) ^ 2 ^ k) h₁ h₂ 1
  rw [h1, torus_conj_of hγ _ _ h₁ h₂ 1] at h2
  have h3 := pinnedX_injective .G2 K γ h2
  rw [mul_one, mul_one] at h3
  have h4 : (t ^ p₁) ^ m₁ * (t ^ p₂) ^ m₂ =
      ((t ^ p₁) ^ 2 ^ k) ^ m₁ * ((t ^ p₂) ^ 2 ^ k) ^ m₂ := Units.ext h3
  have e1 : (t ^ p₁) ^ m₁ * (t ^ p₂) ^ m₂ = t := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, he, zpow_one]
  have e2 : ((t ^ p₁) ^ 2 ^ k) ^ m₁ * ((t ^ p₂) ^ 2 ^ k) ^ m₂ = t ^ 2 ^ k := by
    rw [← zpow_natCast, ← zpow_natCast (t ^ p₂), ← zpow_mul, ← zpow_mul, ← zpow_mul,
      ← zpow_mul, ← zpow_add, ← zpow_natCast]
    congr 1
    push_cast
    linear_combination ((2 : ℤ) ^ k) * he
  rw [e1, e2] at h4
  have h5 := congrArg Units.val h4
  rw [Units.val_pow_eq_pow_val, ht, Units.val_mk0] at h5
  exact h5.symm

theorem zpowers_inf_centralizer_torusFix {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {s γ : Fin Tag.G2.rank → ℤ} (hs : IsRoot .G2 s) (hγ : IsRoot .G2 γ)
    {p₁ p₂ c₁ c₂ m₁ m₂ : ℤ} (hc₁ : ∑ j, Tag.G2.cartan g2ia j * s j = c₁)
    (hc₂ : ∑ j, Tag.G2.cartan g2ir j * s j = c₂) (hc : p₁ * c₁ + p₂ * c₂ = 0)
    (h₁ : ∑ j, Tag.G2.cartan g2ia j * γ j = m₁) (h₂ : ∑ j, Tag.G2.cartan g2ir j * γ j = m₂)
    (he : p₁ * m₁ + p₂ * m₂ = 1) :
    zpowers (fieldAut K) ⊓ centralizer (inn (torusFix K s) : Set (MulAut (adjointGroup .G2 K))) =
      ⊥ := by
  refine eq_bot_iff.2 fun α hα => ?_
  obtain ⟨hα₁, hα₂⟩ := mem_inf.1 hα
  obtain ⟨k, hk, rfl⟩ := exists_eq_fieldAut_pow_of_mem_zpowers hK hn hα₁
  rw [mem_centralizer_inn_iff] at hα₂
  have hk0 : k = 0 := eq_zero_of_fieldAut_pow_fix_torus hK hn hk hγ h₁ h₂ he fun t h =>
    hα₂ _ (mem_torusFix_of hs (t ^ p₁) (t ^ p₂) hc₁ hc₂ (by
      rw [← zpow_mul, ← zpow_mul, ← zpow_add, hc, zpow_zero]))
  rw [hk0, pow_zero]
  exact one_mem _

theorem yamada_3_19_2 {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    zpowers (fieldAut K) ⊓ centralizer (inn (J₁ K) : Set (MulAut (adjointGroup .G2 K))) = ⊥ ∧
      zpowers (fieldAut K) ⊓ centralizer (inn (J₂ K) : Set (MulAut (adjointGroup .G2 K))) = ⊥ ∧
      zpowers (fieldAut K) ⊓ centralizer (inn (J₃ K) : Set (MulAut (adjointGroup .G2 K))) = ⊥ ∧
      zpowers (fieldAut K) ⊓ centralizer (inn (J₄ K) : Set (MulAut (adjointGroup .G2 K))) = ⊥ ∧
      zpowers (fieldAut K) ⊓ centralizer (inn (J₅ K) : Set (MulAut (adjointGroup .G2 K))) = ⊥ ∧
      zpowers (fieldAut K) ⊓ centralizer (inn (J₆ K) : Set (MulAut (adjointGroup .G2 K))) = ⊥ :=
  ⟨zpowers_inf_centralizer_torusFix (p₁ := 0) (p₂ := 1) (c₁ := 1) (c₂ := 0) (m₁ := 0) (m₂ := 1)
      hK hn isRoot_g2c isRoot_g2v (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
    zpowers_inf_centralizer_torusFix (p₁ := 1) (p₂ := 0) (c₁ := 0) (c₂ := 1) (m₁ := 1)
      (m₂ := -1) hK hn isRoot_g2v isRoot_g2u (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    zpowers_inf_centralizer_torusFix (p₁ := 2) (p₂ := 1) (c₁ := -1) (c₂ := 2) (m₁ := 2)
      (m₂ := -3) hK hn isRoot_g2r isRoot_g2a (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    zpowers_inf_centralizer_torusFix (p₁ := 3) (p₂ := 2) (c₁ := 2) (c₂ := -3) (m₁ := -1)
      (m₂ := 2) hK hn isRoot_g2a isRoot_g2r (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    zpowers_inf_centralizer_torusFix (p₁ := 3) (p₂ := 1) (c₁ := -1) (c₂ := 3) (m₁ := 0)
      (m₂ := 1) hK hn isRoot_g2b isRoot_g2v (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    zpowers_inf_centralizer_torusFix (p₁ := 1) (p₂ := 1) (c₁ := 1) (c₂ := -1) (m₁ := -1)
      (m₂ := 2) hK hn isRoot_g2u isRoot_g2r (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)⟩

end Centralizers

section Coordinates

variable
  {K : Type} [Field K]

theorem units_map_entrywise_g2N (σ : K ≃+* K) (A B C D E F : K) :
    Units.map (entrywiseHom σ.toRingHom) (g2N A B C D E F) =
      g2N (σ A) (σ B) (σ C) (σ D) (σ E) (σ F) := by
  simp only [g2N, map_mul, units_map_entrywise_pinnedX]

theorem map_entrywise_of_g2N {H : Subgroup (ModGL .G2 K)} (hHS : ∀ x ∈ H,
      ∃ A B C D E F : K, x = g2N A B C D E F) (σ : K ≃+* K)
    (hH : ∀ A B C D E F : K, g2N A B C D E F ∈ H →
      g2N (σ A) (σ B) (σ C) (σ D) (σ E) (σ F) ∈ H)
    (hH' : ∀ A B C D E F : K, g2N A B C D E F ∈ H →
      g2N (σ.symm A) (σ.symm B) (σ.symm C) (σ.symm D) (σ.symm E) (σ.symm F) ∈ H) :
    H.map (Units.map (entrywiseHom σ.toRingHom)) = H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨A, B, C, D, E, F, rfl⟩ := hHS x hx
    rw [units_map_entrywise_g2N]
    exact hH A B C D E F hx
  · intro x hx
    obtain ⟨A, B, C, D, E, F, rfl⟩ := hHS x hx
    refine ⟨_, hH' A B C D E F hx, ?_⟩
    rw [units_map_entrywise_g2N]
    simp only [RingEquiv.apply_symm_apply]

theorem coords_of_mem {H : Subgroup (ModGL .G2 K)} (h : H ≤ S K) :
    ∀ x ∈ H, ∃ A B C D E F : K, x = g2N A B C D E F := fun _ hx => mem_S.1 (h hx)

variable [CharP K 2]

theorem map_entrywise_U (σ : K ≃+* K) :
    (U K).map (Units.map (entrywiseHom σ.toRingHom)) = U K :=
  map_entrywise_of_g2N (coords_of_mem U_le_S) σ
    (fun A B C D E F h => by
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := g2N_mem_U_iff.1 h
      simp only [map_zero]
      exact g2N_mem_U_iff.2 ⟨rfl, rfl, rfl, rfl, rfl⟩)
    fun A B C D E F h => by
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := g2N_mem_U_iff.1 h
      simp only [map_zero]
      exact g2N_mem_U_iff.2 ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem map_entrywise_Y (σ : K ≃+* K) :
    (Y K).map (Units.map (entrywiseHom σ.toRingHom)) = Y K :=
  map_entrywise_of_g2N (coords_of_mem Y_le_S) σ
    (fun A B C D E F h => by
      obtain ⟨rfl, rfl, rfl, rfl⟩ := g2N_mem_Y_iff.1 h
      simp only [map_zero]
      exact g2N_mem_Y_iff.2 ⟨rfl, rfl, rfl, rfl⟩)
    fun A B C D E F h => by
      obtain ⟨rfl, rfl, rfl, rfl⟩ := g2N_mem_Y_iff.1 h
      simp only [map_zero]
      exact g2N_mem_Y_iff.2 ⟨rfl, rfl, rfl, rfl⟩

theorem map_entrywise_X (σ : K ≃+* K) :
    (X K).map (Units.map (entrywiseHom σ.toRingHom)) = X K :=
  map_entrywise_of_g2N (coords_of_mem X_le_S) σ
    (fun A B C D E F h => by
      obtain ⟨rfl, rfl, rfl⟩ := g2N_mem_X_iff.1 h
      simp only [map_zero]
      exact g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩)
    fun A B C D E F h => by
      obtain ⟨rfl, rfl, rfl⟩ := g2N_mem_X_iff.1 h
      simp only [map_zero]
      exact g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩

theorem map_entrywise_W (σ : K ≃+* K) :
    (W K).map (Units.map (entrywiseHom σ.toRingHom)) = W K :=
  map_entrywise_of_g2N (coords_of_mem W_le_S) σ
    (fun A B C D E F h => by
      obtain ⟨rfl, rfl, rfl⟩ := g2N_mem_W_iff.1 h
      simp only [map_zero]
      exact g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩)
    fun A B C D E F h => by
      obtain ⟨rfl, rfl, rfl⟩ := g2N_mem_W_iff.1 h
      simp only [map_zero]
      exact g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩

theorem map_entrywise_F (σ : K ≃+* K) :
    (Model.F K).map (Units.map (entrywiseHom σ.toRingHom)) = Model.F K :=
  map_entrywise_of_g2N (coords_of_mem F_le_S) σ
    (fun A B C D E F h => by
      obtain ⟨rfl, rfl⟩ := g2N_mem_F_iff.1 h
      simp only [map_zero]
      exact g2N_mem_F_iff.2 ⟨rfl, rfl⟩)
    fun A B C D E F h => by
      obtain ⟨rfl, rfl⟩ := g2N_mem_F_iff.1 h
      simp only [map_zero]
      exact g2N_mem_F_iff.2 ⟨rfl, rfl⟩

theorem map_entrywise_D (σ : K ≃+* K) :
    (Model.D K).map (Units.map (entrywiseHom σ.toRingHom)) = Model.D K :=
  map_entrywise_of_g2N (coords_of_mem D_le_S) σ
    (fun A B C D E F h => by
      obtain rfl := g2N_mem_D_iff.1 h
      simp only [map_zero]
      exact g2N_mem_D_iff.2 rfl)
    fun A B C D E F h => by
      obtain rfl := g2N_mem_D_iff.1 h
      simp only [map_zero]
      exact g2N_mem_D_iff.2 rfl

theorem map_entrywise_M (σ : K ≃+* K) :
    (M K).map (Units.map (entrywiseHom σ.toRingHom)) = M K :=
  map_entrywise_of_g2N (coords_of_mem M_le_S) σ
    (fun A B C D E F h => by
      obtain rfl := g2N_mem_M_iff.1 h
      simp only [map_zero]
      exact g2N_mem_M_iff.2 rfl)
    fun A B C D E F h => by
      obtain rfl := g2N_mem_M_iff.1 h
      simp only [map_zero]
      exact g2N_mem_M_iff.2 rfl

omit [CharP K 2] in
theorem map_entrywise_S (σ : K ≃+* K) :
    (S K).map (Units.map (entrywiseHom σ.toRingHom)) = S K :=
  map_entrywise_of_g2N (coords_of_mem le_rfl) σ
    (fun _ _ _ _ _ _ _ => g2N_mem_posUnipotent _ _ _ _ _ _)
    fun _ _ _ _ _ _ _ => g2N_mem_posUnipotent _ _ _ _ _ _

end Coordinates

section FieldInvolution

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem orderOf_fieldAut_pow_half {e : ℕ} (hK : Nat.card K = 2 ^ (2 * e)) (he : 1 ≤ e) :
    orderOf (fieldAut K ^ e) = 2 := by
  have hn : 2 ≤ 2 * e := by omega
  rw [orderOf_pow_of_dvd (by omega) ⟨2, by rw [orderOf_fieldAut hK hn]; ring⟩,
    orderOf_fieldAut hK hn]
  exact Nat.mul_div_cancel _ (by omega)

theorem fieldAut_pow_half_not_mem_inner {e : ℕ} (hK : Nat.card K = 2 ^ (2 * e)) (he : 1 ≤ e) :
    fieldAut K ^ e ∉ inner (adjointGroup .G2 K) := by
  rw [fieldAut_pow_mem_inner_iff hK (by omega)]
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

theorem exists_inner_conj_eq_of_outer {e : ℕ} (hK : Nat.card K = 2 ^ (2 * e)) (he : 1 ≤ e)
    {x : MulAut (adjointGroup .G2 K)} (hx : orderOf x = 2)
    (hxL : x ∉ inner (adjointGroup .G2 K)) :
    ∃ w ∈ inner (adjointGroup .G2 K), x = w⁻¹ * fieldAut K ^ e * w := by
  rcases even_G2_involution_inner_or_canonical_field (by omega : 2 ≤ 2 * e) K hK x hx with
    h | ⟨-, hcan⟩
  · exact absurd h hxL
  obtain ⟨β, ψ, hβ, hψ, -⟩ := hcan (frobeniusEquiv K 2 ^ e).toRingHom fun c => by
    rw [show 2 * e / 2 = e by omega]
    exact frobeniusEquiv_pow_apply e c
  have hβf : β = fieldAut K ^ e :=
    MulEquiv.ext fun u => Subtype.ext (by rw [hβ u, coe_fieldAut_pow_apply])
  obtain ⟨g, j, -, rfl⟩ := exists_eq_conj_mul_fieldAut_pow hK (by omega) ψ
  refine ⟨(fieldAut K ^ j)⁻¹ * MulAut.conj g * fieldAut K ^ j, ?_, ?_⟩
  · have := (inner_normal (adjointGroup .G2 K)).conj_mem _ ⟨g, rfl⟩ (fieldAut K ^ j)⁻¹
    rwa [inv_inv] at this
  · have hx' : x = (MulAut.conj g * fieldAut K ^ j)⁻¹ * fieldAut K ^ e *
        (MulAut.conj g * fieldAut K ^ j) := by
      rw [← hβf, ← hψ]
      group
    have hc : fieldAut K ^ j * fieldAut K ^ e * (fieldAut K ^ j)⁻¹ = fieldAut K ^ e := by
      rw [← pow_add, add_comm, pow_add, mul_inv_cancel_right]
    rw [hx']
    calc (MulAut.conj g * fieldAut K ^ j)⁻¹ * fieldAut K ^ e * (MulAut.conj g * fieldAut K ^ j) =
        (fieldAut K ^ j)⁻¹ * (MulAut.conj g)⁻¹ * fieldAut K ^ e * MulAut.conj g *
          fieldAut K ^ j := by group
      _ = (fieldAut K ^ j)⁻¹ * (MulAut.conj g)⁻¹ *
          (fieldAut K ^ j * fieldAut K ^ e * (fieldAut K ^ j)⁻¹) * MulAut.conj g *
            fieldAut K ^ j := by rw [hc]
      _ = ((fieldAut K ^ j)⁻¹ * MulAut.conj g * fieldAut K ^ j)⁻¹ * fieldAut K ^ e *
          ((fieldAut K ^ j)⁻¹ * MulAut.conj g * fieldAut K ^ j) := by group

theorem outer_involutions_eq {e : ℕ} (hK : Nat.card K = 2 ^ (2 * e)) (he : 1 ≤ e) :
    {x : MulAut (adjointGroup .G2 K) | x ∉ inner (adjointGroup .G2 K) ∧ orderOf x = 2} =
      {x | ∃ w ∈ inner (adjointGroup .G2 K), x = w⁻¹ * fieldAut K ^ e * w} := by
  ext x
  constructor
  · rintro ⟨hxL, hx⟩
    exact exists_inner_conj_eq_of_outer hK he hx hxL
  · rintro ⟨w, hw, rfl⟩
    refine ⟨fun h => fieldAut_pow_half_not_mem_inner hK he ?_, ?_⟩
    · have := (inner_normal (adjointGroup .G2 K)).conj_mem _ h w
      rwa [show w * (w⁻¹ * fieldAut K ^ e * w) * w⁻¹ = fieldAut K ^ e by group] at this
    · rw [orderOf_inv_mul_mul, orderOf_fieldAut_pow_half hK he]

theorem inn_inf_centralizer_fieldAut_pow (H : Subgroup (ModGL .G2 K)) (k : ℕ) :
    inn H ⊓ centralizer {fieldAut K ^ k} =
      inn (H ⊓ entrywiseFixedGroup .G2 (frobeniusEquiv K 2 ^ k)) := by
  ext α
  constructor
  · rintro ⟨hα₁, hα₂⟩
    obtain ⟨g, hg, rfl⟩ := mem_inn.1 hα₁
    have h1 := mem_centralizer_singleton_iff.1 hα₂
    rw [mulAut_mul_conj] at h1
    have h2 : (fieldAut K ^ k) g = g := conj_injective (mul_right_cancel h1).symm
    refine conj_mem_inn ⟨hg, mem_entrywiseFixedGroup.2 ⟨g.2, ?_⟩⟩
    rw [← coe_fieldAut_pow_apply, h2]
  · intro hα
    obtain ⟨g, ⟨hg, hgΓ⟩, rfl⟩ := mem_inn.1 hα
    refine ⟨conj_mem_inn hg, mem_centralizer_singleton_iff.2 ?_⟩
    have h2 : (fieldAut K ^ k) g = g := Subtype.ext (by
      rw [coe_fieldAut_pow_apply]
      exact (mem_entrywiseFixedGroup.1 hgΓ).2)
    rw [mulAut_mul_conj, h2]

omit
  [CharP K 2] in
theorem card_inf_entrywiseFixedGroup {H : Subgroup (ModGL .G2 K)} (hHC : H ≤ adjointGroup .G2 K)
    {d : ℕ} (σ : K ≃+* K) (φ : (Fin d → K) → ModGL .G2 K) (hφ : Function.Injective φ)
    (hH : ∀ g, g ∈ H ↔ ∃ v, φ v = g)
    (hσ : ∀ v, Units.map (entrywiseHom σ.toRingHom) (φ v) = φ fun i => σ (v i)) :
    Nat.card (H ⊓ entrywiseFixedGroup .G2 σ : Subgroup (ModGL .G2 K)) =
      Nat.card (fixSubfield σ) ^ d := by
  refine card_eq_of_param (fun w : Fin d → fixSubfield σ => φ fun i => (w i : K))
    (fun w w' h => funext fun i => Subtype.ext (congrFun (hφ h) i)) fun g => ?_
  constructor
  · rintro ⟨hgH, hgΓ⟩
    obtain ⟨v, rfl⟩ := (hH g).1 hgH
    have h1 := (mem_entrywiseFixedGroup.1 hgΓ).2
    rw [hσ] at h1
    have h2 := hφ h1
    exact ⟨fun i => ⟨v i, congrFun h2 i⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    have hmem : (φ fun i => (w i : K)) ∈ H := (hH _).2 ⟨_, rfl⟩
    refine ⟨hmem, mem_entrywiseFixedGroup.2 ⟨hHC hmem, ?_⟩⟩
    rw [hσ]
    congr 1
    funext i
    exact (w i).2

theorem card_inn_inf_centralizer_sq {e : ℕ} (hK : Nat.card K = 2 ^ (2 * e)) (he : 1 ≤ e)
    {H : Subgroup (ModGL .G2 K)} (hHC : H ≤ adjointGroup .G2 K) {d : ℕ}
    (φ : (Fin d → K) → ModGL .G2 K) (hφ : Function.Injective φ)
    (hH : ∀ g, g ∈ H ↔ ∃ v, φ v = g)
    (hσ : ∀ v, Units.map (entrywiseHom (frobeniusEquiv K 2 ^ e).toRingHom) (φ v) =
      φ fun i => (frobeniusEquiv K 2 ^ e) (v i)) :
    Nat.card (inn H ⊓ centralizer {fieldAut K ^ e} : Subgroup (MulAut (adjointGroup .G2 K))) ^ 2 =
      Nat.card (inn H) := by
  have hk := (even_G2_canonical_field_full_centralizer he K hK (frobeniusEquiv K 2 ^ e)
    (frobeniusEquiv_pow_apply e)).2.1
  rw [inn_inf_centralizer_fieldAut_pow, card_inn (inf_le_left.trans hHC), card_inn hHC,
    card_inf_entrywiseFixedGroup hHC _ φ hφ hH hσ, card_eq_of_param φ hφ hH, hk, hK, ← pow_mul,
    ← pow_mul, ← pow_mul]
  ring_nf

theorem centralizer_fieldAut_half_mulEquiv {e : ℕ} (hK : Nat.card K = 2 ^ (2 * e))
    (he : 1 ≤ e) :
    ∃ (k : Type) (_ : Field k), Nat.card k = 2 ^ e ∧
      Nonempty ((inner (adjointGroup .G2 K) ⊓ centralizer {fieldAut K ^ e} :
        Subgroup (MulAut (adjointGroup .G2 K))) ≃* adjointGroup .G2 k) := by
  set σ := frobeniusEquiv K 2 ^ e with hσ
  obtain ⟨-, hk, -, hfix, -⟩ :=
    even_G2_canonical_field_full_centralizer he K hK σ (frobeniusEquiv_pow_apply e)
  have hδ : fieldAut K ^ e = entrywiseAdjointAut .G2 σ := fieldAut_pow e
  set E₀ := (entrywiseAdjointAut .G2 σ).toMonoidHom.eqLocus
    (MonoidHom.id (adjointGroup .G2 K)) with hE₀
  have h1 : E₀.map (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) =
      inner (adjointGroup .G2 K) ⊓ centralizer {fieldAut K ^ e} := by
    ext α
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
      have hg' : (fieldAut K ^ e) g = g := by
        rw [hδ]
        exact hg
      rw [mulAut_mul_conj, hg']
    · rintro ⟨⟨g, rfl⟩, hc⟩
      have h2 := mem_centralizer_singleton_iff.1 hc
      rw [mulAut_mul_conj] at h2
      have h3 : (fieldAut K ^ e) g = g := conj_injective (mul_right_cancel h2).symm
      refine ⟨g, ?_, rfl⟩
      show (entrywiseAdjointAut .G2 σ) g = g
      rw [← hδ]
      exact h3
  refine ⟨fixSubfield σ, inferInstance, hk, ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr h1).symm.trans
    ((E₀.equivMapOfInjective _ conj_injective).symm.trans
      ((E₀.equivMapOfInjective _ Subtype.val_injective).trans
        ((MulEquiv.subgroupCongr hfix).trans
          ((adjointGroup .G2 (fixSubfield σ)).equivMapOfInjective _
            (baseChangeGL_injective _)).symm)))

end FieldInvolution

section Coset

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2] {e : ℕ}

theorem card_sq_U (hK : Nat.card K = 2 ^ (2 * e)) (he : 1 ≤ e) :
    Nat.card (inn (U K) ⊓ centralizer {fieldAut K ^ e} :
      Subgroup (MulAut (adjointGroup .G2 K))) ^ 2 = Nat.card (inn (U K)) :=
  card_inn_inf_centralizer_sq (d := 1) hK he (U_le_adjointGroup K) (fun v => g2N 0 0 0 0 0 (v 0))
    (g2N_comp_injective _ _ _ _ _ _ fun v w _ _ _ _ _ h6 => funext fun i => by
      fin_cases i
      exact h6)
    (fun g => by
      rw [mem_U]
      exact ⟨fun ⟨F, h⟩ => ⟨![F], h.symm⟩, fun ⟨v, h⟩ => ⟨v 0, h.symm⟩⟩)
    fun v => by rw [units_map_entrywise_g2N]; simp only [map_zero]

theorem card_sq_Y (hK : Nat.card K = 2 ^ (2 * e)) (he : 1 ≤ e) :
    Nat.card (inn (Y K) ⊓ centralizer {fieldAut K ^ e} :
      Subgroup (MulAut (adjointGroup .G2 K))) ^ 2 = Nat.card (inn (Y K)) :=
  card_inn_inf_centralizer_sq (d := 2) hK he Y_le_adjointGroup (fun v => g2N 0 0 0 0 (v 0) (v 1))
    (g2N_comp_injective _ _ _ _ _ _ fun v w _ _ _ _ h5 h6 => funext fun i => by
      fin_cases i
      exacts [h5, h6])
    (fun g => by
      rw [mem_Y]
      exact ⟨fun ⟨E, F, h⟩ => ⟨![E, F], h.symm⟩, fun ⟨v, h⟩ => ⟨v 0, v 1, h.symm⟩⟩)
    fun v => by rw [units_map_entrywise_g2N]; simp only [map_zero]

theorem card_sq_W (hK : Nat.card K = 2 ^ (2 * e)) (he : 1 ≤ e) :
    Nat.card (inn (W K) ⊓ centralizer {fieldAut K ^ e} :
      Subgroup (MulAut (adjointGroup .G2 K))) ^ 2 = Nat.card (inn (W K)) :=
  card_inn_inf_centralizer_sq (d := 3) hK he W_le_adjointGroup
    (fun v => g2N 0 0 0 (v 0) (v 1) (v 2))
    (g2N_comp_injective _ _ _ _ _ _ fun v w _ _ _ h4 h5 h6 => funext fun i => by
      fin_cases i
      exacts [h4, h5, h6])
    (fun g => by
      rw [mem_W]
      exact ⟨fun ⟨D, E, F, h⟩ => ⟨![D, E, F], h.symm⟩, fun ⟨v, h⟩ => ⟨v 0, v 1, v 2, h.symm⟩⟩)
    fun v => by rw [units_map_entrywise_g2N]; simp only [map_zero]

theorem card_sq_F (hK : Nat.card K = 2 ^ (2 * e)) (he : 1 ≤ e) :
    Nat.card (inn (Model.F K) ⊓ centralizer {fieldAut K ^ e} :
      Subgroup (MulAut (adjointGroup .G2 K))) ^ 2 = Nat.card (inn (Model.F K)) :=
  card_inn_inf_centralizer_sq (d := 4) hK he F_le_adjointGroup
    (fun v => g2N 0 0 (v 0) (v 1) (v 2) (v 3))
    (g2N_comp_injective _ _ _ _ _ _ fun v w _ _ h3 h4 h5 h6 => funext fun i => by
      fin_cases i
      exacts [h3, h4, h5, h6])
    (fun g => by
      rw [mem_F]
      exact ⟨fun ⟨C, D, E, F, h⟩ => ⟨![C, D, E, F], h.symm⟩,
        fun ⟨v, h⟩ => ⟨v 0, v 1, v 2, v 3, h.symm⟩⟩)
    fun v => by rw [units_map_entrywise_g2N]; simp only [map_zero]

theorem card_sq_D (hK : Nat.card K = 2 ^ (2 * e)) (he : 1 ≤ e) :
    Nat.card (inn (Model.D K) ⊓ centralizer {fieldAut K ^ e} :
      Subgroup (MulAut (adjointGroup .G2 K))) ^ 2 = Nat.card (inn (Model.D K)) :=
  card_inn_inf_centralizer_sq (d := 5) hK he D_le_adjointGroup
    (fun v => g2N 0 (v 0) (v 1) (v 2) (v 3) (v 4))
    (g2N_comp_injective _ _ _ _ _ _ fun v w _ h2 h3 h4 h5 h6 => funext fun i => by
      fin_cases i
      exacts [h2, h3, h4, h5, h6])
    (fun g => by
      rw [mem_D]
      exact ⟨fun ⟨B, C, D, E, F, h⟩ => ⟨![B, C, D, E, F], h.symm⟩,
        fun ⟨v, h⟩ => ⟨v 0, v 1, v 2, v 3, v 4, h.symm⟩⟩)
    fun v => by rw [units_map_entrywise_g2N]; simp only [map_zero]

theorem card_sq_S (hK : Nat.card K = 2 ^ (2 * e)) (he : 1 ≤ e) :
    Nat.card (inn (S K) ⊓ centralizer {fieldAut K ^ e} :
      Subgroup (MulAut (adjointGroup .G2 K))) ^ 2 = Nat.card (inn (S K)) :=
  card_inn_inf_centralizer_sq (d := 6) hK he (S_le_adjointGroup K)
    (fun v => g2N (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))
    (g2N_comp_injective _ _ _ _ _ _ fun v w h1 h2 h3 h4 h5 h6 => funext fun i => by
      fin_cases i
      exacts [h1, h2, h3, h4, h5, h6])
    (fun g => by
      rw [mem_S]
      exact ⟨fun ⟨A, B, C, D, E, F, h⟩ => ⟨![A, B, C, D, E, F], h.symm⟩,
        fun ⟨v, h⟩ => ⟨v 0, v 1, v 2, v 3, v 4, v 5, h.symm⟩⟩)
    fun v => by rw [units_map_entrywise_g2N]

theorem involutions_fieldAut_coset (hK : Nat.card K = 2 ^ (2 * e)) (he : 1 ≤ e) :
    {x : MulAut (adjointGroup .G2 K) |
        (∃ w ∈ inn (S K), x = fieldAut K ^ e * w) ∧ orderOf x = 2} =
      {x | ∃ w ∈ inn (S K), x = w⁻¹ * fieldAut K ^ e * w} := by
  have : Finite (MulAut (adjointGroup .G2 K)) := MulEquiv.finite_left
  let ch : Fin 7 → Subgroup (ModGL .G2 K) := ![⊥, U K, Y K, W K, Model.F K, Model.D K, S K]
  let V : Fin 7 → Subgroup (MulAut (adjointGroup .G2 K)) := fun i => inn (ch i)
  have hnorm : ∀ i : Fin 6, ch i.succ ≤ normalizer (ch i.castSucc : Set (ModGL .G2 K)) := by
    intro i
    fin_cases i
    · exact le_normalizer_of_conj_mem fun x _ y hy => by
        rw [mem_bot.1 hy, mul_one, mul_inv_cancel]
        exact one_mem _
    · exact Y_le_S.trans S_le_normalizer_U
    · exact W_le_S.trans S_le_normalizer_Y
    · exact F_le_S.trans S_le_normalizer_W
    · exact D_le_S.trans S_le_normalizer_F
    · exact S_le_normalizer_D
  have : ∀ i : Fin 6, ((V i.castSucc).subgroupOf (V i.succ)).Normal := fun i =>
    inn_subgroupOf_normal (hnorm i)
  have hsq : ∀ i : Fin 6, ∀ x ∈ ch i.succ, x ∈ adjointGroup .G2 K → x * x ∈ ch i.castSucc := by
    intro i
    fin_cases i
    · intro x (hx : x ∈ U K) _
      have := U_isElementaryAbelian (K := K)
      rw [← sq, CFSG.elemPow_eq_one_of_isElementaryAbelian x hx]
      exact one_mem _
    · intro x (hx : x ∈ Y K) _
      have := Y_isElementaryAbelian (K := K)
      rw [← sq, CFSG.elemPow_eq_one_of_isElementaryAbelian x hx]
      exact one_mem (U K)
    · intro x (hx : x ∈ W K) _
      have := W_isElementaryAbelian (K := K)
      rw [← sq, CFSG.elemPow_eq_one_of_isElementaryAbelian x hx]
      exact one_mem (Y K)
    · intro x (hx : x ∈ Model.F K) _
      obtain ⟨C, D, E, F, rfl⟩ := mem_F.1 hx
      rw [g2N_mul_self]
      exact g2N_mem_W_iff.2 ⟨rfl, rfl, by ring⟩
    · intro x (hx : x ∈ Model.D K) _
      obtain ⟨B, C, D, E, F, rfl⟩ := mem_D.1 hx
      rw [g2N_mul_self]
      exact g2N_mem_F_iff.2 ⟨rfl, rfl⟩
    · intro x (hx : x ∈ S K) _
      obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hx
      rw [g2N_mul_self]
      exact g2N_mem_D_iff.2 rfl
  have : ∀ i : Fin 6,
      CFSG.IsElementaryAbelian 2 (V i.succ ⧸ (V i.castSucc).subgroupOf (V i.succ)) :=
    fun i => inn_quotient_isElementaryAbelian (hsq i)
  refine Common.involution_coset_eq_conj_orbit_of_card_sq (orderOf_fieldAut_pow_half hK he) V
    inn_bot rfl (fun i => inn_mono ?_) (fun i => ?_) fun i => ?_
  · fin_cases i
    exacts [bot_le, U_le_Y, Y_le_W, W_le_F, F_le_D, D_le_S]
  · fin_cases i
    · exact fieldAut_pow_mem_normalizer_inn bot_le (fun k => Subgroup.map_bot _) e
    · exact fieldAut_pow_mem_normalizer_inn (U_le_adjointGroup K) (fun k => map_entrywise_U _) e
    · exact fieldAut_pow_mem_normalizer_inn Y_le_adjointGroup (fun k => map_entrywise_Y _) e
    · exact fieldAut_pow_mem_normalizer_inn W_le_adjointGroup (fun k => map_entrywise_W _) e
    · exact fieldAut_pow_mem_normalizer_inn F_le_adjointGroup (fun k => map_entrywise_F _) e
    · exact fieldAut_pow_mem_normalizer_inn D_le_adjointGroup (fun k => map_entrywise_D _) e
    · exact fieldAut_pow_mem_normalizer_inn (S_le_adjointGroup K) (fun k => map_entrywise_S _) e
  · fin_cases i
    exacts [card_sq_U hK he, card_sq_Y hK he, card_sq_W hK he, card_sq_F hK he, card_sq_D hK he,
      card_sq_S hK he]

theorem yamada_3_20 (hK : Nat.card K = 2 ^ (2 * e)) (he : 1 ≤ e) :
    orderOf (fieldAut K ^ e) = 2 ∧ fieldAut K ^ e ∉ inner (adjointGroup .G2 K) ∧
      {x : MulAut (adjointGroup .G2 K) |
          (∃ w ∈ inn (S K), x = fieldAut K ^ e * w) ∧ orderOf x = 2} =
        {x | ∃ w ∈ inn (S K), x = w⁻¹ * fieldAut K ^ e * w} ∧
      {x : MulAut (adjointGroup .G2 K) | x ∉ inner (adjointGroup .G2 K) ∧ orderOf x = 2} =
        {x | ∃ w ∈ inner (adjointGroup .G2 K), x = w⁻¹ * fieldAut K ^ e * w} ∧
      ∃ (k : Type) (_ : Field k), Nat.card k = 2 ^ e ∧
        Nonempty ((inner (adjointGroup .G2 K) ⊓ centralizer {fieldAut K ^ e} :
          Subgroup (MulAut (adjointGroup .G2 K))) ≃* adjointGroup .G2 k) :=
  ⟨orderOf_fieldAut_pow_half hK he, fieldAut_pow_half_not_mem_inner hK he,
    involutions_fieldAut_coset hK he, outer_involutions_eq hK he,
    centralizer_fieldAut_half_mulEquiv hK he⟩

end Coset

section Thompson

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

variable (K) in
@[expose] noncomputable def innData : G2Data (inner (adjointGroup .G2 K)) K :=
  ⟨(MonoidHom.ofInjective conj_injective).symm⟩

omit [CharP K 2] in
theorem innData_emb : (innData K).emb = MulAut.conj := MonoidHom.ext fun g => by
  simp only [G2Data.emb, innData, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  exact MonoidHom.ofInjective_apply conj_injective

omit [CharP K 2] in
theorem innData_image (H : Subgroup (ModGL .G2 K)) : (innData K).image H = inn H := by
  rw [G2Data.image, innData_emb]
  rfl

theorem eq_S_of_isPGroup {P : Subgroup (ModGL .G2 K)} (hPC : P ≤ adjointGroup .G2 K)
    (hSP : S K ≤ P) (hP : IsPGroup 2 P) : P = S K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2
    (posUnipotent_le_adjointGroup (τ := .G2) (K := K)) card_posUnipotent
  have hP' : IsPGroup 2 (P.subgroupOf (adjointGroup .G2 K)) :=
    hP.of_equiv (subgroupOfEquivOfLe hPC).symm
  have h := (hUp.toSylow hUi).is_maximal' hP' (by
    rw [IsPGroup.toSylow_coe]
    exact fun x hx => mem_subgroupOf.2 (hSP (mem_subgroupOf.1 hx)))
  rw [IsPGroup.toSylow_coe] at h
  have h2 := subgroupOf_inj.1 h
  rwa [inf_eq_left.2 hPC, inf_eq_left.2 (S_le_adjointGroup K)] at h2

theorem inner_inf_eq_inn_S {Q : Subgroup (MulAut (adjointGroup .G2 K))} (hQ : IsPGroup 2 Q)
    (hSQ : inn (S K) ≤ Q) : inner (adjointGroup .G2 K) ⊓ Q = inn (S K) := by
  set P : Subgroup (ModGL .G2 K) :=
    (Q.comap (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K))).map
      (adjointGroup .G2 K).subtype with hPdef
  have hPC : P ≤ adjointGroup .G2 K := by
    rintro _ ⟨g, -, rfl⟩
    exact g.2
  have hSP : S K ≤ P := fun x hx =>
    ⟨⟨x, S_le_adjointGroup K hx⟩, hSQ (conj_mem_inn hx), rfl⟩
  have hP : IsPGroup 2 P := ((hQ.comap_of_injective _ conj_injective).map _)
  have hPS := eq_S_of_isPGroup hPC hSP hP
  rw [← hPS]
  ext α
  constructor
  · rintro ⟨⟨g, rfl⟩, hgQ⟩
    exact conj_mem_inn ⟨g, hgQ, rfl⟩
  · intro hα
    obtain ⟨g, ⟨g', hg'Q, hg'g⟩, rfl⟩ := mem_inn.1 hα
    have hgg : g' = g := Subtype.ext hg'g
    subst hgg
    exact ⟨⟨g', rfl⟩, hg'Q⟩

theorem card_le_of_isElemAbelian {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {E : Subgroup (MulAut (adjointGroup .G2 K))} (hE : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card E ≤ Nat.card K ^ 3 ∧
      (Nat.card E = Nat.card K ^ 3 → E ≤ inner (adjointGroup .G2 K)) := by
  have hcomm := hE.1
  set Γ := (E ⊓ inner (adjointGroup .G2 K)).comap
    (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) with hΓdef
  have hmap : Γ.map MulAut.conj = E ⊓ inner (adjointGroup .G2 K) :=
    map_comap_eq_self inf_le_right
  have hcardΓ : Nat.card Γ = Nat.card (E ⊓ inner (adjointGroup .G2 K) :
      Subgroup (MulAut (adjointGroup .G2 K))) := by
    rw [← hmap, card_map_of_injective conj_injective]
  have hΓ1 : ∀ g ∈ Γ, g * g = 1 := fun g hg => conj_injective (by
    rw [map_mul, map_one, ← sq]
    exact hE.2 _ (mem_inf.1 hg).1)
  have hΓc : ∀ g ∈ Γ, ∀ h ∈ Γ, g * h = h * g := fun g hg h hh => conj_injective (by
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (mul_comm' (⟨_, (mem_inf.1 hg).1⟩ : E) ⟨_, (mem_inf.1 hh).1⟩))
  have hbound := Quasithin.B45G2.card_le_cube_adjointGroup hK (by omega) hΓ1 hΓc
  by_cases hEL : E ≤ inner (adjointGroup .G2 K)
  · rw [inf_eq_left.2 hEL] at hcardΓ
    exact ⟨hcardΓ ▸ hbound, fun _ => hEL⟩
  obtain ⟨y, hyE, hyL⟩ := Set.not_subset.1 hEL
  have hy1 : y ≠ 1 := fun h => hyL (h ▸ one_mem _)
  have hyo : orderOf y = 2 := orderOf_eq_prime (hE.2 y hyE) hy1
  have hfix : ∀ g ∈ Γ, y g = g := fun g hg => by
    have hc : y * MulAut.conj g = MulAut.conj g * y :=
      congrArg Subtype.val (mul_comm' (⟨y, hyE⟩ : E) ⟨_, (mem_inf.1 hg).1⟩)
    rw [mulAut_mul_conj] at hc
    exact conj_injective (mul_right_cancel hc)
  have hsq := Quasithin.B45G2.card_sq_le_of_outer_fixed hn hK y hyo hyL hfix hΓ1 hΓc
  obtain ⟨-, Θ, -, -, hker, hinv⟩ := even_G2_exact_automorphism_normal_form hn K hK
  have hmemker : ∀ x, x ∈ inner (adjointGroup .G2 K) ↔ Θ x = 1 := fun x => by
    rw [← MonoidHom.mem_ker, hker]
    rfl
  have hval : ∀ x ∈ E, x ∉ inner (adjointGroup .G2 K) → ∀ c, Θ x c = c ^ 2 ^ (n / 2) :=
    fun x hx hxL c => by
      rcases hinv x (hE.2 x hx) with h | ⟨-, h, -⟩
      · exact absurd ((hmemker x).2 h) hxL
      · exact h c
  have hsub : (E : Set (MulAut (adjointGroup .G2 K))) ⊆
      ((E ⊓ inner (adjointGroup .G2 K) : Subgroup (MulAut (adjointGroup .G2 K))) :
        Set (MulAut (adjointGroup .G2 K))) ∪
      (fun z => y * z) '' ((E ⊓ inner (adjointGroup .G2 K) :
        Subgroup (MulAut (adjointGroup .G2 K))) : Set (MulAut (adjointGroup .G2 K))) := by
    intro x hx
    by_cases hxL : x ∈ inner (adjointGroup .G2 K)
    · exact Or.inl ⟨hx, hxL⟩
    · refine Or.inr ⟨y⁻¹ * x, ?_, by simp only [mul_inv_cancel_left]⟩
      have hΘ : Θ x = Θ y := RingEquiv.ext fun c => by rw [hval x hx hxL, hval y hyE hyL]
      refine mem_inf.2 ⟨mul_mem (inv_mem hyE) hx, (hmemker _).2 ?_⟩
      rw [map_mul, map_inv, hΘ, inv_mul_cancel]
  have hcard2 : Nat.card E ≤ 2 * Nat.card (E ⊓ inner (adjointGroup .G2 K) :
      Subgroup (MulAut (adjointGroup .G2 K))) := by
    rw [← SetLike.coe_sort_coe, ← SetLike.coe_sort_coe (E ⊓ _), Nat.card_coe_set_eq,
      Nat.card_coe_set_eq]
    calc (E : Set (MulAut (adjointGroup .G2 K))).ncard ≤ _ :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ _ := Set.ncard_union_le _ _
      _ ≤ _ := Nat.add_le_add_left (Set.ncard_image_le (Set.toFinite _)) _
      _ = _ := by ring
  have hlt : Nat.card E < Nat.card K ^ 3 := by
    have h1 : Nat.card E ^ 2 ≤ 4 * 2 ^ (3 * n) := by
      rw [← hcardΓ] at hcard2
      calc Nat.card E ^ 2 ≤ (2 * Nat.card Γ) ^ 2 := Nat.pow_le_pow_left hcard2 2
        _ = 4 * Nat.card Γ ^ 2 := by ring
        _ ≤ 4 * 2 ^ (3 * n) := Nat.mul_le_mul_left 4 hsq
    have h2 : 4 * 2 ^ (3 * n) < (Nat.card K ^ 3) ^ 2 := by
      rw [hK, ← pow_mul, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact (Nat.pow_lt_pow_iff_left two_ne_zero).1 (h1.trans_lt h2)
  exact ⟨hlt.le, fun h => absurd h hlt.ne⟩

theorem centralizer_inn_le_inner {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {E₀ : Subgroup (ModGL .G2 K)} (hE₀C : E₀ ≤ adjointGroup .G2 K)
    (hE₀ : CFSG.IsElementaryAbelian 2 E₀) (hcard : Nat.card E₀ = Nat.card K ^ 3) :
    centralizer (inn E₀ : Set (MulAut (adjointGroup .G2 K))) ≤ inner (adjointGroup .G2 K) := by
  intro α hα
  rw [mem_centralizer_inn_iff] at hα
  obtain ⟨g, hg, hXW⟩ := elementary_le_conj hE₀C hE₀
  set g' : adjointGroup .G2 K := ⟨g, hg⟩ with hg'
  have hUE : ∀ x : adjointGroup .G2 K, (x : ModGL .G2 K) ∈ U K →
      ((g' * x * g'⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) ∈ E₀ := by
    intro x hx
    have hmem : ∀ H : Subgroup (ModGL .G2 K), (x : ModGL .G2 K) ∈ H →
        ((g' * x * g'⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) ∈
          H.map (MulAut.conj g).toMonoidHom := fun H hxH => ⟨x, hxH, rfl⟩
    rcases hXW with hX | hW
    · rw [Subgroup.eq_of_le_of_card_ge hX (by rw [card_map_conj, card_X, hcard])]
      exact hmem _ (Y_le_X (U_le_Y hx))
    · rw [Subgroup.eq_of_le_of_card_ge hW (by rw [card_map_conj, card_W, hcard])]
      exact hmem _ (Y_le_W (U_le_Y hx))
  have hβ : ∀ x : adjointGroup .G2 K, (x : ModGL .G2 K) ∈ rootSubgroup .G2 K g2c →
      ((MulAut.conj g')⁻¹ * α * MulAut.conj g') x = x := fun x hx => by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hα _ (hUE x hx), MulAut.inv_apply,
      MulAut.conj_symm_apply]
    group
  obtain ⟨h, -, hh⟩ := exists_eq_conj_of_fix_rootSubgroup hK hn centralizer_pinnedX_c_le hβ
  refine ⟨g' * h * g'⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hh]
  group

theorem yamada_3_21 {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {Q : Subgroup (MulAut (adjointGroup .G2 K))} (hQ : IsPGroup 2 Q) (hSQ : inn (S K) ≤ Q) :
    (∀ V : Subgroup (MulAut (adjointGroup .G2 K)), V ≤ Q → IsMulCommutative V →
        3 * n ≤ CFSG.Open.pRank 2 V → V ≤ inn (S K)) ∧
      CFSG.Open.pRank 2 Q = 3 * n ∧ rankThompson Q = inn (S K) := by
  have : Finite (MulAut (adjointGroup .G2 K)) := MulEquiv.finite_left
  have hrank := (innData K).pRank_S hK (by omega)
  have hJ := (innData K).rankThompson_S hK (by omega)
  rw [G2Data.S, innData_image] at hrank hJ
  have key : ∀ V : Subgroup (MulAut (adjointGroup .G2 K)), V ≤ Q → IsMulCommutative V →
      3 * n ≤ CFSG.Open.pRank 2 V → V ≤ inn (S K) := by
    intro V hVQ hV hrV
    obtain ⟨E, hEV, hE, hcardE⟩ := SectionRank.exists_pRank one_lt_two V
    obtain ⟨hle, hL⟩ := card_le_of_isElemAbelian hK hn hE
    have hcE : Nat.card E = Nat.card K ^ 3 := by
      refine le_antisymm hle ?_
      rw [hcardE, hK, ← pow_mul, mul_comm]
      exact Nat.pow_le_pow_right (by norm_num) hrV
    have hEL := hL hcE
    set E₀ : Subgroup (ModGL .G2 K) :=
      (E.comap (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K))).map
        (adjointGroup .G2 K).subtype with hE₀def
    have hE₀C : E₀ ≤ adjointGroup .G2 K := by
      rintro _ ⟨g, -, rfl⟩
      exact g.2
    have hinnE₀ : inn E₀ = E := by
      apply le_antisymm
      · intro α hα
        obtain ⟨g, ⟨g', hg'E, hg'g⟩, rfl⟩ := mem_inn.1 hα
        rw [← Subtype.ext hg'g]
        exact hg'E
      · intro α hα
        obtain ⟨g, rfl⟩ := hEL hα
        exact conj_mem_inn ⟨g, hα, rfl⟩
    have hcE₀ : Nat.card E₀ = Nat.card K ^ 3 := by
      rw [← card_inn hE₀C, hinnE₀, hcE]
    have hE₀ : CFSG.IsElementaryAbelian 2 E₀ := by
      have := hE.1
      refine isElementaryAbelian_of_forall (fun x hx y hy => ?_) fun x hx => ?_
      · obtain ⟨g, hgE, rfl⟩ := hx
        obtain ⟨h, hhE, rfl⟩ := hy
        have := congrArg Subtype.val (mul_comm' (⟨_, hgE⟩ : E) ⟨_, hhE⟩)
        simp only [Subgroup.coe_mul, ← map_mul] at this
        exact congrArg Subtype.val (conj_injective this)
      · obtain ⟨g, hgE, rfl⟩ := hx
        have h2 := hE.2 _ hgE
        rw [← map_pow] at h2
        have h3 : g ^ 2 = 1 := conj_injective (by rw [h2, map_one])
        rw [← sq]
        exact congrArg Subtype.val h3
    have hVC : V ≤ centralizer (inn E₀ : Set (MulAut (adjointGroup .G2 K))) := by
      rw [hinnE₀]
      intro v hv
      rw [mem_centralizer_iff]
      intro x hx
      exact congrArg Subtype.val (mul_comm' (⟨x, hEV hx⟩ : V) ⟨v, hv⟩)
    have hVL := hVC.trans (centralizer_inn_le_inner hK hn hE₀C hE₀ hcE₀)
    rw [← inner_inf_eq_inn_S hQ hSQ]
    exact le_inf hVL hVQ
  have hrQ : CFSG.Open.pRank 2 Q = 3 * n := by
    refine le_antisymm (SectionRank.pRank_le one_lt_two fun E _ hE => ?_) ?_
    · calc Nat.card E ≤ Nat.card K ^ 3 := (card_le_of_isElemAbelian hK hn hE).1
        _ = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
    · rw [← hrank.1]
      exact SectionRank.pRank_mono one_lt_two hSQ
  refine ⟨key, hrQ, le_antisymm (iSup₂_le fun A hA => key A hA.1 hA.2.1 (by rw [hA.2.2, hrQ]))
    ?_⟩
  rw [← hJ]
  exact iSup₂_le fun A hA => le_iSup₂_of_le A ⟨hA.1.trans hSQ, hA.2.1,
    by rw [hA.2.2, hrank.1, hrQ]⟩ le_rfl

theorem yamada_3_21_sylow {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (Q : Sylow 2 (MulAut (adjointGroup .G2 K))) (hSQ : inn (S K) ≤ Q) :
    rankThompson (Q : Subgroup (MulAut (adjointGroup .G2 K))) = inn (S K) := by
  have : Finite (MulAut (adjointGroup .G2 K)) := MulEquiv.finite_left
  exact (yamada_3_21 hK hn Q.isPGroup' hSQ).2.2

end Thompson

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

@[expose] noncomputable def act : normalizer (L : Set G) →* MulAut (adjointGroup .G2 K) :=
  (MulAut.congr d.equiv).toMonoidHom.comp L.normalizerMonoidHom

theorem emb_act_apply (x : normalizer (L : Set G)) (g : adjointGroup .G2 K) :
    d.emb (d.act x g) = x * d.emb g * (x : G)⁻¹ := by
  simp [act, emb, MulAut.congr_apply]

theorem act_eq_one_iff (x : normalizer (L : Set G)) :
    d.act x = 1 ↔ (x : G) ∈ centralizer (L : Set G) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨g, rfl⟩ := d.exists_emb_eq hy
    have h1 := d.emb_act_apply x g
    rw [h, MulAut.one_apply] at h1
    calc d.emb g * x = x * d.emb g * (x : G)⁻¹ * x := by rw [← h1]
      _ = x * d.emb g := by group
  · intro h
    refine MulEquiv.ext fun g => d.emb_injective ?_
    rw [d.emb_act_apply, MulAut.one_apply, ← mem_centralizer_iff.1 h _ (d.emb_mem g)]
    group

theorem act_emb (g : adjointGroup .G2 K) :
    d.act ⟨d.emb g, le_normalizer (d.emb_mem g)⟩ = MulAut.conj g :=
  MulEquiv.ext fun h => d.emb_injective (by
    rw [d.emb_act_apply, MulAut.conj_apply, map_mul, map_mul, map_inv])

theorem act_mem_inner_iff {x : G} (hx : x ∈ normalizer (L : Set G)) :
    d.act ⟨x, hx⟩ ∈ inner (adjointGroup .G2 K) ↔ x ∈ L ⊔ centralizer (L : Set G) := by
  constructor
  · rintro ⟨g, hg⟩
    have h1 : d.act (⟨d.emb g, le_normalizer (d.emb_mem g)⟩⁻¹ * ⟨x, hx⟩) = 1 := by
      rw [map_mul, map_inv, act_emb, hg, inv_mul_cancel]
    have h2 := (d.act_eq_one_iff _).1 h1
    rw [coe_mul, coe_inv] at h2
    rw [show x = d.emb g * ((d.emb g)⁻¹ * x) by group]
    exact mul_mem_sup (d.emb_mem g) h2
  · intro hxs
    set T : Subgroup G := ((inner (adjointGroup .G2 K)).comap d.act).map
      (normalizer (L : Set G)).subtype with hT
    have hLT : L ≤ T := by
      intro l hl
      obtain ⟨g, rfl⟩ := d.exists_emb_eq hl
      refine ⟨⟨d.emb g, le_normalizer (d.emb_mem g)⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_comap, act_emb]
      exact ⟨g, rfl⟩
    have hCT : centralizer (L : Set G) ≤ T := by
      intro c hc
      refine ⟨⟨c, centralizer_le_normalizer L hc⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_comap, (d.act_eq_one_iff _).2 hc]
      exact one_mem _
    obtain ⟨y, hy, hyx⟩ := sup_le hLT hCT hxs
    have hyx' : y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [← hyx']
    exact hy



theorem act_mem_centralizer_inn_iff {H : Subgroup (ModGL .G2 K)} {x : G}
    (hx : x ∈ normalizer (L : Set G)) :
    (∀ g : adjointGroup .G2 K, (g : ModGL .G2 K) ∈ H → d.act ⟨x, hx⟩ g = g) ↔
      x ∈ centralizer (d.image H : Set G) := by
  rw [mem_centralizer_iff]
  constructor
  · intro h y hy
    obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hy
    have h1 := d.emb_act_apply ⟨x, hx⟩ g
    rw [h g hg] at h1
    calc d.emb g * x = x * d.emb g * x⁻¹ * x := by rw [← h1]
      _ = x * d.emb g := by group
  · intro h g hg
    refine d.emb_injective ?_
    rw [d.emb_act_apply, ← h _ (d.emb_mem_image hg)]
    group

section Yamada319

variable
  [Finite K] [CharP K 2]

theorem yamada_3_19_1_G {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {δ : Fin Tag.G2.rank → ℤ} (hδ : IsRoot .G2 δ) :
    normalizer (L : Set G) ⊓ centralizer (d.rootGroup δ : Set G) ≤
      (L ⊓ centralizer (d.rootGroup δ : Set G)) ⊔ centralizer (L : Set G) := by
  rintro x ⟨hxN, hxc⟩
  have h1 : d.act ⟨x, hxN⟩ ∈ centralizer (Model.inn (rootSubgroup .G2 K δ) :
      Set (MulAut (adjointGroup .G2 K))) :=
    Model.mem_centralizer_inn_iff.2 ((d.act_mem_centralizer_inn_iff hxN).2 hxc)
  rw [Model.yamada_3_19_1 hK hn hδ] at h1
  obtain ⟨g, hg, hge⟩ := Model.mem_inn.1 h1
  have hgL : d.emb g ∈ L ⊓ centralizer (d.rootGroup δ : Set G) := by
    have h := d.image_inf_centralizer (adjointGroup .G2 K) (rootSubgroup_le_adjointGroup δ)
    rw [d.image_adjointGroup] at h
    rw [rootGroup, ← h]
    exact d.emb_mem_image ⟨g.2, hg⟩
  have h2 : d.act (⟨d.emb g, le_normalizer (d.emb_mem g)⟩⁻¹ * ⟨x, hxN⟩) = 1 := by
    rw [map_mul, map_inv, act_emb, hge, inv_mul_cancel]
  rw [show x = d.emb g * ((d.emb g)⁻¹ * x) by group]
  exact mul_mem_sup hgL ((d.act_eq_one_iff _).1 h2)

end Yamada319

end G2Data

end CFSG.LocalAnalysis.EvenBN.G2
