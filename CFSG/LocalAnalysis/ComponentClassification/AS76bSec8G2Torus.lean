module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Radical
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8TwoLift
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInnerInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDichotomy
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Open (IsElemAbelian)

section Data

variable {G : Type} [Group G]

structure TorusData (B V : Subgroup G) (y : G) : Prop where
  mem : y ∈ B
  mem_normalizer : y ∈ normalizer (V : Set G)
  odd : Odd (orderOf y)
  trans : ∀ b ∈ V ⊓ B, ∀ c ∈ V ⊓ B, b ≠ 1 → c ≠ 1 → ∃ k : ℕ, (y ^ k)⁻¹ * b * y ^ k = c
  norm : ∀ z ∈ normalizer (B : Set G) ⊓ normalizer (V : Set G),
    z⁻¹ * y * z ∈ zpowers y ⊔ centralizer (V : Set G)

theorem TorusData.rightConjugate {B V : Subgroup G} {y : G} (d : TorusData B V y) (x : G) :
    TorusData (rightConjugate B x) (rightConjugate V x) (x⁻¹ * y * x) := by
  refine ⟨?_, ?_, ?_, fun b hb c hc hb1 hc1 => ?_, fun z hz => ?_⟩
  · rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using d.mem
  · rw [mem_normalizer_rightConjugate_iff]
    simpa [mul_assoc] using d.mem_normalizer
  · have h : orderOf (x⁻¹ * y * x) = orderOf y := by
      have h1 := orderOf_injective (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).injective y
      simpa [MulAut.conj_apply] using h1
    rw [h]
    exact d.odd
  · obtain ⟨hbV, hbB⟩ := mem_inf.1 hb
    obtain ⟨hcV, hcB⟩ := mem_inf.1 hc
    rw [mem_rightConjugate_iff] at hbV hbB hcV hcB
    have hb1' : x * b * x⁻¹ ≠ 1 := by
      intro h
      apply hb1
      calc b = x⁻¹ * (x * b * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    have hc1' : x * c * x⁻¹ ≠ 1 := by
      intro h
      apply hc1
      calc c = x⁻¹ * (x * c * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    obtain ⟨k, hk⟩ := d.trans _ (mem_inf.2 ⟨hbV, hbB⟩) _ (mem_inf.2 ⟨hcV, hcB⟩) hb1' hc1'
    refine ⟨k, ?_⟩
    have e : x⁻¹ * y * x = x⁻¹ * y * x⁻¹⁻¹ := by rw [inv_inv]
    rw [e, conj_pow, inv_inv]
    calc (x⁻¹ * y ^ k * x)⁻¹ * b * (x⁻¹ * y ^ k * x) =
        x⁻¹ * ((y ^ k)⁻¹ * (x * b * x⁻¹) * y ^ k) * x := by group
      _ = c := by rw [hk]; group
  · obtain ⟨hzB, hzV⟩ := mem_inf.1 hz
    have hz' : x * z * x⁻¹ ∈ normalizer (B : Set G) ⊓ normalizer (V : Set G) :=
      mem_inf.2 ⟨(mem_normalizer_rightConjugate_iff B x z).1 hzB,
        (mem_normalizer_rightConjugate_iff V x z).1 hzV⟩
    have h := d.norm _ hz'
    have h2 : x⁻¹ * ((x * z * x⁻¹)⁻¹ * y * (x * z * x⁻¹)) * x ∈
        AschbacherTightEmbedding.rightConjugate (zpowers y ⊔ centralizer (V : Set G)) x := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using h
    rw [RankTwoClassical.rightConjugate_sup, RankTwoClassical.rightConjugate_zpowers,
      ← centralizer_rightConjugate] at h2
    have h3 : x⁻¹ * ((x * z * x⁻¹)⁻¹ * y * (x * z * x⁻¹)) * x = z⁻¹ * (x⁻¹ * y * x) * z := by
      group
    rwa [h3] at h2

theorem isElemAbelian_sup_of_commute {H L : Subgroup G} (hH : IsElemAbelian 2 H)
    (hL : IsElemAbelian 2 L) (hHL : H ≤ centralizer (L : Set G)) : IsElemAbelian 2 (H ⊔ L) := by
  have hcH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hH.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcL : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hL.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hHL' : ∀ h ∈ H, ∀ l ∈ L, h * l = l * h := fun h hh l hl =>
    (mem_centralizer_iff.1 (hHL hh) l hl).symm
  have hmem : ∀ x ∈ H ⊔ L, ∃ h ∈ H, ∃ l ∈ L, h * l = x := by
    intro x hx
    have hx' : x ∈ ((H ⊔ L : Subgroup G) : Set G) := hx
    rw [coe_mul_of_left_le_normalizer_right H L (hHL.trans (centralizer_le_normalizer _)),
      Set.mem_mul] at hx'
    exact hx'
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨h₁, hh₁, l₁, hl₁, he₁⟩ := hmem a a.2
    obtain ⟨h₂, hh₂, l₂, hl₂, he₂⟩ := hmem b b.2
    change (a : G) * b = b * a
    rw [← he₁, ← he₂]
    calc h₁ * l₁ * (h₂ * l₂) = h₁ * (l₁ * h₂) * l₂ := by group
      _ = h₁ * (h₂ * l₁) * l₂ := by rw [hHL' h₂ hh₂ l₁ hl₁]
      _ = h₂ * h₁ * (l₁ * l₂) := by rw [← mul_assoc h₁ h₂ l₁, hcH h₁ hh₁ h₂ hh₂]; group
      _ = h₂ * h₁ * (l₂ * l₁) := by rw [hcL l₁ hl₁ l₂ hl₂]
      _ = h₂ * (h₁ * l₂) * l₁ := by group
      _ = h₂ * (l₂ * h₁) * l₁ := by rw [hHL' h₁ hh₁ l₂ hl₂]
      _ = h₂ * l₂ * (h₁ * l₁) := by group
  · obtain ⟨h, hh, l, hl, rfl⟩ := hmem x hx
    rw [(Commute.mul_pow (hHL' h hh l hl) 2 : (h * l) ^ 2 = h ^ 2 * l ^ 2), hH.2 h hh,
      hL.2 l hl, one_mul]

end Data

section Semilinear

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem g2_semilinear
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {γ : Fin Tag.G2.rank → ℤ}
    (hsc : ∀ c ∈ adjointGroup .G2 K, ∀ μ : K, μ ≠ 0 →
      c * pinnedX .G2 K γ 1 * c⁻¹ = pinnedX .G2 K γ μ →
        ∀ s, c * pinnedX .G2 K γ s * c⁻¹ = pinnedX .G2 K γ (μ * s))
    (φ : MulAut ↥(adjointGroup .G2 K))
    (hφ : ∀ s : K, ∃ s' : K, (φ ⟨pinnedX .G2 K γ s, pinnedX_mem_adjointGroup γ s⟩ :
      ModGL .G2 K) = pinnedX .G2 K γ s') :
    ∃ (μ : K) (σ : K ≃+* K), μ ≠ 0 ∧ ∀ s : K,
      (φ ⟨pinnedX .G2 K γ s, pinnedX_mem_adjointGroup γ s⟩ : ModGL .G2 K) =
        pinnedX .G2 K γ (μ * σ s) := by
  obtain ⟨hNF, -⟩ := even_G2_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g₀, σ⟩, hgσ, -⟩ := hNF φ
  have key : ∀ s, (φ ⟨pinnedX .G2 K γ s, pinnedX_mem_adjointGroup γ s⟩ : ModGL .G2 K) =
      g₀ * pinnedX .G2 K γ (σ s) * (g₀ : ModGL .G2 K)⁻¹ := by
    intro s
    rw [hgσ]
    simp only
    rw [units_map_entrywise_pinnedX]
  obtain ⟨μ, hμ⟩ := hφ 1
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [pinnedX_zero] at hμ
    have h1 : φ ⟨pinnedX .G2 K γ 1, pinnedX_mem_adjointGroup γ 1⟩ = 1 := Subtype.ext hμ
    rw [map_eq_one_iff _ φ.injective] at h1
    have h2 : pinnedX .G2 K γ 1 = pinnedX .G2 K γ 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val h1
    exact one_ne_zero (pinnedX_injective .G2 K γ h2)
  have h1 : (g₀ : ModGL .G2 K) * pinnedX .G2 K γ 1 * (g₀ : ModGL .G2 K)⁻¹ =
      pinnedX .G2 K γ μ := by
    rw [← hμ, key, map_one]
  refine ⟨μ, σ, hμ0, fun s => ?_⟩
  rw [key, hsc g₀ g₀.2 μ hμ0 h1]

end Semilinear

section Inf

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}

theorem card_sup_sec3 (hc : Sec3 A R T g) :
    Nat.card (R ⊔ T : Subgroup G) = Nat.card R * Nat.card R := by
  rw [card_sup_eq_mul hc.le_normalizer_R hc.inf_eq_bot, hc.card_eq]

theorem isElemAbelian_sup_sec3 (hc : Sec3 A R T g) (h32 : Lemma32) :
    IsElemAbelian 2 (R ⊔ T : Subgroup G) := by
  refine isElemAbelian_sup_of_commute (hc.elemR h32) (hc.elemT h32) ?_
  rw [le_centralizer_iff]
  exact hc.le_centralizer

theorem sup_inf_sec3 (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) : R ⊔ ((R ⊔ T) ⊓ A) = R ⊔ T :=
  (eq_sup_inf_of_le_sup le_sup_left (hc.sylowR.le.trans (centralizer_le_normalizer _))
    (sup_le le_sup_left (hc.le_sup h32 h4 h34))).symm

theorem inf_eq_bot_sec3 (hc : Sec3 A R T g) (hZA : Odd (Nat.card (center A))) :
    R ⊓ A = ⊥ := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  refine two_subgroup_of_odd_eq_bot _ _ (hc.sylowR.isPGroup.to_le inf_le_left) hZ ?_
  intro x hx
  exact mem_inf.2 ⟨(mem_inf.1 hx).2, hc.sylowR.le (mem_inf.1 hx).1⟩

theorem card_inf_sec3 (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) (hZA : Odd (Nat.card (center A))) :
    Nat.card ((R ⊔ T) ⊓ A : Subgroup G) = Nat.card R := by
  have hRZ : R ⊓ ((R ⊔ T) ⊓ A) = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_left R inf_le_right).trans (inf_eq_bot_sec3 hc hZA).le)
  have hN : (R ⊔ T) ⊓ A ≤ normalizer (R : Set G) := by
    intro x hx
    refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun r hr => ?_)
    exact (mem_centralizer_iff.1 (hc.sylowR.le hr) x (mem_inf.1 hx).2).symm
  have h1 := card_sup_eq_mul hN hRZ
  rw [sup_inf_sec3 hc h32 h4 h34, card_sup_sec3 hc] at h1
  have hR0 : 0 < Nat.card R := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_left hR0 h1).symm

end Inf

section Core

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

abbrev g2Xc
    (γ : Fin Tag.G2.rank → ℤ) (s : K) : ↥(adjointGroup .G2 K) :=
  ⟨pinnedX .G2 K γ s, pinnedX_mem_adjointGroup γ s⟩

omit [Finite G] [Finite K] [CharP K 2] in
theorem psi_conj_eq_conj {n b : G} (hn : n ∈ normalizer (A : Set G)) (hb : b ∈ A)
    {x : ↥(adjointGroup .G2 K)} (hbx : ψ ⟨b, le_normalizer hb⟩ = MulAut.conj x)
    (hnb : n * b * n⁻¹ ∈ A) :
    ψ ⟨n * b * n⁻¹, le_normalizer hnb⟩ = MulAut.conj (ψ ⟨n, hn⟩ x) := by
  have e : (⟨n * b * n⁻¹, le_normalizer hnb⟩ : normalizer (A : Set G)) =
      ⟨n, hn⟩ * ⟨b, le_normalizer hb⟩ * ⟨n, hn⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, hbx, RankTwoHypIIY.conj_apply_eq_mul_conj_mul_inv]

omit [Finite K] [CharP K 2] in
theorem rootSubgroup_comm
    (γ : Fin Tag.G2.rank → ℤ) :
    ∀ u ∈ rootSubgroup .G2 K γ, ∀ v ∈ rootSubgroup .G2 K γ, u * v = v * u := by
  intro u hu v hv
  obtain ⟨s, rfl⟩ := mem_rootSubgroup.1 hu
  obtain ⟨s', rfl⟩ := mem_rootSubgroup.1 hv
  rw [← pinnedX_add, ← pinnedX_add, add_comm]

omit [Finite K] in
theorem rootSubgroup_sq
    (γ : Fin Tag.G2.rank → ℤ) :
    ∀ u ∈ rootSubgroup .G2 K γ, u ^ 2 = 1 := by
  intro u hu
  obtain ⟨s, rfl⟩ := mem_rootSubgroup.1 hu
  rw [sq, pinnedX_mul_self]

omit [Finite K] [CharP K 2] in
theorem card_rootSubgroup_subgroupOf
    (γ : Fin Tag.G2.rank → ℤ) :
    Nat.card ((rootSubgroup .G2 K γ).subgroupOf (adjointGroup .G2 K)) = Nat.card K := by
  have h1 := Subgroup.card_map_of_injective (K := (rootSubgroup .G2 K γ).subgroupOf
    (adjointGroup .G2 K)) (adjointGroup .G2 K).subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left (rootSubgroup_le_adjointGroup γ),
    card_rootSubgroup] at h1
  exact h1.symm

theorem inf_eq_twoLift_of_actsIn
    (h4 : Asc75Theorem4) (h32 : Lemma32)
    (hc : Sec3 A R T g) (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hRq : Nat.card R = Nat.card K) {γ : Fin Tag.G2.rank → ℤ}
    (hT : ActsIn ψ T (rootSubgroup .G2 K γ)) :
    (R ⊔ T) ⊓ A = twoLift ψ (rootSubgroup .G2 K γ) := by
  have h34 : Asc08Lemma34 := asc08Lemma34
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hZC := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hVe := isElemAbelian_sup_sec3 hc h32
  have hle : (R ⊔ T) ⊓ A ≤ twoLift ψ (rootSubgroup .G2 K γ) := by
    intro z hz
    obtain ⟨hzV, hzA⟩ := mem_inf.1 hz
    have hzV' : z ∈ ((R ⊔ T : Subgroup G) : Set G) := hzV
    rw [coe_mul_of_right_le_normalizer_left R T hc.le_normalizer_R, Set.mem_mul] at hzV'
    obtain ⟨r, hr, t, ht, rfl⟩ := hzV'
    have hrN : r ∈ normalizer (A : Set G) := centralizer_le_normalizer _ (hc.sylowR.le hr)
    have htN := hc.le_normalizer ht
    obtain ⟨x, hx⟩ := exists_psi_eq_conj hc h32 h4 h34 hψ ht htN
    refine mem_twoLift_of hzA (hVe.2 _ hzV) (y := x) ?_ (hT t ht htN x hx)
    have e : (⟨r * t, le_normalizer hzA⟩ : normalizer (A : Set G)) = ⟨r, hrN⟩ * ⟨t, htN⟩ := rfl
    rw [e, map_mul, (hψ.eq_one_iff ⟨r, hrN⟩).2 (hc.sylowR.le hr), one_mul, hx]
  refine eq_of_le_of_card_ge hle ?_
  rw [card_twoLift hψ hZ (rootSubgroup_comm γ) (rootSubgroup_sq γ) hZC,
    card_inf_sec3 hc h32 h4 h34 hZA, hRq, card_rootSubgroup_subgroupOf]

theorem torusData_of_actsIn
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (h4 : Asc75Theorem4) (h32 : Lemma32) (hc : Sec3 A R T g) (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hRq : Nat.card R = Nat.card K) {γ : Fin Tag.G2.rank → ℤ}
    (d : Kˣ →* ↥(adjointGroup .G2 K))
    (hd : ∀ (t : Kˣ) (s : K), MulAut.conj (d t) (g2Xc γ s) = g2Xc γ ((t : K) * s))
    (hsc : ∀ c ∈ adjointGroup .G2 K, ∀ μ : K, μ ≠ 0 →
      c * pinnedX .G2 K γ 1 * c⁻¹ = pinnedX .G2 K γ μ →
        ∀ s, c * pinnedX .G2 K γ s * c⁻¹ = pinnedX .G2 K γ (μ * s))
    (hT : ActsIn ψ T (rootSubgroup .G2 K γ)) :
    ∃ y, TorusData A (R ⊔ T) y := by
  have h34 : Asc08Lemma34 := asc08Lemma34
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hZC := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hUc := rootSubgroup_comm (K := K) γ
  have hU2 := rootSubgroup_sq (K := K) γ
  have hVA : (R ⊔ T) ⊓ A = twoLift ψ (rootSubgroup .G2 K γ) :=
    inf_eq_twoLift_of_actsIn h4 h32 hc hZA hψ hRq hT
  have hRZ : R ⊔ ((R ⊔ T) ⊓ A) = R ⊔ T := sup_inf_sec3 hc h32 h4 h34
  have hmemZ : ∀ b ∈ (R ⊔ T) ⊓ A, ∃ s : K, ∃ hbA : b ∈ A,
      ψ ⟨b, le_normalizer hbA⟩ = MulAut.conj (g2Xc γ s) := by
    intro b hb
    rw [hVA] at hb
    obtain ⟨hbA, -, x, hx, hxU⟩ := (mem_twoLift hψ hZ hUc).1 hb
    obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hxU
    exact ⟨s, hbA, by rw [hx]; congr 1; exact Subtype.ext hs.symm⟩
  have hexZ : ∀ s : K, ∃ b ∈ (R ⊔ T) ⊓ A, ∃ hbA : b ∈ A,
      ψ ⟨b, le_normalizer hbA⟩ = MulAut.conj (g2Xc γ s) := by
    intro s
    obtain ⟨b, hb, hbA, hbψ⟩ :=
      exists_mem_twoLift hψ hZ hU2 (g2Xc γ s) (mem_rootSubgroup.2 ⟨s, rfl⟩)
    exact ⟨b, hVA ▸ hb, hbA, hbψ⟩
  have heqZ : ∀ b ∈ (R ⊔ T) ⊓ A, ∀ c ∈ (R ⊔ T) ⊓ A,
      ∀ (hbN : b ∈ normalizer (A : Set G)) (hcN : c ∈ normalizer (A : Set G)),
        ψ ⟨b, hbN⟩ = ψ ⟨c, hcN⟩ → b = c := by
    intro b hb c hc' _ _ h
    rw [hVA] at hb hc'
    exact eq_of_mem_twoLift hψ hZ hUc hb hc' h
  obtain ⟨t₀, ht₀⟩ := IsCyclic.exists_generator (α := Kˣ)
  have ht0 : (t₀ : K) ≠ 0 := t₀.ne_zero
  obtain ⟨y₀, hy₀, hy₀ψ⟩ := hψ.exists_eq (MulAut.conj (d t₀)) ⟨d t₀, rfl⟩
  have hy₀N := le_normalizer hy₀
  have hy₀ψk : ∀ k : ℕ, ψ ⟨y₀ ^ k, pow_mem hy₀N k⟩ = MulAut.conj (d (t₀ ^ k)) := by
    intro k
    have e : (⟨y₀ ^ k, pow_mem hy₀N k⟩ : normalizer (A : Set G)) = ⟨y₀, hy₀N⟩ ^ k := rfl
    rw [e, map_pow, hy₀ψ, ← map_pow, ← map_pow]
  have hy₀inv : ψ ⟨y₀⁻¹, inv_mem hy₀N⟩ = MulAut.conj (d t₀⁻¹) := by
    have e : (⟨y₀⁻¹, inv_mem hy₀N⟩ : normalizer (A : Set G)) = ⟨y₀, hy₀N⟩⁻¹ := rfl
    rw [e, map_inv, hy₀ψ, ← map_inv, ← map_inv]
  have hy₀Z : y₀ ∈ normalizer (((R ⊔ T) ⊓ A : Subgroup G) : Set G) := by
    rw [hVA]
    refine mem_normalizer_twoLift hψ hZ hUc hy₀N fun x => ?_
    rw [hy₀ψ]
    constructor
    · intro hx
      obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hx
      have hx' : x = g2Xc γ s := Subtype.ext hs.symm
      rw [hx', hd]
      exact mem_rootSubgroup.2 ⟨_, rfl⟩
    · intro hx
      obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hx
      have h1 : MulAut.conj (d t₀⁻¹) (MulAut.conj (d t₀) x) = x := by
        rw [← MulAut.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
          MulAut.one_apply]
      have hx' : MulAut.conj (d t₀) x = g2Xc γ s := Subtype.ext hs.symm
      rw [← h1, hx', hd]
      exact mem_rootSubgroup.2 ⟨_, rfl⟩
  have hy₀Zk : ∀ k : ℕ, y₀ ^ k ∈ normalizer (((R ⊔ T) ⊓ A : Subgroup G) : Set G) :=
    fun k => pow_mem hy₀Z k
  refine ⟨y₀⁻¹, inv_mem hy₀, ?_, ?_, ?_, ?_⟩
  · rw [← hRZ]
    refine inv_mem (RankTwoClassical.mem_normalizer_sup (centralizer_le_normalizer _ ?_) hy₀Z)
    rw [mem_centralizer_iff]
    intro r hr
    exact (mem_centralizer_iff.1 (hc.sylowR.le hr) y₀ hy₀).symm
  · rw [orderOf_inv]
    have hq : Odd (Nat.card K - 1) := by
      rw [hK]
      exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).2 even_two) odd_one
    have ht₀q : t₀ ^ (Nat.card K - 1) = 1 := by
      rw [← Nat.card_units]
      exact pow_card_eq_one'
    have hy : y₀ ^ (Nat.card K - 1) ∈ A ⊓ centralizer (A : Set G) := by
      refine mem_inf.2 ⟨pow_mem hy₀ _, (hψ.eq_one_iff ⟨_, pow_mem hy₀N _⟩).1 ?_⟩
      rw [hy₀ψk, ht₀q, map_one, map_one]
    have h1 : (y₀ ^ (Nat.card K - 1)) ^ Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ hy)
    rw [← pow_mul] at h1
    exact (Nat.odd_mul.2 ⟨hq, hZ⟩).of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  · intro b hb c hc' hb1 hc1
    obtain ⟨s, hbA, hbs⟩ := hmemZ b hb
    obtain ⟨s', hcA, hcs⟩ := hmemZ c hc'
    have hs0 : ∀ {u : G} (hu : u ∈ (R ⊔ T) ⊓ A) {s₁ : K} (huA : u ∈ A),
        ψ ⟨u, le_normalizer huA⟩ = MulAut.conj (g2Xc γ s₁) → u ≠ 1 → s₁ ≠ 0 := by
      intro u hu s₁ huA hus hu1 hs₁
      apply hu1
      refine heqZ u hu 1 (mem_inf.2 ⟨one_mem _, one_mem _⟩) (le_normalizer huA) (one_mem _) ?_
      rw [hus, hs₁]
      have h0 : g2Xc γ (0 : K) = 1 := Subtype.ext (pinnedX_zero .G2 K γ)
      rw [h0, map_one]
      exact (map_one ψ).symm
    have hsb := hs0 hb hbA hbs hb1
    have hsc' := hs0 hc' hcA hcs hc1
    obtain ⟨k, hk⟩ : ∃ k : ℕ, t₀ ^ k = Units.mk0 s' hsc' * (Units.mk0 s hsb)⁻¹ := by
      have h1 := ht₀ (Units.mk0 s' hsc' * (Units.mk0 s hsb)⁻¹)
      rw [← mem_powers_iff_mem_zpowers] at h1
      obtain ⟨k, hk⟩ := h1
      exact ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have e : (y₀⁻¹ ^ k)⁻¹ * b * y₀⁻¹ ^ k = y₀ ^ k * b * (y₀ ^ k)⁻¹ := by
      rw [inv_pow, inv_inv]
    rw [e]
    have hmem : y₀ ^ k * b * (y₀ ^ k)⁻¹ ∈ (R ⊔ T) ⊓ A :=
      (mem_normalizer_iff.1 (hy₀Zk k) b).1 hb
    refine heqZ _ hmem c hc' (le_normalizer (mem_inf.1 hmem).2) (le_normalizer hcA) ?_
    rw [psi_conj_eq_conj (pow_mem hy₀N k) hbA hbs (mem_inf.1 hmem).2, hy₀ψk, hd, hcs, hk]
    have e2 : ((Units.mk0 s' hsc' * (Units.mk0 s hsb)⁻¹ : Kˣ) : K) * s = s' := by
      rw [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mk0]
      field_simp
    rw [e2]
  · intro z hz
    obtain ⟨hzA, hzV⟩ := mem_inf.1 hz
    have hzZ : z ∈ normalizer (((R ⊔ T) ⊓ A : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro b
      simp only [mem_inf]
      rw [mem_normalizer_iff.1 hzV b, mem_normalizer_iff.1 hzA b]
    have hφ : ∀ s : K, ∃ s' : K,
        (ψ ⟨z, hzA⟩ ⟨pinnedX .G2 K γ s, pinnedX_mem_adjointGroup γ s⟩ : ModGL .G2 K) =
          pinnedX .G2 K γ s' := by
      intro s
      obtain ⟨b, hb, hbA, hbψ⟩ := hexZ s
      have hzb : z * b * z⁻¹ ∈ (R ⊔ T) ⊓ A := (mem_normalizer_iff.1 hzZ b).1 hb
      have h2 := psi_conj_eq_conj hzA hbA hbψ (mem_inf.1 hzb).2
      obtain ⟨s', hs'A, hs'⟩ := hmemZ _ hzb
      rw [h2] at hs'
      exact ⟨s', congrArg Subtype.val (hinj hs')⟩
    obtain ⟨μ, σ, hμ, hφs⟩ := g2_semilinear hf hK hsc (ψ ⟨z, hzA⟩) hφ
    have hφs' : ∀ s, ψ ⟨z, hzA⟩ (g2Xc γ s) = g2Xc γ (μ * σ s) := fun s => Subtype.ext (hφs s)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, t₀ ^ k = Units.map σ.symm.toRingHom.toMonoidHom t₀ := by
      have h1 := ht₀ (Units.map σ.symm.toRingHom.toMonoidHom t₀)
      rw [← mem_powers_iff_mem_zpowers] at h1
      obtain ⟨k, hk⟩ := h1
      exact ⟨k, hk⟩
    have hσk : σ ((t₀ ^ k : Kˣ) : K) = t₀ := by
      rw [hk, Units.coe_map]
      simp
    have hzinvA : ∀ a ∈ A, z⁻¹ * a * z ∈ A := fun a ha => by
      have h1 := (mem_normalizer_iff.1 (inv_mem hzA) a).1 ha
      simpa using h1
    set w := z⁻¹ * y₀⁻¹ * z * y₀ ^ k with hw
    have hwA : w ∈ A := mul_mem (hzinvA _ (inv_mem hy₀)) (pow_mem hy₀ k)
    have hwZ : ∀ b ∈ (R ⊔ T) ⊓ A, w * b * w⁻¹ = b := by
      intro b hb
      obtain ⟨s, hbA, hbs⟩ := hmemZ b hb
      have hb₁ : y₀ ^ k * b * (y₀ ^ k)⁻¹ ∈ (R ⊔ T) ⊓ A := (mem_normalizer_iff.1 (hy₀Zk k) b).1 hb
      have hb₁ψ := psi_conj_eq_conj (pow_mem hy₀N k) hbA hbs (mem_inf.1 hb₁).2
      rw [hy₀ψk, hd] at hb₁ψ
      have hb₂ : z * (y₀ ^ k * b * (y₀ ^ k)⁻¹) * z⁻¹ ∈ (R ⊔ T) ⊓ A :=
        (mem_normalizer_iff.1 hzZ _).1 hb₁
      have hb₂ψ := psi_conj_eq_conj hzA (mem_inf.1 hb₁).2 hb₁ψ (mem_inf.1 hb₂).2
      rw [hφs', map_mul σ, hσk] at hb₂ψ
      have hb₃ : y₀⁻¹ * (z * (y₀ ^ k * b * (y₀ ^ k)⁻¹) * z⁻¹) * y₀⁻¹⁻¹ ∈ (R ⊔ T) ⊓ A :=
        (mem_normalizer_iff.1 (inv_mem hy₀Z) _).1 hb₂
      have hb₃ψ := psi_conj_eq_conj (inv_mem hy₀N) (mem_inf.1 hb₂).2 hb₂ψ (mem_inf.1 hb₃).2
      rw [hy₀inv, hd] at hb₃ψ
      have hb₄ : z * b * z⁻¹ ∈ (R ⊔ T) ⊓ A := (mem_normalizer_iff.1 hzZ b).1 hb
      have hb₄ψ := psi_conj_eq_conj hzA hbA hbs (mem_inf.1 hb₄).2
      rw [hφs'] at hb₄ψ
      have h34' : y₀⁻¹ * (z * (y₀ ^ k * b * (y₀ ^ k)⁻¹) * z⁻¹) * y₀⁻¹⁻¹ = z * b * z⁻¹ := by
        refine heqZ _ hb₃ _ hb₄ (le_normalizer (mem_inf.1 hb₃).2)
          (le_normalizer (mem_inf.1 hb₄).2) ?_
        rw [hb₃ψ, hb₄ψ]
        have e3 : ((t₀⁻¹ : Kˣ) : K) * (μ * ((t₀ : K) * σ s)) = μ * σ s := by
          rw [Units.val_inv_eq_inv_val]
          field_simp
        rw [e3]
      calc w * b * w⁻¹ =
          z⁻¹ * (y₀⁻¹ * (z * (y₀ ^ k * b * (y₀ ^ k)⁻¹) * z⁻¹) * y₀⁻¹⁻¹) * z := by
            rw [hw]
            group
        _ = z⁻¹ * (z * b * z⁻¹) * z := by rw [h34']
        _ = b := by group
    have hwC : w ∈ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
      rw [← hRZ]
      refine RankTwoClassical.mem_centralizer_sup ?_ ?_
      · rw [mem_centralizer_iff]
        intro r hr
        exact (mem_centralizer_iff.1 (hc.sylowR.le hr) w hwA).symm
      · rw [mem_centralizer_iff]
        intro b hb
        have h1 := hwZ b hb
        calc b * w = w * b * w⁻¹ * w := by rw [h1]
          _ = w * b := by group
    have e : z⁻¹ * y₀⁻¹ * z = w * y₀⁻¹ ^ k := by
      rw [hw, inv_pow]
      group
    rw [e]
    exact mul_mem (mem_sup_right hwC) (mem_sup_left (pow_mem (mem_zpowers _) k))


abbrev g2TorusHomR
    (K : Type) [Field K] : Kˣ →* ↥(adjointGroup .G2 K) :=
  (LieType.Chevalley.torusEltHom .G2 K g2ir).codRestrict (adjointGroup .G2 K)
    fun t => torusElt_mem_adjointGroup g2ir t

abbrev g2TorusHomA
    (K : Type) [Field K] : Kˣ →* ↥(adjointGroup .G2 K) :=
  (LieType.Chevalley.torusEltHom .G2 K g2ia).codRestrict (adjointGroup .G2 K)
    fun t => torusElt_mem_adjointGroup g2ia t

omit [Finite K] [CharP K 2] in
theorem g2TorusHomR_conj
    (t : Kˣ) (s : K) :
    MulAut.conj (g2TorusHomR K t) (g2Xc g2v s) = g2Xc g2v ((t : K) * s) :=
  Subtype.ext (by
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    exact torus_r_v t s)

omit [Finite K] [CharP K 2] in
theorem g2TorusHomA_conj
    (t : Kˣ) (s : K) :
    MulAut.conj (g2TorusHomA K t) (g2Xc g2c s) = g2Xc g2c ((t : K) * s) :=
  Subtype.ext (by
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    exact torus_a_c t s)

omit [Finite G] in
theorem torusData_of_mem {T : Subgroup G} {y a : G}
    (d : TorusData A (R ⊔ rightConjugate T a) y) (ha : a ∈ A)
    (hRA : R ≤ centralizer (A : Set G)) : TorusData A (R ⊔ T) (a * y * a⁻¹) := by
  have d' := d.rightConjugate a⁻¹
  have hA : rightConjugate A a⁻¹ = A :=
    (rightConjugate_eq_self_iff A a⁻¹).2 (inv_mem (le_normalizer ha))
  have hR : rightConjugate R a⁻¹ = R := by
    refine (rightConjugate_eq_self_iff R a⁻¹).2 (inv_mem (centralizer_le_normalizer _ ?_))
    rw [mem_centralizer_iff]
    intro r hr
    exact (mem_centralizer_iff.1 (hRA hr) a ha).symm
  rw [hA, RankTwoClassical.rightConjugate_sup, hR, rightConjugate_mul, mul_inv_cancel,
    rightConjugate_one, inv_inv] at d'
  exact d'

theorem torusData
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h184 : G2Centr184) (h184s : G2Centr184s)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hRq : Nat.card R = Nat.card K) : ∃ y, TorusData A (R ⊔ T) y := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨a, ha, hlong | hshort⟩ := g2_exists_pinned h4 h32 h184 h184s hc hOut hK4 hψ
  · obtain ⟨y, hy⟩ := torusData_of_actsIn hf hK h4 h32 (sec3_conj hc ha) hZA hψ hRq
      (g2TorusHomA K) g2TorusHomA_conj (fun c hc' μ hμ h s => g2_conj_c_eq h184 hK4 hc' hμ h s)
      hlong.2
    exact ⟨a * y * a⁻¹, torusData_of_mem hy ha hc.sylowR.le⟩
  · obtain ⟨y, hy⟩ := torusData_of_actsIn hf hK h4 h32 (sec3_conj hc ha) hZA hψ hRq
      (g2TorusHomR K) g2TorusHomR_conj (fun c hc' μ hμ h s => g2_conj_v_eq hc' hμ h s) hshort.2
    exact ⟨a * y * a⁻¹, torusData_of_mem hy ha hc.sylowR.le⟩

end Core

end CFSG.ComponentClassification.RankTwoExceptional
