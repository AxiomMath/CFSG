module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Shult
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
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Short

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Open (IsElemAbelian)

section Four

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

omit [Finite G] in
theorem twoLift_g2YGroup_inf
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    {α γ α' γ' : K} (h : α ≠ α' ∨ γ ≠ γ') :
    twoLift ψ (g2YGroup K α γ) ⊓ twoLift ψ (g2YGroup K α' γ') = ⊥ := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hZC := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hx₁, hx₂⟩ := mem_inf.1 hx
  obtain ⟨hxA, hx2, y, hy, hyU⟩ := (mem_twoLift hψ hZ (g2YGroup_comm α γ)).1 hx₁
  obtain ⟨_, -, y', hy', hyU'⟩ := (mem_twoLift hψ hZ (g2YGroup_comm α' γ')).1 hx₂
  have hyy : y = y' := hinj (hy.symm.trans hy')
  subst hyy
  have h1 : (y : ModGL .G2 K) ∈ g2YGroup K α γ ⊓ g2YGroup K α' γ' := mem_inf.2 ⟨hyU, hyU'⟩
  rw [g2YGroup_inf_g2YGroup h, mem_bot] at h1
  have hy1 : y = 1 := Subtype.ext h1
  rw [hy1, map_one] at hy
  exact eq_of_sq_eq_one hψ hZ hxA (one_mem A) hx2 (one_pow 2) (by rw [hy]; exact (map_one ψ).symm)

omit [Finite G] [Finite K] in
theorem twoLift_g2YGroup_le_sup
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ) (lam : K) :
    twoLift ψ (g2YGroup K lam 0) ≤
      twoLift ψ (g2YGroup K 0 0) ⊔ twoLift ψ (g2YGroup K 1 0) := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hAvC : ∀ y ∈ g2ShortRadical K, y ∈ adjointGroup .G2 K := fun q hq =>
    g2LongRadical_le_adjointGroup (g2ShortRadical_le_g2LongRadical hq)
  intro z hz
  obtain ⟨hzA, -, y, hy, x, hyx⟩ := (mem_twoLift hψ hZ (g2YGroup_comm lam 0)).1 hz
  have hy₁ : g2N 0 0 0 ((1 + lam) * x) 0 0 ∈ g2YGroup K 0 0 :=
    ⟨(1 + lam) * x, g2N_eq_g2N rfl rfl rfl rfl (by ring) (by ring)⟩
  have hy₂ : g2N 0 0 0 (lam * x) (lam * x) 0 ∈ g2YGroup K 1 0 :=
    ⟨lam * x, g2N_eq_g2N rfl rfl rfl rfl (by ring) (by ring)⟩
  obtain ⟨z₁, hz₁, hz₁A, hz₁ψ⟩ := exists_mem_twoLift hψ hZ (g2YGroup_sq 0 0)
    ⟨_, hAvC _ (g2YGroup_le 0 0 hy₁)⟩ hy₁
  obtain ⟨z₂, hz₂, hz₂A, hz₂ψ⟩ := exists_mem_twoLift hψ hZ (g2YGroup_sq 1 0)
    ⟨_, hAvC _ (g2YGroup_le 1 0 hy₂)⟩ hy₂
  have hB : ∀ U : Subgroup (ModGL .G2 K), U ≤ g2ShortRadical K →
      twoLift ψ U ≤ twoLift ψ (g2ShortRadical K) := fun U hU => twoLift_mono hU
  have hz₁₂ : z₁ * z₂ ∈ twoLift ψ (g2ShortRadical K) :=
    mul_mem (hB _ (g2YGroup_le 0 0) hz₁) (hB _ (g2YGroup_le 1 0) hz₂)
  have he : z = z₁ * z₂ := by
    refine eq_of_mem_twoLift hψ hZ g2ShortRadical_comm (hB _ (g2YGroup_le lam 0) hz) hz₁₂ ?_
    have e : (⟨z₁ * z₂, le_normalizer (twoLift_le hz₁₂)⟩ : normalizer (A : Set G)) =
        ⟨z₁, le_normalizer hz₁A⟩ * ⟨z₂, le_normalizer hz₂A⟩ := rfl
    rw [e, map_mul, hz₁ψ, hz₂ψ, ← map_mul, hy]
    refine congrArg (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)) ?_
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, hyx]
    change g2N 0 0 0 x (lam * x) (0 * x) =
      g2N 0 0 0 ((1 + lam) * x) 0 0 * g2N 0 0 0 (lam * x) (lam * x) 0
    rw [g2N_zero_mul_g2N_zero]
    exact g2N_eq_g2N rfl (by ring) (by ring) (by char2_ring) (by ring) (by ring)
  rw [he]
  exact mul_mem (mem_sup_left hz₁) (mem_sup_right hz₂)

end Four

section Field

theorem exists_ne_zero_ne_one {F : Type*} [Field F] (h : 3 ≤ Nat.card F) :
    ∃ lam : F, lam ≠ 0 ∧ lam ≠ 1 := by
  classical
  by_contra hne
  have hne' : ∀ x : F, x ≠ 0 → x = 1 := fun x hx => by_contra fun h1 => hne ⟨x, hx, h1⟩
  have hs : Function.Surjective (fun b : Bool => if b then (1 : F) else 0) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨false, by simp [hx]⟩
    · exact ⟨true, by simp [hne' x hx]⟩
  have h2 := Nat.card_le_card_of_surjective _ hs
  rw [show Nat.card Bool = 2 by simp] at h2
  omega

end Field

section Conj

variable {G : Type} [Group G]

theorem rightConjugate_injective (X Y : Subgroup G) (y : G)
    (h : rightConjugate X y = rightConjugate Y y) : X = Y := by
  rw [← RankTwoClassical.rightConjugate_rightConjugate_inv X y, h,
    RankTwoClassical.rightConjugate_rightConjugate_inv]

theorem rightConjugate_rightConjugate_sup (X Y : Subgroup G) (x y : G) :
    rightConjugate (rightConjugate (X ⊔ Y) x) y =
      rightConjugate (rightConjugate X x) y ⊔ rightConjugate (rightConjugate Y x) y := by
  rw [show rightConjugate (X ⊔ Y) x = rightConjugate X x ⊔ rightConjugate Y x from
    map_sup _ _ _]
  exact map_sup _ _ _

theorem rightConjugate_swap_lift (T : Subgroup G) (g a : G) :
    rightConjugate (rightConjugate T g⁻¹) (g * a⁻¹ * g⁻¹) =
      rightConjugate (rightConjugate T a⁻¹) g⁻¹ := by
  rw [rightConjugate_mul, rightConjugate_mul]
  congr 1
  group

theorem sec3_rightConjugate_centralizer [Finite G] {A R T : Subgroup G} {g : G}
    (hc : Sec3 A R T g) {k : G} (hk : k ∈ centralizer (A : Set G)) :
    Sec3 A (rightConjugate R k) (rightConjugate T k) (g * k) := by
  have hkN : k ∈ normalizer (centralizer (A : Set G) : Set G) := le_normalizer hk
  refine ⟨hc.hyp, ?_, fun h => hc.not_mem ?_, ?_, ?_⟩
  · have := AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowR k
    rwa [(rightConjugate_eq_self_iff _ k).2 hkN] at this
  · have hk' : k⁻¹ ∈ normalizer (A : Set G) := inv_mem (centralizer_le_normalizer _ hk)
    have := mul_mem h hk'
    rwa [mul_inv_cancel_right] at this
  · have := AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowT k
    rwa [rightConjugate_mul] at this
  · rw [centralizer_rightConjugate]
    exact map_mono hc.le_centralizer

end Conj

section Four2

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

omit [Finite G] [Finite K] [CharP K 2] in
theorem psi_eq_of_conj_centralizer
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    {c n n' : G} (hc : c ∈ centralizer (A : Set G)) (hn : n ∈ normalizer (A : Set G))
    (hn' : n' ∈ normalizer (A : Set G)) (he : n' = c * n * c⁻¹) :
    ψ ⟨n', hn'⟩ = ψ ⟨n, hn⟩ := by
  subst he
  have hcN : c ∈ normalizer (A : Set G) := centralizer_le_normalizer _ hc
  have e : (⟨c * n * c⁻¹, hn'⟩ : normalizer (A : Set G)) =
      ⟨c, hcN⟩ * ⟨n, hn⟩ * (⟨c, hcN⟩ : normalizer (A : Set G))⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, (hψ.eq_one_iff ⟨c, hcN⟩).2 hc, inv_one, one_mul, mul_one]

omit [Finite G] [Finite K] [CharP K 2] in
theorem actsIn_rightConjugate_centralizer
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    {U : Subgroup (ModGL .G2 K)} (hT : ActsIn ψ T U) {k : G}
    (hk : k ∈ centralizer (A : Set G)) : ActsIn ψ (rightConjugate T k) U := by
  intro u hu huN y hy
  rw [mem_rightConjugate_iff] at hu
  have hkN : k ∈ normalizer (A : Set G) := centralizer_le_normalizer _ hk
  have htN : k * u * k⁻¹ ∈ normalizer (A : Set G) := mul_mem (mul_mem hkN huN) (inv_mem hkN)
  refine hT _ hu htN y ?_
  rw [psi_eq_of_conj_centralizer hψ hk huN htN rfl, hy]

omit [Finite G] [Finite K] [CharP K 2] in
theorem g2Pinned_rightConjugate_centralizer
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    {γ : Fin Tag.G2.rank → ℤ} (hT : G2Pinned ψ T γ) {k : G}
    (hk : k ∈ centralizer (A : Set G)) : G2Pinned ψ (rightConjugate T k) γ := by
  obtain ⟨t, ht, ht1, htN, y, hy, hψt⟩ := hT
  have hkN : k ∈ normalizer (A : Set G) := centralizer_le_normalizer _ hk
  have ht'N : k⁻¹ * t * k ∈ normalizer (A : Set G) := mul_mem (mul_mem (inv_mem hkN) htN) hkN
  refine ⟨k⁻¹ * t * k, ?_, ?_, ht'N, y, hy, ?_⟩
  · rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using ht
  · intro h1
    apply ht1
    calc t = k * (k⁻¹ * t * k) * k⁻¹ := by group
      _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
  · rw [psi_eq_of_conj_centralizer hψ (inv_mem hk) htN ht'N (by rw [inv_inv]), hψt]

omit [Finite K] [CharP K 2] in
theorem exists_sec3_of_isSylowOf
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    {R₁ T₁ : Subgroup G} {g₁ : G} (hc : Sec3 A R₁ T₁ g₁)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) {γ : Fin Tag.G2.rank → ℤ}
    (hp : G2Pinned ψ T₁ γ) (ha : ActsIn ψ T₁ (rootSubgroup .G2 K γ)) :
    ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧ G2Pinned ψ T' γ ∧
      ActsIn ψ T' (rootSubgroup .G2 K γ) := by
  obtain ⟨k, hk, hRk⟩ := Lemma22.exists_conj_eq_of_isSylowOf hc.sylowR hR
  have hk' : k⁻¹ ∈ centralizer (A : Set G) := inv_mem hk
  refine ⟨rightConjugate T₁ k⁻¹, g₁ * k⁻¹, ?_, g2Pinned_rightConjugate_centralizer hψ hp hk',
    actsIn_rightConjugate_centralizer hψ ha hk'⟩
  have h := sec3_rightConjugate_centralizer hc hk'
  have e : rightConjugate R₁ k⁻¹ = R := by
    rw [hRk]
    exact (map_conj_eq_rightConjugate R₁ k).symm
  rwa [e] at h

omit [Finite G] in
theorem twoLift_g2YGroup_ne
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hK4 : 4 ≤ Nat.card K) {α γ α' γ' : K} (h : α ≠ α' ∨ γ ≠ γ') :
    twoLift ψ (g2YGroup K α γ) ≠ twoLift ψ (g2YGroup K α' γ') := by
  intro he
  have h1 := twoLift_g2YGroup_inf hZA hψ h
  rw [← he, inf_idem] at h1
  have h2 := card_twoLift_g2YGroup hZA hψ α γ
  rw [h1, card_bot] at h2
  omega

theorem sec3_swap_lift
    (hc : Sec3 A R T g)
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hK4 : 4 ≤ Nat.card K) (hTZ : T = twoLift ψ (g2YGroup K 0 0)) {a : G}
    (haY : T.map (MulAut.conj a).toMonoidHom = twoLift ψ (g2YGroup K 1 0)) :
    Sec3 A (rightConjugate T g⁻¹) (rightConjugate (rightConjugate T g⁻¹) (g * a⁻¹ * g⁻¹))
      (g * a⁻¹ * g⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hsw := hc.swap
  have hBe := isElemAbelian_twoLift hψ hZ (g2ShortRadical_comm (K := K))
  have hT₁ : rightConjugate T a⁻¹ = twoLift ψ (g2YGroup K 1 0) := by
    rw [← haY, map_conj_eq_rightConjugate]
  have hT0B : T ≤ twoLift ψ (g2ShortRadical K) := hTZ.le.trans (twoLift_mono (g2YGroup_le 0 0))
  have hT1B : rightConjugate T a⁻¹ ≤ twoLift ψ (g2ShortRadical K) :=
    hT₁.le.trans (twoLift_mono (g2YGroup_le 1 0))
  refine ⟨hc.hyp, hsw.sylowR, fun hbN => ?_,
    AschbacherTheorem3.isSylowOf_rightConjugate hsw.sylowR _, ?_⟩
  · have haN : a⁻¹ ∈ normalizer (rightConjugate A g : Set G) :=
      (mem_normalizer_rightConjugate_iff A g a⁻¹).2 hbN
    have haK : a⁻¹ ∈ normalizer (rightConjugate (centralizer (A : Set G)) g : Set G) := by
      rw [← centralizer_rightConjugate]
      exact CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer _ haN
    have hT₁K : rightConjugate T a⁻¹ ≤ rightConjugate (centralizer (A : Set G)) g := by
      have h1 := map_mono (f := (MulAut.conj a⁻¹⁻¹).toMonoidHom) hc.sylowT.le
      change rightConjugate T a⁻¹ ≤ rightConjugate (rightConjugate (centralizer (A : Set G)) g)
        a⁻¹ at h1
      rwa [(rightConjugate_eq_self_iff _ a⁻¹).2 haK] at h1
    have hB2 : IsPGroup 2 (twoLift ψ (g2ShortRadical K)) := fun x => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (hBe.2 _ x.2)⟩
    have hP : IsPGroup 2 (T ⊔ rightConjugate T a⁻¹ : Subgroup G) :=
      IsPGroup.to_le hB2 (sup_le hT0B hT1B)
    have h1 := hc.sylowT.eq_of_le le_sup_left (sup_le hc.sylowT.le hT₁K) hP
    have h2 : rightConjugate T a⁻¹ ≤ T :=
      calc rightConjugate T a⁻¹ ≤ T ⊔ rightConjugate T a⁻¹ := le_sup_right
        _ = T := h1
    rw [hT₁, hTZ] at h2
    have h3 := twoLift_g2YGroup_inf hZA hψ (α := 1) (γ := 0) (α' := 0) (γ' := 0)
      (Or.inl one_ne_zero)
    rw [inf_eq_left.2 h2] at h3
    have h4 := card_twoLift_g2YGroup hZA hψ 1 0
    rw [h3, card_bot] at h4
    omega
  · rw [rightConjugate_swap_lift, centralizer_rightConjugate]
    refine map_mono ?_
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hBe.1.is_comm.comm ⟨y, hT0B hy⟩ ⟨x, hT1B hx⟩)

theorem g2_long_of_short
    {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (h4 : Asc75Theorem4) (h32 : Lemma32) (h184 : G2Centr184)
    (h184s : G2Centr184s) (hc : Sec3 A R T g)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hRq : Nat.card R = Nat.card K) (hTp : G2Pinned ψ T g2v)
    (hTv : ActsIn ψ T (rootSubgroup .G2 K g2v)) :
    ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧ G2Pinned ψ T' g2c ∧
      ActsIn ψ T' (rootSubgroup .G2 K g2c) := by
  classical
  by_contra hno
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hnolong : ∀ {R₁ : Subgroup G}, IsSylowOf 2 R₁ (centralizer (A : Set G)) →
      ¬ ∃ (T' : Subgroup G) (g' : G), Sec3 A R₁ T' g' ∧ G2Pinned ψ T' g2c ∧
        ActsIn ψ T' (rootSubgroup .G2 K g2c) := by
    rintro R₁ - ⟨T', g', hc', hp, ha⟩
    exact hno (exists_sec3_of_isSylowOf hψ hc' hc.sylowR hp ha)
  rcases g2_dichotomy hf hK h4 h32 h184 h184s hc hOut hZA hψ hRq with
    ⟨hTA, -⟩ | ⟨-, -, h2tr⟩
  swap
  · exact g2_short_inf_false hf hK h4 h32 h184 h184s hc hOut hZA hψ hRq hTp hTv
      (hnolong hc.sylowR) h2tr
  have hTZ : T = twoLift ψ (g2YGroup K 0 0) := by
    rw [g2YGroup_zero, ← inf_eq_twoLift_of_actsIn h4 h32 hc hZA hψ hRq hTv]
    exact hTA
  obtain ⟨a, -, -, -, haY⟩ := exists_lift_r_mem hZA hψ (1 : K)
  have haT : T.map (MulAut.conj a).toMonoidHom = twoLift ψ (g2YGroup K 1 0) := by
    rw [hTZ, haY 0 0, zero_add]
  have hsw := hc.swap
  have hc' := sec3_swap_lift hc hZA hψ hK4 hTZ haT
  obtain ⟨a₁, ha₁, hlong | hshort⟩ := g2_exists_pinned h4 h32 h184 h184s hc' hOut hK4 hψ
  · exact hnolong hsw.sylowR ⟨_, _, sec3_conj hc' ha₁, hlong.1, hlong.2⟩
  have hc'' := sec3_conj hc' ha₁
  have hR₁q : Nat.card (rightConjugate T g⁻¹) = Nat.card K := by
    rw [rightConjugate_card, hc.card_eq, hRq]
  rcases g2_dichotomy hf hK h4 h32 h184 h184s hc'' hOut hZA hψ hR₁q with
    ⟨-, honly⟩ | ⟨-, -, h2tr'⟩
  swap
  · exact g2_short_inf_false hf hK h4 h32 h184 h184s hc'' hOut hZA hψ hR₁q hshort.1
      hshort.2 (hnolong hsw.sylowR) h2tr'
  obtain ⟨lam, hl0, hl1⟩ := exists_ne_zero_ne_one (F := K) (by omega)
  obtain ⟨aₗ, -, -, -, haₗY⟩ := exists_lift_r_mem hZA hψ lam
  have hTl : rightConjugate T aₗ⁻¹ = twoLift ψ (g2YGroup K lam 0) := by
    rw [← map_conj_eq_rightConjugate, hTZ, haₗY 0 0, zero_add]
  have hT1 : rightConjugate T a⁻¹ = twoLift ψ (g2YGroup K 1 0) := by
    rw [← map_conj_eq_rightConjugate, haT]
  have hR₁a : rightConjugate (rightConjugate T g⁻¹) a₁ = rightConjugate T g⁻¹ :=
    rightConjugate_eq_self_of_mem_centralizer (mem_centralizer_iff.2 fun h hh =>
      (mem_centralizer_iff.1 (hsw.sylowR.le hh) a₁ ha₁).symm)
  have hR₁ : rightConjugate (rightConjugate (twoLift ψ (g2YGroup K 0 0)) g⁻¹) a₁ =
      rightConjugate T g⁻¹ := by
    rw [← hTZ, hR₁a]
  have hT₂ : rightConjugate (rightConjugate (rightConjugate T g⁻¹) (g * a⁻¹ * g⁻¹)) a₁ =
      rightConjugate (rightConjugate (twoLift ψ (g2YGroup K 1 0)) g⁻¹) a₁ := by
    rw [rightConjugate_swap_lift, hT1]
  have hx : rightConjugate (rightConjugate T g⁻¹) (g * aₗ⁻¹ * g⁻¹ * a₁) =
      rightConjugate (rightConjugate (twoLift ψ (g2YGroup K lam 0)) g⁻¹) a₁ := by
    rw [← rightConjugate_mul, rightConjugate_swap_lift, hTl]
  have hle : rightConjugate (rightConjugate T g⁻¹) (g * aₗ⁻¹ * g⁻¹ * a₁) ≤
      rightConjugate T g⁻¹ ⊔
        rightConjugate (rightConjugate (rightConjugate T g⁻¹) (g * a⁻¹ * g⁻¹)) a₁ := by
    rw [hx, hT₂, ← hR₁, ← rightConjugate_rightConjugate_sup]
    exact map_mono (map_mono (twoLift_g2YGroup_le_sup hZA hψ lam))
  rcases honly _ hle with h | h
  · rw [hx, ← hR₁] at h
    exact twoLift_g2YGroup_ne hZA hψ hK4 (Or.inl hl0)
      (rightConjugate_injective _ _ _ (rightConjugate_injective _ _ _ h))
  · rw [hx, hT₂] at h
    exact twoLift_g2YGroup_ne hZA hψ hK4 (Or.inl hl1)
      (rightConjugate_injective _ _ _ (rightConjugate_injective _ _ _ h))

end Four2

end CFSG.ComponentClassification.RankTwoExceptional
