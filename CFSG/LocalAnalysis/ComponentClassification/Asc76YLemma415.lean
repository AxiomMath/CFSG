module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4Tools
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Shapes

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3
  CFSG.ComponentClassification.AschbacherToolkit

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace Assumption41

variable (hΩ : Assumption41 Ω)
include hΩ

theorem exists_rot {K R : Subgroup G} (hK : K ∈ Ω) (hR : IsSylowOf 2 R K) :
    ∃ U, IsDihedralRot U R :=
  exists_isDihedralRot (hΩ.dihedral K hK R hR).1 (hΩ.dihedral K hK R hR).2

theorem tightlyEmbedded {K : Subgroup G} (hK : K ∈ Ω) : TightlyEmbedded K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, fun g hg => ?_⟩
  · obtain ⟨R, hR⟩ := exists_isSylowOf 2 K
    obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
    have h2 : 2 ∣ Nat.card R := ⟨Nat.card U, hU.card_eq⟩
    exact even_iff_two_dvd.mpr (h2.trans (card_dvd_of_le hR.le))
  · have hne : K ≠ AschbacherTightEmbedding.rightConjugate K g := fun h =>
      hg ((rightConjugate_eq_self_iff K g).mp h.symm)
    exact hΩ.inter K hK _ (hΩ.conj_mem K hK g) hne

theorem card_sylow_eq {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hR : IsSylowOf 2 R K)
    (hT : IsSylowOf 2 T J) : Nat.card R = Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hR.card_eq, hT.card_eq]
  by_cases hKJ : K = J
  · rw [hKJ]
  · rw [hΩ.twoPart K hK J hJ hKJ]

theorem one_lt_pRank {K : Subgroup G} (hK : K ∈ Ω) : 1 < CFSG.Open.pRank 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 K
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
  obtain ⟨E, hER, hE, hE4⟩ := hU.exists_fourGroup
  exact CFSG.ComponentClassification.Asc76X.one_lt_pRank_of_fourGroup (hER.trans hR.le) hE hE4

theorem inf_eq_bot {K J P Q : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hP : IsPGroup 2 P) (hPK : P ≤ K) (hQJ : Q ≤ J) : P ⊓ Q = ⊥ :=
  eq_bot_of_isPGroup_of_odd (hP.to_le inf_le_left)
    ((hΩ.inter K hK J hJ hKJ).of_dvd_nat (card_dvd_of_le (inf_le_inf hPK hQJ)))

theorem exists_fourGroup {K R : Subgroup G} (hK : K ∈ Ω) (hR : IsSylowOf 2 R K) :
    ∃ E : Subgroup G, E ≤ R ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 4 := by
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
  obtain ⟨E, hER, hE, hE4⟩ := hU.exists_fourGroup
  exact ⟨E, hER, fun e he => by rw [← pow_two]; exact hE.2 e he, hE4⟩

end Assumption41

theorem ne_weakClosure {K R T : Subgroup G} {s : G} (hsK : s ∈ K) (hsR : s ∈ R)
    (hsT : s ∉ normalizer (T : Set G)) :
    T ≠ ⨆ (k : G) (_ : k ∈ K) (_ : AschbacherTightEmbedding.rightConjugate T k ≤ R ⊔ T),
      AschbacherTightEmbedding.rightConjugate T k := by
  intro h
  have hle : AschbacherTightEmbedding.rightConjugate T s ≤ R ⊔ T := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have : x = s⁻¹ * (s * x * s⁻¹) * s := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (mem_sup_left hsR)) (mem_sup_right hx)) (mem_sup_left hsR)
  have hW : AschbacherTightEmbedding.rightConjugate T s ≤
      ⨆ (k : G) (_ : k ∈ K) (_ : AschbacherTightEmbedding.rightConjugate T k ≤ R ⊔ T),
        AschbacherTightEmbedding.rightConjugate T k :=
    le_iSup_of_le s (le_iSup_of_le hsK (le_iSup_of_le hle le_rfl))
  have hle' : AschbacherTightEmbedding.rightConjugate T s ≤ T := hW.trans h.symm.le
  apply hsT
  rw [← rightConjugate_eq_self_iff]
  exact eq_of_le_of_card_ge hle' (rightConjugate_card T s).ge

structure Setting22 (Ω : Set (Subgroup G)) (K J T R : Subgroup G) : Prop where
  memK : K ∈ Ω
  memJ : J ∈ Ω
  ne : K ≠ J
  sylowT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))
  ne_bot : T ≠ ⊥
  sylowR : IsSylowOf 2 R K
  le_normalizer : T ≤ normalizer (R : Set G)

namespace Setting22

variable {K J T R : Subgroup G} (hs : Setting22 Ω K J T R) (h22 : Asc76Lemma22)
  (hΩ : Assumption41 Ω)
include hs h22 hΩ

theorem spec :
    let W : Subgroup G := ⨆ (k : G) (_ : k ∈ K)
      (_ : AschbacherTightEmbedding.rightConjugate T k ≤ R ⊔ T),
      AschbacherTightEmbedding.rightConjugate T k
    let NRT : Subgroup G := R ⊓ normalizer (T : Set G)
    (Nat.card NRT = Nat.card T ∧ (Nat.card T < Nat.card R → Nonempty (NRT ≃* T))) ∧
    (T ≠ W → IsCyclic T → IsDihedralTwoGroup R ∧
      (IsDihedralTwoGroup (R ⊔ T) ∨ IsWreathedTwoGroup (R ⊔ T))) ∧
    (NormalIn (W ⊔ oddCoreIn K) (K ⊔ T) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ∃ φ : oUpperTwoPrime (K ⊔ T) →*
          Multiplicative (Fin n → ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        Function.Surjective φ ∧ φ.ker = (oddCoreIn K).subgroupOf (oUpperTwoPrime (K ⊔ T))) ∨
      IsCyclic T) ∧
    (IsSylowOf 2 T J → ⁅T, oUpperTwoPrime K⁆ ≤ oddCoreIn K ∨ CFSG.Open.IsElemAbelian 2 T) ∧
    (¬ IsSylowOf 2 T J → IsMulCommutative T) ∧
    (¬ CFSG.Open.IsElemAbelian 2 T → T ≠ W →
      W = T ⊔ NRT ∧
      (∀ E : Subgroup G, NRT ≤ E → E ≤ R → (∀ x ∈ E, x ^ 2 ∈ NRT) →
        (∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ NRT) → NRT.relIndex E ≤ 2) ∧
      ∀ r ∈ R, r ∉ NRT → r ^ 2 ∈ NRT → ∀ x ∈ NRT, r * x * r⁻¹ = x⁻¹) ∧
    (NRT.subgroupOf R).Normal :=
  h22 G K J T R (Assumption41.tightlyEmbedded hΩ hs.memK) (Assumption41.tightlyEmbedded hΩ hs.memJ)
    (hΩ.inter K hs.memK J hs.memJ hs.ne) (hΩ.twoPart K hs.memK J hs.memJ hs.ne) hs.sylowT
    hs.ne_bot hs.sylowR hs.le_normalizer (Assumption41.one_lt_pRank hΩ hs.memK)
    (Assumption41.one_lt_pRank hΩ hs.memJ)

theorem card_inf_normalizer :
    Nat.card (R ⊓ normalizer (T : Set G) : Subgroup G) = Nat.card T :=
  (hs.spec h22 hΩ).1.1

theorem nonempty_mulEquiv (hlt : Nat.card T < Nat.card R) :
    Nonempty ((R ⊓ normalizer (T : Set G) : Subgroup G) ≃* T) :=
  (hs.spec h22 hΩ).1.2 hlt

theorem dihedral_or_wreathed {s : G} (hsR : s ∈ R) (hsT : s ∉ normalizer (T : Set G))
    (hTc : IsCyclic T) : IsDihedralTwoGroup (R ⊔ T) ∨ IsWreathedTwoGroup (R ⊔ T) :=
  ((hs.spec h22 hΩ).2.1 (ne_weakClosure (hs.sylowR.le hsR) hsR hsT) hTc).2

theorem commutator_le (hTJ : IsSylowOf 2 T J) :
    ⁅T, K⁆ ≤ oddCoreIn K ∨ CFSG.Open.IsElemAbelian 2 T := by
  have h := (hs.spec h22 hΩ).2.2.2.1 hTJ
  rwa [hΩ.perfect K hs.memK] at h

theorem isMulCommutative (hTJ : ¬ IsSylowOf 2 T J) : IsMulCommutative T :=
  (hs.spec h22 hΩ).2.2.2.2.1 hTJ

theorem conj_eq_inv (hT2 : ¬ CFSG.Open.IsElemAbelian 2 T) {s : G} (hsR : s ∈ R)
    (hsT : s ∉ normalizer (T : Set G)) {r : G} (hrR : r ∈ R)
    (hr : r ∉ R ⊓ normalizer (T : Set G)) (hr2 : r ^ 2 ∈ R ⊓ normalizer (T : Set G)) {x : G}
    (hx : x ∈ R ⊓ normalizer (T : Set G)) : r * x * r⁻¹ = x⁻¹ :=
  ((hs.spec h22 hΩ).2.2.2.2.2.1 hT2 (ne_weakClosure (hs.sylowR.le hsR) hsR hsT)).2.2 r hrR hr
    hr2 x hx

theorem le_normalizer_inf :
    R ≤ normalizer ((R ⊓ normalizer (T : Set G) : Subgroup G) : Set G) := by
  have h := (hs.spec h22 hΩ).2.2.2.2.2.2
  exact (normal_subgroupOf_iff_le_normalizer inf_le_left).mp h

end Setting22

theorem le_normalizer_of_sylow (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω) {K J T : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) (hT : IsSylowOf 2 T J)
    (hTK : T ≤ normalizer (K : Set G)) :
    J ≤ normalizer (K : Set G) ∧ K ≤ normalizer (J : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR, hTR⟩ := exists_isSylowOf_normalized hT.isPGroup hTK
  obtain ⟨UT, hUT⟩ := Assumption41.exists_rot hΩ hJ hT
  obtain ⟨UR, hUR⟩ := Assumption41.exists_rot hΩ hK hR
  have hT' : IsSylowOf 2 T (J ⊓ normalizer (K : Set G)) := hT.of_le (le_inf hT.le hTK) inf_le_left
  have hs : Setting22 Ω K J T R := ⟨hK, hJ, hKJ, hT', hUT.ne_bot, hR, hTR⟩
  have hRT : R ≤ normalizer (T : Set G) := by
    have h1 := hs.card_inf_normalizer h22 hΩ
    rw [← Assumption41.card_sylow_eq hΩ hK hJ hR hT] at h1
    have : R ⊓ normalizer (T : Set G) = R := eq_of_le_of_card_ge inf_le_left h1.ge
    exact this ▸ inf_le_right
  have hTnab : ¬ CFSG.Open.IsElemAbelian 2 T := fun h => hUT.not_isMulCommutative h.1
  have hRnab : ¬ CFSG.Open.IsElemAbelian 2 R := fun h => hUR.not_isMulCommutative h.1
  have hcK : ⁅T, K⁆ ≤ oddCoreIn K := (hs.commutator_le h22 hΩ hT).resolve_right hTnab
  obtain ⟨ET, hET, hET2, hET4⟩ := Assumption41.exists_fourGroup hΩ hJ hT
  have hKJn : K ≤ normalizer (J : Set G) :=
    le_normalizer_of_commutator_le (Assumption41.tightlyEmbedded hΩ hJ) hT.isPGroup hT.le hTK hcK
      hET hET2 hET4
  have hR' : IsSylowOf 2 R (K ⊓ normalizer (J : Set G)) :=
    hR.of_le (le_inf hR.le (hR.le.trans hKJn)) inf_le_left
  have hs' : Setting22 Ω J K R T := ⟨hJ, hK, Ne.symm hKJ, hR', hUR.ne_bot, hT, hRT⟩
  have hcJ : ⁅R, J⁆ ≤ oddCoreIn J := (hs'.commutator_le h22 hΩ hR).resolve_right hRnab
  obtain ⟨ER, hER, hER2, hER4⟩ := Assumption41.exists_fourGroup hΩ hK hR
  exact ⟨le_normalizer_of_commutator_le (Assumption41.tightlyEmbedded hΩ hK) hR.isPGroup hR.le
    (hR.le.trans hKJn) hcJ hER hER2 hER4, hKJn⟩

omit [Finite G] in
theorem mem_normalizer_of_commute' {V : Subgroup G} {c : G} (hc : ∀ u ∈ V, u * c = c * u) :
    c ∈ normalizer (V : Set G) := by
  rw [mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have : c * u * c⁻¹ = u := by rw [← hc u hu]; group
    rw [this]
    exact hu
  · intro hu
    have h := hc _ hu
    have : u = c * u * c⁻¹ := by
      calc u = c⁻¹ * ((c * u * c⁻¹) * c) := by group
        _ = c⁻¹ * (c * (c * u * c⁻¹)) := by rw [h]
        _ = c * u * c⁻¹ := by group
    rw [this]
    exact hu

section Cases

variable {K J V R U : Subgroup G}

theorem Setting22.inf_eq_bot (hs : Setting22 Ω K J V R) (hΩ : Assumption41 Ω) : V ⊓ R = ⊥ :=
  Assumption41.inf_eq_bot hΩ hs.memJ hs.memK (Ne.symm hs.ne) hs.sylowT.isPGroup
    (hs.sylowT.le.trans inf_le_left) hs.sylowR.le

theorem exists_not_mem_normalizer (hs : Setting22 Ω K J V R) (h22 : Asc76Lemma22)
    (hΩ : Assumption41 Ω) (hlt : Nat.card V < Nat.card R) :
    ∃ s ∈ R, s ∉ normalizer (V : Set G) := by
  by_contra hcon
  push Not at hcon
  have hle : R ≤ R ⊓ normalizer (V : Set G) := le_inf le_rfl hcon
  have h1 := card_le_of_le hle
  rw [hs.card_inf_normalizer h22 hΩ] at h1
  omega

theorem not_noncyclic (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω) (hs : Setting22 Ω K J V R)
    (hU : IsDihedralRot U R) (hlt : Nat.card V < Nat.card R) (hVab : IsMulCommutative V)
    (hVc : ¬ IsCyclic V) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := R ⊓ normalizer (V : Set G) with hA
  obtain ⟨eA⟩ := hs.nonempty_mulEquiv h22 hΩ hlt
  have hAR : A ≤ R := inf_le_left
  have hAV : A ≤ normalizer (V : Set G) := inf_le_right
  have hVR : V ≤ normalizer (R : Set G) := hs.le_normalizer
  have hVJ : V ≤ J := hs.sylowT.le.trans inf_le_left
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have h1 : eA ⟨a, ha⟩ * eA ⟨b, hb⟩ = eA ⟨b, hb⟩ * eA ⟨a, ha⟩ := hVab.is_comm.comm _ _
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (eA.injective h1)
  have hAc : ¬ A ≤ U := by
    intro hAU
    apply hVc
    have : IsCyclic (A.subgroupOf U) := by
      have := hU.isCyclic
      infer_instance
    have hA' : IsCyclic A := isCyclic_of_surjective (subgroupOfEquivOfLe hAU).toMonoidHom
      (subgroupOfEquivOfLe hAU).surjective
    exact isCyclic_of_surjective eA.toMonoidHom eA.surjective
  have hA2 : ∀ a ∈ A, a * a = 1 := (hU.le_or_mul_self hAR hAab).resolve_left hAc
  have hU4 : Nat.card U = 4 :=
    hU.card_eq_four hAR (hs.le_normalizer_inf h22 hΩ) hA2 hAc
  have hV2 : ∀ v ∈ V, v * v = 1 := by
    intro v hv
    have h1 := hA2 _ (eA.symm ⟨v, hv⟩).2
    have h2 : eA.symm ⟨v, hv⟩ * eA.symm ⟨v, hv⟩ = 1 := Subtype.ext h1
    rw [← map_mul, (MulEquiv.map_eq_one_iff _)] at h2
    exact congrArg Subtype.val h2
  have hVA : V ≤ normalizer (A : Set G) := fun v hv =>
    inf_le_normalizer_inf (mem_inf.mpr ⟨hVR hv, le_normalizer (le_normalizer hv)⟩)
  have hAVbot : A ⊓ V = ⊥ := by
    rw [inf_comm]
    exact le_bot_iff.mp ((inf_le_inf_left V hAR).trans (hs.inf_eq_bot hΩ).le)
  obtain ⟨v₁, hv₁V, hv₁⟩ : ∃ v ∈ V, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hVbot : V = ⊥ := eq_bot_iff.mpr fun v hv => (mem_bot).mpr (hcon v hv)
    exact hVc (by rw [hVbot]; infer_instance)
  obtain ⟨v₂, hv₂V, hv₂⟩ : ∃ v ∈ V, v ∉ zpowers v₁ := by
    by_contra hcon
    push Not at hcon
    apply hVc
    have : zpowers v₁ = V := le_antisymm ((zpowers_le).mpr hv₁V) hcon
    rw [← this]
    infer_instance
  have hv₂1 : v₂ ≠ 1 := fun h => hv₂ (h ▸ one_mem _)
  have hv₁₂ : v₁ * v₂ ≠ 1 := by
    intro h
    apply hv₂
    have : v₂ = v₁⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_mem (mem_zpowers v₁)
  obtain ⟨ρ, hρ, hρo⟩ := hU.exists_gen
  have hρU : ρ ∈ U := hρ ▸ mem_zpowers ρ
  rw [hU4] at hρo
  have hconj : ∀ v ∈ V, v * ρ * v⁻¹ = ρ ∨ v * ρ * v⁻¹ = ρ⁻¹ := by
    intro v hv
    have hy : v * ρ * v⁻¹ ∈ U := (mem_normalizer_iff.mp (hU.normalizer_le (hVR hv)) ρ).mp hρU
    have hyy : v * ρ * v⁻¹ * (v * ρ * v⁻¹) ≠ 1 := by
      intro h
      apply hU.gen_mul_self_ne_one (hρo.trans hU4.symm)
      calc ρ * ρ = v⁻¹ * (v * ρ * v⁻¹ * (v * ρ * v⁻¹)) * v := by group
        _ = 1 := by rw [h]; group
    rw [← hρ] at hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hk] at hyy ⊢
    rw [← zpow_mod_orderOf, hρo] at hyy ⊢
    have hk4 : k % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos k (by norm_num)
    have hk0 : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg k (by norm_num)
    have h4 : ρ ^ (4 : ℤ) = 1 := by
      rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, ← hρo, pow_orderOf_eq_one]
    interval_cases h : k % ((4 : ℕ) : ℤ)
    · exact absurd (by simp) hyy
    · left; simp
    · exfalso; apply hyy
      rw [← zpow_add]; norm_num [h4]
    · right
      rw [show (3 : ℤ) = 4 + (-1) by norm_num, zpow_add, h4, one_mul, zpow_neg, zpow_one]
  obtain ⟨v, hvV, hv1, hvρ⟩ : ∃ v ∈ V, v ≠ 1 ∧ v * ρ * v⁻¹ = ρ := by
    rcases hconj v₁ hv₁V with h1 | h1
    · exact ⟨v₁, hv₁V, hv₁, h1⟩
    rcases hconj v₂ hv₂V with h2 | h2
    · exact ⟨v₂, hv₂V, hv₂1, h2⟩
    refine ⟨v₁ * v₂, mul_mem hv₁V hv₂V, hv₁₂, ?_⟩
    calc v₁ * v₂ * ρ * (v₁ * v₂)⁻¹ = v₁ * (v₂ * ρ * v₂⁻¹) * v₁⁻¹ := by group
      _ = (v₁ * ρ * v₁⁻¹)⁻¹ := by rw [h2]; group
      _ = ρ := by rw [h1, inv_inv]
  have hvU : ∀ u ∈ U, u * v = v * u := by
    intro u hu
    rw [← hρ] at hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have : v * ρ ^ k * v⁻¹ = ρ ^ k := by rw [← conj_zpow, hvρ]
    calc ρ ^ k * v = (v * ρ ^ k * v⁻¹) * v := by rw [this]
      _ = v * ρ ^ k := by group
  have hvA : ∀ a ∈ A, a * v = v * a := fun a ha =>
    commute_of_inf_eq_bot hAV hVA hAVbot ha hvV
  obtain ⟨s, hsA, hsU⟩ := Set.not_subset.mp hAc
  have hvR : R ≤ centralizer ({v} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    by_cases hxU : x ∈ U
    · exact hvU x hxU
    · have hsx : s⁻¹ * x ∈ U :=
        hU.mul_mem_of_not_mem (inv_mem (hAR hsA)) hx (fun h => hsU (by simpa using inv_mem h))
          hxU
      calc x * v = s * ((s⁻¹ * x) * v) := by group
        _ = s * (v * (s⁻¹ * x)) := by rw [hvU _ hsx]
        _ = (s * v) * (s⁻¹ * x) := by group
        _ = (v * s) * (s⁻¹ * x) := by rw [hvA s hsA]
        _ = v * x := by group
  have hRJ : R ≤ normalizer (J : Set G) :=
    hvR.trans (centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hs.memJ) (hVJ hvV) hv1
      (hV2 v hvV))
  obtain ⟨-, hJK⟩ := le_normalizer_of_sylow h22 hΩ hs.memJ hs.memK (Ne.symm hs.ne) hs.sylowR hRJ
  have hVJ' : IsSylowOf 2 V J := by
    have h1 := hs.sylowT
    rwa [inf_eq_left.mpr hJK] at h1
  rw [Assumption41.card_sylow_eq hΩ hs.memJ hs.memK hVJ' hs.sylowR] at hlt
  exact lt_irrefl _ hlt

omit [Finite G] in
theorem exists_sq_mem_of_ne {A U : Subgroup G} (hU : IsPGroup 2 U) (hAU : A ≤ U) (hne : A ≠ U) :
    ∃ r ∈ U, r ∉ A ∧ r ^ 2 ∈ A := by
  classical
  obtain ⟨r₀, hr₀U, hr₀A⟩ := Set.not_subset.mp fun h => hne (le_antisymm hAU h)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hU) ⟨r₀, hr₀U⟩
  have hex : ∃ m, r₀ ^ (2 ^ m) ∈ A := ⟨k, by
    have h1 := pow_orderOf_eq_one (⟨r₀, hr₀U⟩ : U)
    rw [hk] at h1
    have h2 : r₀ ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val h1
    rw [h2]
    exact A.one_mem⟩
  have hm := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hm
    exact hr₀A hm
  obtain ⟨m, hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  refine ⟨r₀ ^ (2 ^ m), U.pow_mem hr₀U _, Nat.find_min hex (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ]
  rw [hm'] at hm
  exact hm

theorem case_cyclic (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω) (hs : Setting22 Ω K J V R)
    (hU : IsDihedralRot U R) (hlt : Nat.card V < Nat.card R) (hVc : IsCyclic V)
    (hV2 : Nat.card V ≠ 2) :
    R ⊓ normalizer (V : Set G) = U ∧ Nonempty (V ≃* U) ∧ ⁅V, U⁆ = ⊥ ∧
      IsWreathedTwoGroup (V ⊔ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := R ⊓ normalizer (V : Set G) with hA
  obtain ⟨eA⟩ := hs.nonempty_mulEquiv h22 hΩ hlt
  have hAcard : Nat.card A = Nat.card V := hs.card_inf_normalizer h22 hΩ
  have hAR : A ≤ R := inf_le_left
  have hVR : V ≤ normalizer (R : Set G) := hs.le_normalizer
  have hVp : IsPGroup 2 V := hs.sylowT.isPGroup
  have hV4 : 4 ≤ Nat.card V := by
    obtain ⟨n, hn⟩ := hVp.exists_card_eq
    have hV1 : Nat.card V ≠ 1 := fun h => hs.ne_bot (eq_bot_of_card_eq V h)
    rw [hn] at hV1 hV2 ⊢
    have hn2 : 2 ≤ n := by
      by_contra hlt2
      interval_cases n <;> simp_all
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top V).mp hVc
  have hgV : g ∈ V := hg ▸ mem_zpowers g
  have hgo : orderOf g = Nat.card V := by rw [← hg, Nat.card_zpowers]
  have hgg : g * g ≠ 1 := by
    intro h
    have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hAc : IsCyclic A := isCyclic_of_surjective eA.symm.toMonoidHom eA.symm.surjective
  obtain ⟨a, ha⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top A).mp hAc
  have haA : a ∈ A := ha ▸ mem_zpowers a
  have hao : orderOf a = Nat.card V := by rw [← hAcard, ← ha, Nat.card_zpowers]
  have haa : a * a ≠ 1 := by
    intro h
    have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hAU : A ≤ U := ha ▸ (zpowers_le).mpr (hU.mem_of_mul_self_ne_one (hAR haA) haa)
  obtain ⟨s, hsR, hsN⟩ := exists_not_mem_normalizer hs h22 hΩ hlt
  have hVnab : ¬ CFSG.Open.IsElemAbelian 2 V := fun h =>
    hgg (by rw [← pow_two]; exact h.2 g hgV)
  have hAeq : A = U := by
    by_contra hne
    obtain ⟨r, hrU, hrA, hr2⟩ := exists_sq_mem_of_ne (hU.isPGroup.to_le hU.le) hAU hne
    have hinv := hs.conj_eq_inv h22 hΩ hVnab hsR hsN (hU.le hrU) hrA hr2 haA
    rw [hU.commute_of_mem hrU (hAU haA), mul_assoc, mul_inv_cancel, mul_one] at hinv
    apply haa
    calc a * a = a⁻¹ * a := by rw [← hinv]
      _ = 1 := inv_mul_cancel a
  refine ⟨hAeq, ⟨eA.symm.trans (MulEquiv.subgroupCongr hAeq)⟩, ?_, ?_⟩
  ·
    have hVU : V ≤ normalizer (U : Set G) := fun v hv => hU.normalizer_le (hVR hv)
    have hUV : U ≤ normalizer (V : Set G) := hAeq ▸ inf_le_right
    have hinf : V ⊓ U = ⊥ := le_bot_iff.mp ((inf_le_inf_left V hU.le).trans (hs.inf_eq_bot hΩ).le)
    rw [commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [mem_centralizer_iff]
    intro u hu
    exact (commute_of_inf_eq_bot hVU hUV hinf hv hu).symm
  ·
    rcases hs.dihedral_or_wreathed h22 hΩ hsR hsN hVc with hD | hW
    · exfalso
      have hPnc : ¬ IsMulCommutative ↥(R ⊔ V) := fun hc => hU.not_isMulCommutative
        ⟨⟨fun x y => Subtype.ext (by
          have := congrArg Subtype.val
            (hc.is_comm.comm (⟨x, mem_sup_left x.2⟩ : ↥(R ⊔ V)) ⟨y, mem_sup_left y.2⟩)
          exact this)⟩⟩
      obtain ⟨C, hC⟩ := exists_isDihedralRot hD hPnc
      obtain ⟨zC, -, -, -, hzCuniq, -⟩ := hC.exists_involution
      obtain ⟨ρ, hρ, hρo⟩ := hU.exists_gen
      have hρU : ρ ∈ U := hρ ▸ mem_zpowers ρ
      have hUC : U ≤ C := hρ ▸ (zpowers_le).mpr
        (hC.mem_of_mul_self_ne_one (mem_sup_left (hU.le hρU)) (hU.gen_mul_self_ne_one hρo))
      have hVC : V ≤ C := hg ▸ (zpowers_le).mpr
        (hC.mem_of_mul_self_ne_one (mem_sup_right hgV) hgg)
      obtain ⟨z, hzU, hz1, hzz, -, -⟩ := hU.exists_involution
      have h2V : 2 ∣ Nat.card V := by
        obtain ⟨n, hn⟩ := hVp.exists_card_eq
        rw [hn] at hV4 ⊢
        have : n ≠ 0 := by rintro rfl; norm_num at hV4
        exact dvd_pow_self 2 this
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 h2V
      have ht1 : (t : G) ≠ 1 := by
        intro h
        have : t = 1 := Subtype.ext h
        rw [this, orderOf_one] at ht
        exact absurd ht (by norm_num)
      have htt : (t : G) * t = 1 := by
        have := pow_orderOf_eq_one t
        rw [ht, pow_two] at this
        exact congrArg Subtype.val this
      have hz := (hzCuniq z (hUC hzU) hzz).resolve_left hz1
      have ht' := (hzCuniq t (hVC t.2) htt).resolve_left ht1
      have hzV : z ∈ V ⊓ R := mem_inf.mpr ⟨hz ▸ ht' ▸ t.2, hU.le hzU⟩
      rw [hs.inf_eq_bot hΩ, mem_bot] at hzV
      exact hz1 hzV
    · rwa [sup_comm] at hW

theorem case_two (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω) (hs : Setting22 Ω K J V R)
    (hU : IsDihedralRot U R) (hV2 : Nat.card V = 2) :
    IsDihedralTwoGroup (V ⊔ R) ∧ ∀ v ∈ V, v ≠ 1 → ∀ u ∈ U, v * u * v⁻¹ = u⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVR : V ≤ normalizer (R : Set G) := hs.le_normalizer
  have hinf : V ⊓ R = ⊥ := hs.inf_eq_bot hΩ
  obtain ⟨z, hzU, hz1, hzz, hzuniq, hzc⟩ := hU.exists_involution
  have hA2 : Nat.card (R ⊓ normalizer (V : Set G) : Subgroup G) = 2 :=
    (hs.card_inf_normalizer h22 hΩ).trans hV2
  have key : ∀ v ∈ V, v ≠ 1 → v * v = 1 ∧ v ∉ R ∧ zpowers v = V ∧
      ∀ x ∈ R, x * v = v * x → x ∈ U ∧ x * x = 1 := by
    intro v hvV hv1
    have hvv : v * v = 1 := by
      have := pow_card_eq_one' (x := (⟨v, hvV⟩ : V))
      rw [hV2, pow_two] at this
      exact congrArg Subtype.val this
    have hvR : v ∉ R := fun h => hv1 (by
      have := mem_inf.mpr ⟨hvV, h⟩
      rwa [hinf, mem_bot] at this)
    have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hvv) hv1
    have hzpow : zpowers v = V := eq_of_le_of_card_ge ((zpowers_le).mpr hvV)
      (by rw [Nat.card_zpowers, hvo, hV2])
    refine ⟨hvv, hvR, hzpow, fun x hx hxv => ?_⟩
    have hxN : x ∈ R ⊓ normalizer (V : Set G) := mem_inf.mpr ⟨hx, by
      rw [← hzpow]
      exact mem_normalizer_of_commute' (fun u hu => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        exact ((Commute.zpow_left (Commute.symm hxv) k)).eq)⟩
    have hxx : x * x = 1 := by
      have := pow_card_eq_one' (x := (⟨x, hxN⟩ : (R ⊓ normalizer (V : Set G) : Subgroup G)))
      rw [hA2, pow_two] at this
      exact congrArg Subtype.val this
    refine ⟨?_, hxx⟩
    by_contra hxU
    have hvz : v * z * v⁻¹ = z := by
      have hc : ∀ y ∈ R, v * z * v⁻¹ * y = y * (v * z * v⁻¹) := by
        intro y hy
        have hy' : v⁻¹ * y * v ∈ R := by
          have := (mem_normalizer_iff.mp (inv_mem (hVR hvV)) y).mp hy
          simpa using this
        calc v * z * v⁻¹ * y = v * (z * (v⁻¹ * y * v)) * v⁻¹ := by group
          _ = v * ((v⁻¹ * y * v) * z) * v⁻¹ := by rw [hzc _ hy']
          _ = y * (v * z * v⁻¹) := by group
      have hmem : v * z * v⁻¹ ∈ R := (mem_normalizer_iff.mp (hVR hvV) z).mp (hU.le hzU)
      rcases hU.eq_of_central hzuniq hmem hc with h | h
      · exfalso
        apply hz1
        calc z = v⁻¹ * (v * z * v⁻¹) * v := by group
          _ = 1 := by rw [h]; group
      · exact h
    have hzN : z ∈ R ⊓ normalizer (V : Set G) := mem_inf.mpr ⟨hU.le hzU, by
      rw [← hzpow]
      exact mem_normalizer_of_commute' (fun u hu => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        have hzv : v * z = z * v := by
          calc v * z = v * z * v⁻¹ * v := by group
            _ = z * v := by rw [hvz]
        exact ((Commute.zpow_left hzv k)).eq)⟩
    have hx1 : x ≠ 1 := fun h => hxU (h ▸ U.one_mem)
    have hxz : x ≠ z := fun h => hxU (h ▸ hzU)
    have h4 := card_fourGroup hxx hzz (hzc x hx) hx1 hz1 hxz
    have hle : fourGroup x z hxx hzz (hzc x hx) ≤ R ⊓ normalizer (V : Set G) := by
      intro y hy
      rcases mem_fourGroup.mp hy with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hxN
      · exact hzN
      · exact mul_mem hxN hzN
    have := card_le_of_le hle
    omega
  refine ⟨?_, fun v hvV hv1 =>
    hU.conj_eq_inv_of_centralizer (hVR hvV) (key v hvV hv1).1 (key v hvV hv1).2.2.2⟩
  obtain ⟨v, hvV, hv1⟩ : ∃ v ∈ V, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hs.ne_bot (eq_bot_iff.mpr fun x hx => (mem_bot).mpr (hcon x hx))
  obtain ⟨hvv, hvR, hzpow, hC⟩ := key v hvV hv1
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hinvU := hU.conj_eq_inv_of_centralizer (hVR hvV) hvv hC
  obtain ⟨s, hsR, hsU⟩ := hU.exists_not_mem
  have hss : s * s = 1 := hU.mul_self s hsR hsU
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hs'R : v * s * v⁻¹ ∈ R := (mem_normalizer_iff.mp (hVR hvV) s).mp hsR
  have hs'U : v * s * v⁻¹ ∉ U := fun h => hsU (by
    have := (mem_normalizer_iff.mp (inv_mem (hU.normalizer_le (hVR hvV))) _).mp h
    simpa [mul_assoc] using this)
  set u₀ := s * (v * s * v⁻¹) with hu₀
  have hu₀U : u₀ ∈ U := hU.mul_mem_of_not_mem hsR hs'R hsU hs'U
  have hnsq : ∀ y ∈ U, y * y ≠ u₀ := by
    intro y hy hyy
    have hfix : (s * y) * v = v * (s * y) := by
      have h1 : v * (s * y) * v⁻¹ = s * y := by
        calc v * (s * y) * v⁻¹ = (v * s * v⁻¹) * (v * y * v⁻¹) := by group
          _ = s⁻¹ * u₀ * y⁻¹ := by rw [hinvU y hy, hu₀]; group
          _ = s * y := by rw [← hyy, hsinv]; group
      calc s * y * v = (v * (s * y) * v⁻¹) * v := by rw [h1]
        _ = v * (s * y) := by group
    exact hsU (by
      have := (hC _ (R.mul_mem hsR (hU.le hy)) hfix).1
      have h2 : s = s * y * y⁻¹ := by group
      rw [h2]
      exact U.mul_mem this (U.inv_mem hy))
  obtain ⟨ρ, hρ, hρo⟩ := hU.exists_gen
  have hρU : ρ ∈ U := hρ ▸ mem_zpowers ρ
  have hgen : U ≤ zpowers u₀ := by
    have hu₀' := hu₀U
    rw [← hρ] at hu₀'
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hu₀'
    have hjodd : Odd j := by
      by_contra hev
      rw [Int.not_odd_iff_even] at hev
      obtain ⟨i, rfl⟩ := hev
      exact hnsq (ρ ^ i) (U.zpow_mem hρU i) (by rw [← zpow_add, hj])
    obtain ⟨n, hn⟩ := (hU.isPGroup.to_le hU.le).exists_card_eq
    obtain ⟨i, hi⟩ := hjodd
    have hcop : IsCoprime j ((2 : ℤ) ^ n) := by
      have h2 : IsCoprime j 2 := ⟨1, -i, by rw [hi]; ring⟩
      exact h2.pow_right
    obtain ⟨a, b, hab⟩ := hcop
    have hρq : ρ ^ ((2 : ℤ) ^ n) = 1 := by
      have := pow_orderOf_eq_one ρ
      rw [hρo, hn] at this
      exact_mod_cast this
    have hρmem : ρ ∈ zpowers u₀ := by
      have h1 : ρ = u₀ ^ a * (ρ ^ ((2 : ℤ) ^ n)) ^ b := by
        rw [← hj, ← zpow_mul, ← zpow_mul, ← zpow_add]
        conv_lhs => rw [← zpow_one ρ]
        congr 1
        linear_combination hab.symm
      rw [h1, hρq, one_zpow, mul_one]
      exact zpow_mem (mem_zpowers u₀) a
    rw [← hρ]
    exact (zpowers_le).mpr hρmem
  have hw : (s * v) * (s * v) = u₀ := by rw [hu₀, hvinv]; group
  have hu₀w : u₀ ∈ zpowers (s * v) := by
    rw [← hw, ← pow_two]
    exact pow_mem (mem_zpowers _) 2
  have hUw : U ≤ zpowers (s * v) := hgen.trans ((zpowers_le).mpr hu₀w)
  have hsP : s ∈ R ⊔ V := mem_sup_left hsR
  have hwP : s * v ∈ R ⊔ V := mul_mem hsP (mem_sup_right hvV)
  have hgenP : zpowers (s * v) ⊔ zpowers s = R ⊔ V := by
    apply le_antisymm
    · exact sup_le ((zpowers_le).mpr hwP) ((zpowers_le).mpr hsP)
    · apply sup_le
      · intro r hr
        by_cases hrU : r ∈ U
        · exact mem_sup_left (hUw hrU)
        · have hsr : s⁻¹ * r ∈ U :=
            hU.mul_mem_of_not_mem (inv_mem hsR) hr (fun h => hsU (by simpa using inv_mem h)) hrU
          have : r = s * (s⁻¹ * r) := by group
          rw [this]
          exact mul_mem (mem_sup_right (mem_zpowers s)) (mem_sup_left (hUw hsr))
      · rw [← hzpow]
        apply (zpowers_le).mpr
        have : s * (s * v) ∈ zpowers (s * v) ⊔ zpowers s :=
          mul_mem (mem_sup_right (mem_zpowers s)) (mem_sup_left (mem_zpowers _))
        rwa [← mul_assoc, hss, one_mul] at this
  have hconj : s * (s * v) * s⁻¹ = (s * v)⁻¹ := by
    calc s * (s * v) * s⁻¹ = (s * s) * v * s⁻¹ := by group
      _ = v⁻¹ * s⁻¹ := by rw [hss, one_mul, hvinv]
      _ = (s * v)⁻¹ := (mul_inv_rev s v).symm
  have hPp : IsPGroup 2 ↥(R ⊔ V) :=
    IsPGroup.to_sup_of_normal_left' hU.isPGroup hs.sylowT.isPGroup hVR
  have hDG : HasDihedralGenerators ↥(R ⊔ V) := by
    refine ⟨⟨s * v, hwP⟩, ⟨s, hsP⟩, ?_, ?_, ?_, ?_⟩
    · apply Subgroup.map_injective (R ⊔ V).subtype_injective
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
      exact hgenP
    · exact Subtype.ext (by simp [pow_two, hss])
    · exact Subtype.ext (by simpa using hconj)
    · intro hmem
      have hmem' : s ∈ zpowers (s * v) := by
        have := Subgroup.mem_map_of_mem (R ⊔ V).subtype hmem
        rwa [MonoidHom.map_zpowers] at this
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem'
      have hcomm : Commute s (s * v) := by
        have h1 : Commute ((s * v) ^ k) (s * v) := (Commute.refl (s * v)).zpow_left k
        rwa [hk] at h1
      have h1 := hconj
      rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one] at h1
      have hw1 : u₀ = 1 := by
        rw [← hw]
        calc s * v * (s * v) = (s * v)⁻¹ * (s * v) := by rw [← h1]
          _ = 1 := inv_mul_cancel _
      have hUbot : U = ⊥ := le_bot_iff.mp (hgen.trans (by rw [hw1, zpowers_one_eq_bot]))
      have := hU.four_le
      rw [hUbot, card_bot] at this
      omega
  rcases isCyclic_or_isDihedral_of_hasDihedralGenerators hPp hDG with hcyc | hD
  · exfalso
    apply hU.not_isMulCommutative
    have hc : IsMulCommutative ↥(R ⊔ V) := inferInstance
    exact ⟨⟨fun x y => Subtype.ext (by
      have := congrArg Subtype.val
        (hc.is_comm.comm (⟨x, mem_sup_left x.2⟩ : ↥(R ⊔ V)) ⟨y, mem_sup_left y.2⟩)
      exact this)⟩⟩
  · rwa [sup_comm] at hD

end Cases

theorem lemma415 (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω) {K J R U V : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hR : IsSylowOf 2 R K) (hU : IsDihedralRot U R)
    (hV : IsSylowOf 2 V (J ⊓ normalizer (K : Set G))) (hV1 : V ≠ ⊥)
    (hVR : V ≤ normalizer (R : Set G)) :
    (IsSylowOf 2 V J ∧ J ≤ normalizer (K : Set G) ∧ K ≤ normalizer (J : Set G)) ∨
    (Nonempty (V ≃* U) ∧ ⁅V, U⁆ = ⊥ ∧ IsWreathedTwoGroup (V ⊔ R) ∧
      R ⊓ normalizer (V : Set G) = U) ∨
    (Nat.card V = 2 ∧ IsDihedralTwoGroup (V ⊔ R) ∧
      ∀ v ∈ V, v ≠ 1 → ∀ u ∈ U, v * u * v⁻¹ = u⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hKJ : K = J
  · subst hKJ
    left
    have hV' : IsSylowOf 2 V K := by
      have h1 := hV
      rwa [inf_eq_left.mpr le_normalizer] at h1
    exact ⟨hV', le_normalizer, le_normalizer⟩
  have hs : Setting22 Ω K J V R := ⟨hK, hJ, hKJ, hV, hV1, hR, hVR⟩
  obtain ⟨T, hT, hVT⟩ := exists_isSylowOf_le hV.isPGroup (hV.le.trans inf_le_left)
  have hTR : Nat.card T = Nat.card R := Assumption41.card_sylow_eq hΩ hJ hK hT hR
  have hVle : Nat.card V ≤ Nat.card R := hTR ▸ card_le_of_le hVT
  by_cases hVeq : Nat.card V = Nat.card R
  · left
    have hVT' : V = T := eq_of_le_of_card_ge hVT (by rw [hVeq, hTR])
    have hVJ : IsSylowOf 2 V J := by rw [hVT']; exact hT
    obtain ⟨h1, h2⟩ := le_normalizer_of_sylow h22 hΩ hK hJ hKJ hVJ (hV.le.trans inf_le_right)
    exact ⟨hVJ, h1, h2⟩
  have hlt : Nat.card V < Nat.card R := lt_of_le_of_ne hVle hVeq
  have hVnJ : ¬ IsSylowOf 2 V J := fun h =>
    hVeq (Assumption41.card_sylow_eq hΩ hJ hK h hR)
  have hVab := hs.isMulCommutative h22 hΩ hVnJ
  by_cases hVc : IsCyclic V
  · by_cases hV2 : Nat.card V = 2
    · right; right
      obtain ⟨h1, h2⟩ := case_two h22 hΩ hs hU hV2
      exact ⟨hV2, h1, h2⟩
    · right; left
      obtain ⟨h1, h2, h3, h4⟩ := case_cyclic h22 hΩ hs hU hlt hVc hV2
      exact ⟨h2, h3, h4, h1⟩
  · exact (not_noncyclic h22 hΩ hs hU hlt hVab hVc).elim

end CFSG.ComponentClassification.Asc76.Sec4
