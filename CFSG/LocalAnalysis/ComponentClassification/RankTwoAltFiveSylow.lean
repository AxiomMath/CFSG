module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveGold

public section

open Subgroup Equiv CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G] [Finite G]

@[expose] def EpsOne (V P : Subgroup G) : Prop :=
  IsSylowOf 2 P (normalizer (V : Set G))

theorem lt_inf_normalizer {Q S : Subgroup G} (hS : IsPGroup 2 S) (hQS : Q < S) :
    Q < S ⊓ normalizer (Q : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : Q.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hQS.ne (le_antisymm hQS.le (subgroupOf_eq_top.1 h))
  obtain ⟨x, hxN, hxQ⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  rw [← subgroupOf_normalizer_eq hQS.le] at hxN
  refine lt_of_le_of_ne (le_inf hQS.le le_normalizer) fun h => hxQ ?_
  have hx : (x : G) ∈ S ⊓ normalizer (Q : Set G) := mem_inf.2 ⟨x.2, hxN⟩
  rw [← h] at hx
  exact hx

omit [Finite G] in
theorem rightConjugate_injective {X Y : Subgroup G} {s : G}
    (h : rightConjugate X s = rightConjugate Y s) : X = Y := by
  have h1 := congrArg (fun Z => rightConjugate Z s⁻¹) h
  simp only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
  exact h1

omit [Finite G] in
theorem isElemAbelian_of_le {E F : Subgroup G} (hE : IsElemAbelian 2 E) (hFE : F ≤ E) :
    IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE hFE

namespace Setting310

variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

theorem not_isPGroup_two : ¬ IsPGroup 2 G := by
  intro h2
  obtain ⟨eA⟩ := h.equiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (h2.to_subgroup A)
  rw [Nat.card_congr eA.toEquiv, card_A5] at hk
  have h4 : ¬ (3 : ℕ) ∣ 2 ^ k := fun h5 =>
    absurd ((Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h5)) (by norm_num)
  exact h4 (hk ▸ (by norm_num : (3 : ℕ) ∣ 60))

theorem ne_of_inf_eq {V' : Subgroup G} (hinf : (R ⊔ T) ⊓ V' = V₀) : R ⊔ T ≠ V' := by
  intro he
  have h1 : V₀ = R ⊔ T := by rw [← hinf, ← he, inf_idem]
  have h2 := h.card_V₀
  rw [h1, h.loc.card] at h2
  omega

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

theorem eq_or_eq_of_elemAbelian {V' : Subgroup G}
    (hV' : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (hV₀V' : V₀ ≤ V') (hV'16 : Nat.card V' = 16)
    {E : Subgroup G} (hEP : E ≤ P) (hE : IsElemAbelian 2 E) (hE16 : Nat.card E = 16) :
    E = R ⊔ T ∨ E = V' := by
  rcases h.le_or_le_of_elemAbelian hP hPC hV' hV₀V' hEP hE with h1 | h1
  · exact Or.inl (eq_of_le_of_card_ge h1 (by rw [h.loc.card, hE16]))
  · exact Or.inr (eq_of_le_of_card_ge h1 (by rw [hV'16, hE16]))

section IIa

variable (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIa

theorem sylow_of_eps_one (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P)
    (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G)
    (hPS : P ≤ S) :
    (S : Subgroup G) ≤ normalizer (P : Set G) ∧ Nat.card (S : Subgroup G) = 128 ∧
      (S : Subgroup G) ⊓ normalizer ((R ⊔ T : Subgroup G) : Set G) = P ∧
      (∀ s ∈ (S : Subgroup G), s ∉ P →
        rightConjugate (R ⊔ T) s = V' ∧ rightConjugate V' s = R ⊔ T) ∧
      (∀ E : Subgroup G, E ≤ S → IsElemAbelian 2 E → Nat.card E = 16 → E = R ⊔ T ∨ E = V') ∧
      normalizer ((S : Subgroup G) : Set G) ≤ normalizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hε' : IsSylowOf 2 P (normalizer ((R ⊔ T : Subgroup G) : Set G)) := hε
  have hSp : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  have hPS' : P < S := lt_of_le_of_ne hPS (h.P_not_sylow hP hPC hGold hGs hIIa hP64 hVP S).symm
  obtain ⟨S₂, hS₂⟩ : ∃ S₂ : Subgroup G, (S : Subgroup G) ⊓ normalizer (P : Set G) = S₂ :=
    ⟨_, rfl⟩
  have hPS₂ : P < S₂ := hS₂ ▸ lt_inf_normalizer hSp hPS'
  have hS₂S : S₂ ≤ S := hS₂ ▸ inf_le_left
  have hS₂N : S₂ ≤ normalizer (P : Set G) := hS₂ ▸ inf_le_right
  have hS₂p : IsPGroup 2 S₂ := hSp.to_le hS₂S
  have hS₂V : S₂ ⊓ normalizer ((R ⊔ T : Subgroup G) : Set G) = P :=
    hε'.eq_of_le (le_inf hPS₂.le hε'.le) inf_le_right (hS₂p.to_le inf_le_left)
  have hconjP : ∀ s ∈ S₂, ∀ X : Subgroup G, X ≤ P → rightConjugate X s ≤ P := by
    intro s hs X hX
    have h1 : rightConjugate X s ≤ rightConjugate P s := map_mono hX
    rwa [(rightConjugate_eq_self_iff P s).mpr (hS₂N hs)] at h1
  have hV₀V' : V₀ ≤ V' := hinf ▸ inf_le_right
  have hEP : ∀ E : Subgroup G, E ≤ P → IsElemAbelian 2 E → Nat.card E = 16 →
      E = R ⊔ T ∨ E = V' := fun E hE hEe hE16 =>
    h.eq_or_eq_of_elemAbelian hP hPC hV'inv hV₀V' hV'16 hE hEe hE16
  have hVV' : R ⊔ T ≠ V' := h.ne_of_inf_eq hinf
  have hswap : ∀ s ∈ S₂, s ∉ P →
      rightConjugate (R ⊔ T) s = V' ∧ rightConjugate V' s = R ⊔ T := by
    intro s hs hsP
    have hVs : rightConjugate (R ⊔ T) s = V' := by
      rcases hEP _ (hconjP s hs _ hVP) (isElemAbelian_rightConjugate h.loc.elem s)
        (by rw [rightConjugate_card, h.loc.card]) with h1 | h1
      · exfalso
        apply hsP
        rw [← hS₂V]
        exact mem_inf.mpr ⟨hs, (rightConjugate_eq_self_iff _ s).mp h1⟩
      · exact h1
    refine ⟨hVs, ?_⟩
    rcases hEP _ (hconjP s hs _ hV'P) (isElemAbelian_rightConjugate hV'e s)
      (by rw [rightConjugate_card, hV'16]) with h1 | h1
    · exact h1
    · exact absurd (rightConjugate_injective (hVs.trans h1.symm)) hVV'
  obtain ⟨s₀, hs₀, hs₀P⟩ := IsConcreteLE.exists_of_lt hPS₂
  have hidx : (P.subgroupOf S₂).index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨s₀, hs₀⟩, hs₀P, fun b => ?_⟩
    by_cases hb : (b : G) ∈ P
    · exact Or.inr hb
    · left
      change (b : G) * s₀ ∈ P
      rw [← hS₂V]
      refine mem_inf.mpr ⟨mul_mem b.2 hs₀, ?_⟩
      rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, (hswap b b.2 hb).1,
        (hswap s₀ hs₀ hs₀P).2]
  have hS₂128 : Nat.card S₂ = 128 := by
    have h1 := Subgroup.card_mul_index (P.subgroupOf S₂)
    rw [hidx, Nat.card_congr (subgroupOfEquivOfLe hPS₂.le).toEquiv, hP64] at h1
    omega
  have hES₂ : ∀ E : Subgroup G, E ≤ S₂ → IsElemAbelian 2 E → Nat.card E = 16 →
      E = R ⊔ T ∨ E = V' := by
    intro E hES hE hE16
    by_cases hEP' : E ≤ P
    · exact hEP E hEP' hE hE16
    exfalso
    obtain ⟨e, heE, heP⟩ := IsConcreteLE.not_le_iff_exists.mp hEP'
    have hle : P.relIndex E ≤ 2 := by
      have h1 := Subgroup.relIndex_le_of_le_right (H := P) hES (by
        change (P.subgroupOf S₂).index ≠ 0
        rw [hidx]
        norm_num)
      exact h1.trans (le_of_eq hidx)
    have h8 : 8 ≤ Nat.card (P ⊓ E : Subgroup G) := by
      have h1 := Subgroup.relIndex_mul_card P E
      rw [hE16] at h1
      have h2 : 16 ≤ 2 * Nat.card (P ⊓ E : Subgroup G) :=
        h1 ▸ Nat.mul_le_mul_right _ hle
      omega
    have hcomm : ∀ x ∈ P ⊓ E, e * x * e⁻¹ = x := by
      intro x hx
      have := congrArg Subtype.val (hE.1.is_comm.comm ⟨e, heE⟩ ⟨x, (mem_inf.mp hx).2⟩)
      simp only [coe_mul] at this
      rw [this]
      group
    obtain ⟨hVe, hV'e'⟩ := hswap e (hES heE) heP
    have hsub : P ⊓ E ≤ V₀ := by
      rcases h.le_or_le_of_elemAbelian hP hPC hV'inv hV₀V' inf_le_left
        (isElemAbelian_of_le hE inf_le_right) with h1 | h1
      · intro x hx
        rw [← hinf]
        refine mem_inf.mpr ⟨h1 hx, ?_⟩
        rw [← hVe, mem_rightConjugate_iff, hcomm x hx]
        exact h1 hx
      · intro x hx
        rw [← hinf]
        refine mem_inf.mpr ⟨?_, h1 hx⟩
        rw [← hV'e', mem_rightConjugate_iff, hcomm x hx]
        exact h1 hx
    have := Subgroup.card_le_of_le hsub
    rw [h.card_V₀] at this
    omega
  have hNS₂ : normalizer (S₂ : Set G) ≤ normalizer (P : Set G) := by
    intro x hx
    have hS₂x : rightConjugate S₂ x = S₂ := (rightConjugate_eq_self_iff S₂ x).mpr hx
    have hXS : ∀ X : Subgroup G, X ≤ S₂ → rightConjugate X x ≤ S₂ := fun X hX => by
      have h1 : rightConjugate X x ≤ rightConjugate S₂ x := map_mono hX
      rwa [hS₂x] at h1
    have hVx : rightConjugate (R ⊔ T) x ≤ P := by
      rcases hES₂ _ (hXS _ (hVP.trans hPS₂.le)) (isElemAbelian_rightConjugate h.loc.elem x)
        (by rw [rightConjugate_card, h.loc.card]) with h1 | h1
      · rw [h1]; exact hVP
      · rw [h1]; exact hV'P
    have hV'x : rightConjugate V' x ≤ P := by
      rcases hES₂ _ (hXS _ (hV'P.trans hPS₂.le)) (isElemAbelian_rightConjugate hV'e x)
        (by rw [rightConjugate_card, hV'16]) with h1 | h1
      · rw [h1]; exact hVP
      · rw [h1]; exact hV'P
    have hPx : rightConjugate P x = P := by
      refine eq_of_le_of_card_ge ?_ (by rw [rightConjugate_card])
      calc rightConjugate P x = rightConjugate ((R ⊔ T) ⊔ V') x := by rw [hsup]
        _ = rightConjugate (R ⊔ T) x ⊔ rightConjugate V' x := Subgroup.map_sup _ _ _
        _ ≤ P := sup_le hVx hV'x
    exact (rightConjugate_eq_self_iff P x).mp hPx
  have hS₂eq : S₂ = S := by
    by_contra hne
    obtain ⟨x, hx, hxS₂⟩ :=
      IsConcreteLE.exists_of_lt (lt_inf_normalizer hSp (lt_of_le_of_ne hS₂S hne))
    apply hxS₂
    rw [← hS₂]
    exact mem_inf.mpr ⟨(mem_inf.mp hx).1, hNS₂ (mem_inf.mp hx).2⟩
  subst hS₂eq
  exact ⟨inf_eq_left.mp hS₂, hS₂128, hS₂V, hswap, hES₂, hNS₂⟩

theorem exists_conj_not_mem (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P)
    (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G)
    (hPS : P ≤ S) {a : G} (ha : a ∈ V₀) (ha1 : a ≠ 1) :
    ∃ x : G, x⁻¹ * a * x ∈ (S : Subgroup G) ∧ x⁻¹ * a * x ∉ P := by
  obtain ⟨-, -, -, hswap, -, -⟩ := h.sylow_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS
  have hPS' : P < S := lt_of_le_of_ne hPS (h.P_not_sylow hP hPC hGold hGs hIIa hP64 hVP S).symm
  have hV₀V' : V₀ ≤ V' := hinf ▸ inf_le_right
  obtain ⟨eA⟩ := h.equiv
  obtain ⟨b₀, -, -, -, hb₀tr, -⟩ := exists_klein_three eA h.V₀_le_A h.card_V₀
  have hex : ∃ a₀ ∈ V₀, a₀ ≠ 1 ∧ ∃ x : G,
      x⁻¹ * a₀ * x ∈ (S : Subgroup G) ∧ x⁻¹ * a₀ * x ∉ P := by
    by_contra hcase
    push Not at hcase
    obtain ⟨s₀, hs₀, hs₀P⟩ := IsConcreteLE.exists_of_lt hPS'
    obtain ⟨hVs, hV's⟩ := hswap s₀ hs₀ hs₀P
    have hcl : ∀ c ∈ V₀, ∀ x : G, x⁻¹ * c * x ∈ (S : Subgroup G) → x⁻¹ * c * x ∈ V₀ := by
      intro c hc x hx
      by_cases hc1 : c = 1
      · rw [hc1]; simp
      have hxP := hcase c hc hc1 x hx
      by_cases hbV : x⁻¹ * c * x ∈ R ⊔ T
      · by_contra hb0
        exact h.conj_V₀_ne hc hc1 hbV hb0 x rfl
      · exfalso
        have hc2 : x⁻¹ * c * x * (x⁻¹ * c * x) = 1 := by
          have h1 := h.mul_self (h.V₀_le hc)
          calc x⁻¹ * c * x * (x⁻¹ * c * x) = x⁻¹ * (c * c) * x := by group
            _ = 1 := by rw [h1]; group
        have hV' := hV'inv _ hxP hc2 hbV
        have h1 : s₀ * (x⁻¹ * c * x) * s₀⁻¹ ∈ R ⊔ T := by
          rw [← hVs] at hV'
          exact (mem_rightConjugate_iff _ _ _).mp hV'
        have h2 : s₀ * (x⁻¹ * c * x) * s₀⁻¹ ∉ V₀ := by
          intro h0
          apply hbV
          rw [← hV's, mem_rightConjugate_iff]
          exact hV₀V' h0
        exact h.conj_V₀_ne hc hc1 h1 h2 (x * s₀⁻¹) (by group)
    have hab : IsMulCommutative V₀ :=
      ⟨⟨fun a b => Subtype.ext (h.comm (h.V₀_le a.2) (h.V₀_le b.2))⟩⟩
    have hV₀1 : V₀ ≠ ⊥ := fun he => by
      have := h.card_V₀
      rw [he, card_bot] at this
      omega
    have hall : ∀ v ∈ R ⊔ T, v ∈ V₀ := fun v hv =>
      mem_of_goldschmidt hGold hGs h.oddCore h.not_isPGroup_two S
        (h.V₀_le.trans (hVP.trans hPS)) hab hcl hV₀1 (hPS (hVP hv))
        (by rw [sq]; exact h.mul_self hv)
    have := Subgroup.card_le_of_le (show R ⊔ T ≤ V₀ from hall)
    rw [h.loc.card, h.card_V₀] at this
    omega
  obtain ⟨a₀, ha₀, ha₀1, x, hxS, hxP⟩ := hex
  obtain ⟨k, hk⟩ := hb₀tr a ha a₀ ha₀ ha1 ha₀1
  have e : (b₀ ^ k * x)⁻¹ * a * (b₀ ^ k * x) = x⁻¹ * a₀ * x := by rw [← hk]; group
  exact ⟨b₀ ^ k * x, e ▸ hxS, e ▸ hxP⟩

theorem center_le_V₀ (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P)
    (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G)
    (hPS : P ≤ S) {z : G} (hzS : z ∈ (S : Subgroup G))
    (hz : ∀ y ∈ (S : Subgroup G), z * y = y * z) : z ∈ V₀ := by
  obtain ⟨-, -, -, hswap, -, -⟩ := h.sylow_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS
  have hPS' : P < S := lt_of_le_of_ne hPS (h.P_not_sylow hP hPC hGold hGs hIIa hP64 hVP S).symm
  have hzC : z ∈ centralizer ((R ⊔ T : Subgroup G) : Set G) :=
    mem_centralizer_iff.mpr fun v hv => (hz v (hPS (hVP hv))).symm
  have hzP : z ∈ P := by
    by_contra hzP
    exact h.ne_of_inf_eq hinf (((rightConjugate_eq_self_iff _ z).mpr
      (centralizer_le_normalizer _ hzC)).symm.trans (hswap z hzS hzP).1)
  obtain ⟨s₀, hs₀, hs₀P⟩ := IsConcreteLE.exists_of_lt hPS'
  have hzV : z ∈ R ⊔ T := hPC ▸ mem_inf.mpr ⟨hzP, hzC⟩
  have hzV' : z ∈ V' := by
    rw [← (hswap s₀ hs₀ hs₀P).1, mem_rightConjugate_iff,
      show s₀ * z * s₀⁻¹ = z by rw [← hz s₀ hs₀]; group]
    exact hzV
  exact hinf ▸ mem_inf.mpr ⟨hzV, hzV'⟩

end IIa

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive


