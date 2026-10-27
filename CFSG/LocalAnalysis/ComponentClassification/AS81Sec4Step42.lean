module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step41
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowModel
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem exists_dihedral_rel {X : Type*} [Group X] [Finite X] (h8 : Nat.card X = 8)
    {K : Subgroup X} (h4 : Nat.card K = 4) (hsq : ∀ k ∈ K, k * k = 1) {τ x : X}
    (hτ : τ ∉ K) (hx : x ∈ K) (hnc : τ * x * τ⁻¹ ≠ x) :
    ∃ r s : X, r ^ 4 = 1 ∧ s * s = 1 ∧ s * r * (s * r) = 1 ∧
      (∀ i, 0 < i → i < 4 → r ^ i ≠ 1) ∧ ∀ i < 4, s * r ^ i ≠ 1 := by
  have hidx : K.index = 2 := by
    have := K.card_mul_index
    rw [h4, h8] at this
    omega
  have hmem : ∀ a b, a * b ∈ K ↔ (a ∈ K ↔ b ∈ K) := fun a b => mul_mem_iff_of_index_two hidx
  have hne1 : ∀ {a : X}, a ∉ K → a ≠ 1 := fun ha h => ha (h ▸ K.one_mem)
  have hinvK : ∀ k ∈ K, k⁻¹ = k := fun k hk => inv_eq_of_mul_eq_one_right (hsq k hk)
  have hcommK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := fun a ha b hb => by
    calc a * b = (a * b)⁻¹ := (hinvK _ (K.mul_mem ha hb)).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinvK a ha, hinvK b hb]
  have hτi : τ⁻¹ ∉ K := fun h => hτ (by simpa using K.inv_mem h)
  have hτx : τ * x ∉ K := fun h => hτ (((hmem τ x).mp h).mpr hx)
  set y := τ * x * τ⁻¹ with hydef
  have hy : y ∈ K := (hmem (τ * x) τ⁻¹).mpr (iff_of_false hτx hτi)
  have hτ2 : τ * τ ∈ K := (hmem τ τ).mpr Iff.rfl
  have hτy : τ * y * τ⁻¹ = x := by
    calc τ * y * τ⁻¹ = (τ * τ) * x * (τ * τ)⁻¹ := by rw [hydef]; group
      _ = x * (τ * τ) * (τ * τ)⁻¹ := by rw [hcommK _ hτ2 _ hx]
      _ = x := by group
  have hxy : x ≠ y := fun h => hnc h.symm
  have hx1 : x ≠ 1 := fun h => hxy (by rw [hydef, h]; group)
  have hy1 : y ≠ 1 := fun h => hx1 (by rw [← hτy, h]; group)
  have hyx : x * y ∈ K := K.mul_mem hx hy
  have hxx : x * x = 1 := hsq x hx
  have hxyxy : x * y * (x * y) = 1 := hsq _ hyx
  have hxy1 : x * y ≠ 1 := fun h =>
    hxy ((hinvK x hx).symm.trans (eq_inv_of_mul_eq_one_right h).symm)
  have hK4 : ∀ k ∈ K, k = 1 ∨ k = x ∨ k = y ∨ k = x * y := by
    intro k hk
    by_contra h
    push Not at h
    obtain ⟨hk1, hkx, hky, hkxy⟩ := h
    have hxyx : x * y ≠ x := fun h => hy1 (by simpa using h)
    have hxyy : x * y ≠ y := fun h => hx1 (by simpa using h)
    have hsub : ({1, x, y, x * y, k} : Set X) ⊆ K := by
      rintro z (rfl | rfl | rfl | rfl | rfl)
      · exact K.one_mem
      · exact hx
      · exact hy
      · exact hyx
      · exact hk
    have h5 : ({1, x, y, x * y, k} : Set X).ncard = 5 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
        Set.ncard_pair (Ne.symm hkxy)]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨Ne.symm hxyy, Ne.symm hky⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hxy, Ne.symm hxyx, Ne.symm hkx⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨Ne.symm hx1, Ne.symm hy1, Ne.symm hxy1, Ne.symm hk1⟩
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h5, ← Nat.card_coe_set_eq] at h1
    change 5 ≤ Nat.card K at h1
    omega
  have hττ : τ * (τ * τ) * τ⁻¹ = τ * τ := by group
  have hτ2' : τ * τ = 1 ∨ τ * τ = x * y := by
    rcases hK4 _ hτ2 with h | h | h | h
    · exact Or.inl h
    · exfalso
      apply hnc
      calc y = τ * x * τ⁻¹ := hydef
        _ = τ * (τ * τ) * τ⁻¹ := by rw [h]
        _ = τ * τ := hττ
        _ = x := h
    · exfalso
      apply hxy
      calc x = τ * y * τ⁻¹ := hτy.symm
        _ = τ * (τ * τ) * τ⁻¹ := by rw [h]
        _ = τ * τ := hττ
        _ = y := h
    · exact Or.inr h
  have hnot : ∀ {a b : X}, a ∈ K → b ∉ K → a * b ∉ K := fun ha hb h =>
    hb (((hmem _ _).mp h).mp ha)
  have hxτ : x * τ ∉ K := hnot hx hτ
  rcases hτ2' with h1 | h1
  ·
    have hr2 : (x * τ) ^ 2 = x * y := by
      calc (x * τ) ^ 2 = x * (τ * x * τ⁻¹) * (τ * τ) := by rw [sq]; group
        _ = x * y := by rw [h1, mul_one]
    refine ⟨x * τ, x, ?_, hxx, ?_, ?_, ?_⟩
    · rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hr2, sq, hxyxy]
    · calc x * (x * τ) * (x * (x * τ)) = (x * x) * τ * ((x * x) * τ) := by group
        _ = 1 := by rw [hxx, one_mul, h1]
    · intro i hi0 hi4
      interval_cases i
      · rw [pow_one]
        exact hne1 hxτ
      · rw [hr2]
        exact hxy1
      · rw [pow_succ, hr2]
        exact hne1 (hnot hyx hxτ)
    · intro i hi4
      interval_cases i
      · rw [pow_zero, mul_one]
        exact hx1
      · rw [pow_one, ← mul_assoc, hxx, one_mul]
        exact hne1 hτ
      · rw [hr2, ← mul_assoc, hxx, one_mul]
        exact hy1
      · rw [pow_succ, hr2, ← mul_assoc]
        exact hne1 (hnot (K.mul_mem hx hyx) hxτ)
  ·
    have hr2 : τ ^ 2 = x * y := by rw [sq, h1]
    refine ⟨τ, x, ?_, hxx, ?_, ?_, ?_⟩
    · rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hr2, sq, hxyxy]
    · calc x * τ * (x * τ) = x * (τ * x * τ⁻¹) * (τ * τ) := by group
        _ = x * y * (x * y) := by rw [h1]
        _ = 1 := hxyxy
    · intro i hi0 hi4
      interval_cases i
      · rw [pow_one]
        exact hne1 hτ
      · rw [hr2]
        exact hxy1
      · rw [pow_succ, hr2]
        exact hne1 (hnot hyx hτ)
    · intro i hi4
      interval_cases i
      · rw [pow_zero, mul_one]
        exact hx1
      · rw [pow_one]
        exact hne1 hxτ
      · rw [hr2, ← mul_assoc, hxx, one_mul]
        exact hy1
      · rw [pow_succ, hr2, ← mul_assoc]
        exact hne1 (hnot (K.mul_mem hx hyx) hτ)

omit [Finite G] in
theorem inf_normalizer_le_normalizer :
    normalizer (E : Set G) ⊓ normalizer (F : Set G) ≤
      normalizer ((E ⊔ F : Subgroup G) : Set G) := fun _ hn => mem_normalizer_sup hn.1 hn.2

namespace PlaneData

variable (hD : PlaneData G A R g E F)
include hD

theorem conj_eq_or_eq {n : G} (hn : n ∈ normalizer ((E ⊔ F : Subgroup G) : Set G)) :
    rightConjugate E n = E ∨ rightConjugate E n = F := by
  have hle : rightConjugate E n ≤ E ⊔ F := by
    have h := AschbacherTheorem3.rightConjugate_le_rightConjugate (le_sup_left : E ≤ E ⊔ F) n
    rwa [(rightConjugate_eq_self_iff _ n).mpr hn] at h
  exact hD.frame.eq_or_eq_of_isElemAbelian hD.le hD.type hle
    (AS76b.isElemAbelian_rightConjugate hD.frame.elemE n)
    (by rw [rightConjugate_card, hD.frame.cardE])

theorem mem_normalizer_F {n : G} (hn : n ∈ normalizer ((E ⊔ F : Subgroup G) : Set G))
    (hnE : n ∈ normalizer (E : Set G)) : n ∈ normalizer (F : Set G) := by
  have hle : rightConjugate F n ≤ E ⊔ F := by
    have h := AschbacherTheorem3.rightConjugate_le_rightConjugate (le_sup_right : F ≤ E ⊔ F) n
    rwa [(rightConjugate_eq_self_iff _ n).mpr hn] at h
  rcases hD.frame.eq_or_eq_of_isElemAbelian hD.le hD.type hle
      (AS76b.isElemAbelian_rightConjugate hD.frame.elemF n)
      (by rw [rightConjugate_card, hD.frame.cardF]) with h | h
  · exfalso
    apply hD.frame.ne
    have h' := congrArg (fun X => rightConjugate X n⁻¹) h
    simp only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h'
    rw [h', (rightConjugate_eq_self_iff E _).mpr (inv_mem hnE)]
  · exact (rightConjugate_eq_self_iff F n).mp h

theorem normalizer_inf_eq :
    normalizer ((E ⊔ F : Subgroup G) : Set G) ⊓ normalizer (E : Set G) =
      normalizer (E : Set G) ⊓ normalizer (F : Set G) :=
  le_antisymm (fun _ hn => ⟨hn.2, hD.mem_normalizer_F hn.1 hn.2⟩)
    (fun _ hn => ⟨inf_normalizer_le_normalizer hn, hn.1⟩)

theorem normalizer_le_normalizer_inf :
    normalizer ((E ⊔ F : Subgroup G) : Set G) ≤
      normalizer ((normalizer ((E ⊔ F : Subgroup G) : Set G) ⊓ normalizer (E : Set G) :
        Subgroup G) : Set G) := by
  have key : ∀ k ∈ normalizer ((E ⊔ F : Subgroup G) : Set G), ∀ m,
      m ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) ⊓ normalizer (E : Set G) →
      k * m * k⁻¹ ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) ⊓ normalizer (E : Set G) := by
    intro k hk m hm
    have hm1 : m ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) := (Subgroup.mem_inf.mp hm).1
    have hm2 : m ∈ normalizer (E : Set G) := (Subgroup.mem_inf.mp hm).2
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hk hm1) (inv_mem hk), ?_⟩
    have hmF := hD.mem_normalizer_F hm1 hm2
    rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, ← rightConjugate_mul]
    rcases hD.conj_eq_or_eq hk with h | h
    · rw [h, (rightConjugate_eq_self_iff E m).mpr hm2]
      exact (rightConjugate_eq_self_iff E _).mpr (inv_mem ((rightConjugate_eq_self_iff E k).mp h))
    · rw [h, (rightConjugate_eq_self_iff F m).mpr hmF, ← h, rightConjugate_mul, mul_inv_cancel,
        rightConjugate_one]
  intro k hk
  rw [mem_normalizer_iff]
  intro m
  refine ⟨key k hk m, fun h => ?_⟩
  have := key k⁻¹ (inv_mem hk) _ h
  rwa [show k⁻¹ * (k * m * k⁻¹) * k⁻¹⁻¹ = m by group] at this

end PlaneData

theorem mem_of_mem_sup_odd' {S O : Subgroup G} (hS : IsPGroup 2 S) (hO : Odd (Nat.card O))
    (hOS : O ≤ centralizer (S : Set G)) {x : G} (hx : x ∈ S ⊔ O) {k : ℕ} (hxk : x ^ 2 ^ k = 1) :
    x ∈ S := by
  have hN : S ≤ normalizer (O : Set G) := fun s hs =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun o ho =>
      (mem_centralizer_iff.mp (hOS ho) s hs).symm)
  have hx' : x ∈ ((S ⊔ O : Subgroup G) : Set G) := hx
  rw [coe_mul_of_left_le_normalizer_right S O hN] at hx'
  obtain ⟨s, hs, o, ho, rfl⟩ := hx'
  have hso : Commute s o := mem_centralizer_iff.mp (hOS ho) s hs
  have hSO : S ⊓ O = ⊥ := two_subgroup_of_odd_eq_bot (S ⊓ O) O (hS.to_le inf_le_left) hO
    inf_le_right
  have hok : o ^ 2 ^ k = 1 := by
    have h1 : s ^ 2 ^ k * o ^ 2 ^ k = 1 := by rw [← hso.mul_pow]; exact hxk
    have h2 : o ^ 2 ^ k = (s ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : o ^ 2 ^ k ∈ S ⊓ O := ⟨h2 ▸ S.inv_mem (S.pow_mem hs _), O.pow_mem ho _⟩
    rwa [hSO, mem_bot] at h3
  have ho1 : o = 1 := by
    have hdvd : orderOf (⟨o, ho⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
    rw [← Subgroup.orderOf_coe] at hdvd
    have h2 : orderOf o ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hok
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    · exfalso
      rw [hj] at hdvd
      exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr
        ((dvd_pow_self 2 (Nat.succ_ne_zero j)).trans hdvd))
  rw [ho1]
  simpa using hs

namespace PlaneData

variable (hD : PlaneData G A R g E F)
include hD

theorem isSylowOf_centralizer : IsSylowOf 2 E (centralizer (E : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEC : E ≤ centralizer (E : Set G) := fun e he =>
    mem_centralizer_iff.mpr fun x hx => hD.commE x hx e he
  have hE2 : IsPGroup 2 E := hD.isPGroup_sup.to_le le_sup_left
  have hOE : AS76b.oddCoreIn (centralizer (A : Set G)) ≤ centralizer (E : Set G) :=
    hD.centralizer_eq ▸ le_sup_right
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 (centralizer (E : Set G))
  have hPE : P ≤ E := by
    intro x hx
    obtain ⟨k, hk⟩ := (hP.isPGroup ⟨x, hx⟩)
    have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hxC := hP.le hx
    rw [hD.centralizer_eq] at hxC
    exact mem_of_mem_sup_odd' hE2 (AS76b.odd_card_oddCoreIn _) hOE hxC hk'
  exact (hP.eq_of_le hPE hEC hE2) ▸ hP

theorem factorization_card_centralizer :
    (Nat.card (centralizer (E : Set G))).factorization 2 = 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hD.isSylowOf_centralizer.card_eq
  rw [hD.frame.cardE, show (64 : ℕ) = 2 ^ 6 by norm_num] at h
  exact (Nat.pow_right_injective le_rfl h).symm

theorem card_image_inf (hD' : PlaneData G A R g F E) :
    Nat.card (((normalizer (E : Set G) ⊓ normalizer (F : Set G)).subgroupOf
      (normalizer (E : Set G))).map (pointsAction R E)) = 48 := by
  classical
  obtain ⟨f₁, f₂, κ, hf₁, hf₂, hκ, -, hF4, hFfour⟩ := hD'.exists_four hD
  set ρ := pointsAction R E with hρ
  set p₀ : ↥(pointsIn R E) := ⟨R, hD.R_mem⟩
  set p₁ : ↥(pointsIn R E) := ⟨rightConjugate R g, hD.Rg_mem⟩
  have hp01 : p₀ ≠ p₁ := fun h => hD.Rg_ne (congrArg Subtype.val h).symm
  have h48 := (normalizer_four_of_six hD.six hp01 hF4.ha hF4.hb hF4.hc).1
  rw [← h48]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
  constructor
  · rintro ⟨⟨n, hnE⟩, hn, rfl⟩
    have hnF : n ∈ normalizer (F : Set G) := (Subgroup.mem_inf.mp hn).2
    have key : ∀ f (hf : f ∈ F), ρ ⟨n, hnE⟩ * ρ ⟨f, hD.F_le_normalizer hf⟩ * (ρ ⟨n, hnE⟩)⁻¹ =
        ρ ⟨n * f * n⁻¹, hD.F_le_normalizer ((mem_normalizer_iff.mp hnF f).mp hf)⟩ := by
      intro f hf
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    exact ⟨by rw [key f₁ hf₁]; exact hFfour _ ((mem_normalizer_iff.mp hnF f₁).mp hf₁),
      by rw [key f₂ hf₂]; exact hFfour _ ((mem_normalizer_iff.mp hnF f₂).mp hf₂)⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨m, rfl⟩ := hD'.surjective_pointsAction hD σ
    exact ⟨m, Subgroup.mem_inf.mpr ⟨m.2, hD.mem_normalizer_of_four hf₁ hf₂ hFfour m.2 h1 h2⟩, rfl⟩

theorem card_inf (hD' : PlaneData G A R g F E) :
    Nat.card (normalizer (E : Set G) ⊓ normalizer (F : Set G) : Subgroup G) =
      48 * Nat.card (ptsKer R E) := by
  have hHN : normalizer (E : Set G) ⊓ normalizer (F : Set G) ≤ normalizer (E : Set G) :=
    inf_le_left
  have hKH : ptsKer R E ≤ normalizer (E : Set G) ⊓ normalizer (F : Set G) := fun κ hκ =>
    Subgroup.mem_inf.mpr ⟨ptsKer_le_normalizer hκ, hD.ptsKer_le_normalizer_other hκ⟩
  have h := card_eq_card_inf_ker_mul_card_map (pointsAction R E)
    ((normalizer (E : Set G) ⊓ normalizer (F : Set G)).subgroupOf (normalizer (E : Set G)))
  rw [hD.card_image_inf hD'] at h
  have hK' : (ptsKer R E).subgroupOf (normalizer (E : Set G)) = (pointsAction R E).ker :=
    comap_map_eq_self_of_injective (normalizer (E : Set G)).subtype_injective _
  have hker : (normalizer (E : Set G) ⊓ normalizer (F : Set G)).subgroupOf
      (normalizer (E : Set G)) ⊓ (pointsAction R E).ker =
      (ptsKer R E).subgroupOf (normalizer (E : Set G)) := by
    rw [← hK']
    exact inf_eq_right.mpr fun x hx => hKH hx
  rw [hker, Nat.card_congr (subgroupOfEquivOfLe hHN).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe ptsKer_le_normalizer).toEquiv] at h
  rw [h, mul_comm]

theorem factorization_card_inf (hD' : PlaneData G A R g F E) :
    (Nat.card (normalizer (E : Set G) ⊓ normalizer (F : Set G) : Subgroup G)).factorization 2 =
      10 := by
  classical
  have : Fintype ↥(pointsIn R E) := Fintype.ofFinite _
  obtain ⟨-, -, -, -, -, hK3, -, -⟩ := hD.exists_even
  have hrel := Subgroup.relIndex_mul_card (H := centralizer (E : Set G)) (K := ptsKer R E)
  rw [inf_eq_left.mpr centralizer_le_ptsKer, hK3] at hrel
  have hC := hD.factorization_card_centralizer
  have hpos : Nat.card (centralizer (E : Set G)) ≠ 0 := Nat.card_pos.ne'
  rw [hD.card_inf hD', ← hrel, ← mul_assoc, show 48 * 3 = 2 ^ 4 * 9 by norm_num,
    Nat.factorization_mul (by norm_num) hpos, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.coe_add, Pi.add_apply, hC]
  rw [Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 9)]

theorem card_sup : Nat.card (E ⊔ F : Subgroup G) = 2 ^ 8 := by
  have hFE : F ≤ normalizer (E : Set G) := hD.F_le_normalizer
  have h := card_sup_mul_card_inf hFE
  rw [card_inf_of_frame hD.frame, hD.frame.cardE, hD.frame.cardF] at h
  omega

theorem isSylowOf_inf {S₁ : Subgroup G}
    (hS₁ : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) :
    IsSylowOf 2 (S₁ ⊓ normalizer (E : Set G))
      (normalizer (E : Set G) ⊓ normalizer (F : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hS₁.inf_of_le_normalizer inf_le_left hD.normalizer_le_normalizer_inf
  rw [hD.normalizer_inf_eq] at h
  have e : S₁ ⊓ (normalizer (E : Set G) ⊓ normalizer (F : Set G)) =
      S₁ ⊓ normalizer (E : Set G) := by
    refine le_antisymm (inf_le_inf_left _ inf_le_left) fun x hx => ⟨hx.1, hx.2,
      hD.mem_normalizer_F (hS₁.le hx.1) hx.2⟩
  rwa [e] at h

theorem card_inf_sylow (hD' : PlaneData G A R g F E) {S₁ : Subgroup G}
    (hS₁ : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) :
    Nat.card (S₁ ⊓ normalizer (E : Set G) : Subgroup G) = 2 ^ 10 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [(hD.isSylowOf_inf hS₁).card_eq, hD.factorization_card_inf hD']

theorem mem_of_mem_ptsKer {κ : G} (hκ : κ ∈ ptsKer R E) {k : ℕ} (hk : κ ^ 2 ^ k = 1) : κ ∈ E := by
  classical
  have : Fintype ↥(pointsIn R E) := Fintype.ofFinite _
  obtain ⟨L, -, hLN, hperf, -, hK3, -, -⟩ := hD.exists_even
  obtain ⟨hpow, -⟩ := centralizes_of_relIndex_three centralizer_le_ptsKer
    ptsKer_le_normalizer (fun n hn c hc => conj_mem_centralizer hn hc)
    (fun n hn k hk => conj_mem_ptsKer hn hk) hK3 hLN hperf
  have h3 := hpow κ hκ
  have hC : κ ∈ centralizer (E : Set G) := by
    have hr : 2 ^ k % 3 ≠ 0 := fun h => by
      have : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this) (by norm_num)
    have hmod : κ ^ (2 ^ k % 3) ∈ centralizer (E : Set G) := by
      have e : κ ^ 2 ^ k = (κ ^ 3) ^ (2 ^ k / 3) * κ ^ (2 ^ k % 3) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
      have e2 : κ ^ (2 ^ k % 3) = ((κ ^ 3) ^ (2 ^ k / 3))⁻¹ := by
        rw [hk] at e
        exact eq_inv_of_mul_eq_one_right e.symm
      rw [e2]
      exact inv_mem (pow_mem h3 _)
    have hlt := Nat.mod_lt (2 ^ k) (by norm_num : 0 < 3)
    interval_cases h : 2 ^ k % 3
    · exact absurd rfl hr
    · simpa using hmod
    · have e : κ = κ ^ 3 * (κ ^ 2)⁻¹ := by group
      rw [e]
      exact mul_mem h3 (inv_mem hmod)
  rw [hD.centralizer_eq] at hC
  have hE2 : IsPGroup 2 E := hD.isPGroup_sup.to_le le_sup_left
  have hOE : AS76b.oddCoreIn (centralizer (A : Set G)) ≤ centralizer (E : Set G) :=
    hD.centralizer_eq ▸ le_sup_right
  exact mem_of_mem_sup_odd' hE2 (AS76b.odd_card_oddCoreIn _) hOE hC hk

theorem sup_le_sylow {S₁ : Subgroup G}
    (hS₁ : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) : E ⊔ F ≤ S₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := hS₁
  have hP : IsPGroup 2 ((E ⊔ F).subgroupOf (normalizer ((E ⊔ F : Subgroup G) : Set G))) :=
    hD.frame.sylow.isPGroup.of_equiv (subgroupOfEquivOfLe le_normalizer).symm
  have : ((E ⊔ F).subgroupOf (normalizer ((E ⊔ F : Subgroup G) : Set G))).Normal :=
    normal_in_normalizer
  have hle := hP.le_sylow_of_normal T
  intro x hx
  rw [← hT]
  exact ⟨⟨x, le_normalizer hx⟩, hle (show (⟨x, le_normalizer hx⟩ : ↥(normalizer
    ((E ⊔ F : Subgroup G) : Set G))) ∈ (E ⊔ F).subgroupOf _ from hx), rfl⟩

theorem sq_mem_of_mem_inf (hD' : PlaneData G A R g F E) {S₁ : Subgroup G}
    (hS₁ : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G)))
    {x : G} (hx : x ∈ S₁ ⊓ normalizer (E : Set G)) : x * x ∈ E ⊔ F := by
  classical
  obtain ⟨f₁, f₂, κ, hf₁, hf₂, hκ, -, hF4, hFfour⟩ := hD'.exists_four hD
  set ρ := pointsAction R E with hρ
  set p₀ : ↥(pointsIn R E) := ⟨R, hD.R_mem⟩
  set p₁ : ↥(pointsIn R E) := ⟨rightConjugate R g, hD.Rg_mem⟩
  have hp01 : p₀ ≠ p₁ := fun h => hD.Rg_ne (congrArg Subtype.val h).symm
  have hN := (normalizer_four_of_six hD.six hp01 hF4.ha hF4.hb hF4.hc).2
  have hxE : x ∈ normalizer (E : Set G) := hx.2
  have hxF : x ∈ normalizer (F : Set G) := hD.mem_normalizer_F (hS₁.le hx.1) hx.2
  have key : ∀ f (hf : f ∈ F), ρ ⟨x, hxE⟩ * ρ ⟨f, hD.F_le_normalizer hf⟩ * (ρ ⟨x, hxE⟩)⁻¹ =
      ρ ⟨x * f * x⁻¹, hD.F_le_normalizer ((mem_normalizer_iff.mp hxF f).mp hf)⟩ := by
    intro f hf
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have h₁ := hFfour _ ((mem_normalizer_iff.mp hxF f₁).mp hf₁)
  have h₂ := hFfour _ ((mem_normalizer_iff.mp hxF f₂).mp hf₂)
  rw [← key f₁ hf₁] at h₁
  rw [← key f₂ hf₂] at h₂
  have hcard := hD.card_inf_sylow hD' hS₁
  have hpow : ∀ y (hy : y ∈ S₁ ⊓ normalizer (E : Set G)), y ^ 2 ^ 10 = 1 := by
    intro y hy
    have h := pow_card_eq_one' (G := ↥(S₁ ⊓ normalizer (E : Set G))) (x := ⟨y, hy⟩)
    rw [hcard] at h
    exact congrArg Subtype.val h
  have h16 : ρ ⟨x, hxE⟩ ^ 16 = 1 := by
    have hd1 : orderOf (ρ ⟨x, hxE⟩) ∣ 2 ^ 10 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← map_pow]
      convert map_one ρ
      exact Subtype.ext (hpow x hx)
    have hd2 : orderOf (ρ ⟨x, hxE⟩) ∣ 720 := by
      have h := orderOf_dvd_natCard (ρ ⟨x, hxE⟩)
      rwa [Nat.card_perm, hD.six] at h
    have h16 : orderOf (ρ ⟨x, hxE⟩) ∣ 16 := by
      have h := Nat.dvd_gcd hd1 hd2
      norm_num at h
      exact h
    exact orderOf_dvd_iff_pow_eq_one.mp h16
  have hsq := hN _ h₁ h₂ h16
  rw [← map_mul] at hsq
  obtain ⟨u, hu, hρu⟩ : ∃ u, ∃ hu : u ∈ F,
      ρ ⟨u, hD.F_le_normalizer hu⟩ = ρ (⟨x, hxE⟩ * ⟨x, hxE⟩) := by
    rcases hsq with h | h | h | h
    · exact ⟨1, F.one_mem, by rw [h]; exact map_one ρ⟩
    · exact ⟨f₁, hf₁, h.symm⟩
    · exact ⟨f₂, hf₂, h.symm⟩
    · refine ⟨f₁ * f₂, F.mul_mem hf₁ hf₂, ?_⟩
      rw [h, ← map_mul]
      rfl
  have hSS := hD.sup_le_sylow hS₁
  have huS : u ∈ S₁ ⊓ normalizer (E : Set G) := ⟨hSS (mem_sup_right hu), hD.F_le_normalizer hu⟩
  have hκ' : u⁻¹ * (x * x) ∈ ptsKer R E := by
    refine mem_ptsKer.mpr ⟨mul_mem (inv_mem (hD.F_le_normalizer hu)) (mul_mem hxE hxE), ?_⟩
    have e : (⟨u⁻¹ * (x * x), mul_mem (inv_mem (hD.F_le_normalizer hu)) (mul_mem hxE hxE)⟩ :
        ↥(normalizer (E : Set G))) = (⟨u, hD.F_le_normalizer hu⟩)⁻¹ * (⟨x, hxE⟩ * ⟨x, hxE⟩) :=
      rfl
    rw [e, map_mul, map_inv, hρu, inv_mul_cancel]
  have hκS : u⁻¹ * (x * x) ∈ S₁ ⊓ normalizer (E : Set G) :=
    mul_mem (inv_mem huS) (mul_mem hx hx)
  have hE := hD.mem_of_mem_ptsKer hκ' (hpow _ hκS)
  rw [show x * x = u * (u⁻¹ * (x * x)) by group]
  exact mul_mem (mem_sup_right hu) (mem_sup_left hE)

end PlaneData

omit [Finite G] in
theorem sign_pointsAction_conj [Fintype ↥(pointsIn R E)] [DecidableEq ↥(pointsIn R E)]
    [Fintype ↥(pointsIn R F)] [DecidableEq ↥(pointsIn R F)] {τ : G}
    (hτ : rightConjugate F τ⁻¹ = E) {x : G} (hxF : x ∈ normalizer (F : Set G))
    (hx' : τ * x * τ⁻¹ ∈ normalizer (E : Set G)) :
    Equiv.Perm.sign (pointsAction R E ⟨τ * x * τ⁻¹, hx'⟩) =
      Equiv.Perm.sign (pointsAction R F ⟨x, hxF⟩) := by
  have hτ' : rightConjugate E τ = F := by
    rw [← hτ, rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
  have hmapF : ∀ Q ∈ pointsIn R F, rightConjugate Q τ⁻¹ ∈ pointsIn R E := by
    rintro Q ⟨hQF, y, rfl⟩
    refine ⟨?_, y * τ⁻¹, rightConjugate_mul R y τ⁻¹⟩
    have h := AschbacherTheorem3.rightConjugate_le_rightConjugate hQF τ⁻¹
    rwa [hτ] at h
  have hmapE : ∀ Q ∈ pointsIn R E, rightConjugate Q τ ∈ pointsIn R F := by
    rintro Q ⟨hQE, y, rfl⟩
    refine ⟨?_, y * τ, rightConjugate_mul R y τ⟩
    have h := AschbacherTheorem3.rightConjugate_le_rightConjugate hQE τ
    rwa [hτ'] at h
  let e : ↥(pointsIn R F) ≃ ↥(pointsIn R E) :=
    { toFun := fun Q => ⟨rightConjugate (Q : Subgroup G) τ⁻¹, hmapF Q Q.2⟩
      invFun := fun Q => ⟨rightConjugate (Q : Subgroup G) τ, hmapE Q Q.2⟩
      left_inv := fun Q => Subtype.ext (by
        simp only [rightConjugate_mul, inv_mul_cancel, rightConjugate_one])
      right_inv := fun Q => Subtype.ext (by
        simp only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]) }
  have heq : pointsAction R E ⟨τ * x * τ⁻¹, hx'⟩ = e.permCongr (pointsAction R F ⟨x, hxF⟩) := by
    refine Equiv.ext fun Q => Subtype.ext ?_
    rw [Equiv.permCongr_apply, coe_pointsAction_apply]
    change _ = rightConjugate (rightConjugate (rightConjugate (Q : Subgroup G) τ) x⁻¹) τ⁻¹
    rw [rightConjugate_mul, rightConjugate_mul]
    congr 1
    group
  rw [heq, Equiv.Perm.sign_permCongr]

namespace PlaneData

variable (hD : PlaneData G A R g E F)
include hD

theorem normalizer_R_le : normalizer (R : Set G) ≤ normalizer (A : Set G) := by
  have hstd := hD.frame.base.hyp.standard
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hR1 : R ≠ ⊥ := by
    intro h
    have := hD.frame.cardR
    rw [h, Subgroup.card_bot] at this
    omega
  rw [← AS76b.normalizer_centralizer_eq hstd]
  exact normalizer_two_subgroup_le _ _ hKte hD.frame.sylowR.isPGroup hD.frame.sylowR.le hR1

theorem eq_or_eq_of_mem_pointsIn_inf {Q : Subgroup G} (hQ : Q ∈ pointsIn R (E ⊓ F)) :
    Q = R ∨ Q = rightConjugate R g := by
  by_contra h
  push Not at h
  have hRV : R ∈ pointsIn R (E ⊓ F) := self_mem_pointsIn (le_inf hD.frame.R_le_E hD.frame.R_le_F)
  have hPV : rightConjugate R g ∈ pointsIn R (E ⊓ F) := ⟨hD.Rg_le, g, rfl⟩
  have hsub : ({R, rightConjugate R g, Q} : Set (Subgroup G)) ⊆ pointsIn R (E ⊓ F) := by
    rintro X (rfl | rfl | rfl)
    · exact hRV
    · exact hPV
    · exact hQ
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem (by simp [hD.Rg_ne.symm, Ne.symm h.1]),
    Set.ncard_pair (Ne.symm h.2), ← Nat.card_coe_set_eq, hD.two] at h1
  omega

theorem exists_mem_normalizer_A (hD' : PlaneData G A R g F E) {τ : G}
    (hτN : τ ∈ normalizer ((E ⊔ F : Subgroup G) : Set G)) (hτE : rightConjugate E τ = F) :
    ∃ n ∈ normalizer (A : Set G), rightConjugate E n = F := by
  classical
  have hτF : rightConjugate F τ = E := by
    have hτN' : τ ∈ normalizer ((F ⊔ E : Subgroup G) : Set G) := by rwa [sup_comm]
    rcases hD'.conj_eq_or_eq hτN' with h | h
    · exfalso
      apply hD.frame.ne
      have h' := congrArg (fun X => rightConjugate X τ⁻¹) (hτE.trans h.symm)
      simp only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h'
      exact h'
    · exact h
  have hVτ : rightConjugate (E ⊓ F) τ = E ⊓ F := by
    rw [AschbacherTheorem3.rightConjugate_inf, hτE, hτF, inf_comm]
  have hRτ : rightConjugate R τ ∈ pointsIn R (E ⊓ F) := by
    refine ⟨?_, τ, rfl⟩
    have h := AschbacherTheorem3.rightConjugate_le_rightConjugate
      (le_inf hD.frame.R_le_E hD.frame.R_le_F) τ
    rwa [hVτ] at h
  rcases hD.eq_or_eq_of_mem_pointsIn_inf hRτ with h | h
  · exact ⟨τ, hD.normalizer_R_le ((rightConjugate_eq_self_iff R τ).mp h), hτE⟩
  · have : Fintype ↥(pointsIn R E) := Fintype.ofFinite _
    obtain ⟨t, htE, htF, -, -, htRg, -⟩ := hD.exists_swap hD'
    refine ⟨τ * t⁻¹, hD.normalizer_R_le ?_, ?_⟩
    · rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, h, htRg]
    · rw [← rightConjugate_mul, hτE, (rightConjugate_eq_self_iff F _).mpr (inv_mem htF)]

theorem exists_mem_inf_sign [Fintype ↥(pointsIn R E)] [DecidableEq ↥(pointsIn R E)]
    [Fintype ↥(pointsIn R F)] [DecidableEq ↥(pointsIn R F)] (hD' : PlaneData G A R g F E)
    {S₁ : Subgroup G} (hS₁ : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) :
    ∃ x, ∃ (hx : x ∈ S₁ ⊓ normalizer (E : Set G)) (hxF : x ∈ normalizer (F : Set G)),
      Equiv.Perm.sign (pointsAction R E ⟨x, hx.2⟩) = 1 ∧
        Equiv.Perm.sign (pointsAction R F ⟨x, hxF⟩) = -1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htE, htF, hte, hto⟩ := hD.exists_odd hD'
  set H := normalizer (E : Set G) ⊓ normalizer (F : Set G) with hH
  let ψ₁ : ↥H →* ℤˣ := Equiv.Perm.sign.comp ((pointsAction R E).comp (inclusion inf_le_left))
  let ψ₂ : ↥H →* ℤˣ := Equiv.Perm.sign.comp ((pointsAction R F).comp (inclusion inf_le_right))
  let ψ : ↥H →* ℤˣ × ℤˣ := ψ₁.prod ψ₂
  have hS₂ := hD.isSylowOf_inf hS₁
  set S₂' := (S₁ ⊓ normalizer (E : Set G)).subgroupOf H with hS₂'
  have hodd : ¬ 2 ∣ S₂'.index := (isSylowOf_iff.mp hS₂).2.2
  set M := S₂'.map ψ.rangeRestrict
  have hdvd1 : M.index ∣ S₂'.index := index_map_dvd _ ψ.rangeRestrict_surjective
  have hdvd2 : M.index ∣ 4 := by
    refine M.index_dvd_card.trans ?_
    have h := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] at h
  have hM1 : M.index = 1 := by
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show M.index ∣ 2 ^ 2 from hdvd2)
    rcases j with _ | j
    · simpa using hj'
    · exfalso
      exact hodd ((dvd_pow_self 2 (Nat.succ_ne_zero j)).trans (hj' ▸ hdvd1))
  have hMtop : M = ⊤ := Subgroup.index_eq_one.mp hM1
  have htH : t ∈ H := Subgroup.mem_inf.mpr ⟨htE, htF⟩
  have hmem : ψ.rangeRestrict ⟨t, htH⟩ ∈ M := hMtop ▸ mem_top _
  obtain ⟨⟨x, hxH⟩, hx, hxt⟩ := hmem
  have hxt' : ψ ⟨x, hxH⟩ = ψ ⟨t, htH⟩ := congrArg Subtype.val hxt
  have hx₁ : ψ₁ ⟨x, hxH⟩ = ψ₁ ⟨t, htH⟩ := congrArg Prod.fst hxt'
  have hx₂ : ψ₂ ⟨x, hxH⟩ = ψ₂ ⟨t, htH⟩ := congrArg Prod.snd hxt'
  refine ⟨x, hx, (Subgroup.mem_inf.mp hxH).2, ?_, ?_⟩
  · exact hx₁.trans hte
  · exact hx₂.trans hto

theorem step42_quot (hD' : PlaneData G A R g F E) {S₁ : Subgroup G}
    (hS₁ : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) :
    ((E ⊔ F).relIndex S₁ = 4 ∧ (∀ s ∈ S₁, s * s ∈ E ⊔ F) ∧ S₁ ≤ normalizer (E : Set G)) ∨
      ((∃ φ : ↥S₁ →* DihedralGroup 4, Function.Surjective φ ∧
          φ.ker = (E ⊔ F).subgroupOf S₁) ∧
        ∃ n ∈ normalizer (A : Set G), rightConjugate E n = F) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSS := hD.sup_le_sylow hS₁
  have hcard₂ := hD.card_inf_sylow hD' hS₁
  have hcardS := hD.card_sup
  have hSN : E ⊔ F ≤ normalizer (E : Set G) := sup_le le_normalizer hD.F_le_normalizer
  by_cases hE : S₁ ≤ normalizer (E : Set G)
  · left
    have heq : S₁ ⊓ normalizer (E : Set G) = S₁ := inf_eq_left.mpr hE
    refine ⟨?_, fun s hs => hD.sq_mem_of_mem_inf hD' hS₁ ⟨hs, hE hs⟩, hE⟩
    have hS₁card : Nat.card S₁ = 2 ^ 10 := by rw [← heq]; exact hcard₂
    have h := Subgroup.relIndex_mul_card (H := E ⊔ F) (K := S₁)
    rw [inf_eq_left.mpr hSS, hcardS, hS₁card] at h
    omega
  · right
    obtain ⟨τ, hτ, hτE⟩ := Set.not_subset.mp hE
    have hτN := hS₁.le hτ
    have hτF : rightConjugate E τ = F := by
      rcases hD.conj_eq_or_eq hτN with h | h
      · exact absurd ((rightConjugate_eq_self_iff E τ).mp h) hτE
      · exact h
    have hτF' : rightConjugate F τ = E := by
      have hτN' : τ ∈ normalizer ((F ⊔ E : Subgroup G) : Set G) := by rwa [sup_comm]
      rcases hD'.conj_eq_or_eq hτN' with h | h
      · exfalso
        apply hD.frame.ne
        have h' := congrArg (fun X => rightConjugate X τ⁻¹) (hτF.trans h.symm)
        simp only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h'
        exact h'
      · exact h
    refine ⟨?_, hD.exists_mem_normalizer_A hD' hτN hτF⟩
    set S₂ := S₁ ⊓ normalizer (E : Set G) with hS₂def
    have hiff : ∀ y : ↥S₁, y ∈ S₂.subgroupOf S₁ ↔ (y : G) ∈ normalizer (E : Set G) :=
      fun y => ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩
    have hidx : (S₂.subgroupOf S₁).index = 2 := by
      refine Subgroup.index_eq_two_iff.mpr ⟨⟨τ, hτ⟩, fun b => ?_⟩
      have hb := hS₁.le b.2
      rw [hiff, hiff]
      change (((b : G) * τ ∈ normalizer (E : Set G)) ∧ (b : G) ∉ normalizer (E : Set G)) ∨
        ((b : G) ∈ normalizer (E : Set G) ∧ (b : G) * τ ∉ normalizer (E : Set G))
      rw [← rightConjugate_eq_self_iff, ← rightConjugate_eq_self_iff, ← rightConjugate_mul]
      rcases hD.conj_eq_or_eq hb with h | h
      · rw [h, hτF]
        exact Or.inr ⟨rfl, hD.frame.ne.symm⟩
      · rw [h, hτF']
        exact Or.inl ⟨rfl, hD.frame.ne.symm⟩
    have hS₁card : Nat.card S₁ = 2 ^ 11 := by
      have h := (S₂.subgroupOf S₁).card_mul_index
      rw [hidx, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv, hcard₂] at h
      omega
    have : Fintype ↥(pointsIn R E) := Fintype.ofFinite _
    have : Fintype ↥(pointsIn R F) := Fintype.ofFinite _
    obtain ⟨x, hx, hxF, hxe, hxo⟩ := hD.exists_mem_inf_sign hD' hS₁
    have hSalt : ∀ y (hy : y ∈ E ⊔ F),
        Equiv.Perm.sign (pointsAction R E ⟨y, hSN hy⟩) = 1 := by
      intro y hy
      have hSA : E ⊔ F ≤ A ⊓ normalizer (E : Set G) := le_inf (sup_le hD.E_le_A hD.F_le_A) hSN
      exact Equiv.Perm.mem_alternatingGroup.mp
        (pointsAction_mem_alternatingGroup (M := A ⊓ normalizer (E : Set G)) inf_le_right
          hD.radical (hSA hy))
    have hτF'' : rightConjugate F τ⁻¹ = E := by
      rw [← hτF, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
    have hcx : τ * x * τ⁻¹ ∈ normalizer (E : Set G) := by
      rw [← rightConjugate_eq_self_iff]
      rw [show τ * x * τ⁻¹ = (τ⁻¹)⁻¹ * x * τ⁻¹ by rw [inv_inv], ← rightConjugate_mul,
        ← rightConjugate_mul, (show rightConjugate E (τ⁻¹)⁻¹ = F by rw [inv_inv]; exact hτF),
        (rightConjugate_eq_self_iff F x).mpr hxF, hτF'']
    have hnc : τ * x * τ⁻¹ * x⁻¹ ∉ E ⊔ F := by
      intro hy
      have h1 := hSalt _ hy
      have e : (⟨τ * x * τ⁻¹ * x⁻¹, hSN hy⟩ : ↥(normalizer (E : Set G))) =
          ⟨τ * x * τ⁻¹, hcx⟩ * (⟨x, hx.2⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, map_inv, hxe, inv_one, mul_one,
        sign_pointsAction_conj hτF'' hxF hcx, hxo] at h1
      exact absurd h1 (by decide)
    set N := (E ⊔ F).subgroupOf S₁ with hNdef
    have hNn : N.Normal := ⟨fun a ha b => by
      rw [hNdef, mem_subgroupOf] at ha ⊢
      exact (mem_normalizer_iff.mp (hS₁.le b.2) a).mp ha⟩
    set π := QuotientGroup.mk' N with hπ
    have hπ1 : ∀ y : ↥S₁, π y = 1 ↔ (y : G) ∈ E ⊔ F := fun y => by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hNdef, mem_subgroupOf]
    have hN8 : Nat.card (↥S₁ ⧸ N) = 8 := by
      rw [← Subgroup.index_eq_card]
      have h := Subgroup.relIndex_mul_card (H := E ⊔ F) (K := S₁)
      rw [inf_eq_left.mpr hSS, hcardS, hS₁card] at h
      change (E ⊔ F).relIndex S₁ = 8
      omega
    set Kb := (S₂.subgroupOf S₁).map π with hKb
    have hK4 : Nat.card Kb = 4 := by
      show Nat.card ((S₂.subgroupOf S₁).map π) = 4
      have h := card_eq_card_inf_ker_mul_card_map π (S₂.subgroupOf S₁)
      have hle : N ≤ S₂.subgroupOf S₁ := fun y hy => (hiff y).mpr (hSN hy)
      have hS₂' : Nat.card (S₂.subgroupOf S₁) = 2 ^ 10 :=
        (Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv).trans hcard₂
      have hN' : Nat.card N = 2 ^ 8 :=
        (Nat.card_congr (subgroupOfEquivOfLe hSS).toEquiv).trans hcardS
      rw [QuotientGroup.ker_mk', inf_eq_right.mpr hle, hS₂', hN'] at h
      omega
    have hsqK : ∀ k ∈ Kb, k * k = 1 := by
      rintro _ ⟨k, hk, rfl⟩
      rw [← map_mul, hπ1]
      exact hD.sq_mem_of_mem_inf hD' hS₁ hk
    have hτK : π ⟨τ, hτ⟩ ∉ Kb := by
      rintro ⟨k, hk, hkτ⟩
      apply hτE
      have h1 : π (k⁻¹ * ⟨τ, hτ⟩) = 1 := by rw [map_mul, map_inv, hkτ, inv_mul_cancel]
      rw [hπ1] at h1
      have h2 : (k : G) * (k⁻¹ * ⟨τ, hτ⟩ : ↥S₁) ∈ normalizer (E : Set G) :=
        mul_mem hk.2 (hSN h1)
      simpa using h2
    have hxK : π ⟨x, hx.1⟩ ∈ Kb := ⟨⟨x, hx.1⟩, hx, rfl⟩
    have hncK : π ⟨τ, hτ⟩ * π ⟨x, hx.1⟩ * (π ⟨τ, hτ⟩)⁻¹ ≠ π ⟨x, hx.1⟩ := by
      intro h
      apply hnc
      have h1 : π (⟨τ, hτ⟩ * ⟨x, hx.1⟩ * (⟨τ, hτ⟩)⁻¹ * (⟨x, hx.1⟩)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h, mul_inv_cancel]
      rwa [hπ1] at h1
    obtain ⟨r', s', hr4, hs2, hsr, hrne, hsne⟩ :=
      exists_dihedral_rel hN8 hK4 hsqK hτK hxK hncK
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective N r'
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective N s'
    refine HeSylow.exists_dihedral_quotient hSS hS₁.le (by rw [hS₁card, hcardS]; norm_num)
      r.2 s.2 ?_ ?_ ?_ ?_ ?_
    · have h := (hπ1 (r ^ 4)).mp (by rw [map_pow]; exact hr4)
      simpa using h
    · have h := (hπ1 (s * s)).mp (by rw [map_mul]; exact hs2)
      simpa using h
    · have h := (hπ1 (s * r * (s * r))).mp (by rw [map_mul, map_mul]; exact hsr)
      simpa using h
    · intro i hi0 hi4 h
      apply hrne i hi0 hi4
      rw [← map_pow, hπ1]
      simpa using h
    · intro i hi4 h
      apply hsne i hi4
      rw [← map_pow, ← map_mul, hπ1]
      simpa using h

end PlaneData

theorem step42_quot_of {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hS : Sec4Setting G A R g E F) {S₁ : Subgroup G}
    (hS₁ : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) :
    ((E ⊔ F).relIndex S₁ = 4 ∧ (∀ s ∈ S₁, s * s ∈ E ⊔ F) ∧ S₁ ≤ normalizer (E : Set G)) ∨
      ((∃ φ : ↥S₁ →* DihedralGroup 4, Function.Surjective φ ∧
          φ.ker = (E ⊔ F).subgroupOf S₁) ∧
        ∃ n ∈ normalizer (A : Set G), rightConjugate E n = F) :=
  (planeData_of hE16 h11 hS.frame hS.even).step42_quot
    (planeData_of hE16 h11 hS.frame.swap hS.even) hS₁

end CFSG.ComponentClassification.AS81
