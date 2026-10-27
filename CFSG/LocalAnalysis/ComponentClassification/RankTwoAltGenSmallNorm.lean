module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenRootK
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixAut

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
  CFSG.Quasithin.SteinbergCB

section Lift

variable {n : ℕ}

theorem liftA_apply_castLE (hn : 6 ≤ n) (z : alternatingGroup (Fin n)) (y : Fin n) :
    (liftA hn z : Perm (Fin (n + 4))) (Fin.castLEEmb (by omega : n ≤ n + 4) (tau45 hn y)) =
      Fin.castLEEmb (by omega : n ≤ n + 4) (tau45 hn ((z : Perm (Fin n)) y)) := by
  rw [coe_liftA, viaEmbeddingHom_apply_image]
  congr 1
  simp only [Perm.mul_apply, Perm.coe_inv, symm_apply_apply]

theorem liftA_apply_of_not_mem (hn : 6 ≤ n) (z : alternatingGroup (Fin n)) {p : Fin (n + 4)}
    (hp : p ∉ Set.range (Fin.castLEEmb (by omega : n ≤ n + 4))) :
    (liftA hn z : Perm (Fin (n + 4))) p = p := by
  rw [coe_liftA]
  exact viaEmbeddingHom_apply_of_notMem _ _ hp

theorem liftA_fix_iff (hn : 6 ≤ n) (z : alternatingGroup (Fin n)) (y : Fin n) :
    (liftA hn z : Perm (Fin (n + 4))) (Fin.castLEEmb (by omega : n ≤ n + 4) (tau45 hn y)) =
      Fin.castLEEmb (by omega : n ≤ n + 4) (tau45 hn y) ↔ (z : Perm (Fin n)) y = y := by
  rw [liftA_apply_castLE, (Fin.castLEEmb _).injective.eq_iff, (tau45 hn).injective.eq_iff]

theorem support_liftA_eq_iff (hn : 6 ≤ n) (z₁ z₂ : alternatingGroup (Fin n)) :
    (liftA hn z₁ : Perm (Fin (n + 4))).support = (liftA hn z₂ : Perm (Fin (n + 4))).support ↔
      ∀ y : Fin n, (z₁ : Perm (Fin n)) y = y ↔ (z₂ : Perm (Fin n)) y = y := by
  constructor
  · intro h y
    have h1 : Fin.castLEEmb (by omega : n ≤ n + 4) (tau45 hn y) ∈
        (liftA hn z₁ : Perm (Fin (n + 4))).support ↔
        Fin.castLEEmb (by omega : n ≤ n + 4) (tau45 hn y) ∈
          (liftA hn z₂ : Perm (Fin (n + 4))).support := by rw [h]
    rw [mem_support, mem_support, not_iff_not, liftA_fix_iff, liftA_fix_iff] at h1
    exact h1
  · intro h
    ext p
    rw [mem_support, mem_support, not_iff_not]
    by_cases hp : p ∈ Set.range (Fin.castLEEmb (by omega : n ≤ n + 4))
    · obtain ⟨i, rfl⟩ := hp
      obtain ⟨y, rfl⟩ := (tau45 hn).surjective i
      rw [liftA_fix_iff, liftA_fix_iff]
      exact h y
    · rw [liftA_apply_of_not_mem hn z₁ hp, liftA_apply_of_not_mem hn z₂ hp]

theorem card_support_of_cycleType {α : Type*} [Fintype α] [DecidableEq α] {π : Perm α}
    (hπ : π.cycleType = {2, 2}) : π.support.card = 4 := by
  rw [← sum_cycleType, hπ]
  rfl

end Lift

namespace AltGenSetting

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}
  {Φ : alternatingGroup (Fin (n + 4)) →* G} (s : AltGenSetting A R T g n Φ)
include s

theorem mem_normalizer_of_conj_mem_centralizer {t a b : G} (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (ha : a⁻¹ * t * a ∈ centralizer (A : Set G)) (hb : b⁻¹ * t * b ∈ centralizer (A : Set G)) :
    b⁻¹ * a ∈ normalizer (A : Set G) := by
  have hc := s.sec3
  have hKt := RankTwoSporadic.tightlyEmbedded_centralizer_of_standard hc.hyp.standard
  by_contra hN
  have hN' : b⁻¹ * a ∉ normalizer (centralizer (A : Set G) : Set G) := by
    rwa [normalizer_centralizer_eq hc.hyp.standard]
  have hodd := hKt.2 _ hN'
  have hk : a⁻¹ * t * a ∈
      centralizer (A : Set G) ⊓ rightConjugate (centralizer (A : Set G)) (b⁻¹ * a) := by
    refine Subgroup.mem_inf.mpr ⟨ha, ?_⟩
    rw [mem_rightConjugate_iff]
    have h1 : b⁻¹ * a * (a⁻¹ * t * a) * (b⁻¹ * a)⁻¹ = b⁻¹ * t * b := by group
    rw [h1]
    exact hb
  have hk2 : (a⁻¹ * t * a) ^ 2 = 1 := by
    rw [sq]
    calc a⁻¹ * t * a * (a⁻¹ * t * a) = a⁻¹ * (t * t) * a := by group
      _ = 1 := by rw [ht2, mul_one, inv_mul_cancel]
  have hk1 : a⁻¹ * t * a ≠ 1 := fun h1 => ht1 (by
    calc t = a * (a⁻¹ * t * a) * a⁻¹ := by group
      _ = 1 := by rw [h1, mul_one, mul_inv_cancel])
  have hdvd : orderOf (a⁻¹ * t * a) ∣ 2 := orderOf_dvd_of_pow_eq_one hk2
  have hodd' : Odd (orderOf (a⁻¹ * t * a)) :=
    hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hk)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact hk1 (orderOf_eq_one_iff.mp h)
  · rw [h] at hodd'
    exact absurd hodd' (by decide)

theorem conj_mem_centralizer_of_mem_normalizer {m k : G} (hm : m ∈ normalizer (A : Set G))
    (hk : k ∈ centralizer (A : Set G)) : m * k * m⁻¹ ∈ centralizer (A : Set G) := by
  have hm' : m ∈ normalizer (centralizer (A : Set G) : Set G) := by
    rw [normalizer_centralizer_eq s.sec3.hyp.standard]
    exact hm
  exact (mem_normalizer_iff.mp hm' k).mp hk

theorem conj_mem_centralizer_of_fix {γ π : alternatingGroup (Fin (n + 4))}
    (h : ∀ i : Fin n, (π : Perm (Fin (n + 4))) ((γ : Perm (Fin (n + 4)))
      (Fin.castLEEmb (by omega : n ≤ n + 4) i)) =
        (γ : Perm (Fin (n + 4))) (Fin.castLEEmb (by omega : n ≤ n + 4) i)) :
    (Φ γ)⁻¹ * Φ π * Φ γ ∈ centralizer (A : Set G) := by
  obtain ⟨σ, hσdef⟩ : ∃ σ : alternatingGroup (Fin (n + 4)), σ = γ⁻¹ * π * γ := ⟨_, rfl⟩
  have hσ : ∀ i : Fin n, (σ : Perm (Fin (n + 4))) (Fin.castLEEmb (by omega : n ≤ n + 4) i) =
      Fin.castLEEmb (by omega : n ≤ n + 4) i := by
    intro i
    rw [hσdef, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply,
      Perm.mul_apply, h i, Perm.coe_inv, symm_apply_apply]
  have hrw : (Φ γ)⁻¹ * Φ π * Φ γ = Φ σ := by rw [hσdef, map_mul, map_mul, map_inv]
  rw [hrw, mem_centralizer_iff]
  intro a ha
  obtain ⟨z, rfl⟩ := s.exists_liftA_eq ha
  have hdisj : Perm.Disjoint (liftA s.six_le z : Perm (Fin (n + 4))) (σ : Perm (Fin (n + 4))) := by
    intro p
    by_cases hp : p ∈ Set.range (Fin.castLEEmb (by omega : n ≤ n + 4))
    · obtain ⟨i, rfl⟩ := hp
      exact Or.inr (hσ i)
    · exact Or.inl (liftA_apply_of_not_mem s.six_le z hp)
  have hc : liftA s.six_le z * σ = σ * liftA s.six_le z := Subtype.ext hdisj.commute.eq
  rw [← map_mul, ← map_mul, hc]

theorem support_eq_of_mem_centralizer {π : alternatingGroup (Fin (n + 4))}
    (hπ : Φ π ∈ centralizer (A : Set G)) (h4 : (π : Perm (Fin (n + 4))).support.card = 4) :
    (π : Perm (Fin (n + 4))).support = Finset.univ.map (Fin.natAddEmb n) := by
  have hsub : (π : Perm (Fin (n + 4))).support ⊆ Finset.univ.map (Fin.natAddEmb n) := by
    intro x hx
    rw [Finset.mem_map]
    by_cases hxn : (x : ℕ) < n
    · exfalso
      have h1 := s.fix_of_mem_centralizer hπ ⟨x, hxn⟩
      rw [mem_support] at hx
      apply hx
      have h2 : (Fin.castLEEmb (by omega : n ≤ n + 4) ⟨x, hxn⟩ : Fin (n + 4)) = x :=
        Fin.ext (by simp)
      rw [h2] at h1
      exact h1
    · refine ⟨⟨(x : ℕ) - n, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
      simp only [Fin.natAddEmb_apply, Fin.val_natAdd]
      omega
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin, h4]

theorem support_eq_of_conj_mem_centralizer {π₁ π₂ : alternatingGroup (Fin (n + 4))} {x : G}
    (h1 : (π₁ : Perm (Fin (n + 4))).cycleType = {2, 2})
    (h2 : (π₂ : Perm (Fin (n + 4))).cycleType = {2, 2})
    (hx1 : x⁻¹ * Φ π₁ * x ∈ centralizer (A : Set G))
    (hx2 : x⁻¹ * Φ π₂ * x ∈ centralizer (A : Set G)) :
    (π₁ : Perm (Fin (n + 4))).support = (π₂ : Perm (Fin (n + 4))).support := by
  obtain ⟨γ, hγ⟩ := exists_conj_eq_of_cycleType_eq (σ := rootLast n) (τ := π₁)
    (by rw [cycleType_rootLast, h1]) rootLast_mul_rootLast rootLast_ne_one
  have hr : (Φ γ)⁻¹ * Φ π₁ * Φ γ = Φ (rootLast n) := by
    rw [← hγ, map_mul, map_mul, map_inv]
    group
  have ht2 : Φ π₁ * Φ π₁ = 1 := by
    rw [← map_mul, ← hγ]
    have : γ * rootLast n * γ⁻¹ * (γ * rootLast n * γ⁻¹) = γ * (rootLast n * rootLast n) * γ⁻¹ :=
      by group
    rw [this, rootLast_mul_rootLast, mul_one, mul_inv_cancel, map_one]
  have ht1 : Φ π₁ ≠ 1 := by
    intro h
    apply s.map_rootLast_ne_one
    rw [← hr, h, mul_one, inv_mul_cancel]
  have hm := s.mem_normalizer_of_conj_mem_centralizer ht1 ht2 hx1
    (by rw [hr]; exact s.rootLast_mem_centralizer)
  have hk2 : Φ (γ⁻¹ * π₂ * γ) ∈ centralizer (A : Set G) := by
    have h3 := s.conj_mem_centralizer_of_mem_normalizer hm hx2
    have h4 : (Φ γ)⁻¹ * x * (x⁻¹ * Φ π₂ * x) * ((Φ γ)⁻¹ * x)⁻¹ = Φ (γ⁻¹ * π₂ * γ) := by
      rw [map_mul, map_mul, map_inv]
      group
    rwa [h4] at h3
  have hs1 := s.support_eq_of_mem_centralizer s.rootLast_mem_centralizer
    (card_support_of_cycleType cycleType_rootLast)
  have hs2 := s.support_eq_of_mem_centralizer hk2 (card_support_of_cycleType (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      show ((γ : Perm (Fin (n + 4)))⁻¹ * π₂ * γ) =
        ((γ : Perm (Fin (n + 4)))⁻¹ * π₂ * ((γ : Perm (Fin (n + 4)))⁻¹)⁻¹) by rw [inv_inv],
      cycleType_conj, h2]))
  have e1 : (π₁ : Perm (Fin (n + 4))) = (γ : Perm (Fin (n + 4))) *
      (rootLast n : Perm (Fin (n + 4))) * (γ : Perm (Fin (n + 4)))⁻¹ := by
    rw [← hγ]
    rfl
  have e2 : (π₂ : Perm (Fin (n + 4))) = (γ : Perm (Fin (n + 4))) *
      ((γ⁻¹ * π₂ * γ : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) *
        (γ : Perm (Fin (n + 4)))⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e1, e2, support_conj, support_conj, hs1, hs2]

end AltGenSetting

theorem cycleType_liftA_of_le_seven {n : ℕ} (hn : 6 ≤ n) (h7 : n ≤ 7)
    {w : alternatingGroup (Fin n)} (h2 : w * w = 1) (h1 : w ≠ 1) :
    ((liftA hn w : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))).cycleType = {2, 2} := by
  have hw2 : (w : Perm (Fin n)) * w = 1 := congrArg Subtype.val h2
  have hw1 : (w : Perm (Fin n)) ≠ 1 := fun h => h1 (Subtype.ext h)
  have hle : (w : Perm (Fin n)).support.card ≤ n := by
    have := Finset.card_le_univ (w : Perm (Fin n)).support
    rwa [Fintype.card_fin] at this
  have hct : (w : Perm (Fin n)).cycleType = {2, 2} := by
    rcases cycleType_of_mul_self hw1 hw2 (mem_alternatingGroup.mp w.2) (by omega) with h | h
    · exact h
    · exfalso
      have h8 := sum_cycleType (w : Perm (Fin n))
      rw [h] at h8
      have h8' : (w : Perm (Fin n)).support.card = 8 := by rw [← h8]; rfl
      omega
  rw [coe_liftA, cycleType_viaEmbeddingHom', cycleType_conj, hct]

theorem exists_fix_ne_of_inVexo {u v : Perm (Fin 6)} (hu : InVexo u) (hv : InVexo v)
    (huv : u ≠ v) : ∃ y : Fin 6, u y = y ∧ v y ≠ y := by
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first
    | exact absurd rfl huv
    | decide

namespace AltGenSetting

section Six

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {Φ : alternatingGroup (Fin (6 + 4)) →* G} (s : AltGenSetting A R T g 6 Φ)
include s

theorem exists_conjPerm_six {x : G}
    (hx : x ∈ normalizer (A : Set G)) :
    ∃ σ : Perm (Fin 6), ∀ z : alternatingGroup (Fin 6),
      Φ (liftA s.six_le (conjPerm 6 σ z)) = x * Φ (liftA s.six_le z) * x⁻¹ := by
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut (alternatingGroup (Fin 6)),
      α = MulAut.congr s.psiA.symm (Lemma39.normConj A ⟨x, hx⟩) := ⟨_, rfl⟩
  have hα : ∀ z, Φ (liftA s.six_le (α z)) = x * Φ (liftA s.six_le z) * x⁻¹ := by
    intro z
    rw [hαdef, MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
      MulEquiv.trans_apply, ← psiA_apply s, MulEquiv.apply_symm_apply, Lemma39.normConj_apply,
      psiA_apply]
  have hd1 : a6d1 * a6d1 = 1 := by decide
  have hd2 : a6d2 * a6d2 = 1 := by decide
  have hd1' : a6d1 ≠ 1 := by decide
  have hd2' : a6d2 ≠ 1 := by decide
  obtain ⟨γ₀, hγ₀⟩ := exists_conj_eq_of_cycleType_eq (σ := rootLast 6)
    (τ := liftA s.six_le a6d1)
    (by rw [cycleType_rootLast, cycleType_liftA_of_le_seven s.six_le (by norm_num) hd1 hd1'])
    rootLast_mul_rootLast rootLast_ne_one
  have hfix1 : ∀ i : Fin 6, (liftA s.six_le a6d1 : Perm (Fin (6 + 4)))
      ((γ₀ : Perm (Fin (6 + 4))) (Fin.castLEEmb (by omega : 6 ≤ 6 + 4) i)) =
        (γ₀ : Perm (Fin (6 + 4))) (Fin.castLEEmb (by omega : 6 ≤ 6 + 4) i) := by
    intro i
    rw [← hγ₀, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply,
      Perm.mul_apply, Perm.coe_inv, symm_apply_apply,
      s.fix_of_mem_centralizer s.rootLast_mem_centralizer i]
  have hsupp : (liftA s.six_le a6d1 : Perm (Fin (6 + 4))).support =
      (liftA s.six_le a6d2 : Perm (Fin (6 + 4))).support :=
    (support_liftA_eq_iff s.six_le a6d1 a6d2).mpr (by decide)
  have hfix2 : ∀ i : Fin 6, (liftA s.six_le a6d2 : Perm (Fin (6 + 4)))
      ((γ₀ : Perm (Fin (6 + 4))) (Fin.castLEEmb (by omega : 6 ≤ 6 + 4) i)) =
        (γ₀ : Perm (Fin (6 + 4))) (Fin.castLEEmb (by omega : 6 ≤ 6 + 4) i) := by
    intro i
    by_contra hne
    have h1 := mem_support.mpr hne
    rw [← hsupp, mem_support] at h1
    exact h1 (hfix1 i)
  have hK1 := s.conj_mem_centralizer_of_fix hfix1
  have hK2 := s.conj_mem_centralizer_of_fix hfix2
  have hconjK : ∀ w : alternatingGroup (Fin 6),
      (Φ γ₀)⁻¹ * Φ (liftA s.six_le w) * Φ γ₀ ∈ centralizer (A : Set G) →
        (x * Φ γ₀)⁻¹ * Φ (liftA s.six_le (α w)) * (x * Φ γ₀) ∈ centralizer (A : Set G) := by
    intro w hw
    rw [hα]
    have h1 : (x * Φ γ₀)⁻¹ * (x * Φ (liftA s.six_le w) * x⁻¹) * (x * Φ γ₀) =
        (Φ γ₀)⁻¹ * Φ (liftA s.six_le w) * Φ γ₀ := by group
    rw [h1]
    exact hw
  have hw1 : α a6d1 * α a6d1 = 1 := by rw [← map_mul, hd1, map_one]
  have hw2 : α a6d2 * α a6d2 = 1 := by rw [← map_mul, hd2, map_one]
  have hw1' : α a6d1 ≠ 1 := fun h => hd1' (α.injective (h.trans (map_one α).symm))
  have hw2' : α a6d2 ≠ 1 := fun h => hd2' (α.injective (h.trans (map_one α).symm))
  have hsupp' := s.support_eq_of_conj_mem_centralizer
    (cycleType_liftA_of_le_seven s.six_le (by norm_num) hw1 hw1')
    (cycleType_liftA_of_le_seven s.six_le (by norm_num) hw2 hw2') (hconjK _ hK1) (hconjK _ hK2)
  have hfixw := (support_liftA_eq_iff s.six_le (α a6d1) (α a6d2)).mp hsupp'
  have hne : ((α a6d1 : alternatingGroup (Fin 6)) : Perm (Fin 6)) ≠ α a6d2 := fun h =>
    a6d1_ne_a6d2 (congrArg Subtype.val (α.injective (Subtype.ext h)))
  have hcomm : ((α a6d1 : alternatingGroup (Fin 6)) : Perm (Fin 6)) * α a6d2 =
      (α a6d2 : Perm (Fin 6)) * α a6d1 := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
      show a6d1 * a6d2 = a6d2 * a6d1 by decide]
  have hw1p : ((α a6d1 : alternatingGroup (Fin 6)) : Perm (Fin 6)) * α a6d1 = 1 :=
    congrArg Subtype.val hw1
  have hw2p : ((α a6d2 : alternatingGroup (Fin 6)) : Perm (Fin 6)) * α a6d2 = 1 :=
    congrArg Subtype.val hw2
  have hw1q : ((α a6d1 : alternatingGroup (Fin 6)) : Perm (Fin 6)) ≠ 1 := fun h =>
    hw1' (Subtype.ext h)
  have hw2q : ((α a6d2 : alternatingGroup (Fin 6)) : Perm (Fin 6)) ≠ 1 := fun h =>
    hw2' (Subtype.ext h)
  obtain ⟨σ, -, hσ⟩ := four6_check ((α a6d1 : alternatingGroup (Fin 6)) : Perm (Fin 6)) hw1p hw1q
    (mem_alternatingGroup.mp (α a6d1).2) ((α a6d2 : alternatingGroup (Fin 6)) : Perm (Fin 6))
    hw2p hw2q hne.symm hcomm (mem_alternatingGroup.mp (α a6d2).2)
  rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    have hφ1 : InV0 ((((conjPerm 6 σ) * α) a6d1 : alternatingGroup (Fin 6)) : Perm (Fin 6)) := by
      rw [MulAut.mul_apply, conjPerm_apply]
      exact h1
    have hφ2 : InV0 ((((conjPerm 6 σ) * α) a6d2 : alternatingGroup (Fin 6)) : Perm (Fin 6)) := by
      rw [MulAut.mul_apply, conjPerm_apply]
      exact h2
    obtain ⟨τ, hτ⟩ := mem_range_conj_of_normalizes_rootFour ((conjPerm 6 σ) * α) (fun u hu => by
      have hne' : ((((conjPerm 6 σ) * α) a6d1 : alternatingGroup (Fin 6)) : Perm (Fin 6)) ≠
          (((conjPerm 6 σ) * α) a6d2 : alternatingGroup (Fin 6)) := fun he =>
        a6d1_ne_a6d2 (congrArg Subtype.val (((conjPerm 6 σ) * α).injective (Subtype.ext he)))
      rcases inV0_cover inV0_a6d1 inV0_a6d2 a6d1_ne_a6d2 hu with h | h | h
      · rw [show u = a6d1 from Subtype.ext h]
        exact hφ1
      · rw [show u = a6d2 from Subtype.ext h]
        exact hφ2
      · rw [show u = a6d1 * a6d2 from Subtype.ext h, map_mul]
        exact inV0_mul hφ1 hφ2 hne')
    refine ⟨σ⁻¹ * τ, fun z => ?_⟩
    have hz : conjPerm 6 (σ⁻¹ * τ) z = α z := by
      apply Subtype.ext
      have h3 := hτ z
      rw [MulAut.mul_apply, conjPerm_apply] at h3
      rw [conjPerm_apply]
      calc (σ⁻¹ * τ) * (z : Perm (Fin 6)) * (σ⁻¹ * τ)⁻¹ = σ⁻¹ * (τ * z * τ⁻¹) * σ := by group
        _ = σ⁻¹ * (σ * (α z : Perm (Fin 6)) * σ⁻¹) * σ := by rw [h3]
        _ = (α z : Perm (Fin 6)) := by group
    rw [hz, hα]
  ·
    exfalso
    have hne'' : σ * (α a6d1 : Perm (Fin 6)) * σ⁻¹ ≠ σ * (α a6d2 : Perm (Fin 6)) * σ⁻¹ :=
      fun he => hne (by simpa using he)
    obtain ⟨y, hy1, hy2⟩ := exists_fix_ne_of_inVexo h1 h2 hne''
    have e1 : (α a6d1 : Perm (Fin 6)) (σ⁻¹ y) = σ⁻¹ y := by
      rw [Perm.mul_apply, Perm.mul_apply] at hy1
      calc (α a6d1 : Perm (Fin 6)) (σ⁻¹ y) = σ⁻¹ (σ ((α a6d1 : Perm (Fin 6)) (σ⁻¹ y))) := by
            rw [Perm.coe_inv, symm_apply_apply]
        _ = σ⁻¹ y := by rw [hy1]
    apply hy2
    rw [Perm.mul_apply, Perm.mul_apply, (hfixw (σ⁻¹ y)).mp e1, Perm.coe_inv, apply_symm_apply]

end Six

section Small

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}
  {Φ : alternatingGroup (Fin (n + 4)) →* G} (s : AltGenSetting A R T g n Φ)
include s

theorem exists_conjPerm_small (hn : n = 6 ∨ n = 7) {x : G}
    (hx : x ∈ normalizer (A : Set G)) :
    ∃ σ : Perm (Fin n), ∀ z : alternatingGroup (Fin n),
      Φ (liftA s.six_le (conjPerm n σ z)) = x * Φ (liftA s.six_le z) * x⁻¹ := by
  rcases hn with rfl | rfl
  · exact s.exists_conjPerm_six hx
  · obtain ⟨σ, hσ⟩ := conjPerm_surjective (Or.inr le_rfl)
      ((MulAut.congr s.psiA.symm) (Lemma39.normConj A ⟨x, hx⟩))
    refine ⟨σ, fun z => ?_⟩
    rw [hσ, MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.trans_apply,
      ← psiA_apply s, MulEquiv.apply_symm_apply, Lemma39.normConj_apply, psiA_apply]

theorem normalizer_le_small (hn : n = 6 ∨ n = 7) :
    normalizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G) := fun _ hx => by
  obtain ⟨σ, hσ⟩ := s.exists_conjPerm_small hn hx
  exact s.mem_sup_of_conjPerm σ hσ

end Small

end AltGenSetting

end CFSG.ComponentClassification.RankTwoAlt
