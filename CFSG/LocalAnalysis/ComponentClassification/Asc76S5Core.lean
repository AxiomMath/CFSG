module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Rep
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_le_inf {A L X : Subgroup G} (hXL : X ≤ L) (hXA : X ≤ normalizer (A : Set G))
    (hAL : A ≤ normalizer (L : Set G)) : ⁅X, A⁆ ≤ A ⊓ L := by
  rw [commutator_le]
  intro x hx a ha
  refine ⟨?_, ?_⟩
  · have h := (mem_normalizer_iff.mp (hXA hx) a).mp ha
    have : ⁅x, a⁆ = (x * a * x⁻¹) * a⁻¹ := by group
    rw [this]
    exact A.mul_mem h (A.inv_mem ha)
  · have h := (mem_normalizer_iff.mp (hAL ha) x⁻¹).mp (L.inv_mem (hXL hx))
    have : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by group
    rw [this]
    exact L.mul_mem (hXL hx) h

theorem commutator_le_inf_of_le_normalizer {H₁ H₂ : Subgroup G}
    (h1 : H₁ ≤ normalizer (H₂ : Set G)) (h2 : H₂ ≤ normalizer (H₁ : Set G)) :
    ⁅H₁, H₂⁆ ≤ H₁ ⊓ H₂ := by
  rw [commutator_le]
  intro x hx y hy
  refine ⟨?_, ?_⟩
  · have h := (mem_normalizer_iff.mp (h2 hy) x⁻¹).mp (H₁.inv_mem hx)
    have : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [this]
    exact H₁.mul_mem hx h
  · have h := (mem_normalizer_iff.mp (h1 hx) y).mp hy
    have : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by group
    rw [this]
    exact H₂.mul_mem h (H₂.inv_mem hy)

theorem mem_normalizer_rightConjugate {Y : Subgroup G} {m x : G} :
    x ∈ normalizer (rightConjugate Y m : Set G) ↔ m * x * m⁻¹ ∈ normalizer (Y : Set G) := by
  rw [← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff]

variable [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_of_normal {A K₀ L : Subgroup G}
    (hA : standardComponentIsStandard A) (hK₀K : K₀ ≤ centralizer (A : Set G))
    (hK₀ : Even (Nat.card K₀))
    (hNK : normalizer (centralizer (A : Set G) : Set G) ≤ normalizer (K₀ : Set G))
    (hK₀L : K₀ ≤ L) (hLK₀ : L ≤ normalizer (K₀ : Set G)) (hAL : A ≤ normalizer (L : Set G))
    (hO : ∀ N : Subgroup G, N ≤ L → L ≤ normalizer (N : Set G) → Odd (Nat.card N) → N = ⊥) :
    normalizer (L : Set G) ≤ normalizer (K₀ : Set G) := by
  have hq : Open.IsQuasisimple A := hA.1
  have hAA : ⁅A, A⁆ = A := commutator_self_of_isQuasisimple hq
  set K := centralizer (A : Set G) with hKdef
  have hK : TightlyEmbedded K := tightlyEmbedded_centralizer hA
  have hNA : normalizer (K : Set G) = normalizer (A : Set G) := normalizer_centralizer_eq hA
  have hK₀N : normalizer (K₀ : Set G) ≤ normalizer (K : Set G) :=
    normalizer_le_normalizer_of_tightlyEmbedded hK hK₀K hK₀
  intro m hm
  by_contra hmK₀
  have hmK : m ∉ normalizer (K : Set G) := fun h => hmK₀ (hNK h)
  set X := rightConjugate K₀ m with hX
  have hXL : X ≤ L := by
    rw [← (rightConjugate_eq_self_iff L m).mpr hm]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate hK₀L m
  have hLX : L ≤ normalizer (X : Set G) := by
    intro l hl
    rw [mem_normalizer_rightConjugate]
    exact hLK₀ ((mem_normalizer_iff.mp hm l).mp hl)
  have hKX : K₀ ⊓ X = ⊥ := by
    refine hO _ (inf_le_left.trans hK₀L) (fun l hl => mem_normalizer_inf (hLK₀ hl) (hLX hl)) ?_
    have hle : K₀ ⊓ X ≤ K ⊓ rightConjugate K m :=
      inf_le_inf hK₀K (AschbacherTheorem3.rightConjugate_le_rightConjugate hK₀K m)
    exact (hK.2 m hmK).of_dvd_nat (card_dvd_of_le hle)
  have hcomm : ⁅K₀, X⁆ = ⊥ := by
    rw [eq_bot_iff, ← hKX]
    exact commutator_le_inf_of_le_normalizer (hK₀L.trans hLX) (hXL.trans hLK₀)
  have hXA : X ≤ normalizer (A : Set G) := by
    have h1 : X ≤ centralizer (K₀ : Set G) := by
      rw [commutator_comm] at hcomm
      exact (commutator_eq_bot_iff_le_centralizer).mp hcomm
    rw [← hNA]
    exact h1.trans ((centralizer_le_normalizer _).trans hK₀N)
  have hXAc : ⁅X, A⁆ = ⊥ := by
    have hAinf : A ≤ normalizer ((A ⊓ L : Subgroup G) : Set G) := fun a ha =>
      mem_normalizer_inf (le_normalizer ha) (hAL ha)
    rcases le_centerOf_or_eq_of_le_normalizer hq inf_le_left hAinf with hZ | hEq
    · refine commutator_eq_bot_of_commutator_commutator_eq_bot hAA ?_
      rw [commutator_eq_bot_iff_le_centralizer]
      exact (commutator_le_inf hXL hXA hAL).trans (hZ.trans inf_le_right)
    · have hAL' : A ≤ L := hEq ▸ inf_le_right
      have hAX : A ≤ normalizer (X : Set G) := hAL'.trans hLX
      have hAXinf : A ≤ normalizer ((X ⊓ A : Subgroup G) : Set G) := fun a ha =>
        mem_normalizer_inf (hAX ha) (le_normalizer ha)
      rcases le_centerOf_or_eq_of_le_normalizer hq inf_le_right hAXinf with hZ' | hEq'
      · exact commutator_eq_bot_of_inf_le_centerOf hq hXA hAX (hZ'.trans inf_le_right)
      · exfalso
        have hAKm : A ≤ centralizer (rightConjugate A m : Set G) := by
          rw [← AschbacherTheorem3.rightConjugate_centralizer]
          exact (hEq' ▸ inf_le_left).trans
            (AschbacherTheorem3.rightConjugate_le_rightConjugate hK₀K m)
        exact commutator_rightConjugate_ne_bot hA m
          ((commutator_eq_bot_iff_le_centralizer).mpr hAKm)
  have hXK : X ≤ K := (commutator_eq_bot_iff_le_centralizer).mp hXAc
  have hle : X ≤ K ⊓ rightConjugate K m :=
    le_inf hXK (AschbacherTheorem3.rightConjugate_le_rightConjugate hK₀K m)
  have hodd := (hK.2 m hmK).of_dvd_nat (card_dvd_of_le hle)
  rw [hX, rightConjugate_card] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) hK₀

theorem le_centralizer_of_isSzOrU3 {A N₁ P : Subgroup G} (hA : ⁅A, A⁆ = A) (hN : IsSzOrU3 N₁)
    (hAN : A ≤ normalizer (N₁ : Set G)) (hP : IsSylowOf 2 P N₁)
    (hAP : A ≤ centralizer (P : Set G)) : A ≤ centralizer (N₁ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  set ψ : A →* MulAut N₁ := N₁.normalizerMonoidHom.comp (inclusion hAN) with hψ
  have hψapp : ∀ (a : A) (x : N₁), ((ψ a x : N₁) : G) = (a : G) * x * (a : G)⁻¹ := by
    intro a x
    rfl
  have hfix : ∀ a : A, ∃ c ∈ (Q : Subgroup N₁),
      c ∈ centralizer ((Q : Subgroup N₁) : Set N₁) ∧ ψ a = MulAut.conj c := by
    intro a
    refine Asc76X.benderFacts.aut_fix_sylow N₁ hN Q (ψ a) fun x hx => ?_
    have hxP : (x : G) ∈ P := by
      rw [hQ] at hx
      exact hx
    apply Subtype.ext
    rw [hψapp]
    have h := mem_centralizer_iff.mp (hAP a.2) x hxP
    calc (a : G) * x * (a : G)⁻¹ = x * a * (a : G)⁻¹ := by rw [h]
      _ = x := by group
  have hab : ∀ a b : A, ψ a * ψ b = ψ b * ψ a := by
    intro a b
    obtain ⟨c, hc, hcZ, hca⟩ := hfix a
    obtain ⟨d, hd, -, hdb⟩ := hfix b
    rw [hca, hdb, ← map_mul, ← map_mul]
    congr 1
    exact (mem_centralizer_iff.mp hcZ d hd).symm
  have hker : ∀ a : A, ψ a = 1 := by
    have hle : ⁅A, A⁆ ≤ (ψ.ker).map A.subtype := by
      rw [commutator_le]
      intro x hx y hy
      refine ⟨⁅(⟨x, hx⟩ : A), (⟨y, hy⟩ : A)⁆, ?_, rfl⟩
      change ψ ⁅(⟨x, hx⟩ : A), (⟨y, hy⟩ : A)⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hab _ _
    intro a
    have ha : (a : G) ∈ (ψ.ker).map A.subtype := hle (hA.symm ▸ a.2)
    obtain ⟨b, hb, hba⟩ := ha
    have : b = a := Subtype.ext hba
    rw [← this]
    exact hb
  intro a ha
  rw [mem_centralizer_iff]
  intro x hx
  have h := congrArg Subtype.val (DFunLike.congr_fun (hker ⟨a, ha⟩) ⟨x, hx⟩)
  rw [hψapp] at h
  change a * x * a⁻¹ = x at h
  calc x * a = a * x * a⁻¹ * a := by rw [h]
    _ = a * x := by group

end CFSG.ComponentClassification.Asc76.Sec5
