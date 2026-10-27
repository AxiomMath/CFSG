module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.CharacterTheory.Semidihedral.Local.PowerFusionTransfer

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open Subgroup CFSG.ABGLocalTools

variable {X : Type*} [Group X] [Finite X]

theorem exists_mem_normalizer_of_lt {T P : Subgroup X} (hP : IsPGroup 2 P) (hTP : T < P) :
    ∃ n ∈ P, n ∉ T ∧ ∀ x ∈ T, n * x * n⁻¹ ∈ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent P := hP.isNilpotent
  have hlt : T.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    exact absurd hTP (not_lt_of_ge (subgroupOf_eq_top.mp h))
  have h2 := normalizerCondition_of_isNilpotent (G := P) (T.subgroupOf P) hlt
  obtain ⟨n, hn, hn'⟩ := SetLike.exists_of_lt h2
  refine ⟨n, n.2, hn', fun x hx => ?_⟩
  have hxP : x ∈ P := hTP.le hx
  exact (mem_normalizer_iff.mp hn ⟨x, hxP⟩).mp hx

theorem isSylowOf_top_of_fusion {T : Subgroup X} (hT : IsPGroup 2 T) {t : X} (htT : t ∈ T)
    (hC : ∃ m : ℕ, Odd m ∧
      Nat.card (centralizer ({t} : Set X)) = Nat.card (T ⊓ centralizer ({t} : Set X) : Subgroup X) * m)
    (hfus : ∀ g : X, g * t * g⁻¹ ∈ T → ∃ τ ∈ T, g * t * g⁻¹ = τ * t * τ⁻¹) :
    IsSylowOf 2 T ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hTP⟩ := hT.exists_le_sylow
  have hPT : (P : Subgroup X) ≤ T := by
    by_contra hnle
    have hlt : T < (P : Subgroup X) := lt_of_le_of_ne hTP (fun h => hnle (h ▸ le_refl _))
    obtain ⟨n, hnP, hnT, hnorm⟩ := exists_mem_normalizer_of_lt P.isPGroup' hlt
    obtain ⟨τ, hτT, hτ⟩ := hfus n (hnorm t htT)
    have hcn : τ⁻¹ * n ∈ centralizer ({t} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      have h1 : τ⁻¹ * n * t = t * (τ⁻¹ * n) := by
        have h2 : n * t * n⁻¹ * n = τ * t * τ⁻¹ * n := by rw [hτ]
        have h3 : n * t = τ * t * τ⁻¹ * n := by simpa [mul_assoc] using h2
        calc τ⁻¹ * n * t = τ⁻¹ * (n * t) := by rw [mul_assoc]
          _ = τ⁻¹ * (τ * t * τ⁻¹ * n) := by rw [h3]
          _ = t * (τ⁻¹ * n) := by group
      exact h1
    have hcP : τ⁻¹ * n ∈ (P : Subgroup X) ⊓ centralizer ({t} : Set X) :=
      ⟨P.mul_mem (P.inv_mem (hTP hτT)) hnP, hcn⟩
    have hAB : T ⊓ centralizer ({t} : Set X) ≤ (P : Subgroup X) ⊓ centralizer ({t} : Set X) :=
      inf_le_inf_right _ hTP
    obtain ⟨m, hmodd, hm⟩ := hC
    have hBpg : IsPGroup 2 ((P : Subgroup X) ⊓ centralizer ({t} : Set X) : Subgroup X) :=
      P.isPGroup'.to_inf_left
    have hApg : IsPGroup 2 (T ⊓ centralizer ({t} : Set X) : Subgroup X) := hT.to_inf_left
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hBpg
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hApg
    have hBdvd : Nat.card ((P : Subgroup X) ⊓ centralizer ({t} : Set X) : Subgroup X) ∣
        Nat.card (centralizer ({t} : Set X)) :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hb, hm, ha] at hBdvd
    have hcop : Nat.Coprime (2 ^ b) m := (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hmodd))
    have hba : 2 ^ b ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right hBdvd
    have hle : Nat.card ((P : Subgroup X) ⊓ centralizer ({t} : Set X) : Subgroup X) ≤
        Nat.card (T ⊓ centralizer ({t} : Set X) : Subgroup X) := by
      rw [hb, ha]
      exact Nat.le_of_dvd (by positivity) hba
    have heq : T ⊓ centralizer ({t} : Set X) = (P : Subgroup X) ⊓ centralizer ({t} : Set X) :=
      Subgroup.eq_of_le_of_card_ge hAB hle
    have : τ⁻¹ * n ∈ T := (heq ▸ hcP).1
    apply hnT
    have h5 := T.mul_mem hτT this
    simpa using h5
  have hPeq : (P : Subgroup X) = T := le_antisymm hPT hTP
  rw [isSylowOf_iff]
  refine ⟨le_top, hT, ?_⟩
  rw [relIndex_top_right, ← hPeq]
  exact P.not_dvd_index

theorem isMulCommutative_of_index_two {P : Type*} [Group P] (N : Subgroup P) [N.Normal]
    (h : N.index = 2) : IsMulCommutative (P ⧸ N) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card (P ⧸ N) = 2 := h
  haveI : IsCyclic (P ⧸ N) := isCyclic_of_prime_card hc
  infer_instance

theorem not_mem_commutator_of_fusion {P : Sylow 2 X} {U : Subgroup X} {t : X}
    (hUP : U ≤ (P : Subgroup X)) (hUn : (U.subgroupOf (P : Subgroup X)).Normal)
    (hidx : (U.subgroupOf (P : Subgroup X)).index = 2) (htP : t ∈ (P : Subgroup X))
    (ht2 : t * t = 1) (htU : t ∉ U)
    (hfus : ∀ g : X, g * t * g⁻¹ ∈ (P : Subgroup X) → g * t * g⁻¹ ∉ U) :
    t ∉ commutator X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup (P : Subgroup X) := U.subgroupOf (P : Subgroup X) with hN
  haveI : N.Normal := hUn
  haveI : IsMulCommutative ((P : Subgroup X) ⧸ N) := isMulCommutative_of_index_two N hidx
  set x : (P : Subgroup X) := ⟨t, htP⟩ with hx
  have hxN : x ∉ N := fun h => htU h
  have hfus' : ∀ (k : ℕ) (g : X) (h : g⁻¹ * (x : X) ^ k * g ∈ (P : Subgroup X)),
      (QuotientGroup.mk' N ⟨g⁻¹ * (x : X) ^ k * g, h⟩ : (P : Subgroup X) ⧸ N) =
        QuotientGroup.mk' N (x ^ k) := by
    intro k g h
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hxx : (x : X) ^ k = 1 := by
        rw [hj, ← two_mul, pow_mul, show (x : X) ^ 2 = 1 by rw [sq]; exact ht2, one_pow]
      have hxx' : x ^ k = 1 := Subtype.ext hxx
      have : (⟨g⁻¹ * (x : X) ^ k * g, h⟩ : (P : Subgroup X)) = 1 := by
        apply Subtype.ext
        simp [hxx]
      rw [this, hxx']
    · have hxk : (x : X) ^ k = t := by
        rw [hj, pow_succ, pow_mul, show (x : X) ^ 2 = 1 by rw [sq]; exact ht2, one_pow, one_mul]
      have hxk' : x ^ k = x := by
        apply Subtype.ext
        simpa using hxk
      have hy : g⁻¹ * t * g ∉ U := by
        have := hfus g⁻¹ (by simpa [hxk] using h)
        simpa using this
      have hy' : (⟨g⁻¹ * (x : X) ^ k * g, h⟩ : (P : Subgroup X)) ∉ N := by
        intro hmemN
        apply hy
        rw [hN, mem_subgroupOf] at hmemN
        simpa [hxk] using hmemN
      have hmem : x⁻¹ * ⟨g⁻¹ * (x : X) ^ k * g, h⟩ ∈ N :=
        (mul_mem_iff_of_index_two hidx).mpr
          ⟨fun hxi => absurd (inv_mem_iff.mp hxi) hxN, fun hyN => absurd hyN hy'⟩
      have hmem' : (⟨g⁻¹ * (x : X) ^ k * g, h⟩ : (P : Subgroup X))⁻¹ * x ∈ N := by
        have := N.inv_mem hmem
        simpa [mul_inv_rev] using this
      rw [hxk']
      exact QuotientGroup.eq.mpr hmem'
  obtain ⟨-, -, -, hxK, -⟩ := CFSG.Semidihedral.Local.power_fusion_transfer_detection P N x hxN hfus'
  intro hcomm
  apply hxK
  exact Abelianization.commutator_subset_ker _ hcomm

theorem isSylowOf_commutator_of_fusion {P : Sylow 2 X} {U : Subgroup X} {t : X}
    (hUP : U ≤ (P : Subgroup X)) (hidx : (U.subgroupOf (P : Subgroup X)).index = 2)
    (htP : t ∈ (P : Subgroup X)) (htc : t ∉ commutator X) (hUc : U ≤ commutator X) :
    IsSylowOf 2 U (commutator X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsSylowOf 2 (P : Subgroup X) ⊤ := by
    rw [isSylowOf_iff]
    exact ⟨le_top, P.isPGroup', by rw [relIndex_top_right]; exact P.not_dvd_index⟩
  have h1 := hP.inf_of_le_normalizer (N := commutator X) le_top
    (by rw [normalizer_eq_top])
  have h2 : (P : Subgroup X) ⊓ commutator X = U := by
    refine le_antisymm ?_ (le_inf hUP hUc)
    rintro y ⟨hyP, hyc⟩
    by_contra hyU
    have htU : t ∉ U := fun h => htc (hUc h)
    have hmem : (⟨t, htP⟩ : (P : Subgroup X))⁻¹ * ⟨y, hyP⟩ ∈ U.subgroupOf (P : Subgroup X) :=
      (mul_mem_iff_of_index_two hidx).mpr
        ⟨fun hti => absurd (by simpa [mem_subgroupOf] using inv_mem_iff.mp hti) htU,
          fun hyU' => absurd (by simpa [mem_subgroupOf] using hyU') hyU⟩
    have hmem' : t⁻¹ * y ∈ U := by simpa [mem_subgroupOf] using hmem
    have : t ∈ commutator X := by
      have h3 : t = y * (t⁻¹ * y)⁻¹ := by group
      rw [h3]
      exact mul_mem hyc (inv_mem (hUc hmem'))
    exact htc this
  rwa [h2] at h1

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
