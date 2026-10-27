module

public import CFSG.ClassicalInvolution.Q3.Q3NLExact
public import CFSG.ClassicalInvolution.Uniform.UStand
public import CFSG.ClassicalInvolution.Asc77.AscT3SInv
public import CFSG.ClassicalInvolution.Asc77.AscT3CoreInvol

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3CII.T3S
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement Pointwise

section Conj

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_exactCore3_sup {K K' : Subgroup G} {z c t : G}
    (hK : IsClassicalMember3 K z) (hK' : IsClassicalMember3 K' z)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcK : c ∈ trivialOnQuot K)
    (hcK' : c ∈ trivialOnQuot K') (hKN' : K ≤ Subgroup.normalizer (K' : Set G))
    (hK'N : K' ≤ Subgroup.normalizer (K : Set G)) (ht : t ∈ K ⊔ K') (ht2 : t * t = 1)
    (htc : c * t = t * c) :
    ∃ g ∈ K ⊔ K', c * g = g * c ∧ g * t * g⁻¹ ∈ exactCore3 c K ⊔ exactCore3 c K' := by
  classical
  set M : Subgroup G := K ⊔ K'
  set N₀ : Subgroup G := oddCoreOf M
  have hNodd : Odd (Nat.card N₀) := oddCoreOf_odd_natCard M
  have hKN : oddCoreOf K ≤ N₀ := oddCoreOf_le_oddCoreOf_sup hK'N
  have hK'N₀ : oddCoreOf K' ≤ N₀ := by
    have := oddCoreOf_le_oddCoreOf_sup hKN'
    rwa [sup_comm] at this
  have hNnorm : ∀ x ∈ M, ∀ n ∈ N₀, x * n * x⁻¹ ∈ N₀ := fun x hx n hn =>
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer
      (Subgroup.le_normalizer hx)) n).mp hn
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htM : t ∈ M := ht
  have hmul : t ∈ (K : Set G) * (K' : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K K' hKN']
    exact ht
  obtain ⟨k, hk, k', hk', hkk'⟩ := hmul
  obtain ⟨i, hi, n, hn, hkin⟩ := exactCore3_cover hK hc2 hcK k hk
  obtain ⟨i', hi', n', hn', hkin'⟩ := exactCore3_cover hK' hc2 hcK' k' hk'
  have hi'M : i' ∈ M := Subgroup.mem_sup_right (exactCore3_le_left c K' hi')
  set P₀ : Subgroup G := exactCore3 c K ⊔ exactCore3 c K'
  set pp : G := i * i' with hpp
  have hppP : pp ∈ P₀ := P₀.mul_mem (Subgroup.mem_sup_left hi) (Subgroup.mem_sup_right hi')
  set m : G := (i'⁻¹ * n * i') * n' with hmdef
  have hmN : m ∈ N₀ := by
    refine N₀.mul_mem ?_ (hK'N₀ hn')
    have := hNnorm i'⁻¹ (M.inv_mem hi'M) n (hKN hn)
    simpa using this
  have htpm : t = pp * m := by
    rw [← hkk', hkin, hkin', hpp, hmdef]
    group
  have hcp : c * pp = pp * c := by
    have h1 : c * i = i * c :=
      (Subgroup.mem_centralizer_singleton_iff.mp (exactCore3_le_centralizer c K hi)).symm
    have h2 : c * i' = i' * c :=
      (Subgroup.mem_centralizer_singleton_iff.mp (exactCore3_le_centralizer c K' hi')).symm
    rw [hpp, ← mul_assoc, h1, mul_assoc, h2]
    group
  have hcpow : ∀ j : ℕ, c * pp ^ j = pp ^ j * c := fun j =>
    ((show Commute c pp from hcp).pow_right j).eq
  have hpm : pp = t * m⁻¹ := by
    rw [htpm]
    group
  have hq : pp * pp ∈ N₀ := by
    have e : pp * pp = (t * m⁻¹ * t⁻¹) * m⁻¹ := by
      calc pp * pp = (t * m⁻¹) * (t * m⁻¹) := by rw [← hpm]
        _ = (t * m⁻¹ * t⁻¹) * m⁻¹ := by rw [hti]; group
    rw [e]
    exact N₀.mul_mem (hNnorm t htM _ (N₀.inv_mem hmN)) (N₀.inv_mem hmN)
  set q : G := pp * pp
  have hqodd : Odd (orderOf q) :=
    hNodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N₀ hq)
  obtain ⟨s, hs⟩ := hqodd
  set u : G := pp ^ orderOf q with hu
  have huP : u ∈ P₀ := P₀.pow_mem hppP _
  have huu : u * u = 1 := by
    rw [hu, ← pow_add, ← two_mul, pow_mul, sq]
    exact pow_orderOf_eq_one q
  have hqs : q ^ s ∈ N₀ := N₀.pow_mem hq s
  have hut : u * t ∈ N₀ := by
    have e : u * t = q ^ s * (t * m⁻¹ * t⁻¹) := by
      have hu' : u = q ^ s * pp := by
        rw [hu, hs, pow_succ, pow_mul, sq]
      rw [hu', hti]
      nth_rewrite 1 [hpm]
      group
    rw [e]
    exact N₀.mul_mem hqs (hNnorm t htM _ (N₀.inv_mem hmN))
  have hutodd : Odd (orderOf (u * t)) :=
    hNodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N₀ hut)
  obtain ⟨j, hj⟩ := T3Core.exists_conj_of_mul_mem_odd huu ht2 hutodd
  have hcu : c * u = u * c := hcpow _
  have hcut : c * (u * t) = (u * t) * c := by
    rw [← mul_assoc, hcu, mul_assoc, htc, mul_assoc]
  have hcutj : c * (u * t) ^ j = (u * t) ^ j * c :=
    ((show Commute c (u * t) from hcut).pow_right j).eq
  have hgN : (u * t) ^ j ∈ N₀ := N₀.pow_mem hut j
  refine ⟨((u * t) ^ j)⁻¹, M.inv_mem (oddCoreOf_le_self M hgN), ?_, ?_⟩
  · have := ((show Commute c ((u * t) ^ j) from hcutj).inv_right).eq
    exact this
  · have e : ((u * t) ^ j)⁻¹ * t * (((u * t) ^ j)⁻¹)⁻¹ = u := by
      have h1 : (u * t) ^ j * u * ((u * t) ^ j)⁻¹ = t := hj
      calc ((u * t) ^ j)⁻¹ * t * (((u * t) ^ j)⁻¹)⁻¹
          = ((u * t) ^ j)⁻¹ * ((u * t) ^ j * u * ((u * t) ^ j)⁻¹) * (((u * t) ^ j)⁻¹)⁻¹ := by
            rw [h1]
        _ = u := by group
    rw [e]
    exact huP

theorem exactCore3_mul_eq {K : Subgroup G} {z a : G}
    (hKz : K ≤ Subgroup.centralizer ({z} : Set G)) : exactCore3 (a * z) K = exactCore3 a K := by
  have h : K ⊓ Subgroup.centralizer ({a * z} : Set G) = K ⊓ Subgroup.centralizer ({a} : Set G) := by
    ext k
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hk, h1⟩
      refine ⟨hk, ?_⟩
      have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp (hKz hk)
      have : k * a * z = a * k * z := by
        calc k * a * z = k * (a * z) := by group
          _ = (a * z) * k := h1
          _ = a * (z * k) := by group
          _ = a * (k * z) := by rw [hkz]
          _ = a * k * z := by group
      exact mul_right_cancel this
    · rintro ⟨hk, h1⟩
      refine ⟨hk, ?_⟩
      have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp (hKz hk)
      calc k * (a * z) = (k * a) * z := by group
        _ = (a * k) * z := by rw [h1]
        _ = a * (k * z) := by group
        _ = a * (z * k) := by rw [hkz]
        _ = (a * z) * k := by group
  exact h

theorem conjSub_closure_triple (h x y w : G) :
    conjSub h (Subgroup.closure ({x, y, w} : Set G)) =
      Subgroup.closure ({h * x * h⁻¹, h * y * h⁻¹, h * w * h⁻¹} : Set G) := by
  unfold conjSub
  rw [MonoidHom.map_closure]
  congr 1
  ext v
  simp [Set.image_insert_eq, MulAut.conj_apply]

theorem closure_triple_mul_right {z t a : G} (hz : z * z = 1) :
    Subgroup.closure ({z, t, a * z} : Set G) = Subgroup.closure ({z, t, a} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro v hv
    rcases hv with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  · rw [Subgroup.closure_le]
    intro v hv
    rcases hv with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · have h1 : v * z ∈ Subgroup.closure ({z, t, v * z} : Set G) :=
        Subgroup.subset_closure (by simp)
      have h2 : z ∈ Subgroup.closure ({z, t, v * z} : Set G) :=
        Subgroup.subset_closure (by simp)
      have := Subgroup.mul_mem _ h1 h2
      rwa [mul_assoc, hz, mul_one] at this

theorem isClassicalMember3_of_unique {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) {M : Subgroup G} (hM : M ∈ Ω) {t : G}
    (hMt : IsUniqueInvolution M t) : IsClassicalMember3 M t := by
  obtain ⟨w, hw⟩ := hΩ.classical M hM
  have hwt : w = t := (hw.isUniqueInvolution_sl2).eq hMt
  subst hwt
  exact hw.toQ3 (by norm_num)

end Conj

end CFSG.ClassicalInvolution.Q3.Q3T6D
