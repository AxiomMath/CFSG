module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCase
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_eq_self_of_conj_mem_zpowers {p : ℕ} [Fact p.Prime] {x n : G} (hx1 : x ≠ 1)
    (hxp : x ^ p = 1) {k : ℕ} (hn : n ^ (p ^ k) = 1) (hxn : n * x * n⁻¹ ∈ zpowers x) :
    n * x * n⁻¹ = x := by
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hxn
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have key : ∀ i : ℕ, n ^ i * x * (n ^ i)⁻¹ = x ^ (j ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc n ^ (i + 1) * x * (n ^ (i + 1))⁻¹
          = n * (n ^ i * x * (n ^ i)⁻¹) * n⁻¹ := by group
        _ = n * x ^ (j ^ i) * n⁻¹ := by rw [ih]
        _ = (n * x * n⁻¹) ^ (j ^ i) := by simp
        _ = x ^ (j ^ (i + 1)) := by rw [← hj, ← zpow_mul, pow_succ, mul_comm]
  have h1 : x ^ (j ^ (p ^ k)) = x := by rw [← key, hn]; simp
  have h2 : (p : ℤ) ∣ j ^ (p ^ k) - 1 := by
    have : x ^ (j ^ (p ^ k) - 1) = 1 := by rw [zpow_sub, h1, zpow_one, mul_inv_cancel]
    have h := orderOf_dvd_iff_zpow_eq_one.mpr this
    rwa [hord] at h
  have h3 : ((j : ZMod p)) ^ (p ^ k) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (j ^ (p ^ k) - 1) p).mpr h2
    push_cast at this
    exact sub_eq_zero.mp this
  rw [ZMod.pow_card_pow] at h3
  have h4 : (p : ℤ) ∣ j - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h3, sub_self]
  have h5 : x ^ (j - 1) = 1 := by
    rw [← hord] at h4
    exact orderOf_dvd_iff_zpow_eq_one.mp h4
  rw [← hj, ← mul_inv_eq_one, ← zpow_sub_one, h5]

theorem isSylowOf_map_conj {p : ℕ} [Fact p.Prime] {S C : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf p S C) (g : G) :
    CFSG.ABGLocalTools.IsSylowOf p (S.map (MulAut.conj g).toMonoidHom)
      (C.map (MulAut.conj g).toMonoidHom) := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨map_mono h1, h2.map _, ?_⟩
  rwa [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

theorem IsGenericPoint.conj_of_mem_normalizer {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M : Subgroup G} (hPM : (P : Subgroup G) ≤ M) {x n : G} (hx : IsGenericPoint p P M x)
    (hnP : n ∈ (P : Subgroup G))
    (hn : n ∈ normalizer (((P : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G) :
      Set G)) : IsGenericPoint p P M (MulAut.conj n x) := by
  obtain ⟨hxP, hxL, hsyl, hrk⟩ := hx
  set S : Subgroup G := (P : Subgroup G) ⊓ centralizer ({x} : Set G) with hS
  have hSmap : S.map (MulAut.conj n).toMonoidHom = S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hPmap : (P : Subgroup G).map (MulAut.conj n).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hnP)
  have hSy : (P : Subgroup G) ⊓ centralizer ({MulAut.conj n x} : Set G) = S := by
    calc (P : Subgroup G) ⊓ centralizer ({MulAut.conj n x} : Set G)
        = (P : Subgroup G).map (MulAut.conj n).toMonoidHom ⊓
            (centralizer ({x} : Set G)).map (MulAut.conj n).toMonoidHom := by
          rw [centralizer_singleton_conj, hPmap]
      _ = S.map (MulAut.conj n).toMonoidHom :=
          (Subgroup.map_inf_eq _ _ _ (MulAut.conj n).injective).symm
      _ = S := hSmap
  refine ⟨?_, hxL.conj (hPM hnP), ?_, ?_⟩
  · rw [MulAut.conj_apply]
    exact (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hnP hxP)
      ((P : Subgroup G).inv_mem hnP)
  · rw [hSy, centralizer_singleton_conj]
    have := isSylowOf_map_conj hsyl n
    rwa [hSmap] at this
  · rw [hSy]
    exact hrk

theorem le_centralizer_of_unique_generic {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M : Subgroup G} (hPM : (P : Subgroup G) ≤ M) {x : G} (hx : IsGenericPoint p P M x)
    (hU : ∀ y : G, IsGenericPoint p P M y → zpowers y = zpowers x) :
    (P : Subgroup G) ≤ centralizer ({x} : Set G) := by
  by_contra hne
  have hprime : p.Prime := Fact.out
  obtain ⟨-, ⟨-, hx1, hxp, -, -⟩, -, -⟩ := id hx
  set S : Subgroup G := (P : Subgroup G) ⊓ centralizer ({x} : Set G) with hS
  have hlt : S < (P : Subgroup G) :=
    lt_of_le_of_ne inf_le_left fun h => hne (h ▸ inf_le_right)
  obtain ⟨n, ⟨hnP, hnN⟩, hnS⟩ := IsConcreteLE.exists_of_lt
    (pGroup_proper_subgroup_lt_internal_normalizer p hprime P S P.isPGroup' hlt)
  have hy := hx.conj_of_mem_normalizer hPM hnP hnN
  have hmem : n * x * n⁻¹ ∈ zpowers x := by
    have := hU _ hy ▸ mem_zpowers (MulAut.conj n x)
    simpa [MulAut.conj_apply] using this
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨n, hnP⟩
  have hk' : n ^ (p ^ k) = 1 := congrArg Subtype.val hk
  have hcomm := conj_eq_self_of_conj_mem_zpowers hx1 hxp hk' hmem
  exact hnS ⟨hnP, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hcomm)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
