module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem7OneS331
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22A

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped Pointwise

namespace Lem22

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

variable {T L V H P : Subgroup G} {p : ℕ}

theorem oTwoUpper_le_sup_F4 (h331 : Stmt3_3_1_F4) (hyp : Hyp1223 G T L V)
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hsol : Group.IsSolvable ↥H)
    (hp : p.Prime) (hp2 : p ≠ 2) (hPp : IsPGroup p ↥P) (hPH : P ≤ H)
    (hPi : ¬ p ∣ P.relIndex H) (hP1 : P ≠ ⊥) : oTwoUpper H ≤ P ⊔ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hmin := (Lem7.minParabolic_F4 h331 hyp hHs).subgroupOf
  obtain ⟨q, hq, hq2, hZ⟩ := hmin.exists_odd_prime_of_solvable hsol
  have hpH : p ∣ Nat.card ↥H := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hP1 (Subgroup.eq_bot_of_card_eq P hk)
    have h1 : p ^ k ∣ Nat.card ↥H := by
      rw [← hk]
      exact Subgroup.card_dvd_of_le hPH
    exact (dvd_pow_self p hk0).trans h1
  have hpq : p = q := (hZ p hp hpH).resolve_left hp2
  subst hpq
  set N := CFSG.Open.pCore 2 ↥H with hN
  set φ := QuotientGroup.mk' N with hφ
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hker : φ.ker ≤ (H ⊓ Subgroup.normalizer (L : Set G)).subgroupOf H := by
    rw [hφ, QuotientGroup.ker_mk']
    exact hmin.pCore_le_M
  have hmY := hmin.map_of_surjective hsurj hker
  have hOY : CFSG.Open.pCore 2 (↥H ⧸ N) = ⊥ := B6.pCore_quotient_pCore
  have hZY : ∀ r : ℕ, r.Prime → r ∣ Nat.card (↥H ⧸ N) → r = 2 ∨ r = p :=
    fun r hr hrY => hZ r hr (hrY.trans (Subgroup.index_dvd_card _))
  have hKY : IsPGroup p (twoResidual (⊤ : Subgroup (↥H ⧸ N))) :=
    hmY.isPGroup_twoResidual_of_pCore_eq_bot hOY inferInstance hp hZY
  have hKn : (twoResidual (⊤ : Subgroup (↥H ⧸ N))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  set P' := P.subgroupOf H with hP'
  have hP'p : IsPGroup p ↥P' := hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hP'i : ¬ p ∣ (P'.map φ).index := fun hd =>
    hPi (hd.trans (Subgroup.index_map_dvd P' hsurj))
  have hKS := hKY.le_sylow_of_normal ((hP'p.map φ).toSylow hP'i)
  intro k hk
  have hkH : k ∈ H := oTwoUpper_le H hk
  have hkK : (⟨k, hkH⟩ : ↥H) ∈ twoResidual (⊤ : Subgroup ↥H) := by
    rw [B6.twoResidual_top_eq_subgroupOf H, Subgroup.mem_subgroupOf]
    exact oTwoUpper_le_of_pow_mem (twoResidual_isTwoQuotient H) hk
  have hkK' : φ ⟨k, hkH⟩ ∈ twoResidual (⊤ : Subgroup (↥H ⧸ N)) := by
    rw [← B6.twoResidual_map_top hsurj]
    exact Subgroup.mem_map_of_mem φ hkK
  obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.mp (hKS hkK')
  have hxN : x⁻¹ * ⟨k, hkH⟩ ∈ N := QuotientGroup.eq.mp hxk
  have hmem : (x : G)⁻¹ * k ∈ pCoreOf 2 H := ⟨_, hxN, rfl⟩
  have e : k = (x : G) * ((x : G)⁻¹ * k) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
    (Subgroup.mem_sup_right hmem)

theorem le_normalizer_sup_F4 (h331 : Stmt3_3_1_F4) (hyp : Hyp1223 G T L V)
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hsol : Group.IsSolvable ↥H)
    (hp : p.Prime) (hp2 : p ≠ 2) (hPp : IsPGroup p ↥P) (hPH : P ≤ H)
    (hPi : ¬ p ∣ P.relIndex H) (hP1 : P ≠ ⊥) :
    H ≤ Subgroup.normalizer ((P ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
  have heq : P ⊔ pCoreOf 2 H = oTwoUpper H ⊔ pCoreOf 2 H :=
    le_antisymm (sup_le_sup_right (le_oTwoUpper hp hp2 hPp hPH) _)
      (sup_le (oTwoUpper_le_sup_F4 h331 hyp hHs hsol hp hp2 hPp hPH hPi hP1) le_sup_right)
  rw [heq]
  intro g hg
  exact Lem21Post.mem_normalizer_sup (le_normalizer_oTwoUpper H hg)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hg)

theorem exists_pow_mem_sup_F4 (h331 : Stmt3_3_1_F4) (hyp : Hyp1223 G T L V)
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hsol : Group.IsSolvable ↥H)
    (hp : p.Prime) (hp2 : p ≠ 2) (hPp : IsPGroup p ↥P) (hPH : P ≤ H)
    (hPi : ¬ p ∣ P.relIndex H) (hP1 : P ≠ ⊥) {x : G} (hx : x ∈ H) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ P ⊔ pCoreOf 2 H := by
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H hx
  exact ⟨k, oTwoUpper_le_sup_F4 h331 hyp hHs hsol hp hp2 hPp hPH hPi hP1 hk⟩

theorem exists_mul_of_mem_F4 (h331 : Stmt3_3_1_F4) (hyp : Hyp1223 G T L V)
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hsol : Group.IsSolvable ↥H)
    (hp : p.Prime) (hp2 : p ≠ 2) (hPp : IsPGroup p ↥P) (hPH : P ≤ H)
    (hPi : ¬ p ∣ P.relIndex H) (hP1 : P ≠ ⊥) (hHPT : H = P ⊔ T) {g : G} (hg : g ∈ H) :
    ∃ x ∈ P, ∃ t ∈ T, g = x * t := by
  have hmin := Lem7.minParabolic_F4 h331 hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  set N₁ := P ⊔ pCoreOf 2 H with hN₁
  have hTN : T ≤ Subgroup.normalizer (N₁ : Set G) :=
    hTH.trans (le_normalizer_sup_F4 h331 hyp hHs hsol hp hp2 hPp hPH hPi hP1)
  have hgK : g ∈ N₁ ⊔ T := by
    have hle : H ≤ N₁ ⊔ T := by
      rw [hHPT]
      exact sup_le_sup_right le_sup_left T
    exact hle hg
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left N₁ T hTN
  have hgK' : g ∈ (N₁ : Set G) * (T : Set G) := by
    rw [← hset]
    exact hgK
  obtain ⟨n, hn, t, ht, hnt⟩ := hgK'
  have hPQ : P ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hPH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hset2 := Subgroup.coe_mul_of_left_le_normalizer_right P (pCoreOf 2 H) hPQ
  have hn' : n ∈ (P : Set G) * (pCoreOf 2 H : Set G) := by
    rw [← hset2]
    exact hn
  obtain ⟨x, hx, q, hq, hxq⟩ := hn'
  refine ⟨x, hx, q * t, T.mul_mem (hQT hq) ht, ?_⟩
  have hnt' : n * t = g := hnt
  have hxq' : x * q = n := hxq
  rw [← hnt', ← hxq', mul_assoc]

theorem exists_mul_mem_normalizer_F4 (h331 : Stmt3_3_1_F4) (hyp : Hyp1223 G T L V)
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hsol : Group.IsSolvable ↥H)
    (hp : p.Prime) (hp2 : p ≠ 2) (hPp : IsPGroup p ↥P) (hPH : P ≤ H)
    (hPi : ¬ p ∣ P.relIndex H) (hP1 : P ≠ ⊥) {g : G} (hg : g ∈ H) :
    ∃ q ∈ pCoreOf 2 H, q * g ∈ Subgroup.normalizer (P : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  set N₁ := P ⊔ pCoreOf 2 H with hN₁
  have hN₁H : N₁ ≤ H := sup_le hPH (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hn : (N₁.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN₁H).mpr
      (le_normalizer_sup_F4 h331 hyp hHs hsol hp hp2 hPp hPH hPi hP1)
  set P' := P.subgroupOf H with hP'
  have hP'p : IsPGroup p ↥P' := hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  set S : Sylow p ↥H := hP'p.toSylow hPi with hS
  have hSN : (S : Subgroup ↥H) ≤ N₁.subgroupOf H := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hy))
  have hfr := Sylow.normalizer_sup_eq_top' S hSN
  have hmem : (⟨g, hg⟩ : ↥H) ∈ Subgroup.normalizer (S : Set ↥H) ⊔ N₁.subgroupOf H := by
    rw [hfr]
    exact Subgroup.mem_top _
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.normal_mul] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  have haN : (a : G) ∈ N₁ := Subgroup.mem_subgroupOf.mp ha
  have hPQ : P ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hPH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right P (pCoreOf 2 H) hPQ
  have haN' : (a : G) ∈ (P : Set G) * (pCoreOf 2 H : Set G) := by
    rw [← hset]
    exact haN
  obtain ⟨x, hx, q, hq, hxq⟩ := haN'
  have hbP : (b : G) ∈ Subgroup.normalizer (P : Set G) := by
    refine Sec121Swap.mem_normalizer_of_conj_mem fun y hy => ?_
    have h1 : (⟨y, hPH hy⟩ : ↥H) ∈ S := by
      show (⟨y, hPH hy⟩ : ↥H) ∈ P'
      exact Subgroup.mem_subgroupOf.mpr hy
    have h2 : b * ⟨y, hPH hy⟩ * b⁻¹ ∈ P' := (Subgroup.mem_normalizer_iff.mp hb _).mp h1
    have h3 : ((b * ⟨y, hPH hy⟩ * b⁻¹ : ↥H) : G) ∈ P := Subgroup.mem_subgroupOf.mp h2
    simpa using h3
  refine ⟨x * q⁻¹ * x⁻¹, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hPH hx)) q⁻¹).mp (Subgroup.inv_mem _ hq)
  · have hg' : g = (a : G) * b := by
      have := congrArg Subtype.val hab
      simpa using this.symm
    rw [hg', ← hxq]
    have e : x * q⁻¹ * x⁻¹ * (x * q * (b : G)) = x * b := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hx) hbP

end Lem22

end CFSG.Quasithin.H13
