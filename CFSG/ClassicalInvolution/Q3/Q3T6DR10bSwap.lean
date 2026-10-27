module

public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20Three.isSylow2In_S_centralizer (d : Std20Three K K' J S R R' W V z t) :
    IsSylow2In (S : Subgroup G) (Subgroup.centralizer ({z} : Set G)) :=
  ⟨d.hSz, S.isPGroup', fun _ _ hV' hle => S.is_maximal' hV' hle⟩

theorem Std20Three.odd_index_centralizer (d : Std20Three K K' J S R R' W V z t) :
    Odd (Subgroup.centralizer ({z} : Set G)).index := by
  have h1 := Subgroup.index_dvd_of_le d.hSz
  have h2 : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
  have h3 : ¬ 2 ∣ (Subgroup.centralizer ({z} : Set G)).index := fun h => h2 (h.trans h1)
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h3)

theorem Std20Three.exists_conj_into_S (d : Std20Three K K' J S R R' W V z t) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) (hc2 : IsPGroup 2 ↥(Subgroup.zpowers c)) :
    ∃ y ∈ Subgroup.centralizer ({z} : Set G), y * c * y⁻¹ ∈ (S : Subgroup G) := by
  obtain ⟨P', hP', hcP'⟩ := IsSylow2In.exists_ge hc2 (Subgroup.zpowers_le.mpr hc)
  obtain ⟨y, hy, hyP⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hP' d.isSylow2In_S_centralizer
  refine ⟨y, hy, ?_⟩
  rw [← hyP]
  exact conj_mem_conjSub (hcP' (Subgroup.mem_zpowers c))

theorem Std20Three.swap_fusion [FrameSimple G] (d : Std20Three K K' J S R R' W V z t)
    (hnc : ∃ x y : G, x * y ≠ y * x) {b : G} (hb : b ∈ (S : Subgroup G))
    (hbK : conjSub b K = K') (hb4 : (b * b) * (b * b) = 1) :
    (∃ (n : ℕ) (h c : G), Odd n ∧ c ∈ (S : Subgroup G) ∧ conjSub c K = K ∧
        c = h⁻¹ * b ^ n * h) ∨
      (∃ (h c : G), c ∈ (S : Subgroup G) ∧ conjSub c K ≠ K ∧ c = h⁻¹ * (b * b) * h) := by
  classical
  have hne := d.ne
  have h1 : ∀ g ∈ Subgroup.centralizer ({z} : Set G), conjSub g K = K ∨ conjSub g K = K' :=
    fun g hg => d.late_conj_K hg
  have h2 : ∀ g ∈ Subgroup.centralizer ({z} : Set G), conjSub g K' = K ∨ conjSub g K' = K' :=
    fun g hg => d.late_conj_K' hg
  obtain ⟨ϕ, hϕ⟩ : ∃ ϕ : ↥(Subgroup.centralizer ({z} : Set G)) →* Multiplicative (ZMod 2),
      ∀ c : ↥(Subgroup.centralizer ({z} : Set G)), ϕ c = 1 ↔ conjSub (c : G) K = K :=
    ⟨swapHom hne h1 h2, swapHom_eq_one_iff hne h1 h2⟩
  have hbC : b ∈ Subgroup.centralizer ({z} : Set G) := d.hSz hb
  have hb2 : IsPGroup 2 (Subgroup.zpowers b) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hb)
  have hϕb : ϕ ⟨b, hbC⟩ ≠ 1 := by
    rw [Ne, hϕ]
    show conjSub b K ≠ K
    rw [hbK]
    exact hne
  obtain ⟨g, n, hg, hneq⟩ := CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.exists_fusion_of_noIndexTwo (FrameSimple.noIndexTwo d.branch.nonabelian) d.odd_index_centralizer ϕ hbC hb2
    hϕb
  have hb4' : b ^ 4 = 1 := by
    rw [show b ^ 4 = (b * b) * (b * b) by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
    exact hb4
  set c₀ : G := g⁻¹ * b ^ n * g with hc₀
  have hc₀4 : c₀ ^ 4 = 1 := by
    have h : c₀ = (MulAut.conj g⁻¹) (b ^ n) := by simp [hc₀]
    rw [h, ← map_pow, ← pow_mul, mul_comm, pow_mul, hb4', one_pow, map_one]
  obtain ⟨y, hyC, hyS⟩ := d.exists_conj_into_S hg (T3CII.isPGroup_zpowers_of_pow_four hc₀4)
  set c : G := y * c₀ * y⁻¹ with hc
  have hcC : c ∈ Subgroup.centralizer ({z} : Set G) := by
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ hyC hg) (Subgroup.inv_mem _ hyC)
  have hϕc : ϕ ⟨c, hcC⟩ = ϕ ⟨c₀, hg⟩ := by
    have : (⟨c, hcC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨y, hyC⟩ * ⟨c₀, hg⟩ * ⟨y, hyC⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    generalize ϕ ⟨y, hyC⟩ = a
    generalize ϕ ⟨c₀, hg⟩ = b
    revert a b
    decide
  have hcconj : ∀ w : G, y * (g⁻¹ * w * g) * y⁻¹ = (g * y⁻¹)⁻¹ * w * (g * y⁻¹) := by
    intro w
    group
  rcases Nat.even_or_odd n with hn | hn
  ·
    have hc1 : ϕ ⟨c₀, hg⟩ ≠ 1 := fun h => hneq (h.trans (z2_pow_even _ _ hn).symm)
    have hϕc1 : ϕ ⟨c, hcC⟩ ≠ 1 := by rw [hϕc]; exact hc1
    obtain ⟨m, r, hr, hnm⟩ : ∃ m r : ℕ, r < 4 ∧ n = 4 * m + r :=
      ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
    have hbn : b ^ n = b ^ r := by rw [hnm, pow_add, pow_mul, hb4', one_pow, one_mul]
    have hr2 : r = 0 ∨ r = 2 := by
      obtain ⟨k, hk⟩ := hn
      omega
    rcases hr2 with rfl | rfl
    · exfalso
      apply hc1
      have h0 : c₀ = 1 := by rw [hc₀, hbn]; group
      have h' : (⟨c₀, hg⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 := Subtype.ext h0
      rw [h', map_one]
    · right
      refine ⟨g * y⁻¹, c, hyS, fun h => hϕc1 ((hϕ ⟨c, hcC⟩).mpr h), ?_⟩
      rw [hc, hc₀, hbn, hcconj, pow_two]
  · left
    refine ⟨n, g * y⁻¹, c, hn, hyS, ?_, ?_⟩
    · have h0 : ϕ ⟨c₀, hg⟩ = 1 := by
        by_contra h
        apply hneq
        have hb' : ϕ ⟨b, hbC⟩ ^ n = ϕ ⟨b, hbC⟩ := z2_pow_odd _ _ hn
        exact (z2_eq_of_ne_one h hϕb).trans hb'.symm
      exact (hϕ ⟨c, hcC⟩).mp (hϕc.trans h0)
    · rw [hc, hc₀, hcconj]

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
