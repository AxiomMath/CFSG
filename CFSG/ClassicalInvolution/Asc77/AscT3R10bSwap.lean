module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIITransfer
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateCfg

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section Hom

variable {G : Type} [Group G] {K K' : Subgroup G} {z : G}

theorem z2_pow_even (x : Multiplicative (ZMod 2)) (n : ℕ) (hn : Even n) : x ^ n = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h : x ^ 2 = 1 := by revert x; decide
  rw [← two_mul, pow_mul, h, one_pow]

theorem z2_pow_odd (x : Multiplicative (ZMod 2)) (n : ℕ) (hn : Odd n) : x ^ n = x := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, z2_pow_even x (2 * k) (even_two_mul k), one_mul]

theorem z2_eq_of_ne_one {x y : Multiplicative (ZMod 2)} (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  revert x y; decide

@[expose] noncomputable def swapChar (K : Subgroup G) (g : G) : Multiplicative (ZMod 2) := by
  classical exact if conjSub g K = K then 1 else Multiplicative.ofAdd 1

theorem swapChar_of_eq {g : G} (h : conjSub g K = K) : swapChar K g = 1 := by
  simp [swapChar, h]

theorem swapChar_of_ne {g : G} (h : conjSub g K ≠ K) : swapChar K g = Multiplicative.ofAdd 1 := by
  simp [swapChar, h]

theorem swapChar_eq_one_iff {g : G} : swapChar K g = 1 ↔ conjSub g K = K := by
  by_cases h : conjSub g K = K
  · simp [swapChar_of_eq h, h]
  · rw [swapChar_of_ne h]
    simp only [h, iff_false]
    decide

@[expose] noncomputable def swapHom (hne : K' ≠ K)
    (h1 : ∀ g ∈ Subgroup.centralizer ({z} : Set G), conjSub g K = K ∨ conjSub g K = K')
    (h2 : ∀ g ∈ Subgroup.centralizer ({z} : Set G), conjSub g K' = K ∨ conjSub g K' = K') :
    ↥(Subgroup.centralizer ({z} : Set G)) →* Multiplicative (ZMod 2) where
  toFun c := swapChar K (c : G)
  map_one' := by
    apply swapChar_of_eq
    exact conjSub_one K
  map_mul' x y := by
    have hxy : conjSub (((x * y : ↥(Subgroup.centralizer ({z} : Set G))) : G)) K =
        conjSub (x : G) (conjSub (y : G) K) := conjSub_mul _ _ _
    have hfix : ∀ g ∈ Subgroup.centralizer ({z} : Set G),
        conjSub g K = K → conjSub g K' = K' := by
      intro g hg hgK
      rcases h2 g hg with h | h
      · exact absurd (conjSub_injective g (h.trans hgK.symm)) hne
      · exact h
    have hsw : ∀ g ∈ Subgroup.centralizer ({z} : Set G),
        conjSub g K ≠ K → conjSub g K' = K := by
      intro g hg hgK
      rcases h2 g hg with h | h
      · exact h
      · exfalso
        apply hgK
        rcases h1 g hg with h' | h'
        · exact h'
        · exact absurd (conjSub_injective g (h.trans h'.symm)) hne
    show swapChar K (((x * y : ↥(Subgroup.centralizer ({z} : Set G))) : G)) =
      swapChar K (x : G) * swapChar K (y : G)
    by_cases hy : conjSub (y : G) K = K
    · have hxy' : conjSub (((x * y : ↥(Subgroup.centralizer ({z} : Set G))) : G)) K =
          conjSub (x : G) K := by rw [hxy, hy]
      rw [swapChar_of_eq hy, mul_one]
      by_cases hx : conjSub (x : G) K = K
      · rw [swapChar_of_eq hx, swapChar_of_eq (hxy'.trans hx)]
      · rw [swapChar_of_ne hx, swapChar_of_ne (fun h => hx (hxy'.symm.trans h))]
    · have hyK' : conjSub (y : G) K = K' := (h1 y y.2).resolve_left hy
      have hxy' : conjSub (((x * y : ↥(Subgroup.centralizer ({z} : Set G))) : G)) K =
          conjSub (x : G) K' := by rw [hxy, hyK']
      rw [swapChar_of_ne hy]
      by_cases hx : conjSub (x : G) K = K
      · rw [swapChar_of_eq hx, one_mul,
          swapChar_of_ne (fun h => hne (by rw [← hfix x x.2 hx, ← hxy', h]))]
      · rw [swapChar_of_ne hx, swapChar_of_eq (hxy'.trans (hsw x x.2 hx)), ← ofAdd_add]
        decide

theorem swapHom_eq_one_iff (hne : K' ≠ K)
    (h1 : ∀ g ∈ Subgroup.centralizer ({z} : Set G), conjSub g K = K ∨ conjSub g K = K')
    (h2 : ∀ g ∈ Subgroup.centralizer ({z} : Set G), conjSub g K' = K ∨ conjSub g K' = K')
    (c : ↥(Subgroup.centralizer ({z} : Set G))) :
    swapHom hne h1 h2 c = 1 ↔ conjSub (c : G) K = K :=
  swapChar_eq_one_iff

theorem isPGroup_zpowers_of_pow_four {c : G} (h : c ^ 4 = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers c) := by
  have hd : orderOf c ∣ 2 ^ 2 := by simpa using orderOf_dvd_of_pow_eq_one h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

end Hom

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.isSylow2In_S_centralizer (d : Std20 p f K K' J S R R' W V z t) :
    IsSylow2In (S : Subgroup G) (Subgroup.centralizer ({z} : Set G)) :=
  ⟨d.hSz, S.isPGroup', fun _ _ hV' hle => S.is_maximal' hV' hle⟩

theorem Std20.odd_index_centralizer (d : Std20 p f K K' J S R R' W V z t) :
    Odd (Subgroup.centralizer ({z} : Set G)).index := by
  have h1 := Subgroup.index_dvd_of_le d.hSz
  have h2 : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
  have h3 : ¬ 2 ∣ (Subgroup.centralizer ({z} : Set G)).index := fun h => h2 (h.trans h1)
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h3)

theorem Std20.exists_conj_into_S (d : Std20 p f K K' J S R R' W V z t) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) (hc2 : IsPGroup 2 ↥(Subgroup.zpowers c)) :
    ∃ y ∈ Subgroup.centralizer ({z} : Set G), y * c * y⁻¹ ∈ (S : Subgroup G) := by
  obtain ⟨P', hP', hcP'⟩ := IsSylow2In.exists_ge hc2 (Subgroup.zpowers_le.mpr hc)
  obtain ⟨y, hy, hyP⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hP' d.isSylow2In_S_centralizer
  refine ⟨y, hy, ?_⟩
  rw [← hyP]
  exact conj_mem_conjSub (hcP' (Subgroup.mem_zpowers c))

theorem Std20.swap_fusion [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
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
  obtain ⟨g, n, hg, hneq⟩ := exists_fusion_of_isSimpleGroup hnc d.odd_index_centralizer ϕ hbC hb2
    hϕb
  have hb4' : b ^ 4 = 1 := by
    rw [show b ^ 4 = (b * b) * (b * b) by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
    exact hb4
  set c₀ : G := g⁻¹ * b ^ n * g with hc₀
  have hc₀4 : c₀ ^ 4 = 1 := by
    have h : c₀ = (MulAut.conj g⁻¹) (b ^ n) := by simp [hc₀]
    rw [h, ← map_pow, ← pow_mul, mul_comm, pow_mul, hb4', one_pow, map_one]
  obtain ⟨y, hyC, hyS⟩ := d.exists_conj_into_S hg (isPGroup_zpowers_of_pow_four hc₀4)
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

end CFSG.ClassicalInvolution.Asc77.T3CII
