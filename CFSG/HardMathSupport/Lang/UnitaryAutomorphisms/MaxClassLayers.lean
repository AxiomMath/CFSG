module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.MaxClassFiltration
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.MaxClassIndex
public import CFSG.HardMathSupport.Lang.Proving.BlackburnCounting

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] [Finite G]

theorem lcsFil_card {M : Subgroup G} {n : ℕ} (hn : 3 ≤ n) (hcard : Nat.card G = 3 ^ n)
    (hMi : M.index = 3) {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n)
    (hL : ∀ k, 1 ≤ k → k ≤ n - 1 → Nat.card ((⊤ : Subgroup G).lowerCentralSeries k) = 3 ^ (n - 1 - k)) :
    Nat.card (lcsFil M j) = 3 ^ (n - j) := by
  by_cases h1 : j = 1
  · subst h1
    rw [lcsFil_of_le le_rfl]
    have := Subgroup.card_mul_index M
    rw [hMi, hcard] at this
    have h3 : 3 ^ n = 3 ^ (n - 1) * 3 := by rw [← pow_succ]; congr 1; omega
    rw [h3] at this
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
  · rw [lcsFil_of_gt (by omega), hL (j - 1) (by omega) (by omega)]
    congr 1; omega

omit [Finite G] in
theorem cx_eq_cmap (x w : G) : cx x w = Proving.cmap x⁻¹ w := by
  rw [Proving.cmap_eq]; simp [cx, mul_assoc]

omit [Finite G] in
theorem cx_mul (x w w' : G) : cx x (w * w') = w'⁻¹ * cx x w * w' * cx x w' := by
  simp only [cx]; group

section Layers

variable {M : Subgroup G} [M.Normal] (hM : (⊤ : Subgroup G).lowerCentralSeries 1 ≤ M) {n : ℕ}
  {x : G}

include hM

theorem layer_inj {j : ℕ} (hj : 1 ≤ j)
    (hidx : ((lcsFil M (j + 1)).subgroupOf (lcsFil M j)).index = 3)
    (hex : ∃ w ∈ lcsFil M j, cx x w ∉ lcsFil M (j + 2)) :
    ∀ y ∈ lcsFil M j, y ∉ lcsFil M (j + 1) → cx x y ∉ lcsFil M (j + 2) := by
  intro y hy hy1 hcy
  have := lcsFil_normal M (j + 2)
  set K := Proving.cSub x⁻¹ (lcsFil M j) (lcsFil M (j + 2)) with hK
  have hKA : K ≤ lcsFil M j := fun w hw => (Proving.mem_cSub.1 hw).1
  have hAK : lcsFil M (j + 1) ≤ K := by
    intro w hw
    refine Proving.mem_cSub.2 ⟨lcsFil_anti M hM (Nat.le_succ j) hw, ?_⟩
    rw [← cx_eq_cmap]
    exact lcsFil_cx_mem M x (by omega) hw
  have hyK : y ∈ K := Proving.mem_cSub.2 ⟨hy, by rw [← cx_eq_cmap]; exact hcy⟩
  have hmul := Subgroup.relIndex_mul_relIndex (lcsFil M (j + 1)) K (lcsFil M j) hAK hKA
  have h3 : (lcsFil M (j + 1)).relIndex (lcsFil M j) = 3 := hidx
  rw [h3] at hmul
  have hne1 : (lcsFil M (j + 1)).relIndex K ≠ 1 := fun h1 =>
    hy1 ((Subgroup.relIndex_eq_one.1 h1) hyK)
  have hprime : (3 : ℕ).Prime := Nat.prime_three
  have h1 : K.relIndex (lcsFil M j) = 1 := by
    rcases (Nat.dvd_prime hprime).1 (Dvd.intro _ hmul) with h | h
    · exact absurd h hne1
    · rw [h] at hmul; omega
  have hAj : lcsFil M j ≤ K := Subgroup.relIndex_eq_one.1 h1
  obtain ⟨w, hw, hw'⟩ := hex
  exact hw' (by have := (Proving.mem_cSub.1 (hAj hw)).2; rwa [← cx_eq_cmap] at this)

theorem layer_surj {j : ℕ} (hj : 1 ≤ j)
    (hidx1 : ((lcsFil M (j + 1)).subgroupOf (lcsFil M j)).index = 3)
    (hidx2 : ((lcsFil M (j + 2)).subgroupOf (lcsFil M (j + 1))).index = 3)
    (hinj : ∀ y ∈ lcsFil M j, y ∉ lcsFil M (j + 1) → cx x y ∉ lcsFil M (j + 2)) :
    ∀ z ∈ lcsFil M (j + 1), ∃ y ∈ lcsFil M j, ∃ w ∈ lcsFil M (j + 2), z = cx x y * w := by
  have hN := lcsFil_normal M (j + 2)
  let π : G →* G ⧸ lcsFil M (j + 2) := QuotientGroup.mk' (lcsFil M (j + 2))
  have key : ∀ c b : G, c ∈ lcsFil M (j + 1) → b ∈ lcsFil M j → π (b⁻¹ * c * b) = π c := by
    intro c b hc hb
    have h1 : ⁅c, b⁆ ∈ lcsFil M (j + 2) := by
      have := lcsFil_comm M (by omega : 1 ≤ j + 1) hj hc hb
      exact lcsFil_anti M hM (by omega : j + 2 ≤ j + 1 + j) this
    have h2 : π ⁅c, b⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    rw [map_mul, map_mul, map_inv]
    calc (π b)⁻¹ * π c * π b = (π b)⁻¹ * (π b * π c) := by rw [← h2, mul_assoc]
      _ = π c := by group
  let ψ : lcsFil M j →* G ⧸ lcsFil M (j + 2) :=
    { toFun := fun w => π (cx x (w : G))
      map_one' := by simp [cx]
      map_mul' := fun a b => by
        have hc : cx x (a : G) ∈ lcsFil M (j + 1) := lcsFil_cx_mem M x hj a.2
        have : cx x ((a * b : lcsFil M j) : G) = (b : G)⁻¹ * cx x (a : G) * (b : G) * cx x (b : G) :=
          cx_mul x a b
        simp only [this, map_mul, key _ _ hc b.2] }
  have hψ : ∀ w : lcsFil M j, ψ w = π (cx x (w : G)) := fun w => rfl
  have hker : ψ.ker = (lcsFil M (j + 1)).subgroupOf (lcsFil M j) := by
    ext w
    rw [MonoidHom.mem_ker, hψ, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : cx x (w : G) ∈ lcsFil M (j + 2) := (QuotientGroup.eq_one_iff _).1 h
      by_contra hw
      exact hinj w w.2 hw h'
    · intro h
      exact (QuotientGroup.eq_one_iff _).2 (lcsFil_cx_mem M x (by omega) h)
  set T : Subgroup (G ⧸ lcsFil M (j + 2)) := (lcsFil M (j + 1)).map π with hT
  have hrange : ψ.range ≤ T := by
    rintro _ ⟨w, rfl⟩
    exact ⟨cx x (w : G), lcsFil_cx_mem M x hj w.2, rfl⟩
  have hcardψ : Nat.card ψ.range = 3 := by
    rw [← Subgroup.index_ker, hker, hidx1]
  have hcardT : Nat.card T = 3 := by
    rw [hT, Proving.card_map_mk'_eq_index, hidx2]
  have hEq : ψ.range = T :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hcardψ, hcardT])
  intro z hz
  have hzT : π z ∈ T := ⟨z, hz, rfl⟩
  rw [← hEq] at hzT
  obtain ⟨w, hw⟩ := hzT
  refine ⟨w, w.2, (cx x (w : G))⁻¹ * z, ?_, by group⟩
  have : π (cx x (w : G)) = π z := hw
  rw [← QuotientGroup.eq]
  exact this

end Layers

section Counting

variable [Fact (Nat.Prime 3)]

theorem exists_cx_not_mem (hG : IsPGroup 3 G) {n : ℕ} (hn : 3 ≤ n) (hcard : Nat.card G = 3 ^ n)
    (hne : (⊤ : Subgroup G).lowerCentralSeries (n - 2) ≠ ⊥) {x : G}
    (hCx : Nat.card (Subgroup.centralizer ({x} : Set G)) = 9)
    {M : Subgroup G} [M.Normal] (hM : (⊤ : Subgroup G).lowerCentralSeries 1 ≤ M)
    (hMi : M.index = 3) (hxM : x ∉ M) {j : ℕ} (hj : 1 ≤ j) (hjn : j + 2 ≤ n) :
    ∃ w ∈ lcsFil M j, cx x w ∉ lcsFil M (j + 2) := by
  by_contra hall
  push Not at hall
  have hnc := two_dvd_index_lcs_one hG hn hcard hne
  have hL : ∀ k, 1 ≤ k → k ≤ n - 1 →
      Nat.card ((⊤ : Subgroup G).lowerCentralSeries k) = 3 ^ (n - 1 - k) :=
    fun k hk1 hk => card_lcs_eq hG hcard hne hnc hk1 hk
  have hbot := lcs_eq_bot hG hn hcard hne
  have hAj : Nat.card (lcsFil M j) = 3 ^ (n - j) := lcsFil_card hn hcard hMi hj (by omega) hL
  have hjM : lcsFil M j ≤ M := by
    have := lcsFil_anti M hM (by omega : 1 ≤ j)
    rwa [lcsFil_of_le le_rfl] at this
  have key := Proving.card_le_pow_mul_centralizer_of_index x⁻¹ (lcsFil M j) (j + 1) (n - 1)
    (by omega) hbot
    (fun l hl1 hl2 => le_of_eq (relIndex_lcs_eq hG hcard hne hnc (by omega) (by omega)))
    (fun y hy => by
      rw [← cx_eq_cmap]
      have := hall y hy
      rwa [lcsFil_of_gt (by omega : 2 ≤ j + 2), show j + 2 - 1 = j + 1 by omega] at this)
  rw [hAj] at key
  have h9 : 9 ≤ Nat.card (Proving.cSub x⁻¹ (lcsFil M j) ⊥) := by
    have e : 3 ^ (n - j) = 3 ^ (n - 1 - (j + 1)) * 9 := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    rw [e] at key
    exact Nat.le_of_mul_le_mul_left key (pow_pos (by norm_num) _)
  have hle : Proving.cSub x⁻¹ (lcsFil M j) ⊥ ≤ M ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    obtain ⟨hyH, hyc⟩ := Proving.mem_cSub_bot.1 hy
    refine Subgroup.mem_inf.2 ⟨hjM hyH, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : x * y = y * x := by
      have h1 : x⁻¹ * y = y * x⁻¹ := hyc
      calc x * y = x * (y * x⁻¹) * x := by group
        _ = x * (x⁻¹ * y) * x := by rw [h1]
        _ = y * x := by group
    exact this.symm
  have hge : 9 ≤ Nat.card (M ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) :=
    h9.trans (Subgroup.card_le_of_le hle)
  have hrel : M.relIndex (Subgroup.centralizer ({x} : Set G)) = 3 := by
    have hd := Subgroup.relIndex_dvd_index_of_normal (H := M) (K := Subgroup.centralizer ({x} : Set G))
    rw [hMi] at hd
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exfalso
      exact hxM ((Subgroup.relIndex_eq_one.1 h) (Subgroup.mem_centralizer_singleton_iff.2 rfl))
    · exact h
  have hmul := Subgroup.relIndex_mul_card (H := M) (K := Subgroup.centralizer ({x} : Set G))
  rw [hrel, hCx] at hmul
  omega

end Counting

theorem lcs_one_le_of_index_prime {M : Subgroup G} [M.Normal] (hMi : M.index = 3) :
    (⊤ : Subgroup G).lowerCentralSeries 1 ≤ M := by
  have hcard : Nat.card (G ⧸ M) = 3 := hMi
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic (G ⧸ M) := isCyclic_of_prime_card hcard
  let _ : CommGroup (G ⧸ M) := IsCyclic.commGroup
  rw [Subgroup.top_lowerCentralSeries_one]
  show ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ M
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [← QuotientGroup.eq_one_iff (N := M)]
  change (QuotientGroup.mk' M) ⁅a, b⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem cubeSetup_of_maxClass [Fact (Nat.Prime 3)] (hG : IsPGroup 3 G) {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card G = 3 ^ n) (hne : (⊤ : Subgroup G).lowerCentralSeries (n - 2) ≠ ⊥)
    {x : G} (hx3 : x ^ 3 = 1) (hCx : Nat.card (Subgroup.centralizer ({x} : Set G)) = 9)
    {M : Subgroup G} [M.Normal] (hMi : M.index = 3) (hxM : x ∉ M) :
    CubeSetup x (lcsFil M) n := by
  have hM := lcs_one_le_of_index_prime hMi
  have hnc := two_dvd_index_lcs_one hG hn hcard hne
  have hL : ∀ k, 1 ≤ k → k ≤ n - 1 →
      Nat.card ((⊤ : Subgroup G).lowerCentralSeries k) = 3 ^ (n - 1 - k) :=
    fun k hk1 hk => card_lcs_eq hG hcard hne hnc hk1 hk
  have hbot := lcs_eq_bot hG hn hcard hne
  have hidx : ∀ j, 1 ≤ j → j + 1 ≤ n →
      ((lcsFil M (j + 1)).subgroupOf (lcsFil M j)).index = 3 := by
    intro j hj hjn
    have hle : lcsFil M (j + 1) ≤ lcsFil M j := lcsFil_anti M hM (Nat.le_succ j)
    have hmul := Subgroup.relIndex_mul_card (H := lcsFil M (j + 1)) (K := lcsFil M j)
    rw [inf_of_le_left hle, lcsFil_card hn hcard hMi hj (by omega) hL,
      lcsFil_card hn hcard hMi (by omega) hjn hL] at hmul
    have h3 : 3 ^ (n - j) = 3 * 3 ^ (n - (j + 1)) := by
      rw [← pow_succ']; congr 1; omega
    rw [h3] at hmul
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) _) hmul
  have hex := fun j (hj : 1 ≤ j) (hjn : j + 2 ≤ n) =>
    exists_cx_not_mem hG hn hcard hne hCx hM hMi hxM hj hjn
  have hinj := fun j (hj : 1 ≤ j) (hjn : j + 2 ≤ n) =>
    layer_inj hM hj (hidx j hj (by omega)) (hex j hj hjn)
  exact CubeSetup.of_lcs M hM (by omega) hbot hx3
    (fun j hj hjn => layer_surj hM hj (hidx j hj (by omega)) (hidx (j + 1) (by omega) (by omega))
      (hinj j hj hjn))
    hinj

section LForm

variable [Fact (Nat.Prime 3)] (hG : IsPGroup 3 G) {n : ℕ} (hn : 3 ≤ n)
  (hcard : Nat.card G = 3 ^ n) (hne : (⊤ : Subgroup G).lowerCentralSeries (n - 2) ≠ ⊥)
  {x : G} (hx3 : x ^ 3 = 1) (hCx : Nat.card (Subgroup.centralizer ({x} : Set G)) = 9)
  {M : Subgroup G} [M.Normal] (hMi : M.index = 3) (hxM : x ∉ M)

include hG hn hcard hne hx3 hCx hMi hxM

theorem lcs_pow_three_eq_one_mem (hn4 : 4 ≤ n) {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (hz3 : z ^ 3 = 1) : z ∈ (⊤ : Subgroup G).lowerCentralSeries (n - 3) := by
  have S := cubeSetup_of_maxClass hG hn hcard hne hx3 hCx hMi hxM
  have := S.pow_three_eq_one_mem (z := z) (by rwa [lcsFil_of_gt (by omega)]) hz3
  rwa [lcsFil_of_gt (by omega), show n - 2 - 1 = n - 3 by omega] at this

end LForm

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
