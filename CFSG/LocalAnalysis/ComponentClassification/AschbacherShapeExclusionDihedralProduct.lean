module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherShapeExclusionCaseOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherShapeExclusionDihedral

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion

open Subgroup

variable {G : Type} [Group G]

namespace Setting

variable {A : Subgroup G} {S₀ : Sylow 2 A} {t x ρ : G} {k : ℕ}

theorem mem_of_bar_mem [Finite G] (hs : Setting A S₀ t x ρ k) {g : G} (hgA : g ∈ A)
    (hg2 : ∃ m : ℕ, g ^ 2 ^ m = 1)
    (hgT : bar A g ∈ (sylowBar S₀ : Subgroup (A ⧸ center A))) :
    g ∈ (S₀ : Subgroup A).map A.subtype := by
  have hSA := hs.S_le_A
  obtain ⟨s, hsS, hsg⟩ := (mem_sylowBar_iff S₀).1 hgT
  have hc := (bar_eq_bar_iff (hSA hsS) hgA).1 hsg
  set c := s⁻¹ * g with hcdef
  have hcA : c ∈ A := mul_mem (inv_mem (hSA hsS)) hgA
  have hgsc : g = s * c := by rw [hcdef]; group
  have hcs : Commute s c := mem_centralizer_iff.1 hc s (hSA hsS)
  obtain ⟨m, hm⟩ := hg2
  have hcm : c ^ 2 ^ m ∈ (S₀ : Subgroup A).map A.subtype := by
    have : c ^ 2 ^ m = (s ^ 2 ^ m)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hcs.symm.mul_pow, hcs.symm.eq, ← hgsc, hm]
    rw [this]
    exact inv_mem (pow_mem hsS _)
  have hS2 : IsPGroup 2 ((S₀ : Subgroup A).map A.subtype) := S₀.isPGroup'.map _
  obtain ⟨m', hm'⟩ := hS2 ⟨_, hcm⟩
  have hc2 : c ^ 2 ^ (m + m') = 1 := by
    rw [pow_add, pow_mul]
    simpa using congrArg Subtype.val hm'
  set c' : A := ⟨c, hcA⟩ with hc'
  have hc'p : IsPGroup 2 (zpowers c') := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    have hdvd : orderOf c' ∣ 2 ^ (m + m') := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext (by simpa using hc2)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨j, hj⟩
  have hc'n : (zpowers c').Normal := by
    refine ⟨fun w hw b => ?_⟩
    have hcomm : b * w = w * b := by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
      exact (Commute.zpow_right (Subtype.ext (mem_centralizer_iff.1 hc b b.2)) j).eq
    rw [hcomm, mul_inv_cancel_right]
    exact hw
  have hc'S := hc'p.le_sylow_of_normal S₀ (mem_zpowers c')
  rw [hgsc]
  exact mul_mem hsS ⟨c', hc'S, rfl⟩

theorem central_mem_zpowers_rho [Finite G] (hs : Setting A S₀ t x ρ k) {g : G}
    (hgS : g ∈ (S₀ : Subgroup A).map A.subtype) (hgc : g ∈ centralizer (A : Set G)) :
    g ∈ zpowers ρ := by
  have hW := Config.central_le_zpowers_x_sq hs.quasi S₀ hs.config (mem_inf.2 ⟨hgS, hgc⟩)
  exact (zpowers_le.2 hs.config.x_sq_mem) hW

theorem data_bar [Finite G] (hs : Setting A S₀ t x ρ k) {u : G}
    (huS : u ∈ (S₀ : Subgroup A).map A.subtype) (huM : u ∉ zpowers ρ ⊔ zpowers x)
    (hu2 : u ^ 2 = 1) (hur : u * ρ * u⁻¹ = ρ⁻¹) (hue : u * hs.config.e * u⁻¹ = hs.config.e)
    {n : ℕ} (hn : 2 ≤ n) (hro : orderOf (bar A ρ) = 2 ^ n) :
    DihedralTimesTwo.Data (sylowBar S₀ : Subgroup (A ⧸ center A)) (bar A ρ) (bar A u)
      (bar A hs.config.e) n := by
  have h := hs.config
  have hSA := hs.S_le_A
  have hρA := hSA h.rho_mem
  have huA := hSA huS
  have heA := hSA h.e_mem
  have heu : h.e * u = u * h.e := by
    calc h.e * u = u * h.e * u⁻¹ * u := by rw [hue]
      _ = u * h.e := by group
  refine ⟨hn, bar_mem_sylowBar S₀ h.rho_mem, bar_mem_sylowBar S₀ huS,
    bar_mem_sylowBar S₀ h.e_mem, hro, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← bar_pow huA, hu2, bar_one]
  · rw [← bar_pow heA, h.e_sq, bar_one]
  · rw [← bar_mul huA hρA, ← bar_inv huA, ← bar_mul (mul_mem huA hρA) (inv_mem huA), hur,
      bar_inv hρA]
  · have := h.e_comm_zpow 1
    rw [zpow_one] at this
    rw [← bar_mul heA hρA, ← bar_mul hρA heA, this]
  · rw [← bar_mul heA huA, ← bar_mul huA heA, heu]
  · intro q hq
    obtain ⟨g, hgS, rfl⟩ := (mem_sylowBar_iff S₀).1 hq
    obtain ⟨i, hi | hi | hi | hi⟩ := h.S_cases huS huM hgS <;> refine ⟨i, ?_⟩ <;> rw [hi]
    · exact Or.inl (bar_zpow hρA i)
    · exact Or.inr (Or.inl (by rw [bar_mul (zpow_mem hρA i) heA, bar_zpow hρA]))
    · exact Or.inr (Or.inr (Or.inl (by rw [bar_mul huA (zpow_mem hρA i), bar_zpow hρA])))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [bar_mul (mul_mem huA (zpow_mem hρA i)) heA, bar_mul huA (zpow_mem hρA i), bar_zpow hρA]
  · intro i
    constructor
    · intro he
      rw [← bar_zpow hρA, bar_eq_bar_iff heA (zpow_mem hρA i)] at he
      have hmem := hs.central_mem_zpowers_rho (mul_mem (inv_mem h.e_mem) (zpow_mem h.rho_mem i))
        he
      apply h.e_not_mem
      have : h.e = ρ ^ i * (h.e⁻¹ * ρ ^ i)⁻¹ := by group
      rw [this]
      exact mul_mem (zpow_mem (mem_zpowers ρ) i) (inv_mem hmem)
    · intro he
      rw [← bar_zpow hρA, ← bar_mul huA (zpow_mem hρA i),
        bar_eq_bar_iff heA (mul_mem huA (zpow_mem hρA i))] at he
      have hmem := hs.central_mem_zpowers_rho
        (mul_mem (inv_mem h.e_mem) (mul_mem huS (zpow_mem h.rho_mem i))) he
      apply huM
      have : u = h.e * (h.e⁻¹ * (u * ρ ^ i)) * ρ ^ (-i) := by group
      rw [this]
      exact mul_mem (mul_mem h.e_mem_M (mem_sup_left hmem))
        (mem_sup_left (zpow_mem (mem_zpowers ρ) _))

theorem e_central_IIa [Finite G] (hs : Setting A S₀ t x ρ k) {u : G}
    (huS : u ∈ (S₀ : Subgroup A).map A.subtype) (huM : u ∉ zpowers ρ ⊔ zpowers x)
    (hue : u * hs.config.e * u⁻¹ = hs.config.e) {s : G}
    (hsS : s ∈ (S₀ : Subgroup A).map A.subtype) : hs.config.e * s = s * hs.config.e := by
  have h := hs.config
  by_cases hsM : s ∈ zpowers ρ ⊔ zpowers x
  · exact h.M_comm h.e_mem_M hsM
  · have hm := h.M_index_two.2.1 u huS s hsS huM hsM
    have heu : h.e * u = u * h.e := by
      calc h.e * u = u * h.e * u⁻¹ * u := by rw [hue]
        _ = u * h.e := by group
    have hem : h.e * (u⁻¹ * s) = (u⁻¹ * s) * h.e := h.M_comm h.e_mem_M hm
    calc h.e * s = (h.e * u) * (u⁻¹ * s) := by group
      _ = u * (h.e * (u⁻¹ * s)) := by rw [heu]; group
      _ = s * h.e := by rw [hem]; group

theorem central_involution_IIa [Finite G] (hs : Setting A S₀ t x ρ k) {u : G}
    (huS : u ∈ (S₀ : Subgroup A).map A.subtype) (huM : u ∉ zpowers ρ ⊔ zpowers x)
    (hur : u * ρ * u⁻¹ = ρ⁻¹) (hue : u * hs.config.e * u⁻¹ = hs.config.e) {w : G}
    (hwS : w ∈ (S₀ : Subgroup A).map A.subtype)
    (hwc : ∀ s ∈ (S₀ : Subgroup A).map A.subtype, s * w = w * s) (hw2 : w ^ 2 = 1) :
    w = 1 ∨ w = x ^ 2 ∨ w = hs.config.e ∨ w = x ^ 2 * hs.config.e := by
  have h := hs.config
  have hconj : ∀ i : ℤ, u * ρ ^ i * u⁻¹ = ρ ^ (-i) := fun i => by
    rw [← _root_.conj_zpow, hur, inv_zpow']
  have hρu : ρ * u = u * ρ⁻¹ := by
    calc ρ * u = u * (u⁻¹ * ρ * u) := by group
      _ = u * ρ⁻¹ := by
          congr 1
          have := hconj (-1)
          rw [zpow_neg_one, neg_neg, zpow_one] at this
          calc u⁻¹ * ρ * u = u⁻¹ * (u * ρ⁻¹ * u⁻¹) * u := by rw [this]
            _ = ρ⁻¹ := by group
  have hρ2 : ρ ^ 2 ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [h.rho_order] at this
    have := Nat.le_of_dvd (by norm_num) this
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h.hk
    omega
  have hinvρ : ∀ i : ℤ, u * ρ ^ i = ρ ^ i * u → (ρ ^ i) ^ 2 = 1 := by
    intro i hi
    have h1 : ρ ^ (-i) = ρ ^ i := by rw [← hconj, hi, mul_inv_cancel_right]
    rw [pow_two]
    nth_rewrite 1 [← h1]
    rw [← zpow_add, neg_add_cancel, zpow_zero]
  have hnot : ∀ i : ℤ, ρ * (u * ρ ^ i) ≠ u * ρ ^ i * ρ := by
    intro i h1
    apply hρ2
    have h2 : u * ρ ^ (i - 1) = u * ρ ^ (i + 1) := by
      calc u * ρ ^ (i - 1) = ρ * u * ρ ^ i := by
            rw [hρu, mul_assoc, ← zpow_neg_one, ← zpow_add]
            ring_nf
        _ = u * ρ ^ i * ρ := by rw [mul_assoc, h1]
        _ = u * ρ ^ (i + 1) := by rw [mul_assoc, ← zpow_add_one]
    have h3 := mul_left_cancel h2
    calc ρ ^ 2 = ρ ^ (i + 1) * (ρ ^ (i - 1))⁻¹ := by
          rw [← zpow_neg, ← zpow_add, show i + 1 + -(i - 1) = 2 by ring]; norm_cast
      _ = 1 := by rw [← h3, mul_inv_cancel]
  obtain ⟨i, hi | hi | hi | hi⟩ := h.S_cases huS huM hwS <;> subst hi
  · rcases h.rho_zpow_sq (hinvρ i (hwc u huS)) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · have hcomm : u * ρ ^ i = ρ ^ i * u := by
      have h1 := hwc u huS
      have h2 : u * (ρ ^ i * h.e) * u⁻¹ = ρ ^ (-i) * h.e := by
        calc u * (ρ ^ i * h.e) * u⁻¹ = (u * ρ ^ i * u⁻¹) * (u * h.e * u⁻¹) := by group
          _ = ρ ^ (-i) * h.e := by rw [hconj, hue]
      rw [h1, mul_inv_cancel_right] at h2
      have h3 : ρ ^ (-i) = ρ ^ i := (mul_right_cancel h2).symm
      calc u * ρ ^ i = (u * ρ ^ i * u⁻¹) * u := by group
        _ = ρ ^ i * u := by rw [hconj, h3]
    rcases h.rho_zpow_sq (hinvρ i hcomm) with h1 | h1 <;> rw [h1]
    · exact Or.inr (Or.inr (Or.inl (one_mul _)))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · exact absurd (hwc ρ h.rho_mem) (hnot i)
  · exfalso
    apply hnot i
    have h1 := hwc ρ h.rho_mem
    have hec := (hs.e_central_IIa huS huM hue h.rho_mem)
    calc ρ * (u * ρ ^ i) = ρ * (u * ρ ^ i * h.e) * h.e⁻¹ := by group
      _ = u * ρ ^ i * h.e * ρ * h.e⁻¹ := by rw [h1]
      _ = u * ρ ^ i * ρ := by rw [mul_assoc (u * ρ ^ i), hec]; group

theorem false_of_caseIIa_E8 [Finite G] (hs : Setting A S₀ t x ρ k) {u : G}
    (huS : u ∈ (S₀ : Subgroup A).map A.subtype) (huM : u ∉ zpowers ρ ⊔ zpowers x)
    (hur : u * ρ * u⁻¹ = ρ⁻¹) (hue : u * hs.config.e * u⁻¹ = hs.config.e)
    (hz : x ^ 2 ∈ centralizer (A : Set G)) (hk2 : k = 2) : False := by
  have h := hs.config
  have : IsSimpleGroup (A ⧸ center A) := hs.quasi.2
  have hnonab := nonabelian_bar hs.quasi
  have hSA := hs.S_le_A
  have hρA := hSA h.rho_mem
  have huA := hSA huS
  have heA := hSA h.e_mem
  have hx2S : x ^ 2 ∈ (S₀ : Subgroup A).map A.subtype := pow_mem h.x_mem 2
  have hz1 : bar A (x ^ 2) = 1 := (bar_eq_one_iff (hSA hx2S)).2 hz
  have hρ2 : bar A ρ ^ 2 = 1 := by
    have hρx : ρ ^ 2 = x ^ 2 := by
      have := h.rho_pow
      rw [hk2] at this
      simpa using this
    rw [← bar_pow hρA, hρx, hz1]
  have hru : bar A ρ * bar A u = bar A u * bar A ρ := by
    have hinv : (bar A ρ)⁻¹ = bar A ρ := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hρ2]
    have h1 : bar A u * bar A ρ * (bar A u)⁻¹ = bar A ρ := by
      rw [← bar_mul huA hρA, ← bar_inv huA, ← bar_mul (mul_mem huA hρA) (inv_mem huA), hur,
        bar_inv hρA, hinv]
    calc bar A ρ * bar A u = (bar A u * bar A ρ * (bar A u)⁻¹) * bar A u := by rw [h1]
      _ = bar A u * bar A ρ := by group
  have hre : bar A ρ * bar A h.e = bar A h.e * bar A ρ := by
    have := h.e_comm_zpow 1
    rw [zpow_one] at this
    rw [← bar_mul hρA heA, ← bar_mul heA hρA, this]
  have hue' : bar A u * bar A h.e = bar A h.e * bar A u := by
    rw [← bar_mul huA heA, ← bar_mul heA huA, hs.e_central_IIa huS huM hue huS]
  have hcent : ∀ c : A ⧸ center A, Commute c (bar A ρ) → Commute c (bar A u) →
      Commute c (bar A h.e) →
      c ∈ centralizer ((sylowBar S₀ : Subgroup (A ⧸ center A)) : Set (A ⧸ center A)) := by
    intro c hc1 hc2 hc3
    rw [mem_centralizer_iff]
    intro q hq
    obtain ⟨g, hgS, rfl⟩ := (mem_sylowBar_iff S₀).1 hq
    obtain ⟨i, hi | hi | hi | hi⟩ := h.S_cases huS huM hgS <;> subst hi
    · rw [bar_zpow hρA]
      exact (hc1.symm.zpow_left i).eq
    · rw [bar_mul (zpow_mem hρA i) heA, bar_zpow hρA]
      exact ((hc1.symm.zpow_left i).mul_left hc3.symm).eq
    · rw [bar_mul huA (zpow_mem hρA i), bar_zpow hρA]
      exact (hc2.symm.mul_left (hc1.symm.zpow_left i)).eq
    · rw [bar_mul (mul_mem huA (zpow_mem hρA i)) heA, bar_mul huA (zpow_mem hρA i),
        bar_zpow hρA]
      exact ((hc2.symm.mul_left (hc1.symm.zpow_left i)).mul_left hc3.symm).eq
  have hρc := hcent _ (Commute.refl _) hru hre
  have huc := hcent _ hru.symm (Commute.refl _) hue'
  have hec := hcent _ hre.symm hue'.symm (Commute.refl _)
  have hT : IsMulCommutative (sylowBar S₀ : Subgroup (A ⧸ center A)) := by
    rw [← le_centralizer_iff_isMulCommutative]
    intro q hq
    obtain ⟨g, hgS, rfl⟩ := (mem_sylowBar_iff S₀).1 hq
    obtain ⟨i, hi | hi | hi | hi⟩ := h.S_cases huS huM hgS <;> subst hi
    · rw [bar_zpow hρA]
      exact zpow_mem hρc i
    · rw [bar_mul (zpow_mem hρA i) heA, bar_zpow hρA]
      exact mul_mem (zpow_mem hρc i) hec
    · rw [bar_mul huA (zpow_mem hρA i), bar_zpow hρA]
      exact mul_mem huc (zpow_mem hρc i)
    · rw [bar_mul (mul_mem huA (zpow_mem hρA i)) heA, bar_mul huA (zpow_mem hρA i),
        bar_zpow hρA]
      exact mul_mem (mul_mem huc (zpow_mem hρc i)) hec
  have he1 : bar A h.e ≠ 1 := fun h1 =>
    h.e_not_mem (hs.central_mem_zpowers_rho h.e_mem ((bar_eq_one_iff heA).1 h1))
  refine false_of_abelian_sylow_fixed (DihedralTimesTwo.commutator_eq_top_of_simple hnonab)
    (sylowBar S₀) hT (bar_mem_sylowBar S₀ h.e_mem) he1 fun nbar hn => ?_
  obtain ⟨n, hnA, rfl⟩ := bar_surjective nbar
  have hS2 : IsPGroup 2 ((S₀ : Subgroup A).map A.subtype) := S₀.isPGroup'.map _
  have hconjS : ∀ m : A ⧸ center A,
      m ∈ normalizer ((sylowBar S₀ : Subgroup (A ⧸ center A)) : Set (A ⧸ center A)) →
      ∀ g ∈ A, bar A g = m → ∀ s ∈ (S₀ : Subgroup A).map A.subtype,
        g * s * g⁻¹ ∈ (S₀ : Subgroup A).map A.subtype := by
    intro m hm g hgA hgm s hsS
    apply hs.mem_of_bar_mem (mul_mem (mul_mem hgA (hSA hsS)) (inv_mem hgA))
    · obtain ⟨j, hj⟩ := hS2 ⟨s, hsS⟩
      refine ⟨j, ?_⟩
      rw [conj_pow, show s ^ 2 ^ j = 1 by simpa using congrArg Subtype.val hj, mul_one,
        mul_inv_cancel]
    · rw [bar_mul (mul_mem hgA (hSA hsS)) (inv_mem hgA), bar_mul hgA (hSA hsS), bar_inv hgA,
        hgm]
      exact (mem_normalizer_iff.1 hm _).1 (bar_mem_sylowBar S₀ hsS)
  have h1 := hconjS _ hn n hnA rfl
  have h2 := hconjS _ (inv_mem hn) n⁻¹ (inv_mem hnA) (bar_inv hnA)
  set w := n * h.e * n⁻¹ with hw
  have hwS : w ∈ (S₀ : Subgroup A).map A.subtype := h1 _ h.e_mem
  have hwc : ∀ s ∈ (S₀ : Subgroup A).map A.subtype, s * w = w * s := by
    intro s hsS
    have hs' := h2 s hsS
    rw [inv_inv] at hs'
    have hes := hs.e_central_IIa huS huM hue hs'
    calc s * w = n * ((n⁻¹ * s * n) * h.e) * n⁻¹ := by rw [hw]; group
      _ = n * (h.e * (n⁻¹ * s * n)) * n⁻¹ := by rw [hes]
      _ = w * s := by rw [hw]; group
  have hw2 : w ^ 2 = 1 := by rw [hw, conj_pow, h.e_sq]; group
  have hbarw : bar A n * bar A h.e * (bar A n)⁻¹ = bar A w := by
    rw [hw, bar_mul (mul_mem hnA heA) (inv_mem hnA), bar_mul hnA heA, bar_inv hnA]
  rw [hbarw]
  rcases hs.central_involution_IIa huS huM hur hue hwS hwc hw2 with h3 | h3 | h3 | h3
  · exfalso
    apply he1
    have : h.e = n⁻¹ * w * n := by rw [hw]; group
    rw [this, h3, mul_one, inv_mul_cancel, bar_one]
  · exfalso
    apply h.e_not_mem
    have : h.e = n⁻¹ * w * n := by rw [hw]; group
    rw [this, h3, mem_centralizer_iff.1 hz n⁻¹ (inv_mem hnA), inv_mul_cancel_right]
    exact h.x_sq_mem
  · rw [h3]
  · rw [h3, bar_mul (hSA hx2S) heA, hz1, one_mul]

theorem false_of_caseIIa [Finite G] (hs : Setting A S₀ t x ρ k) {u : G}
    (huS : u ∈ (S₀ : Subgroup A).map A.subtype) (huM : u ∉ zpowers ρ ⊔ zpowers x)
    (hu2 : u ^ 2 = 1) (hux : u * x * u⁻¹ = x⁻¹) : False := by
  have h := hs.config
  have : IsSimpleGroup (A ⧸ center A) := hs.quasi.2
  have hnonab := nonabelian_bar hs.quasi
  have hSA := hs.S_le_A
  have hρA := hSA h.rho_mem
  have huA := hSA huS
  have heA := hSA h.e_mem
  have hx2A := hSA (pow_mem h.x_mem 2)
  obtain ⟨hur, a, ha, htu⟩ := h.involution_outside huS huM hu2
  have hue := h.u_e_of_inv hur hux
  have hαr : conjBar hs.t_norm (bar A ρ) = (bar A ρ)⁻¹ := by
    rw [conjBar_bar hs.t_norm hρA, h.t_rho, bar_inv hρA]
  have hαu : conjBar hs.t_norm (bar A u) = bar A u * bar A ρ ^ a := by
    rw [conjBar_bar hs.t_norm huA, htu, bar_mul huA (zpow_mem hρA a), bar_zpow hρA]
  have hαe : conjBar hs.t_norm (bar A h.e) = bar A (x ^ 2) * bar A h.e := by
    rw [conjBar_bar hs.t_norm heA, h.t_e, bar_mul hx2A heA]
  rcases hs.central_trivial_or with hz | htriv
  · have hz1 : bar A (x ^ 2) = 1 := (bar_eq_one_iff hx2A).2 hz
    rcases (show k = 2 ∨ 3 ≤ k by have := h.hk; omega) with hk2 | hk3
    · exact hs.false_of_caseIIa_E8 huS huM hur hue hz hk2
    ·
      have hro : orderOf (bar A ρ) = 2 ^ (k - 1) := by
        have hy1 : ¬ bar A ρ ^ 2 ^ (k - 2) = 1 := by
          intro h1
          rw [← bar_pow hρA] at h1
          change bar A h.y = 1 at h1
          rw [bar_eq_one_iff (hSA (zpowers_le.2 h.rho_mem h.y_mem))] at h1
          have hW := Config.central_le_zpowers_x_sq hs.quasi S₀ h
            (mem_inf.2 ⟨zpowers_le.2 h.rho_mem h.y_mem, h1⟩)
          apply h.x_sq_ne_one
          rcases mem_zpowers_of_sq_eq_one hs.x_sq_sq hW with h2 | h2
          · rw [← h.y_sq, h2, one_pow]
          · rw [← h.y_sq, h2, hs.x_sq_sq]
        have hfin : bar A ρ ^ 2 ^ (k - 2 + 1) = 1 := by
          rw [show k - 2 + 1 = k - 1 by omega, ← bar_pow hρA, h.rho_pow, hz1]
        rw [orderOf_eq_prime_pow hy1 hfin, show k - 2 + 1 = k - 1 by omega]
      have hd := hs.data_bar huS huM hu2 hur hue (n := k - 1) (by omega) hro
      exact DihedralTimesTwo.false_of_dihedral_times_two hnonab (sylowBar S₀) hd
        (conjBar hs.t_norm) hαr ha hαu (Or.inl (by rw [hαe, hz1, one_mul]))
  · have hro : orderOf (bar A ρ) = 2 ^ k := by
      rw [orderOf_bar_of_trivial S₀ htriv h.rho_mem, h.rho_order]
    have hd := hs.data_bar huS huM hu2 hur hue h.hk hro
    refine DihedralTimesTwo.false_of_dihedral_times_two hnonab (sylowBar S₀) hd
      (conjBar hs.t_norm) hαr ha hαu (Or.inr ?_)
    rw [hαe, DihedralTimesTwo.Data.z_def, ← bar_zpow hρA, h.rho_pow_z]

end Setting

end CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion
