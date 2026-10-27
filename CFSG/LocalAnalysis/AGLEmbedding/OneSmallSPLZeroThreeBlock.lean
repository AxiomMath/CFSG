module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeSection
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeMoved
import CFSG.LocalAnalysis.AGLEmbedding.Sp48Gen

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem D1PhaseThree.le_normalizer_barM_of_perfect_of_rank {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} (h : D1PhaseThree p P M H R) (hr : CFSG.Open.pRank 3 (H ⊓ M) ≤ 3)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hDK : D ≤ barM M (H ⊓ M)) (hD : ⁅D, D⁆ = D) :
    D ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  refine le_normalizer_of_perfect_of_orbit hD fun g hg hinj => ?_
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hlift : ∀ j, ∃ k : G, k ∈ H ⊓ M ∧ ∃ hkM : k ∈ M, mk ⟨k, hkM⟩ = g j := by
    intro j
    obtain ⟨m, hm, hmg⟩ := hDK (hg j)
    exact ⟨m, Subgroup.mem_subgroupOf.mp hm, m.2, hmg⟩
  choose k hk hkM hkg using hlift
  have hinj' : Function.Injective fun j => L.map (MulAut.conj (k j)).toMonoidHom := by
    intro i j hij
    apply hinj
    change (barM M L).map (MulAut.conj (g i)).toMonoidHom =
      (barM M L).map (MulAut.conj (g j)).toMonoidHom
    rw [← hkg i, ← hkg j, ← barM_map_conj (hkM i), ← barM_map_conj (hkM j)]
    exact congrArg (barM M) hij
  have hle := h.le_pRank_three_of_injective_conj hB3 hL k hk hinj'
  omega

variable {P : Sylow 3 G} {M H R : Subgroup G}

theorem D1PhaseThree.exists_ne_one_mem_normalizer (h3 : D1PhaseThree 3 P M H R)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (hr : CFSG.Open.pRank 3 (H ⊓ M) ≤ 3) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {X : Subgroup G} (hXK : X ≤ H ⊓ M) {x : G}
    (hxX : x ∈ X) (hx3 : x ^ 3 = 1) (hxL : x ∉ Subgroup.normalizer (L : Set G)) {y : G}
    (hyX : y ∈ X) (hyx : y ∉ Subgroup.zpowers x) :
    ∃ w ∈ X, w ≠ 1 ∧ w ∈ Subgroup.normalizer (L : Set G) := by
  have hmm : ∀ (a b : G) (K : Subgroup G), K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro a b K
    rw [Subgroup.map_map]
    congr 1
    ext g
    simp [MulAut.conj_apply, mul_assoc]
  have hnorm : ∀ a b : G, L.map (MulAut.conj a).toMonoidHom = L.map (MulAut.conj b).toMonoidHom →
      a⁻¹ * b ∈ Subgroup.normalizer (L : Set G) := by
    intro a b hab
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change L.map (MulAut.conj (a⁻¹ * b)).toMonoidHom = L
    rw [hmm, ← hab, ← hmm, inv_mul_cancel]
    ext g
    simp
  have hx2 : x ^ 2 ∉ Subgroup.normalizer (L : Set G) := fun h => hxL (by
    have : x = x ^ 2 * x ^ 2 := by
      rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, hx3, one_mul, pow_one]
    rw [this]
    exact Subgroup.mul_mem _ h h)
  set g : Fin 4 → G := ![1, x, x ^ 2, y] with hg
  have hgK : ∀ j, g j ∈ H ⊓ M := by
    intro j
    fin_cases j
    · exact Subgroup.one_mem _
    · exact hXK hxX
    · exact (H ⊓ M).pow_mem (hXK hxX) 2
    · exact hXK hyX
  by_contra hno
  push Not at hno
  apply absurd (h3.le_pRank_three_of_injective_conj hB3 hL g hgK ?_) (by omega)
  intro i j hij
  have hn := hnorm _ _ hij
  have hy : ∀ k : ℕ, k < 3 → (x ^ k)⁻¹ * y ∈ Subgroup.normalizer (L : Set G) → False := by
    intro k hk hmem
    have hw1 : (x ^ k)⁻¹ * y ≠ 1 := fun h1 => hyx (by
      have : y = x ^ k := (inv_mul_eq_one.mp h1).symm
      rw [this]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) k)
    exact hno _ (X.mul_mem (X.inv_mem (X.pow_mem hxX k)) hyX) hw1 hmem
  have hy' : ∀ k : ℕ, k < 3 → y⁻¹ * x ^ k ∈ Subgroup.normalizer (L : Set G) → False := by
    intro k hk hmem
    exact hy k hk (by
      have := Subgroup.inv_mem _ hmem
      simpa using this)
  fin_cases i <;> fin_cases j <;> simp [hg] at hn ⊢
  all_goals first
    | exact hxL hn
    | exact hx2 hn
    | exact hy 0 (by norm_num) (by simpa using hn)
    | exact hy 1 (by norm_num) (by simpa using hn)
    | exact hy 2 (by norm_num) (by simpa using hn)
    | exact hy' 1 (by norm_num) (by simpa using hn)
    | exact hy' 2 (by norm_num) (by simpa using hn)
    | exact hxL (by simpa [pow_two] using hn)

omit [Finite G] in
theorem isMulCommutative_of_card_le_nine {A : Subgroup G} (hA : IsPGroup 3 A)
    (h9 : Nat.card A ≤ 9) [Finite A] : IsMulCommutative A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := hA.exists_card_eq
  have hm2 : m ≤ 2 := by
    by_contra h
    have : 3 ^ 3 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases m
  · rw [pow_zero] at hm
    have hbot : A = ⊥ := Subgroup.eq_bot_of_card_eq A hm
    subst hbot
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · rw [pow_one] at hm
    have : IsCyclic A := isCyclic_of_prime_card hm
    exact IsCyclic.isMulCommutative
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hm

theorem mem_normalizer_of_mk_mem_barM {L : Subgroup G} (hL : IsTwoPrimeComponent M L) {g : G}
    (hgM : g ∈ M) (hg : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgM⟩ ∈
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  have hle : barM M (Subgroup.zpowers g) ≤
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨h, hhM⟩, hh, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_subgroupOf.mp hh
    have : (⟨h, hhM⟩ : M) = ⟨g, hgM⟩ ^ k := Subtype.ext (by simpa using hk.symm)
    rw [this, map_zpow]
    exact Subgroup.zpow_mem _ hg k
  exact hL.le_normalizer hle (Subgroup.zpowers_le.mpr hgM) (Subgroup.mem_zpowers g)

theorem D1PhaseThree.false_of_moved_weakBlock_three (h3 : D1PhaseThree 3 P M H R)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock)
    (hSch : KFactCatalogSchreier) (hOp : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥)
    (hB : CFSG.Open.pRank 3 (barM M (H ⊓ M)) ≤ 3) {X : Subgroup G} (hXK : X ≤ H ⊓ M)
    (hXp : ∀ x ∈ X, x ^ 3 = 1) {z : G} (hzK : z ∈ H ⊓ M) (hz3 : z ^ 3 = 1) (hzX : z ∉ X)
    (hXz : X ≤ Subgroup.centralizer ({z} : Set G))
    {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hDp : ⁅D, D⁆ = D) (hDK : D ≤ barM M (H ⊓ M))
    (hzD : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzK.2⟩ ∈ D)
    (hZ : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzK.2⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      W = ⊥)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hDL : D ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {x : G} (hxX : x ∈ X) (hxL : x ∉ Subgroup.normalizer (L : Set G)) {X₀ : Subgroup G}
    (hX₀X : X₀ ≤ X) (hX₀ne : X₀ ≠ ⊥) (hX₀c : IsMulCommutative X₀)
    (hX₀L : X₀ ≤ Subgroup.normalizer (L : Set G))
    (hxX₀ : x ∈ Subgroup.normalizer (X₀ : Set G)) : False := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hzM : z ∈ M := hzK.2
  set zb := mk ⟨z, hzM⟩ with hzb
  set B := barM M (H ⊓ M) with hBdef
  have hLbC : IsComponentOf (barM M L) ⊤ := hL.component
  have hZ3 : ∀ L' : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf L' ⊤ → ∀ w ∈ L',
      w ∈ Subgroup.centralizer (L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      IsPGroup 3 (Subgroup.zpowers w) → w = 1 := fun L' hL' w hw hwC hw3 =>
    eq_one_of_mem_center_component hOp hL' hw hwC hw3
  have hzbB : zb ∈ B := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hzK)
  have hzb3 : zb ^ 3 = 1 := by
    rw [hzb, ← map_pow]
    have : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [this, map_one]
  obtain ⟨j, hjLB, hjc⟩ := h3.exists_inner_mem_barM h84 h86 hD2 hSch hL hDp hDK hDL hzD
  have hxM : x ∈ M := (hXK hxX).2
  set xb := mk ⟨x, hxM⟩ with hxb
  have hxbB : xb ∈ B := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hXK hxX))
  have hxb3 : xb ^ 3 = 1 := by
    rw [hxb, ← map_pow]
    have : (⟨x, hxM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hXp x hxX)
    rw [this, map_one]
  have hxbL : xb ∉ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun h =>
    hxL (mem_normalizer_of_mk_mem_barM hL.toIsTwoPrimeComponent hxM h)
  have hxbz : xb * zb = zb * xb := by
    rw [hxb, hzb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hXz hxX))
  have hX₀M : X₀ ≤ M := hX₀X.trans (hXK.trans inf_le_right)
  have hX₀el : IsElemAbelian 3 X₀ := ⟨hX₀c, fun w hw => hXp w (hX₀X hw)⟩
  set X₀b := barM M X₀ with hX₀b
  have hX₀card : Nat.card X₀b = Nat.card X₀ := card_barM_of_elem hp3 (by norm_num) hX₀M hX₀el
  have hX₀ne' : X₀b ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hX₀card
    exact hX₀ne (Subgroup.eq_bot_of_card_eq X₀ hX₀card.symm)
  have hX₀z' : X₀b ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨w, hwM⟩, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hzb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (hXz (hX₀X (Subgroup.mem_subgroupOf.mp hw))))
  have hzX₀' : zb ∉ X₀b := mk_not_mem_barM_of_commute hp3 (by norm_num)
    (fun w hw => hXp w (hX₀X hw)) hzM hz3 (fun h => hzX (hX₀X h)) (hX₀X.trans hXz)
  exact false_of_moved_component_three hLbC hZ3 hB hxbB hxb3 hxbL hzbB hzb3 hxbz (hDL hzD)
    (not_mem_centralizer_of_perfect hZ hLbC) hjLB hjc (barM_mono (hX₀X.trans hXK))
    (isElemAbelian_barM_of hX₀el) hX₀ne' (barM_le_normalizer_barM hX₀L) hX₀z'
    (mem_normalizer_barM hxM hxX₀) hzX₀'

theorem D1PhaseThree.le_normalizer_block_three (h3 : D1PhaseThree 3 P M H R)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock)
    (hSch : KFactCatalogSchreier) (hOp : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥)
    (hB : CFSG.Open.pRank 3 (barM M (H ⊓ M)) ≤ 3) (hr : CFSG.Open.pRank 3 (H ⊓ M) ≤ 3)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {X : Subgroup G} (hXK : X ≤ H ⊓ M) (hXp : ∀ x ∈ X, x ^ 3 = 1) (hX9 : 9 ≤ Nat.card X)
    (hX27 : Nat.card X ≤ 27) {z : G} (hzK : z ∈ H ⊓ M) (hz3 : z ^ 3 = 1) (hzX : z ∉ X)
    (hXz : X ≤ Subgroup.centralizer ({z} : Set G))
    {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hDp : ⁅D, D⁆ = D) (hDK : D ≤ barM M (H ⊓ M))
    (hDL : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      D ≤ Subgroup.normalizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hzD : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzK.2⟩ ∈ D)
    (hZ : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzK.2⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      W = ⊥)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    X ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key := fun {x : G} hxX hxL {X₀ : Subgroup G} hX₀X hX₀ne hX₀c hX₀L hxX₀ =>
    h3.false_of_moved_weakBlock_three h84 h86 hD2 hSch hOp hB hXK hXp hzK hz3 hzX hXz hDp hDK hzD
      hZ hL (hDL L hL) (x := x) hxX hxL (X₀ := X₀) hX₀X hX₀ne hX₀c hX₀L hxX₀
  have hXpg : IsPGroup 3 X := fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact hXp x x.2)⟩
  have hcen : ∀ x ∈ X, (∀ y ∈ X, x * y = y * x) → x ∈ Subgroup.normalizer (L : Set G) := by
    intro x hxX hxc
    by_contra hxL
    obtain ⟨y, hyX, hyx⟩ : ∃ y ∈ X, y ∉ Subgroup.zpowers x := by
      by_contra h
      push Not at h
      have hle := Subgroup.card_le_of_le (show X ≤ Subgroup.zpowers x from h)
      rw [Nat.card_zpowers] at hle
      have hord : orderOf x ≤ 3 :=
        Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hXp x hxX))
      omega
    obtain ⟨w, hwX, hw1, hwL⟩ :=
      h3.exists_ne_one_mem_normalizer hB3 hr hL hXK hxX (hXp x hxX) hxL hyX hyx
    have hX₀p : IsPGroup 3 (X ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) :=
      hXpg.to_le inf_le_left
    have hlt : Nat.card (X ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) < Nat.card X := by
      refine Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left fun h => hxL ?_)
      have hx' : x ∈ X ⊓ Subgroup.normalizer (L : Set G) := by rw [h]; exact hxX
      exact hx'.2
    have h9 : Nat.card (X ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) ≤ 9 := by
      have hdvd : Nat.card (X ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) ∣ Nat.card X :=
        Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨a, ha⟩ := hXpg.exists_card_eq
      obtain ⟨b, hb⟩ := hX₀p.exists_card_eq
      rw [ha, hb] at hdvd hlt
      rw [hb]
      have hab := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
      have hlt' := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
      have : a ≤ 3 := by
        by_contra hh
        have : 3 ^ 4 ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have : b ≤ 2 := by omega
      calc 3 ^ b ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
        _ = 9 := by norm_num
    refine key hxX hxL inf_le_left (fun h => hw1 ?_) (isMulCommutative_of_card_le_nine hX₀p h9)
      inf_le_right ?_
    · have : w ∈ (X ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) := ⟨hwX, hwL⟩
      rw [h] at this
      exact this
    · rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        have hxg : x * g * x⁻¹ = g := by rw [hxc g hg.1, mul_inv_cancel_right]
        rw [hxg]
        exact hg
      · intro hg
        have hgX : g ∈ X := by
          have := X.mul_mem (X.mul_mem (X.inv_mem hxX) hg.1) hxX
          simpa [mul_assoc] using this
        have hxg : x * g * x⁻¹ = g := by rw [hxc g hgX, mul_inv_cancel_right]
        rw [hxg] at hg
        exact hg
  intro x hxX
  by_contra hxL
  set ZX : Subgroup G := X ⊓ Subgroup.centralizer (X : Set G) with hZX
  have hZXne : ZX ≠ ⊥ := by
    have hnt : Nontrivial X := by
      rw [Subgroup.nontrivial_iff_ne_bot]
      intro h
      rw [h, Subgroup.card_bot] at hX9
      omega
    have : Nontrivial (Subgroup.center X) := hXpg.center_nontrivial
    obtain ⟨c, hc⟩ := exists_ne (1 : Subgroup.center X)
    intro h
    apply hc
    have hcZ : ((c : X) : G) ∈ ZX := ⟨(c : X).2, Subgroup.mem_centralizer_iff.mpr fun y hy => by
      have := Subgroup.mem_center_iff.mp c.2 ⟨y, hy⟩
      exact congrArg Subtype.val this⟩
    rw [h, Subgroup.mem_bot] at hcZ
    exact Subtype.ext (Subtype.ext hcZ)
  have hZXc : IsMulCommutative ZX := ⟨⟨fun a b => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp a.2.2 b b.2.1).symm⟩⟩
  have hZXL : ZX ≤ Subgroup.normalizer (L : Set G) := fun c hc =>
    hcen c hc.1 fun y hy => (Subgroup.mem_centralizer_iff.mp hc.2 y hy).symm
  have hxZX : x ∈ Subgroup.normalizer (ZX : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have hxg : x * g * x⁻¹ = g := by
        rw [(Subgroup.mem_centralizer_iff.mp hg.2 x hxX), mul_inv_cancel_right]
      rw [hxg]
      exact hg
    · intro hg
      have hcx := Subgroup.mem_centralizer_iff.mp hg.2 x hxX
      have hgg : x * g * x⁻¹ = g := by
        have h1 : x * (x * g * x⁻¹) = x * g := by
          rw [hcx]
          group
        exact mul_left_cancel (a := x) h1
      rw [hgg] at hg
      exact hg
  exact key hxX hxL inf_le_left hZXne hZXc hZXL hxZX

end CFSG.AGLEmbedding
