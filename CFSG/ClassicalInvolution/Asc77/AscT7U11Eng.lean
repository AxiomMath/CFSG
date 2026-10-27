module

public import CFSG.ClassicalInvolution.Asc77.AscT7U10
public import CFSG.ClassicalInvolution.Asc77.AscT7TStar2
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Ctx

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7U

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z : G}

structure Hyp25F (K : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z : G) : Prop where
  hz2 : z * z = 1
  hz1 : z ≠ 1
  hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s
  hRS : R ≤ (S : Subgroup G)
  zA : z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)
  hRne : R ≠ R'
  cA : ∀ {s : G}, s ∈ (S : Subgroup G) →
    conjSub s ((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) =
      (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)
  twin_sq : ∀ {x : G}, x * z * x⁻¹ = z → conjSub (x * x) K = K
  not_norm : ∀ {t'' g : G}, g * z * g⁻¹ = t'' → z ≠ t'' →
    (¬ ∃ y : G, y * z * y⁻¹ = t'' * z) → conjSub z (conjSub g K) ≠ conjSub g K
  swap_nf : ∃ t' ∈ (S : Subgroup G), t' * t' = 1 ∧ (∃ g : G, g * z * g⁻¹ = t') ∧
    conjSub t' R = R' ∧ ¬ ∃ y : G, y * z * y⁻¹ = t' * z
  c25_5 : ∀ A : Subgroup G, z ∈ A → A ≤ (S : Subgroup G) →
    (∀ s ∈ (S : Subgroup G), conjSub s A = A) →
    (∀ a ∈ A, a ≠ 1 → z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))) → A = Subgroup.zpowers z

theorem not_sq_eq_zE (hyp : Hyp25F K S R R' z) {t' g : G}
    (hg : g * z * g⁻¹ = t') (hzt : z ≠ t') (hnf : ¬ ∃ y : G, y * z * y⁻¹ = t' * z) {b : G}
    (hbt : b * t' = t' * b) (hbb : b * b = z) : False := by
  have hx : (g⁻¹ * b * g) * z * (g⁻¹ * b * g)⁻¹ = z := by
    calc (g⁻¹ * b * g) * z * (g⁻¹ * b * g)⁻¹ = g⁻¹ * b * (g * z * g⁻¹) * b⁻¹ * g := by group
      _ = g⁻¹ * b * t' * b⁻¹ * g := by rw [hg]
      _ = g⁻¹ * (b * t' * b⁻¹) * g := by group
      _ = g⁻¹ * t' * g := by rw [hbt]; group
      _ = z := by rw [← hg]; group
  have h1 := hyp.twin_sq hx
  have h2 : conjSub (b * b) (conjSub g K) = conjSub g K := by
    calc conjSub (b * b) (conjSub g K) = conjSub ((b * b) * g) K := (conjSub_mul (b * b) g K).symm
      _ = conjSub (g * ((g⁻¹ * b * g) * (g⁻¹ * b * g))) K := by congr 1; group
      _ = conjSub g (conjSub ((g⁻¹ * b * g) * (g⁻¹ * b * g)) K) := by rw [conjSub_mul]
      _ = conjSub g K := by rw [h1]
  rw [hbb] at h2
  exact hyp.not_norm hg hzt hnf h2

theorem comm_of_central_modE (hyp : Hyp25F K S R R' z) {t' g : G}
    (ht'S : t' ∈ (S : Subgroup G)) (ht'2 : t' * t' = 1) (hg : g * z * g⁻¹ = t')
    (hnf : ¬ ∃ y : G, y * z * y⁻¹ = t' * z) {x : G} (hxS : x ∈ (S : Subgroup G))
    (hx : ∀ s ∈ (S : Subgroup G), s * x * s⁻¹ * x⁻¹ ∈ Subgroup.zpowers z) :
    t' * x = x * t' := by
  have hz2 : z * z = 1 := hyp.hz2
  have hinv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
  have hzc : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hx t' ht'S)
  rw [hinv] at hk
  rcases Int.even_or_odd' k with ⟨k', hk' | hk'⟩
  · have : z ^ k = 1 := by rw [hk', zpow_mul, zpow_two, hz2, one_zpow]
    rw [this] at hk
    have h1 : t' * x * t' = x := by
      have := congrArg (fun w => w * x) hk
      simp only [one_mul] at this
      calc t' * x * t' = (t' * x * t' * x⁻¹) * x := by group
        _ = x := by rw [← hk]; group
    calc t' * x = (t' * x * t') * t' := by
          calc t' * x = t' * x * (t' * t') := by rw [ht'2, mul_one]
            _ = (t' * x * t') * t' := by group
      _ = x * t' := by rw [h1]
  · exfalso
    have : z ^ k = z := by
      rw [hk', zpow_add_one, zpow_mul, zpow_two, hz2, one_zpow, one_mul]
    rw [this] at hk
    have h1 : t' * x * t' = z * x := by
      calc t' * x * t' = (t' * x * t' * x⁻¹) * x := by group
        _ = z * x := by rw [← hk]
    have h2 : x⁻¹ * t' * x = z * t' := by
      have h3 : t' * x = z * x * t' := by
        calc t' * x = (t' * x * t') * t' := by
              calc t' * x = t' * x * (t' * t') := by rw [ht'2, mul_one]
                _ = (t' * x * t') * t' := by group
          _ = z * x * t' := by rw [h1]
      have hxz : x⁻¹ * z * x = z := by
        have := hzc x hxS
        calc x⁻¹ * z * x = x⁻¹ * (z * x) := by group
          _ = x⁻¹ * (x * z) := by rw [this]
          _ = z := by group
      calc x⁻¹ * t' * x = x⁻¹ * (t' * x) := by group
        _ = x⁻¹ * (z * x * t') := by rw [h3]
        _ = (x⁻¹ * z * x) * t' := by group
        _ = z * t' := by rw [hxz]
    apply hnf
    refine ⟨x⁻¹ * g, ?_⟩
    calc (x⁻¹ * g) * z * (x⁻¹ * g)⁻¹ = x⁻¹ * (g * z * g⁻¹) * x := by group
      _ = x⁻¹ * t' * x := by rw [hg]
      _ = z * t' := h2
      _ = t' * z := (hzc t' ht'S).symm

theorem sq_comm_of_central_modE (hyp : Hyp25F K S R R' z) {x : G}
    (hx : ∀ s ∈ (S : Subgroup G), s * x * s⁻¹ * x⁻¹ ∈ Subgroup.zpowers z)
    (hxS : x ∈ (S : Subgroup G)) {s : G} (hs : s ∈ (S : Subgroup G)) :
    s * (x * x) * s⁻¹ = x * x := by
  have hz2 : z * z = 1 := hyp.hz2
  have hxz : x * z = z * x := hyp.hzS x hxS
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hx s hs)
  have hsx : s * x * s⁻¹ = z ^ k * x := by
    calc s * x * s⁻¹ = (s * x * s⁻¹ * x⁻¹) * x := by group
      _ = z ^ k * x := by rw [← hk]
  have hcz : x * z ^ k = z ^ k * x := (Commute.zpow_right (show Commute x z from hxz) k).eq
  have hz2k : z ^ k * z ^ k = 1 := by
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hz2, one_zpow]
  calc s * (x * x) * s⁻¹ = (s * x * s⁻¹) * (s * x * s⁻¹) := by group
    _ = (z ^ k * x) * (z ^ k * x) := by rw [hsx]
    _ = z ^ k * (x * z ^ k) * x := by group
    _ = z ^ k * (z ^ k * x) * x := by rw [hcz]
    _ = (z ^ k * z ^ k) * (x * x) := by group
    _ = x * x := by rw [hz2k, one_mul]

theorem exists_involution_of_central_modE (hyp : Hyp25F K S R R' z) {t' g : G}
    (ht'S : t' ∈ (S : Subgroup G)) (ht'2 : t' * t' = 1) (hg : g * z * g⁻¹ = t')
    (hzt : z ≠ t') (hnf : ¬ ∃ y : G, y * z * y⁻¹ = t' * z) {A : Subgroup G}
    (hAS : A ≤ (S : Subgroup G)) :
    ∀ m : ℕ, ∀ x : G, orderOf x = 2 ^ m → x ∈ A → x ∉ Subgroup.zpowers z →
      (∀ s ∈ (S : Subgroup G), s * x * s⁻¹ * x⁻¹ ∈ Subgroup.zpowers z) →
      ∃ y ∈ A, y * y = 1 ∧ y ≠ 1 ∧ y ≠ z ∧
        ∀ s ∈ (S : Subgroup G), s * y * s⁻¹ * y⁻¹ ∈ Subgroup.zpowers z := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro x hm hxA hxT hxc
    rcases m with _ | _ | m
    · exfalso
      have : x = 1 := orderOf_eq_one_iff.mp (by simpa using hm)
      exact hxT (this ▸ one_mem _)
    · have hxx : x * x = 1 := by
        have := pow_orderOf_eq_one x
        rw [hm] at this
        simpa [pow_two] using this
      refine ⟨x, hxA, hxx, fun h => hxT (h ▸ one_mem _), fun h => hxT (h ▸ Subgroup.mem_zpowers z),
        hxc⟩
    · have hxS : x ∈ (S : Subgroup G) := hAS hxA
      have hdvd : 2 ∣ orderOf x := by rw [hm]; exact dvd_pow_self 2 (Nat.succ_ne_zero _)
      have hxx_ord : orderOf (x * x) = 2 ^ (m + 1) := by
        rw [← pow_two, orderOf_pow_of_dvd (by norm_num) hdvd, hm]
        rw [pow_succ]; omega
      have hxxA : x * x ∈ A := A.mul_mem hxA hxA
      by_cases hxxT : x * x ∈ Subgroup.zpowers z
      · exfalso
        have hz2 : z * z = 1 := hyp.hz2
        have hxx1 : x * x ≠ 1 := by
          intro h
          rw [h] at hxx_ord
          have : (2 : ℕ) ^ (m + 1) = 1 := by simpa using hxx_ord.symm
          have h2 : 2 ≤ 2 ^ (m + 1) := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxxT
        have hxxz : x * x = z := by
          rcases Int.even_or_odd' k with ⟨k', hk' | hk'⟩
          · exfalso
            apply hxx1
            rw [← hk, hk', zpow_mul, zpow_two, hz2, one_zpow]
          · rw [← hk, hk', zpow_add_one, zpow_mul, zpow_two, hz2, one_zpow, one_mul]
        have hcomm := comm_of_central_modE hyp ht'S ht'2 hg hnf hxS hxc
        exact not_sq_eq_zE hyp hg hzt hnf hcomm.symm hxxz
      · refine ih (m + 1) (by omega) (x * x) hxx_ord hxxA hxxT (fun s hs => ?_)
        have := sq_comm_of_central_modE hyp hxc hxS hs
        have e : s * (x * x) * s⁻¹ * (x * x)⁻¹ = 1 := by
          rw [this]; group
        rw [e]; exact one_mem _

theorem exists_normal_four_badE (hyp : Hyp25F K S R R' z)
    (hne : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ≠
      Subgroup.zpowers z) :
    ∃ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      a * a = 1 ∧ a ≠ 1 ∧ a ≠ z ∧
        (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) ∧
        z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) := by
  set A := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) with hA
  have hAS : A ≤ (S : Subgroup G) := inf_le_left
  have hzA : z ∈ A := hyp.zA
  have hz2 : z * z = 1 := hyp.hz2
  have hz1 : z ≠ 1 := hyp.hz1
  have hzc : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  obtain ⟨t', ht'S, ht'2, ⟨g, hg⟩, ht'R, hnf⟩ := hyp.swap_nf
  have hRne : R ≠ R' := hyp.hRne
  have hRS : R ≤ (S : Subgroup G) := hyp.hRS
  have hzt : z ≠ t' := by
    intro h
    apply hRne
    have h1 : conjSub t' R = R := by
      rw [← h]
      exact T7F2.conjSub_eq_of_centralizes fun r hr => hyp.hzS r (hRS hr)
    rw [← ht'R, h1]
  have hTc : ∀ s ∈ (S : Subgroup G), ∀ x ∈ Subgroup.zpowers z, s * x = x * s := by
    intro s hs x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_right (show Commute s z from hzc s hs) k).eq
  obtain ⟨x, hxA, hxT, hxc⟩ := exists_central_mod S.isPGroup' hAS
    (fun s hs => hyp.cA hs) (Subgroup.zpowers_le.mpr hzA) hTc
    (Ne.symm hne)
  obtain ⟨m, hm⟩ := AscL62.orderOf_eq_two_pow_of_isPGroup S.isPGroup' (hAS hxA)
  obtain ⟨y, hyA, hyy, hy1, hyz, hyc⟩ :=
    exists_involution_of_central_modE hyp ht'S ht'2 hg hzt hnf hAS m x hm hxA hxT hxc
  have hyS : y ∈ (S : Subgroup G) := hAS hyA
  have hyzc : y * z = z * y := hzc y hyS
  have hyconj : ∀ s ∈ (S : Subgroup G), s * y * s⁻¹ = y ∨ s * y * s⁻¹ = y * z := by
    intro s hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hyc s hs)
    rcases Int.even_or_odd' k with ⟨k', hk' | hk'⟩
    · left
      have : z ^ k = 1 := by rw [hk', zpow_mul, zpow_two, hz2, one_zpow]
      rw [this] at hk
      calc s * y * s⁻¹ = (s * y * s⁻¹ * y⁻¹) * y := by group
        _ = y := by rw [← hk]; group
    · right
      have : z ^ k = z := by rw [hk', zpow_add_one, zpow_mul, zpow_two, hz2, one_zpow, one_mul]
      rw [this] at hk
      calc s * y * s⁻¹ = (s * y * s⁻¹ * y⁻¹) * y := by group
        _ = z * y := by rw [← hk]
        _ = y * z := hyzc.symm
  have hyz2 : (y * z) * (y * z) = 1 := by
    calc (y * z) * (y * z) = y * (z * y) * z := by group
      _ = y * (y * z) * z := by rw [← hyzc]
      _ = (y * y) * (z * z) := by group
      _ = 1 := by rw [hyy, hz2, one_mul]
  let E : Subgroup G :=
    { carrier := {w | w = 1 ∨ w = y ∨ w = z ∨ w = y * z}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (ha | ha | ha | ha) (hb | hb | hb | hb) <;> rw [ha, hb]
        · simp
        · simp
        · simp
        · simp
        · simp
        · exact Or.inl hyy
        · exact Or.inr (Or.inr (Or.inr rfl))
        · right; right; left
          calc y * (y * z) = (y * y) * z := by group
            _ = z := by rw [hyy, one_mul]
        · simp
        · exact Or.inr (Or.inr (Or.inr hyzc.symm))
        · exact Or.inl hz2
        · right; left
          calc z * (y * z) = (z * y) * z := by group
            _ = (y * z) * z := by rw [← hyzc]
            _ = y * (z * z) := by group
            _ = y := by rw [hz2, mul_one]
        · simp
        · right; right; left
          calc y * z * y = y * (z * y) := by group
            _ = y * (y * z) := by rw [← hyzc]
            _ = (y * y) * z := by group
            _ = z := by rw [hyy, one_mul]
        · right; left
          calc y * z * z = y * (z * z) := by group
            _ = y := by rw [hz2, mul_one]
        · exact Or.inl hyz2
      inv_mem' := by
        rintro a (ha | ha | ha | ha) <;> rw [ha]
        · simp
        · right; left; exact inv_eq_of_mul_eq_one_right hyy
        · right; right; left; exact inv_eq_of_mul_eq_one_right hz2
        · right; right; right
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hyy, inv_eq_of_mul_eq_one_right hz2, hyzc] }
  have hzE : z ∈ E := Or.inr (Or.inr (Or.inl rfl))
  have hyE : y ∈ E := Or.inr (Or.inl rfl)
  have hzS : z ∈ (S : Subgroup G) := hAS hzA
  have hES : E ≤ (S : Subgroup G) := by
    rintro w (hw | hw | hw | hw) <;> rw [hw]
    · exact one_mem _
    · exact hyS
    · exact hzS
    · exact Subgroup.mul_mem _ hyS hzS
  have hconjE : ∀ s ∈ (S : Subgroup G), ∀ w ∈ E, s * w * s⁻¹ ∈ E := by
    intro s hs w hw
    have hszs : s * z * s⁻¹ = z := by
      calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [hzc s hs]
        _ = z := by group
    rcases hw with hw | hw | hw | hw <;> rw [hw]
    · simp
    · rcases hyconj s hs with h | h
      · rw [h]; exact hyE
      · rw [h]; exact Or.inr (Or.inr (Or.inr rfl))
    · rw [hszs]; exact hzE
    · have e : s * (y * z) * s⁻¹ = (s * y * s⁻¹) * (s * z * s⁻¹) := by group
      rw [e, hszs]
      rcases hyconj s hs with h | h
      · rw [h]; exact Or.inr (Or.inr (Or.inr rfl))
      · rw [h]
        right; left
        calc y * z * z = y * (z * z) := by group
          _ = y := by rw [hz2, mul_one]
  have hEnorm : ∀ s ∈ (S : Subgroup G), conjSub s E = E := by
    intro s hs
    ext w
    rw [mem_conjSub_iff]
    constructor
    · intro hw
      have := hconjE s hs _ hw
      simpa [mul_assoc] using this
    · intro hw
      have := hconjE s⁻¹ (Subgroup.inv_mem _ hs) w hw
      simpa [mul_assoc] using this
  have hcontra : ¬ ∀ w ∈ E, w ≠ 1 → z ∈ zStarOf (Subgroup.centralizer ({w} : Set G)) := by
    intro hall
    have hE := hyp.c25_5 E hzE hES hEnorm hall
    have hyzp : y ∈ Subgroup.zpowers z := hE ▸ hyE
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyzp
    rcases Int.even_or_odd' k with ⟨k', hk' | hk'⟩
    · apply hy1
      rw [← hk, hk', zpow_mul, zpow_two, hz2, one_zpow]
    · apply hyz
      rw [← hk, hk', zpow_add_one, zpow_mul, zpow_two, hz2, one_zpow, one_mul]
  push Not at hcontra
  obtain ⟨w, hwE, hw1, hwz⟩ := hcontra
  have hwz' : w ≠ z := fun h => hwz (h ▸ T7T.mem_zStarOf_centralizer_self z)
  have hw : w = y ∨ w = y * z := by
    rcases hwE with h | h | h | h
    · exact absurd h hw1
    · exact Or.inl h
    · exact absurd h hwz'
    · exact Or.inr h
  have hwA : w ∈ A := by
    rcases hw with rfl | rfl
    · exact hyA
    · exact A.mul_mem hyA hzA
  refine ⟨w, hwA, ?_, hw1, hwz', ?_, hwz⟩
  · rcases hw with rfl | rfl
    · exact hyy
    · exact hyz2
  · intro s hs
    rcases hw with rfl | rfl
    · exact hyconj s hs
    · have hszs : s * z * s⁻¹ = z := by
        calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [hzc s hs]
          _ = z := by group
      have e : s * (y * z) * s⁻¹ = (s * y * s⁻¹) * (s * z * s⁻¹) := by group
      rw [e, hszs]
      rcases hyconj s hs with h | h
      · left; rw [h]
      · right
        rw [h]

theorem comm_swap_of_normal_fourE (hyp : Hyp25F K S R R' z) {t' g : G}
    (ht'S : t' ∈ (S : Subgroup G)) (ht'2 : t' * t' = 1) (hg : g * z * g⁻¹ = t')
    (hnf : ¬ ∃ y : G, y * z * y⁻¹ = t' * z) {a : G} (haS : a ∈ (S : Subgroup G))
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) :
    t' * a = a * t' := by
  have hz2 : z * z = 1 := hyp.hz2
  have haz : a * z = z * a := hyp.hzS a haS
  refine comm_of_central_modE hyp ht'S ht'2 hg hnf haS fun s hs => ?_
  rcases hconj s hs with h | h
  · rw [h]
    have : a * a⁻¹ = 1 := by group
    rw [this]; exact one_mem _
  · rw [h]
    have : a * z * a⁻¹ = z := by
      calc a * z * a⁻¹ = (z * a) * a⁻¹ := by rw [haz]
        _ = z := by group
    rw [this]; exact Subgroup.mem_zpowers z

end T7U

end CFSG.ClassicalInvolution.Asc77
