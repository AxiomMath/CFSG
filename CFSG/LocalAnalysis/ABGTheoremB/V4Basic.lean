module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.DataConstructionSetting
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.ConjugacyBasic
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusTools
public import CFSG.LocalAnalysis.ABGTheoremB.V4Defs

public section

namespace CFSG.ABGTheoremB.V4

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGTheoremB.TotallyInverted
open scoped Pointwise

variable {G : Type} [Group G]

theorem exists_mul_mem_centralizer_of_coprime [Finite G] {A M : Subgroup G}
    (hAM : A ≤ Subgroup.normalizer (M : Set G)) (hM : Group.IsSolvable M)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card M)) {g : G}
    (hg : ∀ a ∈ A, g⁻¹ * (a * g * a⁻¹) ∈ M) :
    ∃ m ∈ M, g * m ∈ Subgroup.centralizer (A : Set G) := by
  let _ := Omnibus.conjActOn A M hAM
  let c : A → M := fun a => ⟨g⁻¹ * (a * g * (a : G)⁻¹), hg a a.2⟩
  have hc : ∀ a b : A, c (a * b) = c a * (a • c b) := by
    intro a b
    apply Subtype.ext
    change g⁻¹ * ((a * b : G) * g * (a * b : G)⁻¹) =
      g⁻¹ * (a * g * (a : G)⁻¹) * ((a : G) * (g⁻¹ * (b * g * (b : G)⁻¹)) * (a : G)⁻¹)
    group
  obtain ⟨m, hm⟩ := CFSG.exists_principal_cocycle_of_solvable_coprime hM hcop c hc
  refine ⟨m, m.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h := congrArg Subtype.val (hm ⟨a, ha⟩)
  change g⁻¹ * (a * g * a⁻¹) = (m : G) * (a * (m : G) * a⁻¹)⁻¹ at h
  calc a * (g * m) = g * (g⁻¹ * (a * g * a⁻¹)) * a * m := by group
    _ = g * ((m : G) * (a * (m : G) * a⁻¹)⁻¹) * a * m := by rw [h]
    _ = g * m * a := by group

theorem comm_of_sq_comm {u z : G} (hu : Odd (orderOf u)) (h : u ^ 2 * z = z * u ^ 2) :
    u * z = z * u := by
  have hmem : u ^ 2 ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h
  exact Subgroup.mem_centralizer_singleton_iff.mp (Omnibus.mem_of_sq_mem hu hmem)

theorem exists_pow_mul_eq {M : Subgroup G} {k m : G} (hk : k ∈ Subgroup.normalizer (M : Set G))
    (hm : m ∈ M) (n : ℕ) : ∃ m' ∈ M, (m * k) ^ n = m' * k ^ n := by
  induction n with
  | zero => exact ⟨1, M.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨m', hm', h⟩ := ih
    have hkn : k ^ n ∈ Subgroup.normalizer (M : Set G) := Subgroup.pow_mem _ hk n
    refine ⟨m' * (k ^ n * m * (k ^ n)⁻¹), M.mul_mem hm'
      ((Subgroup.mem_normalizer_iff.mp hkn m).mp hm), ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem mem_of_pow_mem_of_coprime [Finite G] {X M : Subgroup G} {k : G} (hk : k ∈ X) {n : ℕ}
    (hn : Nat.Coprime (Nat.card X) n) (h : k ^ n ∈ M) : k ∈ M := by
  have hord : Nat.Coprime (orderOf k) n :=
    Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard X hk) hn
  have hle : Subgroup.zpowers (k ^ n) ≤ Subgroup.zpowers k :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers k) n)
  have heq : Subgroup.zpowers (k ^ n) = Subgroup.zpowers k :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers,
      Nat.Coprime.orderOf_pow hord])
  have hkmem : k ∈ Subgroup.zpowers (k ^ n) := heq ▸ Subgroup.mem_zpowers k
  exact (Subgroup.zpowers_le.mpr h) hkmem

theorem permutable_inf_of_le_normalizer [Finite G] {X Y M : Subgroup G}
    (hXY : (X : Set G) * Y = Y * X) (hcop : Nat.Coprime (Nat.card X) (Nat.card Y))
    (hXM : X ≤ Subgroup.normalizer (M : Set G)) :
    (X : Set G) * ((Y ⊓ M : Subgroup G) : Set G) = ((Y ⊓ M : Subgroup G) : Set G) * X ∧
      (X ⊓ M = ⊥ → X ≤ Subgroup.normalizer ((Y ⊓ M : Subgroup G) : Set G)) := by
  have key : ∀ x ∈ X, ∀ y ∈ Y ⊓ M, ∃ y' ∈ Y ⊓ M, ∃ x' ∈ X, x * y = y' * x' ∧
      x * x'⁻¹ ∈ M := by
    intro x hx y hy
    have hmem : x * y ∈ (Y : Set G) * X := by
      rw [← hXY]
      exact ⟨x, hx, y, hy.1, rfl⟩
    obtain ⟨y', hy', x', hx', hxy⟩ := hmem
    change y' * x' = x * y at hxy
    set k := x * x'⁻¹ with hkdef
    have hkX : k ∈ X := X.mul_mem hx (X.inv_mem hx')
    have hm : x * y * x⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hXM hx) y).mp hy.2
    have hy'e : y' = x * y * x⁻¹ * k := by rw [hkdef, ← hxy]; group
    obtain ⟨m', hm', hpow⟩ := exists_pow_mul_eq (hXM hkX) hm (Nat.card Y)
    have hyY : y' ^ Nat.card Y = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard Y hy')
    rw [← hy'e, hyY] at hpow
    have hkpow : k ^ Nat.card Y ∈ M := by
      rw [eq_inv_of_mul_eq_one_right hpow.symm]
      exact M.inv_mem hm'
    have hkM : k ∈ M := mem_of_pow_mem_of_coprime hkX hcop hkpow
    refine ⟨y', ⟨hy', ?_⟩, x', hx', hxy.symm, hkM⟩
    rw [hy'e]
    exact M.mul_mem hm hkM
  have hsub : (X : Set G) * ((Y ⊓ M : Subgroup G) : Set G) ⊆
      ((Y ⊓ M : Subgroup G) : Set G) * X := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨y', hy', x', hx', h, -⟩ := key x hx y hy
    exact ⟨y', hy', x', hx', h.symm⟩
  refine ⟨Set.Subset.antisymm hsub ?_, ?_⟩
  · rintro _ ⟨y, hy, x, hx, rfl⟩
    obtain ⟨y', hy', x', hx', h, -⟩ := key x⁻¹ (X.inv_mem hx) y⁻¹ ((Y ⊓ M).inv_mem hy)
    refine ⟨x'⁻¹, X.inv_mem hx', y'⁻¹, (Y ⊓ M).inv_mem hy', ?_⟩
    have := congrArg (·⁻¹) h
    simp only [mul_inv_rev, inv_inv] at this
    exact this.symm
  · intro hXM' x hx
    have hconj : ∀ x ∈ X, ∀ y ∈ Y ⊓ M, x * y * x⁻¹ ∈ Y ⊓ M := by
      intro x hx y hy
      obtain ⟨y', hy', x', hx', h, hk⟩ := key x hx y hy
      have hk' : x * x'⁻¹ ∈ X ⊓ M := ⟨X.mul_mem hx (X.inv_mem hx'), hk⟩
      rw [hXM', Subgroup.mem_bot, mul_inv_eq_one] at hk'
      have : x * y * x⁻¹ = y' := by rw [h, hk']; group
      rw [this]
      exact hy'
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hconj x hx y
    · intro hy
      have := hconj x⁻¹ (X.inv_mem hx) _ hy
      simpa [mul_assoc] using this

theorem mem_sup_iff_of_le_normalizer {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) {g : G} :
    g ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ h]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

theorem mem_sup_iff_of_le_normalizer' {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) {g : G} :
    g ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ h]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

theorem odd_card_of_le {A B : Subgroup G} (h : A ≤ B) (hB : Odd (Nat.card B)) :
    Odd (Nat.card A) :=
  hB.of_dvd_nat (Subgroup.card_dvd_of_le h)

theorem le_normalizer_centralizer {A Y : Subgroup G} (h : A ≤ Subgroup.normalizer (Y : Set G)) :
    A ≤ Subgroup.normalizer (Subgroup.centralizer (Y : Set G) : Set G) := by
  intro g hg
  rw [← DataConstruction.conjSub_eq_self_iff, DataConstruction.conjSub_centralizer,
    DataConstruction.conjSub_eq_self_of_mem (h hg)]

section SettingFacts

variable [Finite G] {σ : Setting G}

open TotallyInverted.DataConstruction in
theorem exists_conj_x_eq_xs (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (i : Fin 3) :
    ∃ g ∈ Subgroup.normalizer (σ.T : Set G), g * σ.x * g⁻¹ = σ.xs i := by
  obtain ⟨a, haN, -, ha1, ha2⟩ := exists_a hσ hII.automizer_T
  have hcyc := xs_cycle hσ ha1 ha2
  refine ⟨a ^ (i : ℕ), Subgroup.pow_mem _ haN _, ?_⟩
  have h := pow_conj_xs hcyc i 0
  rw [zero_add] at h
  exact h

omit [Finite G] in
theorem conjSub_C {g : G} (hg : g ∈ Subgroup.normalizer (σ.T : Set G)) : conjSub g σ.C = σ.C := by
  rw [Setting.C, DataConstruction.conjSub_centralizer, DataConstruction.conjSub_eq_self_of_mem hg]

theorem conjSub_oddCoreIn_C {g : G} (hg : g ∈ Subgroup.normalizer (σ.T : Set G)) :
    conjSub g (oddCoreIn σ.C) = oddCoreIn σ.C := by
  rw [DataConstruction.conjSub_oddCoreIn, conjSub_C hg]

omit [Finite G] in
theorem conjSub_N {g : G} {i : Fin 3} (hgi : g * σ.x * g⁻¹ = σ.xs i) :
    conjSub g σ.N = σ.Ns i := by
  rw [Setting.N, DataConstruction.conjSub_centralizer_singleton, hgi, Setting.Ns]

theorem conjSub_ON {g : G} {i : Fin 3} (hgi : g * σ.x * g⁻¹ = σ.xs i) :
    conjSub g σ.ON = oddCoreIn (σ.Ns i) := by
  rw [Setting.ON, DataConstruction.conjSub_oddCoreIn, conjSub_N hgi]

omit [Finite G] in
theorem isPGroup_D : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S

theorem isPGroup_T (hσ : σ.IsValid) : IsPGroup 2 σ.T := σ.S.isPGroup'.to_le (σ.T_le_S hσ)

theorem eq_x_of_mem_center_D (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {z : G}
    (hz : z ∈ centerOf σ.D) (hz2 : orderOf z = 2) : z = σ.x := by
  rw [← hII.center_S_eq_center_D] at hz
  exact hσ.center_involution z hz hz2

theorem x_mem_of_le_D (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {B : Subgroup G}
    (hBD : B ≤ σ.D) (hDB : σ.D ≤ Subgroup.normalizer (B : Set G)) (hB : B ≠ ⊥) : σ.x ∈ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B' : Subgroup σ.D := B.subgroupOf σ.D with hB'def
  have hB'n : B'.Normal := ⟨fun b hb d => (Subgroup.mem_normalizer_iff.mp (hDB d.2) b).mp hb⟩
  have hD2 : IsPGroup 2 σ.D := isPGroup_D
  have hnil : Group.IsNilpotent σ.D := hD2.isNilpotent
  have hB'1 : B' ≠ ⊥ := by
    intro h
    apply hB
    rw [eq_bot_iff]
    intro b hb
    have : (⟨b, hBD hb⟩ : σ.D) ∈ B' := hb
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hB'1
  set Z : Subgroup σ.D := B' ⊓ Subgroup.center σ.D
  have hZ2 : IsPGroup 2 Z := hD2.to_subgroup Z
  have hZnt : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr hZ
  have hdvd : 2 ∣ Nat.card Z := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ2
    rw [hn]
    rcases n with _ | n
    · rw [pow_zero] at hn
      exact absurd (Nat.card_eq_one_iff_unique.mp hn).1 (not_subsingleton_iff_nontrivial.mpr hZnt)
    · exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hzc : ((z : σ.D) : G) ∈ centerOf σ.D := by
    refine Subgroup.mem_inf.mpr ⟨((z : σ.D)).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have := Subgroup.mem_center_iff.mp (z.2.2) ⟨d, hd⟩
    exact congrArg Subtype.val this
  have hzo : orderOf ((z : σ.D) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hzx := eq_x_of_mem_center_D hσ hII hzc hzo
  rw [← hzx]
  exact z.2.1

theorem le_N_of_le_Ns (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {Y : Subgroup G}
    (hDY : σ.D ≤ Subgroup.normalizer (Y : Set G)) {i : Fin 3} (hYi : Y ≤ σ.Ns i) :
    Y ≤ σ.N := by
  set B : Subgroup G := σ.D ⊓ Subgroup.centralizer (Y : Set G) with hBdef
  have hBD : B ≤ σ.D := inf_le_left
  have hDB : σ.D ≤ Subgroup.normalizer (B : Set G) :=
    (le_inf Subgroup.le_normalizer (le_normalizer_centralizer hDY)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hxi : σ.xs i ∈ B := by
    refine Subgroup.mem_inf.mpr ⟨σ.T_le_D hσ (Conjugacy.xs_mem_T i), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYi hy)
  have hB : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hxi
    exact Conjugacy.xs_ne_one hσ i hxi
  have hx := x_mem_of_le_D hσ hII hBD hDB hB
  intro y hy
  rw [Setting.mem_N_iff]
  exact ((Subgroup.mem_centralizer_iff.mp hx.2) y hy)

end SettingFacts

section FamilyW

variable [Finite G] {σ : Setting G} {J W : Subgroup G}

theorem J_le_N (hσ : σ.IsValid) (hJ : σ.IsV21Layer J) : J ≤ σ.N := hJ.le.trans hσ.L₀_le_N

omit [Finite G] in
theorem N_le_normalizer_pCore : σ.N ≤ Subgroup.normalizer (pCoreIn σ.p σ.N : Set G) :=
  DataConstruction.le_normalizer_pCoreIn _ _

theorem odd_card_pCore_N (hσ : σ.IsValid) : Odd (Nat.card (pCoreIn σ.p σ.N)) :=
  Omnibus.odd_card_of_isPGroup hσ.p_prime hσ.p_ne_two (DataConstruction.isPGroup_pCoreIn _ _)

theorem pCore_N_le_ON (hσ : σ.IsValid) : pCoreIn σ.p σ.N ≤ σ.ON :=
  le_oddCoreIn (pCoreIn_le _ _) N_le_normalizer_pCore (odd_card_pCore_N hσ)

theorem W_le_N (hσ : σ.IsValid) (hJ : σ.IsV21Layer J) (hW : W ∈ σ.familyW J) : W ≤ σ.N :=
  hW.1.trans (J_le_N hσ hJ)

theorem T_le_normalizer_W (hσ : σ.IsValid) (hW : W ∈ σ.familyW J) :
    σ.T ≤ Subgroup.normalizer (W : Set G) :=
  (σ.T_le_D hσ).trans hW.2.1

theorem C_inf_pCore_le_oddCoreIn_C (hσ : σ.IsValid) :
    σ.C ⊓ pCoreIn σ.p σ.N ≤ oddCoreIn σ.C := by
  refine le_oddCoreIn inf_le_left ?_
    (odd_card_of_le inf_le_right (odd_card_pCore_N hσ))
  exact (le_inf Subgroup.le_normalizer (σ.C_le_N.trans N_le_normalizer_pCore)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

theorem exists_mul_eq_of_mem_W (hσ : σ.IsValid) (hJ : σ.IsV21Layer J) (hW : W ∈ σ.familyW J)
    {w : G} (hw : w ∈ W) : ∃ c ∈ oddCoreIn σ.C ⊓ J, ∃ k ∈ pCoreIn σ.p σ.N, c * k = w := by
  have hw' : w ∈ oddCoreIn σ.C ⊓ J ⊔ pCoreIn σ.p σ.N := by
    rw [← hW.2.2.2]
    exact Subgroup.mem_sup_left hw
  have hnorm : oddCoreIn σ.C ⊓ J ≤ Subgroup.normalizer (pCoreIn σ.p σ.N : Set G) :=
    (inf_le_right.trans (J_le_N hσ hJ)).trans N_le_normalizer_pCore
  exact (mem_sup_iff_of_le_normalizer hnorm).mp hw'

theorem W_le_C (hσ : σ.IsValid) (hJ : σ.IsV21Layer J) (hW : W ∈ σ.familyW J) : W ≤ σ.C := by
  intro w hw
  rw [Setting.C, Subgroup.mem_centralizer_iff]
  intro t ht
  obtain ⟨c, hc, k, hk, rfl⟩ := exists_mul_eq_of_mem_W hσ hJ hW hw
  have hcC : c ∈ σ.C := oddCoreIn_le σ.C hc.1
  have htc : t * c = c * t := (Subgroup.mem_centralizer_iff.mp hcC) t ht
  have htN : t ∈ σ.N := σ.T_le_N hσ ht
  have h1 : (c * k)⁻¹ * (t * (c * k) * t⁻¹) ∈ W :=
    W.mul_mem (W.inv_mem hw) ((Subgroup.mem_normalizer_iff.mp (T_le_normalizer_W hσ hW ht) _).mp hw)
  have h2 : (c * k)⁻¹ * (t * (c * k) * t⁻¹) ∈ pCoreIn σ.p σ.N := by
    have e : (c * k)⁻¹ * (t * (c * k) * t⁻¹) = k⁻¹ * (t * k * t⁻¹) := by
      calc (c * k)⁻¹ * (t * (c * k) * t⁻¹) = k⁻¹ * c⁻¹ * ((t * c) * k * t⁻¹) := by group
        _ = k⁻¹ * c⁻¹ * ((c * t) * k * t⁻¹) := by rw [htc]
        _ = k⁻¹ * (t * k * t⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hk)
      ((Subgroup.mem_normalizer_iff.mp (N_le_normalizer_pCore htN) k).mp hk)
  have h3 : (c * k)⁻¹ * (t * (c * k) * t⁻¹) ∈ W ⊓ pCoreIn σ.p σ.N := ⟨h1, h2⟩
  rw [hW.2.2.1, Subgroup.mem_bot, inv_mul_eq_one] at h3
  calc t * (c * k) = t * (c * k) * t⁻¹ * t := by group
    _ = c * k * t := by rw [← h3]

theorem W_le_oddCoreIn_C (hσ : σ.IsValid) (hJ : σ.IsV21Layer J) (hW : W ∈ σ.familyW J) :
    W ≤ oddCoreIn σ.C := by
  intro w hw
  obtain ⟨c, hc, k, hk, rfl⟩ := exists_mul_eq_of_mem_W hσ hJ hW hw
  have hcC : c ∈ σ.C := oddCoreIn_le σ.C hc.1
  have hkC : k ∈ σ.C := by
    have : k = c⁻¹ * (c * k) := by group
    rw [this]
    exact σ.C.mul_mem (σ.C.inv_mem hcC) (W_le_C hσ hJ hW hw)
  exact (oddCoreIn σ.C).mul_mem hc.1 (C_inf_pCore_le_oddCoreIn_C hσ ⟨hkC, hk⟩)

theorem odd_card_W (hσ : σ.IsValid) (hJ : σ.IsV21Layer J) (hW : W ∈ σ.familyW J) :
    Odd (Nat.card W) :=
  odd_card_of_le (W_le_oddCoreIn_C hσ hJ hW) (odd_card_oddCoreIn σ.C)

omit [Finite G] in
theorem W_inf_ON (hJ : σ.IsV21Layer J) (hW : W ∈ σ.familyW J) : W ⊓ σ.ON = ⊥ := by
  rw [eq_bot_iff, ← hW.2.2.1]
  intro w hw
  refine ⟨hw.1, ?_⟩
  rw [← hJ.inf_eq]
  exact ⟨hW.1 hw.1, hw.2⟩

omit [Finite G] in
theorem W_le_L (hJ : σ.IsV21Layer J) (hW : W ∈ σ.familyW J) : W ≤ σ.L :=
  hW.1.trans (hJ.le.trans le_sup_left)

omit [Finite G] in
theorem C_le_normalizer_W_sup (hJ : σ.IsV21Layer J) (hW : W ∈ σ.familyW J) :
    σ.C ≤ Subgroup.normalizer ((W ⊔ pCoreIn σ.p σ.N : Subgroup G) : Set G) := by
  rw [hW.2.2.2]
  refine (le_inf (le_inf (le_normalizer_oddCoreIn σ.C) (σ.C_le_N.trans hJ.normal))
    (σ.C_le_N.trans N_le_normalizer_pCore)).trans ?_
  exact (inf_le_inf_right _ Subgroup.inf_normalizer_le_normalizer_inf).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem ON_le_normalizer_W_sup (hσ : σ.IsValid) (hJ : σ.IsV21Layer J) (hW : W ∈ σ.familyW J) :
    σ.ON ≤ Subgroup.normalizer ((W ⊔ pCoreIn σ.p σ.N : Subgroup G) : Set G) := by
  rw [hW.2.2.2]
  intro o ho
  have hnorm : oddCoreIn σ.C ⊓ J ≤ Subgroup.normalizer (pCoreIn σ.p σ.N : Set G) :=
    (inf_le_right.trans (J_le_N hσ hJ)).trans N_le_normalizer_pCore
  apply DataConstruction.mem_normalizer_of_conj_mem
  intro y hy
  obtain ⟨c, hc, k, hk, rfl⟩ := (mem_sup_iff_of_le_normalizer hnorm).mp hy
  have hoN : o ∈ σ.N := σ.ON_le_N ho
  have hcomm : c⁻¹ * o * c * o⁻¹ ∈ pCoreIn σ.p σ.N := by
    apply hJ.commutator_le
    have := Subgroup.commutator_mem_commutator ((J).inv_mem hc.2) ho
    rwa [commutatorElement_def, inv_inv] at this
  have hk' : o * k * o⁻¹ ∈ pCoreIn σ.p σ.N :=
    (Subgroup.mem_normalizer_iff.mp (N_le_normalizer_pCore hoN) k).mp hk
  rw [mem_sup_iff_of_le_normalizer hnorm]
  refine ⟨c, hc, (c⁻¹ * o * c * o⁻¹) * (o * k * o⁻¹), Subgroup.mul_mem _ hcomm hk', ?_⟩
  group

theorem mul_comm_W_of_isSylowOf (hσ : σ.IsValid) (hJ : σ.IsV21Layer J) (hW : W ∈ σ.familyW J)
    {P : Subgroup G} (hP : IsSylowOf σ.p P σ.C) :
    (P : Set G) * (W : Set G) = (W : Set G) * (P : Set G) := by
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  set Op := pCoreIn σ.p σ.N with hOp
  set B : Subgroup G := σ.C ⊓ (W ⊔ Op) with hB
  have hWC := W_le_C hσ hJ hW
  have hWN : W ≤ Subgroup.normalizer (Op : Set G) := (W_le_N hσ hJ hW).trans N_le_normalizer_pCore
  have hCB : σ.C ≤ Subgroup.normalizer (B : Set G) :=
    (le_inf Subgroup.le_normalizer (C_le_normalizer_W_sup hJ hW)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hPB : P ≤ Subgroup.normalizer (B : Set G) := hP.le.trans hCB
  have hCOp : σ.C ⊓ Op ≤ P := by
    refine le_trans ?_ (Omnibus.pCoreIn_le_of_isSylowOf hP)
    refine DataConstruction.le_pCoreIn inf_le_left ?_
      ((DataConstruction.isPGroup_pCoreIn _ _).to_le inf_le_right)
    exact (le_inf Subgroup.le_normalizer (σ.C_le_N.trans N_le_normalizer_pCore)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hBmem : ∀ b ∈ B, ∃ w ∈ W, ∃ k ∈ σ.C ⊓ Op, w * k = b := by
    intro b hb
    obtain ⟨w, hw, k, hk, rfl⟩ := (mem_sup_iff_of_le_normalizer hWN).mp hb.2
    refine ⟨w, hw, k, ⟨?_, hk⟩, rfl⟩
    have : k = w⁻¹ * (w * k) := by group
    rw [this]
    exact σ.C.mul_mem (σ.C.inv_mem (hWC hw)) hb.1
  have hWB : W ≤ B := fun w hw => ⟨hWC hw, Subgroup.mem_sup_left hw⟩
  have h1 : ((B ⊔ P : Subgroup G) : Set G) = (W : Set G) * (P : Set G) := by
    rw [Subgroup.coe_mul_of_right_le_normalizer_left B P hPB]
    apply Set.Subset.antisymm
    · rintro _ ⟨b, hb, x, hx, rfl⟩
      obtain ⟨w, hw, k, hk, rfl⟩ := hBmem b hb
      exact ⟨w, hw, k * x, P.mul_mem (hCOp hk) hx, by simp only [mul_assoc]⟩
    · rintro _ ⟨w, hw, x, hx, rfl⟩
      exact ⟨w, hWB hw, x, hx, rfl⟩
  have h2 : ((P ⊔ B : Subgroup G) : Set G) = (P : Set G) * (W : Set G) := by
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P B hPB]
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, b, hb, rfl⟩
      obtain ⟨w, hw, k, hk, rfl⟩ := hBmem b hb
      have hk' : w * k * w⁻¹ ∈ σ.C ⊓ Op :=
        ⟨σ.C.mul_mem (σ.C.mul_mem (hWC hw) hk.1) (σ.C.inv_mem (hWC hw)),
          (Subgroup.mem_normalizer_iff.mp (hWN hw) k).mp hk.2⟩
      refine ⟨x * (w * k * w⁻¹), P.mul_mem hx (hCOp hk'), w, hw, ?_⟩
      group
    · rintro _ ⟨x, hx, w, hw, rfl⟩
      exact ⟨x, hx, w, hWB hw, rfl⟩
  rw [← h1, ← h2, sup_comm]

theorem coprime_card_of_two_of_odd {A M : Subgroup G} (hA : IsPGroup 2 A)
    (hM : Odd (Nat.card M)) : Nat.Coprime (Nat.card A) (Nat.card M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hA
  rw [hb]
  exact Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hM)

theorem isSolvable_pCore_N (hσ : σ.IsValid) : Group.IsSolvable (pCoreIn σ.p σ.N) := by
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  have := (DataConstruction.isPGroup_pCoreIn σ.p σ.N).isNilpotent
  infer_instance

theorem exists_mul_eq_of_mem_C_inf_L₀ (hσ : σ.IsValid) (hJ : σ.IsV21Layer J) {z : G}
    (hzC : z ∈ σ.C) (hzL : z ∈ σ.L₀) : ∃ j ∈ σ.C ⊓ J, ∃ o ∈ σ.ON, j * o = z := by
  have hJON : J ≤ Subgroup.normalizer (σ.ON : Set G) := (J_le_N hσ hJ).trans σ.N_le_normalizer_ON
  rw [hJ.sup_eq] at hzL
  obtain ⟨j₀, hj₀, o₀, ho₀, rfl⟩ := (mem_sup_iff_of_le_normalizer hJON).mp hzL
  have hTOp : σ.T ≤ Subgroup.normalizer (pCoreIn σ.p σ.N : Set G) :=
    (σ.T_le_N hσ).trans N_le_normalizer_pCore
  have hcop : Nat.Coprime (Nat.card σ.T) (Nat.card (pCoreIn σ.p σ.N)) :=
    coprime_card_of_two_of_odd (isPGroup_T hσ) (odd_card_pCore_N hσ)
  have hfix : ∀ t ∈ σ.T, j₀⁻¹ * (t * j₀ * t⁻¹) ∈ pCoreIn σ.p σ.N := by
    intro t ht
    have htN : t ∈ σ.N := σ.T_le_N hσ ht
    have htz : t * (j₀ * o₀) * t⁻¹ = j₀ * o₀ :=
      by rw [(Subgroup.mem_centralizer_iff.mp hzC t ht)]; group
    rw [← hJ.inf_eq]
    refine ⟨J.mul_mem (J.inv_mem hj₀) ((Subgroup.mem_normalizer_iff.mp (hJ.normal htN) j₀).mp hj₀),
      ?_⟩
    have e : j₀⁻¹ * (t * j₀ * t⁻¹) = o₀ * (t * o₀ * t⁻¹)⁻¹ := by
      calc j₀⁻¹ * (t * j₀ * t⁻¹) = j₀⁻¹ * (t * (j₀ * o₀) * t⁻¹) * (t * o₀ * t⁻¹)⁻¹ := by group
        _ = o₀ * (t * o₀ * t⁻¹)⁻¹ := by rw [htz]; group
    rw [e]
    exact σ.ON.mul_mem ho₀ (σ.ON.inv_mem
      ((Subgroup.mem_normalizer_iff.mp (σ.N_le_normalizer_ON htN) o₀).mp ho₀))
  obtain ⟨n, hn, hjn⟩ :=
    exists_mul_mem_centralizer_of_coprime hTOp (isSolvable_pCore_N hσ) hcop hfix
  refine ⟨j₀ * n, ⟨hjn, J.mul_mem hj₀ (hJ.pCore_le hn)⟩, n⁻¹ * o₀,
    σ.ON.mul_mem (σ.ON.inv_mem (pCore_N_le_ON hσ hn)) ho₀, by group⟩

end FamilyW

end CFSG.ABGTheoremB.V4
