module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Open CFSG.SectionRank

section Lift

variable {L : Type*} [Group L]

theorem exists_cube_adjust {a N z w : L} (hz : ∀ g, g * z = z * g) (hw : ∀ g, g * w = w * g)
    (h1 : N * a * N⁻¹ = z * a⁻¹) (h3 : a ^ 3 = w) : (a * (w⁻¹ * z)) ^ 3 = 1 := by
  have hzc : Commute z a⁻¹ := (hz a⁻¹).symm
  have e1 : N * a ^ 3 * N⁻¹ = (N * a * N⁻¹) ^ 3 := (conj_pow).symm
  rw [h1, hzc.mul_pow, h3, inv_pow, h3] at e1
  have e2 : N * w * N⁻¹ = w := by rw [hw N]; group
  rw [e2] at e1
  have hww : w * w = z ^ 3 := by
    calc w * w = (z ^ 3 * w⁻¹) * w := by rw [← e1]
      _ = z ^ 3 := by group
  have hu : Commute w⁻¹ z := by
    have := hw z
    exact ((Commute.inv_left (show Commute w z from (hw z).symm)))
  have hau : Commute a (w⁻¹ * z) := by
    have h : ∀ g, Commute g w⁻¹ := fun g => (Commute.inv_right (hw g))
    exact (h a).mul_right (hz a)
  rw [hau.mul_pow, h3, hu.mul_pow, ← hww]
  group

theorem comm_eq_one_of_reflection {a b N y₁ y₂ : L} {k : ℤ}
    (hy₁ : ∀ g, g * y₁ = y₁ * g) (hy₂ : ∀ g, g * y₂ = y₂ * g)
    (hc : ∀ g, g * (a * b * a⁻¹ * b⁻¹) = (a * b * a⁻¹ * b⁻¹) * g) (ha3 : a ^ 3 = 1)
    (h1 : N * a * N⁻¹ = y₁ * a⁻¹) (h2 : N * b * N⁻¹ = b * a ^ k * y₂) :
    a * b * a⁻¹ * b⁻¹ = 1 := by
  set c := a * b * a⁻¹ * b⁻¹ with hcdef
  have hNc : N * c * N⁻¹ = c := by rw [hc N]; group
  have hconj : N * c * N⁻¹ = (N * a * N⁻¹) * (N * b * N⁻¹) * (N * a * N⁻¹)⁻¹ *
      (N * b * N⁻¹)⁻¹ := by
    simp only [hcdef]; group
  rw [h1, h2] at hconj
  have key : (y₁ * a⁻¹) * (b * a ^ k * y₂) * (y₁ * a⁻¹)⁻¹ * (b * a ^ k * y₂)⁻¹ =
      a⁻¹ * b * a * b⁻¹ := by
    have e1 : (y₁ * a⁻¹) * (b * a ^ k * y₂) * (y₁ * a⁻¹)⁻¹ * (b * a ^ k * y₂)⁻¹ =
        y₁ * (a⁻¹ * (b * a ^ k) * (y₂ * (a * y₁⁻¹) * y₂⁻¹) * (a ^ k)⁻¹ * b⁻¹) := by group
    have e2 : y₂ * (a * y₁⁻¹) * y₂⁻¹ = a * y₁⁻¹ := by
      have : y₂ * (a * y₁⁻¹) = (a * y₁⁻¹) * y₂ := (hy₂ _).symm
      rw [this]; group
    have e3 : a⁻¹ * (b * a ^ k) * (a * y₁⁻¹) * (a ^ k)⁻¹ * b⁻¹ =
        y₁⁻¹ * (a⁻¹ * (b * a ^ k) * a * ((a ^ k)⁻¹ * b⁻¹)) := by
      have h : ∀ x : L, x * y₁⁻¹ = y₁⁻¹ * x := fun x => by
        have := hy₁ x
        calc x * y₁⁻¹ = y₁⁻¹ * (y₁ * x) * y₁⁻¹ := by group
          _ = y₁⁻¹ * (x * y₁) * y₁⁻¹ := by rw [this]
          _ = y₁⁻¹ * x := by group
      calc a⁻¹ * (b * a ^ k) * (a * y₁⁻¹) * (a ^ k)⁻¹ * b⁻¹
          = (a⁻¹ * (b * a ^ k) * a) * y₁⁻¹ * ((a ^ k)⁻¹ * b⁻¹) := by group
        _ = y₁⁻¹ * (a⁻¹ * (b * a ^ k) * a * ((a ^ k)⁻¹ * b⁻¹)) := by
            rw [h (a⁻¹ * (b * a ^ k) * a), mul_assoc]
    rw [e1, e2, e3]
    group
  rw [key, hNc] at hconj
  have hcinv : c * c = 1 := by
    have : a⁻¹ * b * a * b⁻¹ = a⁻¹ * (b * a * b⁻¹ * a⁻¹) * a := by group
    have h' : b * a * b⁻¹ * a⁻¹ = c⁻¹ := by simp only [hcdef]; group
    rw [this, h'] at hconj
    have hc' : ∀ g, g * c⁻¹ = c⁻¹ * g := fun g => by
      calc g * c⁻¹ = c⁻¹ * (c * g) * c⁻¹ := by group
        _ = c⁻¹ * (g * c) * c⁻¹ := by rw [hc g]
        _ = c⁻¹ * g := by group
    have h2 : a⁻¹ * c⁻¹ * a = c⁻¹ := by rw [hc' a⁻¹]; group
    exact mul_eq_one_iff_eq_inv.2 (hconj.trans h2)
  have hab : ∀ n : ℕ, a ^ n * b = c ^ n * b * a ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      calc a ^ (m + 1) * b = a * (a ^ m * b) := by group
        _ = a * (c ^ m * b * a ^ m) := by rw [ih]
        _ = c ^ m * (a * b) * a ^ m := by
            have hcm : ∀ g, g * c ^ m = c ^ m * g := fun g => (Commute.pow_right (hc g) m)
            rw [← mul_assoc, ← mul_assoc, hcm a]; group
        _ = c ^ m * (c * b * a) * a ^ m := by simp only [hcdef]; group
        _ = c ^ (m + 1) * b * a ^ (m + 1) := by
            have hcm : ∀ g, g * c ^ m = c ^ m * g := fun g => (Commute.pow_right (hc g) m)
            calc c ^ m * (c * b * a) * a ^ m = (c ^ m * c) * b * a * a ^ m := by group
              _ = c ^ (m + 1) * b * a ^ (m + 1) := by group
  have hc3 : c ^ 3 = 1 := by
    have h := hab 3
    rw [ha3, one_mul] at h
    simp only [mul_one] at h
    have : c ^ 3 * b = b := by
      calc c ^ 3 * b = c ^ 3 * b * 1 := by group
        _ = b := by rw [← h]; group
    simpa using this
  calc c = c ^ 3 * (c * c)⁻¹ := by group
    _ = 1 := by rw [hc3, hcinv]; group

end Lift

section Main

variable {L Q : Type*} [Group L] [Group Q]

theorem exists_elemAbelian_of_reflection_lifts (π : L →* Q) (hπ : Function.Surjective π)
    (hc : ∀ x, π x = 1 → x ∈ Subgroup.center L) {ι : Type*} (e n : ι → Q)
    (hcomm : ∀ i j, e i * e j = e j * e i) (he : ∀ i, e i ^ 3 = 1)
    (hinv : ∀ i, n i * e i * (n i)⁻¹ = (e i)⁻¹)
    (hrel : ∀ i j, ∃ k : ℤ, n i * e j * (n i)⁻¹ = e j * e i ^ k) :
    ∃ R : Subgroup L, (∀ x ∈ R, x ^ 3 = 1) ∧ (∀ x ∈ R, ∀ y ∈ R, x * y = y * x) ∧
      R.map π = Subgroup.closure (Set.range e) := by
  have hcen : ∀ x, π x = 1 → ∀ g, g * x = x * g := fun x hx g =>
    Subgroup.mem_center_iff.1 (hc x hx) g
  choose a₀ ha₀ using fun i => hπ (e i)
  choose N hN using fun i => hπ (n i)
  have hcor : ∀ i, ∃ a : L, π a = e i ∧ a ^ 3 = 1 := by
    intro i
    set z := N i * a₀ i * (N i)⁻¹ * a₀ i with hz
    set w := a₀ i ^ 3 with hw
    have hπz : π z = 1 := by
      simp only [hz, map_mul, map_inv, hN, ha₀, hinv, inv_mul_cancel]
    have hπw : π w = 1 := by simp only [hw, map_pow, ha₀, he]
    have hu : π (w⁻¹ * z) = 1 := by rw [map_mul, map_inv, hπw, hπz]; simp
    refine ⟨a₀ i * (w⁻¹ * z), by rw [map_mul, hu, ha₀, mul_one], ?_⟩
    exact exists_cube_adjust (hcen z hπz) (hcen w hπw)
      (a := a₀ i) (N := N i) (by simp only [hz]; group) rfl
  choose a ha ha3 using hcor
  have hpair : ∀ i j, a i * a j = a j * a i := by
    intro i j
    obtain ⟨k, hk⟩ := hrel i j
    set y₁ := N i * a i * (N i)⁻¹ * a i with hy₁
    set y₂ := (a j * a i ^ k)⁻¹ * (N i * a j * (N i)⁻¹) with hy₂
    have hπy₁ : π y₁ = 1 := by
      simp only [hy₁, map_mul, map_inv, hN, ha, hinv, inv_mul_cancel]
    have hπy₂ : π y₂ = 1 := by
      simp only [hy₂, map_mul, map_inv, map_zpow, hN, ha]
      rw [hk]; group
    have hcc : π (a i * a j * (a i)⁻¹ * (a j)⁻¹) = 1 := by
      simp only [map_mul, map_inv, ha]
      rw [hcomm i j]; group
    have := comm_eq_one_of_reflection (hcen y₁ hπy₁) (hcen y₂ hπy₂) (hcen _ hcc) (ha3 i)
      (a := a i) (b := a j) (N := N i) (k := k) (by simp only [hy₁]; group)
      (by simp only [hy₂]; group)
    calc a i * a j = a i * a j * (a i)⁻¹ * (a j)⁻¹ * (a j * a i) := by group
      _ = a j * a i := by rw [this, one_mul]
  have hcommS : ∀ x ∈ Set.range a, ∀ y ∈ Set.range a, x * y = y * x := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hpair i j
  have hpw : (Set.range a).Pairwise Commute := fun x hx y hy _ => hcommS x hx y hy
  have hcl := Subgroup.isMulCommutative_closure hpw
  have hRc : ∀ x ∈ Subgroup.closure (Set.range a), ∀ y ∈ Subgroup.closure (Set.range a),
      x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcl.is_comm.comm (⟨x, hx⟩ : Subgroup.closure (Set.range a)) ⟨y, hy⟩)
  refine ⟨Subgroup.closure (Set.range a), ?_, hRc, ?_⟩
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact ha3 i
    | one => simp
    | mul x y hx hy hx3 hy3 =>
      have := hRc x hx y hy
      rw [(show Commute x y from this).mul_pow, hx3, hy3, one_mul]
    | inv x hx hx3 => rw [inv_pow, hx3, inv_one]
  · rw [MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, (ha i).symm⟩
    · rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, ha i⟩

theorem pRank_ge_of_lift [Finite L] (π : L →* Q)
    (hker : ∀ x, π x = 1 ↔ x ∈ Subgroup.center L) (R : Subgroup L)
    (hR3 : ∀ x ∈ R, x ^ 3 = 1) (hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x)
    (hZ : 3 ∣ Nat.card (Subgroup.center L)) {m : ℕ} (hD : 3 ^ m ≤ Nat.card (R.map π)) :
    m + 1 ≤ pRank 3 (⊤ : Subgroup L) := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) 3 hZ
  set z : L := (x : L) with hzdef
  have hzc : z ∈ Subgroup.center L := x.2
  have hzo : orderOf z = 3 := by
    rw [hzdef, Subgroup.orderOf_coe]; exact hx
  set Z : Subgroup L := Subgroup.zpowers z with hZdef
  have hZc : Z ≤ Subgroup.center L := (Subgroup.zpowers_le).2 hzc
  have hZcen : ∀ w ∈ Z, ∀ g : L, g * w = w * g := fun w hw g =>
    Subgroup.mem_center_iff.1 (hZc hw) g
  haveI : Z.Normal := ⟨fun n hn g => by
    rw [hZcen n hn g, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hZ3 : ∀ w ∈ Z, w ^ 3 = 1 := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  set R' : Subgroup L := R ⊔ Z with hR'
  have hmem : ∀ x ∈ R', ∃ y ∈ R, ∃ w ∈ Z, y * w = x := fun x hx =>
    Subgroup.mem_sup_of_normal_right.1 hx
  have hR'3 : ∀ x ∈ R', x ^ 3 = 1 := by
    intro x hx
    obtain ⟨y, hy, w, hw, rfl⟩ := hmem x hx
    have hcw : Commute y w := hZcen w hw y
    rw [hcw.mul_pow, hR3 y hy, hZ3 w hw, one_mul]
  have hR'c : ∀ x ∈ R', ∀ y ∈ R', x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, w, hw, rfl⟩ := hmem x hx
    obtain ⟨b, hb, v, hv, rfl⟩ := hmem y hy
    calc a * w * (b * v) = a * b * (w * v) := by
          rw [show a * w * (b * v) = a * (w * b) * v by group, ← hZcen w hw b]; group
      _ = b * a * (v * w) := by rw [hRc a ha b hb, ← hZcen w hw v]
      _ = b * v * (a * w) := by
          rw [show b * a * (v * w) = b * (a * v) * w by group, hZcen v hv a]; group
  have hPG : IsPGroup 3 R' := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hR'3 g g.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (G := R')).1 hPG
  have hψ : Nat.card ((π.comp R'.subtype).ker) * Nat.card (π.comp R'.subtype).range =
      Nat.card R' := Subgroup.card_ker_mul_card_range _
  have hrange : (π.comp R'.subtype).range = R.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hR', Subgroup.map_sup]
    have : Z.map π = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨w, hw, rfl⟩
      rw [Subgroup.mem_bot]
      exact (hker w).2 (hZc hw)
    rw [this, sup_bot_eq]
  have hker3 : 3 ≤ Nat.card ((π.comp R'.subtype).ker) := by
    have hle : Z.subgroupOf R' ≤ (π.comp R'.subtype).ker := by
      intro w hw
      rw [MonoidHom.mem_ker]
      exact (hker _).2 (hZc hw)
    have hZR' : Z ≤ R' := le_sup_right
    have hcZ : Nat.card (Z.subgroupOf R') = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR').toEquiv, hZdef,
        Nat.card_zpowers, hzo]
    rw [← hcZ]
    exact Nat.card_mono (Set.toFinite _) hle
  rw [hrange] at hψ
  have hbig : 3 ^ (m + 1) ≤ Nat.card R' := by
    rw [← hψ, pow_succ, mul_comm]
    exact Nat.mul_le_mul hker3 hD
  rw [hk] at hbig
  have hmk : m + 1 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).1 hbig
  refine hmk.trans (le_pRank (by norm_num) le_top ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => hR'3 y hy⟩ hk)
  exact Subtype.ext (hR'c a a.2 b b.2)

end Main

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
