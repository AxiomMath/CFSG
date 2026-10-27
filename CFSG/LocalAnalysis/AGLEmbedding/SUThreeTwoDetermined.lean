module

public import CFSG.LocalAnalysis.AGLEmbedding.SUPairInvolution
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding.SUDet

open Subgroup
open CFSG.AGLEmbedding.SUPair (Heis27)

variable {Y : Type} [Group Y] [Finite Y]

theorem eq_one_of_conj_eq_mul {c x a : Y} (hcx : c * x * c⁻¹ = a * x) (hca : c * a = a * c)
    {m : ℕ} (hc : c ^ (2 ^ m) = 1) (ha : a ^ 3 = 1) : a = 1 := by
  have hk : ∀ k : ℕ, c ^ k * x * (c ^ k)⁻¹ = a ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hck : c ^ k * a = a * c ^ k := (Commute.pow_left hca k).eq
      calc c ^ (k + 1) * x * (c ^ (k + 1))⁻¹ = c * (c ^ k * x * (c ^ k)⁻¹) * c⁻¹ := by
              rw [pow_succ', mul_inv_rev]; group
        _ = c * (a ^ k * x) * c⁻¹ := by rw [ih]
        _ = a ^ k * (c * x * c⁻¹) := by
              rw [show c * (a ^ k * x) * c⁻¹ = (c * a ^ k) * x * c⁻¹ by group,
                (Commute.pow_right hca k).eq]; group
        _ = a ^ (k + 1) * x := by rw [hcx, pow_succ]; group
  have h1 := hk (2 ^ m)
  rw [hc, one_mul, inv_one, mul_one] at h1
  have h2 : a ^ (2 ^ m) = 1 := by
    have := congrArg (· * x⁻¹) h1
    simpa using this.symm
  have hco : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left m (by norm_num)
  have := (pow_gcd_eq_one (a := a) (m := 2 ^ m) (n := 3)).mpr ⟨h2, ha⟩
  rwa [Nat.Coprime.gcd_eq_one hco, pow_one] at this

structure Good (D A Z S : Subgroup Y) (y : Y) : Prop where
  mem : y ∈ S
  normA : ∀ a ∈ A, y * a * y⁻¹ ∈ A
  normA' : ∀ a ∈ A, y⁻¹ * a * y ∈ A
  centZ : ∀ z ∈ Z, y * z = z * y
  trivD : ∀ d ∈ D, y * d * y⁻¹ * d⁻¹ ∈ A
  inv : ∀ a ∈ A, y ^ 2 * a * (y ^ 2)⁻¹ * a ∈ Z

variable {D A Z S : Subgroup Y}

theorem mem_of_zpow_mem {s : Y} (hs3 : s ^ 3 = 1) {n : ℤ} (hn : (n : ZMod 3) ≠ 0)
    (h : s ^ n ∈ Z) : s ∈ Z := by
  have h2 : s ^ (n * n) ∈ Z := by rw [zpow_mul]; exact zpow_mem h n
  have hmod : (n * n) % 3 = 1 := by
    have : ((n * n : ℤ) : ZMod 3) = 1 := by
      push_cast
      generalize (n : ZMod 3) = x at hn ⊢
      revert x; decide
    have h' := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (n * n) 3).mp (by simpa using this.symm)
    omega
  have hs : s ^ (n * n) = s := by
    have he : n * n = 3 * ((n * n) / 3) + 1 := by omega
    rw [he, zpow_add, zpow_mul, show (3 : ℤ) = (3 : ℕ) by rfl,
      zpow_natCast, hs3, one_zpow, one_mul, zpow_one]
  rwa [hs] at h2

theorem not_mem_of_good (hH : Heis27 A Z) {y : Y} (hy : Good D A Z S y) {s : Y} (hs : s ∈ A)
    (hsZ : s ∉ Z) (k : ℤ) : (s ^ k)⁻¹ * (y * s * y⁻¹) ∉ Z := by
  intro hz
  set z := (s ^ k)⁻¹ * (y * s * y⁻¹) with hzdef
  have hzA : z ∈ A := hH.le hz
  have hys : y * s * y⁻¹ = s ^ k * z := by rw [hzdef]; group
  have hcen : ∀ a ∈ A, z * a = a * z := fun a ha => hH.central z hz a ha
  have hyz : y * z * y⁻¹ = z := by rw [hy.centZ z hz]; group
  have hy2 : y ^ 2 * s * (y ^ 2)⁻¹ = s ^ (k * k) * z ^ (k + 1) := by
    have h1 : y ^ 2 * s * (y ^ 2)⁻¹ = y * (s ^ k * z) * y⁻¹ := by rw [← hys, sq]; group
    have h2 : y * (s ^ k * z) * y⁻¹ = (y * s * y⁻¹) ^ k * (y * z * y⁻¹) := by
      rw [conj_zpow]; group
    rw [h1, h2, hys, hyz]
    have hc : Commute z s := hcen s hs
    rw [(hc.symm.zpow_left k).mul_zpow, ← zpow_mul, mul_assoc, ← zpow_add_one]
  have hinv := hy.inv s hs
  rw [hy2] at hinv
  have hmem : s ^ (k * k + 1) ∈ Z := by
    have e : s ^ (k * k) * z ^ (k + 1) * s = s ^ (k * k + 1) * z ^ (k + 1) := by
      have hc : Commute (z ^ (k + 1)) s := (show Commute z s from hcen s hs).zpow_left (k + 1)
      rw [mul_assoc, hc.eq, ← mul_assoc, ← zpow_add_one]
    rw [e] at hinv
    have := Z.mul_mem hinv (Z.inv_mem (zpow_mem hz (k + 1)))
    simpa using this
  have hn : ((k * k + 1 : ℤ) : ZMod 3) ≠ 0 := by
    push_cast
    generalize (k : ZMod 3) = x
    revert x; decide
  exact hsZ (mem_of_zpow_mem (hH.cube s hs) hn hmem)

theorem eq_of_good (hH : Heis27 A Z) [D.Normal] (hS : IsPGroup 2 S)
    (hCS : ∀ c ∈ S, (∀ d ∈ D, c * d = d * c) → c = 1) {y y' : Y} (hy : Good D A Z S y)
    (hy' : Good D A Z S y') {s : Y} (hs : s ∈ A) (hsZ : s ∉ Z)
    (h : (y * s * y⁻¹)⁻¹ * (y' * s * y'⁻¹) ∈ Z) : y = y' := by
  set c := y'⁻¹ * y with hcdef
  have hcS : c ∈ S := S.mul_mem (S.inv_mem hy'.mem) hy.mem
  obtain ⟨m, hm⟩ := hS ⟨c, hcS⟩
  have hcm : c ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
  have hcen : ∀ z ∈ Z, ∀ a ∈ A, z * a = a * z := hH.central
  have hy'z : ∀ z ∈ Z, y'⁻¹ * z * y' = z := fun z hz => by
    rw [show y'⁻¹ * z * y' = y'⁻¹ * (z * y') by group, ← hy'.centZ z hz]; group
  have hcA : ∀ a ∈ A, c * a * c⁻¹ ∈ A := fun a ha => by
    have := hy'.normA' _ (hy.normA a ha)
    rw [show c * a * c⁻¹ = y'⁻¹ * (y * a * y⁻¹) * y' by rw [hcdef]; group]
    exact this
  have hcZ : ∀ z ∈ Z, c * z = z * c := fun z hz => by
    have h1 : y * z = z * y := hy.centZ z hz
    have h2 : y'⁻¹ * z = z * y'⁻¹ := by
      have := hy'.centZ z hz
      calc y'⁻¹ * z = y'⁻¹ * (z * y') * y'⁻¹ := by group
        _ = y'⁻¹ * (y' * z) * y'⁻¹ := by rw [this]
        _ = z * y'⁻¹ := by group
    calc c * z = y'⁻¹ * (y * z) := by rw [hcdef]; group
      _ = y'⁻¹ * (z * y) := by rw [h1]
      _ = (y'⁻¹ * z) * y := by group
      _ = z * y'⁻¹ * y := by rw [h2]
      _ = z * c := by rw [hcdef]; group
  obtain ⟨z₀, hz₀Z, hz₀⟩ : ∃ z ∈ Z, y' * s * y'⁻¹ = (y * s * y⁻¹) * z := ⟨_, h, by group⟩
  obtain ⟨z₁, hz₁Z, hz₁⟩ : ∃ z ∈ Z, y ^ 2 * s * (y ^ 2)⁻¹ = z * s⁻¹ :=
    ⟨_, hy.inv s hs, by group⟩
  obtain ⟨z₂, hz₂Z, hz₂⟩ : ∃ z ∈ Z, y' ^ 2 * s * (y' ^ 2)⁻¹ = z * s⁻¹ :=
    ⟨_, hy'.inv s hs, by group⟩
  have hfs : c * s * c⁻¹ * s⁻¹ ∈ Z := by
    have k0 : y * s * y⁻¹ = y' * s * y'⁻¹ * z₀⁻¹ := by rw [hz₀]; group
    have e : c * s * c⁻¹ = s * (y'⁻¹ * z₀⁻¹ * y') := by
      calc c * s * c⁻¹ = y'⁻¹ * (y * s * y⁻¹) * y' := by rw [hcdef]; group
        _ = y'⁻¹ * (y' * s * y'⁻¹ * z₀⁻¹) * y' := by rw [k0]
        _ = s * (y'⁻¹ * z₀⁻¹ * y') := by group
    rw [e, hy'z _ (Z.inv_mem hz₀Z)]
    have : s * z₀⁻¹ * s⁻¹ = z₀⁻¹ := by rw [← hcen _ (Z.inv_mem hz₀Z) s hs]; group
    rw [this]
    exact Z.inv_mem hz₀Z
  have hwA : y * s * y⁻¹ ∈ A := hy.normA s hs
  have hfw : c * (y * s * y⁻¹) * c⁻¹ * (y * s * y⁻¹)⁻¹ ∈ Z := by
    have k1 : y'⁻¹ * s⁻¹ * y' = z₂⁻¹ * (y' * s * y'⁻¹) := by
      have hs' : s⁻¹ = z₂⁻¹ * (y' ^ 2 * s * (y' ^ 2)⁻¹) := by rw [hz₂]; group
      calc y'⁻¹ * s⁻¹ * y' = y'⁻¹ * (z₂⁻¹ * (y' ^ 2 * s * (y' ^ 2)⁻¹)) * y' := by rw [← hs']
        _ = (y'⁻¹ * z₂⁻¹ * y') * (y' * s * y'⁻¹) := by simp only [sq]; group
        _ = z₂⁻¹ * (y' * s * y'⁻¹) := by rw [hy'z _ (Z.inv_mem hz₂Z)]
    have k2 : c * (y * s * y⁻¹) * c⁻¹ = z₁ * (y'⁻¹ * s⁻¹ * y') := by
      calc c * (y * s * y⁻¹) * c⁻¹ = y'⁻¹ * (y ^ 2 * s * (y ^ 2)⁻¹) * y' := by
            rw [hcdef]; simp only [sq]; group
        _ = y'⁻¹ * (z₁ * s⁻¹) * y' := by rw [hz₁]
        _ = (y'⁻¹ * z₁ * y') * (y'⁻¹ * s⁻¹ * y') := by group
        _ = z₁ * (y'⁻¹ * s⁻¹ * y') := by rw [hy'z _ hz₁Z]
    have k3 : (y * s * y⁻¹) * z₀ * (y * s * y⁻¹)⁻¹ = z₀ := by
      rw [← hcen z₀ hz₀Z _ hwA]; group
    have e : c * (y * s * y⁻¹) * c⁻¹ * (y * s * y⁻¹)⁻¹ =
        z₁ * z₂⁻¹ * ((y * s * y⁻¹) * z₀ * (y * s * y⁻¹)⁻¹) := by
      rw [k2, k1, hz₀]; group
    rw [e, k3]
    exact Z.mul_mem (Z.mul_mem hz₁Z (Z.inv_mem hz₂Z)) hz₀Z
  let F : Subgroup Y :=
    { carrier := {a | a ∈ A ∧ c * a * c⁻¹ * a⁻¹ ∈ Z}
      one_mem' := ⟨A.one_mem, by simp [Z.one_mem]⟩
      mul_mem' := by
        rintro a b ⟨ha, hza⟩ ⟨hb, hzb⟩
        refine ⟨A.mul_mem ha hb, ?_⟩
        have e : c * (a * b) * c⁻¹ * (a * b)⁻¹ =
            (c * a * c⁻¹) * (c * b * c⁻¹ * b⁻¹) * a⁻¹ := by group
        rw [e, ← hcen _ hzb _ (hcA a ha), mul_assoc]
        exact Z.mul_mem hzb hza
      inv_mem' := by
        rintro a ⟨ha, hza⟩
        refine ⟨A.inv_mem ha, ?_⟩
        have e : c * a⁻¹ * c⁻¹ * a⁻¹⁻¹ = a⁻¹ * (c * a * c⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [e, mul_assoc, hcen _ (Z.inv_mem hza) a ha, ← mul_assoc, inv_mul_cancel, one_mul]
        exact Z.inv_mem hza }
  have hFA : F ≤ A := fun a ha => ha.1
  have hZF : Z ≤ F := fun z hz => ⟨hH.le hz, by
    have : c * z * c⁻¹ * z⁻¹ = 1 := by rw [hcZ z hz]; group
    rw [this]; exact Z.one_mem⟩
  have hsF : s ∈ F := ⟨hs, hfs⟩
  have hwF : y * s * y⁻¹ ∈ F := ⟨hwA, hfw⟩
  have hFcard : Nat.card F = 27 := by
    have hdvd : Nat.card F ∣ 27 := hH.card ▸ card_dvd_of_le hFA
    have hZcard : Nat.card Z = 3 := hH.card_center
    have h3 : 3 ∣ Nat.card F := hZcard ▸ card_dvd_of_le hZF
    have hne3 : Nat.card F ≠ 3 := by
      intro h3'
      have : Z = F := eq_of_le_of_card_ge hZF (by rw [h3', hZcard])
      exact hsZ (this ▸ hsF)
    have hne9 : Nat.card F ≠ 9 := by
      intro h9
      set ZF := Z.subgroupOf F
      haveI : ZF.Normal := ⟨fun n hn g => by
        rw [mem_subgroupOf] at hn ⊢
        have : (g : Y) * n * (g : Y)⁻¹ = n := by
          rw [← hcen _ hn _ (hFA g.2)]; group
        simpa [this] using hn⟩
      have hq := card_eq_card_quotient_mul_card_subgroup ZF
      rw [h9, Nat.card_congr (subgroupOfEquivOfLe hZF).toEquiv, hZcard] at hq
      have hq3 : Nat.card (↥F ⧸ ZF) = 3 := by omega
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hsq : (QuotientGroup.mk (⟨s, hsF⟩ : ↥F) : ↥F ⧸ ZF) ≠ 1 := by
        rw [Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
        exact hsZ
      have htop := zpowers_eq_top_of_prime_card hq3 hsq
      have hwq : (QuotientGroup.mk (⟨y * s * y⁻¹, hwF⟩ : ↥F) : ↥F ⧸ ZF) ∈
          zpowers (QuotientGroup.mk (⟨s, hsF⟩ : ↥F) : ↥F ⧸ ZF) := by
        rw [htop]; exact mem_top _
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hwq
      rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, mem_subgroupOf] at hk
      apply not_mem_of_good hH hy hs hsZ k
      simpa using hk
    have h27 : Nat.card F = 1 ∨ Nat.card F = 3 ∨ Nat.card F = 9 ∨ Nat.card F = 27 := by
      have : Nat.card F ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hd : Nat.divisors 27 = {1, 3, 9, 27} := by decide
      rw [hd] at this
      simpa using this
    rcases h27 with h1 | h1 | h1 | h1
    · rw [h1] at h3; norm_num at h3
    · exact absurd h1 hne3
    · exact absurd h1 hne9
    · exact h1
  have hAF : A ≤ F := by
    have := eq_of_le_of_card_ge hFA (by rw [hFcard, hH.card])
    rw [this]
  have hcA' : ∀ a ∈ A, c * a * c⁻¹ = a := by
    intro a ha
    set z := c * a * c⁻¹ * a⁻¹ with hz
    have hzZ : z ∈ Z := (hAF ha).2
    have hz1 := eq_one_of_conj_eq_mul (x := a) (a := z) (by rw [hz]; group) (hcZ z hzZ) hcm
      (hH.cube z (hH.le hzZ))
    have : c * a * c⁻¹ = z * a := by rw [hz]; group
    rw [this, hz1, one_mul]
  have hcD : ∀ d ∈ D, c * d = d * c := by
    intro d hd
    have hy'D : ∀ e ∈ D, y'⁻¹ * e * y' * e⁻¹ ∈ A := by
      intro e he
      have he' : y'⁻¹ * e * y' ∈ D := by
        have := (inferInstance : D.Normal).conj_mem e he y'⁻¹
        simpa using this
      have h1 := hy'.trivD _ he'
      have e1 : y' * (y'⁻¹ * e * y') * y'⁻¹ * (y'⁻¹ * e * y')⁻¹ = (y'⁻¹ * e * y' * e⁻¹)⁻¹ := by
        group
      rw [e1] at h1
      simpa using A.inv_mem h1
    set a := c * d * c⁻¹ * d⁻¹ with ha
    have haA : a ∈ A := by
      have e : a = (y'⁻¹ * (y * d * y⁻¹ * d⁻¹) * y') * (y'⁻¹ * d * y' * d⁻¹) := by
        rw [ha, hcdef]; group
      rw [e]
      exact A.mul_mem (hy'.normA' _ (hy.trivD d hd)) (hy'D d hd)
    have hca : c * a = a * c := by
      have := hcA' a haA
      calc c * a = c * a * c⁻¹ * c := by group
        _ = a * c := by rw [this]
    have ha1 := eq_one_of_conj_eq_mul (x := d) (a := a) (by rw [ha]; group) hca hcm (hH.cube a haA)
    have : c * d * c⁻¹ = d := by
      calc c * d * c⁻¹ = a * d := by rw [ha]; group
        _ = d := by rw [ha1, one_mul]
    calc c * d = c * d * c⁻¹ * c := by group
      _ = d * c := by rw [this]
  have hc1 := hCS c hcS hcD
  calc y = y' * c := by rw [hcdef]; group
    _ = y' := by rw [hc1, mul_one]

theorem mem_of_good (hH : Heis27 A Z) [D.Normal] (hS : IsPGroup 2 S)
    (hCS : ∀ c ∈ S, (∀ d ∈ D, c * d = d * c) → c = 1) {s : Y} (hs : s ∈ A) (hsZ : s ∉ Z)
    (X : Finset Y) (hX6 : X.card = 6) (hXg : ∀ x ∈ X, Good D A Z S x) {y : Y}
    (hy : Good D A Z S y) : y ∈ X := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ZA : Subgroup ↥A := Z.subgroupOf A with hZA
  haveI : ZA.Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    have : (g : Y) * n * (g : Y)⁻¹ = n := by rw [← hH.central _ hn _ g.2]; group
    simpa [this] using hn⟩
  haveI : Fintype (↥A ⧸ ZA) := Fintype.ofFinite _
  set sb : ↥A ⧸ ZA := QuotientGroup.mk ⟨s, hs⟩ with hsb
  let ψ : Y → ↥A ⧸ ZA := fun g =>
    if hg : g * s * g⁻¹ ∈ A then QuotientGroup.mk ⟨_, hg⟩ else 1
  have hψ : ∀ g (hg : Good D A Z S g), ψ g = QuotientGroup.mk ⟨g * s * g⁻¹, hg.normA s hs⟩ :=
    fun g hg => dif_pos _
  have hψeq : ∀ g g', Good D A Z S g → Good D A Z S g' → ψ g = ψ g' → g = g' := by
    intro g g' hg hg' he
    rw [hψ g hg, hψ g' hg', QuotientGroup.eq, hZA, mem_subgroupOf] at he
    exact eq_of_good hH hS hCS hg hg' hs hsZ (by simpa using he)
  have hψnot : ∀ g, Good D A Z S g → ψ g ∉ zpowers sb := by
    intro g hg hmem
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    rw [hψ g hg, hsb, ← QuotientGroup.mk_zpow, QuotientGroup.eq, hZA, mem_subgroupOf] at hk
    exact not_mem_of_good hH hg hs hsZ k (by simpa using hk)
  have hZA3 : Nat.card ZA = 3 := by
    rw [hZA, Nat.card_congr (subgroupOfEquivOfLe hH.le).toEquiv, hH.card_center]
  have hQ : Nat.card (↥A ⧸ ZA) = 9 := by
    have h := card_eq_card_quotient_mul_card_subgroup ZA
    rw [hH.card, hZA3] at h
    omega
  have hsb3 : orderOf sb = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hsb, ← QuotientGroup.mk_pow]
      have : (⟨s, hs⟩ : ↥A) ^ 3 = 1 := Subtype.ext (by simpa using hH.cube s hs)
      rw [this]; rfl
    · rw [hsb, Ne, QuotientGroup.eq_one_iff, hZA, mem_subgroupOf]
      exact hsZ
  set C : Finset (↥A ⧸ ZA) := Finset.univ.filter (fun q => q ∉ zpowers sb) with hC
  have hCcard : C.card = 6 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun q : ↥A ⧸ ZA => q ∈ zpowers sb)
    have h2 : (Finset.univ.filter (fun q : ↥A ⧸ ZA => q ∈ zpowers sb)).card = 3 := by
      rw [← hsb3, ← Nat.card_zpowers, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    have h3 : (Finset.univ : Finset (↥A ⧸ ZA)).card = 9 := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hQ]
    rw [h2, h3] at h1
    rw [hC]
    omega
  have hsub : X.image ψ ⊆ C := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψnot x (hXg x hx)⟩
  have hinj : Set.InjOn ψ X := fun a ha b hb he => hψeq a b (hXg a ha) (hXg b hb) he
  have himg : (X.image ψ).card = 6 := by rw [Finset.card_image_of_injOn hinj, hX6]
  have heq : X.image ψ = C := Finset.eq_of_subset_of_card_le hsub (by rw [hCcard, himg])
  have hyC : ψ y ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψnot y hy⟩
  rw [← heq] at hyC
  obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hyC
  rw [← hψeq x y (hXg x hx) hy hxy]
  exact hx

end CFSG.AGLEmbedding.SUDet
