module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Y
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Orbit
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Models5
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ExtB

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

theorem cyclic_card_pow_le (n i : ℕ) :
    Nat.card {a : Multiplicative (ZMod (2 ^ n)) // a ^ (2 ^ i) = 1} ≤ 2 ^ i := by
  classical
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  have h := IsCyclic.card_pow_eq_one_le (α := Multiplicative (ZMod (2 ^ n))) (n := 2 ^ i)
    (by positivity)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h

theorem Z2n2_card_ker_pow_le (n i : ℕ) :
    Nat.card {m : Z2n2 n // m ^ (2 ^ i) = 1} ≤ 4 ^ i := by
  have e : {m : Z2n2 n // m ^ (2 ^ i) = 1} ≃
      {a : Multiplicative (ZMod (2 ^ n)) // a ^ (2 ^ i) = 1} ×
        {a : Multiplicative (ZMod (2 ^ n)) // a ^ (2 ^ i) = 1} :=
    { toFun := fun m => (⟨m.1.1, by simpa using congrArg Prod.fst m.2⟩,
        ⟨m.1.2, by simpa using congrArg Prod.snd m.2⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), by
        apply Prod.ext
        · simpa using p.1.2
        · simp
          exact p.2.2⟩
      left_inv := fun m => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod]
  have h := cyclic_card_pow_le n i
  calc Nat.card {a : Multiplicative (ZMod (2 ^ n)) // a ^ (2 ^ i) = 1} *
      Nat.card {a : Multiplicative (ZMod (2 ^ n)) // a ^ (2 ^ i) = 1} ≤ 2 ^ i * 2 ^ i :=
        Nat.mul_le_mul h h
    _ = 4 ^ i := by rw [← mul_pow]; norm_num

theorem Z2n2_pow_exp (n : ℕ) (m : Z2n2 n) : m ^ (2 ^ n) = 1 := by
  have h1 : ∀ a : Multiplicative (ZMod (2 ^ n)), a ^ (2 ^ n) = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul]
    simp
  exact Prod.ext (h1 m.1) (h1 m.2)

theorem Z2n2_card_ker_pow (n i : ℕ) (hi : i ≤ n) :
    Nat.card {m : Z2n2 n // m ^ (2 ^ i) = 1} = 4 ^ i := by
  let φ : Z2n2 n →* Z2n2 n := powMonoidHom (2 ^ i)
  let ψ : Z2n2 n →* Z2n2 n := powMonoidHom (2 ^ (n - i))
  have hker : Nat.card φ.ker = Nat.card {m : Z2n2 n // m ^ (2 ^ i) = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun m => by simp [φ, MonoidHom.mem_ker]))
  have hkerψ : Nat.card ψ.ker = Nat.card {m : Z2n2 n // m ^ (2 ^ (n - i)) = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun m => by simp [ψ, MonoidHom.mem_ker]))
  have hrange : φ.range ≤ ψ.ker := by
    rintro _ ⟨m, rfl⟩
    rw [MonoidHom.mem_ker]
    show ((m ^ (2 ^ i)) ^ (2 ^ (n - i))) = 1
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hi]
    exact Z2n2_pow_exp n m
  have hcard : Nat.card (Z2n2 n) = 4 ^ n := card_Z2n2 n
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card φ.range ≤ 4 ^ (n - i) :=
    le_trans (Subgroup.card_le_of_le hrange) (hkerψ ▸ Z2n2_card_ker_pow_le n (n - i))
  have h3 : Nat.card φ.ker ≤ 4 ^ i := hker ▸ Z2n2_card_ker_pow_le n i
  have h4 : 4 ^ n = 4 ^ i * 4 ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
  have hpos : 0 < 4 ^ (n - i) := by positivity
  have key : Nat.card φ.ker * Nat.card φ.range = 4 ^ i * 4 ^ (n - i) := by
    rw [← h4]; exact h1.trans hcard
  have h5 : 4 ^ i * 4 ^ (n - i) ≤ Nat.card φ.ker * 4 ^ (n - i) := by
    calc 4 ^ i * 4 ^ (n - i) = Nat.card φ.ker * Nat.card φ.range := key.symm
      _ ≤ Nat.card φ.ker * 4 ^ (n - i) := Nat.mul_le_mul_left _ h2
  have h6 : 4 ^ i ≤ Nat.card φ.ker := Nat.le_of_mul_le_mul_right h5 hpos
  rw [← hker]
  exact le_antisymm h3 h6

theorem Z2n2_exists_sq_ne_one (n : ℕ) (hn : 2 ≤ n) : ∃ m : Z2n2 n, m * m ≠ 1 := by
  refine ⟨(Multiplicative.ofAdd 1, 1), ?_⟩
  intro h
  have h1 := congrArg Prod.fst h
  have h2 : ((1 : ZMod (2 ^ n)) + 1) = 0 := by
    have := congrArg Multiplicative.toAdd h1
    simpa using this
  have h3 : ((2 : ℕ) : ZMod (2 ^ n)) = 0 := by
    have : ((2 : ℕ) : ZMod (2 ^ n)) = (1 : ZMod (2 ^ n)) + 1 := by norm_num
    rw [this]; exact h2
  rw [ZMod.natCast_eq_zero_iff] at h3
  have h4 : 2 ^ n ≤ 2 := Nat.le_of_dvd (by norm_num) h3
  have h5 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

variable {G : Type} [Group G]

def Om (P : Subgroup G) (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (i : ℕ) : Subgroup G where
  carrier := {g | g ∈ P ∧ g ^ (2 ^ i) = 1}
  one_mem' := ⟨P.one_mem, one_pow _⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨P.mul_mem ha hb, ?_⟩
    have hc : Commute a b := hP a ha b hb
    rw [hc.mul_pow, ha', hb', one_mul]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨P.inv_mem ha, by rw [inv_pow, ha', inv_one]⟩

theorem mem_Om {P : Subgroup G} {hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a} {i : ℕ} {g : G} :
    g ∈ Om P hP i ↔ g ∈ P ∧ g ^ (2 ^ i) = 1 := Iff.rfl

theorem card_Om {P : Subgroup G} (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {n : ℕ}
    (e : ↥P ≃* Z2n2 n) {i : ℕ} (hi : i ≤ n) : Nat.card (Om P hP i) = 4 ^ i := by
  rw [← Z2n2_card_ker_pow n i hi]
  refine Nat.card_congr
    { toFun := fun g => ⟨e ⟨g.1, g.2.1⟩, ?_⟩
      invFun := fun m => ⟨((e.symm m.1 : ↥P) : G), (e.symm m.1).2, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h1 : (⟨g.1, g.2.1⟩ : ↥P) ^ (2 ^ i) = 1 := Subtype.ext (by simpa using g.2.2)
    rw [← map_pow, h1, map_one]
  · have h1 : (e.symm m.1) ^ (2 ^ i) = 1 := by
      rw [← map_pow, m.2, map_one]
    have := congrArg Subtype.val h1
    simpa using this
  · intro g
    apply Subtype.ext
    simp
  · intro m
    apply Subtype.ext
    simp

theorem Om_zero {P : Subgroup G} (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) : Om P hP 0 = ⊥ := by
  ext g
  rw [mem_Om, Subgroup.mem_bot]
  simp only [pow_zero, pow_one]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ P.one_mem, h⟩

theorem Om_top {P : Subgroup G} (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {n : ℕ}
    (e : ↥P ≃* Z2n2 n) : Om P hP n = P := by
  apply le_antisymm
  · exact fun g hg => hg.1
  · intro g hg
    refine ⟨hg, ?_⟩
    have h1 : (e ⟨g, hg⟩) ^ (2 ^ n) = 1 := Z2n2_pow_exp n _
    rw [← map_pow] at h1
    have h2 : (⟨g, hg⟩ : ↥P) ^ (2 ^ n) = 1 := e.injective (by rw [h1, map_one])
    have := congrArg Subtype.val h2
    simpa using this

theorem Om_mono {P : Subgroup G} (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (i : ℕ) :
    Om P hP i ≤ Om P hP (i + 1) := by
  intro g hg
  refine ⟨hg.1, ?_⟩
  have : g ^ (2 ^ (i + 1)) = (g ^ (2 ^ i)) ^ 2 := by rw [← pow_mul, pow_succ]
  rw [this, hg.2, one_pow]

theorem Om_pow_surj [Finite G] {P : Subgroup G} (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {n : ℕ}
    (e : ↥P ≃* Z2n2 n) {i : ℕ} (hi : i + 1 ≤ n) {z : G} (hz : z ∈ Om P hP 1) :
    ∃ g ∈ Om P hP (i + 1), g ^ (2 ^ i) = z := by
  let A := Om P hP (i + 1)
  let ψ : ↥A →* ↥(Om P hP 1) :=
    { toFun := fun g => ⟨g.1 ^ (2 ^ i), P.pow_mem g.2.1 _, by
        rw [← pow_mul, ← pow_add]
        exact g.2.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro g h
        apply Subtype.ext
        have hc : Commute g.1 h.1 := hP _ g.2.1 _ h.2.1
        exact hc.mul_pow _ }
  have hker : Nat.card ψ.ker = Nat.card (Om P hP i) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨g.1.1, g.1.2.1, by
          have h1 : ψ g.1 = 1 := g.2
          have := congrArg (fun w : ↥(Om P hP 1) => (w : G)) h1
          simpa [ψ] using this⟩
        invFun := fun m => ⟨⟨m.1, Om_mono hP i m.2⟩, by
          show ψ ⟨m.1, Om_mono hP i m.2⟩ = 1
          apply Subtype.ext
          simpa [ψ] using m.2.2⟩
        left_inv := fun g => by apply Subtype.ext; apply Subtype.ext; rfl
        right_inv := fun m => by apply Subtype.ext; rfl }
  have hmul := Subgroup.card_ker_mul_card_range ψ
  rw [hker, card_Om hP e (by omega : i ≤ n)] at hmul
  have hA : Nat.card ↥A = 4 ^ (i + 1) := card_Om hP e hi
  rw [hA] at hmul
  have hrange : Nat.card ψ.range = 4 := by
    have h4 : 4 ^ i * Nat.card ψ.range = 4 ^ i * 4 := by rw [hmul, pow_succ]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h4
  have hO1 : Nat.card ↥(Om P hP 1) = 4 := by
    have := card_Om hP e (by omega : 1 ≤ n)
    simpa using this
  have htop : ψ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hrange, hO1])
  have : (⟨z, hz⟩ : ↥(Om P hP 1)) ∈ ψ.range := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨g, hg⟩ := this
  refine ⟨g.1, g.2, ?_⟩
  have := congrArg (fun w : ↥(Om P hP 1) => (w : G)) hg
  simpa [ψ] using this

theorem Om_conj {P : Subgroup G} {hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a} {y : G}
    (hyP : ∀ q ∈ P, y * q * y⁻¹ ∈ P) {j : ℕ} {g : G} (hg : g ∈ Om P hP j) :
    y * g * y⁻¹ ∈ Om P hP j := by
  refine ⟨hyP g hg.1, ?_⟩
  rw [conj_pow, hg.2]
  group

theorem Om_comm_pow {P : Subgroup G} (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {y : G}
    (hyP : ∀ q ∈ P, y * q * y⁻¹ ∈ P) (i : ℕ) {g : G} (hg : g ∈ P) :
    (y * g * y⁻¹ * g⁻¹) ^ (2 ^ i) = y * g ^ (2 ^ i) * y⁻¹ * (g ^ (2 ^ i))⁻¹ := by
  have hc : Commute (y * g * y⁻¹) g⁻¹ := hP _ (hyP g hg) _ (P.inv_mem hg)
  rw [hc.mul_pow, conj_pow, inv_pow]

theorem Om_freeSec2 [Finite G] {P V : Subgroup G} (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {n : ℕ}
    (e : ↥P ≃* Z2n2 n) (hVO : V = Om P hP 1) {y : G} (hy : y * y = 1)
    (hyP : ∀ q ∈ P, y * q * y⁻¹ ∈ P) (hV4 : Nat.card V = 4)
    (hmoved : ∃ v ∈ V, y * v * y⁻¹ ≠ v) {i : ℕ} (hi : i < n) :
    FreeSec2 y (Om P hP i) (Om P hP (i + 1)) := by
  have hyV : ∀ v ∈ V, y * v * y⁻¹ ∈ V := by
    intro v hv
    rw [hVO] at hv ⊢
    exact Om_conj hyP hv
  have hV2 : IsPGroup 2 ↥V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  have hNcard : Nat.card (Om P hP i) = 4 ^ i := card_Om hP e (by omega)
  have hAcard : Nat.card (Om P hP (i + 1)) = 4 ^ (i + 1) := card_Om hP e (by omega)
  have hMN : ∀ m ∈ Om P hP (i + 1), ∀ k ∈ Om P hP i, m * k * m⁻¹ ∈ Om P hP i := by
    intro m hm k hk
    have h1 := hP m hm.1 k hk.1
    have : m * k * m⁻¹ = k := by
      calc m * k * m⁻¹ = (k * m) * m⁻¹ := by rw [h1]
        _ = k := by group
    rw [this]; exact hk
  have hNK : Om P hP i ≤ cenMod (Om P hP (i + 1)) (Om P hP i) y hMN := by
    intro g hg
    exact ⟨Om_mono hP i hg,
      (Om P hP i).mul_mem (Om_conj hyP hg) ((Om P hP i).inv_mem hg)⟩
  have hKA : cenMod (Om P hP (i + 1)) (Om P hP i) y hMN ≤ Om P hP (i + 1) := fun g hg => hg.1
  have key : ∀ g ∈ P, y * g * y⁻¹ * g⁻¹ ∈ Om P hP i ↔
      y * g ^ (2 ^ i) * y⁻¹ * (g ^ (2 ^ i))⁻¹ = 1 := by
    intro g hg
    constructor
    · intro h
      have := h.2
      rwa [Om_comm_pow hP hyP i hg] at this
    · intro h
      refine ⟨P.mul_mem (hyP g hg) (P.inv_mem hg), ?_⟩
      rw [Om_comm_pow hP hyP i hg]; exact h
  obtain ⟨z₁, hz₁V, hz₁1, hz₁fix⟩ := exists_fixed_ne_one hy hV2 (by rw [hV4]; norm_num) hyV
  obtain ⟨v₂, hv₂V, hv₂mv⟩ := hmoved
  obtain ⟨g₁, hg₁A, hg₁pow⟩ := Om_pow_surj hP e (by omega : i + 1 ≤ n) (hVO ▸ hz₁V)
  obtain ⟨g₂, hg₂A, hg₂pow⟩ := Om_pow_surj hP e (by omega : i + 1 ≤ n) (hVO ▸ hv₂V)
  have hg₁K : g₁ ∈ cenMod (Om P hP (i + 1)) (Om P hP i) y hMN := by
    refine ⟨hg₁A, (key g₁ hg₁A.1).2 ?_⟩
    rw [hg₁pow]
    calc y * z₁ * y⁻¹ * z₁⁻¹ = z₁ * z₁⁻¹ := by rw [hz₁fix]
      _ = 1 := by group
  have hg₁N : g₁ ∉ Om P hP i := fun h => hz₁1 (by rw [← hg₁pow]; exact h.2)
  have hg₂K : g₂ ∉ cenMod (Om P hP (i + 1)) (Om P hP i) y hMN := by
    intro h
    have := (key g₂ hg₂A.1).1 h.2
    rw [hg₂pow] at this
    exact hv₂mv (mul_inv_eq_one.1 this)
  have hlt1 : Om P hP i < cenMod (Om P hP (i + 1)) (Om P hP i) y hMN :=
    lt_of_le_of_ne hNK (fun h => hg₁N (by rw [h]; exact hg₁K))
  have hlt2 : cenMod (Om P hP (i + 1)) (Om P hP i) y hMN < Om P hP (i + 1) :=
    lt_of_le_of_ne hKA (fun h => hg₂K (by rw [h]; exact hg₂A))
  have c1 := Subgroup.card_lt_of_lt hlt1
  have c2 := Subgroup.card_lt_of_lt hlt2
  have d1 := Subgroup.card_dvd_of_le hNK
  have d2 := Subgroup.card_dvd_of_le hKA
  obtain ⟨m, hm⟩ := d1
  obtain ⟨m', hm'⟩ := d2
  have hpos : 0 < 4 ^ i := by positivity
  have hA4 : Nat.card (Om P hP (i + 1)) = 4 ^ i * 4 := by rw [hAcard, pow_succ]
  have e1 : 4 ^ i * 4 = 4 ^ i * (m * m') := by
    calc 4 ^ i * 4 = Nat.card (Om P hP (i + 1)) := hA4.symm
      _ = Nat.card (cenMod (Om P hP (i + 1)) (Om P hP i) y hMN) * m' := hm'
      _ = (4 ^ i * m) * m' := by rw [hm, hNcard]
      _ = 4 ^ i * (m * m') := by ring
  have e2 : 4 = m * m' := Nat.eq_of_mul_eq_mul_left hpos e1
  rw [hm, hNcard] at c1
  have hm1 : 1 < m := by
    by_contra hle
    have : m ≤ 1 := by omega
    have := Nat.mul_le_mul_left (4 ^ i) this
    omega
  have hKpos : 0 < Nat.card (cenMod (Om P hP (i + 1)) (Om P hP i) y hMN) := Nat.card_pos
  have hm'1 : 1 < m' := by
    by_contra hle
    have : m' ≤ 1 := by omega
    have := Nat.mul_le_mul_left (Nat.card (cenMod (Om P hP (i + 1)) (Om P hP i) y hMN)) this
    omega
  have hm2 : m = 2 := by
    by_contra hne
    have h3 : 3 ≤ m := by omega
    have := Nat.mul_le_mul h3 (by omega : 2 ≤ m')
    omega
  have hKcard : Nat.card (cenMod (Om P hP (i + 1)) (Om P hP i) y hMN) = 4 ^ i * 2 := by
    rw [hm, hNcard, hm2]
  have hfix : Nat.card (fixSec y (Om P hP i) (Om P hP (i + 1))) =
      Nat.card (cenMod (Om P hP (i + 1)) (Om P hP i) y hMN) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun g => Iff.rfl))
  refine ⟨Om_mono hP i, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    have : ⁅a, b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hP a ha.1 b hb.1)
    rw [this]; exact (Om P hP i).one_mem
  · intro a ha
    refine ⟨P.mul_mem ha.1 ha.1, ?_⟩
    have : (a * a) ^ (2 ^ i) = a ^ (2 ^ (i + 1)) := by
      rw [← pow_two, ← pow_mul, ← pow_succ']
    rw [this]; exact ha.2
  · intro g hg
    exact Om_conj hyP hg
  · intro g hg
    exact Om_conj hyP hg
  · rw [hfix, hKcard, hAcard, hNcard]
    ring

theorem Om_one_eq [Finite G] {P V : Subgroup G} (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {n : ℕ} (hn : 1 ≤ n)
    (e : ↥P ≃* Z2n2 n) (hVP : V ≤ P) (hV4 : Nat.card V = 4) (hVsq : ∀ v ∈ V, v * v = 1) :
    V = Om P hP 1 := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro v hv
    exact ⟨hVP hv, by rw [pow_one, pow_two]; exact hVsq v hv⟩
  · rw [card_Om hP e hn, hV4]; simp

theorem yfacts_abel [Finite G] {P V : Subgroup G} {n : ℕ} (hn : 2 ≤ n) (e : ↥P ≃* Z2n2 n)
    (hVP : V ≤ P) (hV4 : Nat.card V = 4) (hVsq : ∀ v ∈ V, v * v = 1) : YFacts V P := by
  have hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (comm_of_equiv_comm e ⟨a, ha⟩ ⟨b, hb⟩)
  have hVO : V = Om P hP 1 := Om_one_eq hP (by omega) e hVP hV4 hVsq
  have hPcard : Nat.card P = 4 ^ n := by rw [Nat.card_congr e.toEquiv, card_Z2n2]
  have h16 : 16 ≤ 4 ^ n := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨⟨⊥, ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨bot_le, Or.inl rfl, fun a ha b hb => ?_, ?_⟩
    · rw [commutatorElement_eq_one_iff_mul_comm.2 (hP a ha b hb)]
      exact (⊥ : Subgroup G).one_mem
    · rw [hPcard, Subgroup.card_bot]; omega
  · intro w hw hw2 hwV
    exfalso
    apply hwV
    rw [hVO]
    exact ⟨hw, by rw [pow_one, pow_two]; exact hw2⟩
  · intro u hu hu2
    exact ⟨P, le_rfl, hu, hP, by rw [hPcard]; exact h16⟩
  · obtain ⟨m, hm⟩ := Z2n2_exists_sq_ne_one n hn
    refine ⟨((e.symm m : ↥P) : G), (e.symm m).2, ?_⟩
    intro h
    apply hm
    have h1 : (e.symm m) * (e.symm m) = 1 := Subtype.ext (by simpa using h)
    have := congrArg e h1
    simpa using this
  · exact ⟨n, hn, hPcard⟩

theorem abel_chain [Finite G] {P V : Subgroup G} {n : ℕ} (hn : 1 ≤ n) (e : ↥P ≃* Z2n2 n)
    (hVP : V ≤ P) (hV4 : Nat.card V = 4) (hVsq : ∀ v ∈ V, v * v = 1) {y : G} (hy : y * y = 1)
    (hyP : ∀ q ∈ P, y * q * y⁻¹ ∈ P) (hmoved : ∃ v ∈ V, y * v * y⁻¹ ≠ v) :
    ∃ Pi : ℕ → Subgroup G, Pi 0 = ⊥ ∧ Pi n = P ∧ ∀ i < n, FreeSec2 y (Pi i) (Pi (i + 1)) := by
  have hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (comm_of_equiv_comm e ⟨a, ha⟩ ⟨b, hb⟩)
  have hVO : V = Om P hP 1 := Om_one_eq hP hn e hVP hV4 hVsq
  exact ⟨fun i => Om P hP i, Om_zero hP, Om_top hP e,
    fun i hi => Om_freeSec2 hP e hVO hy hyP hV4 hmoved hi⟩

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
