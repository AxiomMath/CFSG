module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IndexNormal

public section

open scoped commutatorElement

namespace CFSG.CGT.Stroth76

section Commutator

variable {M : Type*} [Group M]

theorem commutatorElement_mul_right_of_commute {a b x : M} (hx : x * a = a * x) :
    ⁅a, b * x⁆ = ⁅a, b⁆ := by
  have h : x * a⁻¹ = a⁻¹ * x := (Commute.inv_right (show Commute x a from hx)).eq
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * x) * a⁻¹ * (b * x)⁻¹ = a * b * (x * a⁻¹) * x⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h]; group

theorem commutatorElement_mul_left_of_commute {a b y : M} (hy : y * b = b * y) :
    ⁅a * y, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * y * b * (a * y)⁻¹ * b⁻¹ = a * (y * b) * y⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hy]; group

theorem commutatorElement_ne_one_iff {a b : M} : ⁅a, b⁆ ≠ 1 ↔ a * b ≠ b * a :=
  not_congr commutatorElement_eq_one_iff_mul_comm

variable [Finite M] {A : Subgroup M}

theorem index_centralizer_eq_two_of_central {A : Subgroup M}
    (hA : ∀ a ∈ A, ∀ m : M, a * m = m * a) (hcard : Nat.card M ≤ 4 * Nat.card A) {a b : M}
    (hab : a * b ≠ b * a) :
    (Subgroup.centralizer ({a} : Set M)).index = 2 ∧
      Nat.card (Subgroup.centralizer ({a} : Set M)) = 2 * Nat.card A := by
  set H := Subgroup.centralizer ({a} : Set M) with hH
  have hAH : A ≤ H := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hA x hx a)
  have haH : a ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have haA : a ∉ A := fun h => hab (hA a h b)
  have hbH : b ∉ H := fun h => hab (Subgroup.mem_centralizer_singleton_iff.mp h).symm
  have hApos : 0 < Nat.card A := Nat.card_pos
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hAH
  have hlt : Nat.card A < Nat.card H :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hAH (fun h => haA (h ▸ haH)))
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> simp_all
    · exact h
  have hidx : Nat.card H * H.index = Nat.card M := H.card_mul_index
  have hne1 : H.index ≠ 1 := fun h => hbH (Subgroup.index_eq_one.mp h ▸ Subgroup.mem_top b)
  have hne0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : k * H.index ≤ 4 := by
    have h1 : Nat.card A * (k * H.index) ≤ Nat.card A * 4 := by
      rw [← mul_assoc, ← hk, hidx, mul_comm]; exact hcard
    exact Nat.le_of_mul_le_mul_left h1 hApos
  have hi2 : 2 ≤ H.index := by omega
  have hk2' : k = 2 := by nlinarith
  have hi2' : H.index = 2 := by subst hk2'; omega
  exact ⟨hi2', by rw [hk, hk2', mul_comm]⟩

theorem commutatorElement_right_eq_of_central (hA : ∀ a ∈ A, ∀ m : M, a * m = m * a)
    (hcard : Nat.card M ≤ 4 * Nat.card A) {e b d : M} (heb : ⁅e, b⁆ ≠ 1) (hed : ⁅e, d⁆ ≠ 1) :
    ⁅e, b⁆ = ⁅e, d⁆ := by
  rw [commutatorElement_ne_one_iff] at heb hed
  have hidx := (index_centralizer_eq_two_of_central hA hcard heb).1
  have hbH : b ∉ Subgroup.centralizer ({e} : Set M) := fun h =>
    heb (Subgroup.mem_centralizer_singleton_iff.mp h).symm
  have hdH : d ∉ Subgroup.centralizer ({e} : Set M) := fun h =>
    hed (Subgroup.mem_centralizer_singleton_iff.mp h).symm
  have hx : b⁻¹ * d ∈ Subgroup.centralizer ({e} : Set M) := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff]
    exact iff_of_false hbH hdH
  have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
  rw [show d = b * (b⁻¹ * d) by group, commutatorElement_mul_right_of_commute hx']

theorem commutatorElement_left_eq_of_central (hA : ∀ a ∈ A, ∀ m : M, a * m = m * a)
    (hcard : Nat.card M ≤ 4 * Nat.card A) {a e b : M} (hab : ⁅a, b⁆ ≠ 1) (heb : ⁅e, b⁆ ≠ 1) :
    ⁅a, b⁆ = ⁅e, b⁆ := by
  rw [commutatorElement_ne_one_iff] at hab heb
  have hidx := (index_centralizer_eq_two_of_central hA hcard (Ne.symm hab)).1
  have haH : a ∉ Subgroup.centralizer ({b} : Set M) := fun h =>
    hab (Subgroup.mem_centralizer_singleton_iff.mp h)
  have heH : e ∉ Subgroup.centralizer ({b} : Set M) := fun h =>
    heb (Subgroup.mem_centralizer_singleton_iff.mp h)
  have hy : a⁻¹ * e ∈ Subgroup.centralizer ({b} : Set M) := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff]
    exact iff_of_false haH heH
  have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
  rw [show e = a * (a⁻¹ * e) by group, commutatorElement_mul_left_of_commute hy']

theorem commutatorElement_eq_of_central_index_le_four (hA : ∀ a ∈ A, ∀ m : M, a * m = m * a)
    (hcard : Nat.card M ≤ 4 * Nat.card A) {a b c d : M} (hab : ⁅a, b⁆ ≠ 1) (hcd : ⁅c, d⁆ ≠ 1) :
    ⁅a, b⁆ = ⁅c, d⁆ := by
  have key : ∀ e : M, ⁅e, b⁆ ≠ 1 → ⁅e, d⁆ ≠ 1 → ⁅a, b⁆ = ⁅c, d⁆ := fun e heb hed => by
    rw [commutatorElement_left_eq_of_central hA hcard hab heb,
      commutatorElement_right_eq_of_central hA hcard heb hed,
      ← commutatorElement_left_eq_of_central hA hcard hcd hed]
  by_cases had : ⁅a, d⁆ = 1
  · by_cases hcb : ⁅c, b⁆ = 1
    · refine key (a * c) ?_ ?_
      · rwa [commutatorElement_mul_left_of_commute
          (commutatorElement_eq_one_iff_mul_comm.mp hcb)]
      · have hda : a * d = d * a := commutatorElement_eq_one_iff_mul_comm.mp had
        have h : ⁅a * c, d⁆ = a * ⁅c, d⁆ * a⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]
          calc a * c * d * (a * c)⁻¹ * d⁻¹ = a * (c * d * c⁻¹ * d⁻¹) * (d * a⁻¹ * d⁻¹) := by
                group
            _ = a * (c * d * c⁻¹ * d⁻¹) * a⁻¹ := by
                rw [show d * a⁻¹ * d⁻¹ = a⁻¹ by
                  rw [(Commute.inv_right (show Commute d a from hda.symm)).eq, mul_assoc,
                    mul_inv_cancel, mul_one]]
        rw [h]
        intro h1
        apply hcd
        calc ⁅c, d⁆ = a⁻¹ * (a * ⁅c, d⁆ * a⁻¹) * a := by group
          _ = 1 := by rw [h1]; group
    · exact key c hcb hcd
  · exact key a hab had

theorem commutatorElement_mem_of_central_index_le_four (hA : ∀ a ∈ A, ∀ m : M, a * m = m * a)
    (hcard : Nat.card M ≤ 4 * Nat.card A) {a b : M} (hab : ⁅a, b⁆ ≠ 1) : ⁅a, b⁆ ∈ A := by
  have hab' := commutatorElement_ne_one_iff.mp hab
  obtain ⟨hia, hca⟩ := index_centralizer_eq_two_of_central hA hcard hab'
  obtain ⟨hib, -⟩ := index_centralizer_eq_two_of_central hA hcard (Ne.symm hab')
  set Ha := Subgroup.centralizer ({a} : Set M)
  set Hb := Subgroup.centralizer ({b} : Set M)
  haveI := Subgroup.normal_of_index_eq_two hia
  haveI := Subgroup.normal_of_index_eq_two hib
  have haHa : a ∈ Ha := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hbHb : b ∈ Hb := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have haHb : a ∉ Hb := fun h => hab' (Subgroup.mem_centralizer_singleton_iff.mp h)
  have hzHa : ⁅a, b⁆ ∈ Ha := by
    rw [commutatorElement_def, show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact mul_mem haHa ((inferInstance : Ha.Normal).conj_mem _ (inv_mem haHa) b)
  have hzHb : ⁅a, b⁆ ∈ Hb := by
    rw [commutatorElement_def]
    exact mul_mem ((inferInstance : Hb.Normal).conj_mem _ hbHb a) (inv_mem hbHb)
  have hAH : A ≤ Ha ⊓ Hb := le_inf
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hA x hx a))
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hA x hx b))
  have hlt : Ha ⊓ Hb < Ha := lt_of_le_of_ne inf_le_left (fun h => haHb (h ▸ haHa).2)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (inf_le_left : Ha ⊓ Hb ≤ Ha)
  have hlt' := Subgroup.card_lt_of_lt hlt
  have hpos : 0 < Nat.card (Ha ⊓ Hb : Subgroup M) := Nat.card_pos
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> simp_all
    · exact h
  have hle : Nat.card (Ha ⊓ Hb : Subgroup M) ≤ Nat.card A := by nlinarith
  have hAeq : A = Ha ⊓ Hb := Subgroup.eq_of_le_of_card_ge hAH hle
  rw [hAeq]
  exact ⟨hzHa, hzHb⟩

end Commutator

section Ambient

variable {G : Type*} [Group G] [Finite G]

theorem conj_commutatorElement_eq_of_central_index_le_four {A Q : Subgroup G} (hAQ : A ≤ Q)
    (hQA : Q ≤ Subgroup.centralizer (A : Set G)) (hcard : Nat.card Q ≤ 4 * Nat.card A)
    {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) (hab : ⁅a, b⁆ ≠ 1) {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    ⁅a, b⁆ ∈ A ∧ g * ⁅a, b⁆ * g⁻¹ = ⁅a, b⁆ := by
  set A' := A.subgroupOf Q
  have hA' : ∀ x ∈ A', ∀ m : Q, x * m = m * x := fun x hx m => Subtype.ext
    ((Subgroup.mem_centralizer_iff.mp (hQA m.2)) x (Subgroup.mem_subgroupOf.mp hx))
  have hcard' : Nat.card Q ≤ 4 * Nat.card A' := by
    rwa [show Nat.card A' = Nat.card A from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAQ).toEquiv]
  have hga : g * a * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hg a).mp ha
  have hgb : g * b * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hg b).mp hb
  have hcoe : ∀ x y : Q, ((⁅x, y⁆ : Q) : G) = ⁅(x : G), (y : G)⁆ := fun x y => by
    simp [commutatorElement_def]
  have hconj : ⁅g * a * g⁻¹, g * b * g⁻¹⁆ = g * ⁅a, b⁆ * g⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]; group
  have h1 : ⁅(⟨a, ha⟩ : Q), (⟨b, hb⟩ : Q)⁆ ≠ 1 := fun h => hab (by
    have := congrArg Subtype.val h
    rwa [hcoe] at this)
  have h2 : ⁅(⟨g * a * g⁻¹, hga⟩ : Q), (⟨g * b * g⁻¹, hgb⟩ : Q)⁆ ≠ 1 := fun h => hab (by
    have := congrArg Subtype.val h
    rw [hcoe] at this
    simp only [OneMemClass.coe_one] at this
    rw [hconj] at this
    calc ⁅a, b⁆ = g⁻¹ * (g * ⁅a, b⁆ * g⁻¹) * g := by group
      _ = 1 := by rw [this]; group)
  refine ⟨?_, ?_⟩
  · have := commutatorElement_mem_of_central_index_le_four hA' hcard' h1
    rw [Subgroup.mem_subgroupOf, hcoe] at this
    exact this
  · have := congrArg Subtype.val (commutatorElement_eq_of_central_index_le_four hA' hcard' h1 h2)
    rw [hcoe, hcoe] at this
    rw [← hconj]
    exact this.symm

end Ambient

section OddAut

theorem eq_one_of_pow_four_of_pow_odd {C : Type*} [Monoid C] {d : C} (h4 : d ^ 4 = 1) {m : ℕ}
    (hm : Odd m) (hdm : d ^ m = 1) : d = 1 := by
  obtain ⟨j, rfl⟩ := hm
  have h2 : d ^ 2 = 1 := by
    have h : d ^ (2 * (2 * j + 1)) = 1 := by rw [pow_mul', hdm, one_pow]
    rwa [show 2 * (2 * j + 1) = 4 * j + 2 by ring, pow_add, pow_mul, h4, one_pow,
      one_mul] at h
  rwa [pow_succ, pow_mul, h2, one_pow, one_mul] at hdm

theorem apply_eq_self_of_odd_iterate {C : Type*} [CommGroup C] {A : Subgroup C} (σ : C →* C)
    (hσA : ∀ a ∈ A, σ a = a) (hinv : ∀ r : C, r * r = 1 → r ∈ A) (hC4 : ∀ q : C, q ^ 4 ∈ A)
    (hA4 : ∀ a ∈ A, a ^ 4 = 1) {m : ℕ} (hm : Odd m) (hσm : ∀ q, σ^[m] q = q) (q : C) :
    σ q = q := by
  have F2 : ∀ r : C, r * r ∈ A → σ r * r⁻¹ ∈ A := by
    intro r hr
    apply hinv
    have h1 : σ r * σ r = r * r := by rw [← map_mul]; exact hσA _ hr
    calc σ r * r⁻¹ * (σ r * r⁻¹) = σ r * σ r * (r⁻¹ * r⁻¹) := by ac_rfl
      _ = 1 := by rw [h1, ← mul_inv, mul_inv_cancel]
  set d := σ q * q⁻¹ with hd
  have hσq : σ q = d * q := by rw [hd, inv_mul_cancel_right]
  have hd2 : d * d ∈ A := by
    have h : d * d = σ (q * q) * (q * q)⁻¹ := by
      rw [hd, map_mul, mul_inv]; ac_rfl
    rw [h]
    apply F2
    have := hC4 q
    rwa [show q ^ 4 = q * q * (q * q) by
      rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_add, pow_add, pow_add, pow_one]
      ac_rfl] at this
  have hβ := F2 d hd2
  set β := σ d * d⁻¹ with hβdef
  have hσd : σ d = β * d := by rw [hβdef, inv_mul_cancel_right]
  have hiter : ∀ n : ℕ, ∃ α ∈ A, σ^[n] q = q * d ^ n * α := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨α, hα, h⟩ := ih
      refine ⟨β ^ n * α, mul_mem (pow_mem hβ n) hα, ?_⟩
      rw [Function.iterate_succ_apply', h, map_mul, map_mul, map_pow, hσA α hα, hσq, hσd,
        mul_pow, pow_succ]
      ac_rfl
  obtain ⟨α, hα, h⟩ := hiter m
  rw [hσm] at h
  have hdm : d ^ m ∈ A := by
    have h' : d ^ m * α = 1 := by
      have h'' : q * (d ^ m * α) = q * 1 := by rw [mul_one, ← mul_assoc]; exact h.symm
      exact mul_left_cancel h''
    rw [eq_inv_of_mul_eq_one_left h']
    exact inv_mem hα
  have hdA : d ∈ A := by
    obtain ⟨j, rfl⟩ := hm
    have h1 : d = ((d * d) ^ j)⁻¹ * d ^ (2 * j + 1) := by
      rw [pow_succ, pow_mul, sq, inv_mul_cancel_left]
    rw [h1]
    exact mul_mem (inv_mem (pow_mem hd2 j)) hdm
  have hσd' : σ d = d := hσA d hdA
  have hiter2 : ∀ n : ℕ, σ^[n] q = q * d ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hσd', hσq, pow_succ]
      ac_rfl
  have h1 : d ^ m = 1 := by
    have h' := hiter2 m
    rw [hσm] at h'
    have h'' : q * d ^ m = q * 1 := by rw [mul_one]; exact h'.symm
    exact mul_left_cancel h''
  rw [hσq, eq_one_of_pow_four_of_pow_odd (hA4 d hdA) hm h1, one_mul]

variable {G : Type*} [Group G]

theorem mem_centralizer_of_odd_pow_mem {A Q : Subgroup G} (hAQ : A ≤ Q)
    (hQc : IsMulCommutative Q) (hinv : ∀ r ∈ Q, r * r = 1 → r ∈ A)
    (hQ4 : ∀ q ∈ Q, q ^ 4 ∈ A) (hA4 : ∀ a ∈ A, a ^ 4 = 1) {g : G}
    (hgA : g ∈ Subgroup.centralizer (A : Set G)) (hgQ : g ∈ Subgroup.normalizer (Q : Set G))
    {m : ℕ} (hm : Odd m) (hgm : g ^ m ∈ Q) : g ∈ Subgroup.centralizer (Q : Set G) := by
  letI : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hQc.is_comm.comm }
  have hconjQ : ∀ x ∈ Q, g⁻¹ * x * g ∈ Q := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hgQ) x).mp hx
    rwa [inv_inv] at this
  let σ : Q →* Q :=
    { toFun := fun x => ⟨g⁻¹ * x * g, hconjQ x x.2⟩
      map_one' := Subtype.ext (show g⁻¹ * 1 * g = 1 by group)
      map_mul' := fun x y => Subtype.ext
        (show g⁻¹ * ((x : G) * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) by group) }
  have hσ : ∀ x : Q, ((σ x : Q) : G) = g⁻¹ * x * g := fun x => rfl
  have hiter : ∀ (n : ℕ) (x : Q), ((σ^[n] x : Q) : G) = (g ^ n)⁻¹ * x * g ^ n := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', hσ, ih, pow_succ]
      group
  have hgcomm : ∀ a ∈ A, g⁻¹ * a * g = a := fun a ha => by
    rw [mul_assoc, (Subgroup.mem_centralizer_iff.mp hgA) a ha, inv_mul_cancel_left]
  have key := apply_eq_self_of_odd_iterate (A := A.subgroupOf Q) σ
    (fun a ha => Subtype.ext (by rw [hσ]; exact hgcomm a (Subgroup.mem_subgroupOf.mp ha)))
    (fun r hr => Subgroup.mem_subgroupOf.mpr (hinv r r.2 (congrArg Subtype.val hr)))
    (fun q => Subgroup.mem_subgroupOf.mpr (by
      show ((q : G)) ^ 4 ∈ A
      exact hQ4 q q.2))
    (fun a ha => Subtype.ext (by
      show ((a : G)) ^ 4 = 1
      have h := hA4 a (Subgroup.mem_subgroupOf.mp ha)
      exact h))
    hm (fun q => Subtype.ext (by
      rw [hiter]
      have hc : (q : G) * g ^ m = g ^ m * q := Subgroup.mul_comm_of_mem_isMulCommutative Q q.2 hgm
      rw [mul_assoc, hc, inv_mul_cancel_left]))
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have := congrArg Subtype.val (key ⟨h, hh⟩)
  rw [hσ] at this
  calc h * g = g * (g⁻¹ * h * g) := by group
    _ = g * h := by rw [this]

theorem exists_involution_mul_mem_of_involutive {C : Type*} [CommGroup C] {A : Subgroup C}
    (σ τ : C →* C) (hσσ : ∀ x, σ (σ x) = x) (hστ : ∀ x, σ (τ x) = τ (σ x))
    (hσA : ∀ a ∈ A, σ a ∈ A) {z : C} (hz2 : z * z = 1) (hzA : z ∉ A) :
    ∃ z' : C, z' * z' = 1 ∧ z' ∉ A ∧ σ z' * z' ∈ A ∧ (τ z * z ∈ A → τ z' * z' ∈ A) := by
  by_cases hc : σ z * z ∈ A
  · exact ⟨z, hz2, hzA, hc, id⟩
  · have hσ2 : σ z * σ z = 1 := by rw [← map_mul, hz2, map_one]
    refine ⟨σ z * z, ?_, hc, ?_, fun hτ => ?_⟩
    · calc σ z * z * (σ z * z) = (σ z * σ z) * (z * z) := by ac_rfl
        _ = 1 := by rw [hσ2, hz2, one_mul]
    · have h : σ (σ z * z) * (σ z * z) = 1 := by
        calc σ (σ z * z) * (σ z * z) = z * σ z * (σ z * z) := by rw [map_mul, hσσ]
          _ = (σ z * σ z) * (z * z) := by ac_rfl
          _ = 1 := by rw [hσ2, hz2, one_mul]
      rw [h]
      exact one_mem A
    · set α := τ z * z with hα
      have hτz : τ z = α * z := by rw [hα, mul_assoc, hz2, mul_one]
      have h : τ (σ z * z) * (σ z * z) = σ α * α := by
        calc τ (σ z * z) * (σ z * z) = σ (τ z) * τ z * (σ z * z) := by rw [map_mul, hστ]
          _ = σ α * σ z * (α * z) * (σ z * z) := by rw [hτz, map_mul]
          _ = σ α * α * ((σ z * σ z) * (z * z)) := by ac_rfl
          _ = σ α * α := by rw [hσ2, hz2, one_mul, mul_one]
      rw [h]
      exact mul_mem (hσA α hτ) hτ

@[expose] def conjInvHomOfMemNormalizer {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) : Q →* Q where
  toFun x := ⟨g⁻¹ * x * g, by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp x.2
    rwa [inv_inv] at this⟩
  map_one' := Subtype.ext (show g⁻¹ * 1 * g = 1 by group)
  map_mul' x y := Subtype.ext
    (show g⁻¹ * ((x : G) * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) by group)

theorem coe_conjInvHomOfMemNormalizer {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (x : Q) :
    ((conjInvHomOfMemNormalizer hg x : Q) : G) = g⁻¹ * x * g := rfl

theorem exists_involution_conj_mem {A Q : Subgroup G} (hAQ : A ≤ Q) (hQc : IsMulCommutative Q)
    {g h : G} (hgQ : g ∈ Subgroup.normalizer (Q : Set G))
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hg2 : g * g = 1)
    (hhQ : h ∈ Subgroup.normalizer (Q : Set G)) (hgh : g * h = h * g) {z : G} (hzQ : z ∈ Q)
    (hz2 : z * z = 1) (hzA : z ∉ A) :
    ∃ z' ∈ Q, z' * z' = 1 ∧ z' ∉ A ∧ z'⁻¹ * (g⁻¹ * z' * g) ∈ A ∧
      (z⁻¹ * (h⁻¹ * z * h) ∈ A → z'⁻¹ * (h⁻¹ * z' * h) ∈ A) := by
  letI : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hQc.is_comm.comm }
  set σ := conjInvHomOfMemNormalizer hgQ
  set τ := conjInvHomOfMemNormalizer hhQ
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hσσ : ∀ x, σ (σ x) = x := fun x => Subtype.ext (by
    show g⁻¹ * (g⁻¹ * x * g) * g = x
    rw [hginv, show g * (g * (x : G) * g) * g = (g * g) * x * (g * g) by group, hg2]
    group)
  have hστ : ∀ x, σ (τ x) = τ (σ x) := fun x => Subtype.ext (by
    show g⁻¹ * (h⁻¹ * x * h) * g = h⁻¹ * (g⁻¹ * x * g) * h
    calc g⁻¹ * (h⁻¹ * x * h) * g = (h * g)⁻¹ * x * (h * g) := by group
      _ = (g * h)⁻¹ * x * (g * h) := by rw [hgh]
      _ = h⁻¹ * (g⁻¹ * x * g) * h := by group)
  have hσA : ∀ a ∈ A.subgroupOf Q, σ a ∈ A.subgroupOf Q := fun a ha => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    show g⁻¹ * a * g ∈ A
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hgA) a).mp ha
    rwa [inv_inv] at this
  have hinvQ : ∀ x : Q, x * x = 1 → x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right hx
  have hcommQ : ∀ x y : Q, x * y = y * x := fun x y => mul_comm x y
  have hz2' : (⟨z, hzQ⟩ : Q) * ⟨z, hzQ⟩ = 1 := Subtype.ext hz2
  have hzA' : (⟨z, hzQ⟩ : Q) ∉ A.subgroupOf Q := fun h => hzA (Subgroup.mem_subgroupOf.mp h)
  obtain ⟨z', hz'2, hz'A, hz'σ, hz'τ⟩ :=
    exists_involution_mul_mem_of_involutive σ τ hσσ hστ hσA hz2' hzA'
  have key : ∀ (w : Q) (k : G) (hk : k ∈ Subgroup.normalizer (Q : Set G)), w * w = 1 →
      ((conjInvHomOfMemNormalizer hk w * w ∈ A.subgroupOf Q) ↔
        (w : G)⁻¹ * (k⁻¹ * w * k) ∈ A) := by
    intro w k hk hw
    rw [Subgroup.mem_subgroupOf, show ((w : G))⁻¹ = ((w⁻¹ : Q) : G) from rfl, hinvQ w hw,
      ← coe_conjInvHomOfMemNormalizer hk w, ← Subgroup.coe_mul, hcommQ]
  refine ⟨z', z'.2, congrArg Subtype.val hz'2, fun h => hz'A (Subgroup.mem_subgroupOf.mpr h),
    (key z' g hgQ hz'2).mp hz'σ, fun hzh => (key z' h hhQ hz'2).mp (hz'τ ?_)⟩
  exact (key ⟨z, hzQ⟩ h hhQ hz2').mpr hzh

end OddAut

section Burnside

variable {Y : Type*} [Group Y]

theorem eq_one_of_isPGroup_two_of_pow_odd {H : Type*} [Group H] (hH : IsPGroup 2 H) {x : H}
    {n : ℕ} (hn : Odd n) (hx : x ^ n = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hH x
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  have hd := orderOf_dvd_of_pow_eq_one hx
  rw [hj] at hd
  rcases j with _ | j
  · exact orderOf_eq_one_iff.mp (by simpa using hj)
  · exact absurd (dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero j)) hd)
      (Nat.not_even_iff_odd.mpr hn ∘ even_iff_two_dvd.mpr)

theorem exists_oddComplement_of_normalizer_le_centralizer [Finite Y] (A Q : Subgroup Y) [A.Normal]
    (hQZ : Q ≤ Subgroup.centralizer (A : Set Y)) (hQ2 : IsPGroup 2 Q)
    (hQidx : ¬ 2 ∣ Q.relIndex (Subgroup.centralizer (A : Set Y)))
    (hN : ∀ g ∈ Subgroup.centralizer (A : Set Y), g ∈ Subgroup.normalizer (Q : Set Y) →
      g ∈ Subgroup.centralizer (Q : Set Y)) :
    ∃ O : Subgroup Y, O.Normal ∧ O ≤ Subgroup.centralizer (A : Set Y) ∧ ¬ 2 ∣ Nat.card O ∧
      Subgroup.centralizer (A : Set Y) ≤ Q ⊔ O := by
  set Z := Subgroup.centralizer (A : Set Y) with hZ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Z.Normal := Subgroup.normal_centralizer
  have hP2 : IsPGroup 2 (Q.subgroupOf Z) := hQ2.comap_of_injective Z.subtype Subtype.val_injective
  let Psyl : Sylow 2 Z := hP2.toSylow hQidx
  have hPs : (Psyl : Subgroup Z) = Q.subgroupOf Z := IsPGroup.toSylow_coe hP2 hQidx
  have hPmap : (Psyl : Subgroup Z).map Z.subtype = Q := by
    rw [hPs, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQZ]
  have hcen : Subgroup.normalizer (Psyl : Set Z) ≤ Subgroup.centralizer (Psyl : Set Z) := by
    intro z hz
    have hz' : ∀ h : Z, (h : Y) ∈ Q ↔ (z : Y) * h * (z : Y)⁻¹ ∈ Q := by
      intro h
      have := Subgroup.mem_normalizer_iff.mp hz h
      rw [hPs, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at this
      exact this
    have hzN : (z : Y) ∈ Subgroup.normalizer (Q : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        exact (hz' ⟨h, hQZ hh⟩).mp hh
      · intro hh
        have hhZ : h ∈ Z := by
          have h1 : (z : Y) * h * (z : Y)⁻¹ ∈ Z := hQZ hh
          have := mul_mem (mul_mem (inv_mem z.2) h1) z.2
          rwa [show (z : Y)⁻¹ * ((z : Y) * h * (z : Y)⁻¹) * z = h by group] at this
        exact (hz' ⟨h, hhZ⟩).mpr hh
    have hzC := hN z z.2 hzN
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hp' : p ∈ (Psyl : Subgroup Z) := hp
    rw [hPs, Subgroup.mem_subgroupOf] at hp'
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hzC) p hp')
  set φ := MonoidHom.transferSylow Psyl hcen
  have hK := MonoidHom.ker_transferSylow_isComplement' Psyl hcen
  have hKodd := MonoidHom.not_dvd_card_ker_transferSylow Psyl hcen
  set O := φ.ker.map Z.subtype with hO
  have hOcard : Nat.card O = Nat.card φ.ker := Nat.card_congr
    (Subgroup.equivMapOfInjective φ.ker Z.subtype Subtype.val_injective).toEquiv.symm
  have hOZ : O ≤ Z := by rw [hO]; exact Subgroup.map_subtype_le _
  have hOodd : ¬ 2 ∣ Nat.card O := by rw [hOcard]; exact hKodd
  have hZQO : Z ≤ Q ⊔ O := by
    intro z hz
    have h1 : (⟨z, hz⟩ : Z) ∈ φ.ker ⊔ (Psyl : Subgroup Z) := by rw [hK.sup_eq_top]; trivial
    have h2 := Subgroup.mem_map_of_mem Z.subtype h1
    rw [Subgroup.map_sup, ← hO, hPmap, sup_comm] at h2
    exact h2
  refine ⟨O, ⟨fun o ho y => ?_⟩, hOZ, hOodd, hZQO⟩
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp ho
  have hyZ : y * (k : Y) * y⁻¹ ∈ Z := (inferInstance : Z.Normal).conj_mem _ k.2 y
  set k' : Z := ⟨y * k * y⁻¹, hyZ⟩ with hk'
  have hord : orderOf k' = orderOf k := by
    rw [← Subgroup.orderOf_coe k', ← Subgroup.orderOf_coe k]
    exact orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective (k : Y)
  have hodd : Odd (orderOf k') := by
    rw [hord]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
      (fun h => hKodd (h.trans (φ.ker.orderOf_dvd_natCard hk))))
  have hφ : φ k' = 1 :=
    eq_one_of_isPGroup_two_of_pow_odd Psyl.isPGroup' hodd
      (by rw [← map_pow, pow_orderOf_eq_one, map_one])
  exact Subgroup.mem_map.mpr ⟨k', hφ, rfl⟩

end Burnside

end CFSG.CGT.Stroth76
