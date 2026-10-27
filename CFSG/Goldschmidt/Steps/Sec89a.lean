module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Goldschmidt.Sec89

open CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G]

theorem eq_one_of_conj_eq_mul {g s w : G} (h : g⁻¹ * s * g = s * w) (hw : g⁻¹ * w * g = w)
    (hg : Odd (orderOf g)) {k : ℕ} (hwk : w ^ 2 ^ k = 1) : w = 1 := by
  have hc : Commute g w := by
    change g * w = w * g
    calc g * w = g * (g⁻¹ * w * g) := by rw [hw]
      _ = w * g := by group
  have key : ∀ n : ℕ, (g ^ n)⁻¹ * s * g ^ n = s * w ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcn : g * w ^ n = w ^ n * g := (hc.pow_right n).eq
      calc (g ^ (n + 1))⁻¹ * s * g ^ (n + 1) = g⁻¹ * ((g ^ n)⁻¹ * s * g ^ n) * g := by
            rw [pow_succ]; group
        _ = g⁻¹ * s * (w ^ n * g) := by rw [ih]; group
        _ = g⁻¹ * s * (g * w ^ n) := by rw [hcn]
        _ = (g⁻¹ * s * g) * w ^ n := by group
        _ = s * w ^ (n + 1) := by rw [h, pow_succ']; group
  have hn := key (orderOf g)
  rw [pow_orderOf_eq_one, inv_one, one_mul, mul_one] at hn
  have hw1 : w ^ orderOf g = 1 := by
    have := congrArg (s⁻¹ * ·) hn
    simpa using this.symm
  have hcop : Nat.Coprime (orderOf g) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hg)
  have h1 : orderOf w ∣ Nat.gcd (orderOf g) (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hw1) (orderOf_dvd_of_pow_eq_one hwk)
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem conj_mem_of_mem_normalizer {N : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (N : Set G)) {c : G} (hc : c ∈ N) : g⁻¹ * c * g ∈ N := by
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) c).mp hc
  simpa using this

theorem exists_mul_conj_eq [Finite G] {N : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (N : Set G)) (hfix : ∀ c ∈ N, g⁻¹ * c * g = c → c = 1)
    {s : G} (hs : s⁻¹ * (g⁻¹ * s * g) ∈ N) : ∃ c ∈ N, g⁻¹ * (s * c) * g = s * c := by
  let f : N → N := fun c =>
    ⟨c * (g⁻¹ * c * g)⁻¹, N.mul_mem c.2 (N.inv_mem (conj_mem_of_mem_normalizer hg c.2))⟩
  have hf : Function.Injective f := by
    intro c d hcd
    have h1 : (c : G) * (g⁻¹ * c * g)⁻¹ = d * (g⁻¹ * d * g)⁻¹ := congrArg Subtype.val hcd
    have h2 : g⁻¹ * ((d : G)⁻¹ * c) * g = (d : G)⁻¹ * c := by
      calc g⁻¹ * ((d : G)⁻¹ * c) * g
          = (d : G)⁻¹ * (d * (g⁻¹ * d * g)⁻¹) * (g⁻¹ * c * g) := by group
        _ = (d : G)⁻¹ * (c * (g⁻¹ * c * g)⁻¹) * (g⁻¹ * c * g) := by rw [h1]
        _ = (d : G)⁻¹ * c := by group
    have h3 := hfix _ (N.mul_mem (N.inv_mem d.2) c.2) h2
    exact Subtype.ext (by
      calc (c : G) = d * ((d : G)⁻¹ * c) := by group
        _ = d := by rw [h3, mul_one])
  obtain ⟨c, hc⟩ := (Finite.injective_iff_surjective.mp hf) ⟨_, hs⟩
  have hc' : (c : G) * (g⁻¹ * c * g)⁻¹ = s⁻¹ * (g⁻¹ * s * g) := congrArg Subtype.val hc
  refine ⟨c, c.2, ?_⟩
  calc g⁻¹ * (s * c) * g = s * (s⁻¹ * (g⁻¹ * s * g)) * (g⁻¹ * c * g) := by group
    _ = s * ((c : G) * (g⁻¹ * c * g)⁻¹) * (g⁻¹ * c * g) := by rw [hc']
    _ = s * c := by group

theorem conj_eq_of_forall_sq [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P)
    (hcomm : ∀ y ∈ P, ∀ z ∈ P, y * z = z * y) {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) (hodd : Odd (orderOf g))
    (hinv : ∀ y ∈ P, y ^ 2 = 1 → g⁻¹ * y * g = y) : ∀ y ∈ P, g⁻¹ * y * g = y := by
  have key : ∀ k : ℕ, ∀ y ∈ P, y ^ 2 ^ k = 1 → g⁻¹ * y * g = y := by
    intro k
    induction k with
    | zero =>
      intro y _ hy
      rw [pow_zero, pow_one] at hy
      rw [hy]
      group
    | succ k ih =>
      intro y hy hyk
      have hy2 : g⁻¹ * y ^ 2 * g = y ^ 2 :=
        ih _ (P.pow_mem hy 2) (by rw [← pow_mul, ← pow_succ']; exact hyk)
      have hy'P : g⁻¹ * y * g ∈ P := conj_mem_of_mem_normalizer hg hy
      have hwP : y⁻¹ * (g⁻¹ * y * g) ∈ P := P.mul_mem (P.inv_mem hy) hy'P
      have hcy := hcomm _ (P.inv_mem hy) _ hy'P
      have hw2 : (y⁻¹ * (g⁻¹ * y * g)) ^ 2 = 1 := by
        calc (y⁻¹ * (g⁻¹ * y * g)) ^ 2
            = y⁻¹ * ((g⁻¹ * y * g) * y⁻¹) * (g⁻¹ * y * g) := by rw [pow_two]; group
          _ = y⁻¹ * (y⁻¹ * (g⁻¹ * y * g)) * (g⁻¹ * y * g) := by rw [← hcy]
          _ = (y ^ 2)⁻¹ * (g⁻¹ * y ^ 2 * g) := by simp only [pow_two]; group
          _ = 1 := by rw [hy2, inv_mul_cancel]
      have hwg := hinv _ hwP hw2
      have hmul : g⁻¹ * y * g = y * (y⁻¹ * (g⁻¹ * y * g)) := by group
      have hw1 := eq_one_of_conj_eq_mul hmul hwg hodd (k := 1) (by rw [pow_one]; exact hw2)
      calc g⁻¹ * y * g = y * (y⁻¹ * (g⁻¹ * y * g)) := hmul
        _ = y := by rw [hw1, mul_one]
  intro y hy
  obtain ⟨k, hk⟩ := hP ⟨y, hy⟩
  exact key k y hy (by simpa using congrArg Subtype.val hk)

theorem mem_of_forall_sq {A : Subgroup G} {Z : Set G} (hZ : ∀ z ∈ Z, z ^ 2 ∈ Z)
    (h1 : ∀ z ∈ Z, z ^ 2 = 1 → z ∈ A) (h2 : ∀ z ∈ Z, z ^ 2 ∈ A → z ^ 2 = 1) :
    ∀ k : ℕ, ∀ z ∈ Z, z ^ 2 ^ k = 1 → z ∈ A := by
  intro k
  induction k with
  | zero =>
    intro z _ hz
    rw [pow_zero, pow_one] at hz
    rw [hz]
    exact A.one_mem
  | succ k ih =>
    intro z hz hzk
    have : z ^ 2 ∈ A := ih _ (hZ z hz) (by rw [← pow_mul, ← pow_succ']; exact hzk)
    exact h1 z hz (h2 z hz this)

theorem zpow_eq_one_or_eq {y : G} (hy2 : y ^ 2 = 1) (k : ℤ) : y ^ k = 1 ∨ y ^ k = y := by
  have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
  have hy2' : y ^ (2 : ℤ) = 1 := by rw [zpow_ofNat]; exact hy2
  rw [hk, zpow_add, zpow_mul, hy2', one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]


theorem mem_normalizer_of_forall_comm {A : Subgroup G} {y : G} (hyA : ∀ a ∈ A, a * y = y * a) :
    y ∈ Subgroup.normalizer (A : Set G) := Subgroup.mem_normalizer_iff.mpr fun a => by
  constructor
  · intro ha
    rw [show y * a * y⁻¹ = a by rw [← hyA a ha]; group]
    exact ha
  · intro ha
    have h1 := hyA _ ha
    have e : a = y * a * y⁻¹ := by
      calc a = y⁻¹ * ((y * a * y⁻¹) * y) := by group
        _ = y⁻¹ * (y * (y * a * y⁻¹)) := by rw [h1]
        _ = y * a * y⁻¹ := by group
    rw [e]
    exact ha

theorem mem_or_mul_mem_of_mem_sup {A : Subgroup G} {y : G} (hy2 : y ^ 2 = 1)
    (hyA : ∀ a ∈ A, a * y = y * a) {z : G} (hz : z ∈ A ⊔ Subgroup.zpowers y) :
    z ∈ A ∨ ∃ a ∈ A, z = a * y := by
  have hle : Subgroup.zpowers y ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_of_forall_comm hyA)
  have hz' : z ∈ (A : Set G) * (Subgroup.zpowers y : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left A _ hle]
    exact hz
  obtain ⟨a, ha, w, hw, rfl⟩ := Set.mem_mul.mp hz'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rcases zpow_eq_one_or_eq hy2 k with h | h
  · left
    rw [h, mul_one]
    exact ha
  · right
    exact ⟨a, ha, by rw [h]⟩

theorem isElemAbelian_sup_zpowers [Finite G] {A : Subgroup G} (hA : IsElemAbelian 2 A) {y : G}
    (hy : y ∉ A) (hy2 : y ^ 2 = 1) (hyA : ∀ a ∈ A, a * y = y * a) :
    IsElemAbelian 2 (A ⊔ Subgroup.zpowers y) ∧
      Nat.card A * 2 ≤ Nat.card (A ⊔ Subgroup.zpowers y : Subgroup G) := by
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hmem := fun {z : G} (hz : z ∈ A ⊔ Subgroup.zpowers y) =>
    mem_or_mul_mem_of_mem_sup hy2 hyA hz
  have hcA : ∀ z ∈ A ⊔ Subgroup.zpowers y, ∀ b ∈ A, z * b = b * z := fun z hz b hb => by
    rcases hmem hz with hzA | ⟨a, ha, rfl⟩
    · exact hAc z hzA b hb
    · rw [mul_assoc, ← hyA b hb, ← mul_assoc, hAc a ha b hb, mul_assoc]
  have hcy : ∀ z ∈ A ⊔ Subgroup.zpowers y, z * y = y * z := fun z hz => by
    rcases hmem hz with hzA | ⟨a, ha, rfl⟩
    · exact hyA z hzA
    · calc a * y * y = y * a * y := by rw [hyA a ha]
        _ = y * (a * y) := by rw [mul_assoc]
  refine ⟨⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩, ?_⟩
  · change (u : G) * v = v * u
    rcases hmem v.2 with hvA | ⟨b, hb, hv⟩
    · exact hcA u u.2 v hvA
    · rw [hv, ← mul_assoc, hcA u u.2 b hb, mul_assoc, hcy u u.2, ← mul_assoc]
  · rcases hmem hz with hzA | ⟨a, ha, rfl⟩
    · exact hA.2 z hzA
    · have ha2 := hA.2 a ha
      calc (a * y) ^ 2 = a * (y * a) * y := by rw [pow_two]; group
        _ = a ^ 2 * y ^ 2 := by rw [← hyA a ha]; simp only [pow_two]; group
        _ = 1 := by rw [ha2, hy2, one_mul]
  · let f : A × Bool → (A ⊔ Subgroup.zpowers y : Subgroup G) := fun p =>
      ⟨p.1 * cond p.2 y 1, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (by
        cases p.2
        · exact Subgroup.one_mem _
        · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y))⟩
    have hf : Function.Injective f := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h' : (a : G) * cond b y 1 = a' * cond b' y 1 := congrArg Subtype.val h
      cases b <;> cases b' <;> simp only [Bool.cond_false, Bool.cond_true, mul_one] at h'
      · exact Prod.ext (Subtype.ext h') rfl
      · refine absurd ?_ hy
        rw [show y = (a' : G)⁻¹ * a by rw [h']; group]
        exact A.mul_mem (A.inv_mem a'.2) a.2
      · refine absurd ?_ hy
        rw [show y = (a : G)⁻¹ * a' by rw [← h']; group]
        exact A.mul_mem (A.inv_mem a.2) a'.2
      · exact Prod.ext (Subtype.ext (mul_right_cancel h')) rfl
    have h1 := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1

end CFSG.Goldschmidt.Sec89
