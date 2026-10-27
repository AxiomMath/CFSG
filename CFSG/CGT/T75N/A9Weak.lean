module

public import CFSG.CGT.T75N.A9Aut

public section

namespace CFSG.CGT.T75N

open Equiv Equiv.Perm

section Lift

variable {Y G : Type*} [Group Y] [Group G]

theorem exists_lift_primePower [Finite Y] (π : Y →* G) (hπ : Function.Surjective π) {p : ℕ}
    [hp : Fact p.Prime] {g : G} {s : ℕ} (hg : g ^ p ^ s = 1) :
    ∃ y : Y, π y = g ∧ ∃ m : ℕ, y ^ p ^ m = 1 := by
  obtain ⟨y₀, hy₀⟩ := hπ g
  have hn : orderOf y₀ ≠ 0 := (orderOf_pos y₀).ne'
  obtain ⟨e, n', hn', hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.ne_one
  have hcop : Nat.Coprime (p ^ e) n' :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hn')
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 1 0
  refine ⟨y₀ ^ k, ?_, e, ?_⟩
  · rw [map_pow, hy₀]
    have h1 : orderOf g ∣ p ^ s := orderOf_dvd_of_pow_eq_one hg
    have h2 : orderOf g ∣ orderOf y₀ := by rw [← hy₀]; exact orderOf_map_dvd π y₀
    obtain ⟨t, -, hge⟩ := (Nat.dvd_prime_pow hp.out).1 h1
    have h3 : p ^ t ∣ p ^ e := by
      have h5 : p ^ t ∣ p ^ e * n' := by rw [← hge, ← hn]; exact h2
      have hcop' : Nat.Coprime (p ^ t) n' :=
        Nat.Coprime.pow_left t ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hn')
      exact (Nat.Coprime.dvd_of_dvd_mul_right hcop' h5)
    have h4 : k ≡ 1 [MOD orderOf g] := hk1.of_dvd (hge ▸ h3)
    rw [pow_eq_pow_iff_modEq.2 h4, pow_one]
  · rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hn]
    have : n' ∣ k := (Nat.modEq_zero_iff_dvd).1 hk2
    obtain ⟨c, hc⟩ := this
    exact ⟨c, by rw [hc]; ring⟩

theorem commute_of_comm_mem_center {Z : Subgroup Y} (hZ : Z ≤ Subgroup.center Y) {x y : Y}
    {m k : ℕ} (hx : x ^ 5 ^ m = 1) (hy : y ^ 2 ^ k = 1) (hxy : y * x * y⁻¹ * x⁻¹ ∈ Z) :
    y * x = x * y := by
  set c := y * x * y⁻¹ * x⁻¹ with hcdef
  have hcc : ∀ g : Y, g * c = c * g := fun g => (Subgroup.mem_center_iff.1 (hZ hxy) g)
  have hyx : y * x * y⁻¹ = c * x := by rw [hcdef]; group
  have hconj : ∀ j : ℕ, y ^ j * x * (y ^ j)⁻¹ = c ^ j * x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e1 : y ^ (j + 1) * x * (y ^ (j + 1))⁻¹ = y * (y ^ j * x * (y ^ j)⁻¹) * y⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      rw [e1, ih]
      have e2 : y * (c ^ j * x) * y⁻¹ = c ^ j * (y * x * y⁻¹) := by
        have hcj : y * c ^ j = c ^ j * y :=
          (Commute.pow_right (show Commute y c from hcc y) j).eq
        calc y * (c ^ j * x) * y⁻¹ = (y * c ^ j) * x * y⁻¹ := by group
          _ = (c ^ j * y) * x * y⁻¹ := by rw [hcj]
          _ = c ^ j * (y * x * y⁻¹) := by group
      rw [e2, hyx, pow_succ]; group
  have h1 : c ^ 2 ^ k = 1 := by
    have := hconj (2 ^ k)
    rw [hy, inv_one, mul_one, one_mul] at this
    exact (mul_eq_right.1 this.symm)
  have h2 : c ^ 5 ^ m = 1 := by
    have h3 : (y * x * y⁻¹) ^ 5 ^ m = 1 := by
      rw [conj_pow, hx]; simp
    rw [hyx, Commute.mul_pow (show Commute c x from (hcc x).symm), hx, mul_one] at h3
    exact h3
  have hcop : Nat.gcd (2 ^ k) (5 ^ m) = 1 := Nat.Coprime.pow k m (by norm_num)
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rwa [hcop, pow_one] at this
  have : y * x * y⁻¹ * x⁻¹ = 1 := hc1
  calc y * x = (y * x * y⁻¹ * x⁻¹) * (x * y) := by group
    _ = x * y := by rw [this, one_mul]

end Lift

section A9

def c5' : Perm (Fin 9) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

def a' : Perm (Fin 9) := swap 5 6 * swap 7 8

def b' : Perm (Fin 9) := swap 5 7 * swap 6 8

theorem c5'_even : c5' ∈ alternatingGroup (Fin 9) := by
  rw [mem_alternatingGroup]; decide

theorem a'_even : a' ∈ alternatingGroup (Fin 9) := by
  rw [mem_alternatingGroup]; decide

theorem b'_even : b' ∈ alternatingGroup (Fin 9) := by
  rw [mem_alternatingGroup]; decide

def c5 : alternatingGroup (Fin 9) := ⟨c5', c5'_even⟩

def a : alternatingGroup (Fin 9) := ⟨a', a'_even⟩

def b : alternatingGroup (Fin 9) := ⟨b', b'_even⟩

theorem c5_pow : c5 ^ 5 = 1 := by decide

theorem c5_ne : c5 ≠ 1 := by decide

theorem a_sq : a * a = 1 := by decide

theorem b_sq : b * b = 1 := by decide

theorem a_c5 : a * c5 * a⁻¹ * c5⁻¹ = 1 := by decide

theorem b_c5 : b * c5 * b⁻¹ * c5⁻¹ = 1 := by decide

@[expose] def klein : Subgroup (alternatingGroup (Fin 9)) where
  carrier := {1, a, b, a * b}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> decide
  inv_mem' := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem klein_card : Nat.card klein = 4 := by
  have h : Nat.card klein = Set.ncard (klein : Set (alternatingGroup (Fin 9))) :=
    (Set.ncard_def _).symm ▸ rfl
  rw [h]
  show Set.ncard ({1, a, b, a * b} : Set (alternatingGroup (Fin 9))) = 4
  rw [Set.ncard_insert_of_notMem (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; decide),
    Set.ncard_insert_of_notMem (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; decide),
    Set.ncard_pair (by decide)]

end A9

section Main

theorem a9Input_weak :
    ∀ (Y : Type) [Group Y] [Finite Y] (Z : Subgroup Y) [Z.Normal], Z ≤ Subgroup.center Y →
      Nonempty (Y ⧸ Z ≃* alternatingGroup (Fin 9)) →
        ∀ (N : Type) [Group N] [Finite N], (∀ a b : N, a * b = b * a) → (∀ a : N, a * a = 1) →
          ∀ ρ : Y →* MulAut N, ρ.ker ≤ Z → 2 ^ 6 < Nat.card N := by
  intro Y _ _ Z _ hZ ⟨e⟩ N _ _ hc h2 ρ hρ
  by_contra hcon
  push Not at hcon
  have hNp : IsPGroup 2 N := fun x => ⟨1, by simpa [pow_one, sq] using h2 x⟩
  obtain ⟨d, hd⟩ := hNp.exists_card_eq
  have hd6 : d ≤ 6 := by
    rw [hd] at hcon
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcon
  let π : Y →* alternatingGroup (Fin 9) := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hπk : ∀ y : Y, π y = 1 ↔ y ∈ Z := fun y => by
    show e (QuotientGroup.mk' Z y) = 1 ↔ y ∈ Z
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff y
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hxπ, m, hxm⟩ := exists_lift_primePower (p := 5) π hπs (g := c5) (s := 1)
    (by simpa using c5_pow)
  obtain ⟨y₁, hy₁π, k₁, hy₁k⟩ := exists_lift_primePower (p := 2) π hπs (g := a) (s := 1)
    (by simpa [pow_two] using a_sq)
  obtain ⟨y₂, hy₂π, k₂, hy₂k⟩ := exists_lift_primePower (p := 2) π hπs (g := b) (s := 1)
    (by simpa [pow_two] using b_sq)
  have hcm₁ : y₁ * x = x * y₁ := commute_of_comm_mem_center hZ hxm hy₁k (by
    rw [← hπk, map_mul, map_mul, map_mul, map_inv, map_inv, hy₁π, hxπ]
    exact a_c5)
  have hcm₂ : y₂ * x = x * y₂ := commute_of_comm_mem_center hZ hxm hy₂k (by
    rw [← hπk, map_mul, map_mul, map_mul, map_inv, map_inv, hy₂π, hxπ]
    exact b_c5)
  have hu : ρ x ≠ 1 := by
    intro h
    have h1 : x ∈ Z := hρ h
    have h2' := (hπk x).2 h1
    rw [hxπ] at h2'
    exact c5_ne h2'
  have hu5 : (ρ x) ^ 5 = 1 :=
    pow_five_eq_one' hc h2 hd hd6 (k := m) (by rw [← map_pow, hxm, map_one])
  let C : Subgroup Y := Subgroup.centralizer {x}
  have hmemC : ∀ y : Y, y * x = x * y → y ∈ C := fun y hy => by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact hy.symm
  let y₁' : C := ⟨y₁, hmemC y₁ hcm₁⟩
  let y₂' : C := ⟨y₂, hmemC y₂ hcm₂⟩
  let Φ : C →* alternatingGroup (Fin 9) := π.comp C.subtype
  let ρC : C →* MulAut N := ρ.comp C.subtype
  have hkl : klein ≤ Φ.range := by
    intro z hz
    rcases (show z = 1 ∨ z = a ∨ z = b ∨ z = a * b from hz) with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact ⟨y₁', hy₁π⟩
    · exact ⟨y₂', hy₂π⟩
    · exact ⟨y₁' * y₂', by show π (y₁ * y₂) = a * b; rw [map_mul, hy₁π, hy₂π]⟩
  have h4 : 4 ∣ Nat.card Φ.range := klein_card ▸ Subgroup.card_dvd_of_le hkl
  have hker : ρC.ker ≤ Φ.ker := by
    intro c hc
    have h1 : c.1 ∈ ρ.ker := hc
    exact (hπk c.1).2 (hρ h1)
  let g : C ⧸ ρC.ker →* alternatingGroup (Fin 9) := QuotientGroup.lift ρC.ker Φ hker
  have hgr : g.range = Φ.range := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨QuotientGroup.mk c, rfl⟩
  have hdvd1 : Nat.card Φ.range ∣ Nat.card ρC.range := by
    rw [← hgr, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρC).toEquiv]
    exact Subgroup.card_range_dvd g
  have h4' : 2 ^ 2 ∣ Nat.card ρC.range := by simpa using h4.trans hdvd1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4'
  let S : Subgroup (MulAut N) := S₀.map ρC.range.subtype
  have hSc : Nat.card S = 2 ^ 2 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hS₀]
  have hSp : IsPGroup 2 S := IsPGroup.of_card hSc
  have hcom : ∀ w ∈ S, w * ρ x = ρ x * w := by
    intro w hw
    obtain ⟨q, -, rfl⟩ := Subgroup.mem_map.1 hw
    obtain ⟨c, hc'⟩ := q.2
    have hcx : c.1 * x = x * c.1 := ((Subgroup.mem_centralizer_iff.1 c.2) x (by simp)).symm
    show q.1 * ρ x = ρ x * q.1
    rw [← hc']
    show ρ c.1 * ρ x = ρ x * ρ c.1
    rw [← map_mul, ← map_mul, hcx]
  have h6 := card_dvd_six' hc hu hu5 h2 hd hd6 hSp hcom
  rw [hSc] at h6
  omega

end Main

end CFSG.CGT.T75N
