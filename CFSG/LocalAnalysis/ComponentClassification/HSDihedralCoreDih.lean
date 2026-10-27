module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralDihedral
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreDefs

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup

variable {X : Type} [Group X] {A : Type} [Group A]

namespace LocalDatum

variable (Δ : LocalDatum X A)

@[expose] def dn : ℕ := Classical.choose Δ.dihedral

theorem two_le_dn : 2 ≤ Δ.dn := (Classical.choose_spec Δ.dihedral).1

@[expose] def dφ : ↥Δ.D ≃* DihedralGroup Δ.dn :=
  Classical.choice (Classical.choose_spec Δ.dihedral).2

theorem dn_ne_zero : Δ.dn ≠ 0 := by have := Δ.two_le_dn; omega

theorem card_D : Nat.card Δ.D = 2 * Δ.dn := by
  rw [Nat.card_congr Δ.dφ.toEquiv, DihedralGroup.nat_card]

abbrev dE (g : DihedralGroup Δ.dn) : X := ((Δ.dφ.symm g : ↥Δ.D) : X)

theorem dE_mem (g : DihedralGroup Δ.dn) : Δ.dE g ∈ Δ.D := (Δ.dφ.symm g).2

theorem dE_mul (g h : DihedralGroup Δ.dn) : Δ.dE (g * h) = Δ.dE g * Δ.dE h := by
  simp [dE]

theorem dE_one : Δ.dE 1 = 1 := by simp [dE]

theorem dE_injective : Function.Injective Δ.dE := fun _ _ hgh =>
  Δ.dφ.symm.injective (Subtype.ext hgh)

theorem exists_dE {d : X} (hd : d ∈ Δ.D) : ∃ g, Δ.dE g = d :=
  ⟨Δ.dφ ⟨d, hd⟩, by simp [dE]⟩

theorem dE_pow (g : DihedralGroup Δ.dn) (k : ℕ) : Δ.dE (g ^ k) = Δ.dE g ^ k := by
  simp [dE]

theorem commute_dE_iff (g h : DihedralGroup Δ.dn) :
    Δ.dE g * Δ.dE h = Δ.dE h * Δ.dE g ↔ g * h = h * g := by
  rw [← Δ.dE_mul, ← Δ.dE_mul]
  exact Δ.dE_injective.eq_iff

variable [Finite X]

theorem even_dn : Even Δ.dn := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD2 : IsPGroup 2 Δ.D := Δ.sylow.isPGroup.to_le Δ.D_le
  obtain ⟨k, hk⟩ := hD2.exists_card_eq
  rw [Δ.card_D] at hk
  have h2 := Δ.two_le_dn
  rcases k with _ | _ | k
  · omega
  · omega
  · refine ⟨2 ^ k, ?_⟩
    rw [pow_succ, pow_succ] at hk
    omega

abbrev dz : X := Δ.dE (r ((Δ.dn / 2 : ℕ) : ZMod Δ.dn))

omit [Finite X] in
theorem dz_mem : Δ.dz ∈ Δ.D := Δ.dE_mem _

theorem dz_sq : Δ.dz ^ 2 = 1 := by
  rw [← Δ.dE_pow, (r_sq_eq_one_iff' Δ.even_dn Δ.dn_ne_zero _).mpr (Or.inr rfl), Δ.dE_one]

theorem dz_ne_one : Δ.dz ≠ 1 := by
  intro h
  rw [← Δ.dE_one] at h
  exact r_half_ne_one Δ.even_dn Δ.dn_ne_zero (Δ.dE_injective h)

theorem dz_central (g : DihedralGroup Δ.dn) :
    g * r ((Δ.dn / 2 : ℕ) : ZMod Δ.dn) = r ((Δ.dn / 2 : ℕ) : ZMod Δ.dn) * g := by
  have h2 : 2 * ((Δ.dn / 2 : ℕ) : ZMod Δ.dn) = 0 :=
    (two_mul_eq_zero_iff Δ.even_dn Δ.dn_ne_zero _).mpr (Or.inr rfl)
  rcases g with j | i
  · exact commute_r_r _ _
  · exact ((commute_r_sr_iff i _).mpr h2).symm

theorem dz_comm {d : X} (hd : d ∈ Δ.D) : d * Δ.dz = Δ.dz * d := by
  obtain ⟨g, rfl⟩ := Δ.exists_dE hd
  exact (Δ.commute_dE_iff _ _).mpr (Δ.dz_central g)

theorem eq_dz_of_central (h8 : 8 ≤ Nat.card Δ.D) {y : X} (hy : y ∈ Δ.D)
    (hc : ∀ d ∈ Δ.D, y * d = d * y) : y = 1 ∨ y = Δ.dz := by
  have h4 : 4 ≤ Δ.dn := by rw [Δ.card_D] at h8; omega
  obtain ⟨g, rfl⟩ := Δ.exists_dE hy
  rcases g with j | i
  · have h := (Δ.commute_dE_iff _ _).mp (hc _ (Δ.dE_mem (sr 0)))
    rw [commute_r_sr_iff, two_mul_eq_zero_iff Δ.even_dn Δ.dn_ne_zero] at h
    rcases h with rfl | rfl
    · left
      rw [← Δ.dE_one]
      rfl
    · right
      rfl
  · exfalso
    have h := (Δ.commute_dE_iff _ _).mp (hc _ (Δ.dE_mem (r 1)))
    have h' := ((commute_r_sr_iff i 1).mp h.symm)
    rw [mul_one] at h'
    have : NeZero Δ.dn := ⟨Δ.dn_ne_zero⟩
    have h2 : ((2 : ℕ) : ZMod Δ.dn) = 0 := by exact_mod_cast h'
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega

theorem dz_mem_of_normal (h8 : 8 ≤ Nat.card Δ.D) {N : Subgroup X} (hND : N ≤ Δ.D)
    (hN : N ≠ ⊥) (hnorm : ∀ d ∈ Δ.D, ∀ x ∈ N, d * x * d⁻¹ ∈ N) : Δ.dz ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD2 : IsPGroup 2 ↥Δ.D := Δ.sylow.isPGroup.to_le Δ.D_le
  have : Group.IsNilpotent ↥Δ.D := hD2.isNilpotent
  set N' := N.subgroupOf Δ.D
  have hN'n : N'.Normal := ⟨fun x hx d => by
    rw [mem_subgroupOf] at hx ⊢
    exact hnorm d d.2 x hx⟩
  have hN'ne : N' ≠ ⊥ := by
    intro h
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hND hx⟩ : ↥Δ.D) ∈ N' := mem_subgroupOf.mpr hx
    rw [h, mem_bot] at this
    exact (mem_bot).mpr (congrArg Subtype.val this)
  have := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'ne
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp this
  obtain ⟨hyN, hyZ⟩ := mem_inf.mp hy
  have hc : ∀ d ∈ Δ.D, (y : X) * d = d * y := fun d hd =>
    (congrArg Subtype.val ((mem_center_iff.mp hyZ) ⟨d, hd⟩)).symm
  rcases Δ.eq_dz_of_central h8 y.2 hc with h | h
  · exfalso
    apply hy1
    apply Subtype.ext
    exact Subtype.ext h
  · rw [← h]
    exact mem_subgroupOf.mp hyN

abbrev db : X := Δ.dE (sr 0)

omit [Finite X] in
theorem db_mem : Δ.db ∈ Δ.D := Δ.dE_mem _

omit [Finite X] in
theorem db_sq : Δ.db ^ 2 = 1 := by rw [← Δ.dE_pow, sr_sq, Δ.dE_one]

omit [Finite X] in
theorem db_ne_one : Δ.db ≠ 1 := by
  intro h
  rw [← Δ.dE_one] at h
  exact sr_ne_r 0 0 (Δ.dE_injective h)

omit [Finite X] in
theorem db_ne_dz : Δ.db ≠ Δ.dz := fun h => sr_ne_r _ _ (Δ.dE_injective h)

theorem mem_of_commute_db {d : X} (hd : d ∈ Δ.D) (hc : d * Δ.db = Δ.db * d) :
    d = 1 ∨ d = Δ.dz ∨ d = Δ.db ∨ d = Δ.db * Δ.dz := by
  obtain ⟨g, rfl⟩ := Δ.exists_dE hd
  have h := (commute_sr_iff Δ.even_dn Δ.dn_ne_zero 0 g).mp ((Δ.commute_dE_iff _ _).mp hc)
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl Δ.dE_one
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · right; right; right
    rw [← Δ.dE_mul, sr_mul_r, zero_add]

theorem commute_db_dz : Δ.db * Δ.dz = Δ.dz * Δ.db := Δ.dz_comm Δ.db_mem

abbrev da : X := Δ.dE (r ((Δ.dn / 4 : ℕ) : ZMod Δ.dn))

omit [Finite X] in
theorem da_mem : Δ.da ∈ Δ.D := Δ.dE_mem _

theorem four_dvd_dn (h8 : 8 ≤ Nat.card Δ.D) : 4 ∣ Δ.dn := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD2 : IsPGroup 2 Δ.D := Δ.sylow.isPGroup.to_le Δ.D_le
  obtain ⟨k, hk⟩ := hD2.exists_card_eq
  rw [Δ.card_D] at hk h8
  rcases k with _ | _ | _ | k
  · omega
  · omega
  · omega
  · refine ⟨2 ^ k, ?_⟩
    rw [pow_succ, pow_succ, pow_succ] at hk
    omega

theorem da_sq (h8 : 8 ≤ Nat.card Δ.D) : Δ.da ^ 2 = Δ.dz := by
  rw [← Δ.dE_pow, r_quarter_sq (Δ.four_dvd_dn h8)]

theorem eq_of_comm_mod_dz (h16 : 16 ≤ Nat.card Δ.D) {d : X} (hd : d ∈ Δ.D) (hd2 : d ^ 2 = 1)
    (hc : ∀ y ∈ Δ.D, d * y * d⁻¹ * y⁻¹ = 1 ∨ d * y * d⁻¹ * y⁻¹ = Δ.dz) : d = 1 ∨ d = Δ.dz := by
  have h8 : 8 ≤ Δ.dn := by rw [Δ.card_D] at h16; omega
  obtain ⟨g, rfl⟩ := Δ.exists_dE hd
  have hg2 : g ^ 2 = 1 := Δ.dE_injective (by rw [Δ.dE_pow, hd2, Δ.dE_one])
  have := eq_of_comm_mod_center Δ.even_dn h8 g hg2 fun y => by
    rcases hc _ (Δ.dE_mem y) with h | h
    · left
      apply Δ.dE_injective
      rw [Δ.dE_one, ← h]
      simp [dE]
    · right
      apply Δ.dE_injective
      change _ = Δ.dz
      rw [← h]
      simp [dE]
  rcases this with rfl | rfl
  · exact Or.inl Δ.dE_one
  · exact Or.inr rfl

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
