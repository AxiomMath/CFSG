module

public import CFSG.ClassicalInvolution.Q3.Q3MProd
public import CFSG.ClassicalInvolution.Q3.Q3MFin
import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.ClassicalInvolution.Q3.M

open scoped MatrixGroups

variable {C : Type*} [Group C]

private theorem factorization_24_three : Nat.factorization 24 3 = 1 := by
  have h : (24 : ℕ) = 3 * 8 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem sylow_smul_mem (P : Sylow 3 C) (g x : C) :
    x ∈ ((g • P : Sylow 3 C) : Subgroup C) ↔ g⁻¹ * x * g ∈ (P : Subgroup C) := by
  have h : ((g • P : Sylow 3 C) : Subgroup C) =
      (P : Subgroup C).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    ext y
    simp [Subgroup.pointwise_smul_def]
  rw [h, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g = y := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem pow_mul_mem_of_pow_eq_one {N : Subgroup C} [N.Normal] {p n : C} (hn : n ∈ N) {m : ℕ}
    (hp : p ^ m = 1) : (p * n) ^ m ∈ N := by
  have hn1 : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  have h1 : (QuotientGroup.mk' N) (p * n) = (QuotientGroup.mk' N) p := by
    rw [map_mul, hn1, mul_one]
  have h2 : (QuotientGroup.mk' N) ((p * n) ^ m) = 1 := by
    rw [map_pow, h1, ← map_pow, hp, map_one]
  exact (QuotientGroup.eq_one_iff _).mp h2

section Three

variable {G : Type*} [Group G]

theorem exists_ne_one_of_card_three {S : Subgroup G} (hS : Nat.card S = 3) :
    ∃ s ∈ S, s ≠ 1 ∧ s ^ 3 = 1 := by
  have : Finite S := Nat.finite_of_card_ne_zero (by omega)
  have hbot : S ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot S).mp (by omega)
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
  refine ⟨a, a.2, fun h => ha (Subtype.ext h), ?_⟩
  have : a ^ Nat.card S = 1 := pow_card_eq_one'
  rw [hS] at this
  simpa using congrArg Subtype.val this

theorem eq_zpowers_of_card_three {S : Subgroup G} (hS : Nat.card S = 3) {y : G} (hy : y ∈ S)
    (hy1 : y ≠ 1) : S = Subgroup.zpowers y := by
  have : Finite S := Nat.finite_of_card_ne_zero (by omega)
  have hy3 : y ^ 3 = 1 := by
    have : (⟨y, hy⟩ : S) ^ Nat.card S = 1 := pow_card_eq_one'
    rw [hS] at this
    simpa using congrArg Subtype.val this
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy) ?_).symm
  rw [Nat.card_zpowers, hord, hS]

theorem mem_zpowers_of_pow_three {s : G} (hs : s ^ 3 = 1) {y : G} (hy : y ∈ Subgroup.zpowers s) :
    y = 1 ∨ y = s ∨ y = s⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hs' : s ^ (3 : ℤ) = 1 := by exact_mod_cast hs
  have hk : s ^ k = s ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, hs', one_zpow, mul_one]
  rw [hk]
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h | h | h
  · left; rw [h]; simp
  · right; left; rw [h]; simp
  · right; right
    rw [h]
    have : s ^ (2 : ℤ) * s = 1 := by
      rw [← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num, hs']
    exact eq_inv_of_mul_eq_one_left this

end Three

def sylImg (L : Subgroup C) (φ : L →* SL(2, ZMod 3)) (P : Subgroup C) :
    Subgroup SL(2, ZMod 3) :=
  (P.subgroupOf L).map φ

theorem mem_sylImg {L : Subgroup C} {φ : L →* SL(2, ZMod 3)} {P : Subgroup C}
    {y : SL(2, ZMod 3)} : y ∈ sylImg L φ P ↔ ∃ x : L, (x : C) ∈ P ∧ φ x = y := by
  unfold sylImg
  simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem sylImg_mono {L : Subgroup C} {φ : L →* SL(2, ZMod 3)} {P Q : Subgroup C} (h : P ≤ Q) :
    sylImg L φ P ≤ sylImg L φ Q := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_sylImg.mp hy
  exact mem_sylImg.mpr ⟨x, h hx, rfl⟩

variable [Finite C]

theorem sylImg_card {L : Subgroup C} (hL : L.IsSubnormal) {φ : L →* SL(2, ZMod 3)}
    (hφ : Function.Surjective φ) (P : Sylow 3 C) : Nat.card (sylImg L φ P) = 3 := by
  obtain ⟨R, hR⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hL
  have hRP : (R : Subgroup L) = (P : Subgroup C).subgroupOf L := by
    have h1 : (R : Subgroup L) = ((R : Subgroup L).map L.subtype).comap L.subtype :=
      (Subgroup.comap_map_eq_self_of_injective L.subtype_injective _).symm
    rw [h1, hR]
    exact Subgroup.inf_subgroupOf_right _ _
  have hS : sylImg L φ P = ((R.mapSurjective hφ : Sylow 3 SL(2, ZMod 3)) : Subgroup _) := by
    rw [Sylow.coe_mapSurjective, hRP]
    rfl
  rw [hS, (R.mapSurjective hφ).card_eq_multiplicity, CFSG.ClassicalInvolution.natCard_sl2Three,
    factorization_24_three]
  norm_num

omit [Finite C] in
theorem exp_six_of_sup {N : Subgroup C} [N.Normal] (P : Sylow 3 C) {L : Subgroup C}
    (φ : L →* SL(2, ZMod 3)) (hN : ∀ x : L, (x : C) ∈ N → φ x ^ 2 = 1) :
    ∀ y ∈ sylImg L φ ((P : Subgroup C) ⊔ N), y ^ 6 = 1 := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_sylImg.mp hy
  obtain ⟨p, hp, n, hn, hpn⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨p, hp⟩
  have hk' : p ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hmem : ((x ^ (3 ^ k) : L) : C) ∈ N := by
    rw [Subgroup.coe_pow, ← hpn]
    exact pow_mul_mem_of_pow_eq_one hn hk'
  have h := hN _ hmem
  rw [map_pow, ← pow_mul] at h
  exact sl2_pow_six (by rwa [mul_comm] at h)

theorem mem_of_exp_six {M S : Subgroup SL(2, ZMod 3)} (hS : Nat.card S = 3) (hSM : S ≤ M)
    (hM : ∀ y ∈ M, y ^ 6 = 1) {y : SL(2, ZMod 3)} (hy : y ∈ M) (hy3 : y ^ 3 = 1) : y ∈ S := by
  by_contra hyS
  obtain ⟨s, hs, hs1, hs3⟩ := exists_ne_one_of_card_three hS
  have hy1 : y ≠ 1 := fun h => hyS (h ▸ S.one_mem)
  have hys : y ≠ s := fun h => hyS (h ▸ hs)
  have hysi : y ≠ s⁻¹ := fun h => hyS (h ▸ S.inv_mem hs)
  exact sl2_three_distinct s y hs3 hy3 hs1 hy1 hys hysi
    ⟨hM _ (M.mul_mem (hSM hs) hy), hM _ (M.mul_mem (hSM hs) (M.inv_mem hy))⟩

theorem wielandt_diagonal {U V L : Subgroup C} [U.Normal] [V.Normal]
    (hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (h2 : ∀ x ∈ U ⊓ V, ∃ k : ℕ, x ^ (2 ^ k) = 1)
    (h3 : ∀ x : C, (∃ k : ℕ, x ^ (3 ^ k) = 1) → ∃ u ∈ U, ∃ v ∈ V, x = u * v)
    (hL : L.IsSubnormal) (φ : L →* SL(2, ZMod 3)) (hφ : Function.Surjective φ)
    (hV : ∀ x : L, (x : C) ∈ V → φ x = 1) (hU : ∀ x : L, (x : C) ∈ U → φ x ^ 2 = 1) :
    False := by
  have key : ∀ P P' : Sylow 3 C, sylImg L φ P = sylImg L φ P' := by
    intro P P'
    obtain ⟨Q, hQ⟩ := exists_sylow_sup_inf hcomm h2 h3 P P'
    obtain ⟨s, hsQ, hs1, hs3⟩ := exists_ne_one_of_card_three (sylImg_card hL hφ Q)
    obtain ⟨x, hxQ, rfl⟩ := mem_sylImg.mp hsQ
    have hQle1 : (Q : Subgroup C) ≤ (P : Subgroup C) ⊔ V := by
      rw [hQ]
      exact sup_le (inf_le_left.trans le_sup_left) (inf_le_right.trans le_sup_right)
    have hQle2 : (Q : Subgroup C) ≤ (P' : Subgroup C) ⊔ U := by
      rw [hQ]
      exact sup_le (inf_le_right.trans le_sup_right) (inf_le_left.trans le_sup_left)
    have hV2 : ∀ x : L, (x : C) ∈ V → φ x ^ 2 = 1 := fun x hx => by
      rw [hV x hx]
      exact one_pow 2
    have hPmem : φ x ∈ sylImg L φ P :=
      mem_of_exp_six (sylImg_card hL hφ P) (sylImg_mono le_sup_left)
        (exp_six_of_sup P φ hV2) (mem_sylImg.mpr ⟨x, hQle1 hxQ, rfl⟩) hs3
    have hP'mem : φ x ∈ sylImg L φ P' :=
      mem_of_exp_six (sylImg_card hL hφ P') (sylImg_mono le_sup_left)
        (exp_six_of_sup P' φ hU) (mem_sylImg.mpr ⟨x, hQle2 hxQ, rfl⟩) hs3
    rw [eq_zpowers_of_card_three (sylImg_card hL hφ P) hPmem hs1,
      eq_zpowers_of_card_three (sylImg_card hL hφ P') hP'mem hs1]
  obtain ⟨P⟩ : Nonempty (Sylow 3 C) := inferInstance
  have hc := sylImg_card hL hφ P
  obtain ⟨s, hsP, hs1, hs3⟩ := exists_ne_one_of_card_three hc
  obtain ⟨a, ha1, ha2⟩ := CFSG.ClassicalInvolution.Q3.M.sl2_three_not_normal s hs3 hs1
  obtain ⟨l, hl⟩ := hφ a
  have hkey := key P ((l : C) • P)
  obtain ⟨x, hxP, rfl⟩ := mem_sylImg.mp hsP
  have hconj : φ l * φ x * (φ l)⁻¹ ∈ sylImg L φ ((l : C) • P : Sylow 3 C) := by
    refine mem_sylImg.mpr ⟨l * x * l⁻¹, ?_, by simp [map_mul, map_inv]⟩
    rw [sylow_smul_mem]
    have : (l : C)⁻¹ * ((l * x * l⁻¹ : L) : C) * (l : C) = (x : C) := by
      simp [mul_assoc]
    rw [this]
    exact hxP
  rw [hl] at hconj
  rw [← hkey, eq_zpowers_of_card_three hc (mem_sylImg.mpr ⟨x, hxP, rfl⟩) hs1] at hconj
  have hne1 : a * φ x * a⁻¹ ≠ 1 := by
    intro h
    apply hs1
    have := congrArg (fun t => a⁻¹ * t * a) h
    simpa [mul_assoc] using this
  rcases mem_zpowers_of_pow_three hs3 hconj with h | h | h
  · exact hne1 h
  · exact ha1 h
  · exact ha2 h

end CFSG.ClassicalInvolution.Q3.M
