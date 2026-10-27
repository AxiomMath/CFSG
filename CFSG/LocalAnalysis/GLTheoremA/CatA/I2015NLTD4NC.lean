module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLTD4N
import CFSG.Walter.PSL2Facts.Even
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearPSL2
import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open scoped Pointwise

theorem td4n_noSL2_of_card_ge {N : ℕ} {E : Type} [Group E] [Finite E] (h : N ^ 3 ≤ Nat.card E) :
    TD4NoSL2 N E := by
  intro F _ _ _ hF ι hι
  have h1 : Nat.card E ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Nat.card_le_card_of_injective _ hι
  rw [CFSG.GorensteinWalter.sl2_card_formula F] at h1
  have h2 : Nat.card F * (Nat.card F ^ 2 - 1) < Nat.card F ^ 3 := by
    have hpos : 0 < Nat.card F := Nat.card_pos
    have : Nat.card F ^ 2 - 1 < Nat.card F ^ 2 := Nat.sub_lt (by positivity) one_pos
    calc Nat.card F * (Nat.card F ^ 2 - 1) < Nat.card F * Nat.card F ^ 2 :=
          Nat.mul_lt_mul_of_pos_left this hpos
      _ = Nat.card F ^ 3 := by ring
  have h3 : Nat.card F ^ 3 ≤ N ^ 3 := Nat.pow_le_pow_left hF 3
  omega

private theorem solvable_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    [Group.IsSolvable Y] : Group.IsSolvable X :=
  Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem td4n_dickson_card {F : Type} [Field F] [Finite F] [CharP F 2]
    {E : Type} [Group E] [Finite E]
    (ι : E →* Matrix.SpecialLinearGroup (Fin 2) F) (hι : Function.Injective ι)
    (hns : ¬ Group.IsSolvable E) :
    Nat.card E = 60 ∨ ∃ m : ℕ, m ≠ 0 ∧ Nat.card E = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n₀, -, hn₀⟩ := FiniteField.card F 2
  have hK : Nat.card F = 2 ^ (n₀ : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn₀
  let eP : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)
  let H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    ι.range.map eP.symm.toMonoidHom
  let eH : E ≃* ↥H := (MonoidHom.ofInjective hι).trans
    (ι.range.equivMapOfInjective eP.symm.toMonoidHom eP.symm.injective)
  have hHns : ¬ Group.IsSolvable ↥H := fun h => hns (solvable_of_equiv eH)
  have hcard : Nat.card E = Nat.card ↥H := Nat.card_congr eH.toEquiv
  rw [hcard]
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, -, hNz, ⟨eD⟩⟩ | ⟨-, ⟨e4⟩⟩ | ⟨-, ⟨eS⟩⟩ | ⟨-, ⟨eA⟩⟩ |
      ⟨m, t, -, -, N₀, C, hN₀, hN₀el, -, hCcyc, -, -, hsup⟩ | ⟨m, hm, -, ⟨eP'⟩⟩ |
      ⟨m, hm, -, ⟨eG⟩⟩
  · exact absurd (Group.isSolvable_of_comm fun a b => hEl.toIsMulCommutative.is_comm.comm a b) hHns
  · have : CommGroup ↥H := IsCyclic.commGroup
    exact absurd (inferInstance : Group.IsSolvable ↥H) hHns
  · have hz : NeZero z := ⟨fun h0 => by
      have hpos : 0 < Nat.card ↥H := Nat.card_pos
      rw [hNz, h0] at hpos
      omega⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact absurd (solvable_of_equiv eD) hHns
  · have : Nat.card (alternatingGroup (Fin 4)) = 2 ^ 2 * 3 ^ 1 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    have := CFSG.SignalizerFunctorTheorem.CatalogBridge.isSolvable_of_natCard_two_three this
    exact absurd (solvable_of_equiv e4) hHns
  · have : Nat.card (Equiv.Perm (Fin 4)) = 2 ^ 3 * 3 ^ 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      decide
    have := CFSG.SignalizerFunctorTheorem.CatalogBridge.isSolvable_of_natCard_two_three this
    exact absurd (solvable_of_equiv eS) hHns
  · left
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  · exfalso
    have : IsMulCommutative N₀ := hN₀el.toIsMulCommutative
    have hNs : Group.IsSolvable N₀ := Group.isSolvable_of_comm fun a b => this.is_comm.comm a b
    have : N₀.Normal := hN₀
    have : CommGroup C := IsCyclic.commGroup
    have hsurj : Function.Surjective ((QuotientGroup.mk' N₀).comp C.subtype) := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N₀ y
      have hx : x ∈ N₀ ⊔ C := hsup ▸ Subgroup.mem_top x
      have hx' : x ∈ (N₀ : Set ↥H) * (C : Set ↥H) := by
        rw [← Subgroup.normal_mul]
        exact hx
      obtain ⟨n, hn, c, hc, rfl⟩ := hx'
      refine ⟨⟨c, hc⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
    have hQs : Group.IsSolvable (↥H ⧸ N₀) := Group.isSolvable_of_surjective hsurj
    exact hHns (Group.isSolvable_of_ker_le_range N₀.subtype (QuotientGroup.mk' N₀) (by
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))
  · right
    refine ⟨m, hm, ?_⟩
    rw [Nat.card_congr eP'.toEquiv, CFSG.Walter.psl2_even_card hm]
  · right
    refine ⟨m, hm, ?_⟩
    rw [Nat.card_congr eG.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula, GaloisField.card 2 m hm]

theorem td4n_eq_of_two_pow_mul_odd {m n a b : ℕ} (ha : Odd a) (hb : Odd b)
    (h : 2 ^ m * a = 2 ^ n * b) : m = n := by
  have key : ∀ m n a b : ℕ, Odd a → m < n → 2 ^ m * a = 2 ^ n * b → False := by
    intro m n a b ha hmn h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    have h2 : 2 ^ m * a = 2 ^ m * (2 ^ (k + 1) * b) := by
      rw [h, pow_add, pow_add]
      ring
    have h3 : a = 2 ^ (k + 1) * b := Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) m) h2
    have h4 : Even a := by
      rw [h3]
      exact (Nat.even_pow.2 ⟨even_two, by omega⟩).mul_right b
    exact (Nat.not_even_iff_odd.2 ha) h4
  rcases lt_trichotomy m n with h1 | h1 | h1
  · exact (key m n a b ha h1 h).elim
  · exact h1
  · exact (key n m b a hb h1 h.symm).elim

theorem td4n_odd_two_pow_sq_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd ((2 ^ k) ^ 2 - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h : (2 ^ (j + 1)) ^ 2 = 2 * (2 * (2 ^ j) ^ 2) := by ring
  have h1 : 1 ≤ (2 ^ j) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_two_pow)
  rw [h]
  exact ⟨2 * (2 ^ j) ^ 2 - 1, by omega⟩

theorem td4n_psl3_card_ne {f : ℕ} (hf : 2 ≤ f) {c n : ℕ}
    (hc : c = (2 ^ f) ^ 3 - 1 ∨ c = (2 ^ f) ^ 3 + 1)
    (hn : n * 3 = (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * c) :
    n ≠ 60 ∧ ∀ m : ℕ, m ≠ 0 → n ≠ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  set q := 2 ^ f with hq
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq2 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hq23 : 16 ≤ q ^ 2 := by nlinarith
  have hq3 : 64 ≤ q ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
  obtain ⟨s, hs⟩ : ∃ s, q ^ 3 = s + 1 := ⟨q ^ 3 - 1, by omega⟩
  have hs63 : 63 ≤ s := by omega
  have hodd1 : Odd (q ^ 2 - 1) := by
    have := td4n_odd_two_pow_sq_sub_one (k := f) (by omega)
    exact this
  have hodd2 : Odd c := by
    have heven : Even (q ^ 3) := by
      rw [hq, ← pow_mul]
      exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
    obtain ⟨r, hr⟩ := heven
    rcases hc with h | h
    · exact ⟨r - 1, by omega⟩
    · exact ⟨r, by omega⟩
  refine ⟨?_, fun m hm hnm => ?_⟩
  · intro h60
    rw [h60] at hn
    have h1 : 15 ≤ q ^ 2 - 1 := by omega
    have h2 : 63 ≤ c := by rcases hc with h | h <;> omega
    have h3 : 64 * 15 * 63 ≤ q ^ 3 * (q ^ 2 - 1) * c :=
      Nat.mul_le_mul (Nat.mul_le_mul hq3 h1) h2
    omega
  ·
    have h2f3 : 2 ^ (3 * f) = q ^ 3 := by rw [hq, ← pow_mul, mul_comm]
    have hm1 : 2 ^ m * (3 * ((2 ^ m) ^ 2 - 1)) = 2 ^ (3 * f) * ((q ^ 2 - 1) * c) := by
      have h1 : n * 3 = 2 ^ m * (3 * ((2 ^ m) ^ 2 - 1)) := by rw [hnm]; ring
      rw [← h1, hn, h2f3]
      ring
    have hodd3 : Odd (3 * ((2 ^ m) ^ 2 - 1)) :=
      (by decide : Odd 3).mul (td4n_odd_two_pow_sq_sub_one (by omega))
    have hm3 : m = 3 * f := td4n_eq_of_two_pow_mul_odd hodd3 (hodd1.mul hodd2) hm1
    subst hm3
    rw [h2f3, hs] at hm1
    have hsq : (s + 1) ^ 2 - 1 = s * (s + 2) := by
      have : (s + 1) ^ 2 = s * (s + 2) + 1 := by ring
      omega
    have hcancel := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos s) hm1
    rw [hsq] at hcancel
    have hq2s : q ^ 2 - 1 ≤ s := by omega
    have hs0 : 0 < s := by omega
    rcases hc with hc | hc
    · have hc' : c = s := by omega
      rw [hc'] at hcancel
      have : 3 * (s + 2) = q ^ 2 - 1 := Nat.eq_of_mul_eq_mul_right hs0 (by linarith)
      omega
    · have hc' : c = s + 2 := by omega
      rw [hc'] at hcancel
      have : 3 * s = q ^ 2 - 1 := Nat.eq_of_mul_eq_mul_right (by omega : 0 < s + 2) (by linarith)
      omega

theorem td4n_noSL2_of_psl3_card {E : Type} [Group E] [Finite E]
    (hs : IsSimpleGroup E) (hna : ∃ x y : E, x * y ≠ y * x) {f : ℕ} (hf : 2 ≤ f) {c : ℕ}
    (hc : c = (2 ^ f) ^ 3 - 1 ∨ c = (2 ^ f) ^ 3 + 1)
    (hcard : Nat.card E * 3 = (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * c) (N : ℕ) :
    TD4NoSL2 N E := by
  haveI := hs
  intro F _ _ _ _ ι hι
  have hns : ¬ Group.IsSolvable E := fun h => by
    obtain ⟨x, y, hxy⟩ := hna
    exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr h x y)
  obtain ⟨h60, hm⟩ := td4n_psl3_card_ne hf hc hcard
  rcases td4n_dickson_card ι hι hns with h | ⟨m, hm0, h⟩
  · exact h60 h
  · exact hm m hm0 h

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
