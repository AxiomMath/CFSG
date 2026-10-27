module

public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.InductionSylow

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup

theorem isCyclic_of_odd_card_subgroup_dihedralGroup {n : ℕ} (R : Subgroup (DihedralGroup n))
    (hR : Odd (Nat.card R)) : IsCyclic R := by
  have hle : R ≤ zpowers (DihedralGroup.r 1) := by
    intro x hx
    rcases x with i | i
    · obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
      exact ⟨k, DihedralGroup.r_one_zpow k⟩
    · exfalso
      have h1 : orderOf (⟨DihedralGroup.sr i, hx⟩ : R) ∣ Nat.card R := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, DihedralGroup.orderOf_sr] at h1
      exact (Nat.not_even_iff_odd.mpr hR) (even_iff_two_dvd.mpr h1)
  have : IsCyclic (R.subgroupOf (zpowers (DihedralGroup.r 1))) := Subgroup.isCyclic _
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
    (MulEquiv.surjective _)

variable {Q : Type} [Group Q]

theorem eq_one_of_pow_three_of_sq {y : Q} (h3 : y ^ 3 = 1) (h2 : y ^ 2 = 1) : y = 1 := by
  rw [show y = y ^ 3 * (y ^ 2)⁻¹ by group, h3, h2, inv_one, mul_one]

theorem mem_of_sq_eq_one_of_odd_index {L : Subgroup Q} [L.Normal] (hL : Odd L.index) {x : Q}
    (hx : x ^ 2 = 1) : x ∈ L := by
  have h1 : orderOf (x : Q ⧸ L) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one])
  have h2 : orderOf (x : Q ⧸ L) ∣ L.index := L.index_eq_card ▸ orderOf_dvd_natCard _
  have h3 : orderOf (x : Q ⧸ L) = 1 :=
    (Nat.Coprime.coprime_dvd_left h1 (Nat.coprime_two_left.mpr hL)).eq_one_of_dvd h2
  rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3

theorem mem_of_conj_eq_inv {L : Subgroup Q} (hL : L.Normal) {t x : Q} (ht : t ∈ L)
    (htx : t * x * t⁻¹ = x⁻¹) (hx : x ^ 3 = 1) : x ∈ L := by
  have hx' : t * x⁻¹ * t⁻¹ = x := by
    simpa [mul_inv_rev, mul_assoc] using congrArg (·⁻¹) htx
  have h2 : x ^ 2 ∈ L := by
    have : x ^ 2 = x * t * x⁻¹ * t⁻¹ := by
      calc x ^ 2 = x * (t * x⁻¹ * t⁻¹) := by rw [hx', sq]
        _ = x * t * x⁻¹ * t⁻¹ := by group
    rw [this]
    exact L.mul_mem (hL.conj_mem t ht x) (L.inv_mem ht)
  have h4 : x = (x ^ 2) ^ 2 := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hx, one_mul]
  rw [h4]
  exact L.pow_mem h2 2

theorem card_inf_centralizer_conj {W : Subgroup Q} {c : Q} (hc : c ∈ normalizer (W : Set Q))
    (u : Q) : Nat.card (W ⊓ centralizer ({c * u * c⁻¹} : Set Q) : Subgroup Q) =
      Nat.card (W ⊓ centralizer ({u} : Set Q) : Subgroup Q) := by
  have hW : W.map (MulAut.conj c).toMonoidHom = W := by
    ext x
    rw [mem_map_conj_iff]
    have h := mem_normalizer_iff.mp (inv_mem hc) x
    rw [inv_inv] at h
    exact h.symm
  have hmap : (W ⊓ centralizer ({u} : Set Q)).map (MulAut.conj c).toMonoidHom =
      W ⊓ centralizer ({c * u * c⁻¹} : Set Q) := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective, hW, centralizer_conj]
  rw [← hmap, Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
    (MulAut.conj c).injective]

theorem odd_of_isOddPrimePower {q : ℕ} (hq : GorensteinWalter.IsOddPrimePower q) : Odd q := by
  obtain ⟨p, n, -, hp, -, rfl⟩ := hq
  exact hp.pow

theorem eight_dvd_card_pgl2 {K : Type*} [Field K] [Finite K] (hq : Odd (Nat.card K)) :
    8 ∣ Nat.card (GorensteinWalter.PGL2 K) := by
  rw [GorensteinWalter.pgl2_card_formula]
  exact Dvd.dvd.mul_left (Nat.eight_dvd_sq_sub_one_of_odd hq) _

theorem card_le_three_mul_card_ker {Q A K : Type} [Group Q] [Group A] [Finite A] [Field K]
    [Finite K] (hK : GorensteinWalter.IsOddPrimePower (Nat.card K)) {L : Subgroup Q} [L.Normal]
    (hL : Odd L.index) (ψ : L ≃* GorensteinWalter.PSL2 K) {ζ : Q} (hζ2 : ζ ^ 2 = 1)
    (hζ1 : ζ ≠ 1) (g : A →* Q) (hgL : ∀ a, g a ∈ L) (hgζ : ∀ a, g a * ζ = ζ * g a)
    (hg3 : ∀ a, g a ^ 3 = 1) : Nat.card A ≤ 3 * Nat.card g.ker := by
  have hζL : ζ ∈ L := mem_of_sq_eq_one_of_odd_index hL hζ2
  have hord : orderOf (ψ ⟨ζ, hζL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hζ2 hζ1
  have hq := odd_of_isOddPrimePower hK
  obtain ⟨ε, hε, hε1⟩ : ∃ ε : ℤ, (Nat.card K : ℤ) ≡ ε [ZMOD 4] ∧ (ε = 1 ∨ ε = -1) := by
    have h4 : Nat.card K % 4 = 1 ∨ Nat.card K % 4 = 3 := by
      obtain ⟨k, hk⟩ := hq
      omega
    rcases h4 with h4 | h4
    · exact ⟨1, by unfold Int.ModEq; omega, Or.inl rfl⟩
    · exact ⟨-1, by unfold Int.ModEq; omega, Or.inr rfl⟩
  obtain ⟨m, -, ⟨δ⟩⟩ := ABGDGroups.psl2_centralizer_involution_dihedral hK hε hε1 hord
  have hcen : ∀ a, ψ (g.codRestrict L hgL a) ∈
      centralizer ({ψ ⟨ζ, hζL⟩} : Set (GorensteinWalter.PSL2 K)) := by
    intro a
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (hgζ a))
  let φ : A →* DihedralGroup m :=
    δ.toMonoidHom.comp ((ψ.toMonoidHom.comp (g.codRestrict L hgL)).codRestrict _ hcen)
  have hφ : ∀ a, φ a = 1 ↔ g a = 1 := by
    intro a
    change δ ⟨ψ (g.codRestrict L hgL a), hcen a⟩ = 1 ↔ g a = 1
    rw [MulEquiv.map_eq_one_iff, Subgroup.mk_eq_one, MulEquiv.map_eq_one_iff]
    change (⟨g a, hgL a⟩ : L) = 1 ↔ g a = 1
    rw [Subgroup.mk_eq_one]
  have hker : φ.ker = g.ker := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hφ]
  have h3 : ∀ x ∈ φ.range, x ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, hφ, map_pow, hg3]
  have : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have hp : IsPGroup 3 φ.range := fun x => ⟨1, Subtype.ext (by simpa using h3 x x.2)⟩
  have hodd : Odd (Nat.card φ.range) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    rw [hk]
    exact Odd.pow (by decide)
  have := isCyclic_of_odd_card_subgroup_dihedralGroup φ.range hodd
  have hle : Nat.card φ.range ≤ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd (by norm_num) (Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by simpa using h3 x x.2))
  have hcard : Nat.card A = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hcard, hker, mul_comm]
  exact Nat.mul_le_mul_right _ hle

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
