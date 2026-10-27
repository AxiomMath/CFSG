module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding

section Sylow

variable {W : Type*} [Group W] [Finite W]

theorem exists_conj_le_of_not_dvd_index {J U : Subgroup W} (hJ : ¬ 3 ∣ J.index)
    (hU : IsPGroup 3 U) : ∃ g : W, ∀ u ∈ U, g⁻¹ * u * g ∈ J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hUP⟩ := hU.exists_le_sylow
  obtain ⟨Q⟩ : Nonempty (Sylow 3 J) := inferInstance
  set Q' : Subgroup W := (Q : Subgroup J).map J.subtype with hQ'
  have hcardQ' : Nat.card Q' = Nat.card (Q : Subgroup J) :=
    Nat.card_congr ((Q : Subgroup J).equivMapOfInjective J.subtype J.subtype_injective).toEquiv.symm
  have hmul : Nat.card J * J.index = Nat.card W := Subgroup.card_mul_index J
  have hfac : Nat.card Q' = 3 ^ (Nat.card W).factorization 3 := by
    rw [hcardQ', Q.card_eq_multiplicity, ← hmul, Nat.factorization_mul Nat.card_pos.ne'
      (Subgroup.index_ne_zero_of_finite), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hJ, add_zero]
  let S : Sylow 3 W := Sylow.ofCard Q' hfac
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W S P
  refine ⟨g, fun u hu => ?_⟩
  have hu' : u ∈ (P : Subgroup W) := hUP hu
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hu'
  have h2 : ((MulAut.conj g)⁻¹ • u : W) = g⁻¹ * u * g := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  rw [h2] at hu'
  obtain ⟨j, -, hj⟩ := hu'
  have : g⁻¹ * u * g = (j : W) := hj.symm
  rw [this]
  exact j.2

theorem false_of_elemAbelian_of_nine_dvd_orderOf {J : Subgroup W} (hJ : ¬ 3 ∣ J.index)
    (hE : ∀ U : Subgroup W, U ≤ J → IsPGroup 3 U → IsElemAbelian 3 U) {y : W}
    (hy : 9 ∣ orderOf y) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 3
    (by norm_num)
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (dvd_zero 3)
  have ha : 2 ≤ a := by
    by_contra h
    have h9 : 3 ^ 2 ∣ 3 ^ a * b := by simpa [← hab] using hy
    have h3b : Nat.Coprime (3 ^ 2) b := Nat.Coprime.pow_left 2
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb)
    have h32 : 3 ^ 2 ∣ 3 ^ a := h3b.dvd_of_dvd_mul_right h9
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h32
    omega
  set z : W := y ^ b with hz
  have hzo : orderOf z = 3 ^ a := by
    rw [hz, orderOf_pow' y hb0, hab, Nat.gcd_mul_left_left,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb0)]
  have hU : IsPGroup 3 (Subgroup.zpowers z) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hzo])
  obtain ⟨g, hg⟩ := exists_conj_le_of_not_dvd_index hJ hU
  have hzJ : g⁻¹ * z * g ∈ J := hg z (Subgroup.mem_zpowers z)
  set z' : W := g⁻¹ * z * g with hz'
  have hz'o : orderOf z' = 3 ^ a := by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
    rw [MulAut.conj_apply, inv_inv] at this
    rw [hz', this, hzo]
  have hU' : IsPGroup 3 (Subgroup.zpowers z') :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hz'o])
  have h3 := (hE (Subgroup.zpowers z') ((Subgroup.zpowers_le).2 hzJ) hU').2 z'
    (Subgroup.mem_zpowers z')
  have hdvd : 3 ^ a ∣ 3 := hz'o ▸ orderOf_dvd_of_pow_eq_one h3
  have := Nat.le_of_dvd (by norm_num) hdvd
  have h9 : 3 ^ 2 ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  omega

end Sylow

section Map

variable {W W₁ : Type*} [Group W] [Group W₁] {ρ : W →* W₁}

theorem isElemAbelian_of_map (hcop : Nat.Coprime 3 (Nat.card ρ.ker)) {J : Subgroup W}
    (hE : ∀ U : Subgroup W₁, U ≤ J.map ρ → IsPGroup 3 U → IsElemAbelian 3 U) :
    ∀ U : Subgroup W, U ≤ J → IsPGroup 3 U → IsElemAbelian 3 U := by
  have hk1 : ∀ x : W, ρ x = 1 → ∀ e : ℕ, x ^ 3 ^ e = 1 → x = 1 := fun x hx e he =>
    eq_one_of_mem_of_coprime_three hcop hx he
  intro U hUJ hU
  have hU1 := hE (U.map ρ) (Subgroup.map_mono hUJ) (hU.map ρ)
  have hinj : ∀ x ∈ U, ρ x = 1 → x = 1 := fun x hx h1 => by
    obtain ⟨e, he⟩ := hU ⟨x, hx⟩
    exact hk1 x h1 e (by simpa using congrArg Subtype.val he)
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have hc := hU1.1.is_comm.comm ⟨ρ x, x, x.2, rfl⟩ ⟨ρ y, y, y.2, rfl⟩
    have hc' : ρ ((x : W) * (y : W) * ((y : W) * (x : W))⁻¹) = 1 := by
      have := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul] at this
      rw [map_mul, map_inv, map_mul, map_mul, this, mul_inv_cancel]
    have := hinj _ (mul_mem (mul_mem x.2 y.2) (inv_mem (mul_mem y.2 x.2))) hc'
    simpa using mul_inv_eq_one.1 this
  · exact hinj _ (pow_mem hx 3) (by rw [map_pow]; exact hU1.2 _ ⟨x, hx, rfl⟩)

end Map

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
