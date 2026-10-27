module

public import CFSG.GH74.GLS.Stage4.T2SL2B
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma18iii
public import CFSG.CharacterTheory.Semidihedral.ProjectiveSL2Cover

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank

theorem ng_two_ne_zero {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 := by
  have := Fintype.ofFinite K
  refine Ring.two_ne_zero fun h => ?_
  have h1 : Fintype.card K % 2 = 0 := FiniteField.even_card_of_char_two h
  rw [← Nat.card_eq_fintype_card] at h1
  have h3 := Nat.odd_iff.mp hodd
  omega

theorem ng_even_card_L2 {F₀ : Type} [Field F₀] [Finite F₀]
    (hodd : GorensteinWalter.IsOddPrimePower (Nat.card F₀)) : 2 ∣ Nat.card (L2 F₀) := by
  have h1 : Nat.card (L2 F₀) = Nat.card (GorensteinWalter.PSL2 F₀) :=
    Nat.card_congr (L2.equivPSL F₀).toEquiv
  rw [h1, GorensteinWalter.psl2_card_formula F₀ hodd]
  obtain ⟨p, n, hp, hpodd, hn, hq⟩ := hodd
  rw [hq]
  have hodd' : Odd (p ^ n) := hpodd.pow
  obtain ⟨k, hk⟩ := hodd'
  rw [hk]
  have : (2 * k + 1) * ((2 * k + 1) ^ 2 - 1) / 2 = (2 * k + 1) * (2 * (k * (k + 1))) := by
    have : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
      have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
      omega
    rw [this]
    have : (2 * k + 1) * (4 * (k * (k + 1))) = 2 * ((2 * k + 1) * (2 * (k * (k + 1)))) := by ring
    rw [this]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [this]
  exact ⟨(2 * k + 1) * (k * (k + 1)), by ring⟩

theorem sl2_exists_conj_neg_mem {F : Type} [Field F] [Finite F]
    (hF : IVK.L2Field F) {y : Matrix.SpecialLinearGroup (Fin 2) F} (hy1 : y ≠ 1)
    (hyodd : Odd (orderOf y)) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
      Rest.T2.negOne F ∈ Subgroup.closure ({y, g * y * g⁻¹} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  classical
  have h2 : (2 : F) ≠ 0 := ng_two_ne_zero hF.1
  let e' := specialLinearGroupEquivStatedSL 2 F
  let ψ : Matrix.SpecialLinearGroup (Fin 2) F →* L2 F :=
    (QuotientGroup.mk' ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))).comp e'.toMonoidHom
  have hψsurj : Function.Surjective ψ := fun x => by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := e'.surjective a
    exact ⟨b, rfl⟩
  have hneg1 : Rest.T2.negOne F * Rest.T2.negOne F = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Rest.T2.t2B_negOne_eq, Matrix.SpecialLinearGroup.coe_one]
    simp
  have hker : ∀ x, ψ x = 1 → x = 1 ∨ x = Rest.T2.negOne F := by
    intro x hx
    have h1 : e' x ∈ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) :=
      (QuotientGroup.eq_one_iff _).1 hx
    rw [← map_center_eq_statedScalars 2 F] at h1
    obtain ⟨c, hc, hcx⟩ := h1
    have hcx' : c = x := e'.injective hcx
    subst hcx'
    rcases (CFSG.Semidihedral.ProjectiveSL2Cover.mem_center_iff_eq_one_or_minusIdentity F c).1 hc with
      h | h
    · exact Or.inl h
    · right
      rw [h]
      apply Subtype.ext
      rw [Rest.T2.t2B_negOne_eq, CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_matrix]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  have hψy : ψ y ≠ 1 := by
    intro h
    rcases hker y h with h1 | h1
    · exact hy1 h1
    · have hy2 : y ^ 2 = 1 := by rw [h1, pow_two, hneg1]
      have hd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
      rcases (Nat.dvd_prime Nat.prime_two).1 hd with h3 | h3
      · exact hy1 (orderOf_eq_one_iff.1 h3)
      · rw [h3] at hyodd
        exact absurd hyodd (by decide)
  have hψodd : Odd (orderOf (ψ y)) := Odd.of_dvd_nat hyodd (orderOf_map_dvd ψ y)
  obtain ⟨g', F₀, iF₀, fF₀, hch, hle, ⟨ε⟩⟩ :=
    IVK.Proofs2.ivk_1_8_iii F hF (L2 F) (MulEquiv.refl (L2 F)) (ψ y) hψy hψodd
  obtain ⟨g, rfl⟩ := hψsurj g'
  refine ⟨g, ?_⟩
  by_contra hneg
  set M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.closure ({y, g * y * g⁻¹} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) with hM
  have hmap : M.map ψ = Subgroup.closure ({ψ y, ψ g * ψ y * (ψ g)⁻¹} : Set (L2 F)) := by
    rw [hM, MonoidHom.map_closure, Set.image_pair]
    simp [map_mul, map_inv]
  have hodd₀ : GorensteinWalter.IsOddPrimePower (Nat.card F₀) := by
    obtain ⟨p, n, hp, hpodd, hn, hq⟩ := isOddPrimePower_of_L2Field hF
    have : Fact p.Prime := ⟨hp⟩
    have := Fintype.ofFinite F
    have hcharF : CharP F p :=
      charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hq)
    have hringF : ringChar F = p := ringChar.eq F p
    have := Fintype.ofFinite F₀
    have : CharP F₀ (ringChar F₀) := ringChar.charP F₀
    obtain ⟨n', hprime, hcard⟩ := FiniteField.card F₀ (ringChar F₀)
    refine ⟨ringChar F₀, n', hprime, ?_, n'.pos, by rw [Nat.card_eq_fintype_card, hcard]⟩
    rw [hch, hringF]
    exact hpodd
  have hEven : 2 ∣ Nat.card ↥(M.map ψ) := by
    rw [hmap, Nat.card_congr ε.toEquiv]
    exact ng_even_card_L2 hodd₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(M.map ψ)) 2 hEven
  obtain ⟨m, hmM, hmx⟩ := x.2
  have hxo : orderOf (x : L2 F) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hψm1 : ψ m ≠ 1 := by
    intro h
    rw [show ψ m = (x : L2 F) from hmx] at h
    rw [h, orderOf_one] at hxo
    omega
  have hψmm : ψ (m * m) = 1 := by
    rw [map_mul, show ψ m = (x : L2 F) from hmx]
    have : orderOf (x : L2 F) ∣ 2 := by rw [hxo]
    have h2' : (x : L2 F) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 this
    rwa [pow_two] at h2'
  have hmm : m * m = 1 := by
    rcases hker _ hψmm with h | h
    · exact h
    · exact absurd (h ▸ M.mul_mem hmM hmM) hneg
  have hm1 : m ≠ 1 := fun h => hψm1 (by rw [h, map_one])
  have hmneg : m = Rest.T2.negOne F := Rest.T2.eq_negOne_of_involution h2 hmm hm1
  exact hneg (hmneg ▸ hmM)

end CFSG.GH74.GLS.Stage4.Rest
