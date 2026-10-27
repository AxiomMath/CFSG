module

public import CFSG.GH74.GLS.IVK.Lifted.SL2TwoOrder
public import CFSG.GH74.GLS.IVK.Lifted.Companion
public import CFSG.GH74.GLS.IVK.Lifted.Lem19Lift
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Trace

variable {F : Type} [Field F] [Finite F]

theorem trace_aut_eq (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (x : SpecialLinearGroup (Fin 2) F) :
    (α x : Matrix (Fin 2) (Fin 2) F) 0 0 + (α x : Matrix (Fin 2) (Fin 2) F) 1 1 =
      (gammaOf hodd h3 α).right ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1) := by
  obtain ⟨G, hG⟩ := exists_rep hodd h3 α
  have h1 : Matrix.trace ((SpecialLinearGroup.toGL (α x) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace ((GeneralLinearGroup.map ((gammaOf hodd h3 α).right : F →+* F)
        (SpecialLinearGroup.toGL x) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [hG x]
    simpa using Matrix.trace_units_conj G
      ((GeneralLinearGroup.map ((gammaOf hodd h3 α).right : F →+* F) (SpecialLinearGroup.toGL x) :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  simp only [Matrix.trace_fin_two] at h1
  simpa [GeneralLinearGroup.map_apply] using h1

end Trace

section Arith

theorem two_part_sl2_lt (q₀ d : ℕ) (hq₀ : Odd q₀) (hq₀1 : 1 < q₀) (hd : Even d) (hd0 : d ≠ 0) :
    (q₀ * (q₀ ^ 2 - 1)).factorization 2 < (q₀ ^ d * ((q₀ ^ d) ^ 2 - 1)).factorization 2 := by
  obtain ⟨e, he⟩ := hd
  have he0 : e ≠ 0 := by omega
  have hqd : Odd (q₀ ^ d) := hq₀.pow
  have hodd2 : Odd (q₀ ^ 2) := hq₀.pow
  have hxe : Odd ((q₀ ^ 2) ^ e) := hodd2.pow
  have hq2 : 1 < q₀ ^ 2 := by nlinarith
  have hsq : q₀ ^ 2 - 1 ≠ 0 := by omega
  have hA : (q₀ ^ d) ^ 2 - 1 = ((q₀ ^ 2) ^ e - 1) * ((q₀ ^ 2) ^ e + 1) := by
    have h1 : (q₀ ^ d) ^ 2 = ((q₀ ^ 2) ^ e) ^ 2 := by
      rw [he]
      ring
    rw [h1]
    have hpos : 1 ≤ (q₀ ^ 2) ^ e := Nat.one_le_pow _ _ (by omega)
    have hpos2 : 1 ≤ ((q₀ ^ 2) ^ e) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [hpos, hpos2]
    ring
  have hdvd1 : q₀ ^ 2 - 1 ∣ (q₀ ^ 2) ^ e - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow (q₀ ^ 2) 1 e
  have hdvd2 : 2 ∣ (q₀ ^ 2) ^ e + 1 := by
    obtain ⟨k, hk⟩ := hxe
    exact ⟨k + 1, by omega⟩
  have hdvd : 2 * (q₀ ^ 2 - 1) ∣ (q₀ ^ d) ^ 2 - 1 := by
    rw [hA, mul_comm 2]
    exact mul_dvd_mul hdvd1 hdvd2
  have hqd1 : 1 < q₀ ^ d := Nat.one_lt_pow hd0 hq₀1
  have hne1 : (q₀ ^ d) ^ 2 - 1 ≠ 0 := by
    have : 1 < (q₀ ^ d) ^ 2 := by nlinarith
    omega
  have hv1 : (2 * (q₀ ^ 2 - 1)).factorization 2 ≤ ((q₀ ^ d) ^ 2 - 1).factorization 2 :=
    (Nat.factorization_le_iff_dvd (by omega) hne1).2 hdvd 2
  rw [Nat.factorization_mul (by norm_num) hsq] at hv1
  simp only [Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two] at hv1
  have hq₂ : q₀.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro h; exact (Nat.not_even_iff_odd.2 hq₀) (even_iff_two_dvd.2 h))
  have hqd₂ : (q₀ ^ d).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro h; exact (Nat.not_even_iff_odd.2 hqd) (even_iff_two_dvd.2 h))
  rw [Nat.factorization_mul (by omega) hsq, Nat.factorization_mul (by omega) hne1]
  simp only [Finsupp.add_apply, hq₂, hqd₂]
  omega

end Arith

section Big

variable {F : Type} [Field F] [Finite F]

theorem three_le_two_part_sl2 (hodd : Odd (Nat.card F)) :
    3 ≤ (Nat.card (SpecialLinearGroup (Fin 2) F)).factorization 2 := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hq := hodd
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self m
  have h8 : Nat.card F ^ 2 - 1 = 8 * t := by
    rw [hm]
    have : (2 * m + 1) ^ 2 = 8 * t + 1 := by nlinarith [ht]
    omega
  have hq0 : Nat.card F ≠ 0 := Nat.card_pos.ne'
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0] at h8
    have : 1 < Nat.card F := Finite.one_lt_card
    have : 1 < Nat.card F ^ 2 := by nlinarith
    omega
  have hdvd : 2 ^ 3 ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [h8]
    exact Dvd.dvd.mul_left ⟨t, by ring⟩ _
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
    (mul_ne_zero hq0 (by omega))).1 hdvd

theorem not_fixes_big_cyclic (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) {Q : Type} [Group Q]
    (e : Q ≃* SpecialLinearGroup (Fin 2) F) (φ : MulAut Q)
    (hσ1 : (gammaOf hodd h3 (MulAut.congr e φ)).right ≠ 1)
    (hσ2 : ∃ j : ℕ, orderOf (gammaOf hodd h3 (MulAut.congr e φ)).right = 2 ^ j) {b : Q} (hb : φ b = b)
    {c : ℕ} (hbo : orderOf b = 2 ^ c)
    (hbig : 2 ^ (c + 1) = 2 ^ (Nat.card (SpecialLinearGroup (Fin 2) F)).factorization 2) : False := by
  classical
  set α : MulAut (SpecialLinearGroup (Fin 2) F) := MulAut.congr e φ with hα
  set σ : F ≃+* F := (gammaOf hodd h3 α).right with hσ
  set x : SpecialLinearGroup (Fin 2) F := e b with hx
  have hαx : α x = x := by
    rw [hα, hx, MulAut.congr_apply]
    simp [hb]
  have htr : (x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1 ∈ fixedField σ := by
    rw [mem_fixedField_iff]
    have := trace_aut_eq hodd h3 α x
    rw [hαx] at this
    exact this.symm
  have hxo : orderOf x = 2 ^ c := by
    rw [hx, MulEquiv.orderOf_eq]
    exact hbo
  have h8 := three_le_two_part_sl2 hodd
  have hc2 : 2 ≤ c := by
    have : 2 ^ 3 ≤ 2 ^ (c + 1) := by
      rw [hbig]
      exact Nat.pow_le_pow_right (by norm_num) h8
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
    omega
  have hnotc : x ∉ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
    intro hxc
    have h2 := sq_eq_one_of_mem_center_sl2 hxc
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [hxo] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    have h4 : 2 ^ 2 ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hc2
    omega
  obtain ⟨c', hc'⟩ := exists_sl_companion_order (fixedField σ) x (nonscalar_of_not_mem_center x hnotc) htr
  have hc'o : orderOf c' = 2 ^ c := hc'.trans hxo
  have hodd₀ : Odd (Nat.card ↥(fixedField σ)) := odd_card_fixedField σ hodd
  have h0 := two_power_order_sl2_le hodd₀ c' hc'o
  obtain ⟨j, hj⟩ := hσ2
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hσ1 (orderOf_eq_one_iff.1 (by simpa using hj))
  have hev : Even (orderOf σ) := by
    rw [hσ, hj]
    exact (Nat.even_pow.2 ⟨even_two, hj0⟩)
  have hq : Nat.card ↥(fixedField σ) ^ orderOf σ = Nat.card F := fixedField_card_pow σ
  have hq₀1 : 1 < Nat.card ↥(fixedField σ) := one_lt_card_fixedField σ
  have hlt := two_part_sl2_lt (Nat.card ↥(fixedField σ)) (orderOf σ) hodd₀ hq₀1 hev
    (orderOf_pos σ).ne'
  rw [hq, ← CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    ← CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at hlt
  have h1 : c + 1 ≤ (Nat.card (SpecialLinearGroup (Fin 2) ↥(fixedField σ))).factorization 2 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h0
  have h2 : c + 1 = (Nat.card (SpecialLinearGroup (Fin 2) F)).factorization 2 :=
    Nat.pow_right_injective (le_refl 2) hbig
  omega

end Big

section Glue

variable {F : Type} [Field F] [Finite F] {Q : Type} [Group Q]

theorem field_part_ne_one_of_fixedCond (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Q ≃* SpecialLinearGroup (Fin 2) F) (φ : MulAut Q) (hφ1 : φ ≠ 1) (hf : FixedCond Q φ) :
    (gammaOf hodd h3 (MulAut.congr e φ)).right ≠ 1 := by
  have hα1 : MulAut.congr e φ ≠ 1 := fun h =>
    hφ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  intro hσ
  obtain ⟨G, hG⟩ := eq_slConjugation_of_right_eq_one hodd h3 _ hσ
  apply not_fixedCond_of_comm φ _ hf
  apply comm_fixed_of_congr e φ
  rw [hG]
  exact fixed_comm_of_slConjugation G (hG ▸ hα1)

theorem three_lt_card_of_isQuasisimple [Finite Q] (hodd : Odd (Nat.card F))
    (e : Q ≃* SpecialLinearGroup (Fin 2) F) (hq : CFSG.IsQuasisimple Q) : 3 < Nat.card F := by
  by_contra hle
  have hlt : 1 < Nat.card F := Finite.one_lt_card
  have h3 : Nat.card F = 3 := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have hcard : Nat.card Q = 2 ^ 3 * 3 ^ 1 := by
    rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h3]
    norm_num
  have hsolv : Group.IsSolvable Q := by
    let _ : Fintype Q := Fintype.ofFinite Q
    exact Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hnt : Nontrivial Q := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [hcard]
    norm_num
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial Q).ne (haveI := hq.1; Group.IsPerfect.commutator_eq_top)

end Glue

section Main

theorem ivk_1_19_V : IVK_1_19_V := by
  intro G _ _ z S K F h hFc hmod s hs hsR V hVP hVc hVidx
  classical
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h6 : Std6r1 G z S K := h.toStd6r1
  have hKc : IsPCompIn 2 (centralizer ({z} : Set G)) K := std6r1_comp_isPCompIn h6
  have hS2 : IsPGroup 2 ↥S := std6r1_S_pgroup h6
  have hsyl := std6r1_exists_sylow_P h6
  have hPz : Pz S z = S ⊓ K := std6r1_Pz_eq h6
  have hRz : Rz S z = (S ⊓ K) ⊔ (S ⊓ cSec K) := std6r1_Rz_eq h6
  rw [hPz] at hs hVP hVidx
  rw [hRz] at hsR
  have hFS : F ≤ S := h.F_le
  have hsS : s ∈ S := (sup_le inf_le_left hFS) hs
  have hsN : s ∈ normalizer (K : Set G) := std6r1_S_normalizes h6 hsS
  obtain ⟨F₁, hF₁f, hF₁fin, hodd, ⟨e₀⟩⟩ := hmod
  let e : Hat K ≃* SpecialLinearGroup (Fin 2) F₁ :=
    e₀.trans (specialLinearGroupEquivStatedSL 2 F₁).symm
  have hq : CFSG.IsQuasisimple (Hat K) := TwoThin.isQuasisimple_hat hKc
  have h3 : 3 < Nat.card F₁ := three_lt_card_of_isQuasisimple hodd e hq
  obtain ⟨g, hg⟩ := hVc.exists_generator
  have hv₀V : (g : G) ∈ V := g.2
  have hv₀K : (g : G) ∈ K := (hVP g.2).2
  have hVord : orderOf (g : G) = Nat.card ↥V := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hPcard : Nat.card ↥(S ⊓ K) = 2 * Nat.card ↥V := by
    have h1 := Subgroup.relIndex_mul_card (H := V) (K := S ⊓ K)
    rw [inf_eq_left.2 hVP, hVidx] at h1
    exact h1.symm
  have hPA : Nat.card ↥(S ⊓ K) = 2 ^ (Nat.card (SpecialLinearGroup (Fin 2) F₁)).factorization 2 := by
    rw [card_P_eq_abs hS2 hsyl, Nat.card_congr e.toEquiv]
  have hA3 := three_le_two_part_sl2 hodd
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (Nat.card (SpecialLinearGroup (Fin 2) F₁)).factorization 2 = c + 1 :=
    ⟨(Nat.card (SpecialLinearGroup (Fin 2) F₁)).factorization 2 - 1, by omega⟩
  have hVc2 : Nat.card ↥V = 2 ^ c := by
    rw [hPA, hc, pow_succ] at hPcard
    omega
  have hbig : 2 ^ (c + 1) = 2 ^ (Nat.card (SpecialLinearGroup (Fin 2) F₁)).factorization 2 := by
    rw [hc]
  have hv₀o : orderOf (g : G) = 2 ^ c := hVord.trans hVc2
  have hzp : IsPGroup 2 ↥(zpowers (g : G)) :=
    IsPGroup.of_card (n := c) (by rw [Nat.card_zpowers, hv₀o])
  have hzle : zpowers (g : G) ≤ K := zpowers_le.2 hv₀K
  obtain ⟨b, hb⟩ : ∃ b : Hat K, b = hatMk K ⟨(g : G), hv₀K⟩ := ⟨_, rfl⟩
  have hbo : orderOf b = 2 ^ c := by
    have := orderOf_hatMk hzle hzp (mem_zpowers (g : G))
    rw [hv₀o] at this
    rw [hb]
    exact this
  have hφb : phi K s hsN b = b := by
    rw [hb, phi_mk K hsN]
    congr 1
    apply Subtype.ext
    have := hcon (g : G) hv₀V
    show s * (g : G) * s⁻¹ = (g : G)
    rw [this]
    group
  have hFnorm : F ≤ normalizer ((S ⊓ K : Subgroup G) : Set G) := by
    intro f hf
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    exact ⟨S.mul_mem (S.mul_mem (hFS hf) hn.1) (S.inv_mem (hFS hf)),
      (Subgroup.mem_normalizer_iff.1 (std6r1_S_normalizes h6 (hFS hf)) n).1 hn.2⟩
  have hs' : s ∈ F ⊔ (S ⊓ K) := by rwa [sup_comm] at hs
  obtain ⟨f₀, hf₀, p₀, hp₀, hsfp⟩ := M.mem_sup_of_le_normalizer hFnorm hs'
  obtain ⟨hf₀N, hFa⟩ := h.F_fAut f₀ hf₀
  have hp₀N : p₀ ∈ normalizer (K : Set G) := le_normalizer hp₀.2
  have hφ : phi K s hsN = phi K f₀ hf₀N * MulAut.conj (hatMk K ⟨p₀, hp₀.2⟩) := by
    rw [phi_congr K hsfp hsN (mul_mem hf₀N hp₀N), phi_mul K hf₀N hp₀N, phi_of_mem K hp₀.2]
  have hσ : (gammaOf hodd h3 (MulAut.congr e (phi K s hsN))).right =
      (gammaOf hodd h3 (MulAut.congr e (phi K f₀ hf₀N))).right := by
    rw [hφ, map_mul, gammaOf_mul_right, congr_conj, gammaOf_conj_right, mul_one]
  have hφf1 : phi K f₀ hf₀N ≠ 1 := by
    intro h1
    have hcs := (phi_eq_one_iff K hf₀N).1 h1
    apply hsR
    rw [hsfp]
    exact mul_mem (mem_sup_right ⟨hFS hf₀, hcs⟩) (mem_sup_left hp₀)
  have hσ1 := field_part_ne_one_of_fixedCond hodd h3 e (phi K f₀ hf₀N) hφf1 hFa.2.2.2.2
  obtain ⟨k, hk⟩ := hFa.2.2.2.1
  have hσ2 : ∃ j : ℕ, orderOf (gammaOf hodd h3 (MulAut.congr e (phi K f₀ hf₀N))).right = 2 ^ j := by
    have h1 : orderOf (MulAut.congr e (phi K f₀ hf₀N)) = 2 ^ k := by
      rw [MulEquiv.orderOf_eq]
      exact hk
    have h2 := orderOf_map_dvd
      ((SemidirectProduct.rightHom : PGammaL2 F₁ →* (F₁ ≃+* F₁)).comp (gammaOf hodd h3))
      (MulAut.congr e (phi K f₀ hf₀N))
    rw [h1] at h2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    exact ⟨j, hj⟩
  rw [← hσ] at hσ1 hσ2
  exact not_fixes_big_cyclic hodd h3 e (phi K s hsN) hσ1 hσ2 hφb hbo hbig

end Main

end CFSG.GH74.GLS.IVK.Lifted
