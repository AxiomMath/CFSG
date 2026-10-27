module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFHeP

public section

namespace CFSG.ComponentClassification.SolMax.He11

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {A : Type*} [Group A]

theorem not_hasOddA_of_prime_dvd {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hpA : p ∣ Nat.card A) (hpY : ¬ p ∣ Nat.card Y) : ¬ FiveFHe.HasOddA Y A := by
  rintro ⟨S, -, -, ρ, hρ, -⟩
  apply hpY
  have h1 := FiveFHe.card_eq_card_ker_mul hρ
  exact (hpA.trans ⟨Nat.card ρ.ker, by rw [h1, mul_comm]⟩).trans (card_subgroup_dvd_card S)

theorem not_hasOddA_cent1_seven
    (hA : Nat.card A = 2520) :
    ¬ FiveFHe.HasOddA (heP ⊓ centralizer {heT1P} : Subgroup (Equiv.Perm (Fin 8330))) A := by
  have hc1 : Nat.card (heP ⊓ centralizer {heT1P} : Subgroup (Equiv.Perm (Fin 8330))) = 21504 :=
    card_heP_cent1
  exact not_hasOddA_of_prime_dvd (p := 5) (by rw [hA]; norm_num) (by rw [hc1]; norm_num)

theorem not_hasOddA_cent0_seven
    [IsSimpleGroup A] (hA : Nat.card A = 2520) (hnab : ∃ a b : A, a * b ≠ b * a) :
    ¬ FiveFHe.HasOddA (heP ⊓ centralizer {heGenPerm 0} : Subgroup (Equiv.Perm (Fin 8330))) A := by
  intro h
  have hO : pPrimeCore 2 (heP ⊓ centralizer {heGenPerm 0} : Subgroup (Equiv.Perm (Fin 8330))) =
      ⊥ := FiveFHe.pPrimeCore_two_eq_bot_of_oddCore (heInner0_oddCore card_heP_cent0)
  obtain ⟨S, hS, ⟨e⟩⟩ := FiveFHe.exists_mulEquiv_of_hasOddA hO h
  have : IsSimpleGroup S := e.isSimpleGroup
  have hS7 : Nat.card S = 2520 := by rw [Nat.card_congr e.toEquiv, hA]
  have hnabS : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hc0 : Nat.card (heP ⊓ centralizer {heGenPerm 0} : Subgroup (Equiv.Perm (Fin 8330))) =
      161280 := card_heP_cent0
  have hn := FiveFHe.normal_of_isSubnormal_simple hS hnabS (by rw [hS7, hc0]; norm_num)
  obtain ⟨hC, -⟩ := oddCore_eq_bot_of_restrict heInnerGrp0_le heA0_mem_grp0 heA0_ne_one
    heDelta0_injective heInnerGrp0_stab heA0_fix heInnerRes0_range (v := 8)
    (by rw [card_heX0]; norm_num) oddWitness_heX0 (by rw [card_heP_cent0, card_heX0])
  let f : (heP ⊓ centralizer {heGenPerm 0} : Subgroup (Equiv.Perm (Fin 8330))) ≃* heInnerGrp0 :=
    MulEquiv.subgroupCongr hC.symm
  have hcard : Nat.card (S.map f.toMonoidHom) = 2520 := by
    rw [card_map_of_injective f.injective, hS7]
  exact FiveFHe.false_of_normal_heInnerGrp0 (hn.map _ f.surjective) (by rw [hcard]; norm_num)
    (by rw [hcard]; norm_num)

theorem not_hasOddA_heP_seven
    (hA : Nat.card A = 2520) (hnab : ∃ a b : A, a * b ≠ b * a) :
    ¬ FiveFHe.HasOddA heP A := by
  have : IsSimpleGroup heP := heP_simple
  have hnabP : ∃ a b : heP, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : center heP = ⊤ := eq_top_iff.2 fun g _ => mem_center_iff.2 fun g' => h g' g
    rw [heP_center_eq_bot] at htop
    have h2 := congrArg (fun H : Subgroup heP => Nat.card H) htop
    simp only [card_bot, card_top, card_heP] at h2
    norm_num at h2
  refine FiveFHe.not_hasOddA_of_quasisimple (MonoidHom.id heP) Function.injective_id
    (LocalCores.isQuasisimple_of_isSimpleGroup hnabP).1 (fun S _ x _ => ⟨x, rfl⟩) hnab
    fun k hk hodd => ?_
  rw [card_heP, hA] at hk
  obtain ⟨m, rfl⟩ := hodd
  omega

theorem exists_mulEquiv_heAutU
    [IsSimpleGroup A]
    (hA : Nat.card A = 2520) (hnab : ∃ a b : A, a * b ≠ b * a) {G : Type*} [Group G]
    (Θ : G ≃* heP) (s : MulAut G) (hs : s * s = 1) (h : FiveFHe.HasOddA (fixedSubgroup s) A) :
    ∃ Φ : G ≃* heP, MulAut.congr Φ s = heConjR ⟨heAutU, heAutU_mem_heAutGroup⟩ := by
  have hbij := ctbh_full_automorphism_permutation_model.1
  have h0 := h.of_mulEquiv (((fixedSubgroup s).equivMapOfInjective Θ.toMonoidHom
    Θ.injective).trans (MulEquiv.subgroupCongr (FiveFHe.map_fixedSubgroup_congr Θ s)))
  obtain ⟨x, hx⟩ := hbij.2 (MulAut.congr Θ s)
  have hxx : x * x = 1 := hbij.1 (by rw [map_mul, hx, map_one, ← map_mul, hs, map_one])
  rw [← hx] at h0
  by_cases hx1 : x = 1
  · exfalso
    rw [hx1, map_one] at h0
    have htop : fixedSubgroup (1 : MulAut heP) = ⊤ := eq_top_iff.2 fun g _ => rfl
    exact not_hasOddA_heP_seven hA hnab ((h0.of_mulEquiv (MulEquiv.subgroupCongr htop)).of_mulEquiv
      Subgroup.topEquiv)
  have hx2 : orderOf (x : Equiv.Perm (Fin 8330)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq]; exact hxx) hx1
  let e₁ : fixedSubgroup (heConjR x) ≃*
      (heP ⊓ centralizer {(x : Equiv.Perm (Fin 8330))} : Subgroup (Equiv.Perm (Fin 8330))) :=
    ((fixedSubgroup (heConjR x)).equivMapOfInjective heP.subtype heP.subtype_injective).trans
      (MulEquiv.subgroupCongr (map_fixedSubgroup_heConjR x))
  have h1 := h0.of_mulEquiv e₁
  by_cases hxP : (x : Equiv.Perm (Fin 8330)) ∈ heP
  · exfalso
    rcases involution_conj_cases hxP hx2 with ⟨c, hc, hxc⟩ | ⟨c, hc, hxc⟩
    · rw [hxc] at h1
      exact not_hasOddA_cent0_seven hA hnab (h1.of_mulEquiv (infCentralizerConjEquiv hc _))
    · rw [hxc] at h1
      exact not_hasOddA_cent1_seven hA (h1.of_mulEquiv (infCentralizerConjEquiv hc _))
  obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
  refine ⟨Θ.trans (MulAut.conj (⟨g, hg⟩ : heP)⁻¹), MulEquiv.ext fun p => Subtype.ext ?_⟩
  have h2 : ∀ q : heP, ((MulAut.congr Θ s q : heP) : Equiv.Perm (Fin 8330)) =
      (x : Equiv.Perm (Fin 8330)) * q * (x : Equiv.Perm (Fin 8330))⁻¹ := fun q => by
    rw [← hx]
    rfl
  have h4 : MulAut.congr (Θ.trans (MulAut.conj (⟨g, hg⟩ : heP)⁻¹)) s p =
      (⟨g, hg⟩ : heP)⁻¹ * MulAut.congr Θ s (⟨g, hg⟩ * p * (⟨g, hg⟩ : heP)⁻¹) * ⟨g, hg⟩ := by
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
      MulAut.conj_apply, MulAut.conj_symm_apply, inv_inv]
  rw [h4, coe_mul, coe_mul, h2, heConjR_apply]
  simp only [coe_mul, coe_inv]
  rw [hxg]
  group

end CFSG.ComponentClassification.SolMax.He11
