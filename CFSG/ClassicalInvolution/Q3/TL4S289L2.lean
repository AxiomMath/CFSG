module

public import CFSG.ClassicalInvolution.Q3.TL4S289Exit
public import CFSG.ClassicalInvolution.Q3.TL4MF164L2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint CFSG.GorensteinWalter

namespace S289L2

variable {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {z : X}

theorem natCard_eq_four_of_mem_USet (hd : TightDatum R S z)
    (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) {U : Subgroup X}
    (hU : U ∈ USet (CoreAssembly.conjClass (tightCore R))) : Nat.card U = 4 := by
  obtain ⟨e⟩ := hq
  have hΩ := hd.hypOmegaGen
  obtain ⟨R', -, J', hJ', hR'J', -, -, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  have hS8 : Nat.card ↥((S : Subgroup R).map R.subtype) = 8 := by
    rw [Subgroup.card_map_of_injective R.subtype_injective, Nat.card_congr e.toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h8 := Sec6Gen.natCard_isSylow2In_eq hΩ (CoreAssembly.mem_conjClass_self _) hJ'
    hd.sylow_core hR'J'
  omega

omit [Finite X] in
theorem orderOf_gen_eq_four' {U : Subgroup X} {s : U} (hs : ∀ x : U, x ∈ Subgroup.zpowers s)
    (hU4 : Nat.card U = 4) : orderOf (s : X) = 4 := by
  rw [Subgroup.orderOf_coe, ← hU4, orderOf_eq_card_of_forall_mem_zpowers hs]

omit [Finite X] in
theorem sq_eq_of_orderOf_four {J : Subgroup X} {w s : X} (hw : IsUniqueInvolution J w)
    (hsJ : s ∈ J) (hs4 : orderOf s = 4) : s ^ 2 = w := by
  have h2 : orderOf (s ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hs4]; norm_num), hs4]
  rcases hw.unique _ (J.pow_mem hsJ 2)
    (by rw [← pow_add]; exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hs4])) with h | h
  · rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · exact h

end S289L2

open S289L2 in
theorem secIdE3L2NoStar_proved : SecIdE3L2NoStar := by
  intro X _ _ R S z hm hs hidx p f hp hp2 hfe hL L hLΩ
  have : Fact p.Prime := ⟨hp⟩
  have hd := hm.datum
  have hΩ := hd.hypOmegaGen
  refine Set.eq_empty_of_forall_notMem fun J hJ => ?_
  obtain ⟨hJΩ, hJL, U, hU, hUJ, hUN⟩ := hJ
  have hU4 := natCard_eq_four_of_mem_USet hd hm.cls.1 hU
  obtain ⟨-, -, -, -, -, -, hUc, -, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  obtain ⟨s, hs'⟩ := hUc.exists_generator
  have hs4 : orderOf (s : X) = 4 := orderOf_gen_eq_four' hs' hU4
  obtain ⟨zJ, hzJ⟩ := hd.exists_isUniqueInvolution_member hJΩ
  obtain ⟨zL, hzL⟩ := hd.exists_isUniqueInvolution_member hLΩ
  have hsJ : (s : X) ^ 2 = zJ := sq_eq_of_orderOf_four hzJ (hUJ s.2) hs4
  have hsL : (s : X) * zL * (s : X)⁻¹ = zL :=
    hzL.conj_eq (conjSub_eq_of_mem_normalizer (hUN s.2))
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := MF164.exists_fstar_equiv_psl2 hs hL
  set N := genFittingFStar X with hNdef
  have : N.Normal := genFittingFStar_normal X
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · have h1 : 1 < Nat.card F := Finite.one_lt_card
      rw [hF, h, pow_zero] at h1
      omega
    · exact h
  have hK : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hp.odd_of_ne_two hp2, hf1, hF⟩
  have hcard : 3 < Nat.card F := by
    obtain ⟨k, hk⟩ := hfe
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    rw [hF, hk, ← two_mul, pow_mul]
    calc 3 < 3 ^ 2 := by norm_num
      _ ≤ (p ^ 2) := Nat.pow_le_pow_left h3 2
      _ ≤ (p ^ 2) ^ k := Nat.le_self_pow (by omega) _
  have hsurj := pGammaL2ToMulAutPSL2_surjective F hF hK hcard
  have hnab : ∃ a b : N, a * b ≠ b * a := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have hc : Subgroup.center (PSL2 F) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      apply e.symm.injective
      rw [map_mul, map_mul, h]
    have hnt : Nontrivial (PSL2 F) := inferInstance
    rw [psl2_center_eq_bot F] at hc
    exact bot_ne_top hc
  have hC : Subgroup.centralizer (N : Set X) = ⊥ := centralizer_genFittingFStar_eq_bot hnab
  set ι := normalPSL2ToPGammaL2 N F hK hcard e hsurj with hιdef
  have hιinj : Function.Injective ι := normalPSL2ToPGammaL2_injective N F hK hcard e hC hsurj
  obtain ⟨i, hi⟩ : ∃ i : F, i * i = -1 := by
    have := Fintype.ofFinite F
    have h4 : Fintype.card F % 4 ≠ 3 := by
      rw [← Nat.card_eq_fintype_card, hF]
      obtain ⟨k, hk⟩ := hfe
      obtain ⟨m, hm'⟩ := (hp.odd_of_ne_two hp2).pow (n := k)
      rw [hk, show p ^ (k + k) = (p ^ k) ^ 2 by ring, hm',
        show (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 by ring]
      omega
    obtain ⟨i, hi⟩ := FiniteField.isSquare_neg_one_iff.2 h4
    exact ⟨i, hi.symm⟩
  have hconj : ∀ w ∈ N, w * w = 1 → w ≠ 1 → ∃ x c : PGL2 F, ι w = SemidirectProduct.inl x ∧
      c ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ∧
      (SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) : PGammaL2 F) =
        SemidirectProduct.inl c * SemidirectProduct.inl x * (SemidirectProduct.inl c)⁻¹ := by
    intro w hwN hw2 hw1
    set x := Matrix.ProjectiveSpecialLinearGroup.toPGL (e ⟨w, hwN⟩) with hxdef
    have hιw : ι w = SemidirectProduct.inl x :=
      normalPSL2ToPGammaL2_apply_subtype N F hK hcard e hsurj ⟨w, hwN⟩
    have hx1 : x ≠ 1 := fun h => hw1 (hιinj (by rw [hιw, h, map_one, map_one]))
    have hx2 : x * x = 1 := by
      apply SemidirectProduct.inl_injective (φ := pgl2FieldAut F)
      rw [map_mul, ← hιw, ← map_mul, hw2, map_one, map_one]
    obtain ⟨c, hc, hcx⟩ := MF164.exists_conj_s0 hK hcard hi ⟨_, rfl⟩ hx1 hx2
    exact ⟨x, c, hιw, hc, by rw [← hcx, map_mul, map_mul, map_inv]⟩
  obtain ⟨eS⟩ := hm.cls.1
  have hzN : z ∈ N := by
    set φ : QuaternionGroup 2 →* X :=
      R.subtype.comp ((S : Subgroup R).subtype.comp eS.symm.toMonoidHom) with hφ
    have hφi : Function.Injective φ :=
      R.subtype_injective.comp ((S : Subgroup R).subtype_injective.comp eS.symm.injective)
    have hwR : φ (QuaternionGroup.a 1) ∈ R :=
      ((eS.symm (QuaternionGroup.a 1) : ↥(S : Subgroup R)) : ↥R).2
    have hw4 : orderOf (φ (QuaternionGroup.a 1)) = 4 := by
      rw [orderOf_injective φ hφi, QuaternionGroup.orderOf_a_one]
    have hwz : φ (QuaternionGroup.a 1) ^ 2 = z := hd.eq_of_orderOf_eq_two (R.pow_mem hwR 2) (by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hw4]; norm_num), hw4])
    rw [← hwz]
    exact MF164.sq_mem_of_index_le_two hidx _
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class (tightCore R) L hLΩ
  have hzLa : zL = a * z * a⁻¹ := (hd.isUniqueInvolution_core.conj a).eq hzL |>.symm
  have hzLN : zL ∈ N := by
    rw [hzLa]
    exact (genFittingFStar_normal X).conj_mem z hzN a
  by_cases h4f : 4 ∣ f
  · obtain ⟨x, c, hιz, hc, hs0x⟩ :=
      hconj z hzN hd.isUniqueInvolution_core.sq hd.isUniqueInvolution_core.ne_one
    exact MF164.false_of_datum hp hp2 hf1 hF h4f hm hιinj (fun w => ⟨(e.symm w : X), by
      rw [hιdef, normalPSL2ToPGammaL2_apply_subtype N F hK hcard e hsurj,
        MulEquiv.apply_symm_apply]⟩) hιz hc hs0x
  obtain ⟨x, c, hιzL, -, hs0x⟩ := hconj zL hzLN hzL.sq hzL.ne_one
  set g : PGammaL2 F :=
    SemidirectProduct.inl c * ι (s : X) * (SemidirectProduct.inl c)⁻¹ with hg
  have hιsx : ι (s : X) * SemidirectProduct.inl x = SemidirectProduct.inl x * ι (s : X) := by
    rw [← hιzL, ← map_mul, ← map_mul]
    congr 1
    calc (s : X) * zL = (s : X) * zL * (s : X)⁻¹ * s := by group
      _ = zL * s := by rw [hsL]
  have hgs : g * SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) =
      SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) * g := by
    rw [hs0x, hg]
    calc _ = SemidirectProduct.inl c * (ι (s : X) * SemidirectProduct.inl x) *
          (SemidirectProduct.inl c)⁻¹ := by group
      _ = SemidirectProduct.inl c * (SemidirectProduct.inl x * ι (s : X)) *
          (SemidirectProduct.inl c)⁻¹ := by rw [hιsx]
      _ = _ := by group
  have hs4' : (s : X) ^ 4 = 1 := by rw [← hs4, pow_orderOf_eq_one]
  have hg4 : g ^ 4 = 1 := by
    rw [hg, conj_pow, ← map_pow, hs4', map_one, mul_one, mul_inv_cancel]
  have hunconj : ∀ y : PGammaL2 F, (SemidirectProduct.inl c : PGammaL2 F) * (ι (s : X)) ^ 2 *
      (SemidirectProduct.inl c)⁻¹ = SemidirectProduct.inl c * y * (SemidirectProduct.inl c)⁻¹ →
      (ι (s : X)) ^ 2 = y := fun y h => by
    calc (ι (s : X)) ^ 2 = (SemidirectProduct.inl c)⁻¹ * (SemidirectProduct.inl c *
          (ι (s : X)) ^ 2 * (SemidirectProduct.inl c)⁻¹) * SemidirectProduct.inl c := by group
      _ = y := by rw [h]; group
  have hsq : (s : X) ^ 2 = zL := by
    rcases MF164.sq_eq_of_commute_s0 hK (MF164.sq_eq_one_of_pow_four hp hf1 hF h4f) hgs hg4 with
      h | h
    · exfalso
      rw [hg, conj_pow] at h
      have h1 : ι ((s : X) ^ 2) = ι 1 := by
        rw [map_pow, map_one]
        exact hunconj 1 (by rw [h]; group)
      have h4 := orderOf_dvd_of_pow_eq_one (hιinj h1)
      rw [hs4] at h4
      omega
    · rw [hg, conj_pow, hs0x] at h
      apply hιinj
      rw [map_pow, hιzL]
      exact hunconj _ h
  have hzJL : zJ = zL := hsJ.symm.trans hsq
  exact hJL (hd.eq_of_isUniqueInvolution_member hJΩ hLΩ hzJ (hzJL ▸ hzL))
