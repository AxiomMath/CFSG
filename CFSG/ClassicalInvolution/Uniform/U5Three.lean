module

public import CFSG.ClassicalInvolution.Uniform.U3Witness
public import CFSG.ClassicalInvolution.Uniform.U5Util

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups commutatorElement

section Edge

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem natCard_sl2_galoisField_three : Nat.card SL(2, GaloisField 3 1) = 24 := by
  have hF : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  norm_num

theorem two_pow_factorization_24 : (2 : ℕ) ^ (Nat.factorization 24) 2 = 8 := by
  have h : (Nat.factorization 24) 2 = 3 := by
    rw [Nat.factorization_def _ Nat.prime_two]
    have h1 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [h1, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
    have h0 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    omega
  rw [h]
  norm_num

theorem exists_card_eight_of_quaternion_pairs {K J : Subgroup G} (hKJ : Commutes K J)
    {z i j i' j' : G} (hiK : i ∈ K) (hjK : j ∈ K) (hi'J : i' ∈ J) (hj'J : j' ∈ J)
    (hzJ : z ∈ J) (hz1 : z ≠ 1) (hzz : z * z = 1) (hii : i * i = z) (hjj : j * j = z)
    (hi'i' : i' * i' = z) (hj'j' : j' * j' = z) (hij : i * j = z * (j * i))
    (hij' : i' * j' = z * (j' * i')) :
    ∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  have zi : Commute z i := by
    show z * i = i * z
    rw [← hii]; group
  have zj : Commute z j := by
    show z * j = j * z
    rw [← hjj]; group
  have zi' : Commute z i' := by
    show z * i' = i' * z
    rw [← hi'i']; group
  have zj' : Commute z j' := by
    show z * j' = j' * z
    rw [← hj'j']; group
  have c1 : i * i' = i' * i := hKJ i hiK i' hi'J
  have c2 : i * j' = j' * i := hKJ i hiK j' hj'J
  have c3 : j * i' = i' * j := hKJ j hjK i' hi'J
  have c4 : j * j' = j' * j := hKJ j hjK j' hj'J
  have hnc : i * j ≠ j * i := by
    intro h
    rw [hij] at h
    have h' : z * (j * i) = 1 * (j * i) := by rw [one_mul]; exact h
    exact hz1 (mul_right_cancel h')
  have hiJ : i ∉ J := fun h => hnc (hKJ j hjK i h).symm
  have hjJ : j ∉ J := fun h => hnc (hKJ i hiK j h)
  have zji : z * (j * i) = (j * i) * z := (zj.mul_right zi).eq
  have zji' : z * (j' * i') = (j' * i') * z := (zj'.mul_right zi').eq
  have zii' : z * (i * i') = (i * i') * z := (zi.mul_right zi').eq
  have zjj' : z * (j * j') = (j * j') * z := (zj.mul_right zj').eq
  have haa : (i * i') * (i * i') = 1 := by
    calc (i * i') * (i * i') = i * (i' * i) * i' := by group
      _ = i * (i * i') * i' := by rw [← c1]
      _ = (i * i) * (i' * i') := by group
      _ = 1 := by rw [hii, hi'i', hzz]
  have hbb : (j * j') * (j * j') = 1 := by
    calc (j * j') * (j * j') = j * (j' * j) * j' := by group
      _ = j * (j * j') * j' := by rw [← c4]
      _ = (j * j) * (j' * j') := by group
      _ = 1 := by rw [hjj, hj'j', hzz]
  have hab : (i * i') * (j * j') = (j * j') * (i * i') := by
    calc (i * i') * (j * j') = i * (i' * j) * j' := by group
      _ = i * (j * i') * j' := by rw [← c3]
      _ = (i * j) * (i' * j') := by group
      _ = (z * (j * i)) * (z * (j' * i')) := by rw [hij, hij']
      _ = ((j * i) * z) * (z * (j' * i')) := by rw [zji]
      _ = (j * i) * (z * z) * (j' * i') := by group
      _ = (j * i) * (j' * i') := by rw [hzz, mul_one]
      _ = j * (i * j') * i' := by group
      _ = j * (j' * i) * i' := by rw [c2]
      _ = (j * j') * (i * i') := by group
  have ha1 : i * i' ≠ 1 := by
    intro h
    apply hiJ
    rw [eq_inv_of_mul_eq_one_left h]
    exact J.inv_mem hi'J
  have ha_z : i * i' ≠ z := by
    intro h
    apply hiJ
    rw [eq_mul_inv_of_mul_eq h]
    exact J.mul_mem hzJ (J.inv_mem hi'J)
  have hb1 : j * j' ≠ 1 := by
    intro h
    apply hjJ
    rw [eq_inv_of_mul_eq_one_left h]
    exact J.inv_mem hj'J
  have hb_z : j * j' ≠ z := by
    intro h
    apply hjJ
    rw [eq_mul_inv_of_mul_eq h]
    exact J.mul_mem hzJ (J.inv_mem hj'J)
  have hb_a : j * j' ≠ i * i' := by
    intro h
    have hm : i⁻¹ * j = i' * j'⁻¹ := by
      calc i⁻¹ * j = i⁻¹ * (j * j') * j'⁻¹ := by group
        _ = i⁻¹ * (i * i') * j'⁻¹ := by rw [h]
        _ = i' * j'⁻¹ := by group
    have hmJ : i⁻¹ * j ∈ J := by
      rw [hm]
      exact J.mul_mem hi'J (J.inv_mem hj'J)
    have e1 : i * (i⁻¹ * j) = (i⁻¹ * j) * i := hKJ i hiK _ hmJ
    have e2 : j = i⁻¹ * j * i := by
      calc j = i * (i⁻¹ * j) := by group
        _ = (i⁻¹ * j) * i := e1
    apply hnc
    calc i * j = i * (i⁻¹ * j * i) := by rw [← e2]
      _ = j * i := by group
  have hb_za : j * j' ≠ z * (i * i') := by
    intro h
    have hm : i⁻¹ * z * j = i' * j'⁻¹ := by
      have e0 : i⁻¹ * z * (z * (i * i')) = i' := by
        calc i⁻¹ * z * (z * (i * i')) = i⁻¹ * (z * z) * (i * i') := by group
          _ = i⁻¹ * 1 * (i * i') := by rw [hzz]
          _ = i' := by group
      calc i⁻¹ * z * j = (i⁻¹ * z * (j * j')) * j'⁻¹ := by group
        _ = (i⁻¹ * z * (z * (i * i'))) * j'⁻¹ := by rw [h]
        _ = i' * j'⁻¹ := by rw [e0]
    have hmJ : i⁻¹ * z * j ∈ J := by
      rw [hm]
      exact J.mul_mem hi'J (J.inv_mem hj'J)
    have e1 : i * (i⁻¹ * z * j) = (i⁻¹ * z * j) * i := hKJ i hiK _ hmJ
    have zi_inv : z * i⁻¹ = i⁻¹ * z := zi.inv_right.eq
    have e2 : z * j = z * (i⁻¹ * j * i) := by
      calc z * j = i * (i⁻¹ * z * j) := by group
        _ = (i⁻¹ * z * j) * i := e1
        _ = (z * i⁻¹) * j * i := by rw [zi_inv]
        _ = z * (i⁻¹ * j * i) := by group
    have e3 : j = i⁻¹ * j * i := mul_left_cancel e2
    apply hnc
    calc i * j = i * (i⁻¹ * j * i) := by rw [← e3]
      _ = j * i := by group
  exact exists_isElemAbelian_card_eight hzz haa hbb zii' zjj' hab hz1 ha1 hb1 ha_z hb_z hb_a hb_za

theorem neg_one_ne_one_sl2_three {F : Type} [Field F] (hF : (3 : F) = 0) :
    (-1 : SL(2, F)) ≠ 1 := by
  intro h
  have h1 := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp at h1
  have h2 : (2 : F) = 0 := by linear_combination (-1 : F) * h1
  exact one_ne_zero (show (1 : F) = 0 by linear_combination hF - h2)

omit [Finite G] in
theorem coe_symm_neg_one_eq {K : Subgroup G} {z : G} (u : IsUniqueInvolution K z)
    (e : K ≃* SL(2, GaloisField 3 1)) : ((e.symm (-1) : K) : G) = z := by
  have hF : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  have h3 : (3 : GaloisField 3 1) = 0 := by
    have h : Nat.card (GaloisField 3 1) • (1 : GaloisField 3 1) = 0 := card_nsmul_eq_zero'
    rw [hF] at h
    simpa using h
  have hsq : (e.symm (-1) : K) * (e.symm (-1) : K) = 1 := by
    rw [← map_mul]
    simp
  have hne : (e.symm (-1) : K) ≠ 1 := by
    intro h
    apply neg_one_ne_one_sl2_three h3
    have := congrArg e h
    simpa using this
  have hsq' : ((e.symm (-1) : K) : G) * ((e.symm (-1) : K) : G) = 1 := by
    have := congrArg Subtype.val hsq
    simpa using this
  refine (u.unique _ (e.symm (-1)).2 hsq').resolve_left fun h => hne (Subtype.ext h)

theorem exists_card_eight_of_commuting_twins {K J : Subgroup G} {z : G} (hKJ : Commutes K J)
    (eK : K ≃* SL(2, GaloisField 3 1)) (eJ : J ≃* SL(2, GaloisField 3 1))
    (hzK : ((eK.symm (-1) : K) : G) = z) (hzJ : ((eJ.symm (-1) : J) : G) = z)
    (hz1 : z ≠ 1) (hzz : z * z = 1) :
    ∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  have hF : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  obtain ⟨A, B, hAA, hBB, hAB⟩ := exists_quaternion_sl2_three hF
  have hABm : A * B = (-1) * (B * A) := by
    rw [commutatorElement_def] at hAB
    calc A * B = (A * B * A⁻¹ * B⁻¹) * (B * A) := by group
      _ = (-1) * (B * A) := by rw [hAB]
  refine exists_card_eight_of_quaternion_pairs (K := K) (J := J) hKJ (z := z)
    (i := ((eK.symm A : K) : G)) (j := ((eK.symm B : K) : G)) (i' := ((eJ.symm A : J) : G))
    (j' := ((eJ.symm B : J) : G)) (eK.symm A).2 (eK.symm B).2 (eJ.symm A).2 (eJ.symm B).2
    (hzJ ▸ (eJ.symm (-1)).2) hz1 hzz ?_ ?_ ?_ ?_ ?_ ?_
  · have : (eK.symm A : K) * (eK.symm A) = eK.symm (-1) := by rw [← map_mul, hAA]
    rw [← hzK, ← this]
    rfl
  · have : (eK.symm B : K) * (eK.symm B) = eK.symm (-1) := by rw [← map_mul, hBB]
    rw [← hzK, ← this]
    rfl
  · have : (eJ.symm A : J) * (eJ.symm A) = eJ.symm (-1) := by rw [← map_mul, hAA]
    rw [← hzJ, ← this]
    rfl
  · have : (eJ.symm B : J) * (eJ.symm B) = eJ.symm (-1) := by rw [← map_mul, hBB]
    rw [← hzJ, ← this]
    rfl
  · have : (eK.symm A : K) * (eK.symm B) = eK.symm (-1) * ((eK.symm B) * (eK.symm A)) := by
      rw [← map_mul, ← map_mul, ← map_mul, ← hABm]
    rw [← hzK]
    exact congrArg Subtype.val this
  · have : (eJ.symm A : J) * (eJ.symm B) = eJ.symm (-1) * ((eJ.symm B) * (eJ.symm A)) := by
      rw [← map_mul, ← map_mul, ← map_mul, ← hABm]
    rw [← hzJ]
    exact congrArg Subtype.val this

theorem false_of_omegaNbr_of_small (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hex : ExactMembers Ω)
    (hG : ¬ 2 ^ 6 ∣ Nat.card G) (hrank : CFSG.Open.twoRank G ≤ 2) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) : False := by
  obtain ⟨hJΩ, hne, R, hR, hRJ, hRN⟩ := hJ
  have h24 : ∀ L ∈ Ω, Nat.card L = 24 := fun L hL =>
    (natCard_memberU hΩ hex hL).trans natCard_sl2_galoisField_three
  obtain ⟨J', hJ'Ω, P, rfl⟩ := hR
  have hR8 : Nat.card (Subgroup.map J'.subtype (P : Subgroup ↥J')) = 8 := by
    rw [Subgroup.card_map_of_injective J'.subtype_injective, Sylow.card_eq_multiplicity,
      h24 J' hJ'Ω, two_pow_factorization_24]
  set R : Subgroup G := Subgroup.map J'.subtype (P : Subgroup ↥J') with hRdef
  obtain ⟨zK, hzK⟩ := hΩ.classical K hK
  obtain ⟨zJ, hzJ⟩ := hΩ.classical J hJΩ
  have uK := hzK.isUniqueInvolution_sl2
  have uJ := hzJ.isUniqueInvolution_sl2
  have hKJne : K ≠ J := hne.symm
  obtain ⟨hv, -⟩ := hΩ.omega4 K hK J hJΩ hKJne
  have hcdvd8 : Nat.card ↥(K ⊓ R) ∣ 2 ^ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_right : K ⊓ R ≤ R)
    rwa [hR8] at this
  have hcdvdKJ : Nat.card ↥(K ⊓ R) ∣ Nat.card ↥(K ⊓ J) :=
    Subgroup.card_dvd_of_le (inf_le_inf_left K hRJ)
  have hnot4 : ¬ 4 ∣ Nat.card ↥(K ⊓ R) := by
    intro h4
    have h4' : 2 ^ 2 ∣ Nat.card ↥(K ⊓ J) := by
      have := h4.trans hcdvdKJ
      simpa using this
    have := (padicValNat_dvd_iff_le Nat.card_pos.ne').mp h4'
    omega
  have hc12 : Nat.card ↥(K ⊓ R) = 1 ∨ Nat.card ↥(K ⊓ R) = 2 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcdvd8
    interval_cases k
    · exact Or.inl (by simpa using hk')
    · exact Or.inr (by simpa using hk')
    · exact absurd (by rw [hk']; norm_num) hnot4
    · exact absurd (by rw [hk']; norm_num) hnot4
  have hprod := CFSG.ClassicalInvolution.Asc77.ChainFrame.card_sup_mul_card_inf' hRN
  rw [h24 K hK, hR8] at hprod
  have hdvd : Nat.card ↥(R ⊔ K) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  have hc2 : Nat.card ↥(K ⊓ R) = 2 := by
    rcases hc12 with h | h
    · exfalso
      rw [h] at hprod
      apply hG
      have h192 : Nat.card ↥(R ⊔ K) = 192 := by omega
      rw [h192] at hdvd
      exact dvd_trans (by norm_num) hdvd
    · exact h
  have : Nontrivial ↥(K ⊓ R) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : ↥(K ⊓ R))
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx2 : x * x = 1 := by
    have h := pow_card_eq_one' (G := ↥(K ⊓ R)) (x := (⟨x, hx⟩ : ↥(K ⊓ R)))
    rw [hc2] at h
    have h' := congrArg Subtype.val h
    simpa [pow_two] using h'
  have hxK : x ∈ K := hx.1
  have hxJ : x ∈ J := hRJ hx.2
  have hxzK : x = zK := (uK.unique x hxK hx2).resolve_left hx1'
  have hxzJ : x = zJ := (uJ.unique x hxJ hx2).resolve_left hx1'
  have hKJcomm : Commutes K J := by
    refine (hΩ.omega4_commutes hex hK hJΩ hKJne).2 ?_
    have hord : orderOf (⟨x, hxK, hxJ⟩ : ↥(K ⊓ J)) = 2 :=
      orderOf_eq_prime (by ext; simpa [pow_two] using hx2)
        (fun h => hx1' (by simpa using congrArg Subtype.val h))
    have h2 : 2 ∣ Nat.card ↥(K ⊓ J) := hord ▸ orderOf_dvd_natCard _
    have h2' : 1 ≤ padicValNat 2 (Nat.card ↥(K ⊓ J)) :=
      (padicValNat_dvd_iff_le (Nat.card_pos (α := ↥(K ⊓ J))).ne').mp
        (by simpa using h2 : 2 ^ 1 ∣ Nat.card ↥(K ⊓ J))
    omega
  obtain ⟨eK⟩ := hzK.nonempty_equiv_sl2_of_exact (hex K hK)
  obtain ⟨eJ⟩ := hzJ.nonempty_equiv_sl2_of_exact (hex J hJΩ)
  have hz1 : zK ≠ 1 := uK.ne_one
  obtain ⟨E, hE, hE8⟩ := exists_card_eight_of_commuting_twins hKJcomm eK eJ
    (coe_symm_neg_one_eq uK eK) ((coe_symm_neg_one_eq uJ eJ).trans (hxzJ.symm.trans hxzK))
    hz1 uK.sq
  have := three_le_twoRank_of_card_eight E hE hE8
  omega

end Edge

end CFSG.ClassicalInvolution.Uniform
