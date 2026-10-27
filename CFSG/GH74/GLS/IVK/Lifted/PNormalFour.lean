module

public import CFSG.GH74.GLS.IVK.Lifted.Rnormal4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Lem45

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5

section Abstract

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_sq_eq_z_of_quat {z : G} {S K : Subgroup G}
    (hPq : ∃ n, IVK.IsQuaternionTwoGroup ↥(S ⊓ K) n)
    (hinv : ∀ x ∈ K, x * x = 1 → x = 1 ∨ x = z) : ∃ u ∈ S ⊓ K, u * u = z := by
  obtain ⟨n, hn3, ⟨ι⟩⟩ := hPq
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  set u : G := ((ι.symm (QuaternionGroup.xa 0) : ↥(S ⊓ K)) : G) with hu
  have huP : u ∈ S ⊓ K := (ι.symm (QuaternionGroup.xa 0)).2
  have huo : orderOf u = 4 := by
    rw [hu, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact QuaternionGroup.orderOf_xa 0
  have husqo : orderOf (u * u) = 2 := by
    rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by rw [huo]; norm_num), huo]
  refine ⟨u, huP, ?_⟩
  rcases hinv (u * u) (K.mul_mem huP.2 huP.2) (mul_self_eq_one_of_orderOf_eq_two husqo) with h1 | h1
  · exact absurd h1 (ne_one_of_orderOf_eq_two husqo)
  · exact h1

theorem z_central_inv {z : G} {S : Subgroup G} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzS : z ∈ S)
    (hzc : ∀ s ∈ S, z * s = s * z) (hStop : M.Syl2In S ⊤)
    (hd : ∃ S' : Sylow 2 G, ∀ g : G, (g ∈ (S' : Subgroup G) ∧
      (∀ s ∈ (S' : Subgroup G), s * g = g * s) ∧ g ^ 2 = 1) ↔ g ∈ zpowers z)
    {x : G} (hxS : x ∈ S) (hxc : ∀ s ∈ S, x * s = s * x) (hx2 : x * x = 1) : x = 1 ∨ x = z := by
  obtain ⟨S', hS'⟩ := hd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS'top : M.Syl2In (S' : Subgroup G) ⊤ :=
    ⟨le_top, S'.isPGroup', by simpa [Subgroup.relIndex_top_right] using Sylow.not_dvd_index S'⟩
  obtain ⟨c, -, hc⟩ := hStop.exists_conj hS'top
  have key : ∀ y ∈ S, (∀ s ∈ S, y * s = s * y) → y * y = 1 → c⁻¹ * y * c ∈ zpowers z := by
    intro y hy hyc hy2
    rw [← hS']
    refine ⟨?_, ?_, ?_⟩
    · rw [hc, M.mem_cj]
      have e : c * (c⁻¹ * y * c) * c⁻¹ = y := by group
      rw [e]; exact hy
    · intro s' hs'
      rw [hc, M.mem_cj] at hs'
      have h1 := hyc _ hs'
      calc s' * (c⁻¹ * y * c) = c⁻¹ * ((c * s' * c⁻¹) * y) * c := by group
        _ = c⁻¹ * (y * (c * s' * c⁻¹)) * c := by rw [h1]
        _ = c⁻¹ * y * c * s' := by group
    · calc (c⁻¹ * y * c) ^ 2 = (c⁻¹ * y * c) * (c⁻¹ * y * c) := pow_two _
        _ = c⁻¹ * (y * y) * c := by group
        _ = 1 := by rw [hy2]; group
  have hcz : c⁻¹ * z * c = z := by
    rcases (M.mem_zpowers_of_sq hz2).1 (key z hzS hzc hz2) with e | e
    · exfalso
      apply hz1
      calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
        _ = 1 := by rw [e]; group
    · exact e
  rcases (M.mem_zpowers_of_sq hz2).1 (key x hxS hxc hx2) with e | e
  · left
    calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = 1 := by rw [e]; group
  · right
    calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = c * z * c⁻¹ := by rw [e]
      _ = c * (c⁻¹ * z * c) * c⁻¹ := by rw [hcz]
      _ = z := by group

theorem exists_central_of_normal {S E : Subgroup G} (hS2 : IsPGroup 2 ↥S) (hES : E ≤ S) (hE1 : E ≠ ⊥)
    (hEn : ∀ s ∈ S, ∀ v ∈ E, s * v * s⁻¹ ∈ E) :
    ∃ y ∈ E, y ≠ 1 ∧ ∀ s ∈ S, y * s = s * y := by
  have : Group.IsNilpotent ↥S := hS2.isNilpotent
  set H : Subgroup ↥S := E.subgroupOf S with hH
  have : H.Normal := ⟨fun n hn g => by
    rw [hH, Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hEn (g : G) g.2 (n : G) hn⟩
  have hHbot : H ≠ ⊥ := by
    obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
    intro hbot
    have hmem : (⟨(u : G), hES u.2⟩ : ↥S) ∈ H := by
      rw [hH, Subgroup.mem_subgroupOf]
      exact u.2
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hu1
    apply Subtype.ext
    simpa using congrArg Subtype.val hmem
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hHbot
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hxH : x ∈ H := hx.1
  have hxc : x ∈ Subgroup.center ↥S := hx.2
  have hxE : (x : G) ∈ E := by
    rw [hH, Subgroup.mem_subgroupOf] at hxH
    exact hxH
  refine ⟨x, hxE, ?_, ?_⟩
  · intro e
    apply hx1
    apply Subtype.ext
    apply Subtype.ext
    simpa using e
  · intro s hs
    have := Subgroup.mem_center_iff.1 hxc ⟨s, hs⟩
    exact (congrArg Subtype.val this).symm

omit [Finite G] in
theorem isFourSubgroup_sq_eq_one {E : Subgroup G} (hE : IVK.IsFourSubgroup E) {y : G} (hy : y ∈ E) :
    y * y = 1 := by
  obtain ⟨hel, -⟩ := hE
  have hexp : ∀ v : ↥E, v ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p 2 ↥E)
  simpa [pow_two] using congrArg Subtype.val (hexp ⟨y, hy⟩)

omit [Finite G] in
theorem exists_x_of_normal_four {S E : Subgroup G} {z : G} (hE : IVK.IsFourSubgroup E)
    (hEn : ∀ s ∈ S, ∀ v ∈ E, s * v * s⁻¹ ∈ E) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzE : z ∈ E)
    (hzc : ∀ s ∈ S, z * s = s * z) :
    ∃ x ∈ E, orderOf x = 2 ∧ x ≠ z ∧ ∀ s ∈ S, s * x * s⁻¹ = x ∨ s * x * s⁻¹ = x * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hel, hE4⟩ := hE
  have hexp : ∀ v : ↥E, v ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p 2 ↥E)
  have hcomm : ∀ a b : ↥E, a * b = b * a := fun a b => hel.toIsMulCommutative.is_comm.comm a b
  have hsq : ∀ v ∈ E, v * v = 1 := by
    intro v hv
    simpa [pow_two] using congrArg Subtype.val (hexp ⟨v, hv⟩)
  have hzle : zpowers z ≤ E := zpowers_le.2 hzE
  have hlt : zpowers z < E := by
    refine lt_of_le_of_ne hzle ?_
    intro h
    have h' : Nat.card ↥(zpowers z) = Nat.card ↥E := by rw [h]
    rw [M.card_zpowers_of_sq hz2 hz1, hE4] at h'
    omega
  obtain ⟨x, hxE, hxz⟩ := IsConcreteLE.exists_of_lt hlt
  have hx1 : x ≠ 1 := fun h => hxz (h ▸ one_mem _)
  have hxz' : x ≠ z := fun h => hxz (h ▸ mem_zpowers z)
  have hx2 : x * x = 1 := hsq x hxE
  refine ⟨x, hxE, orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1, hxz', fun s hs => ?_⟩
  set H : Subgroup ↥E := (zpowers z).subgroupOf E with hH
  have hHidx : H.index = 2 := by
    have h1 := Subgroup.index_mul_card H
    have h2 : Nat.card ↥H = 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv]
      exact M.card_zpowers_of_sq hz2 hz1
    rw [h2, hE4] at h1
    omega
  have hxH : (⟨x, hxE⟩ : ↥E) ∉ H := by
    intro h
    exact hxz (by simpa [hH, Subgroup.mem_subgroupOf] using h)
  set y : G := s * x * s⁻¹ with hy
  have hyE : y ∈ E := hEn s hs x hxE
  have hy2 : y * y = 1 := hsq y hyE
  have hy1 : y ≠ 1 := by
    intro h
    apply hx1
    calc x = s⁻¹ * y * s := by rw [hy]; group
      _ = 1 := by rw [h]; group
  have hyz : y ≠ z := by
    intro h
    apply hxz'
    calc x = s⁻¹ * y * s := by rw [hy]; group
      _ = s⁻¹ * z * s := by rw [h]
      _ = s⁻¹ * (z * s) := by group
      _ = s⁻¹ * (s * z) := by rw [hzc s hs]
      _ = z := by group
  by_cases hyH : (⟨y, hyE⟩ : ↥E) ∈ H
  · exfalso
    have : y ∈ zpowers z := by simpa [hH, Subgroup.mem_subgroupOf] using hyH
    rcases (M.mem_zpowers_of_sq hz2).1 this with h | h
    · exact hy1 h
    · exact hyz h
  · have hmem : (⟨x, hxE⟩ : ↥E) * ⟨y, hyE⟩ ∈ H := by
      rw [Subgroup.mul_mem_iff_of_index_two hHidx]
      exact iff_of_false hxH hyH
    have hmem' : x * y ∈ zpowers z := by simpa [hH, Subgroup.mem_subgroupOf] using hmem
    rcases (M.mem_zpowers_of_sq hz2).1 hmem' with h | h
    · left
      have : y = x⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this, inv_eq_of_mul_eq_one_right hx2]
    · right
      have h' : y = x⁻¹ * z := by
        calc y = x⁻¹ * (x * y) := by group
          _ = x⁻¹ * z := by rw [h]
      rw [h', inv_eq_of_mul_eq_one_right hx2]


theorem exists_normal_four_of_central_prod {S R P₀ : Subgroup G} (hS2 : IsPGroup 2 ↥S) (hRS : R ≤ S)
    (hRn : ∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R) (hrank : 2 ≤ CFSG.Open.pRank 2 R) (hP₀R : P₀ ≤ R)
    (hP₀ : ∃ n, IVK.IsQuaternionTwoGroup ↥P₀ n) {z q : G} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzR : z ∈ R) (hzc : ∀ g ∈ R, g * z = z * g) (hqR : q ∈ R) (hq1 : q ≠ 1) (hqz : q ≠ z)
    (hqc : ∀ p ∈ P₀, p * q = q * p) :
    ∃ E : Subgroup G, E ≤ R ∧ IVK.IsFourSubgroup E ∧ ∀ s ∈ S, ∀ v ∈ E, s * v * s⁻¹ ∈ E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrank' : 2 ≤ pRank 2 ↥(R.subgroupOf S) := by
    rw [pRank_eq_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hRS),
      TwoThin.pRank_two_subgroup_eq_open]
    exact hrank
  have hnormal : (R.subgroupOf S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hRn (g : G) g.2 (n : G) hn
  rcases CFSG.GH74.Uniqueness.SU.SU1.b_normal_Ep2 2 Nat.prime_two ↥S hS2 _ hnormal hrank' with
    ⟨E, hEn, hER, hEel, hE4⟩ | ⟨-, hD | hSD⟩
  · refine ⟨E.map S.subtype, ?_, isFourSubgroup_map S.subtype S.subtype_injective hEel hE4, ?_⟩
    · intro x hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
      exact Subgroup.mem_subgroupOf.1 (hER he)
    · intro s hs x hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
      exact Subgroup.mem_map.2 ⟨⟨s, hs⟩ * e * ⟨s, hs⟩⁻¹, hEn.conj_mem e he ⟨s, hs⟩, rfl⟩
  all_goals
    exfalso
    have hfinal : DSDData ↥R → False := by
      intro hD
      refine no_dsd_central_prod (M := ↥R) (hS2.to_le hRS) hD
        (P := P₀.subgroupOf R) (z := ⟨z, hzR⟩) (q := ⟨q, hqR⟩)
        (Subtype.ext hz2) (fun h1 => hz1 (congrArg Subtype.val h1)) ?_ ?_
        (fun h1 => hq1 (congrArg Subtype.val h1)) (fun h1 => hqz (congrArg Subtype.val h1)) ?_
      · intro g
        exact Subtype.ext (hzc g g.2)
      · obtain ⟨n, hn3, ⟨ι⟩⟩ := hP₀
        exact ⟨n, hn3, ⟨(Subgroup.subgroupOfEquivOfLe hP₀R).trans ι⟩⟩
      · intro p hp
        exact Subtype.ext (hqc (p : G) hp)
    have hψ := Subgroup.subgroupOfEquivOfLe hRS
    have hPcard : 8 ≤ Nat.card ↥P₀ := by
      obtain ⟨n, hn3, ⟨ι⟩⟩ := hP₀
      have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
      rw [Nat.card_congr ι.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      have : 2 ≤ 2 ^ (n - 2) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hPle : Nat.card ↥P₀ ≤ Nat.card ↥R := Subgroup.card_le_of_le hP₀R
    rw [← Nat.card_congr hψ.toEquiv] at hPle
  · obtain ⟨m, hm1, ⟨e⟩⟩ := hD
    have : NeZero (2 ^ m) := ⟨by positivity⟩
    have hcardR : Nat.card ↥(R.subgroupOf S) = 2 * 2 ^ m := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    rw [hcardR] at hPle
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have : m = 1 := by omega
      subst this
      omega
    exact hfinal (DSDData.congr hψ (DSDData.congr e.symm
      (dsdData_dihedral (2 ^ m) (by
        calc 4 = 2 ^ 2 := by norm_num
          _ ∣ 2 ^ m := pow_dvd_pow 2 hm2))))
  · obtain ⟨n', hn4, ⟨e⟩⟩ := hSD
    exact hfinal (DSDData.congr hψ (DSDData.congr e.symm (dsdData_semidihedral n' hn4)))

end Abstract

section Main

variable {G : Type} [Group G] [Finite G]

theorem p_normal_four_of_II4
    (hII : II4_4_4_center) : P_normal_four := by
  intro G _ _ z S K₁ K₂ h
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd : Std4 G z S K₁ K₂ := h.std
  have hM := m4_of_std hII hstd
  have hquat : ∀ K : Subgroup G, (K = K₁ ∨ K = K₂) → ∃ n, IVK.IsQuaternionTwoGroup ↥(S ⊓ K) n :=
    fun K hK => ii4_4_quat G hstd.simple z hstd.orderOf_z S K hstd.sylow
      (hstd.comp_isPCompIn hK) (hstd.comp_pRank hK)
  obtain ⟨u₁, hu₁, hu₁sq⟩ := exists_sq_eq_z_of_quat (hquat K₁ (Or.inl rfl))
    (fun x hx hx2 => hM.inv_comp (Or.inl rfl) hx hx2)
  obtain ⟨u₂, hu₂, hu₂sq⟩ := exists_sq_eq_z_of_quat (hquat K₂ (Or.inr rfl))
    (fun x hx hx2 => hM.inv_comp (Or.inr rfl) hx hx2)
  obtain ⟨hv2, hv1, hvz⟩ := hM.prod_facts hu₁.1 hu₂.1 hu₁.2 hu₂.2 hu₁sq hu₂sq
  have hPeq : Pz S z = S ⊓ (K₁ ⊔ K₂) := by rw [Pz, hstd.rigidProduct_eq]
  have hzS : z ∈ S := hM.z_mem_S
  have hzK : z ∈ K₁ ⊔ K₂ := mem_sup_left (hM.z_mem_comp (Or.inl rfl))
  have hzc : ∀ s ∈ S, z * s = s * z := fun s hs => (M.centralizer_comm (hM.S_syl.1 hs)).symm
  have hvS : u₁ * u₂ ∈ S := S.mul_mem hu₁.1 hu₂.1
  have hvK : u₁ * u₂ ∈ K₁ ⊔ K₂ := mul_mem (mem_sup_left hu₁.2) (mem_sup_right hu₂.2)
  have hRS : S ⊓ (K₁ ⊔ K₂) ≤ S := inf_le_left
  have hrank : 2 ≤ CFSG.Open.pRank 2 (S ⊓ (K₁ ⊔ K₂)) :=
    two_le_pRank_of_pair hM.z_sq hv2 (hzc _ hvS) hM.z_ne hv1 (Ne.symm hvz) ⟨hzS, hzK⟩ ⟨hvS, hvK⟩
  have hRn : ∀ s ∈ S, ∀ r ∈ S ⊓ (K₁ ⊔ K₂), s * r * s⁻¹ ∈ S ⊓ (K₁ ⊔ K₂) := fun s hs r hr =>
    ⟨S.mul_mem (S.mul_mem hs hr.1) (S.inv_mem hs), hM.C_norm_K (hM.S_syl.1 hs) hr.2⟩
  have hu₂1 : u₂ ≠ 1 := by
    intro h1
    apply hM.z_ne
    rw [← hu₂sq, h1, one_mul]
  have hu₂z : u₂ ≠ z := by
    intro h1
    apply hM.z_ne
    calc z = u₂ * u₂ := hu₂sq.symm
      _ = z * z := by rw [h1]
      _ = 1 := hM.z_sq
  obtain ⟨E, hER, hE4, hEn⟩ := exists_normal_four_of_central_prod hM.S_pgroup hRS hRn hrank
    (P₀ := S ⊓ K₁) (inf_le_inf_left S le_sup_left) (hquat K₁ (Or.inl rfl)) (z := z) (q := u₂)
    hM.z_sq hM.z_ne ⟨hzS, hzK⟩ (fun g hg => M.centralizer_comm (hM.S_syl.1 hg.1))
    ⟨hu₂.1, mem_sup_right hu₂.2⟩ hu₂1 hu₂z
    (fun p hp => hM.comm_of_S hp.2 hu₂.2 hp.1 hu₂.1)
  have hES : E ≤ S := hER.trans hRS
  have hE1 : E ≠ ⊥ := by
    intro h1
    have := hE4.2
    rw [h1, Subgroup.card_bot] at this
    omega
  obtain ⟨y, hyE, hy1, hyc⟩ := exists_central_of_normal hM.S_pgroup hES hE1 hEn
  obtain ⟨t₀, ht₀C, ht₀z, ht₀n⟩ := hstd.thm2
  have hcl := hstd.classical.2 t₀ ht₀C ht₀z ht₀n
  have hzE : z ∈ E := by
    have hyz := z_central_inv hM.z_sq hM.z_ne hzS hzc hM.S_top hcl.2.2.2.1 (hES hyE) hyc
      (isFourSubgroup_sq_eq_one hE4 hyE)
    rcases hyz with h1 | h1
    · exact absurd h1 hy1
    · exact h1 ▸ hyE
  obtain ⟨x, hxE, hx2, hxz, hxs⟩ := exists_x_of_normal_four hE4 hEn hM.z_sq hM.z_ne hzE hzc
  exact ⟨x, by rw [hPeq]; exact hER hxE, hx2, hxz, hxs⟩

end Main

end CFSG.GH74.GLS.IVK.Lifted
