module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Three
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23Gen

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.L246.C123 (A7)

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_fpf_three_of_setting_F4 (h526 : Stmt5_2_6_F4)
    (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4) (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4)
    (hQ : Stmt5_2_8_Q_F4) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) :
    ∃ k ∈ oTwoUpper H, orderOf k = 3 ∧ ∀ u ∈ pCoreOf 2 M2, k * u * k⁻¹ = u → u = 1 := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hLin, hQeq, hUK, -⟩ := setting_K_facts_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨-, hU16, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  have hU2 : IsPGroup 2 (pCoreOf 2 M2) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M2
  have hcardK := card_eq_of_isLin2Type hLin
  rw [hQeq, hU16] at hcardK
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥(oTwoUpper H)) 3
    (by rw [hcardK]; norm_num)
  have hk3 : orderOf (k : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hk
  refine ⟨k, k.2, hk3, ?_⟩
  intro u hu hku
  obtain ⟨F, _, _, hF, α, hαs, hαk, β, hβs, hβk, hβ⟩ := hLin
  have hβi : Function.Injective β := by
    have hc : Nat.card ↥(blockU (oTwoUpper H)) ≤ Nat.card (Multiplicative (Fin 2 → F)) := by
      rw [hUK, hU16, Nat.card_eq_fintype_card (α := Multiplicative (Fin 2 → F)),
        Fintype.card_multiplicative, Fintype.card_fun, Fintype.card_fin, hF]
      norm_num
    exact (hβs.bijective_of_nat_card_le hc).1
  have h2 : (2 : F) = 0 := by
    have h4 := FiniteField.cast_card_eq_zero F
    rw [hF] at h4
    have h4' : (2 : F) ^ 2 = 0 := by exact_mod_cast h4
    exact pow_eq_zero_iff (by norm_num) |>.mp h4'
  have hα3 : (α k : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, ← map_pow, ← hk, pow_orderOf_eq_one, map_one]
    rfl
  have hα1 : (α k : Matrix (Fin 2) (Fin 2) F) ≠ 1 := by
    intro h1
    have h1' : α k = 1 := Subtype.ext h1
    have h3' : k ∈ CFSG.pCore 2 ↥(oTwoUpper H) := by
      rw [← hαk]
      exact h1'
    have h4 : (k : G) ∈ pCoreOf 2 (oTwoUpper H) := by
      rw [CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore] at h3'
      exact ⟨_, h3', rfl⟩
    rw [hQeq] at h4
    obtain ⟨e, he⟩ := hU2 ⟨k, h4⟩
    have : orderOf (k : G) ∣ 2 ^ e := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val he
      simpa using this
    rw [hk3] at this
    have h3k := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    norm_num at h3k
  have huK : u ∈ blockU (oTwoUpper H) := by rw [hUK]; exact hu
  have hfix := hβ k ⟨u, huK⟩ ⟨u, huK⟩ hku.symm
  have h0 := mulVec_eq_zero_of_pow_three h2 (α k).2 hα3 hα1 hfix.symm
  have h5 : β ⟨u, huK⟩ = 1 := h0
  have h6 : (⟨u, huK⟩ : ↥(blockU (oTwoUpper H))) = 1 := hβi (h5.trans (map_one β).symm)
  exact congrArg Subtype.val h6

theorem stmt5_2_14_one_of_F4
    (hQ : Stmt5_2_8_Q_F4) (h5211 : Stmt5_2_11_four_F4) (h526 : Stmt5_2_6_F4) (h1284 : Lemma128Four)
    (hSz : Stmt5_2_8_Sz_F4) (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) {x y : G} (hx3 : orderOf x = 3) (hy3 : orderOf y = 3)
    (hxi : ∃ i : G, orderOf i = 2 ∧ i * x = x * i)
    (hyj : ∃ j : G, orderOf j = 2 ∧ j * y = y * j) : ∃ g : G, g * x * g⁻¹ = y := by
  obtain ⟨z, hz2, hzT, hzU⟩ := stmt5_2_12_center_of_F4 hQ hyp hM23 hS
  have hC := centralizer_le_of_setting_F4 hQ h5211 hyp hM23 hS hz2 hzT hzU
  obtain ⟨k, hkK, hk3, hkfix⟩ := exists_fpf_three_of_setting_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hkM2 : k ∈ M2 := hS.K_lt.le hkK
  obtain ⟨π', ρ, hsurj, hker, hinj, hρ, hU16, hU2', hT8, hUT, hπ'⟩ :=
    exists_rho_of_setting_F4 hQ hyp hM23 hS
  have hU2 : IsPGroup 2 (pCoreOf 2 M2) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M2
  have hUM2 : pCoreOf 2 M2 ≤ M2 := CFSG.LieType.BorelTits.pCoreOf_le 2 M2
  have hUN : M2 ≤ Subgroup.normalizer (pCoreOf 2 M2 : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M2)
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    norm_num at hz2

  have red : ∀ w : G, orderOf w = 3 → (∃ i : G, orderOf i = 2 ∧ i * w = w * i) →
      ∃ a : G, a * w * a⁻¹ ∈ M2 ∧ (a * w * a⁻¹) * z = z * (a * w * a⁻¹) := by
    rintro w hw3 ⟨i, hi2, hiw⟩
    obtain ⟨a, ha⟩ :=
      exists_conj_eq_of_orderOf_two_F4 h526 h1284 hSz hU4 hsp hQ h5211 hyp hM23 hS hz2 hzT hzU hi2
    have hcomm : (a * w * a⁻¹) * z = z * (a * w * a⁻¹) := by
      rw [← ha]
      calc a * w * a⁻¹ * (a * i * a⁻¹) = a * (w * i) * a⁻¹ := by group
        _ = a * (i * w) * a⁻¹ := by rw [hiw]
        _ = a * i * a⁻¹ * (a * w * a⁻¹) := by group
    refine ⟨a, hC ?_, hcomm⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hcomm.symm

  have hk3' : orderOf (π' ⟨k, hkM2⟩) = 3 := orderOf_map_eq_three hker hU2 hkM2 hk3
  have notct : ∀ (w : G) (hw : w ∈ M2), orderOf w = 3 → w * z = z * w →
      ((π' ⟨w, hw⟩ : A7) : Equiv.Perm (Fin 7)).cycleType ≠
        ((π' ⟨k, hkM2⟩ : A7) : Equiv.Perm (Fin 7)).cycleType := by
    intro w hw hw3 hwz hct
    obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_cycleType_eq_A7 hk3' hct.symm)
    obtain ⟨m, rfl⟩ := hsurj c
    have hmk : (m : G) * k * (m : G)⁻¹ ∈ M2 := M2.mul_mem (M2.mul_mem m.2 hkM2) (M2.inv_mem m.2)
    have hmk3 : orderOf ((m : G) * k * (m : G)⁻¹) = 3 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hk3
    have hπeq : π ⟨(m : G) * k * (m : G)⁻¹, hmk⟩ = π ⟨w, hw⟩ := by
      rw [← hπ', ← hπ']
      congr 1
      rw [← hc]
      have : (⟨(m : G) * k * (m : G)⁻¹, hmk⟩ : ↥M2) = m * ⟨k, hkM2⟩ * m⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
    obtain ⟨g, hg, hgw⟩ := exists_conj_of_map_eq_three hS.ker_eq hU2 hUM2 hmk hw hmk3 hw3 hπeq

    set gm : G := g * m with hgm
    have hgmM2 : gm ∈ M2 := M2.mul_mem hg m.2
    have hu : gm⁻¹ * z * gm ∈ pCoreOf 2 M2 := by
      have := (Subgroup.mem_normalizer_iff.mp (hUN (M2.inv_mem hgmM2)) z).mp hzU
      simpa using this
    have hwz' : w * z * w⁻¹ = z := by rw [hwz, mul_inv_cancel_right]
    have hku : k * (gm⁻¹ * z * gm) * k⁻¹ = gm⁻¹ * z * gm := by
      have e : w = gm * k * gm⁻¹ := by rw [← hgw, hgm]; group
      rw [e] at hwz'
      calc k * (gm⁻¹ * z * gm) * k⁻¹ = gm⁻¹ * (gm * k * gm⁻¹ * z * (gm * k * gm⁻¹)⁻¹) * gm := by
            group
        _ = gm⁻¹ * z * gm := by rw [hwz']
    have h1 := hkfix _ hu hku
    apply hz1
    calc z = gm * (gm⁻¹ * z * gm) * gm⁻¹ := by group
      _ = 1 := by rw [h1]; group

  obtain ⟨a, haM2, haz⟩ := red x hx3 hxi
  obtain ⟨b, hbM2, hbz⟩ := red y hy3 hyj
  have hx3' : orderOf (a * x * a⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx3
  have hy3' : orderOf (b * y * b⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hy3
  have hcx := notct _ haM2 hx3' haz
  have hcy := notct _ hbM2 hy3' hbz
  have hxo := orderOf_map_eq_three hker hU2 haM2 hx3'
  have hyo := orderOf_map_eq_three hker hU2 hbM2 hy3'
  have hcxy : ((π' ⟨_, haM2⟩ : A7) : Equiv.Perm (Fin 7)).cycleType =
      ((π' ⟨_, hbM2⟩ : A7) : Equiv.Perm (Fin 7)).cycleType := by
    rcases cycleType_of_orderOf_eq_three hk3' with hk | hk <;>
    rcases cycleType_of_orderOf_eq_three hxo with hx | hx <;>
    rcases cycleType_of_orderOf_eq_three hyo with hy | hy <;>
    first
      | exact hx.trans hy.symm
      | exact absurd (hx.trans hk.symm) hcx
      | exact absurd (hy.trans hk.symm) hcy
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_cycleType_eq_A7 hxo hcxy)
  obtain ⟨m, rfl⟩ := hsurj c
  have hmx : (m : G) * (a * x * a⁻¹) * (m : G)⁻¹ ∈ M2 :=
    M2.mul_mem (M2.mul_mem m.2 haM2) (M2.inv_mem m.2)
  have hmx3 : orderOf ((m : G) * (a * x * a⁻¹) * (m : G)⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx3'
  have hπeq : π ⟨(m : G) * (a * x * a⁻¹) * (m : G)⁻¹, hmx⟩ = π ⟨b * y * b⁻¹, hbM2⟩ := by
    rw [← hπ', ← hπ']
    congr 1
    rw [← hc]
    have : (⟨(m : G) * (a * x * a⁻¹) * (m : G)⁻¹, hmx⟩ : ↥M2) = m * ⟨_, haM2⟩ * m⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  obtain ⟨g, -, hg⟩ := exists_conj_of_map_eq_three hS.ker_eq hU2 hUM2 hmx hbM2 hmx3 hy3' hπeq
  refine ⟨b⁻¹ * g * m * a, ?_⟩
  calc b⁻¹ * g * m * a * x * (b⁻¹ * g * m * a)⁻¹ =
        b⁻¹ * (g * ((m : G) * (a * x * a⁻¹) * (m : G)⁻¹) * g⁻¹) * b := by group
    _ = b⁻¹ * (b * y * b⁻¹) * b := by rw [hg]
    _ = y := by group

end CFSG.Quasithin.H13
