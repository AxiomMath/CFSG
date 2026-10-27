module

public import CFSG.Literature.Janko67Model
public import CFSG.RankThree.GF2n.Parrott.A1ModelFacts
public import CFSG.GroupTheory.Extraspecial2PG
public import CFSG.LargeExtraspecial.Transport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes

public section

namespace CFSG.Literature.Janko67

open CFSG.RankThree.GF2n.Parrott CFSG.ComponentClassification.CatFactsSmall.PSp43

open scoped Pointwise


private lemma tC_sq : tC * tC = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change t * t = 1
  exact t_sq

private lemma tC_ne_one : tC ≠ 1 := by
  intro h
  apply t_ne_one
  apply_fun (fun x : C0 => ((x : QP45.originalSubgroup) : Equiv.Perm (Fin 45))) at h
  exact h

private lemma a1C_sq : a1C * a1C = tC := by
  apply Subtype.ext
  apply Subtype.ext
  change alpha1 * alpha1 = t
  exact alpha1_sq

private lemma s1C_cube : s1C ^ 3 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change sigma1 ^ 3 = 1
  exact sigma1_cube

private lemma s2C_cube : s2C ^ 3 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change sigma2 ^ 3 = 1
  exact sigma2_cube

private lemma s1C_ne_one : s1C ≠ 1 := by
  intro h
  apply sigma1_ne_one
  apply_fun (fun x : C0 => ((x : QP45.originalSubgroup) : Equiv.Perm (Fin 45))) at h
  exact h

private lemma s2C_ne_one : s2C ≠ 1 := by
  intro h
  apply sigma2_ne_one
  apply_fun (fun x : C0 => ((x : QP45.originalSubgroup) : Equiv.Perm (Fin 45))) at h
  exact h

private lemma s1C_commute_s2C : Commute s1C s2C := by
  apply Subtype.ext
  apply Subtype.ext
  change sigma1 * sigma2 = sigma2 * sigma1
  exact sigma1_commute_sigma2

private lemma orderOf_tC : orderOf tC = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime tC_sq tC_ne_one

private lemma commute_tC (c : C0) : Commute c tC := by
  apply Subtype.ext
  simpa [tC] using Subgroup.mem_centralizer_singleton_iff.mp c.2

private lemma tC_mem_center_C0 : tC ∈ Subgroup.center C0 :=
  Subgroup.mem_center_iff.mpr fun c => commute_tC c

private lemma orderOf_s1C : orderOf s1C = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime s1C_cube s1C_ne_one

private lemma orderOf_s2C : orderOf s2C = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime s2C_cube s2C_ne_one

private def wC (i j : Fin 3) : C0 := (s1C ^ (i : ℕ)) * (s2C ^ (j : ℕ))

private def w (i j : Fin 3) : Equiv.Perm (Fin 45) :=
  (sigma1 ^ (i : ℕ)) * (sigma2 ^ (j : ℕ))

private lemma coe_wC_apply (i j : Fin 3) :
    ((wC i j : C0) : Equiv.Perm (Fin 45)) = w i j := rfl

private lemma coe_s1C : ((s1C : C0) : Equiv.Perm (Fin 45)) = sigma1 := rfl

private lemma coe_s2C : ((s2C : C0) : Equiv.Perm (Fin 45)) = sigma2 := rfl

private lemma coe_a1C : ((a1C : C0) : Equiv.Perm (Fin 45)) = alpha1 := rfl

private lemma coe_b1C : ((b1C : C0) : Equiv.Perm (Fin 45)) = beta1 := rfl

private lemma coe_a2C : ((a2C : C0) : Equiv.Perm (Fin 45)) = alpha2 := rfl

private lemma coe_b2C : ((b2C : C0) : Equiv.Perm (Fin 45)) = beta2 := rfl

private lemma w_inj_check :
    ∀ i j i' j' : Fin 3, w i j = w i' j' → i = i' ∧ j = j' := by
  decide +kernel

private lemma w_centralize_check :
    ∀ i j : Fin 3,
      (i = 0 ∧ j = 0) ∨
        ¬ (w i j * alpha1 = alpha1 * w i j) ∨
        ¬ (w i j * beta1 = beta1 * w i j) ∨
        ¬ (w i j * alpha2 = alpha2 * w i j) ∨
        ¬ (w i j * beta2 = beta2 * w i j) := by
  decide +kernel

private def sylow3C : Subgroup C0 := Subgroup.closure {s1C, s2C}

private lemma sigma_eq_sup :
    sylow3C = Subgroup.zpowers s1C ⊔ Subgroup.zpowers s2C := by
  rw [sylow3C, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
    ← Subgroup.closure_union]
  congr 1

private lemma commute_zpowers_s1_s2 :
    ∀ a ∈ Subgroup.zpowers s1C, ∀ b ∈ Subgroup.zpowers s2C, Commute a b := by
  intro a ha b hb
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← hi, ← hj]
  exact s1C_commute_s2C.zpow_zpow i j

private lemma mem_zpowers_fin_s1 {x : C0} (hx : x ∈ Subgroup.zpowers s1C) :
    ∃ i : Fin 3, s1C ^ (i : ℕ) = x := by
  have hfin : IsOfFinOrder s1C := isOfFinOrder_of_finite s1C
  have hpow : x ∈ Submonoid.powers s1C := hfin.mem_powers_iff_mem_zpowers.mpr hx
  rw [hfin.mem_powers_iff_mem_range_orderOf, orderOf_s1C] at hpow
  obtain ⟨n, hn, hxn⟩ := Finset.mem_image.mp hpow
  exact ⟨⟨n, by simpa using hn⟩, hxn⟩

private lemma mem_zpowers_fin_s2 {x : C0} (hx : x ∈ Subgroup.zpowers s2C) :
    ∃ j : Fin 3, s2C ^ (j : ℕ) = x := by
  have hfin : IsOfFinOrder s2C := isOfFinOrder_of_finite s2C
  have hpow : x ∈ Submonoid.powers s2C := hfin.mem_powers_iff_mem_zpowers.mpr hx
  rw [hfin.mem_powers_iff_mem_range_orderOf, orderOf_s2C] at hpow
  obtain ⟨n, hn, hxn⟩ := Finset.mem_image.mp hpow
  exact ⟨⟨n, by simpa using hn⟩, hxn⟩

private lemma zpowers_s1_inf_s2 :
    Subgroup.zpowers s1C ⊓ Subgroup.zpowers s2C = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨i, hi⟩ := mem_zpowers_fin_s1 hx1
  obtain ⟨j, hj⟩ := mem_zpowers_fin_s2 hx2
  have hwij : w i 0 = w 0 j := by
    have h : s1C ^ (i : ℕ) = s2C ^ (j : ℕ) := by rw [hi, hj]
    have := congrArg (fun z : C0 => ((z : C0) : Equiv.Perm (Fin 45))) h
    simpa [w, coe_s1C, coe_s2C] using this
  obtain ⟨h0, -⟩ := w_inj_check i 0 0 j hwij
  rw [Subgroup.mem_bot, ← hi, h0]
  simp

private lemma sigma_exists {x : C0} (hx : x ∈ sylow3C) :
    ∃ i j : Fin 3, wC i j = x := by
  rw [sigma_eq_sup] at hx
  obtain ⟨a, ha, b, hb, hab⟩ := (CFSG.mem_sup_of_commute commute_zpowers_s1_s2).mp hx
  obtain ⟨i, hi⟩ := mem_zpowers_fin_s1 ha
  obtain ⟨j, hj⟩ := mem_zpowers_fin_s2 hb
  exact ⟨i, j, by rw [wC, hi, hj, hab]⟩

private lemma card_sigma : Nat.card sylow3C = 9 := by
  rw [sigma_eq_sup, CFSG.card_sup_eq_mul_of_commute _ _ commute_zpowers_s1_s2
    zpowers_s1_inf_s2, Nat.card_zpowers, Nat.card_zpowers, orderOf_s1C, orderOf_s2C]

private lemma isPGroup_sigma : IsPGroup 3 sylow3C :=
  IsPGroup.of_card (n := 2) (by rw [card_sigma]; norm_num)

private noncomputable abbrev iota : C0 →* ↥QA45.originalSubgroup :=
  (Subgroup.inclusion QP45_le_QA45).comp C0.subtype

private lemma iota_injective : Function.Injective iota := by
  intro x y h
  exact Subtype.ext (Subgroup.inclusion_injective QP45_le_QA45 h)

private lemma map_closure_iota :
    (Subgroup.closure {a1C, b1C, a2C, b2C}).map iota = oTwoQA45 := by
  rw [oTwoQA45, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

private lemma card_closure_Q0 :
    Nat.card (Subgroup.closure {a1C, b1C, a2C, b2C}) = 32 := by
  rw [← Subgroup.card_map_of_injective (f := iota) iota_injective, map_closure_iota,
    card_oTwoQA45]
  norm_num

theorem pCore_C0_eq : CFSG.pCore 2 C0 = Subgroup.closure {a1C, b1C, a2C, b2C} := by
  have hp : (CFSG.pCore 2 C0).map C0.subtype =
      Subgroup.closure {⟨alpha1, alpha1_mem_Q⟩, ⟨beta1, beta1_mem_Q⟩,
        ⟨alpha2, alpha2_mem_Q⟩, ⟨beta2, beta2_mem_Q⟩} := by
    simpa only [CFSG.inSubgroup] using qp45_pCore_centralizer_t
  apply Subgroup.map_injective (Subgroup.subtype_injective C0)
  rw [hp, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

theorem card_pCore_C0 : Nat.card (CFSG.pCore 2 C0) = 32 := by
  rw [pCore_C0_eq, card_closure_Q0]

theorem isExtraspecialPGroup_pCore_C0 : IsExtraspecialPGroup 2 (CFSG.pCore 2 C0) := by
  have hmap : (CFSG.pCore 2 C0).map iota = oTwoQA45 := by
    rw [pCore_C0_eq]
    exact map_closure_iota
  have h2 : IsExtraspecialPGroup 2 ↥oTwoQA45 :=
    CFSG.IsExtraspecial2.toIsExtraspecialPGroup isExtraspecial2_oTwoQA45
  exact CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv
    ((Subgroup.equivMapOfInjective (CFSG.pCore 2 C0) iota iota_injective).trans
      (MulEquiv.subgroupCongr hmap)).symm h2

private lemma tC_mem_pCore : tC ∈ CFSG.pCore 2 C0 := by
  rw [pCore_C0_eq, ← a1C_sq]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))

private lemma center_pCore_C0 :
    Subgroup.center ↥(CFSG.pCore 2 C0) =
      Subgroup.zpowers (⟨tC, tC_mem_pCore⟩ : ↥(CFSG.pCore 2 C0)) := by
  have hcard : Nat.card (Subgroup.center ↥(CFSG.pCore 2 C0)) = 2 :=
    isExtraspecialPGroup_pCore_C0.2.2.2
  have hcardz :
      Nat.card (Subgroup.zpowers (⟨tC, tC_mem_pCore⟩ : ↥(CFSG.pCore 2 C0))) = 2 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, orderOf_tC]
  have hle : Subgroup.zpowers (⟨tC, tC_mem_pCore⟩ : ↥(CFSG.pCore 2 C0)) ≤
      Subgroup.center ↥(CFSG.pCore 2 C0) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact commute_tC y.val
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcardz])).symm

private lemma w_centralize {i j : Fin 3}
    (h1 : w i j * alpha1 = alpha1 * w i j)
    (h2 : w i j * beta1 = beta1 * w i j)
    (h3 : w i j * alpha2 = alpha2 * w i j)
    (h4 : w i j * beta2 = beta2 * w i j) : i = 0 ∧ j = 0 := by
  rcases w_centralize_check i j with h | h | h | h | h
  · exact h
  · exact absurd h1 h
  · exact absurd h2 h
  · exact absurd h3 h
  · exact absurd h4 h

private lemma sigma_inf_centralizer :
    sylow3C ⊓ Subgroup.centralizer (CFSG.pCore 2 C0 : Set C0) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxS, hxK⟩
  obtain ⟨i, j, rfl⟩ := sigma_exists hxS
  have hmem : ∀ g ∈ ({a1C, b1C, a2C, b2C} : Set C0), g ∈ CFSG.pCore 2 C0 := by
    intro g hg
    rw [pCore_C0_eq]
    exact Subgroup.subset_closure hg
  have h1 : Commute (wC i j) a1C :=
    (Subgroup.mem_centralizer_iff.mp hxK a1C (hmem a1C (by simp))).symm
  have h2 : Commute (wC i j) b1C :=
    (Subgroup.mem_centralizer_iff.mp hxK b1C (hmem b1C (by simp))).symm
  have h3 : Commute (wC i j) a2C :=
    (Subgroup.mem_centralizer_iff.mp hxK a2C (hmem a2C (by simp))).symm
  have h4 : Commute (wC i j) b2C :=
    (Subgroup.mem_centralizer_iff.mp hxK b2C (hmem b2C (by simp))).symm
  have hp1 : w i j * alpha1 = alpha1 * w i j := by
    have := congrArg (fun z : C0 => ((z : C0) : Equiv.Perm (Fin 45))) h1
    simpa [coe_wC_apply, coe_a1C] using this
  have hp2 : w i j * beta1 = beta1 * w i j := by
    have := congrArg (fun z : C0 => ((z : C0) : Equiv.Perm (Fin 45))) h2
    simpa [coe_wC_apply, coe_b1C] using this
  have hp3 : w i j * alpha2 = alpha2 * w i j := by
    have := congrArg (fun z : C0 => ((z : C0) : Equiv.Perm (Fin 45))) h3
    simpa [coe_wC_apply, coe_a2C] using this
  have hp4 : w i j * beta2 = beta2 * w i j := by
    have := congrArg (fun z : C0 => ((z : C0) : Equiv.Perm (Fin 45))) h4
    simpa [coe_wC_apply, coe_b2C] using this
  obtain ⟨hi, hj⟩ := w_centralize hp1 hp2 hp3 hp4
  rw [Subgroup.mem_bot, wC, hi, hj]
  simp

theorem centralizer_pCore_C0_le :
    Subgroup.centralizer (CFSG.pCore 2 C0 : Set C0) ≤ CFSG.pCore 2 C0 := by
  let K := Subgroup.centralizer (CFSG.pCore 2 C0 : Set C0)
  have hKnormal : K.Normal := Subgroup.normal_centralizer
  have hK3 : ¬ 3 ∣ Nat.card K := by
    intro h3
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3
      (hp := ⟨Nat.prime_three⟩) h3
    have hkC : orderOf (k : C0) = 3 := by rw [Subgroup.orderOf_coe, hk]
    have hkP : IsPGroup 3 (Subgroup.zpowers (k : C0)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hkC]; norm_num)
    obtain ⟨Q, hQ⟩ := hkP.exists_le_sylow
    let hSigmaSylow : Sylow 3 C0 :=
      isPGroup_sigma.toSylow (by
        intro h3dvd
        have hcard : 9 * sylow3C.index = 576 := by
          have hC0 : Nat.card C0 = 576 := qp45_card_centralizer_t
          have h := Subgroup.card_mul_index sylow3C
          rw [card_sigma, hC0] at h
          exact h
        have h27 : 27 ∣ 576 := by
          rw [← hcard]
          exact Nat.mul_dvd_mul_left 9 h3dvd
        norm_num at h27)
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C0 hSigmaSylow Q
    have hkQ : (k : C0) ∈ (Q : Subgroup C0) := hQ (Subgroup.mem_zpowers (k : C0))
    have hkSylow : (k : C0) ∈ ((g • hSigmaSylow : Sylow 3 C0) : Subgroup C0) := by
      rw [hg]
      exact hkQ
    have hkSigma : g⁻¹ * (k : C0) * g ∈ sylow3C := by
      have hkQ' : (k : C0) ∈ MulAut.conj g • (hSigmaSylow : Subgroup C0) := by
        rw [← Sylow.coe_subgroup_smul, hg]
        exact hkQ
      have h := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).mp hkQ'
      simpa [MulAut.conj_apply, hSigmaSylow] using h
    have hkKconj : g⁻¹ * (k : C0) * g ∈ K := by
      have := hKnormal.conj_mem (k : C0) k.2 g⁻¹
      simpa using this
    have hmem : g⁻¹ * (k : C0) * g ∈ sylow3C ⊓ K := ⟨hkSigma, hkKconj⟩
    rw [sigma_inf_centralizer] at hmem
    have h1 : g⁻¹ * (k : C0) * g = 1 := by simpa using hmem
    have hk1 : (k : C0) = 1 := by
      calc (k : C0) = g * (g⁻¹ * (k : C0) * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; simp
    rw [hk1, orderOf_one] at hkC
    omega
  have hKdvd64 : Nat.card K ∣ 2 ^ 6 := by
    have hdiv : Nat.card K ∣ 2 ^ 6 * 3 ^ 2 := by
      have hC0 : Nat.card C0 = 576 := qp45_card_centralizer_t
      rw [show (2 : ℕ) ^ 6 * 3 ^ 2 = 576 by norm_num, ← hC0]
      exact Subgroup.card_subgroup_dvd_card K
    have hcop3 : Nat.Coprime (Nat.card K) 3 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hK3)
    exact (hcop3.pow_right 2).dvd_mul_right.mp hdiv
  have hK2 : IsPGroup 2 K := IsPGroup.of_card_dvd_pow (n := 6) hKdvd64
  have hKle : K ≤ CFSG.pCore 2 C0 := by
    rw [CFSG.pCore]
    exact le_sSup ⟨hKnormal, hK2⟩
  exact hKle

private lemma eq_one_or_eq_tC_of_mem_center_pCore {c : C0}
    (hcQ : c ∈ CFSG.pCore 2 C0)
    (hcZ : (⟨c, hcQ⟩ : ↥(CFSG.pCore 2 C0)) ∈
      Subgroup.center ↥(CFSG.pCore 2 C0)) :
    c = 1 ∨ c = tC := by
  have hz : (⟨c, hcQ⟩ : ↥(CFSG.pCore 2 C0)) ∈
      Subgroup.zpowers (⟨tC, tC_mem_pCore⟩ : ↥(CFSG.pCore 2 C0)) := by
    rw [← center_pCore_C0]
    exact hcZ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hkC : tC ^ k = c := by
    have := congrArg (fun z : ↥(CFSG.pCore 2 C0) => (z : C0)) hk
    simpa using this
  have hk2 : tC ^ (k % 2) = tC ^ k := by
    have h := zpow_mod_orderOf tC k
    rwa [orderOf_tC] at h
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← hkC, ← hk2, h, zpow_zero]
  · right
    rw [← hkC, ← hk2, h, zpow_one]

theorem center_C0 : Subgroup.center C0 = Subgroup.zpowers tC := by
  apply le_antisymm
  · intro c hc
    have hcK : c ∈ Subgroup.centralizer (CFSG.pCore 2 C0 : Set C0) :=
      Subgroup.center_le_centralizer (CFSG.pCore 2 C0 : Set C0) hc
    have hcQ : c ∈ CFSG.pCore 2 C0 := centralizer_pCore_C0_le hcK
    have hcZ : (⟨c, hcQ⟩ : ↥(CFSG.pCore 2 C0)) ∈
        Subgroup.center ↥(CFSG.pCore 2 C0) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hc (y : C0)
    rcases eq_one_or_eq_tC_of_mem_center_pCore hcQ hcZ with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers tC
  · rw [Subgroup.zpowers_le]
    exact tC_mem_center_C0

theorem eq_one_or_eq_tC_of_mem_sylow (T : Sylow 2 C0) {c : C0} (hc : c ∈ (T : Subgroup C0))
    (hcT : ∀ d ∈ (T : Subgroup C0), c * d = d * c) : c = 1 ∨ c = tC := by
  have hcT' : c ∈ (T : Subgroup C0) := hc
  have hQleT : CFSG.pCore 2 C0 ≤ (T : Subgroup C0) :=
    IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup T
  have hcK : c ∈ Subgroup.centralizer (CFSG.pCore 2 C0 : Set C0) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hcT d (hQleT hd)).symm
  have hcQ : c ∈ CFSG.pCore 2 C0 := centralizer_pCore_C0_le hcK
  have hcZ : (⟨c, hcQ⟩ : ↥(CFSG.pCore 2 C0)) ∈
      Subgroup.center ↥(CFSG.pCore 2 C0) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hcK (y : C0) y.2
  exact eq_one_or_eq_tC_of_mem_center_pCore hcQ hcZ

theorem exists_index_two_C0 : ∃ K : Subgroup C0, K.index = 2 := by
  let J := CFSG.pCore 2 C0 ⊔ sylow3C
  refine ⟨J, ?_⟩
  have hinf : CFSG.pCore 2 C0 ⊓ sylow3C = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    rw [card_pCore_C0, card_sigma]
    norm_num
  have hnorm : sylow3C ≤ Subgroup.normalizer (CFSG.pCore 2 C0 : Set C0) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hjoin := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (CFSG.pCore 2 C0) sylow3C hnorm (disjoint_iff.mpr hinf)
  have hcardJ : Nat.card J = 288 := by
    change Nat.card ↥(CFSG.pCore 2 C0 ⊔ sylow3C) = 288
    rw [hjoin, card_pCore_C0, card_sigma]
  have hC0 : Nat.card C0 = 576 := qp45_card_centralizer_t
  have h := Subgroup.card_mul_index J
  rw [hcardJ, hC0] at h
  omega

theorem eq_bot_of_normal_of_odd_card_C0 (K : Subgroup C0) [K.Normal] (hK : Odd (Nat.card K)) :
    K = ⊥ := by
  have hcop : Nat.Coprime (Nat.card K) (Nat.card (CFSG.pCore 2 C0)) := by
    rw [card_pCore_C0]
    simpa only [show (32 : ℕ) = 2 ^ 5 by norm_num] using
      (Nat.coprime_two_right.mpr hK).pow_right 5
  have hinf : K ⊓ CFSG.pCore 2 C0 = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hcomm : ⁅K, CFSG.pCore 2 C0⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact (Subgroup.commutator_le_inf K (CFSG.pCore 2 C0)).trans hinf.le
  have hKleC : K ≤ Subgroup.centralizer (CFSG.pCore 2 C0 : Set C0) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hKle : K ≤ CFSG.pCore 2 C0 := hKleC.trans centralizer_pCore_C0_le
  have hKin : K ⊓ CFSG.pCore 2 C0 = K := inf_eq_left.mpr hKle
  rw [← hKin, hinf]

end CFSG.Literature.Janko67
