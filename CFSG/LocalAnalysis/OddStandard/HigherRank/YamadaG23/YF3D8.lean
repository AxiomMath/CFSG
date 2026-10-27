module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YD8

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

private theorem isE_card {D : Type} [Group D] {K : Subgroup D} (hK : IsE 2 ↥K) :
    Nat.card ↥K = 4 := by
  rw [hK.2]; norm_num

private theorem isE_sq_eq_one {D : Type} [Group D] {K : Subgroup D} (hK : IsE 2 ↥K) {a : D}
    (ha : a ∈ K) : a ^ 2 = 1 := by
  have h := hK.1.2 (⟨a, ha⟩ : ↥K) (Subgroup.mem_top _)
  simpa using congrArg Subtype.val h

private theorem isE_index {D : Type} [Group D] [Finite D] {K : Subgroup D} (hK : IsE 2 ↥K)
    (hD : Nat.card D = 8) : K.index = 2 := by
  have h := K.card_mul_index
  rw [isE_card hK, hD] at h
  omega

private theorem zpowers_of_order_two {D : Type} [Group D] {x y : D} (hx : orderOf x = 2)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← hk]
  have h : x ^ k = x ^ (k % (2 : ℤ)) := by
    have := (zpow_mod_orderOf x k).symm
    rwa [hx] at this
  rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
  · left; rw [h, hk0]; simp
  · right; rw [h, hk1]; simp

private theorem d8_data {D : Type} [Group D] [Finite D] (hD : Nat.card D = 8)
    (hnc : ∃ x y : D, x * y ≠ y * x) {K₁ K₂ : Subgroup D} (h₁ : IsE 2 ↥K₁)
    (h₂ : IsE 2 ↥K₂) (hne : K₁ ≠ K₂) :
    ∃ c a b : D,
      c ∈ K₁ ∧ c ∈ K₂ ∧ c ≠ 1 ∧ c ^ 2 = 1 ∧
      a ∈ K₁ ∧ a ∉ K₂ ∧ a ^ 2 = 1 ∧ a ≠ 1 ∧
      b ∈ K₂ ∧ b ∉ K₁ ∧ b ^ 2 = 1 ∧ b ≠ 1 ∧
      (∀ x : D, c * x = x * c) ∧
      K₁ ⊓ K₂ = Subgroup.zpowers c ∧
      K₁ = Subgroup.closure ({a, c} : Set D) ∧
      K₂ = Subgroup.closure ({b, c} : Set D) ∧
      Subgroup.closure ({a, b} : Set D) = ⊤ ∧
      (a * b) ^ 2 = c ∧ a * b ≠ b * a := by
  have h1card : Nat.card ↥K₁ = 4 := isE_card h₁
  have h2card : Nat.card ↥K₂ = 4 := isE_card h₂
  have hidx1 : K₁.index = 2 := isE_index h₁ hD
  have hidx2 : K₂.index = 2 := isE_index h₂ hD
  have hnorm1 : K₁.Normal := Subgroup.normal_of_index_eq_two hidx1
  have hnorm2 : K₂.Normal := Subgroup.normal_of_index_eq_two hidx2
  have hsup : K₁ ⊔ K₂ = ⊤ := by
    have hdvd : (K₁ ⊔ K₂).index ∣ 2 := by
      simpa [hidx1] using Subgroup.index_dvd_of_le (H := K₁) (K := K₁ ⊔ K₂) le_sup_left
    have hlt : (K₁ ⊔ K₂).index ≠ 2 := by
      intro hidxsup
      have hcard := (K₁ ⊔ K₂).card_mul_index
      rw [hidxsup, hD] at hcard
      have hc4 : Nat.card ↥(K₁ ⊔ K₂) = 4 := by omega
      have hEq : K₁ = K₁ ⊔ K₂ :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hc4, h1card])
      have hK2le : K₂ ≤ K₁ := hEq ▸ le_sup_right
      exact hne (Subgroup.eq_of_le_of_card_ge hK2le (by rw [h1card, h2card])).symm
    have hidx : (K₁ ⊔ K₂).index = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · exact absurd h hlt
    exact Subgroup.index_eq_one.mp hidx
  have hrel : K₁.relIndex K₂ = 2 := by
    haveI := hnorm1
    rw [← Subgroup.relIndex_sup_right (H := K₂) (K := K₁), sup_comm, hsup,
      Subgroup.relIndex_top_right, hidx1]
  have hinfcard : Nat.card ↥(K₁ ⊓ K₂) = 2 := by
    have hcard := Subgroup.card_mul_index (H := K₁.subgroupOf K₂)
    have hidxr : (K₁.subgroupOf K₂).index = 2 := hrel
    rw [hidxr, h2card] at hcard
    have hsub : Nat.card ↥(K₁.subgroupOf K₂) = 2 := by omega
    calc Nat.card ↥(K₁ ⊓ K₂)
        = Nat.card ↥((K₁.subgroupOf K₂).map K₂.subtype) := by
          rw [Subgroup.subgroupOf_map_subtype]
      _ = Nat.card ↥(K₁.subgroupOf K₂) := Subgroup.card_subtype K₂ (K₁.subgroupOf K₂)
      _ = 2 := hsub
  have hne_bot : K₁ ⊓ K₂ ≠ ⊥ := by
    intro hbot
    have h1c : Nat.card ↥(K₁ ⊓ K₂) = 1 := by rw [hbot]; exact Subgroup.card_bot
    omega
  haveI hnt : Nontrivial ↥(K₁ ⊓ K₂) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne_bot
  obtain ⟨c, hc, hc_ne⟩ := Subgroup.exists_ne_one_of_nontrivial (K₁ ⊓ K₂)
  have hcK1 : c ∈ K₁ := hc.1
  have hcK2 : c ∈ K₂ := hc.2
  have hc2 : c ^ 2 = 1 := isE_sq_eq_one h₁ hcK1
  have hc_order : orderOf c = 2 := orderOf_eq_prime hc2 hc_ne
  have hinf_eq : K₁ ⊓ K₂ = Subgroup.zpowers c := by
    have hle : Subgroup.zpowers c ≤ K₁ ⊓ K₂ := Subgroup.zpowers_le.mpr hc
    have hz : Nat.card ↥(Subgroup.zpowers c) = 2 := by rw [Nat.card_zpowers, hc_order]
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hinfcard, hz])).symm
  have hnotle1 : ¬ K₁ ≤ K₂ := by
    intro hle
    exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [h2card, h1card]))
  obtain ⟨a, haK1, ha_notK2⟩ := SetLike.not_le_iff_exists.mp hnotle1
  have ha2 : a ^ 2 = 1 := isE_sq_eq_one h₁ haK1
  have ha_ne : a ≠ 1 := fun h => ha_notK2 (h ▸ K₂.one_mem)
  have hnotle2 : ¬ K₂ ≤ K₁ := by
    intro hle
    exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [h1card, h2card])).symm
  obtain ⟨b, hbK2, hb_notK1⟩ := SetLike.not_le_iff_exists.mp hnotle2
  have hb2 : b ^ 2 = 1 := isE_sq_eq_one h₂ hbK2
  have hb_ne : b ≠ 1 := fun h => hb_notK1 (h ▸ K₁.one_mem)
  have hcomm1 : ∀ y ∈ K₁, c * y = y * c := by
    intro y hy
    have h := h₁.1.comm (a := (⟨c, hcK1⟩ : ↥K₁)) (b := (⟨y, hy⟩ : ↥K₁))
      (Subgroup.mem_top _) (Subgroup.mem_top _)
    simpa using congrArg Subtype.val h
  have hcomm2 : ∀ y ∈ K₂, c * y = y * c := by
    intro y hy
    have h := h₂.1.comm (a := (⟨c, hcK2⟩ : ↥K₂)) (b := (⟨y, hy⟩ : ↥K₂))
      (Subgroup.mem_top _) (Subgroup.mem_top _)
    simpa using congrArg Subtype.val h
  have hc_comm : ∀ x : D, c * x = x * c := by
    have hcen : K₁ ⊔ K₂ ≤ Subgroup.centralizer ({c} : Set D) := by
      refine sup_le ?_ ?_
      · intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro _ hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hcomm1 y hy
      · intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro _ hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hcomm2 y hy
    intro x
    have hx : x ∈ K₁ ⊔ K₂ := hsup ▸ Subgroup.mem_top x
    exact (Subgroup.mem_centralizer_iff.mp (hcen hx)) c (Set.mem_singleton c)
  have hK1_eq : K₁ = Subgroup.closure ({a, c} : Set D) := by
    have hle : Subgroup.closure ({a, c} : Set D) ≤ K₁ := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · rw [hx]; exact haK1
      · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hcK1
    have hcard : Nat.card ↥(Subgroup.closure ({a, c} : Set D)) = 4 := by
      have hdvd : Nat.card ↥(Subgroup.closure ({a, c} : Set D)) ∣ 4 := by
        simpa [h1card] using Subgroup.card_dvd_of_le hle
      have hlt : 2 < Nat.card ↥(Subgroup.closure ({a, c} : Set D)) := by
        have ha_not_zp : a ∉ Subgroup.zpowers c := by
          rw [← hinf_eq]; exact fun h => ha_notK2 h.2
        have hzp_lt : Subgroup.zpowers c < Subgroup.closure ({a, c} : Set D) := by
          refine lt_of_le_of_ne ?_ ?_
          · rw [Subgroup.zpowers_le]; exact Subgroup.subset_closure (by simp)
          · intro heq
            apply ha_not_zp
            rw [heq]
            exact Subgroup.subset_closure (by simp)
        have h := Subgroup.card_lt_of_lt hzp_lt
        rwa [Nat.card_zpowers, hc_order] at h
      have hdvd2 : Nat.card ↥(Subgroup.closure ({a, c} : Set D)) ∣ 2 ^ 2 := by
        simpa using hdvd
      obtain ⟨k, hk, hkcard⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).mp hdvd2
      interval_cases k <;> simp_all
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h1card, hcard])).symm
  have hK2_eq : K₂ = Subgroup.closure ({b, c} : Set D) := by
    have hle : Subgroup.closure ({b, c} : Set D) ≤ K₂ := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · rw [hx]; exact hbK2
      · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hcK2
    have hcard : Nat.card ↥(Subgroup.closure ({b, c} : Set D)) = 4 := by
      have hdvd : Nat.card ↥(Subgroup.closure ({b, c} : Set D)) ∣ 4 := by
        simpa [h2card] using Subgroup.card_dvd_of_le hle
      have hlt : 2 < Nat.card ↥(Subgroup.closure ({b, c} : Set D)) := by
        have hb_not_zp : b ∉ Subgroup.zpowers c := by
          rw [← hinf_eq]; exact fun h => hb_notK1 h.1
        have hzp_lt : Subgroup.zpowers c < Subgroup.closure ({b, c} : Set D) := by
          refine lt_of_le_of_ne ?_ ?_
          · rw [Subgroup.zpowers_le]; exact Subgroup.subset_closure (by simp)
          · intro heq
            apply hb_not_zp
            rw [heq]
            exact Subgroup.subset_closure (by simp)
        have h := Subgroup.card_lt_of_lt hzp_lt
        rwa [Nat.card_zpowers, hc_order] at h
      have hdvd2 : Nat.card ↥(Subgroup.closure ({b, c} : Set D)) ∣ 2 ^ 2 := by
        simpa using hdvd
      obtain ⟨k, hk, hkcard⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).mp hdvd2
      interval_cases k <;> simp_all
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h2card, hcard])).symm
  have htop_abc : Subgroup.closure ({a, b, c} : Set D) = ⊤ := by
    have h1le : K₁ ≤ Subgroup.closure ({a, b, c} : Set D) := by
      rw [hK1_eq, Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · rw [hx]; exact Subgroup.subset_closure (by simp)
      · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact Subgroup.subset_closure (by simp)
    have h2le : K₂ ≤ Subgroup.closure ({a, b, c} : Set D) := by
      rw [hK2_eq, Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · rw [hx]; exact Subgroup.subset_closure (by simp)
      · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact Subgroup.subset_closure (by simp)
    have : (⊤ : Subgroup D) ≤ Subgroup.closure ({a, b, c} : Set D) := by
      rw [← hsup]; exact sup_le h1le h2le
    exact top_le_iff.mp this
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hb2)
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha2)
  have hab_ne : a * b ≠ b * a := by
    intro hab
    have hpair : ({a, b, c} : Set D).Pairwise Commute := by
      intro x hx y hy _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> rw [hx, hy]
      · exact hab
      · exact (hc_comm a).symm
      · exact hab.symm
      · exact (hc_comm b).symm
      · exact hc_comm a
      · exact hc_comm b
    haveI hcommC : IsMulCommutative ↥(Subgroup.closure ({a, b, c} : Set D)) :=
      Subgroup.isMulCommutative_closure hpair
    obtain ⟨x, y, hxy⟩ := hnc
    have hx : x ∈ Subgroup.closure ({a, b, c} : Set D) := htop_abc ▸ Subgroup.mem_top x
    have hy : y ∈ Subgroup.closure ({a, b, c} : Set D) := htop_abc ▸ Subgroup.mem_top y
    exact hxy (by
      have h := mul_comm' (M := ↥(Subgroup.closure ({a, b, c} : Set D))) ⟨x, hx⟩ ⟨y, hy⟩
      simpa using congrArg Subtype.val h)
  have hmem1 : (a * b) ^ 2 ∈ K₁ := by
    have hconj : b * a * b⁻¹ ∈ K₁ := hnorm1.conj_mem a haK1 b
    have heq : (a * b) ^ 2 = a * (b * a * b⁻¹) := by
      rw [pow_two, hbinv]; group
    rw [heq]
    exact K₁.mul_mem haK1 hconj
  have hmem2 : (a * b) ^ 2 ∈ K₂ := by
    have hconj : a * b * a⁻¹ ∈ K₂ := hnorm2.conj_mem b hbK2 a
    have heq : (a * b) ^ 2 = (a * b * a⁻¹) * b := by
      rw [pow_two, hainv]; group
    rw [heq]
    exact K₂.mul_mem hconj hbK2
  have hab_sq : (a * b) ^ 2 = c := by
    have hmem : (a * b) ^ 2 ∈ K₁ ⊓ K₂ := ⟨hmem1, hmem2⟩
    rw [hinf_eq] at hmem
    rcases zpowers_of_order_two hc_order hmem with h | h
    · exfalso
      have hmul : (a * b) * (a * b) = 1 := by simpa [pow_two] using h
      have hab : a * b = b * a := by
        calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hmul).symm
          _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
          _ = b * a := by rw [hbinv, hainv]
      exact hab_ne hab
    · exact h
  have htop : Subgroup.closure ({a, b} : Set D) = ⊤ := by
    have hc_mem : c ∈ Subgroup.closure ({a, b} : Set D) := by
      rw [← hab_sq]
      exact pow_mem ((Subgroup.closure ({a, b} : Set D)).mul_mem
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))) 2
    have h1le : K₁ ≤ Subgroup.closure ({a, b} : Set D) := by
      rw [hK1_eq, Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · rw [hx]; exact Subgroup.subset_closure (by simp)
      · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hc_mem
    have h2le : K₂ ≤ Subgroup.closure ({a, b} : Set D) := by
      rw [hK2_eq, Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · rw [hx]; exact Subgroup.subset_closure (by simp)
      · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hc_mem
    have : (⊤ : Subgroup D) ≤ Subgroup.closure ({a, b} : Set D) := by
      rw [← hsup]; exact sup_le h1le h2le
    exact top_le_iff.mp this
  exact ⟨c, a, b, hcK1, hcK2, hc_ne, hc2, haK1, ha_notK2, ha2, ha_ne, hbK2, hb_notK1, hb2,
    hb_ne, hc_comm, hinf_eq, hK1_eq, hK2_eq, htop, hab_sq, hab_ne⟩

theorem d8_klein_iso {D : Type} [Group D] [Finite D] (hD : Nat.card D = 8)
    (hnc : ∃ x y : D, x * y ≠ y * x) {K₁ K₂ : Subgroup D} (h₁ : IsE 2 ↥K₁) (h₂ : IsE 2 ↥K₂)
    (hne : K₁ ≠ K₂) : Nonempty (D ≃* DihedralGroup 4) := by
  obtain ⟨c, a, b, hcK1, hcK2, hc_ne, hc2, haK1, ha_notK2, ha2, ha_ne, hbK2, hb_notK1, hb2,
    hb_ne, hc_comm, hinf_eq, hK1_eq, hK2_eq, htop, hab_sq, hab_ne⟩ :=
    d8_data hD hnc h₁ h₂ hne
  have ha_order : orderOf a = 2 := orderOf_eq_prime ha2 ha_ne
  have hb_order : orderOf b = 2 := orderOf_eq_prime hb2 hb_ne
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hb2)
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha2)
  have hba_sq : (b * a) ^ 2 = c := by
    have h1 : b * a = (a * b)⁻¹ := by rw [mul_inv_rev, hainv, hbinv]
    rw [h1]
    have h2 : ((a * b)⁻¹) ^ 2 = ((a * b) ^ 2)⁻¹ := by rw [inv_pow]
    rw [h2, hab_sq]
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hc2)
  have hba_order : orderOf (b * a) = 4 := by
    refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · intro h
      have h2 : (b * a) ^ 2 = 1 := by simpa using h
      rw [hba_sq] at h2
      exact hc_ne h2
    · have h4 : (b * a) ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hba_sq]
        exact hc2
      simpa using h4
  obtain ⟨φ⟩ := dihedral_of_involutions' (C := Subgroup.closure ({a, b} : Set D))
    (t := a) (d := b) rfl ha_order hb_order hba_order
  exact ⟨(Subgroup.topEquiv.symm).trans (((MulEquiv.subgroupCongr htop).symm).trans φ)⟩

theorem d8_klein_all {D : Type} [Group D] [Finite D] (hD : Nat.card D = 8)
    (hnc : ∃ x y : D, x * y ≠ y * x) {K₁ K₂ : Subgroup D} (h₁ : IsE 2 ↥K₁) (h₂ : IsE 2 ↥K₂)
    (hne : K₁ ≠ K₂) : {K : Subgroup D | IsE 2 ↥K} = {K₁, K₂} := by
  obtain ⟨c, a, b, hcK1, hcK2, hc_ne, hc2, haK1, ha_notK2, ha2, ha_ne, hbK2, hb_notK1, hb2,
    hb_ne, hc_comm, hinf_eq, hK1_eq, hK2_eq, htop, hab_sq, hab_ne⟩ :=
    d8_data hD hnc h₁ h₂ hne
  have ha_order : orderOf a = 2 := orderOf_eq_prime ha2 ha_ne
  have hb_order : orderOf b = 2 := orderOf_eq_prime hb2 hb_ne
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hb2)
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha2)
  have hba_sq : (b * a) ^ 2 = c := by
    have h1 : b * a = (a * b)⁻¹ := by rw [mul_inv_rev, hainv, hbinv]
    rw [h1]
    have h2 : ((a * b)⁻¹) ^ 2 = ((a * b) ^ 2)⁻¹ := by rw [inv_pow]
    rw [h2, hab_sq]
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hc2)
  obtain ⟨e⟩ := d8_klein_iso hD hnc h₁ h₂ hne
  have hDtop : Nonempty (↥(⊤ : Subgroup D) ≃* DihedralGroup 4) :=
    ⟨Subgroup.topEquiv.trans e⟩
  have hmax := d8_maxElemAbelian (C := (⊤ : Subgroup D)) (t := a) (d := b) htop.symm hDtop
    ha_order hb_order
  have hQ1 : Subgroup.closure ({(b * a) ^ 2, a} : Set D) = K₁ := by
    rw [hba_sq, Set.pair_comm, ← hK1_eq]
  have hQ2 : Subgroup.closure ({(b * a) ^ 2, b} : Set D) = K₂ := by
    rw [hba_sq, Set.pair_comm, ← hK2_eq]
  have hmax' : maxElemAbelian (⊤ : Subgroup D) = {K₁, K₂} := by rw [hmax, hQ1, hQ2]
  ext K
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hK
    have hKel : IsElemAbelian 2 K := by
      refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩
      · exact hK.1.comm (Subgroup.mem_top a) (Subgroup.mem_top b)
      · have h := hK.1.2 (⟨x, hx⟩ : ↥K) (Subgroup.mem_top _)
        simpa using congrArg Subtype.val h
    have hKmax : K ∈ maxElemAbelian (⊤ : Subgroup D) := by
      refine ⟨le_top, hKel, ?_⟩
      intro Y' hKY' _ hY'el
      have hdvdK : Nat.card ↥K ∣ Nat.card ↥Y' := Subgroup.card_dvd_of_le hKY'
      rw [isE_card hK] at hdvdK
      have hdvdY : Nat.card ↥Y' ∣ 8 := by
        simpa [hD] using Subgroup.card_subgroup_dvd_card Y'
      have hne8 : Nat.card ↥Y' ≠ 8 := by
        intro h8
        have htopY : Y' = ⊤ := by rw [← Subgroup.card_eq_iff_eq_top, h8, hD]
        have hcomm : ∀ x y : D, x * y = y * x := fun x y =>
          hY'el.comm (by rw [htopY]; trivial) (by rw [htopY]; trivial)
        obtain ⟨x, y, hxy⟩ := hnc
        exact hxy (hcomm x y)
      obtain ⟨m, hm⟩ := hdvdK
      have hm1 : m = 1 := by
        have hmpos : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h0 | hpos
          · rw [h0, mul_zero] at hm
            exact absurd hm Nat.card_pos.ne'
          · exact hpos
        have hmle : m ≤ 2 := by
          have hle : Nat.card ↥Y' ≤ 8 := Nat.le_of_dvd (by norm_num) hdvdY
          omega
        interval_cases m
        · rfl
        · exfalso; apply hne8; simpa using hm
      rw [hm1, mul_one] at hm
      exact (Subgroup.eq_of_le_of_card_ge hKY' (by rw [hm, isE_card hK])).symm
    rw [hmax'] at hKmax
    rcases hKmax with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact h₁
    · exact h₂

theorem d8_of_two_klein {D : Type} [Group D] [Finite D] (hD : Nat.card D = 8)
    (hnc : ∃ x y : D, x * y ≠ y * x) {K₁ K₂ : Subgroup D} (h₁ : IsE 2 ↥K₁) (h₂ : IsE 2 ↥K₂)
    (hne : K₁ ≠ K₂) :
    Nonempty (D ≃* DihedralGroup 4) ∧ {K : Subgroup D | IsE 2 ↥K} = {K₁, K₂} :=
  ⟨d8_klein_iso hD hnc h₁ h₂ hne, d8_klein_all hD hnc h₁ h₂ hne⟩

end CFSG.OddStandard.HigherRank.YamadaG23
