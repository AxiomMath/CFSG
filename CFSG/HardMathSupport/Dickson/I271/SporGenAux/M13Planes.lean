module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.M13Act
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenCensus

public section

namespace CFSG.HardMathSupport.Dickson.I271.M13

open CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen CFSG.Open

variable {G : Type*} [Group G]

section Basic

variable {g d c : G}

theorem PlaneData.of_heis (hd13 : d ^ 13 = 1) (hc13 : c ^ 13 = 1) (hc1 : c ≠ 1)
    (hcg : c * g = g * c) (hcd : c * d = d * c) (hdg : d * g = g * (d * c ^ 4)) :
    PlaneData d c := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hco : orderOf c = 13 := orderOf_eq_prime hc13 hc1
  refine ⟨hcd.symm, hd13, hc13, fun j k hjk => ?_⟩
  have hcg' : Commute c g := hcg
  have hcd' : Commute c d := hcd
  have hdj : d ^ j = (c ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hjk
  have hcomm : d ^ j * g = g * d ^ j := by
    rw [hdj]
    exact ((hcg'.pow_left k).inv_left).eq
  have h := conj_pow_central hcd' hcg' (dg_conj hcg hcd hdg) j 1
  simp only [pow_one, Nat.mul_one] at h
  have h1 : g * c ^ (4 * j) = g := by
    rw [← h, hcomm]; group
  have h2 : c ^ (4 * j) = 1 := mul_eq_left.1 h1
  have h3 : 13 ∣ 4 * j := hco ▸ orderOf_dvd_of_pow_eq_one h2
  have hj : j % 13 = 0 := by omega
  have hdj1 : d ^ j = 1 := by rw [pow_eq_pow_mod j hd13, hj, pow_zero]
  rw [hdj1, one_mul] at hjk
  exact ⟨hj, Nat.mod_eq_zero_of_dvd (hco ▸ orderOf_dvd_of_pow_eq_one hjk)⟩

end Basic

section Sylow

variable {g d c : G}

theorem heis_sylow [Finite G] (hg13 : g ^ 13 = 1) (hd13 : d ^ 13 = 1) (hc13 : c ^ 13 = 1)
    (hc1 : c ≠ 1) (hcg : c * g = g * c) (hcd : c * d = d * c) (hdg : d * g = g * (d * c ^ 4)) :
    ∃ S : Subgroup G, g ∈ S ∧ d ∈ S ∧ c ∈ S ∧ Nat.card S = 13 ^ 3 ∧
      (∀ s ∈ S, ∃ a b k : ℕ, a < 13 ∧ b < 13 ∧ k < 13 ∧ s = g ^ a * d ^ b * c ^ k) ∧
      (∀ s ∈ S, c * s = s * c) := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hcg' : Commute c g := hcg
  have hcd' : Commute c d := hcd
  have hco : orderOf c = 13 := orderOf_eq_prime hc13 hc1
  have hc4 : c ^ 4 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hco] at this
    norm_num at this
  have hdc : d ∉ Subgroup.zpowers c := by
    intro hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    apply hc4
    have h1 : c ^ k * g = g * c ^ k := (hcg'.zpow_left k).eq
    rw [h1] at hdg
    have h2 := mul_left_cancel hdg
    exact (mul_left_cancel (a := c ^ k) (by rw [mul_one]; exact h2.symm)).symm.symm
  have hdo : orderOf d = 13 :=
    orderOf_eq_prime hd13 fun h => hdc (h ▸ Subgroup.one_mem _)
  have hdN : Subgroup.zpowers d ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_mem' fun n hn => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    rw [← (hcd'.zpow_left k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers c k
  have hA := card_sup_of_le_normalizer hdN (inf_eq_bot_of_not_mem hdo hdc)
  rw [Nat.card_zpowers, Nat.card_zpowers, hdo, hco] at hA
  set A := Subgroup.zpowers d ⊔ Subgroup.zpowers c with hAdef
  have hAset := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hdN
  have hAform : ∀ a ∈ A, ∃ i j : ℤ, a = d ^ i * c ^ j := by
    intro a ha
    rw [← SetLike.mem_coe, hAset] at ha
    obtain ⟨u, hu, v, hv, rfl⟩ := ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact ⟨i, j, rfl⟩
  have hdA : d ∈ A := Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
  have hcA : c ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hgA : g ∉ A := by
    intro hg
    obtain ⟨i, j, hij⟩ := hAform g hg
    apply hc4
    have h1 : g * d = d * g := by
      rw [hij]
      calc d ^ i * c ^ j * d = d ^ i * (c ^ j * d) := mul_assoc _ _ _
        _ = d ^ i * (d * c ^ j) := by rw [(hcd'.zpow_left j).eq]
        _ = d ^ i * d * c ^ j := (mul_assoc _ _ _).symm
        _ = d * d ^ i * c ^ j := by rw [(Commute.self_zpow d i).eq.symm]
        _ = d * (d ^ i * c ^ j) := mul_assoc _ _ _
    rw [← h1] at hdg
    have h2 := mul_left_cancel hdg
    have h3 : d * c ^ 4 = d * 1 := by rw [mul_one]; exact h2.symm
    exact mul_left_cancel h3
  have hgo : orderOf g = 13 :=
    orderOf_eq_prime hg13 fun h => hgA (h ▸ Subgroup.one_mem _)
  have hgd := gd_conj hcg hcd hdg hc13
  have hgN : Subgroup.zpowers g ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_mem' fun a ha => ?_
    obtain ⟨i, j, rfl⟩ := hAform a ha
    have e1 : g * (d ^ i * c ^ j) * g⁻¹ = (g * d * g⁻¹) ^ i * (g * c * g⁻¹) ^ j := by
      rw [conj_zpow, conj_zpow]; group
    rw [e1, hgd, show g * c * g⁻¹ = c by rw [← hcg'.eq, mul_inv_cancel_right]]
    exact A.mul_mem (A.zpow_mem (A.mul_mem hdA (A.pow_mem hcA 9)) i) (A.zpow_mem hcA j)
  have hS := card_sup_of_le_normalizer hgN (inf_eq_bot_of_not_mem hgo hgA)
  rw [Nat.card_zpowers, hgo, hA] at hS
  set S := Subgroup.zpowers g ⊔ A with hSdef
  have hSset := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hgN
  have hgS : g ∈ S := Subgroup.mem_sup_left (Subgroup.mem_zpowers g)
  have hdS : d ∈ S := Subgroup.mem_sup_right hdA
  have hcS : c ∈ S := Subgroup.mem_sup_right hcA
  refine ⟨S, hgS, hdS, hcS, by rw [hS]; norm_num, ?_, ?_⟩
  · intro t htS
    rw [← SetLike.mem_coe, hSset] at htS
    obtain ⟨u, hu, v, hv, rfl⟩ := htS
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, k, rfl⟩ := hAform v hv
    refine ⟨(i % 13).toNat, (j % 13).toNat, (k % 13).toNat, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · have hz : ∀ (y : G) (n : ℤ), orderOf y = 13 → y ^ n = y ^ (n % 13).toNat := by
        intro y n hy
        have h1 : y ^ n = y ^ (n % 13) := by rw [← zpow_mod_orderOf, hy]; simp
        rw [h1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
      rw [hz g i hgo, hz d j hdo, hz c k hco, mul_assoc]
  ·
    intro t htS
    rw [← SetLike.mem_coe, hSset] at htS
    obtain ⟨u, hu, v, hv, rfl⟩ := htS
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, k, rfl⟩ := hAform v hv
    have h1 : Commute c (g ^ i) := hcg'.zpow_right i
    have h2 : Commute c (d ^ j) := hcd'.zpow_right j
    have h3 : Commute c (c ^ k) := Commute.zpow_right (Commute.refl c) k
    exact ((h1.mul_right (h2.mul_right h3))).eq.symm.symm

end Sylow

section Lines

variable {g d c : G}

theorem exists_conj_line [Finite G] (hg13 : g ^ 13 = 1) (hd13 : d ^ 13 = 1)
    (hc13 : c ^ 13 = 1) (hc1 : c ≠ 1) (hcg : c * g = g * c) (hcd : c * d = d * c)
    (hdg : d * g = g * (d * c ^ 4)) (hG : (Nat.card G).factorization 13 = 3)
    (lines : List (ℕ × ℕ))
    (hcov : ∀ a b : ℕ, a < 13 → b < 13 → (a ≠ 0 ∨ b ≠ 0) →
      ∃ e ∈ lines, ∃ μ : ℕ, μ % 13 ≠ 0 ∧ (μ * e.1) % 13 = a ∧ (μ * e.2) % 13 = b)
    {P : Subgroup G} (hP : IsElemAbelian 13 P) (hPc : Nat.card P = 13 ^ 2) :
    ∃ h : G, ∃ e ∈ lines, ∃ μ : ℕ, μ % 13 ≠ 0 ∧
      P.map (MulAut.conj h).toMonoidHom =
        Subgroup.zpowers ((g ^ e.1 * d ^ e.2) ^ μ) ⊔ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hcg' : Commute c g := hcg
  have hcd' : Commute c d := hcd
  have hco : orderOf c = 13 := orderOf_eq_prime hc13 hc1
  have hc4 : c ^ 4 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hco] at this
    norm_num at this
  obtain ⟨S, hgS, hdS, hcS, hScard, hSform, hSc⟩ := heis_sylow hg13 hd13 hc13 hc1 hcg hcd hdg
  let SS : Sylow 13 G := Sylow.ofCard S (by rw [hScard, hG])
  have hPgrp : IsPGroup 13 P := IsPGroup.of_card hPc
  obtain ⟨Q, hQ⟩ := hPgrp.exists_le_sylow
  obtain ⟨m₀, hm₀⟩ := MulAction.exists_smul_eq G SS Q
  have hPS : P.map (MulAut.conj m₀⁻¹).toMonoidHom ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    have hxQ : x ∈ (Q : Subgroup G) := hQ hx
    rw [← hm₀, Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at hxQ
    obtain ⟨t, htS, hts⟩ := (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj m₀) S).1 hxQ
    rw [MulAut.smul_def, MulAut.conj_apply] at hts
    have : (MulAut.conj m₀⁻¹).toMonoidHom x = t := by
      rw [← hts]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    show (MulAut.conj m₀⁻¹).toMonoidHom x ∈ S
    rw [this]; exact htS
  set P' := P.map (MulAut.conj m₀⁻¹).toMonoidHom with hP'def
  have hP'el : IsElemAbelian 13 P' := hP.map _
  have hP'c : Nat.card P' = 13 ^ 2 := by
    rw [hP'def, Subgroup.card_map_of_injective (MulAut.conj m₀⁻¹).injective, hPc]
  suffices key : ∃ e ∈ lines, ∃ μ : ℕ, μ % 13 ≠ 0 ∧
      P' = Subgroup.zpowers ((g ^ e.1 * d ^ e.2) ^ μ) ⊔ Subgroup.zpowers c from by
    obtain ⟨e, he, μ, hμ, h⟩ := key
    exact ⟨m₀⁻¹, e, he, μ, hμ, h⟩
  have hcomm : ∀ s ∈ S, Commute c s := fun s hs => hSc s hs
  have e1 : ∀ k : ℤ, ∀ s ∈ S, c ^ k * s = s * c ^ k := fun k s hs => ((hcomm s hs).zpow_left k).eq
  have hleN : ∀ s ∈ S, s ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    intro s hs
    refine mem_normalizer_of_conj_mem' fun n hn => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    rw [← e1 k s hs, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers c k
  have hczp : Nat.card (Subgroup.zpowers c) = 13 := by rw [Nat.card_zpowers, hco]
  have hcP' : c ∈ P' := by
    by_contra hcP
    have hinf : P' ⊓ Subgroup.zpowers c = ⊥ := by
      rw [inf_comm]; exact inf_eq_bot_of_not_mem hco hcP
    have hleP : P' ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun s hs => hleN s (hPS hs)
    have hcard := card_sup_of_le_normalizer hleP hinf
    rw [hP'c, hczp] at hcard
    have hsupS : P' ⊔ Subgroup.zpowers c ≤ S := sup_le hPS ((Subgroup.zpowers_le).2 hcS)
    have hsupeq : P' ⊔ Subgroup.zpowers c = S :=
      Subgroup.eq_of_le_of_card_ge hsupS (by rw [hcard, hScard]; norm_num)
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right P' (Subgroup.zpowers c) hleP
    have hgm : g ∈ P' ⊔ Subgroup.zpowers c := hsupeq ▸ hgS
    have hdm : d ∈ P' ⊔ Subgroup.zpowers c := hsupeq ▸ hdS
    rw [← SetLike.mem_coe, hset] at hgm hdm
    obtain ⟨p₁, hp₁, v₁, hv₁, hg⟩ := hgm
    obtain ⟨p₂, hp₂, v₂, hv₂, hd⟩ := hdm
    obtain ⟨k₁, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv₁
    obtain ⟨k₂, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv₂
    have hp₁S : p₁ ∈ S := hPS hp₁
    have hp₂S : p₂ ∈ S := hPS hp₂
    have hcomm12 : p₁ * p₂ = p₂ * p₁ := by
      have := hP'el.1.is_comm.comm ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
      exact congrArg Subtype.val this
    have hgd : g * d = d * g := by
      rw [← hg, ← hd]
      calc p₁ * c ^ k₁ * (p₂ * c ^ k₂) = p₁ * (c ^ k₁ * p₂) * c ^ k₂ := by simp only [mul_assoc]
        _ = p₁ * (p₂ * c ^ k₁) * c ^ k₂ := by rw [e1 k₁ p₂ hp₂S]
        _ = (p₁ * p₂) * (c ^ k₁ * c ^ k₂) := by simp only [mul_assoc]
        _ = (p₂ * p₁) * (c ^ k₂ * c ^ k₁) := by rw [hcomm12, ← zpow_add, add_comm, zpow_add]
        _ = p₂ * (p₁ * c ^ k₂) * c ^ k₁ := by simp only [mul_assoc]
        _ = p₂ * (c ^ k₂ * p₁) * c ^ k₁ := by rw [e1 k₂ p₁ hp₁S]
        _ = p₂ * c ^ k₂ * (p₁ * c ^ k₁) := by simp only [mul_assoc]
    have h4 : c ^ 4 = 1 := by
      have h := hdg
      rw [← hgd] at h
      have h' := mul_left_cancel h
      exact mul_eq_left.1 h'.symm
    exact hc4 h4
  have hex : ∃ a ∈ P', a ∉ Subgroup.zpowers c := by
    by_contra hcon
    have hle : P' ≤ Subgroup.zpowers c := fun x hx => by
      by_contra hxc
      exact hcon ⟨x, hx, hxc⟩
    have := Subgroup.card_le_of_le hle
    rw [hP'c, hczp] at this
    norm_num at this
  obtain ⟨a, haP', hac⟩ := hex
  have haS : a ∈ S := hPS haP'
  obtain ⟨i, j, k, hi, hj, hk, hform⟩ := hSform a haS
  have hij : i ≠ 0 ∨ j ≠ 0 := by
    by_contra hcon
    have hi0 : i = 0 := by
      by_contra h
      exact hcon (Or.inl h)
    have hj0 : j = 0 := by
      by_contra h
      exact hcon (Or.inr h)
    subst hi0
    subst hj0
    apply hac
    rw [hform]
    simp only [pow_zero, one_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) k
  obtain ⟨e, he, μ, hμ, hμ1, hμ2⟩ := hcov i j hi hj hij
  obtain ⟨f, hf⟩ := heis_pow hcg hcd hdg hc13 e.1 e.2 μ
  have hga : g ^ i = g ^ (e.1 * μ) := by
    rw [pow_eq_pow_mod (e.1 * μ) hg13, mul_comm e.1 μ, hμ1]
  have hdb : d ^ j = d ^ (e.2 * μ) := by
    rw [pow_eq_pow_mod (e.2 * μ) hd13, mul_comm e.2 μ, hμ2]
  have ha' : a = (g ^ e.1 * d ^ e.2) ^ μ * c ^ (f + k) := by
    rw [hform, hga, hdb, hf, pow_add, mul_assoc]
  have hu : (g ^ e.1 * d ^ e.2) ^ μ = a * (c ^ (f + k))⁻¹ := by rw [ha']; group
  have huP' : (g ^ e.1 * d ^ e.2) ^ μ ∈ P' := by
    rw [hu]
    exact P'.mul_mem haP' (P'.inv_mem (P'.pow_mem hcP' _))
  set u := (g ^ e.1 * d ^ e.2) ^ μ with hudef
  have huS : u ∈ S := hPS huP'
  have huc : u ∉ Subgroup.zpowers c := by
    intro hh
    apply hac
    rw [ha']
    exact Subgroup.mul_mem _ hh (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
  have hu13 : u ^ 13 = 1 := hP'el.2 u huP'
  have hu1 : u ≠ 1 := by
    intro h1
    apply huc
    rw [h1]
    exact Subgroup.one_mem _
  have huo : orderOf u = 13 := orderOf_eq_prime hu13 hu1
  have hinf : Subgroup.zpowers u ⊓ Subgroup.zpowers c = ⊥ := inf_eq_bot_of_not_mem huo huc
  have hleU : Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hleN u huS
  have hcardU := card_sup_of_le_normalizer hleU hinf
  rw [Nat.card_zpowers, huo, hczp] at hcardU
  have hlePU : Subgroup.zpowers u ⊔ Subgroup.zpowers c ≤ P' :=
    sup_le ((Subgroup.zpowers_le).2 huP') ((Subgroup.zpowers_le).2 hcP')
  have hEq := Subgroup.eq_of_le_of_card_ge hlePU (by rw [hcardU, hP'c]; norm_num)
  have hμ' : μ % 13 ≠ 0 := hμ
  exact ⟨e, he, μ, hμ', hEq.symm⟩

end Lines

end CFSG.HardMathSupport.Dickson.I271.M13
