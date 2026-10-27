module

public import CFSG.GH74.GLS.Stage4.Q3n.Glue
public import CFSG.GH74.GLS.Stage4.Q3n.Final
public import CFSG.GH74.GLS.Stage4.Q3n.LGBridge
public import CFSG.GH74.GLS.Stage4.Q3n.Complement
public import CFSG.GH74.GLS.Stage4.Q3n.Split

public section

namespace CFSG.GH74.GLS.Stage4.Q3n

open Subgroup CFSG CFSG.GH74.GLS.Stage4.Rest

theorem q3n_false_split {G : Type} [Group G] [Finite G] {n : ℕ}
    (S : Q3nSetting G n) (hn : 3 ≤ n) : False := by
  classical
  set Mg := Subgroup.centralizer ({S.z} : Set G) with hMg
  set C0 := Subgroup.centralizer (S.U : Set G) with hC0
  obtain ⟨⟨m, hm, h2m⟩, -⟩ := CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  obtain ⟨ω, hω, hωker, hω1, hωinert⟩ := S.exists_omega hn
  have hdeg : ∃ d : ℕ, ω 1 = d ∧
      2 ^ ((Nat.card ↥(Subgroup.centralizer (S.U : Set G))).factorization 2 - 2) ∣ d :=
    ⟨2, by rw [hω1]; norm_num, S.two_pow_dvd_two⟩
  obtain ⟨B, b, f, fb, hB, hBdef, hBdeg, hb, hform⟩ :=
    iv2_11_1_split_proved m hm h2m G S.U S.U_card S.U_exp (S.U_aut hn) (S.exists_complement hn) ω
      hω hωker hdeg hωinert S.z S.z_mem_U S.z_ne_one
  have hformN : Nat.card G * Nat.card C0 ^ 2 * (fb 0 * fb 1 * fb 2) =
      Nat.card Mg ^ 3 * 4 * f := by
    have : ((Nat.card G * Nat.card C0 ^ 2 * (fb 0 * fb 1 * fb 2) : ℕ) : ℂ) =
        ((Nat.card Mg ^ 3 * 4 * f : ℕ) : ℂ) := by
      push_cast
      rw [hω1] at hform
      linear_combination hform
    exact_mod_cast this
  have hP_le : (S.P : Subgroup G) ≤ Mg := S.P_le.trans S.K_le_centralizer_z
  have hMg0 : Nat.card Mg ≠ 0 := Nat.card_pos.ne'
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have ht1 : (Nat.card G).factorization 3 ≤ (Nat.card Mg).factorization 3 := by
    have hdvd : Nat.card (S.P : Subgroup G) ∣ Nat.card Mg := Subgroup.card_dvd_of_le hP_le
    rw [Sylow.card_eq_multiplicity] at hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hMg0).1 hdvd
  have ht2 : (Nat.card Mg).factorization 3 ≤ (Nat.card G).factorization 3 := by
    have : Nat.card Mg ∣ Nat.card G := Subgroup.card_subgroup_dvd_card Mg
    exact (Nat.factorization_le_iff_dvd hMg0 hG0).2 this 3
  have ht : (Nat.card G).factorization 3 = (Nat.card Mg).factorization 3 := le_antisymm ht1 ht2
  have h3Mg : 3 ∣ Nat.card Mg := by
    obtain ⟨e₁⟩ := S.iso₁
    have : Fintype (GaloisField 3 n) := Fintype.ofFinite _
    have hqF : Nat.card (GaloisField 3 n) = 3 ^ n := GaloisField.card 3 n (by omega)
    have hK₁ : Nat.card ↥S.K₁ = 3 ^ n * ((3 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr e₁.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hqF]
    have h3K : 3 ∣ Nat.card ↥S.K₁ := by
      rw [hK₁]
      exact Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) _
    exact h3K.trans (Subgroup.card_dvd_of_le S.K₁_le_centralizer_z)
  have hpos : 1 ≤ (Nat.card G).factorization 3 := by
    rw [ht]
    exact Nat.Prime.factorization_pos_of_dvd Nat.prime_three hMg0 h3Mg
  have h3T : ∃ j : Fin 3, 3 ∣ fb j := by
    by_contra hno
    push Not at hno
    have hT : ¬ 3 ∣ fb 0 * fb 1 * fb 2 := by
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
      · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
        · exact hno 0 h
        · exact hno 1 h
      · exact hno 2 h
    have hC : ¬ 3 ∣ Nat.card C0 ^ 2 * (fb 0 * fb 1 * fb 2) := by
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
      · exact S.three_not_dvd_card_C0 (by omega) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
      · exact hT h
    set t := (Nat.card G).factorization 3 with ht_def
    have hdvd1 : 3 ^ (3 * t) ∣ Nat.card Mg ^ 3 * 4 * f := by
      have h3t : 3 ^ t ∣ Nat.card Mg := by
        rw [ht]
        exact Nat.ordProj_dvd _ _
      have h3 : (3 ^ t) ^ 3 ∣ Nat.card Mg ^ 3 := pow_dvd_pow_of_dvd h3t 3
      rw [← pow_mul, mul_comm] at h3
      exact (h3.mul_right 4).mul_right f
    have hdvd2 : 3 ^ (3 * t) ∣ Nat.card G * (Nat.card C0 ^ 2 * (fb 0 * fb 1 * fb 2)) := by
      rw [← mul_assoc, hformN]
      exact hdvd1
    have hcop : Nat.Coprime (3 ^ (3 * t)) (Nat.card C0 ^ 2 * (fb 0 * fb 1 * fb 2)) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hC)
    have hdvd3 : 3 ^ (3 * t) ∣ Nat.card G := hcop.dvd_of_dvd_mul_right hdvd2
    have hnd := Nat.pow_succ_factorization_not_dvd hG0 Nat.prime_three
    exact hnd ((pow_dvd_pow 3 (by omega : t + 1 ≤ 3 * t)).trans hdvd3)
  obtain ⟨j, hj3⟩ := h3T
  obtain ⟨hbj, hbjdef, hbjdeg⟩ := hb j
  obtain ⟨ψ, hψ, hbψ⟩ := hbj
  have hψmem : ψ ∈ b j := by
    rw [hbψ]
    exact ⟨hψ, fun A _ => Iff.rfl⟩
  have hψdeg := hbjdeg ψ hψmem
  have hψdef := hbjdef ψ hψmem
  obtain ⟨d, hψd, hdvd⟩ := lg33_1 2 Nat.prime_two m hm h2m Mg (S.U.subgroupOf Mg) ψ hψ hψdef
  have hdfb : d = fb j := by
    have : (d : ℂ) = (fb j : ℂ) := hψd.symm.trans hψdeg
    exact_mod_cast this
  have hUcard : Nat.card ↥(S.U.subgroupOf Mg) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.U_le_centralizer_z).toEquiv, S.U_card]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv4 : (Nat.card ↥(S.U.subgroupOf Mg)).factorization 2 = 2 := by
    rw [hUcard, Nat.factorization_def _ Nat.prime_two]
    have := padicValNat.prime_pow (p := 2) 2
    simpa using this
  rw [hv4, hdfb] at hdvd
  have hK₁le := S.K₁_le_centralizer_z
  have hK₂le := S.K₂_le_centralizer_z
  obtain ⟨e₁⟩ := S.iso₁
  obtain ⟨e₂⟩ := S.iso₂
  have hsup : S.K₁.subgroupOf Mg ⊔ S.K₂.subgroupOf Mg = (S.K₁ ⊔ S.K₂).subgroupOf Mg :=
    (Subgroup.subgroupOf_sup hK₁le hK₂le).symm
  have hinf : S.K₁.subgroupOf Mg ⊓ S.K₂.subgroupOf Mg = (S.K₁ ⊓ S.K₂).subgroupOf Mg :=
    by ext x; simp [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  refine final_contradiction (n := n) (by omega) (S.K₁.subgroupOf Mg) (S.K₂.subgroupOf Mg)
    ((Subgroup.subgroupOfEquivOfLe hK₁le).trans e₁) ((Subgroup.subgroupOfEquivOfLe hK₂le).trans e₂)
    (fun x hx y hy => Subtype.ext (S.K_comm _ (Subgroup.mem_subgroupOf.1 hx) _
      (Subgroup.mem_subgroupOf.1 hy)))
    (by rw [hsup]; exact S.K_subgroupOf_normal) (by rw [hsup]; exact S.index_K_le_two)
    ?_ ψ hψ (fb j) hψdeg hdvd hj3
  rw [hinf, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hK₁le)).toEquiv,
    S.K_inter, Nat.card_zpowers, S.z_ord]

theorem ch6t2badgt9_of_split (hS : Q3nSettingOf) : Ch6T2BadGt9 := by
  intro G _ _ hStd hr Gs _ n hn hAt hBad
  obtain ⟨S⟩ := hS G hStd hr Gs n hn hAt hBad
  exact q3n_false_split S hn

end CFSG.GH74.GLS.Stage4.Q3n
