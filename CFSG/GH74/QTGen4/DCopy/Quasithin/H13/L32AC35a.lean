module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk7
public import CFSG.Quasithin.H13.L32A707c
public import CFSG.Quasithin.H13.L32AC47a

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem isSz_of_coprime_three_F4 (h76 : Lemma14_7_6_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (h3 : ¬ 3 ∣ Nat.card ↥(modO2Image H K)) : ∃ n : ℕ, IsSz n (cStar K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 := h76 G T L V H S
  have hK3 : Nat.Coprime (Nat.card ↥(modO2Image H K)) 3 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3 |>.symm
  have hA := CFSG.Quasithin.lemma_1_2_1_four_strong S.hyp.fsu.qtke S.hyp.fsu.simple
    S.hyp.fsu.nonabelian h36 S.hz.1.2 hK
  obtain ⟨e⟩ := modO2_mulEquiv hK
  have hKsub : IsSubnormal (modO2Image H K) ⊤ := subnormal_of_mem_cComp (modO2Image_mem_cComp hK)
  have hsz : ∃ n : ℕ, IsSz n (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rcases hA.1 with ⟨-, -, hlistK⟩ | ⟨-, hZ3, -⟩ | h3' | h4
    · obtain ⟨f, -, -, hf⟩ := hlist _ hlistK h3
      exact ⟨f, isSz_congr e.symm hf⟩
    · exfalso
      apply h3
      rw [← hZ3]
      exact Subgroup.card_subgroup_dvd_card _
    · exact absurd (fitting_eq_bot_of_coprime_three hF3 hKsub hK3)
        (fitting_ne_bot_coprime_six (Or.inl h3')).1
    · exact absurd (fitting_eq_bot_of_coprime_three hF3 hKsub hK3)
        (fitting_ne_bot_coprime_six (Or.inr h4)).1
  obtain ⟨n, hn⟩ := hsz
  exact ⟨n, isSz_congr (cStarEquiv K).symm hn⟩

theorem pPrimeCore_star_eq_bot_F4 (h76 : Lemma14_7_6_F4) (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK)
    (hlist : SQTKList3Dvd) (S : Setting147 G T L V H) :
    CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hX
  have hN3 : Nat.Coprime (Nat.card ↥(CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))) 3 :=
    (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H ⧸ CFSG.pCore 2 ↥H)).symm
  have hF3 := h76 G T L V H S
  have hNn : (CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).Normal := CFSG.pPrimeCore_normal
  have hNsolv : ¬ Group.IsSolvable ↥(CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    intro hs
    have hsub : IsSubnormal (CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)) ⊤ :=
      IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤)
    have hF := fitting_eq_bot_of_coprime_three hF3 hsub hN3
    exact hX (Subgroup.eq_bot_of_card_eq _
      ((CFSG.fitting_eq_bot_iff_card_eq_one_of_solvable _).mp hF))
  obtain ⟨J, hJ, hJN⟩ := exists_cComp_le_of_not_solvable le_top inferInstance hNsolv
  obtain ⟨K, hK, hKJ⟩ := exists_cComp_modO2Image_eq hJ
  have hK3 : ¬ 3 ∣ Nat.card ↥(modO2Image H K) := by
    rw [hKJ]
    intro h
    have h1 := h.trans (Subgroup.card_dvd_of_le hJN)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3.symm h1
  obtain ⟨n, hn⟩ := isSz_of_coprime_three_F4 h76 h36 hlist S hK hK3
  exact h33 G T L V H S K hK n hn

end CFSG.Quasithin.H13.L32A.C
